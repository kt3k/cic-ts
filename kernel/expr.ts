// The core term representation (SPEC.md Sections 2.3, 3.1–3.4).
//
// Corresponds to Lean's `expr`. Bound variables use de Bruijn indices; the
// innermost binder is index 0. This module provides the representation,
// constructors (which precompute the cache flags), structural equality and
// hashing, the generic structural traversals, and the capture-aware de Bruijn
// operations (instantiate/abstract) — a faithful port of Lean's kernel
// `expr.cpp` / `instantiate.cpp` / `abstract.cpp`.

import { type Level, levelEq, levelHasMVar, levelInstantiate } from "./level.ts";
import { type Name, nameEq } from "./name.ts";
import { hashBigInt, mixHash } from "./hash.ts";

export type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit";

/** Lightweight metadata map. Semantically transparent; ignored by the kernel. */
export type KVMap = ReadonlyMap<string, string | bigint | boolean>;

/**
 * Cache flags carried by every `Expr` node (SPEC.md Section 2.3).
 *
 * `looseBVarRange` is `1 +` the largest loose (unbound-at-this-node) de Bruijn
 * index occurring in the term, or 0 if there are none. It lets `instantiate` /
 * `abstract` skip subterms that cannot contain the variables they target.
 */
export interface ExprData {
  readonly hash: number;
  readonly hasFVar: boolean;
  readonly hasMVar: boolean;
  readonly hasLevelMVar: boolean;
  readonly looseBVarRange: number;
}

export type Expr =
  & ExprData
  & (
    | { readonly kind: "bvar"; readonly idx: bigint }
    | { readonly kind: "fvar"; readonly id: Name }
    | { readonly kind: "mvar"; readonly id: Name }
    | { readonly kind: "sort"; readonly level: Level }
    | { readonly kind: "const"; readonly name: Name; readonly levels: readonly Level[] }
    | { readonly kind: "app"; readonly fn: Expr; readonly arg: Expr }
    | {
      readonly kind: "lam";
      readonly name: Name;
      readonly type: Expr;
      readonly body: Expr;
      readonly info: BinderInfo;
    }
    | {
      readonly kind: "pi";
      readonly name: Name;
      readonly type: Expr;
      readonly body: Expr;
      readonly info: BinderInfo;
    }
    | {
      readonly kind: "let";
      readonly name: Name;
      readonly type: Expr;
      readonly value: Expr;
      readonly body: Expr;
    }
    | { readonly kind: "mdata"; readonly data: KVMap; readonly expr: Expr }
    | { readonly kind: "proj"; readonly struct: Name; readonly idx: bigint; readonly expr: Expr }
  );

const HASH_BVAR = 0x9e3779b1;
const HASH_FVAR = 0x85ebca6b;
const HASH_MVAR = 0xc2b2ae35;
const HASH_SORT = 0x27d4eb2f;
const HASH_CONST = 0x165667b1;
const HASH_APP = 0xd3a2646c;
const HASH_LAM = 0xfd7046c5;
const HASH_PI = 0xb55a4f09;
const HASH_LET = 0x1b873593;
const HASH_MDATA = 0x2545f491;
const HASH_PROJ = 0x94d049bb;

const binderInfoOrd: Record<BinderInfo, number> = {
  default: 0,
  implicit: 1,
  strictImplicit: 2,
  instImplicit: 3,
};

/** Loose-bvar range contributed by a subterm that sits under `binders` extra binders. */
function underBinders(range: number, binders: number): number {
  return Math.max(0, range - binders);
}

// --- Constructors -----------------------------------------------------------

/** de Bruijn bound variable. */
export function mkBVar(idx: bigint): Expr {
  if (idx < 0n) throw new Error(`mkBVar: negative index ${idx}`);
  return {
    kind: "bvar",
    idx,
    hash: mixHash(hashBigInt(idx), HASH_BVAR),
    hasFVar: false,
    hasMVar: false,
    hasLevelMVar: false,
    looseBVarRange: Number(idx) + 1,
  };
}

/** Free variable (a local hypothesis identified by name). */
export function mkFVar(id: Name): Expr {
  return {
    kind: "fvar",
    id,
    hash: mixHash(id.hash, HASH_FVAR),
    hasFVar: true,
    hasMVar: false,
    hasLevelMVar: false,
    looseBVarRange: 0,
  };
}

/** Metavariable. Must not appear in terms reaching the type checker. */
export function mkMVar(id: Name): Expr {
  return {
    kind: "mvar",
    id,
    hash: mixHash(id.hash, HASH_MVAR),
    hasFVar: false,
    hasMVar: true,
    hasLevelMVar: false,
    looseBVarRange: 0,
  };
}

/** `Sort u`. */
export function mkSort(level: Level): Expr {
  return {
    kind: "sort",
    level,
    hash: mixHash(level.hash, HASH_SORT),
    hasFVar: false,
    hasMVar: false,
    hasLevelMVar: levelHasMVar(level),
    looseBVarRange: 0,
  };
}

/** A constant in the environment, with its universe arguments. */
export function mkConst(name: Name, levels: readonly Level[] = []): Expr {
  let hash = mixHash(name.hash, HASH_CONST);
  let hasLevelMVar = false;
  for (const l of levels) {
    hash = mixHash(hash, l.hash);
    if (levelHasMVar(l)) hasLevelMVar = true;
  }
  return {
    kind: "const",
    name,
    levels,
    hash,
    hasFVar: false,
    hasMVar: false,
    hasLevelMVar,
    looseBVarRange: 0,
  };
}

/** Application `fn arg` (one argument at a time). */
export function mkApp(fn: Expr, arg: Expr): Expr {
  return {
    kind: "app",
    fn,
    arg,
    hash: mixHash(mixHash(fn.hash, arg.hash), HASH_APP),
    hasFVar: fn.hasFVar || arg.hasFVar,
    hasMVar: fn.hasMVar || arg.hasMVar,
    hasLevelMVar: fn.hasLevelMVar || arg.hasLevelMVar,
    looseBVarRange: Math.max(fn.looseBVarRange, arg.looseBVarRange),
  };
}

/** Left-associated application `fn arg0 arg1 ...`. */
export function mkAppN(fn: Expr, args: readonly Expr[]): Expr {
  let e = fn;
  for (const arg of args) e = mkApp(e, arg);
  return e;
}

/** `fun (name : type) => body`. The binder is index 0 inside `body`. */
export function mkLambda(name: Name, type: Expr, body: Expr, info: BinderInfo = "default"): Expr {
  return {
    kind: "lam",
    name,
    type,
    body,
    info,
    hash: mixHash(mixHash(type.hash, body.hash), HASH_LAM),
    hasFVar: type.hasFVar || body.hasFVar,
    hasMVar: type.hasMVar || body.hasMVar,
    hasLevelMVar: type.hasLevelMVar || body.hasLevelMVar,
    looseBVarRange: Math.max(type.looseBVarRange, underBinders(body.looseBVarRange, 1)),
  };
}

/** `(name : type) → body`. The binder is index 0 inside `body`. */
export function mkPi(name: Name, type: Expr, body: Expr, info: BinderInfo = "default"): Expr {
  return {
    kind: "pi",
    name,
    type,
    body,
    info,
    hash: mixHash(mixHash(type.hash, body.hash), HASH_PI),
    hasFVar: type.hasFVar || body.hasFVar,
    hasMVar: type.hasMVar || body.hasMVar,
    hasLevelMVar: type.hasLevelMVar || body.hasLevelMVar,
    looseBVarRange: Math.max(type.looseBVarRange, underBinders(body.looseBVarRange, 1)),
  };
}

/** `let name : type := value; body`. The binder is index 0 inside `body` only. */
export function mkLet(name: Name, type: Expr, value: Expr, body: Expr): Expr {
  return {
    kind: "let",
    name,
    type,
    value,
    body,
    hash: mixHash(mixHash(mixHash(type.hash, value.hash), body.hash), HASH_LET),
    hasFVar: type.hasFVar || value.hasFVar || body.hasFVar,
    hasMVar: type.hasMVar || value.hasMVar || body.hasMVar,
    hasLevelMVar: type.hasLevelMVar || value.hasLevelMVar || body.hasLevelMVar,
    looseBVarRange: Math.max(
      type.looseBVarRange,
      value.looseBVarRange,
      underBinders(body.looseBVarRange, 1),
    ),
  };
}

/** A metadata-annotated term (semantically transparent). */
export function mkMData(data: KVMap, expr: Expr): Expr {
  return {
    kind: "mdata",
    data,
    expr,
    hash: mixHash(expr.hash, HASH_MDATA),
    hasFVar: expr.hasFVar,
    hasMVar: expr.hasMVar,
    hasLevelMVar: expr.hasLevelMVar,
    looseBVarRange: expr.looseBVarRange,
  };
}

/** Projection of the `idx`-th field of a structure value `expr` of type `struct`. */
export function mkProj(struct: Name, idx: bigint, expr: Expr): Expr {
  if (idx < 0n) throw new Error(`mkProj: negative index ${idx}`);
  return {
    kind: "proj",
    struct,
    idx,
    expr,
    hash: mixHash(mixHash(hashBigInt(idx), expr.hash), HASH_PROJ),
    hasFVar: expr.hasFVar,
    hasMVar: expr.hasMVar,
    hasLevelMVar: expr.hasLevelMVar,
    looseBVarRange: expr.looseBVarRange,
  };
}

// --- Equality ---------------------------------------------------------------

function levelsEq(a: readonly Level[], b: readonly Level[]): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) {
    if (!levelEq(a[i]!, b[i]!)) return false;
  }
  return true;
}

function kvmapEq(a: KVMap, b: KVMap): boolean {
  if (a.size !== b.size) return false;
  for (const [k, v] of a) {
    if (!b.has(k) || b.get(k) !== v) return false;
  }
  return true;
}

/**
 * Exact structural equality (compares binder names, binder info, and metadata).
 * This is *not* definitional equality (`isDefEq`); that lives in the type
 * checker (Phase 2) and accounts for β/δ/ζ/η/proof-irrelevance.
 */
export function exprEq(a: Expr, b: Expr): boolean {
  if (a === b) return true;
  if (a.hash !== b.hash || a.kind !== b.kind) return false;
  switch (a.kind) {
    case "bvar":
      return a.idx === (b as typeof a).idx;
    case "fvar":
    case "mvar":
      return nameEq(a.id, (b as typeof a).id);
    case "sort":
      return levelEq(a.level, (b as typeof a).level);
    case "const":
      return nameEq(a.name, (b as typeof a).name) && levelsEq(a.levels, (b as typeof a).levels);
    case "app":
      return exprEq(a.fn, (b as typeof a).fn) && exprEq(a.arg, (b as typeof a).arg);
    case "lam":
    case "pi": {
      const bb = b as typeof a;
      return (
        binderInfoOrd[a.info] === binderInfoOrd[bb.info] &&
        nameEq(a.name, bb.name) &&
        exprEq(a.type, bb.type) &&
        exprEq(a.body, bb.body)
      );
    }
    case "let": {
      const bb = b as typeof a;
      return (
        nameEq(a.name, bb.name) &&
        exprEq(a.type, bb.type) &&
        exprEq(a.value, bb.value) &&
        exprEq(a.body, bb.body)
      );
    }
    case "mdata":
      return kvmapEq(a.data, (b as typeof a).data) && exprEq(a.expr, (b as typeof a).expr);
    case "proj": {
      const bb = b as typeof a;
      return a.idx === bb.idx && nameEq(a.struct, bb.struct) && exprEq(a.expr, bb.expr);
    }
  }
}

// --- Application spine helpers ----------------------------------------------

/** The head of an application spine: `getAppFn(f a b) = f`. */
export function getAppFn(e: Expr): Expr {
  let cur = e;
  while (cur.kind === "app") cur = cur.fn;
  return cur;
}

/** The arguments of an application spine, left to right: `getAppArgs(f a b) = [a, b]`. */
export function getAppArgs(e: Expr): Expr[] {
  const args: Expr[] = [];
  let cur = e;
  while (cur.kind === "app") {
    args.push(cur.arg);
    cur = cur.fn;
  }
  args.reverse();
  return args;
}

// --- Generic traversal (SPEC.md Section 3.1) --------------------------------
//
// These do NOT track binder depth or touch de Bruijn indices; for capture-aware
// operations use the de Bruijn section below.

/** Rebuild `e` with each immediate subexpression replaced by `g(child)`. */
export function mapChildren(e: Expr, g: (child: Expr) => Expr): Expr {
  switch (e.kind) {
    case "app":
      return mkApp(g(e.fn), g(e.arg));
    case "lam":
      return mkLambda(e.name, g(e.type), g(e.body), e.info);
    case "pi":
      return mkPi(e.name, g(e.type), g(e.body), e.info);
    case "let":
      return mkLet(e.name, g(e.type), g(e.value), g(e.body));
    case "mdata":
      return mkMData(e.data, g(e.expr));
    case "proj":
      return mkProj(e.struct, e.idx, g(e.expr));
    default:
      return e; // bvar, fvar, mvar, sort, const: no subexpressions
  }
}

/**
 * Like {@link mapChildren} but threads a binder depth: `g` is called with
 * `depth + 1` under each binder body and `depth` elsewhere. Used by the
 * capture-aware de Bruijn operations below.
 */
export function mapChildrenWithDepth(
  e: Expr,
  depth: number,
  g: (child: Expr, depth: number) => Expr,
): Expr {
  switch (e.kind) {
    case "app":
      return mkApp(g(e.fn, depth), g(e.arg, depth));
    case "lam":
      return mkLambda(e.name, g(e.type, depth), g(e.body, depth + 1), e.info);
    case "pi":
      return mkPi(e.name, g(e.type, depth), g(e.body, depth + 1), e.info);
    case "let":
      return mkLet(e.name, g(e.type, depth), g(e.value, depth), g(e.body, depth + 1));
    case "mdata":
      return mkMData(e.data, g(e.expr, depth));
    case "proj":
      return mkProj(e.struct, e.idx, g(e.expr, depth));
    default:
      return e; // bvar, fvar, mvar, sort, const: no subexpressions
  }
}

/** Visit `e` and all of its subexpressions, top-down. */
export function forEach(e: Expr, f: (sub: Expr) => void): void {
  f(e);
  switch (e.kind) {
    case "app":
      forEach(e.fn, f);
      forEach(e.arg, f);
      return;
    case "lam":
    case "pi":
      forEach(e.type, f);
      forEach(e.body, f);
      return;
    case "let":
      forEach(e.type, f);
      forEach(e.value, f);
      forEach(e.body, f);
      return;
    case "mdata":
    case "proj":
      forEach(e.expr, f);
      return;
    default:
      return;
  }
}

/** Return the first subexpression (top-down) satisfying `pred`, or `undefined`. */
export function find(e: Expr, pred: (sub: Expr) => boolean): Expr | undefined {
  if (pred(e)) return e;
  switch (e.kind) {
    case "app":
      return find(e.fn, pred) ?? find(e.arg, pred);
    case "lam":
    case "pi":
      return find(e.type, pred) ?? find(e.body, pred);
    case "let":
      return find(e.type, pred) ?? find(e.value, pred) ?? find(e.body, pred);
    case "mdata":
    case "proj":
      return find(e.expr, pred);
    default:
      return undefined;
  }
}

/**
 * Bottom-up-ish rewrite: at each node `f` may return a replacement, or `null`
 * to recurse into the children and rebuild. Does not track binder depth.
 */
export function replace(e: Expr, f: (sub: Expr) => Expr | null): Expr {
  const r = f(e);
  if (r !== null) return r;
  return mapChildren(e, (child) => replace(child, f));
}

// --- de Bruijn operations (SPEC.md Section 3.2–3.4) -------------------------
//
// Faithful port of Lean's kernel `instantiate.cpp` / `abstract.cpp`. These are
// the most error-prone, soundness-critical functions in the kernel, so the
// offset arithmetic mirrors the reference exactly and is covered heavily by
// tests.
//
// Convention: in `instantiate`, `subst[i]` replaces loose `BVar i`. In
// `abstract`, `fvars[i]` becomes `BVar (n - 1 - i)`, so the last free variable
// becomes the innermost bound variable.

/**
 * Add `d` to every loose bound variable with index `>= s`. Binders encountered
 * during the descent raise the threshold. `looseBVarRange` lets us skip closed
 * subterms.
 */
export function liftLooseBVars(e: Expr, s: number, d: number): Expr {
  if (d === 0) return e;
  const go = (m: Expr, s: number): Expr => {
    if (m.looseBVarRange <= s) return m;
    if (m.kind === "bvar") return m.idx >= BigInt(s) ? mkBVar(m.idx + BigInt(d)) : m;
    return mapChildrenWithDepth(m, s, go);
  };
  return go(e, s);
}

/**
 * Subtract `d` from every loose bound variable with index `>= s`. The caller
 * must ensure no loose bvar lies in `[s, s + d)` (those would underflow). This
 * is exactly {@link liftLooseBVars} with a negated shift.
 */
export function lowerLooseBVars(e: Expr, s: number, d: number): Expr {
  return liftLooseBVars(e, s, -d);
}

/**
 * Substitute loose bound variables: `BVar i` ↦ `subst[i]` for `i < n`, and
 * `BVar j` ↦ `BVar (j - n)` for `j >= n` (the consumed binders are removed).
 * Substituted terms are lifted by the current binder depth.
 */
export function instantiate(e: Expr, subst: readonly Expr[]): Expr {
  const n = subst.length;
  if (n === 0) return e;
  const go = (m: Expr, depth: number): Expr => {
    if (m.looseBVarRange <= depth) return m;
    if (m.kind === "bvar") {
      if (m.idx < BigInt(depth)) return m;
      const j = Number(m.idx) - depth;
      if (j < n) return liftLooseBVars(subst[j]!, 0, depth);
      return mkBVar(m.idx - BigInt(n));
    }
    return mapChildrenWithDepth(m, depth, go);
  };
  return go(e, 0);
}

/** Substitute a single loose `BVar 0` with `v`, lowering the outer bvars. */
export function instantiate1(e: Expr, v: Expr): Expr {
  return instantiate(e, [v]);
}

/**
 * Like {@link instantiate} but with `subst` reversed: `BVar i` ↦
 * `subst[n - 1 - i]`. Matches Lean's `instantiateRev`, the natural pairing with
 * {@link abstract}.
 */
export function instantiateRev(e: Expr, subst: readonly Expr[]): Expr {
  const n = subst.length;
  if (n === 0) return e;
  const go = (m: Expr, depth: number): Expr => {
    if (m.looseBVarRange <= depth) return m;
    if (m.kind === "bvar") {
      if (m.idx < BigInt(depth)) return m;
      const j = Number(m.idx) - depth;
      if (j < n) return liftLooseBVars(subst[n - 1 - j]!, 0, depth);
      return mkBVar(m.idx - BigInt(n));
    }
    return mapChildrenWithDepth(m, depth, go);
  };
  return go(e, 0);
}

/**
 * Replace the free variables `fvars` with loose bound variables: `fvars[i]`
 * becomes `BVar (n - 1 - i)`, so the last free variable becomes `BVar 0`. Each
 * `fvars[i]` must be an `fvar` node. This is the inverse of {@link instantiate}
 * and is used when building `lam`/`pi`/`let`.
 */
export function abstract(e: Expr, fvars: readonly Expr[]): Expr {
  const n = fvars.length;
  if (n === 0 || !e.hasFVar) return e;
  const ids = fvars.map((f) => {
    if (f.kind !== "fvar") throw new Error(`abstract: expected an fvar, got ${f.kind}`);
    return f.id;
  });
  const go = (m: Expr, depth: number): Expr => {
    if (!m.hasFVar) return m;
    if (m.kind === "fvar") {
      for (let i = 0; i < n; i++) {
        if (nameEq(m.id, ids[i]!)) return mkBVar(BigInt(depth + n - 1 - i));
      }
      return m;
    }
    return mapChildrenWithDepth(m, depth, go);
  };
  return go(e, 0);
}

/**
 * Substitute universe parameters throughout an expression: every `Sort` and
 * `Const` level is rewritten with {@link levelInstantiate}. Used to specialize a
 * universe-polymorphic constant's type/value at a use site.
 */
export function instantiateLevelParams(
  e: Expr,
  params: readonly Name[],
  args: readonly Level[],
): Expr {
  if (params.length === 0) return e;
  // Level substitution ignores binder depth, so the threaded depth is unused.
  const go = (m: Expr): Expr => {
    switch (m.kind) {
      case "sort":
        return mkSort(levelInstantiate(m.level, params, args));
      case "const":
        return mkConst(m.name, m.levels.map((l) => levelInstantiate(l, params, args)));
      default:
        return mapChildrenWithDepth(m, 0, (child) => go(child));
    }
  };
  return go(e);
}
