// The core term representation (SPEC.md Section 2.3).
//
// Corresponds to Lean's `expr`. Bound variables use de Bruijn indices; the
// innermost binder is index 0. Phase 0 provides the representation,
// constructors (which precompute the cache flags), structural equality, and
// hashing. The de Bruijn operations themselves (instantiate/abstract) are
// Phase 1.

import { type Level, levelEq, levelHasMVar } from "./level.ts";
import { type Name, nameEq } from "./name.ts";
import { hashBigInt, hashString, mixHash } from "./hash.ts";

export type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit";

export type Literal =
  | { readonly kind: "natVal"; readonly value: bigint }
  | { readonly kind: "strVal"; readonly value: string };

/** Lightweight metadata map. Semantically transparent; ignored by the kernel. */
export type KVMap = ReadonlyMap<string, string | bigint | boolean>;

const EMPTY_KVMAP: KVMap = new Map();

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
    | { readonly kind: "lit"; readonly lit: Literal }
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
const HASH_LIT = 0xcc9e2d51;
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

/** A literal. */
export function mkLit(lit: Literal): Expr {
  const payload = lit.kind === "natVal" ? hashBigInt(lit.value) : hashString(lit.value);
  return {
    kind: "lit",
    lit,
    hash: mixHash(payload, HASH_LIT),
    hasFVar: false,
    hasMVar: false,
    hasLevelMVar: false,
    looseBVarRange: 0,
  };
}

/** Natural-number literal. */
export function mkNatLit(value: bigint): Expr {
  if (value < 0n) throw new Error(`mkNatLit: negative value ${value}`);
  return mkLit({ kind: "natVal", value });
}

/** String literal. */
export function mkStrLit(value: string): Expr {
  return mkLit({ kind: "strVal", value });
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

function literalEq(a: Literal, b: Literal): boolean {
  return a.kind === b.kind && a.value === (b as typeof a).value;
}

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
      return nameEq(a.id, (b as typeof a).id);
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
    case "lit":
      return literalEq(a.lit, (b as typeof a).lit);
    case "mdata":
      return kvmapEq(a.data, (b as typeof a).data) && exprEq(a.expr, (b as typeof a).expr);
    case "proj": {
      const bb = b as typeof a;
      return a.idx === bb.idx && nameEq(a.struct, bb.struct) && exprEq(a.expr, bb.expr);
    }
  }
}

export { EMPTY_KVMAP };
