// de Bruijn operations (SPEC.md Section 3.2–3.4).
//
// Faithful port of Lean's kernel `instantiate.cpp` / `abstract.cpp`. These are
// the most error-prone, soundness-critical functions in the kernel, so the
// offset arithmetic mirrors the reference exactly and is covered heavily by
// tests.
//
// Convention: in `instantiate`, `subst[i]` replaces loose `BVar i`. In
// `abstract`, `fvars[i]` becomes `BVar (n - 1 - i)`, so the last free variable
// becomes the innermost bound variable.

import { type Expr, mkApp, mkBVar, mkLambda, mkLet, mkMData, mkPi, mkProj } from "./expr.ts";
import { nameEq } from "./name.ts";

/**
 * Add `d` to every loose bound variable with index `>= s`. Binders encountered
 * during the descent raise the threshold. `looseBVarRange` lets us skip closed
 * subterms.
 */
export function liftLooseBVars(e: Expr, s: number, d: number): Expr {
  if (d === 0) return e;
  const go = (m: Expr, s: number): Expr => {
    if (m.looseBVarRange <= s) return m;
    switch (m.kind) {
      case "bvar":
        return m.idx >= BigInt(s) ? mkBVar(m.idx + BigInt(d)) : m;
      case "app":
        return mkApp(go(m.fn, s), go(m.arg, s));
      case "lam":
        return mkLambda(m.name, go(m.type, s), go(m.body, s + 1), m.info);
      case "pi":
        return mkPi(m.name, go(m.type, s), go(m.body, s + 1), m.info);
      case "let":
        return mkLet(m.name, go(m.type, s), go(m.value, s), go(m.body, s + 1));
      case "mdata":
        return mkMData(m.data, go(m.expr, s));
      case "proj":
        return mkProj(m.struct, m.idx, go(m.expr, s));
      default:
        return m;
    }
  };
  return go(e, s);
}

/**
 * Subtract `d` from every loose bound variable with index `>= s`. The caller
 * must ensure no loose bvar lies in `[s, s + d)` (those would underflow).
 */
export function lowerLooseBVars(e: Expr, s: number, d: number): Expr {
  if (d === 0) return e;
  const go = (m: Expr, s: number): Expr => {
    if (m.looseBVarRange <= s) return m;
    switch (m.kind) {
      case "bvar":
        return m.idx >= BigInt(s) ? mkBVar(m.idx - BigInt(d)) : m;
      case "app":
        return mkApp(go(m.fn, s), go(m.arg, s));
      case "lam":
        return mkLambda(m.name, go(m.type, s), go(m.body, s + 1), m.info);
      case "pi":
        return mkPi(m.name, go(m.type, s), go(m.body, s + 1), m.info);
      case "let":
        return mkLet(m.name, go(m.type, s), go(m.value, s), go(m.body, s + 1));
      case "mdata":
        return mkMData(m.data, go(m.expr, s));
      case "proj":
        return mkProj(m.struct, m.idx, go(m.expr, s));
      default:
        return m;
    }
  };
  return go(e, s);
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
    switch (m.kind) {
      case "bvar": {
        if (m.idx < BigInt(depth)) return m;
        const j = Number(m.idx) - depth;
        if (j < n) return liftLooseBVars(subst[j]!, 0, depth);
        return mkBVar(m.idx - BigInt(n));
      }
      case "app":
        return mkApp(go(m.fn, depth), go(m.arg, depth));
      case "lam":
        return mkLambda(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "pi":
        return mkPi(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "let":
        return mkLet(m.name, go(m.type, depth), go(m.value, depth), go(m.body, depth + 1));
      case "mdata":
        return mkMData(m.data, go(m.expr, depth));
      case "proj":
        return mkProj(m.struct, m.idx, go(m.expr, depth));
      default:
        return m;
    }
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
    switch (m.kind) {
      case "bvar": {
        if (m.idx < BigInt(depth)) return m;
        const j = Number(m.idx) - depth;
        if (j < n) return liftLooseBVars(subst[n - 1 - j]!, 0, depth);
        return mkBVar(m.idx - BigInt(n));
      }
      case "app":
        return mkApp(go(m.fn, depth), go(m.arg, depth));
      case "lam":
        return mkLambda(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "pi":
        return mkPi(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "let":
        return mkLet(m.name, go(m.type, depth), go(m.value, depth), go(m.body, depth + 1));
      case "mdata":
        return mkMData(m.data, go(m.expr, depth));
      case "proj":
        return mkProj(m.struct, m.idx, go(m.expr, depth));
      default:
        return m;
    }
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
    switch (m.kind) {
      case "fvar": {
        for (let i = 0; i < n; i++) {
          if (nameEq(m.id, ids[i]!)) return mkBVar(BigInt(depth + n - 1 - i));
        }
        return m;
      }
      case "app":
        return mkApp(go(m.fn, depth), go(m.arg, depth));
      case "lam":
        return mkLambda(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "pi":
        return mkPi(m.name, go(m.type, depth), go(m.body, depth + 1), m.info);
      case "let":
        return mkLet(m.name, go(m.type, depth), go(m.value, depth), go(m.body, depth + 1));
      case "mdata":
        return mkMData(m.data, go(m.expr, depth));
      case "proj":
        return mkProj(m.struct, m.idx, go(m.expr, depth));
      default:
        return m;
    }
  };
  return go(e, 0);
}
