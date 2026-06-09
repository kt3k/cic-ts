// Traversal combinators (SPEC.md Section 3.1).
//
// Generic structural traversals over `Expr`. These do NOT track binder depth or
// touch de Bruijn indices; for capture-aware operations use `instantiate.ts`.

import { type Expr, mkApp, mkLambda, mkLet, mkMData, mkPi, mkProj } from "./expr.ts";

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
      return e; // bvar, fvar, mvar, sort, const, lit: no subexpressions
  }
}

/**
 * Like {@link mapChildren} but threads a binder depth: `g` is called with
 * `depth + 1` under each binder body and `depth` elsewhere. Used by the
 * capture-aware de Bruijn operations in `instantiate.ts`.
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
      return e; // bvar, fvar, mvar, sort, const, lit: no subexpressions
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
