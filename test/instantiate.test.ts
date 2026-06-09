import { assert, assertEquals } from "@std/assert";
import { nameFromString } from "../src/name.ts";
import { type Expr, exprEq, mkApp, mkBVar, mkConst, mkFVar, mkLambda } from "../src/expr.ts";
import {
  abstract,
  instantiate,
  instantiate1,
  instantiateRev,
  liftLooseBVars,
  lowerLooseBVars,
} from "../src/instantiate.ts";

const nat = mkConst(nameFromString("Nat"));
const v = mkConst(nameFromString("v"));
const x = nameFromString("x");

Deno.test("liftLooseBVars shifts loose bvars at/above the threshold", () => {
  assert(exprEq(liftLooseBVars(mkBVar(0n), 0, 2), mkBVar(2n)));
  // below threshold is untouched
  assert(exprEq(liftLooseBVars(mkBVar(0n), 1, 2), mkBVar(0n)));
  // a binder raises the threshold: #0 is bound, stays; outer ref shifts
  const e = mkLambda(x, nat, mkApp(mkBVar(0n), mkBVar(1n)));
  const lifted = mkLambda(x, nat, mkApp(mkBVar(0n), mkBVar(3n)));
  assert(exprEq(liftLooseBVars(e, 0, 2), lifted));
});

Deno.test("lowerLooseBVars is the inverse of lifting", () => {
  const e = mkLambda(x, nat, mkApp(mkBVar(0n), mkBVar(3n)));
  const lowered = mkLambda(x, nat, mkApp(mkBVar(0n), mkBVar(1n)));
  assert(exprEq(lowerLooseBVars(e, 0, 2), lowered));
});

Deno.test("instantiate1: the five canonical cases", () => {
  // #0 ↦ v
  assert(exprEq(instantiate1(mkBVar(0n), v), v));
  // #1 ↦ #0 (outer bvar decremented)
  assert(exprEq(instantiate1(mkBVar(1n), v), mkBVar(0n)));
  // under a binder, #0 stays bound
  assert(exprEq(instantiate1(mkLambda(x, nat, mkBVar(0n)), v), mkLambda(x, nat, mkBVar(0n))));
  // under a binder, #1 is the target → v lifted by 1
  assert(exprEq(instantiate1(mkLambda(x, nat, mkBVar(1n)), v), mkLambda(x, nat, v)));
  // under a binder, #2 decrements to #1
  assert(exprEq(instantiate1(mkLambda(x, nat, mkBVar(2n)), v), mkLambda(x, nat, mkBVar(1n))));
});

Deno.test("instantiate1 lifts loose bvars inside the substituted term", () => {
  // substitute #1 (a loose bvar) under one binder; it must become #2
  const loose = mkBVar(1n);
  assert(exprEq(instantiate1(mkLambda(x, nat, mkBVar(1n)), loose), mkLambda(x, nat, mkBVar(2n))));
});

Deno.test("instantiate: subst[i] replaces BVar i", () => {
  const a = mkConst(nameFromString("a"));
  const b = mkConst(nameFromString("b"));
  // (#0 #1) with [a, b] → (a b)
  assert(exprEq(instantiate(mkApp(mkBVar(0n), mkBVar(1n)), [a, b]), mkApp(a, b)));
  // #2 with [a, b] → #0 (lowered by n=2)
  assert(exprEq(instantiate(mkBVar(2n), [a, b]), mkBVar(0n)));
});

Deno.test("instantiateRev: subst[n-1-i] replaces BVar i", () => {
  const a = mkConst(nameFromString("a"));
  const b = mkConst(nameFromString("b"));
  // (#0 #1) with rev [a, b] → (b a)
  assert(exprEq(instantiateRev(mkApp(mkBVar(0n), mkBVar(1n)), [a, b]), mkApp(b, a)));
});

Deno.test("abstract: last fvar becomes BVar 0", () => {
  const h = mkFVar(nameFromString("h"));
  const g = mkFVar(nameFromString("g"));
  // abstract over [h]: h ↦ #0
  assert(exprEq(abstract(h, [h]), mkBVar(0n)));
  // abstract over [h, g]: h ↦ #1, g ↦ #0
  assert(exprEq(abstract(mkApp(h, g), [h, g]), mkApp(mkBVar(1n), mkBVar(0n))));
  // under a binder, the index is offset by the binder depth
  assert(exprEq(abstract(mkLambda(x, nat, h), [h]), mkLambda(x, nat, mkBVar(1n))));
});

Deno.test("abstract then instantiate round-trips", () => {
  const h = mkFVar(nameFromString("h"));
  const body: Expr = mkApp(mkConst(nameFromString("f")), h);
  // λ-style: abstract h, then plug v back in
  const abstracted = abstract(body, [h]);
  assert(exprEq(instantiate1(abstracted, v), mkApp(mkConst(nameFromString("f")), v)));
});

Deno.test("instantiate leaves closed terms untouched (and identical)", () => {
  const closed = mkLambda(x, nat, mkBVar(0n));
  assertEquals(instantiate1(closed, v), closed); // same reference via looseBVarRange cutoff
});
