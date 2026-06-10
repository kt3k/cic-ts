import { assert, assertEquals, assertFalse } from "@std/assert";
import { nameFromString } from "./name.ts";
import { mkLevelLit, mkLevelMVar } from "./level.ts";
import {
  abstract,
  type Expr,
  exprEq,
  find,
  forEach,
  instantiate,
  instantiate1,
  instantiateRev,
  liftLooseBVars,
  lowerLooseBVars,
  mapChildren,
  mkApp,
  mkAppN,
  mkBVar,
  mkConst,
  mkFVar,
  mkLambda,
  mkLet,
  mkMVar,
  mkNatLit,
  mkPi,
  mkProj,
  mkSort,
  mkStrLit,
  replace,
} from "./expr.ts";

const nat = mkConst(nameFromString("Nat"));
const v = mkConst(nameFromString("v"));
const x = nameFromString("x");

// --- constructors, cache flags, structural equality ---

Deno.test("constructors set the discriminant", () => {
  assertEquals(mkBVar(0n).kind, "bvar");
  assertEquals(mkSort(mkLevelLit(1)).kind, "sort");
  assertEquals(mkApp(nat, nat).kind, "app");
});

Deno.test("mkAppN is left-associated", () => {
  const f = mkConst(nameFromString("f"));
  const a = mkConst(nameFromString("a"));
  const b = mkConst(nameFromString("b"));
  assert(exprEq(mkAppN(f, [a, b]), mkApp(mkApp(f, a), b)));
});

Deno.test("looseBVarRange: bvar is index + 1", () => {
  assertEquals(mkBVar(0n).looseBVarRange, 1);
  assertEquals(mkBVar(3n).looseBVarRange, 4);
  assertEquals(nat.looseBVarRange, 0);
});

Deno.test("looseBVarRange: a binder closes one level", () => {
  // fun (x : Nat) => x      -- body bvar 0 is bound; closed term
  const id = mkLambda(x, nat, mkBVar(0n));
  assertEquals(id.looseBVarRange, 0);

  // fun (x : Nat) => #1     -- body bvar 1 escapes one binder → loose range 1
  const escapes = mkLambda(x, nat, mkBVar(1n));
  assertEquals(escapes.looseBVarRange, 1);
});

Deno.test("looseBVarRange: combines across app and respects binder depth", () => {
  // (#0 #2) under no binder → range 3
  assertEquals(mkApp(mkBVar(0n), mkBVar(2n)).looseBVarRange, 3);
  // fun => (#0 #2): inside one binder; outer range = max(1,3) - 1 = 2
  const body = mkApp(mkBVar(0n), mkBVar(2n));
  assertEquals(mkLambda(x, nat, body).looseBVarRange, 2);
});

Deno.test("looseBVarRange: let binds only in body", () => {
  // let x : Nat := #0; #0   -- value #0 is loose (range 1), body #0 is bound
  const e = mkLet(x, nat, mkBVar(0n), mkBVar(0n));
  assertEquals(e.looseBVarRange, 1);
});

Deno.test("flag propagation: hasFVar / hasMVar / hasLevelMVar", () => {
  const fv = mkFVar(nameFromString("h"));
  const mv = mkMVar(nameFromString("?m"));
  const sortM = mkSort(mkLevelMVar(nameFromString("?u")));

  assert(mkApp(nat, fv).hasFVar);
  assertFalse(mkApp(nat, nat).hasFVar);

  assert(mkApp(nat, mv).hasMVar);
  assertFalse(mkApp(nat, fv).hasMVar);

  assert(mkPi(x, sortM, nat).hasLevelMVar);
  assert(mkConst(nameFromString("C"), [mkLevelMVar(nameFromString("?u"))]).hasLevelMVar);
  assertFalse(mkConst(nameFromString("C"), [mkLevelLit(0)]).hasLevelMVar);
});

Deno.test("structural equality is exact", () => {
  const a: Expr = mkLambda(x, nat, mkBVar(0n));
  const b: Expr = mkLambda(x, nat, mkBVar(0n));
  assert(exprEq(a, b));

  // different binder info → not structurally equal
  const c = mkLambda(x, nat, mkBVar(0n), "implicit");
  assertFalse(exprEq(a, c));

  // different body
  assertFalse(exprEq(a, mkLambda(x, nat, mkBVar(1n))));

  // literals
  assert(exprEq(mkNatLit(5n), mkNatLit(5n)));
  assertFalse(exprEq(mkNatLit(5n), mkNatLit(6n)));
  assertFalse(exprEq(mkNatLit(5n), mkStrLit("5")));
});

Deno.test("equal exprs have equal hashes", () => {
  const mk = () => mkPi(x, nat, mkProj(nameFromString("S"), 0n, mkBVar(0n)));
  assertEquals(mk().hash, mk().hash);
});

// --- generic traversal (forEach / find / replace / mapChildren) ---

Deno.test("forEach visits every subexpression", () => {
  const e = mkApp(mkConst(nameFromString("f")), mkApp(mkBVar(0n), nat));
  let count = 0;
  forEach(e, () => count++);
  // app, f, app, bvar, Nat
  assertEquals(count, 5);
});

Deno.test("find returns the first matching subexpression", () => {
  const e = mkApp(mkConst(nameFromString("f")), mkFVar(nameFromString("h")));
  const found = find(e, (s) => s.kind === "fvar");
  assert(found !== undefined && found.kind === "fvar");
});

Deno.test("find returns undefined when nothing matches", () => {
  const e = mkApp(nat, nat);
  assertEquals(find(e, (s) => s.kind === "mvar"), undefined);
});

Deno.test("replace rewrites matched nodes and recurses elsewhere", () => {
  const fname = nameFromString("f");
  const f = mkConst(fname);
  const g = mkConst(nameFromString("g"));
  const e = mkApp(f, mkApp(f, nat));
  // replace every `f` with `g`
  const out = replace(e, (s) => (s.kind === "const" && s.name === fname ? g : null));
  assert(exprEq(out, mkApp(g, mkApp(g, nat))));
});

Deno.test("mapChildren rebuilds with mapped immediate children only", () => {
  const e: Expr = mkLambda(x, nat, mkBVar(0n));
  const out = mapChildren(e, () => nat);
  assert(exprEq(out, mkLambda(x, nat, nat)));
});

// --- de Bruijn operations (lift / lower / instantiate / abstract) ---

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
