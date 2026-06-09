import { assert, assertEquals, assertFalse } from "@std/assert";
import { nameFromString } from "./name.ts";
import { mkLevelLit, mkLevelMVar } from "./level.ts";
import {
  type Expr,
  exprEq,
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
} from "./expr.ts";

const nat = mkConst(nameFromString("Nat"));
const x = nameFromString("x");

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
