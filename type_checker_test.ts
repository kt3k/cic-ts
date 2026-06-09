import { assert, assertEquals, assertFalse, assertThrows } from "@std/assert";
import { nameFromString } from "./name.ts";
import { levelZero, mkLevelLit, mkLevelParam, mkLevelSucc } from "./level.ts";
import {
  type Expr,
  exprEq,
  mkApp,
  mkBVar,
  mkConst,
  mkLambda,
  mkLet,
  mkNatLit,
  mkPi,
  mkSort,
} from "./expr.ts";
import { mkAxiom, mkDefinition } from "./declaration.ts";
import { Environment } from "./environment.ts";
import { TypeChecker } from "./type_checker.ts";
import { KernelError } from "./exception.ts";

const type0 = mkSort(levelZero); // Prop
const type1 = mkSort(mkLevelLit(1)); // Type
const a = nameFromString("a");

const Nat = nameFromString("Nat");
const natZero = nameFromString("Nat.zero");
const natSucc = nameFromString("Nat.succ");
const natC = mkConst(Nat);

/** An environment with `Nat : Type`, `Nat.zero : Nat`, `Nat.succ : Nat → Nat`. */
function baseEnv(): Environment {
  let env = new Environment();
  env = env.addDecl(mkAxiom(Nat, [], type1));
  env = env.addDecl(mkAxiom(natZero, [], natC));
  env = env.addDecl(mkAxiom(natSucc, [], mkPi(a, natC, natC)));
  return env;
}

const succ = mkConst(natSucc);
const zero = mkConst(natZero);

Deno.test("infer: Sort u : Sort (u+1)", () => {
  const tc = new TypeChecker(new Environment());
  assert(exprEq(tc.infer(type0), mkSort(mkLevelSucc(levelZero))));
});

Deno.test("infer: constant and application", () => {
  const tc = new TypeChecker(baseEnv());
  assert(exprEq(tc.infer(zero), natC));
  // Nat.succ Nat.zero : Nat
  assert(exprEq(tc.infer(mkApp(succ, zero)), natC));
  // nested
  assert(exprEq(tc.infer(mkApp(succ, mkApp(succ, zero))), natC));
});

Deno.test("infer: lambda gets a Pi type", () => {
  const tc = new TypeChecker(baseEnv());
  // fun (x : Nat) => x   :   (x : Nat) → Nat
  const id = mkLambda(nameFromString("x"), natC, mkBVar(0n));
  assert(exprEq(tc.infer(id), mkPi(nameFromString("x"), natC, natC)));
});

Deno.test("infer: Pi type lives in imax of its parts", () => {
  const tc = new TypeChecker(baseEnv());
  // (x : Nat) → Nat : Type 1   (imax 1 1 = 1)
  assert(exprEq(tc.infer(mkPi(a, natC, natC)), type1));
  // (x : Nat) → Prop : Type 1  (imax 1 1)
  assert(exprEq(tc.infer(mkPi(a, natC, type0)), type1));
});

Deno.test("infer: let binds and substitutes the value", () => {
  const tc = new TypeChecker(baseEnv());
  // let x : Nat := Nat.zero; Nat.succ x   :   Nat
  const e = mkLet(nameFromString("x"), natC, zero, mkApp(succ, mkBVar(0n)));
  assert(exprEq(tc.infer(e), natC));
});

Deno.test("infer: literals", () => {
  const tc = new TypeChecker(baseEnv());
  assert(exprEq(tc.infer(mkNatLit(5n)), mkConst(Nat)));
});

Deno.test("infer rejects loose bound variables", () => {
  const tc = new TypeChecker(baseEnv());
  const err = assertThrows(() => tc.infer(mkBVar(0n)), KernelError);
  assertEquals((err as KernelError).errorKind, "looseBVar");
});

Deno.test("infer rejects ill-typed application", () => {
  const tc = new TypeChecker(baseEnv());
  // Nat.succ applied to a type — argument is not a Nat
  const err = assertThrows(() => tc.infer(mkApp(succ, type0)), KernelError);
  assertEquals((err as KernelError).errorKind, "typeMismatch");
});

Deno.test("infer rejects unknown constants", () => {
  const tc = new TypeChecker(new Environment());
  const err = assertThrows(() => tc.infer(mkConst(Nat)), KernelError);
  assertEquals((err as KernelError).errorKind, "unknownConstant");
});

Deno.test("addDecl accepts a well-typed definition", () => {
  let env = baseEnv();
  // def two : Nat := Nat.succ (Nat.succ Nat.zero)
  env = env.addDecl(
    mkDefinition(nameFromString("two"), [], natC, mkApp(succ, mkApp(succ, zero))),
  );
  assert(env.contains(nameFromString("two")));
});

Deno.test("addDecl rejects a value of the wrong type", () => {
  const env = baseEnv();
  const err = assertThrows(
    () => env.addDecl(mkDefinition(nameFromString("bad"), [], natC, type0)),
    KernelError,
  );
  assertEquals((err as KernelError).errorKind, "typeMismatch");
});

Deno.test("addDecl rejects redeclaration", () => {
  const env = baseEnv();
  const err = assertThrows(() => env.addDecl(mkAxiom(Nat, [], type1)), KernelError);
  assertEquals((err as KernelError).errorKind, "alreadyDeclared");
});

Deno.test("isDefEq: delta-unfolds definitions", () => {
  let env = baseEnv();
  const idName = nameFromString("idNat");
  const idBody = mkLambda(nameFromString("x"), natC, mkBVar(0n));
  env = env.addDecl(mkDefinition(idName, [], mkPi(a, natC, natC), idBody));
  const tc = new TypeChecker(env);
  // idNat ≡ fun (x : Nat) => x
  assert(tc.isDefEq(mkConst(idName), idBody));
  // idNat Nat.zero ≡ Nat.zero  (beta after delta)
  assert(tc.isDefEq(mkApp(mkConst(idName), zero), zero));
});

Deno.test("isDefEq: eta for functions", () => {
  let env = baseEnv();
  env = env.addDecl(mkAxiom(nameFromString("f"), [], mkPi(a, natC, natC)));
  const tc = new TypeChecker(env);
  const f = mkConst(nameFromString("f"));
  // f ≡ fun (x : Nat) => f x
  const etaF = mkLambda(nameFromString("x"), natC, mkApp(f, mkBVar(0n)));
  assert(tc.isDefEq(f, etaF));
});

Deno.test("isDefEq: proof irrelevance", () => {
  let env = baseEnv();
  const P = nameFromString("P");
  env = env.addDecl(mkAxiom(P, [], type0)); // P : Prop
  env = env.addDecl(mkAxiom(nameFromString("h1"), [], mkConst(P))); // h1 : P
  env = env.addDecl(mkAxiom(nameFromString("h2"), [], mkConst(P))); // h2 : P
  const tc = new TypeChecker(env);
  // two proofs of the same proposition are definitionally equal
  assert(tc.isDefEq(mkConst(nameFromString("h1")), mkConst(nameFromString("h2"))));
  // but two distinct Nats are not
  assertFalse(tc.isDefEq(zero, mkApp(succ, zero)));
});

Deno.test("universe-polymorphic identity", () => {
  let env = baseEnv();
  const u = mkLevelParam(nameFromString("u"));
  const uName = nameFromString("u");
  const alpha = nameFromString("α");
  const xn = nameFromString("x");
  // pid.{u} : (α : Sort u) → α → α := fun α x => x
  const pidType = mkPi(alpha, mkSort(u), mkPi(xn, mkBVar(0n), mkBVar(1n)));
  const pidValue = mkLambda(alpha, mkSort(u), mkLambda(xn, mkBVar(0n), mkBVar(0n)));
  const pid = nameFromString("pid");
  env = env.addDecl(mkDefinition(pid, [uName], pidType, pidValue));

  const tc = new TypeChecker(env);
  // pid.{1} Nat : Nat → Nat
  const pid1Nat: Expr = mkApp(mkConst(pid, [mkLevelLit(1)]), natC);
  assert(tc.isDefEq(tc.infer(pid1Nat), mkPi(a, natC, natC)));
  // pid.{1} Nat Nat.zero ≡ Nat.zero
  assert(tc.isDefEq(mkApp(pid1Nat, zero), zero));
  // pid.{0} Nat is ill-typed: Nat : Type 1, not Sort 0
  const err = assertThrows(
    () => tc.infer(mkApp(mkConst(pid, [levelZero]), natC)),
    KernelError,
  );
  assertEquals((err as KernelError).errorKind, "typeMismatch");
});
