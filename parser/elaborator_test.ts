import { assert, assertEquals, assertThrows } from "@std/assert";
import { parse, parseExpr } from "./parser.ts";
import { elabExpr, elaborate } from "./elaborator.ts";
import { ParseError } from "./syntax.ts";
import {
  anonymousName,
  exprEq,
  mkApp,
  mkBVar,
  mkConst,
  mkLambda,
  mkNatLit,
  mkPi,
  mkSort,
  nameFromString,
} from "../kernel/mod.ts";
import { levelZero, mkLevelLit, mkLevelParam } from "../kernel/level.ts";
import { Environment } from "../kernel/environment.ts";
import { TypeChecker } from "../kernel/type_checker.ts";
import { KernelError } from "../kernel/exception.ts";

const natC = mkConst(nameFromString("Nat"));
const x = nameFromString("x");
const y = nameFromString("y");

const elab = (src: string) => elabExpr(parseExpr(src), [], []);

Deno.test("lambda resolves bound names to de Bruijn indices", () => {
  assert(exprEq(elab("fun (x : Nat) => x"), mkLambda(x, natC, mkBVar(0n))));
  assert(exprEq(
    elab("fun (x : Nat) (y : Nat) => x"),
    mkLambda(x, natC, mkLambda(y, natC, mkBVar(1n))),
  ));
});

Deno.test("arrow shifts outer indices by its (anonymous) binder", () => {
  // fun (x : Nat) => Nat → x   — x sits under the arrow binder, so it is #1
  assert(exprEq(
    elab("fun (x : Nat) => Nat → x"),
    mkLambda(x, natC, mkPi(anonymousName, natC, mkBVar(1n))),
  ));
});

Deno.test("∀ and arrow desugar to Pi", () => {
  assert(exprEq(elab("∀ (x : Nat), Nat"), mkPi(x, natC, natC)));
  assert(exprEq(elab("Nat → Nat"), mkPi(anonymousName, natC, natC)));
});

Deno.test("sort sugar and literals", () => {
  assert(exprEq(elab("Type"), mkSort(mkLevelLit(1))));
  assert(exprEq(elab("Type 0"), mkSort(mkLevelLit(1)))); // Type 0 = Sort 1
  assert(exprEq(elab("Prop"), mkSort(levelZero)));
  assert(exprEq(elab("Sort 3"), mkSort(mkLevelLit(3))));
  assert(exprEq(elab("5"), mkNatLit(5n)));
});

Deno.test("free identifiers and universe arguments become constants", () => {
  assert(
    exprEq(
      elab("Nat.succ Nat.zero"),
      mkApp(mkConst(nameFromString("Nat.succ")), mkConst(nameFromString("Nat.zero"))),
    ),
  );
  assert(exprEq(
    elabExpr(parseExpr("Eq.{1}"), [], []),
    mkConst(nameFromString("Eq"), [mkLevelLit(1)]),
  ));
});

Deno.test("universe parameters resolve in scope", () => {
  assert(exprEq(
    elabExpr(parseExpr("Sort u"), [], ["u"]),
    mkSort(mkLevelParam(nameFromString("u"))),
  ));
});

Deno.test("elaboration errors carry positions", () => {
  // unknown universe parameter
  assertThrows(() => elabExpr(parseExpr("Sort u"), [], []), ParseError);
  // a bound variable cannot take universe arguments
  assertThrows(() => elabExpr(parseExpr("fun (x : Nat) => x.{1}"), [], []), ParseError);
});

Deno.test("def folds leading binders into Pi/Lambda", () => {
  const r = elaborate(parse("def idNat (x : Nat) : Nat := x")[0]!);
  assert(r.kind === "decl" && r.decl.kind === "definition");
  assert(exprEq(r.decl.type, mkPi(x, natC, natC)));
  assert(exprEq(r.decl.value, mkLambda(x, natC, mkBVar(0n))));
});

// --- end-to-end: parse → elaborate → drive into a kernel Environment ---------

/** A minimal driver (the standalone Driver module comes next). */
function run(src: string): Environment {
  let env = new Environment();
  for (const cmd of parse(src)) {
    const r = elaborate(cmd);
    switch (r.kind) {
      case "decl":
        env = env.addDecl(r.decl);
        break;
      case "inductive":
        env = env.addInductive(r.decl);
        break;
      case "initQuot":
        env = env.addQuot();
        break;
      case "check":
        new TypeChecker(env).infer(r.expr);
        break;
    }
  }
  return env;
}

const PRELUDE = `inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

axiom Nat.add : Nat → Nat → Nat

inductive Eq.{u} (α : Sort u) (a : α) : α → Prop where
  | refl : Eq.{u} α a a`;

Deno.test("end-to-end: a true theorem is accepted", () => {
  const env = run(
    `${PRELUDE}

theorem two_add_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5

#check two_add_three`,
  );
  assert(env.contains(nameFromString("two_add_three")));
  // the inductive elaboration produced the expected constants
  assertEquals(env.find(nameFromString("Eq.refl"))?.kind, "constructor");
  assertEquals(env.find(nameFromString("Nat.succ"))?.kind, "constructor");
});

Deno.test("end-to-end: a false theorem is rejected by the kernel", () => {
  const err = assertThrows(
    () => run(`${PRELUDE}\n\ntheorem bogus : Eq.{1} Nat 0 1 := Eq.refl.{1} Nat 0`),
    KernelError,
  );
  assertEquals((err as KernelError).errorKind, "typeMismatch");
});

Deno.test("end-to-end: List with a recursive constructor elaborates and reduces", () => {
  const env = run(`${PRELUDE}

inductive List.{u} (α : Type u) : Type u where
  | nil : List.{u} α
  | cons : α → List.{u} α → List.{u} α`);
  assertEquals(env.find(nameFromString("List.rec"))?.kind, "recursor");
  assertEquals(env.find(nameFromString("List.cons"))?.kind, "constructor");
});
