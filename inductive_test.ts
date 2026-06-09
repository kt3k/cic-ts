import { assert, assertEquals, assertThrows } from "@std/assert";
import { anonymousName, nameFromString } from "./name.ts";
import { levelZero, mkLevelLit, mkLevelParam, mkLevelSucc } from "./level.ts";
import {
  type Expr,
  mkApp,
  mkAppN,
  mkBVar,
  mkConst,
  mkLambda,
  mkNatLit,
  mkPi,
  mkSort,
} from "./expr.ts";
import { Environment } from "./environment.ts";
import { TypeChecker } from "./type_checker.ts";
import { mkRecName } from "./inductive.ts";
import { KernelError } from "./exception.ts";

const lit1 = mkLevelLit(1);
const type0 = mkSort(levelZero); // Prop
const type1 = mkSort(lit1); // Type
const anon = anonymousName;

const Nat = nameFromString("Nat");
const natZero = nameFromString("Nat.zero");
const natSucc = nameFromString("Nat.succ");
const natC = mkConst(Nat);
const zero = mkConst(natZero);
const succ = mkConst(natSucc);

function addNat(env: Environment): Environment {
  return env.addInductive({
    levelParams: [],
    numParams: 0,
    isUnsafe: false,
    types: [{
      name: Nat,
      type: type1,
      ctors: [
        { name: natZero, type: natC },
        { name: natSucc, type: mkPi(anon, natC, natC) },
      ],
    }],
  });
}

Deno.test("inductive: Nat declares type, constructors, and recursor", () => {
  const env = addNat(new Environment());
  assertEquals(env.find(Nat)?.kind, "inductive");
  assertEquals(env.find(natZero)?.kind, "constructor");
  assertEquals(env.find(natSucc)?.kind, "constructor");
  assertEquals(env.find(mkRecName(Nat))?.kind, "recursor");

  const tc = new TypeChecker(env);
  assert(tc.isDefEq(tc.infer(zero), natC));
  assert(tc.isDefEq(tc.infer(mkApp(succ, zero)), natC));
});

Deno.test("inductive: Nat.rec reduces (ι) on constructors", () => {
  const env = addNat(new Environment());
  const tc = new TypeChecker(env);
  const x = nameFromString("x");
  const ih = nameFromString("ih");
  // Nat.rec.{1} with motive (fun _ => Nat) computing the identity:
  //   zero ↦ zero,  succ n ↦ succ ih
  const motive = mkLambda(x, natC, natC);
  const sCase = mkLambda(x, natC, mkLambda(ih, natC, mkApp(succ, mkBVar(0n))));
  const recId = (n: Expr): Expr =>
    mkAppN(mkConst(mkRecName(Nat), [lit1]), [motive, zero, sCase, n]);

  const two = mkApp(succ, mkApp(succ, zero));
  assert(tc.isDefEq(recId(zero), zero));
  assert(tc.isDefEq(recId(mkApp(succ, zero)), mkApp(succ, zero)));
  assert(tc.isDefEq(recId(two), two));
  // and the recursor type is correct: inferring the application yields `motive t`
  assert(tc.isDefEq(tc.infer(recId(two)), natC));
});

Deno.test("inductive: Nat.rec reduces on Nat literals", () => {
  const env = addNat(new Environment());
  const tc = new TypeChecker(env);
  const x = nameFromString("x");
  const ih = nameFromString("ih");
  const motive = mkLambda(x, natC, natC);
  const sCase = mkLambda(x, natC, mkLambda(ih, natC, mkApp(succ, mkBVar(0n))));
  const recId = (n: Expr): Expr =>
    mkAppN(mkConst(mkRecName(Nat), [lit1]), [motive, zero, sCase, n]);
  const two = mkApp(succ, mkApp(succ, zero));
  assert(tc.isDefEq(recId(mkNatLit(2n)), two));
});

Deno.test("inductive: Bool with two nullary constructors", () => {
  const Bool = nameFromString("Bool");
  const tt = nameFromString("Bool.true");
  const ff = nameFromString("Bool.false");
  const boolC = mkConst(Bool);
  let env = new Environment();
  env = env.addInductive({
    levelParams: [],
    numParams: 0,
    isUnsafe: false,
    types: [{
      name: Bool,
      type: type1,
      ctors: [{ name: tt, type: boolC }, { name: ff, type: boolC }],
    }],
  });
  const b = nameFromString("b");
  // Bool.rec.{1} motive ct cf : maps true ↦ ct, false ↦ cf
  const motive = mkLambda(b, boolC, natC);
  const rec = (x: Expr): Expr =>
    mkAppN(mkConst(mkRecName(Bool), [lit1]), [motive, zero, mkApp(succ, zero), x]);
  // need Nat in env for the motive target
  env = addNat(env);
  const tc2 = new TypeChecker(env);
  assert(tc2.isDefEq(rec(mkConst(tt)), zero));
  assert(tc2.isDefEq(rec(mkConst(ff)), mkApp(succ, zero)));
});

Deno.test("inductive: List with a parameter and a recursive field", () => {
  const u = nameFromString("u");
  const uL = mkLevelParam(u);
  const List = nameFromString("List");
  const nil = nameFromString("List.nil");
  const cons = nameFromString("List.cons");
  const listU = mkConst(List, [uL]);
  const typeU = mkSort(mkLevelSucc(uL)); // Type u = Sort (u+1)

  let env = addNat(new Environment());
  env = env.addInductive({
    levelParams: [u],
    numParams: 1,
    isUnsafe: false,
    types: [{
      name: List,
      type: mkPi(nameFromString("α"), typeU, typeU), // (α : Type u) → Type u
      ctors: [
        { name: nil, type: mkPi(nameFromString("α"), typeU, mkApp(listU, mkBVar(0n))) },
        {
          name: cons,
          type: mkPi(
            nameFromString("α"),
            typeU,
            mkPi(
              nameFromString("h"),
              mkBVar(0n), // α
              mkPi(
                nameFromString("t"),
                mkApp(listU, mkBVar(1n)), // List α
                mkApp(listU, mkBVar(2n)), // List α
              ),
            ),
          ),
        },
      ],
    }],
  });
  assertEquals(env.find(mkRecName(List))?.kind, "recursor");

  const tc = new TypeChecker(env);
  // List Nat uses u := 0 (Nat : Type 0). List.rec.{1, 0} computes length into Nat:
  //   nil ↦ 0,  cons h t ih ↦ succ ih
  const recName = mkRecName(List);
  const listNat = mkConst(List, [levelZero]);
  const motive = mkLambda(nameFromString("l"), mkApp(listNat, natC), natC);
  const consCase = mkLambda(
    nameFromString("h"),
    natC,
    mkLambda(
      nameFromString("t"),
      mkApp(listNat, natC),
      mkLambda(nameFromString("ih"), natC, mkApp(succ, mkBVar(0n))),
    ),
  );
  // length [zero] = 1
  const nilNat = mkApp(mkConst(nil, [levelZero]), natC);
  const oneElem = mkAppN(mkConst(cons, [levelZero]), [natC, zero, nilNat]);
  const length = (l: Expr): Expr =>
    mkAppN(mkConst(recName, [lit1, levelZero]), [natC, motive, zero, consCase, l]);
  assert(tc.isDefEq(length(nilNat), zero));
  assert(tc.isDefEq(length(oneElem), mkApp(succ, zero)));
});

Deno.test("inductive: Eq with K-like reduction", () => {
  const u = nameFromString("u");
  const uL = mkLevelParam(u);
  const Eq = nameFromString("Eq");
  const refl = nameFromString("Eq.refl");
  const eqU = mkConst(Eq, [uL]);
  const sortU = mkSort(uL);

  let env = addNat(new Environment());
  env = env.addInductive({
    levelParams: [u],
    numParams: 2, // α and a
    isUnsafe: false,
    types: [{
      name: Eq,
      // (α : Sort u) → α → α → Prop
      type: mkPi(
        nameFromString("α"),
        sortU,
        mkPi(nameFromString("a"), mkBVar(0n), mkPi(nameFromString("b"), mkBVar(1n), type0)),
      ),
      ctors: [{
        name: refl,
        // (α : Sort u) → (a : α) → Eq α a a
        type: mkPi(
          nameFromString("α"),
          sortU,
          mkPi(nameFromString("a"), mkBVar(0n), mkAppN(eqU, [mkBVar(1n), mkBVar(0n), mkBVar(0n)])),
        ),
      }],
    }],
  });
  const recVal = env.find(mkRecName(Eq));
  assertEquals(recVal?.kind, "recursor");
  assert(recVal?.kind === "recursor" && recVal.k); // K-like

  const tc = new TypeChecker(env);
  const recName = mkRecName(Eq);
  // motive : (b : Nat) → Eq Nat zero b → Nat
  const eqNat = (b: Expr) => mkAppN(mkConst(Eq, [lit1]), [natC, zero, b]);
  const motive = mkLambda(
    nameFromString("b"),
    natC,
    mkLambda(nameFromString("h"), eqNat(mkBVar(0n)), natC),
  );
  const reflNatZero = mkAppN(mkConst(refl, [lit1]), [natC, zero]);
  // Eq.rec on the actual refl proof reduces to the refl case.
  const recOnRefl = mkAppN(
    mkConst(recName, [lit1, lit1]),
    [natC, zero, motive, zero, zero, reflNatZero],
  );
  assert(tc.isDefEq(recOnRefl, zero));

  // K-like reduction: a *variable* proof of `Eq Nat zero zero` still reduces.
  const h = tc.mkLocalDecl(nameFromString("h"), eqNat(zero));
  const recOnVar = mkAppN(
    mkConst(recName, [lit1, lit1]),
    [natC, zero, motive, zero, zero, h],
  );
  assert(tc.isDefEq(recOnVar, zero));
});

Deno.test("inductive rejects non-positive occurrences", () => {
  const Bad = nameFromString("Bad");
  const badC = mkConst(Bad);
  const err = assertThrows(
    () =>
      new Environment().addInductive({
        levelParams: [],
        numParams: 0,
        isUnsafe: false,
        types: [{
          name: Bad,
          type: type1,
          // Bad.mk : (Bad → Bad) → Bad   -- Bad occurs negatively
          ctors: [{
            name: nameFromString("Bad.mk"),
            type: mkPi(anon, mkPi(anon, badC, badC), badC),
          }],
        }],
      }),
    KernelError,
  );
  assertEquals((err as KernelError).errorKind, "other");
});

Deno.test("inductive rejects fields whose universe is too big", () => {
  const Foo = nameFromString("Foo");
  const fooC = mkConst(Foo);
  const err = assertThrows(
    () =>
      new Environment().addInductive({
        levelParams: [],
        numParams: 0,
        isUnsafe: false,
        types: [{
          name: Foo,
          type: type1, // Foo : Type
          // Foo.mk : Type → Foo   -- field lives in Type 1, too big for Type 0-level Foo
          ctors: [{ name: nameFromString("Foo.mk"), type: mkPi(anon, type1, fooC) }],
        }],
      }),
    KernelError,
  );
  assertEquals((err as KernelError).errorKind, "universeMismatch");
});
