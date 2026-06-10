// Demo: checking a proof with the kernel.
//
// Curry–Howard: a proposition is a type, and a proof of it is a term of that
// type. "Checking a proof" is therefore just type-checking that term — exactly
// what `Environment.addDecl(mkTheorem(...))` does. If it returns without
// throwing, the proof is accepted; an ill-typed proof raises a KernelError.
//
// Run with:  deno run --allow-read demos/proof_check.ts

import { Environment } from "../kernel/environment.ts";
import { mkDefinition, mkTheorem } from "../kernel/declaration.ts";
import { nameFromString } from "../kernel/name.ts";
import { levelZero, mkLevelLit, mkLevelParam } from "../kernel/level.ts";
import {
  type Expr,
  mkApp,
  mkAppN,
  mkBVar,
  mkConst,
  mkLambda,
  mkPi,
  mkSort,
} from "../kernel/expr.ts";
import { mkRecName } from "../kernel/inductive.ts";
import type { KernelError } from "../kernel/exception.ts";

const lit1 = mkLevelLit(1);
const type1 = mkSort(lit1); // Type
const type0 = mkSort(levelZero); // Prop
const anon = nameFromString("");

const Nat = nameFromString("Nat");
const natC = mkConst(Nat);
const natZero = nameFromString("Nat.zero");
const natSucc = nameFromString("Nat.succ");

let env = new Environment();

// Nat as a real inductive type (gives us Nat.zero, Nat.succ, Nat.rec).
env = env.addInductive({
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

// Nat.add defined from the recursor, by recursion on the second argument:
//   fun (a b : Nat) => Nat.rec.{1} (fun (n : Nat) => Nat) a (fun (n ih : Nat) => Nat.succ ih) b
const succC = mkConst(natSucc);
const natAddValue = mkLambda(
  nameFromString("a"),
  natC,
  mkLambda(
    nameFromString("b"),
    natC,
    mkAppN(mkConst(mkRecName(Nat), [lit1]), [
      mkLambda(nameFromString("n"), natC, natC), // motive
      mkBVar(1n), // zero case: a
      mkLambda(
        nameFromString("n"),
        natC,
        mkLambda(nameFromString("ih"), natC, mkApp(succC, mkBVar(0n))),
      ),
      mkBVar(0n), // major premise: b
    ]),
  ),
);
env = env.addDecl(mkDefinition(
  nameFromString("Nat.add"),
  [],
  mkPi(anon, natC, mkPi(anon, natC, natC)),
  natAddValue,
));

/** The Peano numeral `n`: `Nat.succ (… (Nat.zero))`. */
function nat(n: bigint): Expr {
  let e: Expr = mkConst(natZero);
  for (let i = 0n; i < n; i++) e = mkApp(succC, e);
  return e;
}

// Eq as an inductive: Eq.{u} (α : Sort u) (a : α) : α → Prop, with refl.
const u = nameFromString("u");
const uL = mkLevelParam(u);
const Eq = nameFromString("Eq");
const eqU = mkConst(Eq, [uL]);
env = env.addInductive({
  levelParams: [u],
  numParams: 2,
  isUnsafe: false,
  types: [{
    name: Eq,
    type: mkPi(
      nameFromString("α"),
      mkSort(uL),
      mkPi(nameFromString("a"), mkBVar(0n), mkPi(nameFromString("b"), mkBVar(1n), type0)),
    ),
    ctors: [{
      name: nameFromString("Eq.refl"),
      type: mkPi(
        nameFromString("α"),
        mkSort(uL),
        mkPi(nameFromString("a"), mkBVar(0n), mkAppN(eqU, [mkBVar(1n), mkBVar(0n), mkBVar(0n)])),
      ),
    }],
  }],
});

const refl = mkConst(nameFromString("Eq.refl"), [lit1]);
const eqNat = (a: Expr, b: Expr): Expr => mkAppN(mkConst(Eq, [lit1]), [natC, a, b]);
const add = (a: Expr, b: Expr): Expr => mkAppN(mkConst(nameFromString("Nat.add")), [a, b]);

// ── A true theorem: 2 + 3 = 5, proved by `Eq.refl Nat 5`. ────────────────────
// Proposition (type): Eq Nat (Nat.add 2 3) 5
// Proof (term):       Eq.refl Nat 5 : Eq Nat 5 5
// The kernel reduces `Nat.add 2 3` to `5` by δ/β/ι, so the two are
// definitionally equal.
env = env.addDecl(mkTheorem(
  nameFromString("two_add_three"),
  [],
  eqNat(add(nat(2n), nat(3n)), nat(5n)),
  mkAppN(refl, [natC, nat(5n)]),
));
console.log("✓ proof of (2 + 3 = 5) accepted:", env.contains(nameFromString("two_add_three")));

// ── A false theorem: 0 = 1. The kernel rejects the bogus proof. ──────────────
try {
  env.addDecl(mkTheorem(
    nameFromString("bogus"),
    [],
    eqNat(nat(0n), nat(1n)),
    mkAppN(refl, [natC, nat(0n)]), // Eq.refl Nat 0 : Eq Nat 0 0, not Eq Nat 0 1
  ));
  console.log("✗ unreachable — a false proof was accepted!");
} catch (e) {
  console.log("✓ proof of (0 = 1) rejected:", (e as KernelError).errorKind);
}
