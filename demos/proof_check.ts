// Demo: checking a proof with the kernel.
//
// Curry–Howard: a proposition is a type, and a proof of it is a term of that
// type. "Checking a proof" is therefore just type-checking that term — exactly
// what `Environment.addDecl(mkTheorem(...))` does. If it returns without
// throwing, the proof is accepted; an ill-typed proof raises a KernelError.
//
// Run with:  deno run --allow-read demos/proof_check.ts

import { Environment } from "../environment.ts";
import { mkAxiom, mkTheorem } from "../declaration.ts";
import { nameFromString } from "../name.ts";
import { levelZero, mkLevelLit, mkLevelParam } from "../level.ts";
import { type Expr, mkAppN, mkBVar, mkConst, mkNatLit, mkPi, mkSort } from "../expr.ts";
import type { KernelError } from "../exception.ts";

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

// Declare the *type* of Nat.add; the kernel computes it via builtin arithmetic.
env = env.addDecl(mkAxiom(nameFromString("Nat.add"), [], mkPi(anon, natC, mkPi(anon, natC, natC))));

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
// The kernel reduces `Nat.add 2 3` to `5`, so the two are definitionally equal.
env = env.addDecl(mkTheorem(
  nameFromString("two_add_three"),
  [],
  eqNat(add(mkNatLit(2n), mkNatLit(3n)), mkNatLit(5n)),
  mkAppN(refl, [natC, mkNatLit(5n)]),
));
console.log("✓ proof of (2 + 3 = 5) accepted:", env.contains(nameFromString("two_add_three")));

// ── A false theorem: 0 = 1. The kernel rejects the bogus proof. ──────────────
try {
  env.addDecl(mkTheorem(
    nameFromString("bogus"),
    [],
    eqNat(mkNatLit(0n), mkNatLit(1n)),
    mkAppN(refl, [natC, mkNatLit(0n)]), // Eq.refl Nat 0 : Eq Nat 0 0, not Eq Nat 0 1
  ));
  console.log("✗ unreachable — a false proof was accepted!");
} catch (e) {
  console.log("✓ proof of (0 = 1) rejected:", (e as KernelError).errorKind);
}
