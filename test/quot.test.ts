import { assert, assertEquals, assertThrows } from "@std/assert";
import { anonymousName, nameFromString } from "../src/name.ts";
import { levelZero, mkLevelLit, mkLevelParam } from "../src/level.ts";
import { mkApp, mkAppN, mkBVar, mkConst, mkPi, mkSort } from "../src/expr.ts";
import { Environment } from "../src/environment.ts";
import { TypeChecker } from "../src/typeChecker.ts";
import { mkAxiom } from "../src/declaration.ts";
import { quotIndName, quotLiftName, quotMkName, quotName } from "../src/quot.ts";
import { KernelError } from "../src/exception.ts";

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

/** Environment with Nat, Eq, and the Quot primitives. */
function quotEnv(): Environment {
  let env = new Environment();
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
  return env.addQuot();
}

Deno.test("addQuot declares the four primitives", () => {
  const env = quotEnv();
  assertEquals(env.find(quotName)?.kind, "quot");
  assertEquals(env.find(quotMkName)?.kind, "quot");
  assertEquals(env.find(quotLiftName)?.kind, "quot");
  assertEquals(env.find(quotIndName)?.kind, "quot");
  const lift = env.find(quotLiftName);
  assert(lift?.kind === "quot" && lift.quotKind === "lift");
});

Deno.test("addQuot requires Eq to be present", () => {
  const err = assertThrows(() => new Environment().addQuot(), KernelError);
  assertEquals((err as KernelError).errorKind, "other");
});

Deno.test("Quot.mk has type Quot α r", () => {
  let env = quotEnv();
  const r = nameFromString("r");
  env = env.addDecl(mkAxiom(r, [], mkPi(anon, natC, mkPi(anon, natC, type0))));
  const tc = new TypeChecker(env);
  const rC = mkConst(r);
  const mk = mkAppN(mkConst(quotMkName, [lit1]), [natC, rC, zero]);
  assert(tc.isDefEq(tc.infer(mk), mkAppN(mkConst(quotName, [lit1]), [natC, rC])));
});

Deno.test("Quot.lift computes: lift f h (mk a) ≡ f a", () => {
  let env = quotEnv();
  const r = nameFromString("r");
  env = env.addDecl(mkAxiom(r, [], mkPi(anon, natC, mkPi(anon, natC, type0))));
  const tc = new TypeChecker(env);
  const rC = mkConst(r);
  const mk = mkAppN(mkConst(quotMkName, [lit1]), [natC, rC, zero]);
  // h : the soundness premise — its type is irrelevant to the reduction rule.
  const h = tc.mkLocalDecl(nameFromString("h"), natC);
  const lift = mkAppN(
    mkConst(quotLiftName, [lit1, lit1]),
    [natC, rC, natC, succ, h, mk],
  );
  assert(tc.isDefEq(lift, mkApp(succ, zero)));
});

Deno.test("Quot.ind computes: ind h (mk a) ≡ h a", () => {
  let env = quotEnv();
  const r = nameFromString("r");
  env = env.addDecl(mkAxiom(r, [], mkPi(anon, natC, mkPi(anon, natC, type0))));
  const tc = new TypeChecker(env);
  const rC = mkConst(r);
  const mk = mkAppN(mkConst(quotMkName, [lit1]), [natC, rC, zero]);
  const beta = tc.mkLocalDecl(nameFromString("β"), natC);
  const hInd = tc.mkLocalDecl(nameFromString("h"), natC);
  const ind = mkAppN(mkConst(quotIndName, [lit1]), [natC, rC, beta, hInd, mk]);
  assert(tc.isDefEq(ind, mkApp(hInd, zero)));
});
