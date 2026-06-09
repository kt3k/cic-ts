import { assert, assertFalse } from "@std/assert";
import { anonymousName, nameFromString } from "./name.ts";
import { mkLevelLit } from "./level.ts";
import { type Expr, mkApp, mkAppN, mkConst, mkNatLit, mkPi, mkSort } from "./expr.ts";
import { Environment } from "./environment.ts";
import { TypeChecker } from "./type_checker.ts";

const type1 = mkSort(mkLevelLit(1));
const anon = anonymousName;
const Nat = nameFromString("Nat");
const natC = mkConst(Nat);
const natZero = nameFromString("Nat.zero");
const natSucc = nameFromString("Nat.succ");
const zero = mkConst(natZero);
const succ = mkConst(natSucc);

/** Environment with Nat and Bool (for comparison results). */
function env(): Environment {
  let e = new Environment();
  e = e.addInductive({
    levelParams: [],
    numParams: 0,
    isUnsafe: false,
    types: [{
      name: Nat,
      type: type1,
      ctors: [{ name: natZero, type: natC }, { name: natSucc, type: mkPi(anon, natC, natC) }],
    }],
  });
  const Bool = nameFromString("Bool");
  const boolC = mkConst(Bool);
  e = e.addInductive({
    levelParams: [],
    numParams: 0,
    isUnsafe: false,
    types: [{
      name: Bool,
      type: type1,
      ctors: [
        { name: nameFromString("Bool.true"), type: boolC },
        { name: nameFromString("Bool.false"), type: boolC },
      ],
    }],
  });
  return e;
}

const tc = new TypeChecker(env());
const bin = (op: string, a: bigint, b: bigint): Expr =>
  mkAppN(mkConst(nameFromString(op)), [mkNatLit(a), mkNatLit(b)]);

Deno.test("Nat.succ on a literal collapses to a literal", () => {
  assert(tc.isDefEq(mkApp(succ, mkNatLit(4n)), mkNatLit(5n)));
  // succ (succ zero) ≡ 2  -- constructor form meets literal form
  assert(tc.isDefEq(mkApp(succ, mkApp(succ, zero)), mkNatLit(2n)));
});

Deno.test("Nat arithmetic on literals", () => {
  assert(tc.isDefEq(bin("Nat.add", 20n, 22n), mkNatLit(42n)));
  assert(tc.isDefEq(bin("Nat.sub", 5n, 8n), mkNatLit(0n))); // truncated
  assert(tc.isDefEq(bin("Nat.sub", 10n, 3n), mkNatLit(7n)));
  assert(tc.isDefEq(bin("Nat.mul", 6n, 7n), mkNatLit(42n)));
  assert(tc.isDefEq(bin("Nat.div", 17n, 5n), mkNatLit(3n)));
  assert(tc.isDefEq(bin("Nat.div", 1n, 0n), mkNatLit(0n))); // div by zero = 0
  assert(tc.isDefEq(bin("Nat.mod", 17n, 5n), mkNatLit(2n)));
  assert(tc.isDefEq(bin("Nat.mod", 7n, 0n), mkNatLit(7n))); // mod by zero = n
  assert(tc.isDefEq(bin("Nat.pow", 2n, 10n), mkNatLit(1024n)));
  assert(tc.isDefEq(bin("Nat.gcd", 12n, 18n), mkNatLit(6n)));
});

Deno.test("Nat bitwise operations on literals", () => {
  assert(tc.isDefEq(bin("Nat.land", 12n, 10n), mkNatLit(8n)));
  assert(tc.isDefEq(bin("Nat.lor", 12n, 10n), mkNatLit(14n)));
  assert(tc.isDefEq(bin("Nat.xor", 12n, 10n), mkNatLit(6n)));
  assert(tc.isDefEq(bin("Nat.shiftLeft", 1n, 4n), mkNatLit(16n)));
  assert(tc.isDefEq(bin("Nat.shiftRight", 100n, 2n), mkNatLit(25n)));
});

Deno.test("Nat comparisons reduce to Bool constructors", () => {
  assert(tc.isDefEq(bin("Nat.beq", 7n, 7n), mkConst(nameFromString("Bool.true"))));
  assert(tc.isDefEq(bin("Nat.beq", 7n, 8n), mkConst(nameFromString("Bool.false"))));
  assert(tc.isDefEq(bin("Nat.ble", 3n, 5n), mkConst(nameFromString("Bool.true"))));
  assert(tc.isDefEq(bin("Nat.ble", 5n, 3n), mkConst(nameFromString("Bool.false"))));
});

Deno.test("builtins compose and respect Nat.zero as a literal", () => {
  // (2 + 3) * (10 - 4) = 30
  const e = mkAppN(mkConst(nameFromString("Nat.mul")), [
    bin("Nat.add", 2n, 3n),
    bin("Nat.sub", 10n, 4n),
  ]);
  assert(tc.isDefEq(e, mkNatLit(30n)));
  // Nat.zero counts as the literal 0
  assert(
    tc.isDefEq(mkAppN(mkConst(nameFromString("Nat.add")), [zero, mkNatLit(9n)]), mkNatLit(9n)),
  );
  // distinct results are not defeq
  assertFalse(tc.isDefEq(bin("Nat.add", 1n, 1n), mkNatLit(3n)));
});
