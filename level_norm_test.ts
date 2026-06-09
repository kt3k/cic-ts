import { assert, assertEquals, assertFalse } from "@std/assert";
import { nameFromString } from "./name.ts";
import {
  isExplicit,
  isNotZero,
  type Level,
  levelGeq,
  levelInstantiate,
  levelIsEquiv,
  levelLeq,
  levelZero,
  mkLevelIMax,
  mkLevelLit,
  mkLevelMax,
  mkLevelParam,
  mkLevelSucc,
  normalizeLevel,
  toOffset,
} from "./level.ts";

const u = mkLevelParam(nameFromString("u"));
const w = mkLevelParam(nameFromString("v"));

Deno.test("toOffset / isExplicit", () => {
  const [base, k] = toOffset(mkLevelSucc(mkLevelSucc(u)));
  assertEquals(k, 2);
  assert(levelIsEquiv(base, u));
  assert(isExplicit(mkLevelLit(3)));
  assertFalse(isExplicit(mkLevelSucc(u)));
});

Deno.test("isNotZero", () => {
  assert(isNotZero(mkLevelSucc(u)));
  assert(isNotZero(mkLevelIMax(u, mkLevelSucc(w))));
  assertFalse(isNotZero(u));
  assertFalse(isNotZero(mkLevelIMax(mkLevelSucc(u), w)));
});

Deno.test("max is commutative and idempotent up to equivalence", () => {
  assert(levelIsEquiv(mkLevelMax(u, w), mkLevelMax(w, u)));
  assert(levelIsEquiv(mkLevelMax(u, u), u));
});

Deno.test("max absorbs smaller explicit offsets", () => {
  // max (u+1) (u) ≡ u+1
  assert(levelIsEquiv(mkLevelMax(mkLevelSucc(u), u), mkLevelSucc(u)));
  // max 0 u ≡ u
  assert(levelIsEquiv(mkLevelMax(levelZero, u), u));
});

Deno.test("succ distributes over max under normalization", () => {
  // succ (max u v) ≡ max (succ u) (succ v)
  assert(levelIsEquiv(mkLevelSucc(mkLevelMax(u, w)), mkLevelMax(mkLevelSucc(u), mkLevelSucc(w))));
});

Deno.test("imax with zero right operand is zero", () => {
  // imax u 0 ≡ 0
  assert(levelIsEquiv(mkLevelIMax(u, levelZero), levelZero));
  // imax u (v+1) ≡ max u (v+1)
  assert(levelIsEquiv(mkLevelIMax(u, mkLevelSucc(w)), mkLevelMax(u, mkLevelSucc(w))));
});

Deno.test("non-equivalent levels are distinguished", () => {
  assertFalse(levelIsEquiv(u, w));
  assertFalse(levelIsEquiv(u, mkLevelSucc(u)));
  assertFalse(levelIsEquiv(mkLevelMax(u, w), u));
});

Deno.test("normalization is idempotent", () => {
  const samples: Level[] = [
    mkLevelMax(mkLevelSucc(u), mkLevelMax(w, levelZero)),
    mkLevelIMax(u, mkLevelMax(w, mkLevelSucc(u))),
    mkLevelSucc(mkLevelMax(u, w)),
  ];
  for (const l of samples) {
    const n1 = normalizeLevel(l);
    const n2 = normalizeLevel(n1);
    assert(levelIsEquiv(n1, n2));
  }
});

Deno.test("levelGeq / levelLeq", () => {
  assert(levelGeq(mkLevelSucc(u), u)); // u+1 ≥ u
  assertFalse(levelGeq(u, mkLevelSucc(u))); // u ≱ u+1
  assert(levelLeq(u, mkLevelSucc(u)));
  assert(levelGeq(mkLevelMax(u, w), u)); // max u v ≥ u
  assert(levelLeq(levelZero, u)); // 0 ≤ u
});

Deno.test("levelInstantiate substitutes parameters by name", () => {
  // (max u v)[u := 0, v := w+1]
  const result = levelInstantiate(
    mkLevelMax(u, w),
    [nameFromString("u"), nameFromString("v")],
    [levelZero, mkLevelSucc(w)],
  );
  assert(levelIsEquiv(result, mkLevelMax(levelZero, mkLevelSucc(w))));
  assert(levelIsEquiv(result, mkLevelSucc(w)));
});
