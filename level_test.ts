import { assert, assertEquals, assertFalse } from "@std/assert";
import { nameFromString } from "./name.ts";
import {
  levelEq,
  levelHasMVar,
  levelZero,
  mkLevelIMax,
  mkLevelLit,
  mkLevelMax,
  mkLevelMVar,
  mkLevelParam,
  mkLevelSucc,
} from "./level.ts";

Deno.test("mkLevelLit builds succ^n zero", () => {
  assert(levelEq(mkLevelLit(0), levelZero));
  assert(levelEq(mkLevelLit(2), mkLevelSucc(mkLevelSucc(levelZero))));
});

Deno.test("structural equality", () => {
  const u = mkLevelParam(nameFromString("u"));
  const v = mkLevelParam(nameFromString("v"));
  assert(levelEq(mkLevelMax(u, v), mkLevelMax(u, v)));
  assertFalse(levelEq(mkLevelMax(u, v), mkLevelMax(v, u)));
  // max and imax with the same operands are not structurally equal
  assertFalse(levelEq(mkLevelMax(u, v), mkLevelIMax(u, v)));
});

Deno.test("levelHasMVar detects metavariables", () => {
  const u = mkLevelParam(nameFromString("u"));
  const m = mkLevelMVar(nameFromString("?m"));
  assertFalse(levelHasMVar(mkLevelSucc(u)));
  assert(levelHasMVar(mkLevelSucc(m)));
  assert(levelHasMVar(mkLevelIMax(u, m)));
  assertFalse(levelHasMVar(mkLevelLit(5)));
});

Deno.test("equal levels have equal hashes", () => {
  const a = mkLevelMax(mkLevelLit(1), mkLevelParam(nameFromString("u")));
  const b = mkLevelMax(mkLevelLit(1), mkLevelParam(nameFromString("u")));
  assertEquals(a.hash, b.hash);
});
