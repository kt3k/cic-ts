import { assert, assertEquals, assertFalse } from "@std/assert";
import {
  anonymousName,
  mkNumName,
  mkStrName,
  nameEq,
  nameFromString,
  nameToString,
} from "./name.ts";

Deno.test("nameFromString / nameToString roundtrip", () => {
  assertEquals(nameToString(nameFromString("Nat.succ")), "Nat.succ");
  assertEquals(nameToString(nameFromString("List")), "List");
  assertEquals(nameToString(nameFromString("a.b.c.d")), "a.b.c.d");
});

Deno.test("empty string is the anonymous name", () => {
  assert(nameEq(nameFromString(""), anonymousName));
  assertEquals(nameToString(anonymousName), "[anonymous]");
});

Deno.test("numeric components render and compare", () => {
  const n = mkNumName(nameFromString("x"), 7n);
  assertEquals(nameToString(n), "x.7");
  assert(nameEq(n, mkNumName(mkStrName(anonymousName, "x"), 7n)));
});

Deno.test("equality distinguishes structure", () => {
  assert(nameEq(nameFromString("Nat.succ"), nameFromString("Nat.succ")));
  assertFalse(nameEq(nameFromString("Nat.succ"), nameFromString("Nat.zero")));
  assertFalse(nameEq(nameFromString("Nat.succ"), nameFromString("succ.Nat")));
  // str vs num components with the "same" payload differ
  assertFalse(nameEq(mkNumName(anonymousName, 1n), mkStrName(anonymousName, "1")));
});

Deno.test("equal names have equal hashes", () => {
  assertEquals(nameFromString("Nat.succ").hash, nameFromString("Nat.succ").hash);
  assertEquals(mkNumName(anonymousName, 42n).hash, mkNumName(anonymousName, 42n).hash);
});
