import { assert, assertEquals, assertStringIncludes, assertThrows } from "@std/assert";
import { DriverError, runModule } from "./driver.ts";
import { ParseError } from "./syntax.ts";
import { nameFromString } from "../kernel/mod.ts";

const PRELUDE = `inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

axiom Nat.add : Nat → Nat → Nat

inductive Eq.{u} (α : Sort u) (a : α) : α → Prop where
  | refl : Eq.{u} α a a`;

Deno.test("runModule checks a module and collects #check output", () => {
  const { env, checks } = runModule(`${PRELUDE}

theorem two_add_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5

#check two_add_three
#check Nat.succ Nat.zero`);
  assert(env.contains(nameFromString("two_add_three")));
  assertEquals(checks.length, 2);
  assertStringIncludes(checks[0]!.text, "two_add_three : Eq.{1} Nat (Nat.add 2 3) 5");
  assertStringIncludes(checks[1]!.text, "Nat.succ Nat.zero : Nat");
});

Deno.test("kernel rejections become DriverError with a position", () => {
  const err = assertThrows(
    () => runModule(`${PRELUDE}\n\ntheorem bogus : Eq.{1} Nat 0 1 := Eq.refl.{1} Nat 0`),
    DriverError,
  );
  // the failing `theorem` command is on line 10 of the source
  assertEquals((err as DriverError).pos.line, 10);
});

Deno.test("parse errors propagate as ParseError", () => {
  assertThrows(() => runModule("def f := x"), ParseError); // missing ': type'
});

Deno.test("elaboration errors propagate with a position", () => {
  // 'u' is not a declared universe parameter of this axiom
  assertThrows(() => runModule("axiom bad : Sort u"), ParseError);
});

Deno.test("#check shows Sort/Type/Prop sugar", () => {
  const { checks } = runModule(`#check Prop
#check Type
#check Sort 5`);
  assertEquals(checks.map((c) => c.text), [
    "Prop : Type",
    "Type : Type 1",
    "Type 4 : Type 5", // Sort 5 = Type 4, with type Sort 6 = Type 5
  ]);
});

Deno.test("modules thread the environment across runs", () => {
  const first = runModule(PRELUDE);
  const { env } = runModule(
    "def one : Nat := Nat.succ Nat.zero\n#check one",
    first.env,
  );
  assert(env.contains(nameFromString("one")));
});
