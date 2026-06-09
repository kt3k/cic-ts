import { assert, assertEquals, assertThrows } from "@std/assert";
import { type Token, tokenize } from "./lexer.ts";
import { ParseError } from "./syntax.ts";

/** Tokenize and drop the trailing eof, returning [kind, value] pairs. */
function toks(src: string): Array<[string, string]> {
  const ts = tokenize(src);
  assertEquals(ts[ts.length - 1]!.kind, "eof");
  return ts.slice(0, -1).map((t: Token) => [t.kind, t.value]);
}

Deno.test("identifiers, keywords, numerals", () => {
  assertEquals(toks("foo Bar 42 fun"), [
    ["ident", "foo"],
    ["ident", "Bar"],
    ["numeral", "42"],
    ["keyword", "fun"],
  ]);
});

Deno.test("dotted identifiers are a single token", () => {
  assertEquals(toks("Nat.succ Eq.refl"), [
    ["ident", "Nat.succ"],
    ["ident", "Eq.refl"],
  ]);
});

Deno.test("universe args .{ splits off after a name", () => {
  assertEquals(toks("Eq.{1}"), [
    ["ident", "Eq"],
    ["symbol", ".{"],
    ["numeral", "1"],
    ["symbol", "}"],
  ]);
  // dotted name followed by universe args
  assertEquals(toks("Eq.refl.{u}"), [
    ["ident", "Eq.refl"],
    ["symbol", ".{"],
    ["ident", "u"],
    ["symbol", "}"],
  ]);
});

Deno.test("symbols, including unicode and the -> alias", () => {
  assertEquals(toks("( ) { } : := => , | + → ∀ λ"), [
    ["symbol", "("],
    ["symbol", ")"],
    ["symbol", "{"],
    ["symbol", "}"],
    ["symbol", ":"],
    ["symbol", ":="],
    ["symbol", "=>"],
    ["symbol", ","],
    ["symbol", "|"],
    ["symbol", "+"],
    ["symbol", "→"],
    ["symbol", "∀"],
    ["symbol", "λ"],
  ]);
  // '->' lexes to the same token as '→'
  assertEquals(toks("A -> B"), [["ident", "A"], ["symbol", "→"], ["ident", "B"]]);
});

Deno.test("unicode identifiers are allowed (but not reserved symbols)", () => {
  assertEquals(toks("α β γ"), [["ident", "α"], ["ident", "β"], ["ident", "γ"]]);
});

Deno.test("keywords vs identifiers", () => {
  assertEquals(toks("Sort Type Prop inductive #check"), [
    ["keyword", "Sort"],
    ["keyword", "Type"],
    ["keyword", "Prop"],
    ["keyword", "inductive"],
    ["keyword", "#check"],
  ]);
});

Deno.test("line and block comments are skipped", () => {
  assertEquals(toks("a -- comment\n b /- block /- nested -/ -/ c"), [
    ["ident", "a"],
    ["ident", "b"],
    ["ident", "c"],
  ]);
});

Deno.test("token positions are tracked (1-based line/col)", () => {
  const ts = tokenize("foo\n  bar");
  assertEquals(ts[0]!.value, "foo");
  assertEquals([ts[0]!.pos.line, ts[0]!.pos.col], [1, 1]);
  assertEquals(ts[1]!.value, "bar");
  assertEquals([ts[1]!.pos.line, ts[1]!.pos.col], [2, 3]);
});

Deno.test("lexes the proof_check sample program", () => {
  const src = `inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

theorem t : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5`;
  const kinds = tokenize(src).map((t) => t.kind);
  assert(!kinds.slice(0, -1).includes("eof"));
  assertEquals(kinds[kinds.length - 1], "eof");
  // spot-check a few tokens
  const vals = tokenize(src).map((t) => t.value);
  assert(vals.includes("inductive"));
  assert(vals.includes(".{"));
  assert(vals.includes("→"));
  assert(vals.includes(":="));
});

Deno.test("errors carry a position", () => {
  const err = assertThrows(() => tokenize("a = b"), ParseError); // lone '='
  assert((err as ParseError).message.includes("1:3"));
  assertThrows(() => tokenize("/- unterminated"), ParseError);
  assertThrows(() => tokenize("#bogus"), ParseError);
});
