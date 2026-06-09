import { assert, assertEquals, assertThrows } from "@std/assert";
import { parse, parseExpr } from "./parser.ts";
import { ParseError, type SBinder, type SExpr, type SLevel } from "./syntax.ts";

// --- tiny pretty-printers so we can assert on compact strings ---------------

function showLevel(l: SLevel): string {
  switch (l.kind) {
    case "num":
      return l.value.toString();
    case "ident":
      return l.name;
    case "add":
      return `(${showLevel(l.base)}+${l.n})`;
    case "max":
      return `(max ${showLevel(l.lhs)} ${showLevel(l.rhs)})`;
    case "imax":
      return `(imax ${showLevel(l.lhs)} ${showLevel(l.rhs)})`;
  }
}

function showBinder(b: SBinder): string {
  const open = b.info === "explicit" ? "(" : "{";
  const close = b.info === "explicit" ? ")" : "}";
  return `${open}${b.names.join(" ")} : ${show(b.type)}${close}`;
}

function show(e: SExpr): string {
  switch (e.kind) {
    case "ident":
      return e.univs ? `${e.name}.{${e.univs.map(showLevel).join(",")}}` : e.name;
    case "sort":
      return `Sort ${showLevel(e.level)}`;
    case "type":
      return e.level ? `Type ${showLevel(e.level)}` : "Type";
    case "prop":
      return "Prop";
    case "num":
      return e.value.toString();
    case "app":
      return `(${show(e.fn)} ${show(e.arg)})`;
    case "arrow":
      return `(${show(e.from)} -> ${show(e.to)})`;
    case "lam":
      return `(fun ${e.binders.map(showBinder).join(" ")} => ${show(e.body)})`;
    case "pi":
      return `(forall ${e.binders.map(showBinder).join(" ")}, ${show(e.body)})`;
  }
}

const sh = (src: string) => show(parseExpr(src));

// --- expressions ------------------------------------------------------------

Deno.test("application is left-associative", () => {
  assertEquals(sh("f a b c"), "(((f a) b) c)");
});

Deno.test("arrow is right-associative", () => {
  assertEquals(sh("A -> B -> C"), "(A -> (B -> C))");
  assertEquals(sh("A → B"), "(A -> B)");
});

Deno.test("application binds tighter than arrow", () => {
  assertEquals(sh("f a -> g b"), "((f a) -> (g b))");
});

Deno.test("fun and ∀ with typed binders", () => {
  assertEquals(sh("fun (x : Nat) => x"), "(fun (x : Nat) => x)");
  assertEquals(sh("λ (x y : Nat) => x"), "(fun (x y : Nat) => x)");
  assertEquals(sh("∀ (x : Nat), P x"), "(forall (x : Nat), (P x))");
});

Deno.test("sorts and literals", () => {
  assertEquals(sh("Sort u"), "Sort u");
  assertEquals(sh("Sort (u+1)"), "Sort (u+1)");
  assertEquals(sh("Type"), "Type");
  assertEquals(sh("Type 0"), "Type 0");
  assertEquals(sh("Prop"), "Prop");
  assertEquals(sh("42"), "42");
});

Deno.test("universe arguments and level operators", () => {
  assertEquals(sh("Eq.{1}"), "Eq.{1}");
  assertEquals(sh("f.{u,v}"), "f.{u,v}");
  assertEquals(sh("Sort (max u v)"), "Sort (max u v)");
  assertEquals(sh("Sort (imax u (v+1))"), "Sort (imax u (v+1))");
});

Deno.test("parentheses group", () => {
  assertEquals(sh("f (g a) b"), "((f (g a)) b)");
  assertEquals(sh("(A -> B) -> C"), "((A -> B) -> C)");
});

// --- commands ---------------------------------------------------------------

Deno.test("axiom command", () => {
  const m = parse("axiom Nat.add : Nat → Nat → Nat");
  assertEquals(m.length, 1);
  const c = m[0]!;
  assert(c.kind === "axiom");
  assertEquals(c.name, "Nat.add");
  assertEquals(show(c.type), "(Nat -> (Nat -> Nat))");
});

Deno.test("def with universe params and binders", () => {
  const m = parse("def id.{u} (α : Sort u) (x : α) : α := x");
  const c = m[0]!;
  assert(c.kind === "def");
  assertEquals(c.univParams, ["u"]);
  assertEquals(c.binders.map(showBinder), ["(α : Sort u)", "(x : α)"]);
  assertEquals(show(c.type), "α");
  assertEquals(show(c.value), "x");
});

Deno.test("inductive with parameters and constructors", () => {
  const m = parse(`inductive List.{u} (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α`);
  const c = m[0]!;
  assert(c.kind === "inductive");
  assertEquals(c.name, "List");
  assertEquals(c.univParams, ["u"]);
  assertEquals(c.params.map(showBinder), ["(α : Type u)"]);
  // constructor names stay as written; the elaborator qualifies them later
  assertEquals(c.ctors.map((k) => k.name), ["nil", "cons"]);
  assertEquals(show(c.ctors[1]!.type), "(α -> ((List α) -> (List α)))");
});

Deno.test("init_quot and #check commands", () => {
  const m = parse("init_quot\n#check Nat.zero");
  assertEquals(m[0]!.kind, "initQuot");
  const c = m[1]!;
  assert(c.kind === "check");
  assertEquals(show(c.expr), "Nat.zero");
});

Deno.test("parses the full proof_check sample program", () => {
  const m = parse(`inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

axiom Nat.add : Nat → Nat → Nat

inductive Eq.{u} (α : Sort u) (a : α) : α → Prop where
  | refl : Eq α a a

theorem two_add_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5

#check two_add_three`);
  assertEquals(m.map((c) => c.kind), ["inductive", "axiom", "inductive", "theorem", "check"]);
  const thm = m[3]!;
  assert(thm.kind === "theorem");
  assertEquals(show(thm.type), "(((Eq.{1} Nat) ((Nat.add 2) 3)) 5)");
  assertEquals(show(thm.value), "((Eq.refl.{1} Nat) 5)");
});

// --- errors -----------------------------------------------------------------

Deno.test("parse errors carry a position", () => {
  const e1 = assertThrows(() => parse("def f := x"), ParseError); // missing ': type'
  assert(e1 instanceof ParseError);
  assertThrows(() => parseExpr("fun => x"), ParseError); // no binder
  assertThrows(() => parseExpr("(a b"), ParseError); // unbalanced paren
  assertThrows(() => parseExpr("f a b extra )"), ParseError); // trailing input
});
