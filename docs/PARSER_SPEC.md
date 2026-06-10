# cic-ts — Surface Syntax Parser Specification (PARSER_SPEC)

A small Lean-like surface syntax that compiles to the kernel API (`addDecl` / `addInductive` /
`addQuot`). The goal is to express, as readable text, exactly what `demos/proof_check.ts` does by
hand.

## 0. Design Principles

- **Parser + minimal elaborator only.** It resolves names (named variables → de Bruijn indices,
  identifiers → `Const`) and folds declaration parameters into constructors/definitions. It does
  **not** do type inference, implicit argument synthesis, unification, or tactics.
- Output is a list of `Declaration`s fed straight to the existing kernel API. **Soundness stays with
  the kernel**; the front end only translates convenient syntax into kernel calls.
- **Everything is explicit** — including implicit-looking arguments at use sites (always like Lean's
  `@f`). This is v1's main simplification: there is no implicit-argument or universe inference.

## 1. Pipeline

```
text
 │  Lexer        → Token[]
 ▼
Token[]
 │  Parser       → Surface AST (named, with source positions)
 ▼
Surface AST
 │  Elaborator   → kernel Expr / Declaration (de Bruijn, name resolution)
 ▼
Declaration[]
 │  Driver       → grows an Environment (addDecl / addInductive / addQuot)
 ▼
Environment (+ #check output / errors)
```

Suggested modules: `syntax.ts` (Surface AST types), `lexer.ts`, `parser.ts`, `elaborator.ts`,
`driver.ts`.

## 2. Lexical Structure

- **Comments**: `-- line` and `/- block -/` (nestable).
- **Identifiers**: Lean-style, Unicode allowed (`α`, `β`, `→`, `∀`, `λ`, …). A dot-separated
  qualified name such as `Nat.succ` is one token.
- **Numerals**: natural numbers `0`, `42` (sugar for the Peano constructor term
  `Nat.succ (… (Nat.zero))`).
- **Keywords**: `inductive` `axiom` `def` `theorem` `opaque` `where` `fun` `Sort` `Type` `Prop`
  `max` `imax` `init_quot` `#check`.
- **Symbols**: `( ) { } : := => → ∀ λ , | .{ } +`. `->` is an alias for `→`; `\fun`/`λ` and
  `\forall`/`∀` are synonyms.

## 3. Expression Grammar (EBNF, lowest → highest precedence)

```ebnf
expr      ::= "fun" binders "=>" expr            (* lambda *)
            | "∀" binders "," expr               (* dependent function type *)
            | arrow
arrow     ::= app ("→" arrow)?                    (* non-dependent arrow, right-assoc *)
app       ::= atom atom*                          (* application, left-assoc *)
atom      ::= ident univs?                        (* const/variable (+ universe args) *)
            | "Sort" level | "Type" level? | "Prop"
            | numeral
            | "(" expr ")"
binders   ::= binder+
binder    ::= "(" ident+ ":" expr ")"            (* explicit *)
            | "{" ident+ ":" expr "}"            (* implicit (treated as explicit in v1) *)
univs     ::= ".{" level ("," level)* "}"
level     ::= numeral | ident | level "+" numeral
            | "max" level level | "imax" level level | "(" level ")"
```

- `Type` = `Sort (u+1)`, `Type u` = `Sort (u+1)`, `Prop` = `Sort 0`, bare `Type` = `Sort 1`.
- `fun`/`∀` binders **must be typed** (no inference): `fun (x : Nat) => x` is valid, `fun x => x` is
  an error.
- `A → B` desugars to `∀ (_ : A), B` (body does not refer to `A`).

## 4. Declaration Grammar (commands)

```ebnf
command ::= "axiom"   ident univParams? ":" expr
          | "def"     ident univParams? binders? ":" expr ":=" expr
          | "theorem" ident univParams? binders? ":" expr ":=" expr
          | "opaque"  ident univParams? binders? ":" expr ":=" expr
          | "inductive" ident univParams? binders? ":" expr "where" ctor*
          | "init_quot"
          | "#check" expr
ctor    ::= "|" ident ":" expr
univParams ::= ".{" ident ("," ident)* "}"
```

Semantics:

- **Leading binders on `def`/`theorem`/`opaque`** are folded into both the type and the value (as in
  Lean). Example: `def id.{u} (α : Sort u) (x : α) : α := x` → type `(α : Sort u) → (x : α) → α`,
  value `fun (α : Sort u) (x : α) => x`, emitted via `mkDefinition`.
- **`inductive` binders are the parameters** (`numParams` is their count). The `: expr` part is the
  remaining index telescope ending in a `Sort`.
- **Constructor types omit the parameters** (Lean style): the type name, parameters, and universe
  parameters are in scope in constructor types, and the elaborator prepends the parameter binders to
  form the kernel constructor type.
- `init_quot` → `addQuot()` (requires `Eq`).
- `#check e` → display the type from `infer(e)` (does not change the env).

## 5. Name Resolution (Elaborator)

- A scope stack of binder names: an identifier that is bound becomes a de Bruijn index, otherwise it
  resolves to an environment constant (`Const`); if neither, it is an error.
- Universe parameter names (introduced by `.{u}`) resolve to `Level` `param`.
- `ident.{l1,l2}` provides explicit universe arguments. **A constant with zero universe parameters
  may omit `.{}`**; a constant with universe parameters (e.g. `Eq`) must provide them (v1
  limitation; future work: universe inference).

## 6. The proof_check Demo in This Syntax

```lean
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

def Nat.add : Nat → Nat → Nat :=
  fun (a b : Nat) =>
    Nat.rec.{1} (fun (n : Nat) => Nat) a (fun (n ih : Nat) => Nat.succ ih) b

inductive Eq.{u} (α : Sort u) (a : α) : α → Prop where
  | refl : Eq α a a

theorem two_add_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5

#check two_add_three
```

(`Eq.{1}` shows the explicit-universe requirement. Numerals elaborate to Peano constructor terms,
and `Nat.add 2 3` reduces to `5` by δ/β/ι alone, so `Eq.refl.{1} Nat 5 : Eq Nat 5 5` is
definitionally equal to the stated proposition and is accepted.)

## 7. Error Handling

- **Parse errors**: `line:col` with the expected token(s).
- **Resolution errors**: unbound identifier; wrong number of universe arguments.
- **Kernel errors**: a `KernelError` thrown by `addDecl` etc., reported with the source position of
  the offending command.

## 8. Out of Scope for v1 (for soundness and smallness)

Implicit-argument inference / unification / tactics (`by`) / type classes / `match` and patterns
(raw recursors only) / mutual and nested inductives / structure sugar / notation and macros.
