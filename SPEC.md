# cic-ts — Specification (SPEC)

A TypeScript port of the Lean 4 kernel (`src/kernel/`). It implements the **minimal Trusted
Computing Base (TCB)** of the dependent type theory known as the Calculus of Inductive Constructions
(CIC).

Elaboration, tactics, the parser, and surface syntax are out of scope. This project is responsible
only for: "take a fully elaborated term (`Expr`) and independently verify that it has the type it
claims to have."

---

## 0. Design Principles

1. **Keep it small and simple.** The soundness of the kernel depends on this code alone. When
   convenience or performance trades off against soundness, soundness wins.
2. **Immutable.** `Expr` / `Level` are immutable. Transformations always return new values.
3. **Structural sharing and hash-consing.** To handle very large terms, design around structural
   equality and caching from the start.
4. **Fidelity to the reference implementation.** Each module corresponds to a file in the Lean
   kernel; if behavior diverges, the Lean side is authoritative.

---

## 1. Terminology and Assumptions

- Bound variables are represented with **de Bruijn indices**. The innermost binder is `0`. This
  removes the need to reason about α-conversion.
- Input terms to the kernel are assumed to be fully elaborated and to contain **no metavariables
  (`MVar`)**. The `MVar` node exists in the representation but must never appear in a term being
  type-checked (if it does, it is an error).
- All implicit and instance arguments are assumed to be made explicit. `BinderInfo` is retained
  (informational only) and does not affect soundness.

---

## 2. Data Representation

### 2.1 `Name` (`name`)

Hierarchical names, e.g. `Nat.succ` (a `.`-separated name).

```ts
type Name =
  | { kind: "anonymous" }
  | { kind: "str"; prefix: Name; str: string }
  | { kind: "num"; prefix: Name; num: bigint };
```

- Provides equality and hashing.
- Provides conversion to/from strings (`Name.fromString("Nat.succ")`, `name.toString()`).

### 2.2 `Level` (`level.h/.cpp`)

Universe levels — the `u` in `Sort u`.

```ts
type Level =
  | { kind: "zero" } // 0
  | { kind: "succ"; level: Level } // u + 1
  | { kind: "max"; lhs: Level; rhs: Level } // max u v
  | { kind: "imax"; lhs: Level; rhs: Level } // imax u v (0 if rhs is 0, else max)
  | { kind: "param"; name: Name } // universe parameter (universe polymorphism)
  | { kind: "mvar"; name: Name }; // universe metavariable (must not appear in input)
```

Required operations:

- **Normalization / reduction** — the normal form after applying the reduction rules for `max`,
  `imax`, `succ`.
- **`isEquiv(a, b)`** — definitional equality (not the order; `≤` in both directions).
- **`leq(a, b)`** — the partial order `a ≤ b` (needed when comparing `Sort`s during type checking).
- **`instantiate(level, params, args)`** — substitute parameters with level arguments (used when
  unfolding universe-polymorphic constants).

Meaning of `imax`: `imax u v = 0` if `v = 0`, else `max u v`. This is essential to handle the
non-cumulativity of `Prop` (= `Sort 0`).

### 2.3 `Expr` (`expr.h/.cpp`)

The central term representation of the kernel. Twelve kinds.

```ts
type Expr =
  | { kind: "bvar"; idx: bigint } // de Bruijn bound variable
  | { kind: "fvar"; id: Name } // free variable (local hypothesis)
  | { kind: "mvar"; id: Name } // metavariable (must not appear in input)
  | { kind: "sort"; level: Level } // Sort u
  | { kind: "const"; name: Name; levels: Level[] } // constant in the environment (with universe args)
  | { kind: "app"; fn: Expr; arg: Expr } // application (one argument at a time)
  | { kind: "lam"; name: Name; type: Expr; body: Expr; info: BinderInfo } // fun (n : type) => body
  | { kind: "pi"; name: Name; type: Expr; body: Expr; info: BinderInfo } // (n : type) → body
  | { kind: "let"; name: Name; type: Expr; value: Expr; body: Expr } // let n : type := value; body
  | { kind: "lit"; lit: Literal } // literal
  | { kind: "mdata"; data: KVMap; expr: Expr } // metadata annotation (semantically transparent)
  | { kind: "proj"; struct: Name; idx: bigint; expr: Expr }; // structure projection
```

Auxiliary types:

```ts
type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit"

type Literal =
  | { kind: "natVal"; value: bigint }
  | { kind: "strVal"; value: string }

type KVMap = ...   // key-value map for metadata (may be ignored during type checking)
```

Provide constructors for each node (`mkBVar`, `mkApp`, `mkLambda`, ...).

**Cache flags:** each `Expr` should be able to carry the following as precomputed values for
efficiency (Lean embeds these as bits on each node):

- `hash`: structural hash
- `hasFVar`, `hasMVar`, `hasLevelMVar`: whether it contains free variables / metavariables
- `looseBVarRange`: the maximum loose (unbound) BVar index contained + 1 (used for early cutoff in
  `instantiate`/`abstract`)

These may be computed lazily in a first implementation, but become essential for large terms.

---

## 3. Core Term Operations

References: `instantiate.cpp`, `abstract.cpp`, `replace_fn`, `for_each_fn`, `find_fn`.

### 3.1 Traversal combinators

- **`forEach(e, f)`** — visit subterms.
- **`replace(e, f)`** — `f` returns `Expr | null`; `null` means recurse into children.
- **`find(e, pred)`** — find a subterm satisfying a predicate.

### 3.2 `instantiate` (substituting bound variables)

- **`instantiate1(e, v)`** — replace `BVar 0` in `e` with `v` and decrement the outer BVars. The
  core of β-reduction and computing the result type of a Pi.
- **`instantiate(e, vs)`** — substitute several BVars at once (`vs[i]` corresponds to `BVar i`).
- During substitution, loose BVars inside `v` must be shifted by the depth at which they are
  inserted (lifting).

### 3.3 `abstract` (abstracting free variables) — the inverse of `instantiate`

- **`abstract(e, fvars)`** — replace the free variables listed in `fvars` with the corresponding
  `BVar`s. Used when constructing `lam`/`pi`/`let`.

### 3.4 `liftLooseBVars` / `lowerLooseBVars`

- Helpers for shifting loose BVars.

> For soundness, the offset arithmetic of these de Bruijn operations is the most error-prone part.
> Lock it down with tests first (Section 9).

---

## 4. Local Context (`local_ctx.h/.cpp`)

While type checking, when going under a binder, temporarily replace the `BVar` with a fresh `FVar`
(locally nameless style).

```ts
interface LocalDecl {
  fvarId: Name;
  name: Name;
  type: Expr;
  value?: Expr; // present if it is a let-binding
}

interface LocalContext {
  mkLocalDecl(name: Name, type: Expr, info?: BinderInfo): { ctx: LocalContext; fvar: Expr };
  find(fvarId: Name): LocalDecl | undefined;
  // ...
}
```

- Holds a generator for fresh `FVar` `Name`s.
- When going under the body of a `pi`/`lam`: `instantiate1(body, freshFVar)`, process the body, then
  `abstract` on the way back out.

---

## 5. Type Checker (`type_checker.h/.cpp`) — the core

The most important module. Implement the following.

### 5.1 `infer(e): Expr` — type inference

Typing rules per node:

- **`bvar`** — should not appear (already converted to `fvar` under the locally nameless
  discipline). If it appears, error.
- **`fvar`** — look up the type from the local context.
- **`sort u`** — its type is `Sort (u + 1)`.
- **`const n [us]`** — look up the declaration from the environment and `instantiate` its type's
  universe parameters with `us`. The count of `us` must match the declaration's number of universe
  parameters.
- **`app f a`** — reduce `infer(f)` to WHNF to get `Pi x t b`. Check that `a` has type `t`
  (`infer(a)` is defeq to `t`); the result type is `instantiate1(b, a)`.
- **`lam x t b`** — check that `t` is a type (`infer(t)` is a `Sort`). Infer the body under an
  `fvar` to get `bt`; the type is `Pi x t (abstract bt)`.
- **`pi x t b`** — get `infer(t) = Sort u` and, on the body side, `infer(b) = Sort v`; the type is
  `Sort (imax u v)`.
- **`let x t v b`** — check that `t` is a type, `check(v, t)`, and infer the body.
- **`lit (natVal _)`** — `Nat`. **`lit (strVal _)`** — `String`.
- **`proj s i e`** — reduce `infer(e)` to WHNF to get the structure type `S ...`, then return the
  type of the `i`-th field of `S`'s unique constructor, `instantiate`d with the projections of the
  preceding fields (mind dependent projections).
- **`mdata d e`** — `infer(e)`.
- **`mvar`** — error (must not reach the kernel).

### 5.2 `whnf(e): Expr` — Weak Head Normal Form

Reduce until the head can no longer be reduced. Reduction rules:

- **β** — `(fun x => b) a  ⟶  instantiate1(b, a)`
- **δ** — unfold a constant with its definition body (`definition`/`theorem`).
- **ζ** — `let x := v; b  ⟶  instantiate1(b, v)`
- **ι** — reduction when a recursor is applied to constructor arguments. Includes the
  `quot.lift`/`quot.ind` reductions.
- **proj reduction** — `proj i (ctor ... fieldᵢ ...)  ⟶  fieldᵢ`
- **Nat literals** — built-in computation of `Nat.succ`, `Nat.add`, etc. (optional, for performance;
  must match Lean's behavior exactly for soundness).
- δ-unfolding is lazy and done only when necessary (lazy unfolding during `isDefEq`).

### 5.3 `isDefEq(a, b): boolean` — definitional equality

Whether the two are definitionally equal. Outline:

1. If structurally equal, `true` (sped up by hash-consing).
2. Reduce both to WHNF.
3. Case split on the heads:
   - `sort u` vs `sort v` → `Level.isEquiv(u, v)`
   - `const n us` vs `const m vs` → names equal and level lists equiv (otherwise δ-unfold and retry)
   - `app` vs `app` → recursively compare function and spine (lazy δ)
   - `pi`/`lam` → recursively compare binder types and bodies (under an fvar)
   - `lit` → values equal
   - `proj` → struct and index equal + subterm
4. **η-expansion** — `fun x => f x` vs `f`, for function types.
5. **proof irrelevance** — inhabitants of a `Prop` are always equal if their types are defeq.
6. Retry while interleaving δ-unfolding and Nat-literal expansion.

> `isDefEq` is the crux of termination and soundness. Follow Lean's strategies such as
> `lazy_delta_reduction`.

### 5.4 `check(e, expectedType)`

Verify `isDefEq(infer(e), expectedType)`.

### 5.5 Exceptions

Define an error type corresponding to `kernel_exception.h`: type mismatch, unknown constant,
universe parameter count mismatch, unbound variable, occurrence of `MVar`, invalid recursor
application, and so on.

---

## 6. Declarations and Environment (`declaration.h/.cpp`, `environment.h/.cpp`)

### 6.1 `Declaration`

```ts
type Declaration =
  | { kind: "axiom"; name: Name; levelParams: Name[]; type: Expr; isUnsafe: boolean }
  | { kind: "definition"; name: Name; levelParams: Name[]; type: Expr; value: Expr; ... }
  | { kind: "theorem"; name: Name; levelParams: Name[]; type: Expr; value: Expr }
  | { kind: "opaque"; ... }
  | { kind: "quot" }                       // introduce the quotient-type primitives
  | { kind: "inductive"; ... }             // Section 7
```

### 6.2 `Environment`

The collection of declarations verified and accepted so far.

```ts
interface Environment {
  find(name: Name): ConstantInfo | undefined;
  // Type-check a declaration before adding it. This is the main entry point of the kernel.
  addDecl(decl: Declaration): Environment; // throws on failure
}
```

What `addDecl` does:

1. Check that the declaration's `type` is itself well-typed (`infer(type)` is a `Sort`).
2. For `definition`/`theorem`, `check(value, type)`.
3. For `inductive`, the verification in Section 7.
4. If it passes, register it in the environment.

The environment is extended immutably (persistent data structure, or copy-on-write Map).

---

## 7. Inductive Types (`inductive.h/.cpp`)

The most complex part of the kernel. May be deferred in the MVP, but is required to handle
`Nat`/`List`/`Eq`.

What to implement:

1. **Verification of inductive declarations** — check that the parameter count, and the type of each
   constructor:
   - has a result that is the inductive type in question,
   - satisfies **strict positivity** (the inductive type does not occur in a negative position of
     its own constructor arguments),
   - satisfies the universe constraints (such as the restriction on eliminating into `Prop`).
2. **Automatic generation of the recursor** — construct the type of the eliminator with its motive,
   minor premises, and major premise, and add it to the environment.
3. **Registration of the ι-reduction rule** —
   `rec ... (ctorᵢ args)  ⟶  (apply the i-th minor premise to args and the recursive results)`. WHNF
   uses this.
4. **Determination of subsingleton / large elimination** (a `Prop` inductive can be eliminated into
   `Type` only under specific conditions, such as a single constructor).

> Incrementally: start with simple inductives without parameters (`Nat`, `Bool`), then parameterized
> ones (`List`), and finally indexed ones (`Eq`, `Vector`).

---

## 8. Quotient Types (`quot.h/.cpp`)

One of the few axiomatic constructs Lean trusts as built-in. Introduce `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`, and incorporate the computation rule `Quot.lift f h (Quot.mk r a)  ⟶  f a`
into WHNF / `isDefEq`.

---

## 9. Test Strategy (lock down in parallel with implementation, as the top priority)

Since soundness is everything, test both sides thickly: "accept correct terms" and "reject
ill-formed terms."

1. **Unit tests for de Bruijn operations** — boundary cases of offsets for `instantiate1` /
   `abstract` / `liftLooseBVars`. Compare against hand-computed expected values.
2. **Level normalization** — representative cases of `max`/`imax`/`succ`, and the partial order
   `leq`.
3. **Golden tests for type inference** — verify the types of the canonical examples in Section 2,
   e.g. `fun (x : Nat) => x : Nat → Nat`.
4. **Positive and negative cases for defeq** — each of β/δ/ζ/η/proof-irrelevance.
5. **Rejection tests (the heart of soundness)** — that type mismatches, universe parameter count
   mismatches, loose BVars, occurrences of `MVar`, positivity-violating inductives, etc. **always**
   throw.
6. **Cross-checking (ideal)** — `#check` / export small terms in Lean 4 and confirm cic-ts agrees.
   Being able to read Lean's `.olean` / environment export format would be powerful.

---

## 10. Module Layout (correspondence with the Lean kernel)

| cic-ts module     | Lean kernel                            | Contents                                       |
| ----------------- | -------------------------------------- | ---------------------------------------------- |
| `name.ts`         | `name` (lean)                          | hierarchical names                             |
| `level.ts`        | `level.{h,cpp}`                        | universe levels, normalization, ordering       |
| `expr.ts`         | `expr.{h,cpp}`                         | `Expr` representation and constructors         |
| `traverse.ts`     | `for_each_fn`, `replace_fn`, `find_fn` | traversal combinators                          |
| `instantiate.ts`  | `instantiate.cpp`, `abstract.cpp`      | de Bruijn substitution / abstraction           |
| `localContext.ts` | `local_ctx.{h,cpp}`                    | local context                                  |
| `declaration.ts`  | `declaration.{h,cpp}`                  | declarations                                   |
| `environment.ts`  | `environment.{h,cpp}`                  | environment and `addDecl`                      |
| `typeChecker.ts`  | `type_checker.{h,cpp}`                 | `infer` / `whnf` / `isDefEq` / `check`         |
| `inductive.ts`    | `inductive.{h,cpp}`                    | inductive verification and recursor generation |
| `quot.ts`         | `quot.{h,cpp}`                         | quotient types                                 |
| `exception.ts`    | `kernel_exception.h`                   | kernel exceptions                              |

---

## 11. Implementation Phases (recommended order)

1. **Phase 0 — Representation**: `Name`, `Level`, `Expr` with constructors, equality, hashing.
2. **Phase 1 — Operations**: traversal combinators, `instantiate` / `abstract`, Level normalization.
   Lock these down with tests.
3. **Phase 2 — Core type checker**: `infer` / `whnf` / `isDefEq` (β/δ/ζ/η/proof-irrelevance).
   Without inductives or quotients, covering `Sort`/`Pi`/`Lambda`/`App`/`Const`/`Let`. `addDecl` for
   `axiom`/`definition`/`theorem`.
4. **Phase 3 — Inductive types**: verification + recursor generation + ι-reduction.
   `Nat`/`Bool`/`List`/`Eq`.
5. **Phase 4 — Quotient types**: the `Quot` family and its computation rule.
6. **Phase 5 — Polish**: built-in computation for literals (fast `Nat` arithmetic), optimization of
   `proj` reduction, cross-checking against Lean.

For each phase, achieve "clean build + the relevant tests pass" before moving on.
