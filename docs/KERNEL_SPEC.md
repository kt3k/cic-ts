# cic-ts — Kernel Specification (KERNEL_SPEC)

A TypeScript implementation of the **minimal Trusted Computing Base (TCB)** of the dependent type
theory known as the Calculus of Inductive Constructions (CIC). Its design is modeled on the Lean 4
kernel, but it is **not a line-by-line port**: the goal is to perform the _same verification_
conceptually, while staying small and idiomatic in TypeScript. Where a simpler structure checks the
same terms, it is preferred over mirroring Lean's file layout.

Elaboration, tactics, the parser, and surface syntax are out of scope (the parser lives separately
under `parser/`, see `PARSER_SPEC.md`). The kernel is responsible only for: "take a fully elaborated
term (`Expr`) and independently verify that it has the type it claims to have."

---

## 0. Design Principles

1. **Keep it small and simple.** The soundness of the kernel depends on this code alone. When
   convenience or performance trades off against soundness, soundness wins.
2. **Immutable.** `Expr` / `Level` / `Name` are immutable. Transformations always return new values,
   and the `Environment` is extended persistently.
3. **Cached structural hashing.** Every `Name` / `Level` / `Expr` node precomputes a 32-bit
   structural `hash` (and `Expr` also caches the flags in §2.3). Equality is then a fast reference
   check (`a === b`), a fast hash reject (`a.hash !== b.hash`), and only otherwise a structural
   recursion. This is **not** full hash-consing — constructors do not intern nodes into a shared
   table — but it gives the same fast-path behavior for large terms. The exact hash values are an
   implementation detail; only determinism and a reasonable distribution matter (see `hash.ts`).
4. **Conceptual fidelity, not literal fidelity.** The type theory being checked is a pure CIC in the
   style of Lean (the rules for `Sort`/`imax`, definitional equality, inductives, recursors,
   quotients) — deliberately _without_ Lean's extensions of definitional equality: no built-in
   literal arithmetic, no definitional proof irrelevance, and no K-like recursor reduction. The
   _implementation_ is free to diverge in structure, naming, and module boundaries as long as it
   accepts/rejects the same terms.

---

## 1. Terminology and Assumptions

- Bound variables are represented with **de Bruijn indices**. The innermost binder is `0`. This
  removes the need to reason about α-conversion.
- Input terms to the kernel are assumed to be fully elaborated and to contain **no metavariables
  (`MVar`)**. The `MVar` node (and the universe `mvar`) exists in the representation but must never
  appear in a term being type-checked (if it does, it is an error).
- All implicit and instance arguments are assumed to be made explicit. `BinderInfo` is retained
  (informational only) and does not affect soundness.

---

## 2. Data Representation

### 2.1 `Name` (`name.ts`)

Hierarchical names, e.g. `Nat.succ` (a `.`-separated name).

```ts
type Name =
  | { kind: "anonymous" }
  | { kind: "str"; prefix: Name; str: string }
  | { kind: "num"; prefix: Name; num: bigint };
```

- Provides equality (`nameEq`) and a cached `hash`.
- Provides conversion to/from strings (`nameFromString("Nat.succ")`, `nameToString(name)`).

### 2.2 `Level` (`level.ts`)

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

Operations:

- **`normalizeLevel(level)`** — the normal form after applying the reduction rules for `max`,
  `imax`, `succ`.
- **`levelIsEquiv(a, b)`** — definitional equality of levels (`≤` in both directions).
- **`levelLeq(a, b)` / `levelGeq(a, b)`** — the partial order `a ≤ b` (needed when comparing `Sort`s
  during type checking).
- **`levelInstantiate(level, params, args)`** — substitute parameters with level arguments (used
  when unfolding universe-polymorphic constants).
- Helpers: `toOffset` (split `u + k` into `(u, k)`), `isExplicit`, `isNotZero`, `levelHasMVar`.

Meaning of `imax`: `imax u v = 0` if `v = 0`, else `max u v`. This is essential to handle the
non-cumulativity of `Prop` (= `Sort 0`).

### 2.3 `Expr` (`expr.ts`)

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
  | { kind: "mdata"; data: KVMap; expr: Expr } // metadata annotation (semantically transparent)
  | { kind: "proj"; struct: Name; idx: bigint; expr: Expr }; // structure projection
```

Auxiliary types:

```ts
type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit"

type KVMap = ...   // key-value map for metadata (ignored during type checking)
```

There is a constructor for each node (`mkBVar`, `mkApp`, `mkLambda`, ...). The `mvar` and `mdata`
node kinds exist for completeness but are not produced by the surface front end; they are exercised
by the kernel's own invariant tests.

Note that there is no literal node: `Nat` values are plain constructor terms
(`Nat.succ (… (Nat.zero))`), so all computation on them goes through the ordinary reduction rules
(no kernel-level fast path).

**Cache flags:** every `Expr` carries the following as precomputed values (set by the constructors):

- `hash`: structural hash (§0, principle 3)
- `hasFVar`, `hasMVar`, `hasLevelMVar`: whether it contains free variables / metavariables / level
  metavariables
- `looseBVarRange`: the maximum loose (unbound) BVar index contained + 1 (used for early cutoff in
  `instantiate` / `abstract`)

---

## 3. Core Term Operations (`expr.ts`)

The traversal combinators and the de Bruijn operations live alongside the `Expr` definition in
`expr.ts` (in earlier revisions these were separate `traverse.ts` / `instantiate.ts` modules; they
were consolidated since the operations are tiny and share the same recursion skeleton).

### 3.1 Traversal combinators

- **`forEach(e, f)`** — visit every subterm.
- **`find(e, pred)`** — find the first subterm satisfying a predicate.
- **`replace(e, f)`** — `f` returns `Expr | null`; `null` means recurse into children.
- **`mapChildren(e, g)`** / **`mapChildrenWithDepth(e, g)`** — rebuild a node from mapped immediate
  children (the latter tracks binder depth).
- Spine helpers: **`getAppFn(e)`**, **`getAppArgs(e)`**.

### 3.2 `instantiate` (substituting bound variables)

- **`instantiate1(e, v)`** — replace `BVar 0` in `e` with `v` and decrement the outer BVars. The
  core of β-reduction and computing the result type of a Pi.
- **`instantiate(e, subst)`** — substitute several BVars at once (`subst[i]` corresponds to
  `BVar i`); **`instantiateRev(e, subst)`** uses `subst[n-1-i]`.
- During substitution, loose BVars inside `v` are shifted by the depth at which they are inserted
  (lifting). Closed terms are returned unchanged (and identically), using the `looseBVarRange`
  cutoff.

### 3.3 `abstract` (abstracting free variables) — the inverse of `instantiate`

- **`abstract(e, fvars)`** — replace the free variables listed in `fvars` with the corresponding
  `BVar`s. Used when constructing `lam` / `pi` / `let`.

### 3.4 `liftLooseBVars` / `lowerLooseBVars` / `instantiateLevelParams`

- Helpers for shifting loose BVars and for substituting universe parameters inside an `Expr`.

> For soundness, the offset arithmetic of these de Bruijn operations is the most error-prone part.
> It is locked down with direct unit tests (§9).

---

## 4. Local Context (inside `type_checker.ts`)

While type checking, when going under a binder, the bound variable is temporarily replaced by a
fresh `FVar` (locally nameless style). This is a small persistent map and lives **inside**
`type_checker.ts` rather than as its own module:

```ts
interface LocalDecl {
  fvarId: Name;
  name: Name;
  type: Expr;
  value?: Expr; // present if it is a let-binding
}
```

- The `TypeChecker` holds a fresh-`FVar` name generator and the current `LocalContext`.
- When going under the body of a `pi` / `lam`: `instantiate1(body, freshFVar)`, process the body,
  then `abstract` on the way back out.

---

## 5. Type Checker (`type_checker.ts`) — the core

`TypeChecker` is a class constructed from an `Environment`. It exposes `infer`, `whnf`, `isDefEq`,
and `check` (plus the helpers `ensureSort` / `ensurePi`).

### 5.1 `infer(e): Expr` — type inference

Typing rules per node:

- **`bvar`** — should not appear (already converted to `fvar` under the locally nameless
  discipline). If it appears, error.
- **`fvar`** — look up the type from the local context.
- **`sort u`** — its type is `Sort (u + 1)`.
- **`const n [us]`** — look up the declaration from the environment and `levelInstantiate` its
  type's universe parameters with `us`. The count of `us` must match the declaration's number of
  universe parameters.
- **`app f a`** — reduce `infer(f)` to WHNF to get `Pi x t b` (via `ensurePi`). Check that `a` has
  type `t`; the result type is `instantiate1(b, a)`.
- **`lam x t b`** — check that `t` is a type (`infer(t)` is a `Sort`). Infer the body under an
  `fvar` to get `bt`; the type is `Pi x t (abstract bt)`.
- **`pi x t b`** — get `infer(t) = Sort u` and, on the body side, `infer(b) = Sort v`; the type is
  `Sort (imax u v)`.
- **`let x t v b`** — check that `t` is a type, `check(v, t)`, and infer the body.
- **`proj s i e`** — reduce `infer(e)` to WHNF to get the structure type `S ...`, then return the
  type of the `i`-th field of `S`'s unique constructor, `instantiate`d with the projections of the
  preceding fields (dependent projections).
- **`mdata d e`** — `infer(e)`.
- **`mvar`** — error (must not reach the kernel).

### 5.2 `whnf(e): Expr` — Weak Head Normal Form

Reduce until the head can no longer be reduced. Reduction rules:

- **β** — `(fun x => b) a  ⟶  instantiate1(b, a)`
- **δ** — unfold a constant with its definition body (`definition` / `theorem`).
- **ζ** — `let x := v; b  ⟶  instantiate1(b, v)`
- **ι** — reduction when a recursor is applied to constructor arguments. Includes the `Quot.lift` /
  `Quot.ind` reductions.
- **proj reduction** — `proj i (ctor ... fieldᵢ ...)  ⟶  fieldᵢ`
- δ-unfolding is lazy and done only when necessary.

There is deliberately no built-in arithmetic: closed `Nat` arithmetic reduces through the recursor,
one ι-step per `Nat.succ`. Slow, but exactly the reduction relation of the theory.

### 5.3 `isDefEq(a, b): boolean` — definitional equality

Whether the two are definitionally equal. Outline:

1. If structurally equal (reference / hash / structure), `true`.
2. Reduce both to WHNF.
3. Case split on the heads:
   - `sort u` vs `sort v` → `levelIsEquiv(u, v)`
   - `const n us` vs `const m vs` → names equal and level lists equiv (otherwise δ-unfold and retry)
   - `app` vs `app` → recursively compare function and spine (lazy δ)
   - `pi` / `lam` → recursively compare binder types and bodies (under an fvar)
   - `proj` → struct and index equal + subterm
4. **η-expansion** — `fun x => f x` vs `f`, for function types.
5. Retry while interleaving δ-unfolding.

There is deliberately no definitional proof irrelevance: two proofs of the same `Prop` are equal
only if the ordinary rules above make them so.

> `isDefEq` is the crux of termination and soundness.

### 5.4 `check(e, expectedType): void`

Verify `isDefEq(infer(e), expectedType)`; throws a `KernelError` (type mismatch) if not.

### 5.5 Exceptions (`exception.ts`)

`KernelError` carries an `errorKind` tag: type mismatch, unknown constant, universe parameter count
mismatch, unbound variable, occurrence of `MVar`, invalid recursor / inductive application,
already-declared name, and so on.

---

## 6. Declarations and Environment (`declaration.ts`, `environment.ts`)

### 6.1 Declarations and stored constants

`Declaration` is the set of _input builders_ type-checked by `addDecl`. Inductives and quotients are
**not** `Declaration` kinds — they have their own entry points (§6.2):

```ts
type Declaration = AxiomVal | DefinitionVal | TheoremVal | OpaqueVal;
```

built with `mkAxiom` / `mkDefinition` / `mkTheorem` / `mkOpaque`. What is _stored_ in the
environment is a `ConstantInfo`, which additionally covers the constants that inductive/quotient
processing generates:

```ts
type ConstantInfo =
  | Declaration
  | InductiveVal // the inductive type itself
  | ConstructorVal // each constructor
  | RecursorVal // the generated recursor (with its RecursorRule ι-rules)
  | QuotVal; // a Quot primitive
```

Inductive _input_ is an `InductiveDeclaration`
(`{ levelParams, numParams, types: InductiveType[],
... }`, each `InductiveType` carrying its
`Constructor[]`).

### 6.2 `Environment`

The collection of declarations verified and accepted so far. Immutable.

```ts
class Environment {
  find(name: Name): ConstantInfo | undefined;
  contains(name: Name): boolean;
  addDecl(decl: Declaration): Environment; // axiom/definition/theorem/opaque — throws on failure
  addInductive(decl: InductiveDeclaration): Environment; // §7
  addQuot(): Environment; // §8
}
```

What `addDecl` does:

1. Reject a name that is already declared.
2. Check that the declaration's `type` is itself well-typed (`infer(type)` is a `Sort`).
3. For `definition` / `theorem` / `opaque`, `check(value, type)`.
4. If it passes, register the resulting `ConstantInfo` in the environment.

The environment is extended immutably (a copy-on-write `Map` keyed by the name string).

---

## 7. Inductive Types (`inductive.ts`)

The most complex part of the kernel. Entered via `Environment.addInductive`. It handles `Nat` /
`Bool` / `List` / `Eq` and the like.

What it does:

1. **Verification of the inductive declaration** — check the parameter count and the type of each
   constructor:
   - its result is the inductive type in question,
   - it satisfies **strict positivity** (the inductive type does not occur in a negative position of
     its own constructor arguments),
   - it satisfies the universe constraints (e.g. the restriction on eliminating into `Prop`).
2. **Automatic generation of the recursor** — construct the type of the eliminator with its motive,
   minor premises, and major premise, and add it to the environment as a `RecursorVal`.
3. **Registration of the ι-reduction rules** (`RecursorRule`) —
   `rec ... (ctorᵢ args)  ⟶  (apply the i-th minor premise to args and the recursive results)`. WHNF
   uses these.
4. **Subsingleton / large elimination** — a `Prop` inductive may be eliminated into `Type` only
   under specific conditions (such as a single constructor). There is no K-like reduction: ι fires
   only when the major premise reduces to an actual constructor term, so e.g. `Eq.rec` does not
   reduce on a variable proof.

---

## 8. Quotient Types (`quot.ts`)

One of the few axiomatic constructs trusted as built-in. `Environment.addQuot` introduces `Quot`,
`Quot.mk`, `Quot.lift`, `Quot.ind` (it requires `Eq` to already be present), and the computation
rule `Quot.lift f h (Quot.mk r a)  ⟶  f a` is incorporated into WHNF / `isDefEq`.

---

## 9. Test Strategy

Since soundness is everything, both sides are tested thickly: "accept correct terms" and "reject
ill-formed terms." Each kernel test file mirrors a source module (six files, `*_test.ts`):

| test file              | covers                                                         |
| ---------------------- | -------------------------------------------------------------- |
| `name_test.ts`         | name equality / hashing / string round-trip                    |
| `level_test.ts`        | level construction, normalization, equivalence, ordering       |
| `expr_test.ts`         | constructors, cache flags, traversal, de Bruijn operations     |
| `type_checker_test.ts` | `infer` / `isDefEq` (β/δ/ζ/η), recursor-based `Nat` arithmetic |
| `inductive_test.ts`    | inductive verification, recursor + ι-reduction, rejections     |
| `quot_test.ts`         | the `Quot` family and its computation rule                     |

Emphasis:

1. **de Bruijn operations** — boundary cases of offsets for `instantiate1` / `abstract` /
   `liftLooseBVars`, against hand-computed expected values.
2. **Level normalization** — representative cases of `max` / `imax` / `succ`, and the order `leq`.
3. **Type inference golden cases** — e.g. `fun (x : Nat) => x : Nat → Nat`.
4. **defeq positive/negative** — each of β / δ / ζ / η.
5. **Rejection tests (the heart of soundness)** — type mismatches, universe parameter count
   mismatches, loose BVars, positivity-violating inductives, etc. **always** throw.

---

## 10. Module Layout

The kernel is roughly modeled on the Lean 4 kernel's decomposition, but several small modules have
been consolidated (traversal and de Bruijn ops into `expr.ts`; level normalization into `level.ts`;
the local context into `type_checker.ts`).

| cic-ts module     | Contents                                                         |
| ----------------- | ---------------------------------------------------------------- |
| `name.ts`         | hierarchical names                                               |
| `level.ts`        | universe levels, normalization, ordering, instantiation          |
| `expr.ts`         | `Expr` representation, constructors, traversal, de Bruijn ops    |
| `hash.ts`         | deterministic 32-bit hashing utilities (backs the cached `hash`) |
| `declaration.ts`  | declaration / constant-info types and the `mk*` input builders   |
| `environment.ts`  | the `Environment` and `addDecl` / `addInductive` / `addQuot`     |
| `type_checker.ts` | `infer` / `whnf` / `isDefEq` / `check` and the local context     |
| `inductive.ts`    | inductive verification and recursor generation                   |
| `quot.ts`         | quotient types                                                   |
| `exception.ts`    | `KernelError`                                                    |
| `mod.ts`          | the public entry point (re-exports the API surface)              |

---

## 11. Implementation Status

All of the following are implemented and covered by tests:

1. **Representation** — `Name`, `Level`, `Expr` with constructors, equality, cached hashing/flags.
2. **Operations** — traversal combinators, `instantiate` / `abstract`, level normalization.
3. **Core type checker** — `infer` / `whnf` / `isDefEq` (β/δ/ζ/η) over `Sort` / `Pi` / `Lambda` /
   `App` / `Const` / `Let`, and `addDecl` for `axiom` / `definition` / `theorem` / `opaque`.
4. **Inductive types** — verification + recursor generation + ι-reduction (`Nat` / `Bool` / `List` /
   `Eq`).
5. **Quotient types** — the `Quot` family and its computation rule.

Possible future work: cross-checking exported terms against Lean 4, and reading Lean's environment
export format.
