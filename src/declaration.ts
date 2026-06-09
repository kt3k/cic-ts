// Declarations and constant info (SPEC.md Section 6.1).
//
// Corresponds to Lean's `declaration.h`. Phase 2 covers the non-inductive
// declarations: axioms, definitions, theorems, and opaque constants. Inductive
// types (Phase 3) and quotients (Phase 4) extend this union later.
//
// A `Declaration` is what the user submits to `Environment.addDecl`; a
// `ConstantInfo` is what the environment stores after checking. They share the
// same shape here.

import type { Expr } from "./expr.ts";
import type { Name } from "./name.ts";

export interface AxiomVal {
  readonly kind: "axiom";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly isUnsafe: boolean;
}

export interface DefinitionVal {
  readonly kind: "definition";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly value: Expr;
}

export interface TheoremVal {
  readonly kind: "theorem";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly value: Expr;
}

export interface OpaqueVal {
  readonly kind: "opaque";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly value: Expr;
}

export type Declaration = AxiomVal | DefinitionVal | TheoremVal | OpaqueVal;
export type ConstantInfo = Declaration;

/** Whether the kernel may δ-unfold this constant during reduction. */
export function isUnfoldable(ci: ConstantInfo): boolean {
  return ci.kind === "definition" || ci.kind === "theorem";
}

/** The defining value, if any (definitions, theorems, opaque constants). */
export function constValue(ci: ConstantInfo): Expr | undefined {
  return ci.kind === "axiom" ? undefined : ci.value;
}

// --- Constructors -----------------------------------------------------------

export function mkAxiom(
  name: Name,
  levelParams: readonly Name[],
  type: Expr,
  isUnsafe = false,
): AxiomVal {
  return { kind: "axiom", name, levelParams, type, isUnsafe };
}

export function mkDefinition(
  name: Name,
  levelParams: readonly Name[],
  type: Expr,
  value: Expr,
): DefinitionVal {
  return { kind: "definition", name, levelParams, type, value };
}

export function mkTheorem(
  name: Name,
  levelParams: readonly Name[],
  type: Expr,
  value: Expr,
): TheoremVal {
  return { kind: "theorem", name, levelParams, type, value };
}

export function mkOpaque(
  name: Name,
  levelParams: readonly Name[],
  type: Expr,
  value: Expr,
): OpaqueVal {
  return { kind: "opaque", name, levelParams, type, value };
}
