// Declarations and constant info (SPEC.md Section 6.1).
//
// Corresponds to Lean's `declaration.h`. Phase 2 covers the non-inductive
// declarations: axioms, definitions, theorems, and opaque constants. Inductive
// types (Phase 3) extend this union later.
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

// --- Inductive types (Phase 3) ---------------------------------------------

/** The stored info for an inductive type. */
export interface InductiveVal {
  readonly kind: "inductive";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly numParams: number;
  readonly numIndices: number;
  readonly all: readonly Name[]; // all inductives in the mutual block (just `name` here)
  readonly ctors: readonly Name[];
  readonly isRec: boolean;
  readonly isUnsafe: boolean;
}

/** The stored info for a constructor. */
export interface ConstructorVal {
  readonly kind: "constructor";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly induct: Name;
  readonly cidx: number;
  readonly numParams: number;
  readonly numFields: number;
  readonly isUnsafe: boolean;
}

/** One ι-reduction rule of a recursor: how it computes on a given constructor. */
export interface RecursorRule {
  readonly ctor: Name;
  readonly nfields: number;
  readonly rhs: Expr;
}

/** The stored info for a recursor (eliminator). */
export interface RecursorVal {
  readonly kind: "recursor";
  readonly name: Name;
  readonly levelParams: readonly Name[];
  readonly type: Expr;
  readonly all: readonly Name[];
  readonly numParams: number;
  readonly numIndices: number;
  readonly numMotives: number;
  readonly numMinors: number;
  readonly rules: readonly RecursorRule[];
  readonly isUnsafe: boolean;
}

export type Declaration = AxiomVal | DefinitionVal | TheoremVal | OpaqueVal;
export type ConstantInfo =
  | Declaration
  | InductiveVal
  | ConstructorVal
  | RecursorVal;

// --- Inductive declaration (input to Environment.addInductive) --------------

export interface Constructor {
  readonly name: Name;
  readonly type: Expr;
}

export interface InductiveType {
  readonly name: Name;
  readonly type: Expr;
  readonly ctors: readonly Constructor[];
}

export interface InductiveDeclaration {
  readonly levelParams: readonly Name[];
  readonly numParams: number;
  readonly types: readonly InductiveType[];
  readonly isUnsafe: boolean;
}

/** The index at which a recursor's major premise sits in its argument spine. */
export function recursorMajorIdx(rec: RecursorVal): number {
  return rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices;
}

/** Whether the kernel may δ-unfold this constant during reduction. */
export function isUnfoldable(ci: ConstantInfo): boolean {
  return ci.kind === "definition" || ci.kind === "theorem";
}

/** The defining value, if any (definitions, theorems, opaque constants). */
export function constValue(ci: ConstantInfo): Expr | undefined {
  switch (ci.kind) {
    case "definition":
    case "theorem":
    case "opaque":
      return ci.value;
    default:
      return undefined;
  }
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
