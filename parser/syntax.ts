// Surface syntax AST (PARSER_SPEC §3–§4).
//
// The named, position-carrying tree the parser produces and the elaborator
// later lowers to kernel `Expr` / `Declaration`. Identifiers are still names
// here (not yet de Bruijn indices), and no type information is attached.

/** A source position: 1-based line/column and a 0-based code-point offset. */
export interface Pos {
  readonly offset: number;
  readonly line: number;
  readonly col: number;
}

/** An error with a source position, used by the lexer, parser, and elaborator. */
export class ParseError extends Error {
  override readonly name = "ParseError";
  constructor(readonly pos: Pos, message: string) {
    super(`${pos.line}:${pos.col}: ${message}`);
  }
}

// --- Universe levels --------------------------------------------------------

export type SLevel =
  | { readonly kind: "num"; readonly value: bigint; readonly pos: Pos }
  | { readonly kind: "ident"; readonly name: string; readonly pos: Pos } // universe param
  | { readonly kind: "add"; readonly base: SLevel; readonly n: bigint; readonly pos: Pos }
  | { readonly kind: "max"; readonly lhs: SLevel; readonly rhs: SLevel; readonly pos: Pos }
  | { readonly kind: "imax"; readonly lhs: SLevel; readonly rhs: SLevel; readonly pos: Pos };

// --- Binders ----------------------------------------------------------------

export type SBinderInfo = "explicit" | "implicit";

/** A binder group like `(x y : T)` or `{x : T}` — one or more names, one type. */
export interface SBinder {
  readonly names: readonly string[];
  readonly type: SExpr;
  readonly info: SBinderInfo;
  readonly pos: Pos;
}

// --- Expressions ------------------------------------------------------------

export type SExpr =
  | {
    readonly kind: "ident";
    readonly name: string;
    readonly univs?: readonly SLevel[];
    readonly pos: Pos;
  }
  | { readonly kind: "sort"; readonly level: SLevel; readonly pos: Pos } // Sort u
  | { readonly kind: "type"; readonly level?: SLevel; readonly pos: Pos } // Type / Type u
  | { readonly kind: "prop"; readonly pos: Pos } // Prop
  | { readonly kind: "num"; readonly value: bigint; readonly pos: Pos } // Nat literal
  | { readonly kind: "app"; readonly fn: SExpr; readonly arg: SExpr; readonly pos: Pos }
  | {
    readonly kind: "lam";
    readonly binders: readonly SBinder[];
    readonly body: SExpr;
    readonly pos: Pos;
  }
  | {
    readonly kind: "pi";
    readonly binders: readonly SBinder[];
    readonly body: SExpr;
    readonly pos: Pos;
  }
  | { readonly kind: "arrow"; readonly from: SExpr; readonly to: SExpr; readonly pos: Pos };

// --- Commands ---------------------------------------------------------------

export interface SCtor {
  readonly name: string;
  readonly type: SExpr;
  readonly pos: Pos;
}

export type SCommand =
  | {
    readonly kind: "axiom";
    readonly name: string;
    readonly univParams: readonly string[];
    readonly type: SExpr;
    readonly pos: Pos;
  }
  | {
    readonly kind: "def" | "theorem" | "opaque";
    readonly name: string;
    readonly univParams: readonly string[];
    readonly binders: readonly SBinder[];
    readonly type: SExpr;
    readonly value: SExpr;
    readonly pos: Pos;
  }
  | {
    readonly kind: "inductive";
    readonly name: string;
    readonly univParams: readonly string[];
    readonly params: readonly SBinder[];
    readonly type: SExpr;
    readonly ctors: readonly SCtor[];
    readonly pos: Pos;
  }
  | { readonly kind: "initQuot"; readonly pos: Pos }
  | { readonly kind: "check"; readonly expr: SExpr; readonly pos: Pos };

/** A whole input file: a sequence of commands. */
export type SModule = readonly SCommand[];
