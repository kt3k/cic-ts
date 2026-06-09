// Local context (SPEC.md Section 4).
//
// Corresponds to Lean's `local_ctx`. While type checking, going under a binder
// replaces its bound variable with a fresh free variable (locally nameless
// style). The context records each free variable's type, and — for `let`
// binders — its value (so reduction can δ-unfold it).

import type { Expr } from "./expr.ts";
import { type Name, nameToString } from "./name.ts";

export interface LocalDecl {
  readonly fvarId: Name;
  readonly name: Name;
  readonly type: Expr;
  readonly value?: Expr; // present for let-binders
}

export class LocalContext {
  constructor(private readonly decls: ReadonlyMap<string, LocalDecl> = new Map()) {}

  find(fvarId: Name): LocalDecl | undefined {
    return this.decls.get(nameToString(fvarId));
  }

  /** Return an extended context containing `decl` (the original is unchanged). */
  push(decl: LocalDecl): LocalContext {
    const m = new Map(this.decls);
    m.set(nameToString(decl.fvarId), decl);
    return new LocalContext(m);
  }
}
