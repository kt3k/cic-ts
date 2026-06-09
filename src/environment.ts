// The environment (SPEC.md Section 6.2).
//
// Corresponds to Lean's `environment`. Holds the constants accepted so far and
// exposes `addDecl`, the kernel's main entry point: a declaration is fully type
// checked before it is admitted. The environment is immutable — `addDecl`
// returns an extended copy.

import type { ConstantInfo, Declaration, InductiveDeclaration } from "./declaration.ts";
import { type Name, nameToString } from "./name.ts";
import { kernelError } from "./exception.ts";
import { TypeChecker } from "./typeChecker.ts";
import { addInductive } from "./inductive.ts";
import { addQuot } from "./quot.ts";

export class Environment {
  constructor(private readonly consts: ReadonlyMap<string, ConstantInfo> = new Map()) {}

  /** Look up a constant by name. */
  find(name: Name): ConstantInfo | undefined {
    return this.consts.get(nameToString(name));
  }

  /** Whether a constant with this name is already declared. */
  contains(name: Name): boolean {
    return this.consts.has(nameToString(name));
  }

  /**
   * Type-check `decl` and return an environment extended with it. Throws a
   * `KernelError` if the declaration is already present or fails to type check.
   * Declarations are non-recursive, so checking happens against the current
   * environment (without `decl`).
   */
  addDecl(decl: Declaration): Environment {
    if (this.contains(decl.name)) {
      kernelError("alreadyDeclared", `addDecl: '${nameToString(decl.name)}' is already declared`);
    }
    const tc = new TypeChecker(this);
    // The declared type must itself be a type (its inferred type is a sort).
    tc.ensureSort(tc.infer(decl.type));
    // For value-carrying declarations, the value must have the declared type.
    if (decl.kind !== "axiom") {
      tc.check(decl.value, decl.type);
    }
    return this.addConstantUnchecked(decl);
  }

  /**
   * Add a constant to the environment *without* type checking it. Used by the
   * inductive elaborator, which checks declarations as it builds them and emits
   * the inductive/constructor/recursor constants directly.
   */
  addConstantUnchecked(ci: ConstantInfo): Environment {
    const m = new Map(this.consts);
    m.set(nameToString(ci.name), ci);
    return new Environment(m);
  }

  /** Type-check an inductive declaration and return an extended environment. */
  addInductive(decl: InductiveDeclaration): Environment {
    return addInductive(this, decl);
  }

  /** Add the `Quot` primitives (requires `Eq` to be present). */
  addQuot(): Environment {
    return addQuot(this);
  }
}
