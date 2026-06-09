// Public entry point for cic-ts.
//
// The kernel's primary API is `Environment.addDecl` (with `addInductive` /
// `addQuot` for inductive types and quotients): build a declaration out of the
// term/level/name constructors below, submit it, and the kernel type-checks it
// before admitting it. `Environment.find` / `contains` query what has been
// admitted.
//
// Internal machinery — the de Bruijn operations and generic traversal (in
// `expr.ts`), the type-checker engine (`TypeChecker`), hashing, and level
// normalization — is intentionally NOT re-exported here. Import it directly from
// the individual modules if you are extending the kernel itself.

// --- Errors ---
export { KernelError, type KernelErrorKind } from "./exception.ts";

// --- Hierarchical names ---
export {
  anonymousName,
  mkNumName,
  mkStrName,
  type Name,
  nameFromString,
  nameToString,
} from "./name.ts";

// --- Universe levels ---
export {
  type Level,
  levelZero,
  mkLevelIMax,
  mkLevelLit,
  mkLevelMax,
  mkLevelMVar,
  mkLevelParam,
  mkLevelSucc,
  mkLevelSuccN,
} from "./level.ts";

// --- Terms ---
export {
  type BinderInfo,
  type Expr,
  exprEq,
  type KVMap,
  mkApp,
  mkAppN,
  mkBVar,
  mkConst,
  mkLambda,
  mkLet,
  mkMData,
  mkNatLit,
  mkPi,
  mkProj,
  mkSort,
  mkStrLit,
} from "./expr.ts";

// --- Declarations (input builders, input types, and stored constant info) ---
export {
  type AxiomVal,
  type ConstantInfo,
  type Constructor,
  type ConstructorVal,
  type Declaration,
  type DefinitionVal,
  type InductiveDeclaration,
  type InductiveType,
  type InductiveVal,
  mkAxiom,
  mkDefinition,
  mkOpaque,
  mkTheorem,
  type OpaqueVal,
  type QuotKind,
  type QuotVal,
  type RecursorRule,
  type RecursorVal,
  type TheoremVal,
} from "./declaration.ts";

// --- The environment: the main entry point ---
export { Environment } from "./environment.ts";
