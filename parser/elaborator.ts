// Elaborator (PARSER_SPEC §5).
//
// Lowers the surface AST to kernel terms and declarations. Its whole job is:
//   - name resolution: bound names → de Bruijn indices, free names → `Const`;
//   - desugaring: `Type`/`Prop` → `Sort`, `A → B` → a non-dependent `Pi`,
//     numerals → `Nat` literals;
//   - folding declaration parameters into the type (`Pi`) and value (`Lambda`);
//   - for inductives, prepending parameters to constructor types and qualifying
//     constructor names (`refl` → `Eq.refl`).
//
// It does NOT do type inference, implicit-argument synthesis, unification, or
// universe inference — everything must be explicit (see PARSER_SPEC §0, §8).
// Unknown *constants* are not diagnosed here; the kernel rejects them at
// `addDecl`. The elaborator only reports unbound universe parameters and a few
// structural mistakes, with source positions.

import {
  type Expr,
  mkApp,
  mkBVar,
  mkConst,
  mkLambda,
  mkNatLit,
  mkPi,
  mkSort,
} from "../kernel/expr.ts";
import {
  type Level,
  levelZero,
  mkLevelIMax,
  mkLevelLit,
  mkLevelMax,
  mkLevelParam,
  mkLevelSucc,
  mkLevelSuccN,
} from "../kernel/level.ts";
import { anonymousName, type Name, nameFromString } from "../kernel/name.ts";
import {
  type Declaration,
  type InductiveDeclaration,
  mkAxiom,
  mkDefinition,
  mkOpaque,
  mkTheorem,
} from "../kernel/declaration.ts";
import { ParseError, type SBinder, type SCommand, type SExpr, type SLevel } from "./syntax.ts";

/** The kernel action a command elaborates to; the driver applies it. */
export type ElabResult =
  | { readonly kind: "decl"; readonly decl: Declaration }
  | { readonly kind: "inductive"; readonly decl: InductiveDeclaration }
  | { readonly kind: "initQuot" }
  | { readonly kind: "check"; readonly expr: Expr };

// --- Levels -----------------------------------------------------------------

export function elabLevel(l: SLevel, uparams: readonly string[]): Level {
  switch (l.kind) {
    case "num":
      return mkLevelLit(Number(l.value));
    case "ident": {
      if (uparams.includes(l.name)) return mkLevelParam(nameFromString(l.name));
      throw new ParseError(l.pos, `unknown universe parameter '${l.name}'`);
    }
    case "add":
      return mkLevelSuccN(elabLevel(l.base, uparams), Number(l.n));
    case "max":
      return mkLevelMax(elabLevel(l.lhs, uparams), elabLevel(l.rhs, uparams));
    case "imax":
      return mkLevelIMax(elabLevel(l.lhs, uparams), elabLevel(l.rhs, uparams));
  }
}

// --- Expressions ------------------------------------------------------------

/**
 * Elaborate an expression. `scope` lists binder names from outermost to
 * innermost; a name found at position `j` becomes `BVar (scope.length-1-j)`.
 */
export function elabExpr(e: SExpr, scope: readonly string[], uparams: readonly string[]): Expr {
  switch (e.kind) {
    case "ident": {
      const idx = lastIndexOf(scope, e.name);
      if (idx >= 0) {
        if (e.univs && e.univs.length > 0) {
          throw new ParseError(e.pos, `local variable '${e.name}' cannot take universe arguments`);
        }
        return mkBVar(BigInt(scope.length - 1 - idx));
      }
      const univs = (e.univs ?? []).map((u) => elabLevel(u, uparams));
      return mkConst(nameFromString(e.name), univs);
    }
    case "sort":
      return mkSort(elabLevel(e.level, uparams));
    case "type":
      return mkSort(e.level ? mkLevelSucc(elabLevel(e.level, uparams)) : mkLevelLit(1));
    case "prop":
      return mkSort(levelZero);
    case "num":
      return mkNatLit(e.value);
    case "app":
      return mkApp(elabExpr(e.fn, scope, uparams), elabExpr(e.arg, scope, uparams));
    case "arrow": {
      const from = elabExpr(e.from, scope, uparams);
      // the codomain sits under one (anonymous) binder
      const to = elabExpr(e.to, [...scope, "_"], uparams);
      return mkPi(anonymousName, from, to);
    }
    case "lam":
    case "pi": {
      const { items, scope: inner } = elabTelescope(e.binders, scope, uparams);
      const body = elabExpr(e.body, inner, uparams);
      const build = e.kind === "lam" ? mkLambda : mkPi;
      let r = body;
      for (let i = items.length - 1; i >= 0; i--) r = build(items[i]!.name, items[i]!.type, r);
      return r;
    }
  }
}

interface TeleItem {
  readonly name: Name;
  readonly type: Expr;
}

/**
 * Elaborate a binder telescope. Each binder's type is elaborated in the scope
 * accumulated so far (earlier binders are visible to later types), so the
 * returned types already carry correct de Bruijn indices for folding.
 */
function elabTelescope(
  binders: readonly SBinder[],
  scope: readonly string[],
  uparams: readonly string[],
): { items: TeleItem[]; scope: string[] } {
  const items: TeleItem[] = [];
  const s = [...scope];
  for (const group of binders) {
    for (const nm of group.names) {
      items.push({ name: nameFromString(nm), type: elabExpr(group.type, s, uparams) });
      s.push(nm);
    }
  }
  return { items, scope: s };
}

function piTelescope(items: readonly TeleItem[], body: Expr): Expr {
  let r = body;
  for (let i = items.length - 1; i >= 0; i--) r = mkPi(items[i]!.name, items[i]!.type, r);
  return r;
}

function lambdaTelescope(items: readonly TeleItem[], body: Expr): Expr {
  let r = body;
  for (let i = items.length - 1; i >= 0; i--) r = mkLambda(items[i]!.name, items[i]!.type, r);
  return r;
}

// --- Commands ---------------------------------------------------------------

export function elaborate(cmd: SCommand): ElabResult {
  switch (cmd.kind) {
    case "axiom": {
      const type = elabExpr(cmd.type, [], cmd.univParams);
      return {
        kind: "decl",
        decl: mkAxiom(nameFromString(cmd.name), levelParams(cmd.univParams), type),
      };
    }
    case "def":
    case "theorem":
    case "opaque":
      return { kind: "decl", decl: elabDefLike(cmd) };
    case "inductive":
      return { kind: "inductive", decl: elabInductive(cmd) };
    case "initQuot":
      return { kind: "initQuot" };
    case "check":
      return { kind: "check", expr: elabExpr(cmd.expr, [], []) };
  }
}

function elabDefLike(cmd: SCommand & { kind: "def" | "theorem" | "opaque" }): Declaration {
  const up = cmd.univParams;
  const { items, scope } = elabTelescope(cmd.binders, [], up);
  const type = piTelescope(items, elabExpr(cmd.type, scope, up));
  const value = lambdaTelescope(items, elabExpr(cmd.value, scope, up));
  const name = nameFromString(cmd.name);
  const lp = levelParams(up);
  if (cmd.kind === "def") return mkDefinition(name, lp, type, value);
  if (cmd.kind === "theorem") return mkTheorem(name, lp, type, value);
  return mkOpaque(name, lp, type, value);
}

function elabInductive(cmd: SCommand & { kind: "inductive" }): InductiveDeclaration {
  const up = cmd.univParams;
  const { items: params, scope } = elabTelescope(cmd.params, [], up);
  const indType = piTelescope(params, elabExpr(cmd.type, scope, up));
  const indName = nameFromString(cmd.name);
  const ctors = cmd.ctors.map((c) => ({
    // qualify the constructor name with the inductive's name (refl → Eq.refl)
    name: nameFromString(`${cmd.name}.${c.name}`),
    type: piTelescope(params, elabExpr(c.type, scope, up)),
  }));
  return {
    levelParams: levelParams(up),
    numParams: params.length,
    isUnsafe: false,
    types: [{ name: indName, type: indType, ctors }],
  };
}

// --- helpers ----------------------------------------------------------------

function levelParams(names: readonly string[]): Name[] {
  return names.map(nameFromString);
}

function lastIndexOf(xs: readonly string[], x: string): number {
  for (let i = xs.length - 1; i >= 0; i--) {
    if (xs[i] === x) return i;
  }
  return -1;
}
