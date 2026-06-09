// The type checker (SPEC.md Section 5) — the core of the kernel.
//
// Implements `infer` / `whnf` / `isDefEq` / `check`, ported from the strategy in
// Lean's `type_checker.cpp`. Phase 2 scope: Sort, Pi, Lambda, App, Const, Let,
// FVar, Lit, MData. Inductive recursors (ι) and projections need Phase 3, and
// quotients need Phase 4; those node kinds raise an "unsupported" error here.
//
// `infer` is a *checking* inferer: it validates as it goes (argument types,
// binder domains are sorts, etc.), so it doubles as the kernel's `check`.

import {
  type Expr,
  exprEq,
  getAppArgs,
  getAppFn,
  type Literal,
  mkApp,
  mkAppN,
  mkBVar,
  mkConst,
  mkFVar,
  mkLambda,
  mkNatLit,
  mkPi,
  mkProj,
  mkSort,
} from "./expr.ts";
import { type Level, levelIsEquiv, levelZero, mkLevelIMaxSmart, mkLevelSucc } from "./level.ts";
import { mkNumName, type Name, nameEq, nameFromString, nameToString } from "./name.ts";
import { abstract, instantiate1, instantiateLevelParams, liftLooseBVars } from "./instantiate.ts";
import { LocalContext } from "./localContext.ts";
import { constValue, isUnfoldable, recursorMajorIdx, type RecursorVal } from "./declaration.ts";
import { kernelError } from "./exception.ts";
import type { Environment } from "./environment.ts";

const natName = nameFromString("Nat");
const stringName = nameFromString("String");
const natZeroName = nameFromString("Nat.zero");
const natSuccName = nameFromString("Nat.succ");
const freshPrefix = nameFromString("_kfv");

function literalType(lit: Literal): Expr {
  return mkConst(lit.kind === "natVal" ? natName : stringName);
}

/** Expand a `Nat` literal into constructor form so a recursor can reduce on it. */
function natLitToConstructor(value: bigint): Expr {
  if (value === 0n) return mkConst(natZeroName);
  return mkApp(mkConst(natSuccName), mkNatLit(value - 1n));
}

function levelsIsEquiv(as: readonly Level[], bs: readonly Level[]): boolean {
  if (as.length !== bs.length) return false;
  for (let i = 0; i < as.length; i++) {
    if (!levelIsEquiv(as[i]!, bs[i]!)) return false;
  }
  return true;
}

export class TypeChecker {
  private lctx = new LocalContext();
  private freshCounter = 0;

  constructor(readonly env: Environment) {}

  private mkFreshFVar(): Expr & { kind: "fvar" } {
    const id = mkNumName(freshPrefix, BigInt(this.freshCounter++));
    return mkFVar(id) as Expr & { kind: "fvar" };
  }

  // --- Local-context helpers (used by inductive construction, Phase 3) ------

  /** Introduce a fresh free variable into the (persistent) local context. */
  mkLocalDecl(name: Name, type: Expr, value?: Expr): Expr {
    const fv = this.mkFreshFVar();
    const decl = value === undefined
      ? { fvarId: fv.id, name, type }
      : { fvarId: fv.id, name, type, value };
    this.lctx = this.lctx.push(decl);
    return fv;
  }

  /** The recorded type of a free variable. */
  localType(fv: Expr): Expr {
    if (fv.kind !== "fvar") return kernelError("other", "localType: not an fvar");
    const decl = this.lctx.find(fv.id);
    if (decl === undefined) return kernelError("other", "localType: unknown fvar");
    return decl.type;
  }

  /** Build `(fvars) → body`, abstracting the free variables into Pi binders. */
  mkForallFVars(fvars: readonly Expr[], body: Expr): Expr {
    let r = abstract(body, fvars);
    for (let i = fvars.length - 1; i >= 0; i--) {
      const fv = fvars[i]!;
      if (fv.kind !== "fvar") return kernelError("other", "mkForallFVars: not an fvar");
      const ty = abstract(this.localType(fv), fvars.slice(0, i));
      r = mkPi(this.lctx.find(fv.id)!.name, ty, r);
    }
    return r;
  }

  /** Build `fun (fvars) => body`, abstracting the free variables into lambdas. */
  mkLambdaFVars(fvars: readonly Expr[], body: Expr): Expr {
    let r = abstract(body, fvars);
    for (let i = fvars.length - 1; i >= 0; i--) {
      const fv = fvars[i]!;
      if (fv.kind !== "fvar") return kernelError("other", "mkLambdaFVars: not an fvar");
      const ty = abstract(this.localType(fv), fvars.slice(0, i));
      r = mkLambda(this.lctx.find(fv.id)!.name, ty, r);
    }
    return r;
  }

  /** Run `fn` with a fresh free variable bound to (`name` : `type` [:= `value`]). */
  private withBinder<T>(
    name: Name,
    type: Expr,
    value: Expr | undefined,
    fn: (fvar: Expr) => T,
  ): T {
    const fv = this.mkFreshFVar();
    const saved = this.lctx;
    const decl = value === undefined
      ? { fvarId: fv.id, name, type }
      : { fvarId: fv.id, name, type, value };
    this.lctx = saved.push(decl);
    try {
      return fn(fv);
    } finally {
      this.lctx = saved;
    }
  }

  // --- Inference (Section 5.1) ----------------------------------------------

  infer(e: Expr): Expr {
    switch (e.kind) {
      case "bvar":
        return kernelError("looseBVar", `infer: loose bound variable #${e.idx}`);
      case "mvar":
        return kernelError("unexpectedMVar", "infer: metavariable reached the kernel");
      case "fvar": {
        const decl = this.lctx.find(e.id);
        if (decl === undefined) return kernelError("other", "infer: unknown free variable");
        return decl.type;
      }
      case "sort":
        return mkSort(mkLevelSucc(e.level));
      case "const":
        return this.inferConst(e.name, e.levels);
      case "lit":
        return literalType(e.lit);
      case "mdata":
        return this.infer(e.expr);
      case "app":
        return this.inferApp(e);
      case "lam":
        return this.inferLambda(e);
      case "pi":
        return this.inferPi(e);
      case "let":
        return this.inferLet(e);
      case "proj":
        return this.inferProj(e);
    }
  }

  private inferProj(e: Expr & { kind: "proj" }): Expr {
    const structType = this.whnf(this.infer(e.expr));
    const fn = getAppFn(structType);
    const args = getAppArgs(structType);
    if (fn.kind !== "const") {
      return kernelError("typeMismatch", "infer: projection of a non-structure");
    }
    const ind = this.env.find(fn.name);
    if (ind === undefined || ind.kind !== "inductive" || ind.ctors.length !== 1) {
      return kernelError(
        "typeMismatch",
        "infer: projection requires a single-constructor structure",
      );
    }
    const ctorInfo = this.env.find(ind.ctors[0]!);
    if (ctorInfo === undefined || ctorInfo.kind !== "constructor") {
      return kernelError("other", "infer: missing constructor for projection");
    }
    let ctorType = instantiateLevelParams(ctorInfo.type, ctorInfo.levelParams, fn.levels);
    // Apply the structure's parameters.
    for (let i = 0; i < ind.numParams; i++) {
      const pi = this.ensurePi(ctorType);
      if (i >= args.length) {
        return kernelError("typeMismatch", "infer: projection parameter missing");
      }
      ctorType = instantiate1(pi.body, args[i]!);
    }
    // Strip preceding fields, substituting projections of the same value.
    const idx = Number(e.idx);
    for (let j = 0; j < idx; j++) {
      const pi = this.ensurePi(ctorType);
      ctorType = instantiate1(pi.body, mkProj(e.struct, BigInt(j), e.expr));
    }
    return this.ensurePi(ctorType).type;
  }

  private inferConst(name: Name, levels: readonly Level[]): Expr {
    const ci = this.env.find(name);
    if (ci === undefined) {
      return kernelError("unknownConstant", `infer: unknown constant '${nameToString(name)}'`);
    }
    if (levels.length !== ci.levelParams.length) {
      return kernelError(
        "universeMismatch",
        `infer: constant '${
          nameToString(name)
        }' expects ${ci.levelParams.length} universe(s), got ${levels.length}`,
      );
    }
    return instantiateLevelParams(ci.type, ci.levelParams, levels);
  }

  private inferApp(e: Expr & { kind: "app" }): Expr {
    const fnType = this.infer(e.fn);
    const pi = this.ensurePi(fnType);
    const argType = this.infer(e.arg);
    if (!this.isDefEq(argType, pi.type)) {
      return kernelError("typeMismatch", "infer: application argument has the wrong type");
    }
    return instantiate1(pi.body, e.arg);
  }

  private inferLambda(e: Expr & { kind: "lam" }): Expr {
    this.ensureSort(this.infer(e.type));
    return this.withBinder(e.name, e.type, undefined, (fv) => {
      const bodyType = this.infer(instantiate1(e.body, fv));
      return mkPi(e.name, e.type, abstract(bodyType, [fv]), e.info);
    });
  }

  private inferPi(e: Expr & { kind: "pi" }): Expr {
    const u = this.ensureSort(this.infer(e.type));
    return this.withBinder(e.name, e.type, undefined, (fv) => {
      const v = this.ensureSort(this.infer(instantiate1(e.body, fv)));
      return mkSort(mkLevelIMaxSmart(u, v));
    });
  }

  private inferLet(e: Expr & { kind: "let" }): Expr {
    this.ensureSort(this.infer(e.type));
    this.check(e.value, e.type);
    return this.withBinder(e.name, e.type, e.value, (fv) => {
      const bodyType = this.infer(instantiate1(e.body, fv));
      // the let value is definitionally the binder, so substitute it back in
      return instantiate1(abstract(bodyType, [fv]), e.value);
    });
  }

  /** Infer the type of `e` and verify it is definitionally equal to `expected`. */
  check(e: Expr, expected: Expr): void {
    const t = this.infer(e);
    if (!this.isDefEq(t, expected)) {
      kernelError("typeMismatch", "check: inferred type does not match the expected type");
    }
  }

  /** Reduce `e` and require it to be a `Sort`, returning its level. */
  ensureSort(e: Expr): Level {
    const w = this.whnf(e);
    if (w.kind === "sort") return w.level;
    return kernelError("expectedSort", "expected a sort");
  }

  /** Reduce `e` and require it to be a `Pi`, returning the (whnf'd) node. */
  ensurePi(e: Expr): Expr & { kind: "pi" } {
    const w = this.whnf(e);
    if (w.kind === "pi") return w;
    return kernelError("expectedPi", "expected a function type");
  }

  // --- Weak head normal form (Section 5.2) ---------------------------------

  /** Reduce `e` to weak head normal form (β/ζ, δ, ι, and projection). */
  whnf(e: Expr): Expr {
    let cur = e;
    for (;;) {
      const core = this.whnfCore(cur);
      const unfolded = this.unfoldDefinition(core);
      if (unfolded !== undefined) {
        cur = unfolded;
        continue;
      }
      const reduced = this.reduceRecursor(core); // ι
      if (reduced !== undefined) {
        cur = reduced;
        continue;
      }
      const projected = this.reduceProj(core);
      if (projected !== undefined) {
        cur = projected;
        continue;
      }
      return core;
    }
  }

  /** β, ζ, mdata, and fvar-let reductions, without δ-unfolding of constants. */
  private whnfCore(e: Expr): Expr {
    switch (e.kind) {
      case "bvar":
        return kernelError("looseBVar", `whnf: loose bound variable #${e.idx}`);
      case "fvar": {
        const decl = this.lctx.find(e.id);
        if (decl?.value !== undefined) return this.whnfCore(decl.value); // δ for let-fvars
        return e;
      }
      case "mdata":
        return this.whnfCore(e.expr);
      case "let":
        return this.whnfCore(instantiate1(e.body, e.value)); // ζ
      case "app": {
        const fn = this.whnfCore(e.fn);
        if (fn.kind === "lam") return this.whnfCore(instantiate1(fn.body, e.arg)); // β
        if (fn === e.fn) return e;
        return this.whnfCore(mkApp(fn, e.arg));
      }
      default:
        return e;
    }
  }

  /** δ-unfold the head constant of `e` if it is unfoldable; else `undefined`. */
  private unfoldDefinition(e: Expr): Expr | undefined {
    const fn = getAppFn(e);
    if (fn.kind !== "const") return undefined;
    const ci = this.env.find(fn.name);
    if (ci === undefined || !isUnfoldable(ci)) return undefined;
    if (fn.levels.length !== ci.levelParams.length) return undefined;
    const value = constValue(ci);
    if (value === undefined) return undefined;
    const body = instantiateLevelParams(value, ci.levelParams, fn.levels);
    return mkAppN(body, getAppArgs(e));
  }

  /** ι-reduce a recursor applied to a constructor (or Nat literal, or K-target). */
  private reduceRecursor(e: Expr): Expr | undefined {
    const recFn = getAppFn(e);
    if (recFn.kind !== "const") return undefined;
    const ci = this.env.find(recFn.name);
    if (ci === undefined || ci.kind !== "recursor") return undefined;
    const recArgs = getAppArgs(e);
    const majorIdx = recursorMajorIdx(ci);
    if (majorIdx >= recArgs.length) return undefined;

    let major = recArgs[majorIdx]!;
    if (ci.k) {
      const k = this.toCnstrWhenK(ci, major);
      if (k !== undefined) major = k;
    }
    major = this.whnf(major);
    if (major.kind === "lit" && major.lit.kind === "natVal") {
      major = natLitToConstructor(major.lit.value);
    }

    const majorFn = getAppFn(major);
    if (majorFn.kind !== "const") return undefined;
    const rule = ci.rules.find((r) => nameEq(r.ctor, majorFn.name));
    if (rule === undefined) return undefined;
    const majorArgs = getAppArgs(major);
    if (rule.nfields > majorArgs.length) return undefined;
    if (recFn.levels.length !== ci.levelParams.length) return undefined;

    let rhs = instantiateLevelParams(rule.rhs, ci.levelParams, recFn.levels);
    // Apply parameters, motives, and minor premises from the recursor spine.
    const nPMM = ci.numParams + ci.numMotives + ci.numMinors;
    rhs = mkAppN(rhs, recArgs.slice(0, nPMM));
    // Apply the constructor's fields (skipping its parameters).
    const nctorParams = majorArgs.length - rule.nfields;
    rhs = mkAppN(rhs, majorArgs.slice(nctorParams));
    // Re-apply any arguments that followed the major premise.
    if (recArgs.length > majorIdx + 1) {
      rhs = mkAppN(rhs, recArgs.slice(majorIdx + 1));
    }
    return rhs;
  }

  /** For K-like recursors, replace the major premise with its unique constructor. */
  private toCnstrWhenK(rec: RecursorVal, major: Expr): Expr | undefined {
    const type = this.whnf(this.infer(major));
    const fn = getAppFn(type);
    if (fn.kind !== "const" || !nameEq(fn.name, rec.all[0]!)) return undefined;
    const newCtor = this.mkNullaryCtor(type, rec.numParams);
    if (newCtor === undefined) return undefined;
    if (!this.isDefEq(type, this.infer(newCtor))) return undefined;
    return newCtor;
  }

  /** Build `Ctor params` for the single-constructor inductive in `type = I params …`. */
  private mkNullaryCtor(type: Expr, numParams: number): Expr | undefined {
    const fn = getAppFn(type);
    if (fn.kind !== "const") return undefined;
    const ci = this.env.find(fn.name);
    if (ci === undefined || ci.kind !== "inductive" || ci.ctors.length !== 1) return undefined;
    return mkAppN(mkConst(ci.ctors[0]!, fn.levels), getAppArgs(type).slice(0, numParams));
  }

  /** Reduce a projection applied to a constructor application. */
  private reduceProj(e: Expr): Expr | undefined {
    if (e.kind !== "proj") return undefined;
    const c = this.whnf(e.expr);
    const fn = getAppFn(c);
    if (fn.kind !== "const") return undefined;
    const ci = this.env.find(fn.name);
    if (ci === undefined || ci.kind !== "constructor") return undefined;
    const args = getAppArgs(c);
    const idx = ci.numParams + Number(e.idx);
    if (idx >= args.length) return undefined;
    return args[idx];
  }

  // --- Definitional equality (Section 5.3) ---------------------------------

  /** Whether `a` and `b` are definitionally equal. */
  isDefEq(a: Expr, b: Expr): boolean {
    if (exprEq(a, b)) return true;
    return this.isDefEqCore(this.whnf(a), this.whnf(b));
  }

  /** Compare two terms already in weak head normal form. */
  private isDefEqCore(a: Expr, b: Expr): boolean {
    if (exprEq(a, b)) return true;

    // η: expand whichever side is not a lambda.
    const aLam = a.kind === "lam";
    const bLam = b.kind === "lam";
    if (aLam !== bLam) {
      if (aLam) return this.isDefEqEta(a as Expr & { kind: "lam" }, b);
      return this.isDefEqEta(b as Expr & { kind: "lam" }, a);
    }

    let structural = false;
    if (a.kind === b.kind) {
      switch (a.kind) {
        case "sort":
          structural = levelIsEquiv(a.level, (b as typeof a).level);
          break;
        case "const":
          structural = nameEq(a.name, (b as typeof a).name) &&
            levelsIsEquiv(a.levels, (b as typeof a).levels);
          break;
        case "fvar":
          structural = nameEq(a.id, (b as typeof a).id);
          break;
        case "mvar":
          structural = nameEq(a.id, (b as typeof a).id);
          break;
        case "lit":
          structural = a.lit.kind === (b as typeof a).lit.kind &&
            a.lit.value === (b as typeof a).lit.value;
          break;
        case "app": {
          const bb = b as typeof a;
          structural = this.isDefEq(a.fn, bb.fn) && this.isDefEq(a.arg, bb.arg);
          break;
        }
        case "pi":
        case "lam": {
          const bb = b as typeof a;
          structural = this.isDefEq(a.type, bb.type) &&
            this.withBinder(
              a.name,
              a.type,
              undefined,
              (fv) => this.isDefEq(instantiate1(a.body, fv), instantiate1(bb.body, fv)),
            );
          break;
        }
        case "proj": {
          const bb = b as typeof a;
          structural = a.idx === bb.idx && nameEq(a.struct, bb.struct) &&
            this.isDefEq(a.expr, bb.expr);
          break;
        }
        default:
          structural = false;
      }
    }
    if (structural) return true;

    return this.isDefEqProofIrrel(a, b);
  }

  /** η: compare a lambda with the η-expansion of a non-lambda. */
  private isDefEqEta(lam: Expr & { kind: "lam" }, other: Expr): boolean {
    const expanded = mkLambda(
      lam.name,
      lam.type,
      mkApp(liftLooseBVars(other, 0, 1), mkBVar(0n)),
      lam.info,
    );
    return this.isDefEqCore(lam, expanded);
  }

  /**
   * Proof irrelevance: any two proofs of the same proposition are equal. Holds
   * when `a`'s type is a `Prop` and `b` has a definitionally equal type.
   */
  private isDefEqProofIrrel(a: Expr, b: Expr): boolean {
    try {
      const ta = this.infer(a);
      const sort = this.whnf(this.infer(ta));
      if (sort.kind !== "sort" || !levelIsEquiv(sort.level, levelZero)) return false;
      const tb = this.infer(b);
      return this.isDefEq(ta, tb);
    } catch {
      return false;
    }
  }
}
