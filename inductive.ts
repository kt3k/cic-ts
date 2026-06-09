// Inductive types (SPEC.md Section 7).
//
// Faithful port of Lean's kernel `inductive.cpp`, scoped to single
// (non-mutual) inductive declarations — enough for Nat, Bool, List, Eq. It
// verifies the declaration (parameters, field universes, strict positivity,
// valid result type), declares the type and its constructors, then builds and
// declares the recursor (motive, minor premises, ι-reduction rules), including
// large/small elimination and K-like reduction.

import { type Expr, exprEq, getAppArgs, getAppFn, mkApp, mkAppN, mkConst, mkSort } from "./expr.ts";
import { isNotZero, isZeroLevel, type Level, levelGeq, levelZero, mkLevelParam } from "./level.ts";
import { mkNumName, mkStrName, type Name, nameEq, nameFromString, nameToString } from "./name.ts";
import { instantiate1 } from "./instantiate.ts";
import { kernelError } from "./exception.ts";
import type {
  ConstructorVal,
  InductiveDeclaration,
  InductiveType,
  InductiveVal,
  RecursorRule,
  RecursorVal,
} from "./declaration.ts";
import type { Environment } from "./environment.ts";
import { TypeChecker } from "./type_checker.ts";

/** The recursor name for an inductive: `I.rec`. */
export function mkRecName(ind: Name): Name {
  return mkStrName(ind, "rec");
}

class AddInductive {
  private tc: TypeChecker;
  private lparams: readonly Name[];
  private levels: Level[];
  private nparams: number;
  private indType: InductiveType;
  private indName: Name;
  private indCnst: Expr;

  // Filled during checking:
  private params: Expr[] = [];
  private nindices = 0;
  private resultLevel: Level = levelZero; // set in checkInductiveType
  private elimLevel: Level = levelZero;
  private kTarget = false;
  private isRec = false;

  constructor(private startEnv: Environment, private decl: InductiveDeclaration) {
    if (decl.types.length !== 1) {
      kernelError("unsupported", "addInductive: mutual inductives are not supported");
    }
    this.indType = decl.types[0]!;
    this.indName = this.indType.name;
    this.lparams = decl.levelParams;
    this.levels = decl.levelParams.map((p) => mkLevelParam(p));
    this.nparams = decl.numParams;
    this.indCnst = mkConst(this.indName, this.levels);
    this.tc = new TypeChecker(startEnv);
  }

  private whnf(e: Expr): Expr {
    return this.tc.whnf(e);
  }

  /** The indices of `t = I params indices`, i.e. the args after the parameters. */
  private getIIndices(t: Expr): Expr[] {
    return getAppArgs(t).slice(this.nparams);
  }

  /** Whether `t`'s head is the inductive being declared. */
  private isIndAppHead(t: Expr): boolean {
    const fn = getAppFn(t);
    return fn.kind === "const" && nameEq(fn.name, this.indName);
  }

  /** Whether `t` is a fully-applied occurrence of the inductive (params + indices). */
  private isValidIndApp(t: Expr): boolean {
    if (!this.isIndAppHead(t)) return false;
    const args = getAppArgs(t);
    if (args.length !== this.nparams + this.nindices) return false;
    for (let i = 0; i < this.nparams; i++) {
      if (!exprEq(args[i]!, this.params[i]!)) return false;
    }
    return true;
  }

  // Step 1: check the inductive type, collect params, indices, result level.
  private checkInductiveType(): void {
    this.tc.ensureSort(this.tc.infer(this.indType.type));
    let t = this.whnf(this.indType.type);
    let i = 0;
    while (t.kind === "pi") {
      const fv = this.tc.mkLocalDecl(t.name, t.type);
      if (i < this.nparams) this.params.push(fv);
      t = this.whnf(instantiate1(t.body, fv));
      i++;
    }
    if (i < this.nparams) {
      kernelError("other", "addInductive: type has fewer binders than declared parameters");
    }
    this.nindices = i - this.nparams;
    if (t.kind !== "sort") kernelError("expectedSort", "addInductive: type must end in a sort");
    this.resultLevel = t.level;
  }

  // Step 2: pre-scan whether any constructor takes a recursive argument.
  private computeIsRec(): void {
    this.isRec = this.indType.ctors.some((c) => occursIn(this.indName, c.type, this.nparams));
  }

  private inductiveVal(): InductiveVal {
    return {
      kind: "inductive",
      name: this.indName,
      levelParams: this.lparams,
      type: this.indType.type,
      numParams: this.nparams,
      numIndices: this.nindices,
      all: [this.indName],
      ctors: this.indType.ctors.map((c) => c.name),
      isRec: this.isRec,
      isUnsafe: this.decl.isUnsafe,
    };
  }

  // Step 3: strict positivity of a constructor field type.
  private checkPositivity(type: Expr, ctorName: Name, argIdx: number): void {
    const t = this.whnf(type);
    if (!occursIn(this.indName, t, 0)) return; // nonrecursive argument
    if (t.kind === "pi") {
      if (occursIn(this.indName, t.type, 0)) {
        kernelError(
          "other",
          `addInductive: arg #${argIdx + 1} of '${
            nameToString(ctorName)
          }' has a non-positive occurrence`,
        );
      }
      const fv = this.tc.mkLocalDecl(t.name, t.type);
      this.checkPositivity(instantiate1(t.body, fv), ctorName, argIdx);
    } else if (this.isIndAppHead(t)) {
      // recursive argument — fine
    } else {
      kernelError(
        "other",
        `addInductive: arg #${argIdx + 1} of '${nameToString(ctorName)}' has an invalid occurrence`,
      );
    }
  }

  // Step 3: check all constructors are well-formed.
  private checkConstructors(): void {
    const seen = new Set<string>();
    for (const cnstr of this.indType.ctors) {
      const n = cnstr.name;
      if (seen.has(nameToString(n))) {
        kernelError("alreadyDeclared", `addInductive: duplicate constructor '${nameToString(n)}'`);
      }
      seen.add(nameToString(n));
      this.tc.infer(cnstr.type); // type-correctness
      let t = cnstr.type;
      let i = 0;
      while (t.kind === "pi") {
        if (i < this.nparams) {
          const paramType = this.tc.localType(this.params[i]!);
          if (!this.tc.isDefEq(t.type, paramType)) {
            kernelError(
              "typeMismatch",
              `addInductive: arg #${i + 1} of '${nameToString(n)}' does not match the parameters`,
            );
          }
          t = instantiate1(t.body, this.params[i]!);
        } else {
          const s = this.tc.ensureSort(this.tc.infer(t.type));
          if (!(levelGeq(this.resultLevel, s) || isZeroLevel(this.resultLevel))) {
            kernelError(
              "universeMismatch",
              `addInductive: universe of arg #${i + 1} of '${nameToString(n)}' is too big`,
            );
          }
          if (!this.decl.isUnsafe) this.checkPositivity(t.type, n, i);
          const fv = this.tc.mkLocalDecl(t.name, t.type);
          t = instantiate1(t.body, fv);
        }
        i++;
      }
      if (!this.isValidIndApp(this.whnf(t))) {
        kernelError("typeMismatch", `addInductive: invalid result type for '${nameToString(n)}'`);
      }
    }
  }

  private constructorVals(): ConstructorVal[] {
    const out: ConstructorVal[] = [];
    let cidx = 0;
    for (const cnstr of this.indType.ctors) {
      const arity = countPis(cnstr.type);
      out.push({
        kind: "constructor",
        name: cnstr.name,
        levelParams: this.lparams,
        type: cnstr.type,
        induct: this.indName,
        cidx,
        numParams: this.nparams,
        numFields: arity - this.nparams,
        isUnsafe: this.decl.isUnsafe,
      });
      cidx++;
    }
    return out;
  }

  // Step 5: does the recursor only eliminate into Prop?
  private elimOnlyAtUniverseZero(): boolean {
    if (isNotZero(this.resultLevel)) return false; // not an inductive predicate
    const ctors = this.indType.ctors;
    if (ctors.length > 1) return true; // proposition with >1 ctor → Prop-only
    if (ctors.length === 0) return false; // empty (e.g. False) → large elim ok

    // Single constructor: each non-parameter field must be a proof OR occur in
    // the result type (subsingleton / large-elimination condition).
    let type = ctors[0]!.type;
    let i = 0;
    const toCheck: Expr[] = [];
    while (type.kind === "pi") {
      const fv = this.tc.mkLocalDecl(type.name, type.type);
      if (i >= this.nparams) {
        const s = this.tc.ensureSort(this.tc.infer(type.type));
        if (!isZeroLevel(s)) toCheck.push(fv);
      }
      type = instantiate1(type.body, fv);
      i++;
    }
    const resultArgs = getAppArgs(type);
    for (const arg of toCheck) {
      if (!resultArgs.some((a) => exprEq(a, arg))) return true; // condition failed
    }
    return false;
  }

  private initElimLevel(): void {
    if (this.elimOnlyAtUniverseZero()) {
      this.elimLevel = levelZero;
    } else {
      // fresh universe parameter name not already used
      let u = nameFromString("u");
      let n = 1;
      while (this.lparams.some((p) => nameEq(p, u))) {
        u = mkNumName(nameFromString("u"), BigInt(n));
        n++;
      }
      this.elimLevel = mkLevelParam(u);
    }
  }

  // Step 6: K-like reduction target (single ctor, Prop, no fields).
  private initKTarget(): void {
    this.kTarget = this.indType.ctors.length === 1 &&
      isZeroLevel(this.resultLevel) &&
      countPis(this.indType.ctors[0]!.type) === this.nparams;
  }

  private recLevels(): Level[] {
    return this.elimLevel.kind === "param" ? [this.elimLevel, ...this.levels] : this.levels;
  }

  private recLparams(): Name[] {
    return this.elimLevel.kind === "param"
      ? [this.elimLevel.name, ...this.lparams]
      : [...this.lparams];
  }

  /** Whether a constructor field of type `type` is a recursive argument. */
  private isRecArgument(type: Expr): boolean {
    let t = this.whnf(type);
    while (t.kind === "pi") {
      const fv = this.tc.mkLocalDecl(t.name, t.type);
      t = this.whnf(instantiate1(t.body, fv));
    }
    return this.isIndAppHead(t);
  }

  // Step 7+8: build the recursor and its reduction rules.
  private buildRecursor(currentEnv: Environment): RecursorVal {
    this.tc = new TypeChecker(currentEnv);
    // Re-introduce parameters into the fresh checker's context.
    this.params = [];
    let pt = this.whnf(this.indType.type);
    let pi = 0;
    const allIndices: Expr[] = [];
    while (pt.kind === "pi") {
      const fv = this.tc.mkLocalDecl(pt.name, pt.type);
      if (pi < this.nparams) this.params.push(fv);
      else allIndices.push(fv);
      pt = this.whnf(instantiate1(pt.body, fv));
      pi++;
    }

    // Motive C : (indices) → (major : I params indices) → Sort elimLevel
    const majorType = mkAppN(mkAppN(this.indCnst, this.params), allIndices);
    const major = this.tc.mkLocalDecl(nameFromString("t"), majorType);
    let cType: Expr = mkSort(this.elimLevel);
    cType = this.tc.mkForallFVars([major], cType);
    cType = this.tc.mkForallFVars(allIndices, cType);
    const motive = this.tc.mkLocalDecl(nameFromString("motive"), cType);

    // Minor premises, one per constructor.
    const minors: Expr[] = [];
    for (const cnstr of this.indType.ctors) {
      minors.push(this.mkMinor(cnstr, motive));
    }

    // Recursor type: params → motive → minors → indices → (major) → motive indices major
    let recTy: Expr = mkApp(mkAppN(motive, allIndices), major);
    recTy = this.tc.mkForallFVars([major], recTy);
    recTy = this.tc.mkForallFVars(allIndices, recTy);
    recTy = this.tc.mkForallFVars(minors, recTy);
    recTy = this.tc.mkForallFVars([motive], recTy);
    recTy = this.tc.mkForallFVars(this.params, recTy);

    const rules = this.mkRecRules([motive], minors);

    return {
      kind: "recursor",
      name: mkRecName(this.indName),
      levelParams: this.recLparams(),
      type: recTy,
      all: [this.indName],
      numParams: this.nparams,
      numIndices: this.nindices,
      numMotives: 1,
      numMinors: minors.length,
      rules,
      k: this.kTarget,
      isUnsafe: this.decl.isUnsafe,
    };
  }

  /** Build the minor premise (induction case) for one constructor. */
  private mkMinor(cnstr: InductiveType["ctors"][number], motive: Expr): Expr {
    const bu: Expr[] = []; // all fields
    const u: Expr[] = []; // recursive fields
    let t = cnstr.type;
    let i = 0;
    while (t.kind === "pi") {
      if (i < this.nparams) {
        t = instantiate1(t.body, this.params[i]!);
      } else {
        const l = this.tc.mkLocalDecl(t.name, t.type);
        bu.push(l);
        if (this.isRecArgument(t.type)) u.push(l);
        t = instantiate1(t.body, l);
      }
      i++;
    }
    const itIndices = this.getIIndices(this.whnf(t));
    const introApp = mkAppN(mkAppN(mkConst(cnstr.name, this.levels), this.params), bu);
    const cApp = mkApp(mkAppN(motive, itIndices), introApp);

    // Induction hypotheses for the recursive fields.
    const v: Expr[] = [];
    for (const ui of u) {
      const v_i = this.mkIndHyp(ui, motive);
      v.push(v_i);
    }
    const minorTy = this.tc.mkForallFVars(bu, this.tc.mkForallFVars(v, cApp));
    return this.tc.mkLocalDecl(minorPremiseName(cnstr.name, this.indName), minorTy);
  }

  /** The type of the induction hypothesis for a recursive field `ui`. */
  private mkIndHyp(ui: Expr, motive: Expr): Expr {
    let uty = this.whnf(this.tc.infer(ui));
    const xs: Expr[] = [];
    while (uty.kind === "pi") {
      const x = this.tc.mkLocalDecl(uty.name, uty.type);
      xs.push(x);
      uty = this.whnf(instantiate1(uty.body, x));
    }
    const itIndices = this.getIIndices(uty);
    const cApp = mkApp(mkAppN(motive, itIndices), mkAppN(ui, xs));
    const vTy = this.tc.mkForallFVars(xs, cApp);
    return this.tc.mkLocalDecl(nameFromString("ih"), vTy);
  }

  /** Build the ι-reduction rules: one per constructor. */
  private mkRecRules(motives: Expr[], minors: Expr[]): RecursorRule[] {
    const lvls = this.recLevels();
    const rules: RecursorRule[] = [];
    let minorIdx = 0;
    for (const cnstr of this.indType.ctors) {
      const bu: Expr[] = [];
      const u: Expr[] = [];
      let t = cnstr.type;
      let i = 0;
      while (t.kind === "pi") {
        if (i < this.nparams) {
          t = instantiate1(t.body, this.params[i]!);
        } else {
          const l = this.tc.mkLocalDecl(t.name, t.type);
          bu.push(l);
          if (this.isRecArgument(t.type)) u.push(l);
          t = instantiate1(t.body, l);
        }
        i++;
      }
      const v: Expr[] = [];
      for (const ui of u) {
        let uty = this.whnf(this.tc.infer(ui));
        const xs: Expr[] = [];
        while (uty.kind === "pi") {
          const x = this.tc.mkLocalDecl(uty.name, uty.type);
          xs.push(x);
          uty = this.whnf(instantiate1(uty.body, x));
        }
        const itIndices = this.getIIndices(uty);
        let recApp: Expr = mkConst(mkRecName(this.indName), lvls);
        recApp = mkAppN(recApp, this.params);
        recApp = mkAppN(recApp, motives);
        recApp = mkAppN(recApp, minors);
        recApp = mkAppN(recApp, itIndices);
        recApp = mkApp(recApp, mkAppN(ui, xs));
        v.push(this.tc.mkLambdaFVars(xs, recApp));
      }
      let eApp = mkAppN(minors[minorIdx]!, bu);
      eApp = mkAppN(eApp, v);
      const compRhs = this.tc.mkLambdaFVars(
        this.params,
        this.tc.mkLambdaFVars(
          motives,
          this.tc.mkLambdaFVars(minors, this.tc.mkLambdaFVars(bu, eApp)),
        ),
      );
      rules.push({ ctor: cnstr.name, nfields: bu.length, rhs: compRhs });
      minorIdx++;
    }
    return rules;
  }

  run(): Environment {
    this.checkInductiveType();
    this.computeIsRec();
    let env = this.startEnv.addConstantUnchecked(this.inductiveVal());
    // Re-run constructor checks against the env that knows the inductive.
    this.tc = new TypeChecker(env);
    this.reintroParams();
    this.checkConstructors();
    for (const cv of this.constructorVals()) env = env.addConstantUnchecked(cv);

    this.tc = new TypeChecker(env);
    this.reintroParams();
    this.initElimLevel();
    this.initKTarget();
    env = env.addConstantUnchecked(this.buildRecursor(env));
    return env;
  }

  /** Re-create the parameter fvars in the current checker's local context. */
  private reintroParams(): void {
    this.params = [];
    let t = this.whnf(this.indType.type);
    let i = 0;
    while (t.kind === "pi" && i < this.nparams) {
      const fv = this.tc.mkLocalDecl(t.name, t.type);
      this.params.push(fv);
      t = this.whnf(instantiate1(t.body, fv));
      i++;
    }
  }
}

/** Type-check an inductive declaration and return an extended environment. */
export function addInductive(env: Environment, decl: InductiveDeclaration): Environment {
  return new AddInductive(env, decl).run();
}

// --- helpers ---------------------------------------------------------------

function countPis(e: Expr): number {
  let n = 0;
  let t = e;
  while (t.kind === "pi") {
    n++;
    t = t.body;
  }
  return n;
}

/** Whether `name` occurs as a constant anywhere in `e` below `skipBinders` Pis. */
function occursIn(name: Name, e: Expr, skipBinders: number): boolean {
  let t = e;
  for (let i = 0; i < skipBinders && t.kind === "pi"; i++) t = t.body;
  return occursCore(name, t);
}

function occursCore(name: Name, e: Expr): boolean {
  switch (e.kind) {
    case "const":
      return nameEq(e.name, name);
    case "app":
      return occursCore(name, e.fn) || occursCore(name, e.arg);
    case "lam":
    case "pi":
      return occursCore(name, e.type) || occursCore(name, e.body);
    case "let":
      return occursCore(name, e.type) || occursCore(name, e.value) || occursCore(name, e.body);
    case "mdata":
    case "proj":
      return occursCore(name, e.expr);
    default:
      return false;
  }
}

/** Strip the inductive's prefix to name a minor premise, e.g. `Nat.succ` → `succ`. */
function minorPremiseName(ctor: Name, ind: Name): Name {
  if (ctor.kind === "str" && nameEq(ctor.prefix, ind)) return nameFromString(ctor.str);
  return ctor;
}
