// Quotient types (SPEC.md Section 8).
//
// Faithful port of Lean's kernel `quot.cpp`. `addQuot` introduces the four
// trusted primitives — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — after
// checking that `Eq` is present. The computation rule
//   Quot.lift f h (Quot.mk r a)  ⟶  f a
// (and the analogous one for `Quot.ind`) lives in the type checker.

import { type Expr, mkApp, mkAppN, mkConst, mkPi, mkSort } from "./expr.ts";
import { levelZero, mkLevelParam } from "./level.ts";
import { anonymousName, type Name, nameFromString } from "./name.ts";
import { kernelError } from "./exception.ts";
import type { QuotVal } from "./declaration.ts";
import type { Environment } from "./environment.ts";
import { TypeChecker } from "./type_checker.ts";

export const quotName: Name = nameFromString("Quot");
export const quotMkName: Name = nameFromString("Quot.mk");
export const quotLiftName: Name = nameFromString("Quot.lift");
export const quotIndName: Name = nameFromString("Quot.ind");

const eqName = nameFromString("Eq");

/** Non-dependent function type `a → b`. */
function arrow(a: Expr, b: Expr): Expr {
  return mkPi(anonymousName, a, b);
}

/** Introduce the `Quot` primitives, checking that `Eq` is available first. */
export function addQuot(env: Environment): Environment {
  const eq = env.find(eqName);
  if (eq === undefined || eq.kind !== "inductive") {
    kernelError("other", "addQuot: environment is missing the 'Eq' inductive type");
  }

  const uName = nameFromString("u");
  const vName = nameFromString("v");
  const u = mkLevelParam(uName);
  const v = mkLevelParam(vName);
  const sortU = mkSort(u);
  const sortV = mkSort(v);
  const prop = mkSort(levelZero);
  const a = nameFromString("a");

  let out = env;

  // Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u
  {
    const tc = new TypeChecker(out);
    const alpha = tc.mkLocalDecl(a, sortU);
    const r = tc.mkLocalDecl(nameFromString("r"), arrow(alpha, arrow(alpha, prop)));
    const type = tc.mkForallFVars([alpha, r], sortU);
    out = out.addConstantUnchecked(quotVal(quotName, [uName], type, "type"));
  }

  // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot α r
  {
    const tc = new TypeChecker(out);
    const alpha = tc.mkLocalDecl(nameFromString("α"), sortU);
    const r = tc.mkLocalDecl(nameFromString("r"), arrow(alpha, arrow(alpha, prop)));
    const av = tc.mkLocalDecl(a, alpha);
    const quotR = mkAppN(mkConst(quotName, [u]), [alpha, r]);
    const type = tc.mkForallFVars([alpha, r, av], quotR);
    out = out.addConstantUnchecked(quotVal(quotMkName, [uName], type, "mk"));
  }

  // Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
  //                   → (∀ a b, r a b → f a = f b) → @Quot α r → β
  {
    const tc = new TypeChecker(out);
    const alpha = tc.mkLocalDecl(nameFromString("α"), sortU);
    const r = tc.mkLocalDecl(nameFromString("r"), arrow(alpha, arrow(alpha, prop)));
    const beta = tc.mkLocalDecl(nameFromString("β"), sortV);
    const f = tc.mkLocalDecl(nameFromString("f"), arrow(alpha, beta));
    const av = tc.mkLocalDecl(a, alpha);
    const bv = tc.mkLocalDecl(nameFromString("b"), alpha);
    const rab = mkAppN(r, [av, bv]);
    const faEqFb = mkAppN(mkConst(eqName, [v]), [beta, mkApp(f, av), mkApp(f, bv)]);
    const sanity = tc.mkForallFVars([av, bv], arrow(rab, faEqFb));
    const quotR = mkAppN(mkConst(quotName, [u]), [alpha, r]);
    const type = tc.mkForallFVars([alpha, r, beta, f], arrow(sanity, arrow(quotR, beta)));
    out = out.addConstantUnchecked(quotVal(quotLiftName, [uName, vName], type, "lift"));
  }

  // Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} → {β : @Quot α r → Prop}
  //               → (∀ a, β (Quot.mk α r a)) → ∀ q : @Quot α r, β q
  {
    const tc = new TypeChecker(out);
    const alpha = tc.mkLocalDecl(nameFromString("α"), sortU);
    const r = tc.mkLocalDecl(nameFromString("r"), arrow(alpha, arrow(alpha, prop)));
    const quotR = mkAppN(mkConst(quotName, [u]), [alpha, r]);
    const beta = tc.mkLocalDecl(nameFromString("β"), arrow(quotR, prop));
    const av = tc.mkLocalDecl(a, alpha);
    const quotMkA = mkAppN(mkConst(quotMkName, [u]), [alpha, r, av]);
    const allQuot = tc.mkForallFVars([av], mkApp(beta, quotMkA));
    const q = tc.mkLocalDecl(nameFromString("q"), quotR);
    const forallQ = tc.mkForallFVars([q], mkApp(beta, q));
    const type = tc.mkForallFVars(
      [alpha, r, beta],
      mkPi(nameFromString("mk"), allQuot, forallQ),
    );
    out = out.addConstantUnchecked(quotVal(quotIndName, [uName], type, "ind"));
  }

  return out;
}

function quotVal(
  name: QuotVal["name"],
  levelParams: QuotVal["levelParams"],
  type: Expr,
  quotKind: QuotVal["quotKind"],
): QuotVal {
  return { kind: "quot", name, levelParams, type, quotKind };
}
