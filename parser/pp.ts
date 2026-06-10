// Pretty-printer for kernel terms (used by `#check` output and diagnostics).
//
// Best-effort, not a parser inverse: it renders bound variables using their
// binder names, prints `Sort`/`Type`/`Prop` sugar, and shows anonymous `Pi`s as
// arrows. Good enough to read `#check` results.

import { type Expr, getAppArgs, getAppFn } from "../kernel/expr.ts";
import { type Level, toOffset } from "../kernel/level.ts";
import { type Name, nameToString } from "../kernel/name.ts";

export function ppLevel(l: Level): string {
  const [base, k] = toOffset(l);
  const b = ppLevelBase(base);
  if (base.kind === "zero") return k.toString();
  return k === 0 ? b : `(${b}+${k})`;
}

function ppLevelBase(l: Level): string {
  switch (l.kind) {
    case "zero":
      return "0";
    case "param":
      return nameToString(l.name);
    case "mvar":
      return `?${nameToString(l.name)}`;
    case "max":
      return `(max ${ppLevel(l.lhs)} ${ppLevel(l.rhs)})`;
    case "imax":
      return `(imax ${ppLevel(l.lhs)} ${ppLevel(l.rhs)})`;
    case "succ":
      return ppLevel(l); // unreachable: toOffset peeled all succs
  }
}

function ppSort(level: Level): string {
  const [base, k] = toOffset(level);
  if (base.kind === "zero") {
    if (k === 0) return "Prop";
    if (k === 1) return "Type";
    return `Type ${k - 1}`;
  }
  return `Sort ${ppLevel(level)}`;
}

function ppName(name: Name, levels: readonly Level[]): string {
  const base = nameToString(name);
  return levels.length > 0 ? `${base}.{${levels.map(ppLevel).join(",")}}` : base;
}

/** Render `e`, using `ctx` (outermost-first binder names) to name bound vars. */
export function ppExpr(e: Expr, ctx: readonly string[] = []): string {
  return pp(e, ctx, false);
}

function pp(e: Expr, ctx: readonly string[], paren: boolean): string {
  switch (e.kind) {
    case "bvar": {
      const i = Number(e.idx);
      return ctx[ctx.length - 1 - i] ?? `#${e.idx}`;
    }
    case "fvar":
      return nameToString(e.id);
    case "mvar":
      return `?${nameToString(e.id)}`;
    case "sort":
      return ppSort(e.level);
    case "const":
      return ppName(e.name, e.levels);
    case "proj":
      return `${pp(e.expr, ctx, true)}.${e.idx}`;
    case "mdata":
      return pp(e.expr, ctx, paren);
    case "app": {
      const fn = getAppFn(e);
      const args = getAppArgs(e);
      const s = [pp(fn, ctx, true), ...args.map((a) => pp(a, ctx, true))].join(" ");
      return wrap(s, paren);
    }
    case "pi": {
      let s: string;
      if (e.name.kind === "anonymous") {
        s = `${pp(e.type, ctx, true)} → ${pp(e.body, [...ctx, "_"], false)}`;
      } else {
        const nm = nameToString(e.name);
        s = `(${nm} : ${pp(e.type, ctx, false)}) → ${pp(e.body, [...ctx, nm], false)}`;
      }
      return wrap(s, paren);
    }
    case "lam": {
      const nm = nameToString(e.name);
      const s = `fun (${nm} : ${pp(e.type, ctx, false)}) => ${pp(e.body, [...ctx, nm], false)}`;
      return wrap(s, paren);
    }
    case "let": {
      const nm = nameToString(e.name);
      const s = `let ${nm} : ${pp(e.type, ctx, false)} := ${pp(e.value, ctx, false)}; ${
        pp(e.body, [...ctx, nm], false)
      }`;
      return wrap(s, paren);
    }
  }
}

function wrap(s: string, paren: boolean): string {
  return paren ? `(${s})` : s;
}
