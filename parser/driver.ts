// Driver: run a surface-syntax module against a kernel environment.
//
// Ties the front end (parse → elaborate) to the kernel (addDecl / addInductive
// / addQuot), threading an immutable Environment through the commands and
// collecting `#check` results. Kernel errors are re-reported with the source
// position of the command that triggered them.

import { Environment } from "../kernel/environment.ts";
import { TypeChecker } from "../kernel/type_checker.ts";
import { KernelError } from "../kernel/exception.ts";
import type { Pos } from "./syntax.ts";
import { parse } from "./parser.ts";
import { elaborate } from "./elaborator.ts";
import { ppExpr } from "./pp.ts";

/** An error tied to a source position, formatted like `line:col: message`. */
export class DriverError extends Error {
  override readonly name = "DriverError";
  constructor(readonly pos: Pos, message: string) {
    super(`${pos.line}:${pos.col}: ${message}`);
  }
}

/** The rendered result of a `#check` command. */
export interface CheckOutput {
  readonly pos: Pos;
  readonly text: string; // "<expr> : <type>"
}

export interface RunResult {
  readonly env: Environment;
  readonly checks: readonly CheckOutput[];
}

/**
 * Parse, elaborate, and run `src` against `env`. Throws `ParseError` (lexing,
 * parsing, or elaboration) or `DriverError` (a kernel rejection), both carrying
 * a source position.
 */
export function runModule(src: string, env: Environment = new Environment()): RunResult {
  const cmds = parse(src);
  const checks: CheckOutput[] = [];
  let cur = env;
  for (const cmd of cmds) {
    const r = elaborate(cmd);
    try {
      switch (r.kind) {
        case "decl":
          cur = cur.addDecl(r.decl);
          break;
        case "inductive":
          cur = cur.addInductive(r.decl);
          break;
        case "initQuot":
          cur = cur.addQuot();
          break;
        case "check": {
          const type = new TypeChecker(cur).infer(r.expr);
          checks.push({ pos: cmd.pos, text: `${ppExpr(r.expr)} : ${ppExpr(type)}` });
          break;
        }
      }
    } catch (e) {
      if (e instanceof KernelError) throw new DriverError(cmd.pos, e.message);
      throw e;
    }
  }
  return { env: cur, checks };
}
