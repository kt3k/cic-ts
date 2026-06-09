import { assert, assertEquals } from "@std/assert";
import { nameFromString } from "./name.ts";
import {
  type Expr,
  exprEq,
  find,
  forEach,
  mapChildren,
  mkApp,
  mkBVar,
  mkConst,
  mkFVar,
  mkLambda,
  replace,
} from "./expr.ts";

const nat = mkConst(nameFromString("Nat"));
const x = nameFromString("x");

Deno.test("forEach visits every subexpression", () => {
  const e = mkApp(mkConst(nameFromString("f")), mkApp(mkBVar(0n), nat));
  let count = 0;
  forEach(e, () => count++);
  // app, f, app, bvar, Nat
  assertEquals(count, 5);
});

Deno.test("find returns the first matching subexpression", () => {
  const e = mkApp(mkConst(nameFromString("f")), mkFVar(nameFromString("h")));
  const found = find(e, (s) => s.kind === "fvar");
  assert(found !== undefined && found.kind === "fvar");
});

Deno.test("find returns undefined when nothing matches", () => {
  const e = mkApp(nat, nat);
  assertEquals(find(e, (s) => s.kind === "mvar"), undefined);
});

Deno.test("replace rewrites matched nodes and recurses elsewhere", () => {
  const fname = nameFromString("f");
  const f = mkConst(fname);
  const g = mkConst(nameFromString("g"));
  const e = mkApp(f, mkApp(f, nat));
  // replace every `f` with `g`
  const out = replace(e, (s) => (s.kind === "const" && s.name === fname ? g : null));
  assert(exprEq(out, mkApp(g, mkApp(g, nat))));
});

Deno.test("mapChildren rebuilds with mapped immediate children only", () => {
  const e: Expr = mkLambda(x, nat, mkBVar(0n));
  const out = mapChildren(e, () => nat);
  assert(exprEq(out, mkLambda(x, nat, nat)));
});
