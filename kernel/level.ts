// Universe levels (SPEC.md Section 2.2) — the `u` in `Sort u`.
//
// Corresponds to Lean's `level`. Phase 0 provides the representation,
// constructors, structural equality, hashing, and the `hasMVar` predicate.
// Normalization and the `≤` order arrive in Phase 1.

import { type Name, nameCmp, nameEq } from "./name.ts";
import { mixHash } from "./hash.ts";

export type Level =
  | { readonly kind: "zero"; readonly hash: number }
  | { readonly kind: "succ"; readonly level: Level; readonly hash: number }
  | { readonly kind: "max"; readonly lhs: Level; readonly rhs: Level; readonly hash: number }
  | { readonly kind: "imax"; readonly lhs: Level; readonly rhs: Level; readonly hash: number }
  | { readonly kind: "param"; readonly name: Name; readonly hash: number }
  | { readonly kind: "mvar"; readonly name: Name; readonly hash: number };

const HASH_ZERO = 0x9e3779b1;
const HASH_SUCC = 0x7f4a7c15;
const HASH_MAX = 0x6c62272e;
const HASH_IMAX = 0x517cc1b7;
const HASH_PARAM = 0x2545f491;
const HASH_MVAR = 0x94d049bb;

/** The level `0`. */
export const levelZero: Level = { kind: "zero", hash: HASH_ZERO };

/** `level + 1`. */
export function mkLevelSucc(level: Level): Level {
  return { kind: "succ", level, hash: mixHash(level.hash, HASH_SUCC) };
}

/** `max lhs rhs`. */
export function mkLevelMax(lhs: Level, rhs: Level): Level {
  return { kind: "max", lhs, rhs, hash: mixHash(mixHash(lhs.hash, rhs.hash), HASH_MAX) };
}

/** `imax lhs rhs` — equals `0` if `rhs` reduces to `0`, else `max lhs rhs`. */
export function mkLevelIMax(lhs: Level, rhs: Level): Level {
  return { kind: "imax", lhs, rhs, hash: mixHash(mixHash(lhs.hash, rhs.hash), HASH_IMAX) };
}

/** A universe parameter (for universe polymorphism). */
export function mkLevelParam(name: Name): Level {
  return { kind: "param", name, hash: mixHash(name.hash, HASH_PARAM) };
}

/** A universe metavariable. Must not appear in terms reaching the type checker. */
export function mkLevelMVar(name: Name): Level {
  return { kind: "mvar", name, hash: mixHash(name.hash, HASH_MVAR) };
}

/** Build the literal level `n` as `succ^n zero`. */
export function mkLevelLit(n: number): Level {
  if (n < 0 || !Number.isInteger(n)) {
    throw new Error(`mkLevelLit: expected a natural number, got ${n}`);
  }
  let level = levelZero;
  for (let i = 0; i < n; i++) level = mkLevelSucc(level);
  return level;
}

/** Whether the level contains a universe metavariable. */
export function levelHasMVar(level: Level): boolean {
  switch (level.kind) {
    case "zero":
    case "param":
      return false;
    case "mvar":
      return true;
    case "succ":
      return levelHasMVar(level.level);
    case "max":
    case "imax":
      return levelHasMVar(level.lhs) || levelHasMVar(level.rhs);
  }
}

/**
 * Structural equality. This is *syntactic*, not the definitional `isEquiv`
 * (which normalizes); that arrives in Phase 1.
 */
export function levelEq(a: Level, b: Level): boolean {
  if (a === b) return true;
  if (a.hash !== b.hash || a.kind !== b.kind) return false;
  switch (a.kind) {
    case "zero":
      return true;
    case "succ":
      return levelEq(a.level, (b as typeof a).level);
    case "max":
    case "imax":
      return levelEq(a.lhs, (b as typeof a).lhs) && levelEq(a.rhs, (b as typeof a).rhs);
    case "param":
    case "mvar":
      return nameEq(a.name, (b as typeof a).name);
  }
}

// --- Predicates and offsets -------------------------------------------------
//
// The normalization and ordering below are a faithful port of Lean's kernel
// `level.cpp` (`normalize`, `is_equivalent`, `is_geq`). The exact normal form
// is an implementation detail; what matters is that equivalent levels normalize
// to structurally equal forms.

/** Whether the level contains a universe parameter. */
export function levelHasParam(level: Level): boolean {
  switch (level.kind) {
    case "zero":
    case "mvar":
      return false;
    case "param":
      return true;
    case "succ":
      return levelHasParam(level.level);
    case "max":
    case "imax":
      return levelHasParam(level.lhs) || levelHasParam(level.rhs);
  }
}

/** Tree depth: leaves are 0, `succ`/`max`/`imax` add one over their children. */
export function levelDepth(level: Level): number {
  switch (level.kind) {
    case "zero":
    case "param":
    case "mvar":
      return 0;
    case "succ":
      return levelDepth(level.level) + 1;
    case "max":
    case "imax":
      return Math.max(levelDepth(level.lhs), levelDepth(level.rhs)) + 1;
  }
}

/** Whether the level is `succ^k 0` for some `k` (a concrete numeral). */
export function isExplicit(level: Level): boolean {
  switch (level.kind) {
    case "zero":
      return true;
    case "succ":
      return isExplicit(level.level);
    default:
      return false;
  }
}

/** Peel off leading `succ`s: `succ^k base` ↦ `[base, k]`. */
export function toOffset(level: Level): [Level, number] {
  let k = 0;
  let l = level;
  while (l.kind === "succ") {
    l = l.level;
    k++;
  }
  return [l, k];
}

/** Whether the level is syntactically `0`. */
export function isZeroLevel(level: Level): boolean {
  return level.kind === "zero";
}

/** Whether the level is syntactically `1` (= `succ 0`). */
export function isOneLevel(level: Level): boolean {
  return level.kind === "succ" && level.level.kind === "zero";
}

/** Whether the level is provably nonzero regardless of parameter/mvar assignment. */
export function isNotZero(level: Level): boolean {
  switch (level.kind) {
    case "zero":
    case "param":
    case "mvar":
      return false;
    case "succ":
      return true;
    case "max":
      return isNotZero(level.lhs) || isNotZero(level.rhs);
    case "imax":
      return isNotZero(level.rhs);
  }
}

/** Apply `succ` `k` times. */
export function mkLevelSuccN(level: Level, k: number): Level {
  let l = level;
  for (let i = 0; i < k; i++) l = mkLevelSucc(l);
  return l;
}

// --- Smart constructors (port of kernel mk_max / mk_imax) -------------------

const levelKindRank: Record<Level["kind"], number> = {
  zero: 0,
  succ: 1,
  max: 2,
  imax: 3,
  param: 4,
  mvar: 5,
};

/** `max` with the kernel's algebraic simplifications. */
export function mkLevelMaxSmart(l1: Level, l2: Level): Level {
  if (isExplicit(l1) && isExplicit(l2)) {
    return levelDepth(l1) >= levelDepth(l2) ? l1 : l2;
  }
  if (levelEq(l1, l2)) return l1;
  if (isZeroLevel(l1)) return l2;
  if (isZeroLevel(l2)) return l1;
  if (l2.kind === "max" && (levelEq(l2.lhs, l1) || levelEq(l2.rhs, l1))) return l2;
  if (l1.kind === "max" && (levelEq(l1.lhs, l2) || levelEq(l1.rhs, l2))) return l1;
  const [b1, k1] = toOffset(l1);
  const [b2, k2] = toOffset(l2);
  if (levelEq(b1, b2)) return k1 > k2 ? l1 : l2;
  return mkLevelMax(l1, l2);
}

/** `imax` with the kernel's algebraic simplifications. */
export function mkLevelIMaxSmart(l1: Level, l2: Level): Level {
  if (isNotZero(l2)) return mkLevelMaxSmart(l1, l2);
  if (isZeroLevel(l2)) return l2; // imax u 0 = 0
  if (isZeroLevel(l1) || isOneLevel(l1)) return l2; // imax 0 u = imax 1 u = u
  if (levelEq(l1, l2)) return l1; // imax u u = u
  return mkLevelIMax(l1, l2);
}

// --- Normalization ----------------------------------------------------------

/**
 * A total order used during normalization: `succ l` is the immediate successor
 * of `l`, and `0` is minimal. Returns `true` if `a < b`.
 */
function isNormLt(a: Level, b: Level): boolean {
  if (a === b) return false;
  const [l1, k1] = toOffset(a);
  const [l2, k2] = toOffset(b);
  if (!levelEq(l1, l2)) {
    if (l1.kind !== l2.kind) return levelKindRank[l1.kind] < levelKindRank[l2.kind];
    switch (l1.kind) {
      case "zero":
      case "succ":
        return false; // unreachable: bases are never zero/succ when kinds match here
      case "param":
      case "mvar":
        return nameCmp(l1.name, (l2 as typeof l1).name) < 0;
      case "max":
      case "imax": {
        const r2 = l2 as typeof l1;
        if (!levelEq(l1.lhs, r2.lhs)) return isNormLt(l1.lhs, r2.lhs);
        return isNormLt(l1.rhs, r2.rhs);
      }
    }
  }
  return k1 < k2;
}

function pushMaxArgs(level: Level, out: Level[]): void {
  if (level.kind === "max") {
    pushMaxArgs(level.lhs, out);
    pushMaxArgs(level.rhs, out);
  } else {
    out.push(level);
  }
}

function mkLevelMaxList(args: readonly Level[]): Level {
  const n = args.length;
  if (n === 1) return args[0]!;
  let r = mkLevelMaxSmart(args[n - 2]!, args[n - 1]!);
  for (let i = n - 2; i > 0;) {
    i--;
    r = mkLevelMaxSmart(args[i]!, r);
  }
  return r;
}

/** Normalize a level to its canonical form (kernel `normalize`). */
export function normalizeLevel(level: Level): Level {
  const [base, k] = toOffset(level);
  switch (base.kind) {
    case "zero":
    case "param":
    case "mvar":
      return level;
    case "succ":
      return level; // unreachable: toOffset already peeled all succs
    case "imax": {
      const l1 = normalizeLevel(base.lhs);
      const l2 = normalizeLevel(base.rhs);
      return mkLevelSuccN(mkLevelIMaxSmart(l1, l2), k);
    }
    case "max": {
      const todo: Level[] = [];
      pushMaxArgs(base, todo);
      const args: Level[] = [];
      for (const a of todo) pushMaxArgs(normalizeLevel(a), args);
      args.sort((x, y) => (isNormLt(x, y) ? -1 : isNormLt(y, x) ? 1 : 0));

      const rargs: Level[] = [];
      let i = 0;
      if (isExplicit(args[i]!)) {
        // find the largest explicit universe...
        while (i + 1 < args.length && isExplicit(args[i + 1]!)) i++;
        const kExp = toOffset(args[i]!)[1];
        // ...and drop it if some non-explicit succ^k'(l) with k' >= k subsumes it
        let j = i + 1;
        for (; j < args.length; j++) {
          if (toOffset(args[j]!)[1] >= kExp) break;
        }
        if (j < args.length) i++;
      }
      rargs.push(args[i]!);
      let prevBase = toOffset(args[i]!)[0];
      let prevK = toOffset(args[i]!)[1];
      i++;
      for (; i < args.length; i++) {
        const [curBase, curK] = toOffset(args[i]!);
        if (levelEq(prevBase, curBase)) {
          if (prevK < curK) {
            prevBase = curBase;
            prevK = curK;
            rargs.pop();
            rargs.push(args[i]!);
          }
        } else {
          prevBase = curBase;
          prevK = curK;
          rargs.push(args[i]!);
        }
      }
      return mkLevelMaxList(rargs.map((a) => mkLevelSuccN(a, k)));
    }
  }
}

// --- Equivalence and order --------------------------------------------------

/**
 * Definitional equivalence of levels (kernel `is_equivalent`): equal under the
 * universe algebra, in both directions. This is the comparison the type checker
 * uses on `Sort`s, not the syntactic {@link levelEq}.
 */
export function levelIsEquiv(a: Level, b: Level): boolean {
  return levelEq(a, b) || levelEq(normalizeLevel(a), normalizeLevel(b));
}

function isGeqCore(l1: Level, l2: Level): boolean {
  if (levelEq(l1, l2) || isZeroLevel(l2)) return true;
  if (l2.kind === "max") return levelGeq(l1, l2.lhs) && levelGeq(l1, l2.rhs);
  if (l1.kind === "max" && (levelGeq(l1.lhs, l2) || levelGeq(l1.rhs, l2))) return true;
  if (l2.kind === "imax") return levelGeq(l1, l2.lhs) && levelGeq(l1, l2.rhs);
  if (l1.kind === "imax") return levelGeq(l1.rhs, l2);
  const [b1, k1] = toOffset(l1);
  const [b2, k2] = toOffset(l2);
  if (levelEq(b1, b2) || isZeroLevel(b2)) return k1 >= k2;
  if (k1 === k2 && k1 > 0) return levelGeq(b1, b2);
  return false;
}

/** `l1 ≥ l2` for every parameter/mvar assignment (kernel `is_geq`). */
export function levelGeq(l1: Level, l2: Level): boolean {
  return isGeqCore(normalizeLevel(l1), normalizeLevel(l2));
}

/** `l1 ≤ l2` for every parameter/mvar assignment. */
export function levelLeq(l1: Level, l2: Level): boolean {
  return levelGeq(l2, l1);
}

// --- Substitution -----------------------------------------------------------

/** Generic bottom-up rewrite: `f` returns a replacement, or `null` to recurse. */
export function levelReplace(level: Level, f: (l: Level) => Level | null): Level {
  const r = f(level);
  if (r !== null) return r;
  switch (level.kind) {
    case "zero":
    case "param":
    case "mvar":
      return level;
    case "succ":
      return mkLevelSucc(levelReplace(level.level, f));
    case "max":
      return mkLevelMax(levelReplace(level.lhs, f), levelReplace(level.rhs, f));
    case "imax":
      return mkLevelIMax(levelReplace(level.lhs, f), levelReplace(level.rhs, f));
  }
}

/**
 * Substitute universe parameters `params[i]` with `args[i]` (kernel
 * `instantiate`). Used when unfolding a universe-polymorphic constant.
 */
export function levelInstantiate(
  level: Level,
  params: readonly Name[],
  args: readonly Level[],
): Level {
  if (params.length !== args.length) {
    throw new Error(`levelInstantiate: ${params.length} params vs ${args.length} args`);
  }
  return levelReplace(level, (l) => {
    if (!levelHasParam(l)) return l;
    if (l.kind === "param") {
      for (let i = 0; i < params.length; i++) {
        if (nameEq(l.name, params[i]!)) return args[i]!;
      }
      return l;
    }
    return null;
  });
}
