// Universe levels (SPEC.md Section 2.2) — the `u` in `Sort u`.
//
// Corresponds to Lean's `level`. Phase 0 provides the representation,
// constructors, structural equality, hashing, and the `hasMVar` predicate.
// Normalization and the `≤` order arrive in Phase 1.

import { type Name, nameEq } from "./name.ts";
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
