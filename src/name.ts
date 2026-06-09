// Hierarchical names (SPEC.md Section 2.1), e.g. `Nat.succ`.
//
// Corresponds to Lean's `name`. A name is a snoc-list of string/numeric
// components rooted at the anonymous name.

import { hashBigInt, hashString, mixHash } from "./hash.ts";

export type Name =
  | { readonly kind: "anonymous"; readonly hash: number }
  | { readonly kind: "str"; readonly prefix: Name; readonly str: string; readonly hash: number }
  | { readonly kind: "num"; readonly prefix: Name; readonly num: bigint; readonly hash: number };

// Salts keep the three kinds from colliding on otherwise-equal payloads.
const HASH_ANON = 0x1b873593;
const HASH_STR = 0xcc9e2d51;
const HASH_NUM = 0x2545f491;

/** The root (empty) name. */
export const anonymousName: Name = { kind: "anonymous", hash: HASH_ANON };

/** Extend a name with a string component: `prefix.str`. */
export function mkStrName(prefix: Name, str: string): Name {
  const hash = mixHash(mixHash(prefix.hash, hashString(str)), HASH_STR);
  return { kind: "str", prefix, str, hash };
}

/** Extend a name with a numeric component: `prefix.num`. */
export function mkNumName(prefix: Name, num: bigint): Name {
  const hash = mixHash(mixHash(prefix.hash, hashBigInt(num)), HASH_NUM);
  return { kind: "num", prefix, num, hash };
}

/** Build a name from a dot-separated string, e.g. `"Nat.succ"`. Empty string → anonymous. */
export function nameFromString(s: string): Name {
  if (s.length === 0) return anonymousName;
  let name = anonymousName;
  for (const part of s.split(".")) {
    name = mkStrName(name, part);
  }
  return name;
}

/** Render a name as a dot-separated string. The anonymous name renders as `"[anonymous]"`. */
export function nameToString(name: Name): string {
  switch (name.kind) {
    case "anonymous":
      return "[anonymous]";
    case "str":
      return name.prefix.kind === "anonymous"
        ? name.str
        : `${nameToString(name.prefix)}.${name.str}`;
    case "num":
      return name.prefix.kind === "anonymous"
        ? name.num.toString()
        : `${nameToString(name.prefix)}.${name.num.toString()}`;
  }
}

/** Structural equality. Uses the precomputed hash for a cheap mismatch check. */
export function nameEq(a: Name, b: Name): boolean {
  if (a === b) return true;
  if (a.hash !== b.hash || a.kind !== b.kind) return false;
  switch (a.kind) {
    case "anonymous":
      return true;
    case "str":
      return a.str === (b as typeof a).str && nameEq(a.prefix, (b as typeof a).prefix);
    case "num":
      return a.num === (b as typeof a).num && nameEq(a.prefix, (b as typeof a).prefix);
  }
}
