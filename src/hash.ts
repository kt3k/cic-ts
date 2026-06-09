// Deterministic 32-bit hashing utilities.
//
// These back the precomputed `hash` fields on `Name` / `Level` / `Expr`, which
// give the structural-equality fast path described in SPEC.md (Section 0).
// The exact hash values are an implementation detail; only determinism and a
// reasonable distribution matter.

/** Combine two 32-bit hashes into one (order-sensitive). */
export function mixHash(a: number, b: number): number {
  let h = (a ^ Math.imul(b, 0x9e3779b1)) >>> 0;
  h = Math.imul(h ^ (h >>> 15), 0x85ebca6b) >>> 0;
  h = Math.imul(h ^ (h >>> 13), 0xc2b2ae35) >>> 0;
  return (h ^ (h >>> 16)) >>> 0;
}

/** FNV-1a hash of a string. */
export function hashString(s: string): number {
  let h = 2166136261 >>> 0;
  for (let i = 0; i < s.length; i++) {
    h = Math.imul(h ^ s.charCodeAt(i), 16777619) >>> 0;
  }
  return h >>> 0;
}

/** Hash of a bigint via its decimal string. */
export function hashBigInt(n: bigint): number {
  return hashString(n.toString());
}
