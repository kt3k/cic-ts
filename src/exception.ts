// Kernel exceptions (SPEC.md Section 5.5).
//
// Corresponds to Lean's `kernel_exception.h`. A single error type carries a
// descriptive message; the kind tag allows tests to assert on the failure
// category without matching message text.

export type KernelErrorKind =
  | "typeMismatch"
  | "unknownConstant"
  | "alreadyDeclared"
  | "universeMismatch"
  | "looseBVar"
  | "unexpectedMVar"
  | "expectedSort"
  | "expectedPi"
  | "unsupported"
  | "other";

export class KernelError extends Error {
  override readonly name = "KernelError";
  constructor(readonly errorKind: KernelErrorKind, message: string) {
    super(message);
  }
}

export function kernelError(kind: KernelErrorKind, message: string): never {
  throw new KernelError(kind, message);
}
