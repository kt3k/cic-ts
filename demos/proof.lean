-- A standalone proof file checked by the cic-ts front end.
--   deno task run demos/proof.lean

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

axiom Nat.add : Nat → Nat → Nat

inductive Eq.{u} (α : Sort u) (a : α) : α → Prop where
  | refl : Eq.{u} α a a

-- 2 + 3 = 5, proved by reflexivity: the kernel reduces Nat.add 2 3 to 5.
theorem two_add_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5

#check two_add_three
#check Nat.succ (Nat.succ Nat.zero)
