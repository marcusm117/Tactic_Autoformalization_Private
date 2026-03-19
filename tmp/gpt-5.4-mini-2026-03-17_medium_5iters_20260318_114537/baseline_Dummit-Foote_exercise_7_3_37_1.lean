import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_37 {p m : ℕ} (hp : p.Prime) :
  IsNilpotent (span ({↑p} : Set $ ZMod $ p^m) : Ideal $ ZMod $ p^m) := by
  refine ⟨m, ?_⟩
  rw [Ideal.span_singleton_pow]
  simpa [Nat.cast_pow] using (ZMod.natCast_self (p ^ m) : ((p ^ m : ℕ) : ZMod (p ^ m)) = 0)
