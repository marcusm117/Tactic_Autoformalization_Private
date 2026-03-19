import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_3_37 {p m : ℕ} (hp : p.Prime) :
  IsNilpotent (span ({↑p} : Set $ ZMod $ p^m) : Ideal $ ZMod $ p^m) := by
  refine ⟨m + 1, ?_⟩
  rw [Ideal.span_singleton_pow]
  have hpowzero : ((↑p : ZMod (p ^ m)) ^ (m + 1)) = 0 := by
    calc
      ((↑p : ZMod (p ^ m)) ^ (m + 1)) = (((p ^ (m + 1) : ℕ) : ZMod (p ^ m))) := by
        simp
      _ = 0 := by
        rw [pow_succ, Nat.cast_mul]
        simp
  simp [hpowzero]
