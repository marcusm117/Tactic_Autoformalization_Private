import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_2_2 {R : Type*} [Ring R] (p : Polynomial R) :
  p ∣ 0 ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := by
  classical
  simpa [Polynomial.smul_eq_C_mul] using
    (Polynomial.exists_nonzero_smul_eq_zero_iff (R := R) (p := p))
