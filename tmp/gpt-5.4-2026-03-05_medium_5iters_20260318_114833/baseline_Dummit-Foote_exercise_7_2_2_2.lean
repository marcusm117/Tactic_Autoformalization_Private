import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_2_2 {R : Type*} [Ring R] (p : Polynomial R) :
  p ∣ 0 ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := by
  simpa [and_comm, and_left_comm, and_assoc] using (Polynomial.not_isRegular_iff (p := p))
