import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_2_2 {R : Type*} [Ring R] (p : Polynomial R) :
  p ∣ 0 ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := by
  classical
  constructor
  · intro hp
    rcases hp with ⟨q, hq⟩
    rcases Polynomial.exists_nonzero_smul_eq_zero_of_mul_eq_zero (p := p) hq with ⟨b, hb, hbp⟩
    exact ⟨b, hb, hbp⟩
  · rintro ⟨b, hb, hbp⟩
    exact ⟨0, by simp, by simpa using hbp⟩
