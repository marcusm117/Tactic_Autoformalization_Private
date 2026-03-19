import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  rintro ⟨z, hz⟩
  rcases z with ⟨x, y⟩
  have hx : b = a * x := by
    simpa using congrArg Prod.fst hz
  exact ⟨x, hx⟩
