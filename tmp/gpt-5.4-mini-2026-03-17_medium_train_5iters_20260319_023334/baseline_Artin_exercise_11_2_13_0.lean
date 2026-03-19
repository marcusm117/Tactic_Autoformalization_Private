import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  rintro ⟨z, hz⟩
  refine ⟨z.re, ?_⟩
  simpa using congrArg GaussianInt.re hz
