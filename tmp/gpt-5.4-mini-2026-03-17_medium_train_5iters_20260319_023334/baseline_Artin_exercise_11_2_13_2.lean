import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  rintro ⟨z, hz⟩
  refine ⟨z.re, ?_⟩
  have h := congrArg (fun w : GaussianInt => w.re) hz
  simpa using h
