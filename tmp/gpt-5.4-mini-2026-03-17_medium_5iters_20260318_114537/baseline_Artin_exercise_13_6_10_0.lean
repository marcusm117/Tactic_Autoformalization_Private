import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by
  classical
  apply Units.ext
  simpa using (Fintype.prod_univ_units (α := K))
