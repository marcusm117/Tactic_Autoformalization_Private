import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  classical
  apply Polynomial.irreducible_of_no_roots
  · native_decide
  · rintro ⟨a, ha⟩
    fin_cases a <;> norm_num at ha
