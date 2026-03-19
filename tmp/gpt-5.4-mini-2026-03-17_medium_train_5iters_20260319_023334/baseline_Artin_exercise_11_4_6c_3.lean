import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  classical
  have hdeg : (X^3 - 9 : Polynomial (ZMod 31)).natDegree = 3 := by
    native_decide
  have hroot : ∀ a : ZMod 31, ¬ IsRoot (X^3 - 9 : Polynomial (ZMod 31)) a := by
    intro a
    fin_cases a <;> norm_num [Polynomial.IsRoot]
  exact Polynomial.irreducible_of_natDegree_eq_three hdeg hroot
