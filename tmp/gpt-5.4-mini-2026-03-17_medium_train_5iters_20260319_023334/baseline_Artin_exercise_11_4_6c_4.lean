import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  classical
  have hdeg : (X^3 - 9 : Polynomial (ZMod 31)).natDegree = 3 := by
    simpa using
      (Polynomial.natDegree_X_pow_sub_C (R := ZMod 31) (a := (9 : ZMod 31)) (n := 3)
        (by decide) (by decide))
  have hroot : ∀ a : ZMod 31, ¬ IsRoot (X^3 - 9 : Polynomial (ZMod 31)) a := by
    intro a
    fin_cases a <;> native_decide
  exact Polynomial.irreducible_of_natDegree_eq_three hdeg hroot
