import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  classical
  have hmonic : Monic (X^3 - 9 : Polynomial (ZMod 31)) := by
    simp
  have hroot : ∀ a : ZMod 31, ¬ IsRoot (X^3 - 9 : Polynomial (ZMod 31)) a := by
    intro a
    simpa [Polynomial.IsRoot] using (show a ^ 3 ≠ (9 : ZMod 31) by native_decide)
  exact Polynomial.irreducible_of_no_root hmonic hroot
