import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  simpa using
    (Polynomial.irreducible_X_pow_sub_C (K := ZMod 31) (n := 3) (a := 9)
      (by decide)
      (by native_decide))
