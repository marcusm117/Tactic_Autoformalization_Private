import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  classical
  have hcard : Fintype.card (ZMod 7) = Fintype.card F := by
    simpa using hF.symm
  let e : ZMod 7 ≃+* F := FiniteField.equivOfCardEq hcard
  simpa using
    ((Polynomial.mapEquiv e).irreducible_iff).2
      (by native_decide : Irreducible (X ^ 2 + 1 : Polynomial (ZMod 7)))
