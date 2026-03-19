import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  have hpow : (a : ZMod p) ^ p = a := by
    simpa using (pow_card (a : ZMod p))
  exact Int.modEq_iff_eq_zmod.mpr hpow
