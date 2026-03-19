import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (a : ZMod p) ^ p = a := by
    simpa using (ZMod.pow_card (a := (a : ZMod p)))
  have hdiv : p ∣ a - a ^ p := by
    apply (Int.cast_zmod_eq_zero_iff_dvd.mp ?_)
    simpa [hpow]
  exact Int.modEq_iff_dvd.mpr hdiv
