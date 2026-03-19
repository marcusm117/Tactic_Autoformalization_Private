import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (a : ZMod p) ^ p = a := by
    simpa using (ZMod.pow_card (a := (a : ZMod p)))
  have hzero : ((a ^ p - a : ℤ) : ZMod p) = 0 := by
    simp [hpow]
  have hdiv : (p : ℤ) ∣ a ^ p - a := by
    exact_mod_cast hzero
  exact Int.modEq_iff_dvd.mpr hdiv
