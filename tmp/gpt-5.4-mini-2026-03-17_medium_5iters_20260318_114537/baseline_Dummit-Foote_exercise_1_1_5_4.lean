import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨fun g => ?_⟩
  have hmul : (0 : ZMod n) * @Inv.inv (ZMod n) g 0 = 1 := by
    simpa using (@mul_inv_cancel (ZMod n) g (0 : ZMod n))
  have hzero : (0 : ZMod n) * @Inv.inv (ZMod n) g 0 = 0 := by
    simp
  have h01 : (0 : ZMod n) = 1 := by
    calc
      (0 : ZMod n) = (0 : ZMod n) * @Inv.inv (ZMod n) g 0 := by symm; exact hzero
      _ = 1 := hmul
  have hne : (0 : ZMod n) ≠ 1 := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = 0 := by
      simpa using h.symm
    have hdiv : n ∣ 1 := by
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd (n := n) (m := 1)).mp h'
    have hle : n ≤ 1 := Nat.le_of_dvd (by decide) hdiv
    exact (not_lt_of_ge hle hn) hn
  exact hne h01
