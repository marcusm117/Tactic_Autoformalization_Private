import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨?_⟩
  intro g
  haveI := g
  have hne : (0 : ZMod n) ≠ 1 := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = 0 := by
      simpa [eq_comm] using h
    have hdiv : n ∣ (1 : ℕ) := by
      exact (ZMod.natCast_eq_zero_iff_dvd (n := n) (m := 1)).mp h'
    have hle : n ≤ 1 := Nat.le_of_dvd (Nat.pos_of_gt hn) hdiv
    exact not_lt_of_ge hle hn
  have hmul : (0 : ZMod n) * (0 : ZMod n)⁻¹ = 1 := mul_inv_cancel (0 : ZMod n)
  have hzero : (0 : ZMod n) * (0 : ZMod n)⁻¹ = 0 := by simp
  exact hne (by simpa [hzero] using hmul)
