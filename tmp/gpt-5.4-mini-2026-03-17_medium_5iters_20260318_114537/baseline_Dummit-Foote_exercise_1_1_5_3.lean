import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨?_⟩
  intro g
  haveI := g
  have hmul : (0 : ZMod n) * (0 : ZMod n)⁻¹ = 1 := mul_inv_cancel (0 : ZMod n)
  have hzero : (0 : ZMod n) * (0 : ZMod n)⁻¹ = 0 := by
    simpa using (zero_mul ((0 : ZMod n)⁻¹))
  have h01 : (0 : ZMod n) = 1 := by
    calc
      (0 : ZMod n) = (0 : ZMod n) * (0 : ZMod n)⁻¹ := by symm; exact hzero
      _ = 1 := hmul
  have hne : (0 : ZMod n) ≠ 1 := by
    intro h
    exact Nat.lt_irrefl _ (lt_of_lt_of_eq hn (by simpa using h.symm))
  exact hne h01
