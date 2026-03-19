import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨?_⟩
  intro g
  letI : Fact (1 < n) := ⟨hn⟩
  letI : Group (ZMod n) := g
  have h01 : (0 : ZMod n) ≠ 1 := zero_ne_one
  have h : (0 : ZMod n) = 1 := by
    calc
      (0 : ZMod n) = (0 : ZMod n)⁻¹ * 0 := by simp
      _ = 1 := by simpa using (mul_left_inv (0 : ZMod n))
  exact h01 h
