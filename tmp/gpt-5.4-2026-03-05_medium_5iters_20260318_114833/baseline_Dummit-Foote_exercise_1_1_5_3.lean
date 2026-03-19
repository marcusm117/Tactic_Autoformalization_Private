import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨?_⟩
  intro g
  letI : Fact (1 < n) := ⟨hn⟩
  have h01 : (0 : ZMod n) ≠ 1 := zero_ne_one
  letI : Group (ZMod n) := g
  have h10 : (1 : ZMod n) = 0 := by
    calc
      (1 : ZMod n) = (0 : ZMod n)⁻¹ * 0 := by
        symm
        simpa using (inv_mul_cancel (0 : ZMod n))
      _ = 0 := by simp
  exact h01 h10.symm
