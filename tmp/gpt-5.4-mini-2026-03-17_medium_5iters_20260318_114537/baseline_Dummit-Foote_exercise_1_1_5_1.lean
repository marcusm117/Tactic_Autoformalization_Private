import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  classical
  refine ⟨?_⟩
  intro g
  have h0 : (0 : ZMod n) ≠ 1 := ZMod.zero_ne_one (Nat.succ_lt_succ hn)
  have h := g.mul_inv_cancel (0 : ZMod n)
  exact h0 (by simpa using h)
