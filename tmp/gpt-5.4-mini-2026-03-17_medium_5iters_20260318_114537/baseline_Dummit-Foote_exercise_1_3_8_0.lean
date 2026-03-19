import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  refine Infinite.of_injective (fun n : ℕ => Equiv.swap 0 (n + 1)) ?_
  intro m n h
  have h' : m + 1 = n + 1 := by
    simpa using congrArg (fun e : Equiv.Perm ℕ => e 0) h
  exact Nat.add_right_cancel h'
