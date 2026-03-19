import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  refine Infinite.of_injective (fun n : ℕ => Equiv.swap 0 n.succ) ?_
  intro n m h
  have h0 : Equiv.swap 0 n.succ 0 = Equiv.swap 0 m.succ 0 :=
    congrArg (fun e : Equiv.Perm ℕ => e 0) h
  exact Nat.succ.inj <| by simpa using h0
