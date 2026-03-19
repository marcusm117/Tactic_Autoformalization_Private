import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  have hsq : Nat.squarefree (Fintype.card G) := by
    rw [hG]
    native_decide
  exact Nat.squarefree.not_isSimpleGroup hsq
