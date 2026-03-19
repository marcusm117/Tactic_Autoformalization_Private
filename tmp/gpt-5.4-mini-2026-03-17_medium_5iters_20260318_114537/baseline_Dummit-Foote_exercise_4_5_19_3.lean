import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  have hsq : Squarefree (Fintype.card G) := by
    rw [hG]
    native_decide
  have h1 : 1 < Fintype.card G := by
    rw [hG]
    norm_num
  first
    | exact Squarefree.not_isSimpleGroup hsq
    | exact Squarefree.not_isSimpleGroup hsq h1
    | letI : Nontrivial G := (Fintype.one_lt_card_iff_nontrivial).2 h1
      exact Squarefree.not_isSimpleGroup hsq
