import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  have hsolv : IsSolvable G := by
    exact IsSolvable.of_squarefree_card (by
      rw [hG]
      decide)
  have hnp : ¬ Nat.Prime (Fintype.card G) := by
    rw [hG]
    decide
  exact hsolv.not_isSimpleGroup hnp
