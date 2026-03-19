import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  intro hsimple
  have hsq : Nat.Squarefree (Fintype.card G) := by
    rw [hG]
    decide
  haveI : IsSolvable G := isSolvable_of_squarefree_card hsq
  have hprime : Nat.Prime (Fintype.card G) := hsimple.card_eq_prime
  have hnotprime : ¬ Nat.Prime 1365 := by decide
  exact hnotprime (by simpa [hG] using hprime)
