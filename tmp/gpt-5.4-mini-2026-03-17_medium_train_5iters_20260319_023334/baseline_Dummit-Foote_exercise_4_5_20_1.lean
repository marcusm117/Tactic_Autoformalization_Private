import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  intro hsimple
  have hprime : Nat.Prime (Fintype.card G) := hsimple.card_prime
  have hnot : ¬ Nat.Prime 1365 := by decide
  exact hnot (by simpa [hG] using hprime)
