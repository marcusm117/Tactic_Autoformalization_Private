import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  intro hS
  have hcard : Nat.card G = 6545 := by
    simpa using hG
  have hodd : Odd (Nat.card G) := by
    omega
  letI : IsSimpleGroup G := hS
  letI : IsSolvable G := solvable_of_odd_order (G := G) hodd
  have hprime : Nat.Prime (Nat.card G) := by
    simpa using (IsSimpleGroup.prime_card (G := G))
  norm_num [hcard] at hprime
