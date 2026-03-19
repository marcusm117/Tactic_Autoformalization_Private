import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_28 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 105) (P : Sylow 3 G) [hP : P.Normal] :
  ∀ a b : G, a*b = b*a := by
  classical
  have hcyc : IsCyclic G := by
    exact isCyclic_of_card_eq_prime_mul_prime_mul_prime hG (by decide : Nat.Prime 3)
      (by decide : Nat.Prime 5) (by decide : Nat.Prime 7) hP
  haveI := hcyc.commGroup
  intro a b
  simpa using mul_comm a b
