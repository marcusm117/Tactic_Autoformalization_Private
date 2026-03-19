import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  (∃ (P : Sylow p G), P.Normal) ∨ (∃ (P : Sylow q G), P.Normal) ∨ (∃ (P : Sylow r G), P.Normal) := by
  simpa using
    FiniteGroup.exists_normal_sylow_subgroup_of_card_eq_prime_mul_prime_mul_prime
      (G := G) hpqr hpqr1 hG
