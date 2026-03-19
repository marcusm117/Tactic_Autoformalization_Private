import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  have h3 : Nat.Prime 3 := by decide
  have h13 : Nat.Prime 13 := by decide
  have hdiv : 13 ∣ 3 ^ 3 - 1 := by decide
  have hcard : card G = 13 * 3 ^ 3 := by
    omega
  have hnormal : ∃ P : Sylow 3 G, P.Normal := by
    exact exists_normal_sylow_of_card_eq_prime_mul_prime_pow (G := G) (p := 13) (q := 3) h13 h3 hdiv hcard
  rcases hnormal with ⟨P, hP⟩
  exact ⟨3, P, h3, by omega, hP⟩
