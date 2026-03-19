import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  have h3 : Nat.Prime 3 := by decide
  have h13 : Nat.Prime 13 := by decide
  have hcard : card G = 3 ^ 3 * 13 := by
    omega
  simpa [hcard] using
    (Sylow.exists_normal_sylow_of_card_eq_prime_pow_mul_prime (G := G) (p := 3) (q := 13) h3 h13 hcard)
