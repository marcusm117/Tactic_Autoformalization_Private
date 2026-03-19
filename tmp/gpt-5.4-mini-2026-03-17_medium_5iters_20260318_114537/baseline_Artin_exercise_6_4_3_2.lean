import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  haveI : IsSolvableGroup G := by
    exact isSolvableGroup_of_card_eq_prime_pow_mul_prime_pow hp hq hG
  intro hS
  have hprime : Nat.Prime (card G) := IsSimpleGroup.card_eq_prime hS
  have hpdvd : p ∣ card G := by
    rw [hG]
    refine ⟨p * q, by omega⟩
  have hpeq : p = 1 ∨ p = card G := hprime.eq_one_or_self_of_dvd hpdvd
  cases hpeq with
  | inl hp1 =>
      exact hp.ne_one hp1
  | inr hpc =>
      rw [hG] at hpc
      omega
