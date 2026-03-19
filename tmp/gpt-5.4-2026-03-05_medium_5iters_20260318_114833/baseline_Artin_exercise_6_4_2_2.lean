import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro hS
  letI : Fact (Nat.Prime p) := ⟨Nat.prime_iff.mpr hp⟩
  letI : Fact (Nat.Prime q) := ⟨Nat.prime_iff.mpr hq⟩
  have hneq : card G ≠ p * q := by
    simpa [Nat.card_eq_fintype_card] using (hS.card_ne_prime_mul_prime (p := p) (q := q))
  exact hneq hG
