import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro hS
  have hp' : Nat.Prime p := Nat.prime_iff.mp hp
  have hq' : Nat.Prime q := Nat.prime_iff.mp hq
  letI : Fact (Nat.Prime p) := ⟨hp'⟩
  letI : Fact (Nat.Prime q) := ⟨hq'⟩
  have hG' : Nat.card G = p * q := by
    simpa [Nat.card_eq_fintype_card] using hG
  exact (Finite.not_isSimpleGroup_of_card_eq_prime_mul_prime (G := G) (p := p) (q := q) hG') hS
