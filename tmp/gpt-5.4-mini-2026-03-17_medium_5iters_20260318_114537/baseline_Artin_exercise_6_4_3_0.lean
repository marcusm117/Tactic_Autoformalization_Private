import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  exact not_isSimpleGroup_of_card_eq_prime_pow_mul_prime_pow hp hq hG
