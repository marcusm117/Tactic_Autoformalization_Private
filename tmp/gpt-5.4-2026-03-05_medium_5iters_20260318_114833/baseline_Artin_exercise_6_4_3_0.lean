import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  intro hsimple
  have hsolv : IsSolvable G := by
    simpa [pow_one] using
      isSolvable_of_card_eq_prime_pow_mul_prime_pow (G := G) hp hq (a := 2) (b := 1) hG
  letI : CommGroup G := hsimple.commGroup_of_isSolvable hsolv
  have hcardprime : Prime (card G) := hsimple.card_prime
  have hp2 : 1 < p ^ 2 := by
    rw [pow_two]
    nlinarith [hp.one_lt]
  have hnotprime : ¬ Prime (p ^ 2 * q) := by
    exact Nat.not_prime_mul hp2 hq.one_lt
  exact hnotprime (by simpa [hG] using hcardprime)
