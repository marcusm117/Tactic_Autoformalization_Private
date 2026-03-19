import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  intro hsimple
  have hsolv : IsSolvable G := by
    simpa [pow_one] using
      (FiniteGroup.burnside (G := G) (p := p) (q := q) (a := 2) (b := 1) hp hq hG)
  letI : IsSolvable G := hsolv
  letI : CommGroup G := hsimple.commGroup
  have hcardprime : Prime (card G) := hsimple.prime_card
  have hp2ne1 : p ^ 2 ≠ 1 := by
    intro h
    have : p ∣ 1 := by
      rw [← h, pow_two]
      exact dvd_mul_right p p
    exact hp.not_dvd_one this
  have hnotprime : ¬ Prime (p ^ 2 * q) := not_prime_mul hp2ne1 hq.ne_one
  exact False.elim (hnotprime (by simpa [hG] using hcardprime))
