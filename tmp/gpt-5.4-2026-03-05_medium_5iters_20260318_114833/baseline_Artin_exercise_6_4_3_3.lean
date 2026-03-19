import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  intro hsimple
  have hp' : Nat.Prime p := Nat.prime_iff.mp hp
  have hq' : Nat.Prime q := Nat.prime_iff.mp hq
  haveI : Fact (Nat.Prime p) := ⟨hp'⟩
  haveI : Fact (Nat.Prime q) := ⟨hq'⟩
  have hsolv : IsSolvable G := by
    simpa [pow_one] using
      (solvable_of_card_eq_prime_pow_mul_prime_pow
        (G := G) (p := p) (q := q) (a := 2) (b := 1) hG)
  letI : IsSimpleGroup G := hsimple
  letI : IsSolvable G := hsolv
  letI : CommGroup G := inferInstance
  haveI : Fact (Nat.Prime (card G)) := inferInstance
  have hcardprime : Nat.Prime (card G) := Fact.out
  have hp2ne1 : p ^ 2 ≠ 1 := by
    intro h
    have : p ∣ 1 := by
      use p
      simpa [pow_two, Nat.mul_comm] using h.symm
    exact hp'.not_dvd_one this
  have hnotprime : ¬ Nat.Prime (p ^ 2 * q) := Nat.not_prime_mul hp2ne1 hq'.ne_one
  exact False.elim (hnotprime (by simpa [hG] using hcardprime))
