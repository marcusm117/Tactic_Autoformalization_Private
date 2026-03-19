import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hsolv : IsSolvable G := by
    simpa [pow_one] using
      (FiniteGroup.isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (G := G) (p := p) (q := q) (a := 2) (b := 1) hG)
  letI : IsSimpleGroup G := hsimple
  letI : IsSolvable G := hsolv
  letI : CommGroup G := inferInstance
  haveI : Fact (Nat.Prime (card G)) := inferInstance
  have hcardprime : Nat.Prime (card G) := Fact.out
  have hp2ne1 : p ^ 2 ≠ 1 := by
    have hp2 : 2 ≤ p := Nat.Prime.two_le hp
    rw [pow_two]
    omega
  have hnotprime : ¬ Nat.Prime (p ^ 2 * q) := Nat.not_prime_mul hp2ne1 (Nat.Prime.ne_one hq)
  exact False.elim (hnotprime (by simpa [hG] using hcardprime))
