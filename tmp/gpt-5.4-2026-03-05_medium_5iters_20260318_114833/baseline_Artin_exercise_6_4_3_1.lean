import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  intro hsimple
  have hsolv : IsSolvable G := by
    library_search
  letI : IsSimpleGroup G := hsimple
  letI : IsSolvable G := hsolv
  letI : CommGroup G := by
    library_search
  have hcardprime : Nat.Prime (card G) := by
    library_search
  have hp2ne1 : p ^ 2 ≠ 1 := by
    have hp2gt1 : 1 < p ^ 2 := by
      rw [pow_two]
      nlinarith [Nat.Prime.two_le hp]
    exact ne_of_gt hp2gt1
  have hnotprime : ¬ Nat.Prime (p ^ 2 * q) := Nat.not_prime_mul hp2ne1 (Nat.Prime.ne_one hq)
  exact False.elim <| hnotprime (by simpa [hG] using hcardprime)
