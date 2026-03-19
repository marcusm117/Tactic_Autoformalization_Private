import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro hS
  have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
  have hq' : Nat.Prime q := Nat.prime_iff.mpr hq
  have hp1 : p ≠ 1 := hp'.ne_one
  have hq1 : q ≠ 1 := hq'.ne_one
  by_cases hpq : p ≤ q
  · have hqdvd : q ∣ Fintype.card G := by
      refine ⟨p, by simpa [hG, Nat.mul_comm]⟩
    rcases exists_prime_orderOf_dvd_card (G := G) q hq' hqdvd with ⟨x, hx⟩
    let H : Subgroup G := Subgroup.zpowers x
    have hHcard : Fintype.card H = q := by
      simpa [H, hx] using Subgroup.card_zpowers x
    have hindex : H.index = p := by
      have hmul : H.index * q = p * q := by
        calc
          H.index * q = H.index * Fintype.card H := by simpa [hHcard]
          _ = Fintype.card G := H.index_mul_card
          _ = p * q := hG
      exact Nat.eq_of_mul_eq_mul_right hq'.pos hmul
    have hmin : Nat.minFac (Fintype.card G) = p := by
      simpa [hG, hp'.minFac_eq, hq'.minFac_eq, min_eq_left hpq] using
        (Nat.minFac_mul hp1 hq1)
    have hnormal : H.Normal := by
      exact H.normal_of_index_eq_minFac (by simpa [hmin] using hindex)
    letI : H.Normal := hnormal
    have hbt : H = ⊥ ∨ H = ⊤ := hS.eq_bot_or_eq_top H
    cases hbt with
    | inl hbot =>
        have hxmem : x ∈ H := by
          change x ∈ Subgroup.zpowers x
          exact ⟨1, by simp⟩
        have hx1 : x = 1 := by
          simpa [H, hbot] using hxmem
        have hqeq1 : q = 1 := by
          have : 1 = q := by simpa [hx1] using hx
          exact this.symm
        exact False.elim (hq1 hqeq1)
    | inr htop =>
        have hpeq1 : p = 1 := by
          have : 1 = p := by simpa [htop] using hindex
          exact this.symm
        exact False.elim (hp1 hpeq1)
  · have hqp : q ≤ p := le_of_lt (lt_of_not_ge hpq)
    have hpdvd : p ∣ Fintype.card G := by
      refine ⟨q, by simpa [hG]⟩
    rcases exists_prime_orderOf_dvd_card (G := G) p hp' hpdvd with ⟨x, hx⟩
    let H : Subgroup G := Subgroup.zpowers x
    have hHcard : Fintype.card H = p := by
      simpa [H, hx] using Subgroup.card_zpowers x
    have hindex : H.index = q := by
      have hmul : H.index * p = q * p := by
        calc
          H.index * p = H.index * Fintype.card H := by simpa [hHcard]
          _ = Fintype.card G := H.index_mul_card
          _ = p * q := hG
          _ = q * p := by rw [Nat.mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hp'.pos hmul
    have hmin : Nat.minFac (Fintype.card G) = q := by
      simpa [hG, hp'.minFac_eq, hq'.minFac_eq, min_eq_right hqp] using
        (Nat.minFac_mul hp1 hq1)
    have hnormal : H.Normal := by
      exact H.normal_of_index_eq_minFac (by simpa [hmin] using hindex)
    letI : H.Normal := hnormal
    have hbt : H = ⊥ ∨ H = ⊤ := hS.eq_bot_or_eq_top H
    cases hbt with
    | inl hbot =>
        have hxmem : x ∈ H := by
          change x ∈ Subgroup.zpowers x
          exact ⟨1, by simp⟩
        have hx1 : x = 1 := by
          simpa [H, hbot] using hxmem
        have hpeq1 : p = 1 := by
          have : 1 = p := by simpa [hx1] using hx
          exact this.symm
        exact False.elim (hp1 hpeq1)
    | inr htop =>
        have hqeq1 : q = 1 := by
          have : 1 = q := by simpa [htop] using hindex
          exact this.symm
        exact False.elim (hq1 hqeq1)
