import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_2 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p*q) :
  IsSimpleGroup G → false := by
  intro hS
  have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
  have hq' : Nat.Prime q := Nat.prime_iff.mpr hq
  have hG' : Nat.card G = p * q := by
    simpa [Nat.card_eq_fintype_card] using hG
  by_cases hpq : p ≤ q
  · have hqdvd : q ∣ Nat.card G := by
      refine ⟨p, by simpa [hG', Nat.mul_comm]⟩
    rcases exists_prime_orderOf_dvd_card (G := G) hq' hqdvd with ⟨x, hx⟩
    let H : Subgroup G := Subgroup.zpowers x
    have hHcard : Nat.card H = q := by
      simpa [H, hx] using (Nat.card_zpowers x)
    have hindex : H.index = p := by
      have hmul : H.index * q = p * q := by
        simpa [H, hG', hHcard, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          H.index_mul_card
      exact Nat.eq_of_mul_eq_mul_right hq'.pos hmul
    have hmin : Nat.minFac (Nat.card G) = p := by
      rw [hG', Nat.minFac_mul, hp'.minFac_eq, hq'.minFac_eq, min_eq_left hpq]
    have hnormal : H.Normal := by
      exact H.normal_of_index_eq_minFac (by simpa [hmin] using hindex)
    letI : H.Normal := hnormal
    have hbt : H = ⊥ ∨ H = ⊤ := hS.eq_bot_or_eq_top H
    cases hbt with
    | inl hbot =>
        have hxne : x ≠ 1 := by
          intro hx1
          simpa [hx1] using hx
        have hxmem : x ∈ H := by
          simpa [H] using (show x ∈ Subgroup.zpowers x by simp)
        have : x = 1 := by
          simpa [hbot] using hxmem
        exact False.elim (hxne this)
    | inr htop =>
        have hcardGq : Nat.card G = q := by
          simpa [htop] using hHcard
        have hmul : p * q = 1 * q := by
          calc
            p * q = Nat.card G := hG'.symm
            _ = q := hcardGq
            _ = 1 * q := by simp
        have hp1 : p = 1 := Nat.eq_of_mul_eq_mul_right hq'.pos hmul
        exact False.elim (hp'.ne_one hp1)
  · have hqp : q < p := lt_of_not_ge hpq
    have hpdvd : p ∣ Nat.card G := by
      refine ⟨q, by simpa [hG']⟩
    rcases exists_prime_orderOf_dvd_card (G := G) hp' hpdvd with ⟨x, hx⟩
    let H : Subgroup G := Subgroup.zpowers x
    have hHcard : Nat.card H = p := by
      simpa [H, hx] using (Nat.card_zpowers x)
    have hindex : H.index = q := by
      have hmul : H.index * p = q * p := by
        simpa [H, hG', hHcard, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          H.index_mul_card
      exact Nat.eq_of_mul_eq_mul_right hp'.pos hmul
    have hmin : Nat.minFac (Nat.card G) = q := by
      rw [hG', Nat.minFac_mul, hp'.minFac_eq, hq'.minFac_eq, min_eq_right (le_of_lt hqp)]
    have hnormal : H.Normal := by
      exact H.normal_of_index_eq_minFac (by simpa [hmin] using hindex)
    letI : H.Normal := hnormal
    have hbt : H = ⊥ ∨ H = ⊤ := hS.eq_bot_or_eq_top H
    cases hbt with
    | inl hbot =>
        have hxne : x ≠ 1 := by
          intro hx1
          simpa [hx1] using hx
        have hxmem : x ∈ H := by
          simpa [H] using (show x ∈ Subgroup.zpowers x by simp)
        have : x = 1 := by
          simpa [hbot] using hxmem
        exact False.elim (hxne this)
    | inr htop =>
        have hcardGp : Nat.card G = p := by
          simpa [htop] using hHcard
        have hmul : q * p = 1 * p := by
          calc
            q * p = Nat.card G := by simpa [Nat.mul_comm] using hG'.symm
            _ = p := hcardGp
            _ = 1 * p := by simp
        have hq1 : q = 1 := Nat.eq_of_mul_eq_mul_right hp'.pos hmul
        exact False.elim (hq'.ne_one hq1)
