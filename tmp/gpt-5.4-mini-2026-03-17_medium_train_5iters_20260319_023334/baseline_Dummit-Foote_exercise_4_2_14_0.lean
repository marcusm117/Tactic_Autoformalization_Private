import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  intro hs
  have hcard_gt_one : 1 < card G := by
    simpa using (Fintype.one_lt_card : 1 < card G)
  let p : ℕ := Nat.minFac (card G)
  have hp_prime : Nat.Prime p := by
    simpa [p] using Nat.minFac_prime (Nat.ne_of_gt hcard_gt_one)
  have hp_dvd : p ∣ card G := by
    simpa [p] using Nat.minFac_dvd (card G)
  let m : ℕ := card G / p
  have hm_dvd : m ∣ card G := Nat.div_dvd_of_dvd hp_dvd
  obtain ⟨H, fH, hHcard⟩ := hG1 m hm_dvd
  have hleast : ∀ q : ℕ, Nat.Prime q → q ∣ card G → p ≤ q := by
    intro q hq hqd
    simpa [p] using Nat.minFac_le_of_dvd hqd
  have hposH : 0 < Fintype.card H := by
    exact Fintype.card_pos_iff.mpr ⟨1, Subgroup.one_mem H⟩
  have hEq : card G = Fintype.card H * p := by
    have hmul : p * Fintype.card H = card G := by
      simpa [m, hHcard] using (Nat.mul_div_cancel' hp_dvd)
    simpa [mul_comm] using hmul.symm
  have hindex : card G / Fintype.card H = p := by
    exact Nat.div_eq_of_eq_mul_right hEq hposH
  have hindex_prime : Nat.Prime (card G / Fintype.card H) := by
    simpa [hindex] using hp_prime
  have hleast_index : ∀ q : ℕ, Nat.Prime q → q ∣ card G → card G / Fintype.card H ≤ q := by
    intro q hq hqd
    simpa [hindex] using hleast q hq hqd
  have hHnormal : H.Normal := by
    exact Subgroup.normal_of_index_eq_prime (H := H) hindex_prime hleast_index
  have hHne_bot : H ≠ ⊥ := by
    intro hbot
    have hcard1 : Fintype.card H = 1 := by
      simpa [hbot]
    have hGp : card G = p := by
      simpa [hcard1] using hEq
    exact hG (by simpa [hGp] using hp_prime)
  have hHne_top : H ≠ ⊤ := by
    intro htop
    have hEq' : card G = card G * p := by
      simpa [htop] using hEq
    have hlt : card G < card G * p := by
      exact Nat.lt_mul_of_one_lt_right (Nat.pos_of_gt hcard_gt_one) hp_prime.one_lt
    have : card G < card G := by
      simpa [hEq'] using hlt
    exact (Nat.lt_irrefl _ this)
  have hcase := hs.eq_bot_or_eq_top hHnormal
  rcases hcase with hbot | htop
  · exact hHne_bot hbot
  · exact hHne_top htop
