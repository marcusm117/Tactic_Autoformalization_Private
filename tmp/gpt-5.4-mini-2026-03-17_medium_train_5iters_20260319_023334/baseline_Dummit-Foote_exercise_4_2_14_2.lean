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
  have hposG : 0 < card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hposG hp_prime.pos
  have hEq : card G = p * m := by
    dsimp [m]
    simpa [mul_comm] using (Nat.mul_div_cancel' hp_dvd).symm
  have hindex : H.index = p := by
    have hmul : H.index * m = p * m := by
      simpa [hHcard, hEq, m, mul_comm, mul_left_comm, mul_assoc] using (H.index_mul_card)
    exact Nat.mul_right_cancel hmul hm_pos.ne'
  have hHnormal : H.Normal := by
    have hpindex : Nat.Prime H.index := by
      simpa [hindex] using hp_prime
    exact Subgroup.normal_of_prime_index (H := H) hpindex
  have hHne_bot : H ≠ ⊥ := by
    intro hbot
    have hm1 : m = 1 := by
      simpa [hbot] using hHcard
    have hcard : card G = p := by
      simpa [m, hm1] using hEq
    exact hG (by simpa [hcard] using hp_prime)
  have hHne_top : H ≠ ⊤ := by
    intro htop
    have hmEq : m = card G := by
      simpa [htop] using hHcard
    have hdiv : card G / p = card G := by
      simpa [m] using hmEq
    have hlt : card G / p < card G := Nat.div_lt_self hposG hp_prime.one_lt
    exact (Nat.lt_irrefl _ (lt_of_eq_of_lt hdiv hlt))
  have hcases := hs H hHnormal
  rcases hcases with hbot | htop
  · exact hHne_bot hbot
  · exact hHne_top htop
