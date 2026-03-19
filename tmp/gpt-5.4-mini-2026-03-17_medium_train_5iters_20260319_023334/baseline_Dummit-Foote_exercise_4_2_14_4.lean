import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  intro hs
  rcases hs with ⟨hsimple⟩
  have hcard_gt_one : 1 < card G := by
    simpa using (Fintype.one_lt_card : 1 < card G)
  let p : ℕ := Nat.minFac (card G)
  have hp_prime : Nat.Prime p := by
    simpa [p] using Nat.minFac_prime (Nat.ne_of_gt hcard_gt_one)
  have hp_dvd : p ∣ card G := by
    simpa [p] using Nat.minFac_dvd (card G)
  have hp_le_card : p ≤ card G := Nat.le_of_dvd hp_prime.pos hp_dvd
  let m : ℕ := card G / p
  have hm_dvd : m ∣ card G := Nat.div_dvd_of_dvd hp_dvd
  obtain ⟨H, fH, hHcard⟩ := hG1 m hm_dvd
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hp_le_card hp_prime.pos
  have hEqG : card G = p * m := by
    dsimp [m]
    simpa [mul_comm] using (Nat.mul_div_cancel' hp_dvd).symm
  have hindex : H.index = p := by
    have hmul : H.index * m = p * m := by
      calc
        H.index * m = card G := by
          simpa [hHcard] using H.index_mul_card
        _ = p * m := hEqG
    exact Nat.mul_right_cancel hm_pos hmul
  have hquot : p = Fintype.card (G ⧸ H) := by
    simpa [hindex] using (Subgroup.index_eq_card (H := H))
  have hHne_top : H ≠ ⊤ := by
    intro htop
    have hEq : card G / p = card G := by
      simpa [m, htop] using hHcard.symm
    have hlt : card G / p < card G := Nat.div_lt_self hp_prime.pos hcard_gt_one
    exact (Nat.ne_of_lt hlt) hEq
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  let K : Subgroup G := φ.ker
  have hKnormal : K.Normal := by
    intro g x hx
    dsimp [K] at hx ⊢
    simp [MonoidHom.mem_ker, map_mul, map_inv, hx]
  have hKne_top : K ≠ ⊤ := by
    intro htop
    have htriv : ∀ g : G, g ∈ H := by
      intro g
      have hgK : g ∈ K := by
        rw [htop]
        trivial
      have hg1 : φ g = 1 := by
        simpa [K] using hgK
      have hcoset : g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        simpa [φ] using congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ ((1 : G) : G ⧸ H)) hg1
      have hqeq : ((g : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        simpa using hcoset
      have hgInv : g⁻¹ ∈ H := by
        simpa using (QuotientGroup.eq.mp hqeq)
      exact H.inv_mem hgInv
    exact hHne_top (by
      ext g
      constructor
      · intro hg
        trivial
      · intro hg
        exact htriv g)
  have hKne_bot : K ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective φ := by
      simpa [K] using (MonoidHom.ker_eq_bot.mp hbot)
    have hcardRange : Fintype.card φ.range = card G := Fintype.card_range_of_injective φ hinj
    have hrange_dvd : Fintype.card φ.range ∣ Fintype.card (Equiv.Perm (G ⧸ H)) := Fintype.card_dvd_card φ.range
    have hdivG : card G ∣ Nat.factorial p := by
      simpa [hcardRange, hquot, Fintype.card_perm] using hrange_dvd
    have hm_ne_one : m ≠ 1 := by
      intro hm1
      have hcard : card G = p := by
        simpa [m, hm1] using hEqG
      exact hG (by simpa [hcard] using hp_prime)
    have hm_gt_one : 1 < m := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hm_pos) hm_ne_one
    obtain ⟨q, hqprime, hqd⟩ := Nat.exists_prime_and_dvd hm_gt_one
    have hqG : q ∣ card G := dvd_trans hqd hm_dvd
    have hp_le_q : p ≤ q := by
      simpa [p] using Nat.minFac_le_of_dvd hqprime.two_le hqG
    have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
      simpa [Nat.succ_pred_eq_of_pos hp_prime.pos] using (Nat.factorial_succ (p - 1))
    have hpm_fact : p * m ∣ p * Nat.factorial (p - 1) := by
      simpa [hEqG, hfac, mul_comm, mul_left_comm, mul_assoc] using hdivG
    have hm_fact : m ∣ Nat.factorial (p - 1) := (Nat.mul_dvd_mul_iff_left hp_prime.pos).mp hpm_fact
    have hq_le : q ≤ p - 1 := hp_prime.le_of_dvd_factorial (dvd_trans hqd hm_fact)
    have : False := by
      omega
    exact this.elim
  have hcases := hsimple K hKnormal
  rcases hcases with hbot | htop
  · exact hKne_bot hbot
  · exact hKne_top htop
