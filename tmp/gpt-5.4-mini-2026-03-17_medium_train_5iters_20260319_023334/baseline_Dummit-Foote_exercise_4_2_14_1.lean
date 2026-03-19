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
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos (Nat.pos_of_gt hcard_gt_one) hp_prime.pos
  have hEq : card G = p * m := by
    dsimp [m]
    simpa [mul_comm] using (Nat.mul_div_cancel' hp_dvd).symm
  have hleast : ∀ q : ℕ, Nat.Prime q → q ∣ card G → p ≤ q := by
    intro q hq hqd
    simpa [p] using Nat.minFac_le_of_dvd hq.two_le hqd
  have hHne_bot : H ≠ ⊥ := by
    intro hbot
    have hm1 : m = 1 := by
      simpa [m, hbot] using hHcard
    have hcard : card G = p := by
      simpa [hm1] using hEq
    exact hG (by simpa [hcard] using hp_prime)
  have hHne_top : H ≠ ⊤ := by
    intro htop
    have hcard : card G = card G / p := by
      simpa [m, htop] using hHcard
    have hlt : card G / p < card G := Nat.div_lt_self (Nat.pos_of_gt hcard_gt_one) hp_prime.one_lt
    have : card G < card G := by
      simpa [hcard] using hlt
    exact (Nat.lt_irrefl _ this)
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPerm
  let K : Subgroup G := φ.ker
  have hKnormal : K.Normal := by
    simpa [K] using φ.ker_normal
  have hKne_top : K ≠ ⊤ := by
    have hnotforall : ¬ ∀ g : G, g ∈ H := by
      intro hall
      exact hHne_top (by
        ext g
        constructor
        · intro _; exact hall g
        · intro hg; exact hg)
    obtain ⟨g, hg⟩ := not_forall.mp hnotforall
    intro htopK
    have hgK : g ∈ K := by
      simpa [K, htopK]
    have hfix : φ g = 1 := by
      simpa using (MonoidHom.mem_ker.mp hgK)
    have hcoset : g • (1 : G ⧸ H) = 1 := by
      simpa [φ] using congrArg (fun f : Equiv.Perm (G ⧸ H) => f (1 : G ⧸ H)) hfix
    exact hg (by simpa using hcoset)
  have hq : Fintype.card (G ⧸ H) = p := by
    have hmul : Fintype.card (G ⧸ H) * m = p * m := by
      have hmul0 := Fintype.card_quotient_mul_card_subgroup (G := G) (H := H)
      simpa [hHcard, hEq, m, mul_comm, mul_left_comm, mul_assoc] using hmul0
    exact Nat.mul_right_cancel hm_pos.ne' hmul
  have hKne_bot : K ≠ ⊥ := by
    intro hbotK
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot.mp hbotK)
    have hcardRange : Fintype.card φ.range = card G := Fintype.card_range_of_injective φ hinj
    have hrange_dvd : Fintype.card φ.range ∣ Fintype.card (Equiv.Perm (G ⧸ H)) := by
      exact Fintype.card_dvd_card φ.range
    have hdiv : card G ∣ Nat.factorial p := by
      simpa [hcardRange, hq, Fintype.card_perm] using hrange_dvd
    rcases Nat.eq_or_lt_of_le hp_prime.two_le with rfl | hp_gt2
    · have hdiv2 : card G ∣ 2 := by
        simpa using hdiv
      have hle : card G ≤ 2 := Nat.le_of_dvd (by decide) hdiv2
      have hge : 2 ≤ card G := by
        exact Nat.succ_le_of_lt hcard_gt_one
      have hEq2 : card G = 2 := le_antisymm hle hge
      exact hG (by simpa [hEq2] using (show Nat.Prime 2 from by decide))
    · have hp_pos : 0 < p := by
        exact Nat.pos_of_gt hp_gt2
      have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
        simpa [Nat.succ_pred_eq_of_pos hp_pos] using (Nat.factorial_succ (p - 1))
      have hdiv' : p * m ∣ p * Nat.factorial (p - 1) := by
        simpa [hEq, hfac] using hdiv
      have hmdivfact : m ∣ Nat.factorial (p - 1) := (Nat.mul_dvd_mul_iff_left hp_pos.ne').mp hdiv'
      have hm_ne_one : m ≠ 1 := by
        intro hm1
        have hcard : card G = p := by
          simpa [hm1] using hEq
        exact hG (by simpa [hcard] using hp_prime)
      have hm_gt_one : 1 < m := by
        have hm_pos' : 0 < m := by
          exact Nat.div_pos (Nat.pos_of_gt hcard_gt_one) hp_prime.pos
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hm_pos') hm_ne_one
      let q : ℕ := Nat.minFac m
      have hqprime : Nat.Prime q := by
        simpa [q] using Nat.minFac_prime (Nat.ne_of_gt hm_gt_one)
      have hq_dvd_m : q ∣ m := by
        simpa [q] using Nat.minFac_dvd m
      have hq_dvd_card : q ∣ card G := dvd_trans hq_dvd_m hm_dvd
      have hp_le_q : p ≤ q := hleast q hqprime hq_dvd_card
      have hq_le : q ≤ p - 1 := by
        simpa [q] using hqprime.le_of_dvd_factorial hmdivfact
      have hle' : p ≤ p - 1 := le_trans hp_le_q hq_le
      have hlt : p - 1 < p := by
        omega
      exact (Nat.lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  have hsimp := hs K hKnormal
  rcases hsimp with hbot | htop
  · exact hKne_bot hbot
  · exact hKne_top htop
