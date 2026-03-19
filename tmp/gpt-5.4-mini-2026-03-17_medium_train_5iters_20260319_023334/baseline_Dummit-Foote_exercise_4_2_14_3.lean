import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  intro hs
  have hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := by
    simpa [IsSimpleGroup] using hs
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
  have hp_le_card : p ≤ card G := Nat.le_of_dvd (by simpa using hcard_gt_one.le) hp_dvd
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.div_pos hp_le_card hp_prime.pos
  have hEqG : card G = p * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel' hp_dvd).symm
  have hindex : H.index = p := by
    have hmul : H.index * m = p * m := by
      calc
        H.index * m = card G := by
          simpa [H.index_mul_card, hHcard]
        _ = p * m := hEqG
    exact Nat.mul_right_cancel hm_pos hmul
  have hquot : Fintype.card (G ⧸ H) = p := by
    simpa [hindex] using (Subgroup.index_eq_card (H := H))
  let φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom
  let K : Subgroup G := φ.ker
  have hKnormal : K.Normal := by
    simpa [K] using φ.ker_normal
  have hneqH : ∃ g : G, g ∉ H := by
    by_contra h
    exact hHne_top (by
      ext g
      constructor
      · intro _; trivial
      · intro _; exact h g)
  rcases hneqH with ⟨g, hg⟩
  have hφg_ne : φ g ≠ 1 := by
    intro h1
    have hfix : ((g : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      simpa using congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ ((1 : G) : G ⧸ H)) h1
    have hg' : g ∈ H := by
      exact (QuotientGroup.eq).mp hfix
    exact hg hg'
  have hnontriv : Nontrivial φ.range := by
    refine ⟨⟨1, by simp⟩, ⟨φ g, by exact ⟨g, rfl⟩⟩, ?_⟩
    intro h
    have h' := congrArg Subtype.val h
    simpa using h'.symm
  have hrange_gt_one : 1 < Fintype.card φ.range := by
    simpa using (Fintype.one_lt_card : 1 < Fintype.card φ.range)
  have hrange_dvd_fact : Fintype.card φ.range ∣ Nat.factorial p := by
    have h := Fintype.card_dvd_card φ.range
    simpa [hquot, Fintype.card_perm] using h
  have hrange_dvd_G : Fintype.card φ.range ∣ card G := by
    have hcard := φ.card_range_mul_card_ker
    -- hcard : Fintype.card φ.range * Fintype.card K = card G
    exact ⟨Fintype.card K, by simpa [mul_comm, mul_left_comm, mul_assoc] using hcard⟩
  have hprime_div_range : ∀ q : ℕ, Nat.Prime q → q ∣ Fintype.card φ.range → q = p := by
    intro q hq hqd
    have hqG : q ∣ card G := dvd_trans hqd hrange_dvd_G
    have hqfact : q ∣ Nat.factorial p := dvd_trans hqd hrange_dvd_fact
    have hp_le_q : p ≤ q := by
      simpa [p] using Nat.minFac_le_of_dvd (Nat.Prime.two_le hp_prime) hqG
    have hq_le_p : q ≤ p := hp_prime.le_of_dvd_factorial hqfact
    exact le_antisymm hq_le_p hp_le_q
  have hp_dvd_range : p ∣ Fintype.card φ.range := by
    obtain ⟨q, hqprime, hqd⟩ := Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨by
      intro h
      have : Fintype.card φ.range = 1 := by omega
      exact (Nat.ne_of_gt hrange_gt_one) this⟩)
    have hqeq : q = p := hprime_div_range q hqprime hqd
    simpa [hqeq] using hqd
  have hrange_eq_p : Fintype.card φ.range = p := by
    have hp2_not_dvd_fact : ¬ p ^ 2 ∣ Nat.factorial p := by
      intro h
      have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
        simpa [Nat.succ_pred_eq_of_pos hp_prime.pos] using (Nat.factorial_succ (p - 1))
      have hp_dvd_pred : p ∣ Nat.factorial (p - 1) := by
        have h' : p * p ∣ p * Nat.factorial (p - 1) := by
          simpa [hfac, pow_two] using h
        exact (Nat.mul_dvd_mul_iff_left hp_prime.pos).mp h'
      exact hp_prime.not_dvd_factorial hp_dvd_pred
    by
      by_contra hne
      have hgt : p < Fintype.card φ.range := by
        have hle : Fintype.card φ.range ≤ p := le_of_not_gt hne
        exact lt_of_le_of_ne hle (by
          intro hEq
          exact hne (le_antisymm (le_of_eq hEq) (le_of_eq (by simpa using hp_dvd_range))))
      have hqpos : 0 < Fintype.card φ.range / p := by
        exact Nat.div_pos (Nat.le_of_lt hgt) hp_prime.pos
      have hqneq1 : Fintype.card φ.range / p ≠ 1 := by
        intro h1
        have hmul := Nat.mul_div_cancel' hp_dvd_range
        have hEq : Fintype.card φ.range = p := by
          simpa [h1] using hmul.symm
        exact (Nat.ne_of_gt hgt) hEq
      have hqgt1 : 1 < Fintype.card φ.range / p := by
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hqpos) (by simpa using hqneq1.symm)
      obtain ⟨q, hqprime, hqd⟩ := Nat.exists_prime_and_dvd hqgt1
      have hqdiv : q ∣ Fintype.card φ.range := by
        have hmul := Nat.mul_div_cancel' hp_dvd_range
        exact dvd_of_dvd_mul_right hqd
      have hqeq : q = p := hprime_div_range q hqprime hqdiv
      have hp2_dvd_range : p ^ 2 ∣ Fintype.card φ.range := by
        have hpdiv : p ∣ Fintype.card φ.range / p := by
          simpa [hqeq] using hqd
        rcases hp_dvd_range with ⟨t, ht⟩
        rcases hpdiv with ⟨u, hu⟩
        refine ⟨t * u, ?_⟩
        rw [pow_two, ← ht, ← hu, mul_assoc]
      have hp2_dvd_fact : p ^ 2 ∣ Nat.factorial p := dvd_trans hp2_dvd_range hrange_dvd_fact
      exact hp2_not_dvd_fact hp2_dvd_fact
  have hker_card : Fintype.card K = m := by
    have hcard := φ.card_range_mul_card_ker
    have hcard' : Fintype.card φ.range * Fintype.card K = p * m := by
      calc
        Fintype.card φ.range * Fintype.card K = card G := by
          simpa [K] using hcard
        _ = p * m := hEqG
    rw [hrange_eq_p] at hcard'
    exact Nat.mul_left_cancel hm_pos hcard'
  have hKne_bot : K ≠ ⊥ := by
    intro hbot
    have hm1 : m = 1 := by
      simpa [hbot] using hker_card
    have hcard : card G = p := by
      simpa [hm1] using hEqG
    exact hG (by simpa [hcard] using hp_prime)
  have hKne_top : K ≠ ⊤ := by
    intro htop
    have hcard : Fintype.card K = card G := by
      simpa [htop] using hker_card
    have : m = card G := by simpa [hcard] using hker_card
    have hlt : card G / p < card G := Nat.div_lt_self (by simpa using hcard_gt_one) hp_prime.one_lt
    have hEq : card G / p = card G := by simpa [m] using this
    exact (Nat.ne_of_lt hlt) hEq
  have hsK := hsimple K hKnormal
  rcases hsK with hbot | htop
  · exact hKne_bot hbot
  · exact hKne_top htop
