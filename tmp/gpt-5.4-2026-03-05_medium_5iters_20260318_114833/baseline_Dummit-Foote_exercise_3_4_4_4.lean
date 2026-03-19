import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  classical
  have hP :
      ∀ m : ℕ,
        ∀ {A : Type _} [CommGroup A] [Fintype A],
          Fintype.card A = m →
          ∀ {d : ℕ}, d ∣ Fintype.card A → ∃ H : Subgroup A, Fintype.card H = d := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih A _ _ hA d hd
    have hApos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨(1 : A)⟩
    by_cases hd1 : d = 1
    · refine ⟨⊥, ?_⟩
      simp [hd1]
    · by_cases hdprime : Nat.Prime d
      · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card hdprime hd
        refine ⟨Subgroup.zpowers x, ?_⟩
        simpa [hx] using Fintype.card_zpowers x
      · have hd0 : d ≠ 0 := by
          intro h0
          rw [h0] at hd
          simp at hd
          exact (Nat.ne_of_gt hApos) hd
        have hd2 : 2 ≤ d := Nat.succ_le_of_lt <|
          Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hd0, hd1⟩
        obtain ⟨p, hpprime, hpd⟩ := Nat.exists_prime_and_dvd hd2
        obtain ⟨k, hk⟩ := hpd
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card hpprime (dvd_trans hpd hd)
        let N : Subgroup A := Subgroup.zpowers x
        have hNcard : Fintype.card N = p := by
          simpa [N, hx] using Fintype.card_zpowers x
        have hqmul : Fintype.card (A ⧸ N) * p = m := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hA, hNcard] using
            (Subgroup.card_quotient_mul_card_subgroup N)
        have hqpos : 0 < Fintype.card (A ⧸ N) := Fintype.card_pos_iff.mpr ⟨(1 : A ⧸ N)⟩
        have hq_lt : Fintype.card (A ⧸ N) < m := by
          have hlt : Fintype.card (A ⧸ N) * 1 < Fintype.card (A ⧸ N) * p := by
            exact Nat.mul_lt_mul_of_pos_left hpprime.one_lt hqpos
          calc
            Fintype.card (A ⧸ N) = Fintype.card (A ⧸ N) * 1 := by simp
            _ < Fintype.card (A ⧸ N) * p := hlt
            _ = m := hqmul
        obtain ⟨t, ht⟩ := hd
        have ht' : m = d * t := by
          simpa [hA] using ht
        have hqeq : Fintype.card (A ⧸ N) = k * t := by
          apply Nat.eq_of_mul_eq_mul_left hpprime.pos
          calc
            p * Fintype.card (A ⧸ N) = Fintype.card (A ⧸ N) * p := by ac_rfl
            _ = m := hqmul
            _ = d * t := ht'
            _ = (p * k) * t := by rw [hk]
            _ = p * (k * t) := by rw [Nat.mul_assoc]
        have hkdivq : k ∣ Fintype.card (A ⧸ N) := ⟨t, hqeq.symm⟩
        obtain ⟨K, hKcard⟩ :=
          ih (Fintype.card (A ⧸ N)) hq_lt (A := A ⧸ N) rfl hkdivq
        refine ⟨K.comap (QuotientGroup.mk' N), ?_⟩
        calc
          Fintype.card (K.comap (QuotientGroup.mk' N)) = Fintype.card K * Fintype.card N := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using K.card_preimage_mk N
          _ = k * p := by rw [hKcard, hNcard]
          _ = d := by simpa [Nat.mul_comm] using hk.symm
  obtain ⟨H, hH⟩ := hP (Fintype.card G) (A := G) rfl hn
  exact ⟨H, inferInstance, hH⟩
