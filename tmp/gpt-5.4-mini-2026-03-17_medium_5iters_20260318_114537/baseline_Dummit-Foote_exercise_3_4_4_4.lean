import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_4 {G : Type*} [CommGroup G] [Fintype G] {n : ℕ}
    (hn : n ∣ (card G)) :
    ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n  := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {G : Type*} [CommGroup G] [Fintype G], n ∣ card G →
      ∃ (H : Subgroup G) (H_fin : Fintype H), @card H H_fin = n
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G _ _ hn
    by_cases h1 : n = 1
    · subst h1
      refine ⟨⊥, inferInstance, by simp⟩
    have hpos : 0 < n := by
      by_contra hnp
      have hzero : n = 0 := Nat.eq_zero_of_not_pos hnp
      subst hzero
      have hcard : Fintype.card G = 0 := by
        simpa [Nat.zero_dvd_iff] using hn
      exact (Fintype.card_ne_zero (α := G)) hcard
    have hgt1 : 1 < n := by
      exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (by simpa using h1)
    by_cases hp : Nat.Prime n
    · rcases hp.exists_subgroup_card (G := G) hn with ⟨H, hH⟩
      refine ⟨H, inferInstance, ?_⟩
      simpa using hH
    · rcases Nat.exists_prime_and_dvd hgt1 with ⟨p, hpprime, hpdvd⟩
      rcases hpdvd with ⟨k, hk⟩
      have hpdiv : p ∣ card G := by
        exact dvd_trans (by exact ⟨k, hk.symm⟩) hn
      rcases hpprime.exists_subgroup_card (G := G) hpdiv with ⟨N, hN⟩
      have hNcard : @card N inferInstance = p := by
        simpa using hN
      haveI : CommGroup (G ⧸ N) := by infer_instance
      haveI : Fintype (G ⧸ N) := by infer_instance
      have hqmul : card (G ⧸ N) * p = card G := by
        simpa [hNcard] using (Fintype.card_quotient_mul_card (H := N))
      have hqdiv : k ∣ card (G ⧸ N) := by
        have hmul : k * p ∣ card (G ⧸ N) * p := by
          simpa [hk, hqmul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
        exact Nat.dvd_of_mul_dvd_mul_right hmul
      have hkpos : 0 < k := by
        by_contra hk0
        have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
        have hn0 : n = 0 := by
          simpa [hk0'] using hk
        exact (Nat.ne_of_gt hpos) hn0
      have hklt : k < n := by
        rw [hk]
        have hlt : 1 * k < p * k := Nat.mul_lt_mul_right hpgt hkpos
        simpa [one_mul, Nat.mul_comm] using hlt
      rcases ih k hklt (G := G ⧸ N) hqdiv with ⟨K, K_fin, hK⟩
      refine ⟨K.comap (QuotientGroup.mk' N), inferInstance, ?_⟩
      have hcardcomap : @card (K.comap (QuotientGroup.mk' N)) inferInstance =
          card N * card K := by
        simpa using (Fintype.card_comap (f := QuotientGroup.mk' N) (K := K))
      simpa [hNcard, hK, hk, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcardcomap
  exact hP n (G := G) hn
