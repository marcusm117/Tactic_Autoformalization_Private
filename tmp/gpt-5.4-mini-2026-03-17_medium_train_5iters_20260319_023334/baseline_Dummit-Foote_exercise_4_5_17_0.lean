import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_17 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 105) :
  (∃ (P : Sylow 5 G), P.Normal) ∧ (∃ (P : Sylow 7 G), P.Normal) := by
  classical
  constructor
  ·
    have h7 : Fintype.card (Sylow 7 G) = 1 := by
      have hdiv : Fintype.card (Sylow 7 G) ∣ 15 := by
        simpa [hG] using (Sylow.card_dvd_index (p := 7) (G := G))
      have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
        simpa using (Sylow.card_modEq_one (p := 7) (G := G))
      omega
    exact ⟨Classical.choice (Sylow.exists 7 G), by
      simpa using (Sylow.normal_of_card_eq_one (p := 7) (G := G) h7)⟩
  ·
    have h5 : Fintype.card (Sylow 5 G) = 1 := by
      have hdiv : Fintype.card (Sylow 5 G) ∣ 21 := by
        simpa [hG] using (Sylow.card_dvd_index (p := 5) (G := G))
      have hmod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
        simpa using (Sylow.card_modEq_one (p := 5) (G := G))
      omega
    exact ⟨Classical.choice (Sylow.exists 5 G), by
      simpa using (Sylow.normal_of_card_eq_one (p := 5) (G := G) h5)⟩
