import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_17 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 105) :
  (∃ (P : Sylow 5 G), P.Normal) ∧ (∃ (P : Sylow 7 G), P.Normal) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  constructor
  ·
    have hcard5 : Fintype.card (Sylow 5 G) = 1 := by
      let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
      have hPcard : Fintype.card (P : Type) = 5 := by
        simpa [hG] using P.card
      have hindex : (P : Subgroup G).index = 21 := by
        have hmul := (P : Subgroup G).card_mul_index
        omega
      have hdiv : Fintype.card (Sylow 5 G) ∣ 21 := by
        simpa [hindex] using (Sylow.card_dvd_index (p := 5) (G := G) (P := P))
      have hmod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 5))
      omega
    let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
    have hnormIdx : (P : Subgroup G).normalizer.index = 1 := by
      simpa [hcard5] using (Sylow.card_eq_index_normalizer (P := P))
    have hnormalizer : (P : Subgroup G).normalizer = ⊤ := by
      exact Subgroup.index_eq_one.mp hnormIdx
    refine ⟨P, ?_⟩
    simpa using hnormalizer
  ·
    have hcard7 : Fintype.card (Sylow 7 G) = 1 := by
      let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
      have hPcard : Fintype.card (P : Type) = 7 := by
        simpa [hG] using P.card
      have hindex : (P : Subgroup G).index = 15 := by
        have hmul := (P : Subgroup G).card_mul_index
        omega
      have hdiv : Fintype.card (Sylow 7 G) ∣ 15 := by
        simpa [hindex] using (Sylow.card_dvd_index (p := 7) (G := G) (P := P))
      have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 7))
      omega
    let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
    have hnormIdx : (P : Subgroup G).normalizer.index = 1 := by
      simpa [hcard7] using (Sylow.card_eq_index_normalizer (P := P))
    have hnormalizer : (P : Subgroup G).normalizer = ⊤ := by
      exact Subgroup.index_eq_one.mp hnormIdx
    refine ⟨P, ?_⟩
    simpa using hnormalizer
