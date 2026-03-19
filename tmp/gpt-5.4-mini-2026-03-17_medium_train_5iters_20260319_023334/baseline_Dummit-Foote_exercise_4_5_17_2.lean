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
      have hdiv : Fintype.card (Sylow 5 G) ∣ 21 := by
        let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
        have hPcard : Fintype.card (P : Subgroup G) = 5 := by
          simpa [hG] using (P.2.card)
        have hindex : (P : Subgroup G).index = 21 := by
          have h := (P : Subgroup G).card_mul_index
          omega
        simpa [hindex] using (Sylow.card_dvd_index (p := 5) (G := G) (P := P))
      have hmod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 5))
      omega
    let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
    exact ⟨P, (card_eq_one_iff_normal (P := P)).mp hcard5⟩
  ·
    have hcard7 : Fintype.card (Sylow 7 G) = 1 := by
      have hdiv : Fintype.card (Sylow 7 G) ∣ 15 := by
        let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
        have hPcard : Fintype.card (P : Subgroup G) = 7 := by
          simpa [hG] using (P.2.card)
        have hindex : (P : Subgroup G).index = 15 := by
          have h := (P : Subgroup G).card_mul_index
          omega
        simpa [hindex] using (Sylow.card_dvd_index (p := 7) (G := G) (P := P))
      have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 7))
      omega
    let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
    exact ⟨P, (card_eq_one_iff_normal (P := P)).mp hcard7⟩
