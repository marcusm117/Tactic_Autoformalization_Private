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
    have hcard : Fintype.card (Sylow 5 G) = 1 := by
      have hdiv : Fintype.card (Sylow 5 G) ∣ 21 := by
        simpa [hG] using (Sylow.card_dvd_index (p := 5) (G := G))
      have hmod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 5))
      omega
    let P : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
    refine ⟨P, ?_⟩
    exact (Sylow.card_eq_one_iff_normal (P := P)).mp hcard
  ·
    have hcard : Fintype.card (Sylow 7 G) = 1 := by
      have hdiv : Fintype.card (Sylow 7 G) ∣ 15 := by
        simpa [hG] using (Sylow.card_dvd_index (p := 7) (G := G))
      have hmod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
        simpa using (card_sylow_modEq_one (G := G) (p := 7))
      omega
    let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
    refine ⟨P, ?_⟩
    exact (Sylow.card_eq_one_iff_normal (P := P)).mp hcard
