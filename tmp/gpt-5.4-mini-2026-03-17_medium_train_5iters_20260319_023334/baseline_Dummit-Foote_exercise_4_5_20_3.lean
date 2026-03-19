import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  classical
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hmod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa using (Nat.card_sylow_modEq_one (G := G) (p := 13))
  let P : Sylow 13 G := Classical.choice (show Nonempty (Sylow 13 G) from inferInstance)
  have hdiv : Nat.card (Sylow 13 G) ∣ 105 := by
    simpa [hG, P.card] using (Nat.card_sylow_dvd_card_subgroup (G := G) (p := 13) P)
  have huniq : Nat.card (Sylow 13 G) = 1 := by
    rcases hmod with ⟨k, hk⟩
    rcases hdiv with ⟨m, hm⟩
    omega
  have hPnormal : (P : Subgroup G).Normal := by
    exact Sylow.normal_of_card_eq_one huniq
  have hPcard : Fintype.card (P : Subgroup G) = 13 := by
    simpa [hG] using P.card
  have hnotbot : (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    have : (13 : ℕ) = 1 := by
      simpa [hbot] using hPcard
    omega
  have hnottop : (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have : (13 : ℕ) = 1365 := by
      simpa [htop, hG] using hPcard
    omega
  rcases hsimple.eq_bot_or_eq_top (P : Subgroup G) hPnormal with hbot | htop
  · exact hnotbot hbot
  · exact hnottop htop
