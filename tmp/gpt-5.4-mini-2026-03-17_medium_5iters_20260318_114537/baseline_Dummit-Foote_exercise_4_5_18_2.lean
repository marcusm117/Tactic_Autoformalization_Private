import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hm : multiplicity 5 (Nat.card G) = 2 := by
    rw [hG]
    native_decide
  have hdiv : Nat.card (Sylow 5 G) ∣ 8 := by
    simpa [hG, hm] using (Sylow.card_sylow_dvd_card (G := G) (p := 5))
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using (Sylow.card_sylow_modEq_card (G := G) (p := 5))
  have hcard : Nat.card (Sylow 5 G) = 1 := by
    have hle : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by decide) hdiv
    interval_cases n : Nat.card (Sylow 5 G)
    all_goals
      norm_num at hmod ⊢
      omega
  haveI : Subsingleton (Sylow 5 G) := Fintype.card_le_one_iff_subsingleton.mp (by simpa [hcard])
  refine ⟨Classical.choice (show Nonempty (Sylow 5 G) from inferInstance), ?_⟩
  exact Sylow.normal_of_subsingleton (p := 5) (G := G) _
