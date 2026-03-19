import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hdiv : Nat.card (Sylow 5 G) ∣ 8 := by
    have hm : multiplicity 5 (Nat.card G) = 2 := by
      norm_num [hG]
    simpa [hG, hm] using (Nat.card_sylow_dvd_card (G := G) (p := 5))
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using (Nat.card_sylow_modEq_card (G := G) (p := 5))
  have hcard : Nat.card (Sylow 5 G) = 1 := by
    have hle : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by decide) hdiv
    interval_cases n : Nat.card (Sylow 5 G) using hle
    all_goals
      simp at hmod
      omega
  haveI : Subsingleton (Sylow 5 G) := by
    exact Fintype.card_le_one_iff_subsingleton.mp (by simpa [hcard])
  let N : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
  exact ⟨N, by simpa using (Sylow.normal_of_subsingleton (p := 5) (G := G) N)⟩
