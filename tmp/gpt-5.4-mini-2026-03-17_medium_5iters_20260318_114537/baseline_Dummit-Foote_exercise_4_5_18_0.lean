import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_18 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 200) :
  ∃ N : Sylow 5 G, N.Normal := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨N⟩ := Sylow.exists_subgroup (p := 5) G
  have hdiv0 := Nat.card_sylow_dvd_card (G := G) (p := 5)
  have hcalc : Nat.card G / 5 ^ multiplicity 5 (Nat.card G) = 8 := by
    norm_num [hG]
  have hdiv : Nat.card (Sylow 5 G) ∣ 8 := by
    simpa [hcalc, hG] using hdiv0
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    simpa using (Nat.card_sylow_modEq_card (G := G) (p := 5))
  have hcard : Nat.card (Sylow 5 G) = 1 := by
    have hle : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by decide) hdiv
    interval_cases n : Nat.card (Sylow 5 G) using hle <;> (simp at hmod; try contradiction; rfl)
  have hsub : Subsingleton (Sylow 5 G) := by
    exact Fintype.card_le_one_iff_subsingleton.mp (by simpa [hcard])
  letI : Subsingleton (Sylow 5 G) := hsub
  exact ⟨N, Sylow.normal_of_subsingleton (p := 5) (G := G) N⟩
