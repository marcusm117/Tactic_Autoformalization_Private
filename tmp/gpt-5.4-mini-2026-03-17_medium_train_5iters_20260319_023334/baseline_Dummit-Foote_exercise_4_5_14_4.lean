import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_14 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 312) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h13 : Nat.Prime 13 := by norm_num
  haveI : Fact (Nat.Prime 13) := ⟨h13⟩
  have hdiv13 : 13 ∣ card G := by
    rw [hG]
    norm_num
  have hdiv : Fintype.card (Sylow 13 G) ∣ 24 := by
    simpa [hG] using (card_sylow_dvd_card (G := G) (p := 13))
  have hmod : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa using (card_sylow_modEq_one (G := G) (p := 13))
  have hcount : Fintype.card (Sylow 13 G) = 1 := by
    have hle : Fintype.card (Sylow 13 G) ≤ 24 := Nat.le_of_dvd (by decide) hdiv
    interval_cases h : Fintype.card (Sylow 13 G) using hle
    all_goals
      norm_num at hmod
  have hsub : Subsingleton (Sylow 13 G) := by
    rw [Fintype.card_eq_one_iff]
    exact hcount
  haveI : Subsingleton (Sylow 13 G) := hsub
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 13 G))
  refine ⟨13, P, h13, hdiv13, ?_⟩
  change ∀ g : G, g • P = P
  intro g
  exact Subsingleton.elim _ _
