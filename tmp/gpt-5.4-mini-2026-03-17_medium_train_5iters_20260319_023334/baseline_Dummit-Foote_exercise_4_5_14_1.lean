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
  obtain ⟨P⟩ := Sylow.exists (G := G) (p := 13) hdiv13
  refine ⟨13, P, h13, hdiv13, ?_⟩
  have hdiv : Fintype.card (Sylow 13 G) ∣ 24 := by
    simpa [hG] using (Nat.card_sylow_dvd_card (G := G) (p := 13))
  have hmod : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa using (Nat.card_sylow_modEq_one (G := G) (p := 13))
  have hpos : 0 < Fintype.card (Sylow 13 G) := Fintype.card_pos_iff.mpr ⟨P⟩
  have hle : Fintype.card (Sylow 13 G) ≤ 24 := Nat.le_of_dvd (by norm_num) hdiv
  have hcount : Fintype.card (Sylow 13 G) = 1 := by
    interval_cases h : Fintype.card (Sylow 13 G) <;> norm_num at hmod hdiv
  exact Sylow.normal_of_card_eq_one hcount
