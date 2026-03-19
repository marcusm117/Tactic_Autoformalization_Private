import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_14 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 312) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h13 : Nat.Prime 13 := by norm_num
  haveI : Fact (Nat.Prime 13) := ⟨h13⟩
  let P : Sylow 13 G := Classical.choice (show Nonempty (Sylow 13 G) from inferInstance)
  have hdiv : Fintype.card (Sylow 13 G) ∣ 24 := by
    simpa [hG] using (Nat.card_sylow_dvd_card (G := G) (p := 13))
  have hmod : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa using (Nat.card_sylow_modEq_one (G := G) (p := 13))
  have hcount : Fintype.card (Sylow 13 G) = 1 := by
    let n := Fintype.card (Sylow 13 G)
    have hdiv' : n ∣ 24 := by simpa [n] using hdiv
    have hmod' : n ≡ 1 [MOD 13] := by simpa [n] using hmod
    have hle : n ≤ 24 := by
      rcases hdiv' with ⟨k, hk⟩
      omega
    have hn : n = 1 := by
      interval_cases n using hle <;> norm_num at hmod' hdiv'
    simpa [n] using hn
  refine ⟨13, P, h13, by norm_num [hG], ?_⟩
  exact Sylow.normal_of_card_eq_one hcount
