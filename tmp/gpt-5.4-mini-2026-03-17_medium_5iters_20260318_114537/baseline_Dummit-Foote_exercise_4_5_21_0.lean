import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h19 : Nat.Prime 19 := by decide
  let P : Sylow 3 G := Classical.choice inferInstance
  have hPcard : P.card = 9 := by
    simpa [hG] using P.card_eq_card
  have hPnontriv : (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    have : P.card = 1 := by simpa [hbot] using hPcard
    norm_num at this
  have hdiv : Nat.card (Sylow 3 G) ∣ 323 := by
    simpa [hG] using (Nat.card_sylow_dvd_card_sub_one (G := G) (p := 3))
  have hmod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := by
    simpa using (Nat.card_sylow_modEq_one (G := G) (p := 3))
  have hmem : Nat.card (Sylow 3 G) ∈ Nat.divisors 323 := by
    exact Nat.mem_divisors.mpr hdiv
  norm_num at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · have hnorm : (P : Subgroup G).Normal := by
      simpa using (P.normal_of_card_eq_one (by simp))
    have hsplit := hs (P : Subgroup G) hnorm
    rcases hsplit with hbot | htop
    · exact hPnontriv hbot
    · have hcardtop : P.card = 2907 := by
        simpa [htop, hG] using hPcard
      omega
  · have hfalse : False := by
      norm_num at hmod
      exact hmod
    exact hfalse.elim
  · have hindex : (P.normalizer : Subgroup G).index = 19 := by
      simpa using P.card_eq_index_normalizer
    have hnorm : (P.normalizer : Subgroup G).Normal := by
      exact Subgroup.normal_of_index_eq_prime h19 hindex
    have hsplit := hs (P.normalizer : Subgroup G) hnorm
    rcases hsplit with hbot | htop
    · have hPbot : (P : Subgroup G) = ⊥ := by
        apply le_bot_iff.mp
        simpa [hbot] using P.le_normalizer
      exact hPnontriv hPbot
    · have hindex1 : (P.normalizer : Subgroup G).index = 1 := by simpa [htop]
      omega
  · have hfalse : False := by
      norm_num at hmod
      exact hmod
    exact hfalse.elim
