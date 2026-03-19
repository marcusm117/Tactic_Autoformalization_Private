import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  intro hS
  haveI17 : Fact (Nat.Prime 17) := ⟨by decide⟩
  haveI19 : Fact (Nat.Prime 19) := ⟨by decide⟩
  have h17div : Nat.card (Sylow 17 G) ∣ 171 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card_sub_one (G := G) (p := 17))
  have h17mod : Nat.card (Sylow 17 G) ≡ 1 [MOD 17] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 17))
  have h19div : Nat.card (Sylow 19 G) ∣ 153 := by
    simpa [hG] using (Sylow.card_sylow_dvd_card_sub_one (G := G) (p := 19))
  have h19mod : Nat.card (Sylow 19 G) ≡ 1 [MOD 19] := by
    simpa using (Sylow.card_sylow_modEq_one (G := G) (p := 19))
  have h17cases : Nat.card (Sylow 17 G) = 1 ∨ Nat.card (Sylow 17 G) = 171 := by
    have hmem : Nat.card (Sylow 17 G) ∈ Nat.divisors 171 := by
      exact Nat.mem_divisors.mpr ⟨h17div, by decide⟩
    norm_num at hmem h17mod
  have h19cases : Nat.card (Sylow 19 G) = 1 ∨ Nat.card (Sylow 19 G) = 153 := by
    have hmem : Nat.card (Sylow 19 G) ∈ Nat.divisors 153 := by
      exact Nat.mem_divisors.mpr ⟨h19div, by decide⟩
    norm_num at hmem h19mod
  have h17ne1 : Nat.card (Sylow 17 G) ≠ 1 := by
    intro h1
    have hPnorm : (Classical.choice (Sylow 17 G) : Subgroup G).Normal := by
      simpa [h1] using (Sylow.normal_of_card_eq_one (G := G) (p := 17))
    rcases hS.eq_bot_or_eq_top (Classical.choice (Sylow 17 G) : Subgroup G) hPnorm with hbot | htop
    · have hcard : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 1 := by
        simpa [hbot] using (Classical.choice (Sylow 17 G)).card_eq
      have hnontriv : (Classical.choice (Sylow 17 G) : Type*) ≠ Subsingleton.elim _ _ := by
        simpa [hcard] using (Classical.choice (Sylow 17 G)).nontrivial
      exact hnontriv rfl
    · have hcard : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 2907 := by
        simpa [htop, hG] using (Classical.choice (Sylow 17 G)).card_eq
      omega
  have h19ne1 : Nat.card (Sylow 19 G) ≠ 1 := by
    intro h1
    have hPnorm : (Classical.choice (Sylow 19 G) : Subgroup G).Normal := by
      simpa [h1] using (Sylow.normal_of_card_eq_one (G := G) (p := 19))
    rcases hS.eq_bot_or_eq_top (Classical.choice (Sylow 19 G) : Subgroup G) hPnorm with hbot | htop
    · have hcard : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 1 := by
        simpa [hbot] using (Classical.choice (Sylow 19 G)).card_eq
      have hnontriv : (Classical.choice (Sylow 19 G) : Type*) ≠ Subsingleton.elim _ _ := by
        simpa [hcard] using (Classical.choice (Sylow 19 G)).nontrivial
      exact hnontriv rfl
    · have hcard : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 2907 := by
        simpa [htop, hG] using (Classical.choice (Sylow 19 G)).card_eq
      omega
  have h17max : Nat.card (Sylow 17 G) = 171 := by
    rcases h17cases with rfl | h
    · contradiction
    · exact h
  have h19max : Nat.card (Sylow 19 G) = 153 := by
    rcases h19cases with rfl | h
    · contradiction
    · exact h
  have h17card : Fintype.card (Classical.choice (Sylow 17 G) : Type*) = 17 := by
    simpa [hG] using (Classical.choice (Sylow 17 G)).card_eq
  have h19card : Fintype.card (Classical.choice (Sylow 19 G) : Type*) = 19 := by
    simpa [hG] using (Classical.choice (Sylow 19 G)).card_eq
  have hcount17 : 171 * 16 ≤ 2906 := by
    have : 171 * 16 + 153 * 18 + 1 ≤ 2907 := by
      omega
    omega
  have hcount19 : 153 * 18 ≤ 2906 := by omega
  omega
