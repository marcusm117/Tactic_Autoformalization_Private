import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  have h1 : Fintype.card (H ⊓ K) ∣ Fintype.card H := by
    rcases Subgroup.card_eq_card_quotient_mul_card (H := H) (K := H ⊓ K) inf_le_left with hEq
    refine ⟨Fintype.card (H ⧸ (H ⊓ K)), ?_⟩
    simpa [Nat.mul_comm] using hEq.symm
  have h2 : Fintype.card (H ⊓ K) ∣ Fintype.card K := by
    rcases Subgroup.card_eq_card_quotient_mul_card (H := K) (K := H ⊓ K) inf_le_right with hEq
    refine ⟨Fintype.card (K ⧸ (H ⊓ K)), ?_⟩
    simpa [Nat.mul_comm] using hEq.symm
  have hdiv : Fintype.card (H ⊓ K) ∣ 1 := by
    simpa [hHK.gcd_eq_one] using Nat.dvd_gcd h1 h2
  have hcard : Fintype.card (H ⊓ K) = 1 := Nat.dvd_one.mp hdiv
  haveI : Subsingleton (H ⊓ K) := Fintype.card_eq_one_iff.mpr hcard
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hx⟩ : H ⊓ K) = 1 := Subsingleton.elim _ _
    have hx'' : x = 1 := by
      simpa using congrArg Subtype.val hx'
    simpa [Subgroup.mem_bot] using hx''
  · intro hx
    simpa [Subgroup.mem_bot, hx]
