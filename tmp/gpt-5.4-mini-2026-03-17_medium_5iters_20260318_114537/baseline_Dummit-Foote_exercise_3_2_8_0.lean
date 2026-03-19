import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  have h1 : Fintype.card (H ⊓ K) ∣ Fintype.card H :=
    Subgroup.card_dvd_card (inf_le_left : H ⊓ K ≤ H)
  have h2 : Fintype.card (H ⊓ K) ∣ Fintype.card K :=
    Subgroup.card_dvd_card (inf_le_right : H ⊓ K ≤ K)
  have hd : Fintype.card (H ⊓ K) ∣ Nat.gcd (Fintype.card H) (Fintype.card K) :=
    Nat.dvd_gcd h1 h2
  have hd1 : Fintype.card (H ⊓ K) ∣ 1 := by
    simpa [hHK.gcd_eq_one] using hd
  have hle : Fintype.card (H ⊓ K) ≤ 1 := Nat.le_of_dvd (by decide) hd1
  have hpos : 0 < Fintype.card (H ⊓ K) := by
    exact Fintype.card_pos_iff.mpr ⟨1, by simp⟩
  have hcard : Fintype.card (H ⊓ K) = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)
  haveI : Subsingleton (H ⊓ K) := Fintype.card_eq_one_iff.mpr hcard
  ext x
  constructor
  · intro hx
    have hx1 : (⟨x, hx⟩ : H ⊓ K) = 1 := Subsingleton.elim _ _
    have hx' : x = 1 := congrArg Subtype.val hx1
    simpa [Subgroup.mem_bot] using hx'
  · intro hx
    have hx' : x = 1 := by simpa using hx
    simpa [hx']
