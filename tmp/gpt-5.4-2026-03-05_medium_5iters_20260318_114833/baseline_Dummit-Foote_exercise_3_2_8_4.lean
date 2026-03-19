import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  classical
  let e : ↥(H ⊓ K) ≃ { h : H // ((h : G) ∈ K) } :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl }
  letI : Fintype ↥(H ⊓ K) := Fintype.ofEquiv { h : H // ((h : G) ∈ K) } e.symm
  have hHK' : Nat.Coprime (Nat.card H) (Nat.card K) := by
    simpa [Nat.card_eq_fintype_card] using hHK
  have hdivH : Nat.card ↥(H ⊓ K) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdivK : Nat.card ↥(H ⊓ K) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcard : Nat.card ↥(H ⊓ K) = 1 := by
    apply Nat.dvd_one.mp
    have hdvd : Nat.card ↥(H ⊓ K) ∣ Nat.gcd (Nat.card H) (Nat.card K) :=
      Nat.dvd_gcd hdivH hdivK
    simpa [hHK'.gcd_eq_one] using hdvd
  have hcard' : Fintype.card ↥(H ⊓ K) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hle : Fintype.card ↥(H ⊓ K) ≤ 1 := by
    simpa [hcard'] using (show (1 : Nat) ≤ 1 by decide)
  have hs : Subsingleton ↥(H ⊓ K) :=
    (Fintype.card_le_one_iff_subsingleton.mp hle)
  apply le_antisymm
  · intro x hx
    change x = 1
    exact congrArg Subtype.val (hs.elim ⟨x, hx⟩ 1)
  · exact bot_le
