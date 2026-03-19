import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  letI : Fintype ↥(H ⊓ K) :=
    Fintype.ofInjective
      (fun x : ↥(H ⊓ K) => (⟨x.1, x.2.1⟩ : H))
      (by
        intro a b hab
        exact Subtype.ext (congrArg Subtype.val hab))
  have hdivH : card ↥(H ⊓ K) ∣ card H :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdivK : card ↥(H ⊓ K) ∣ card K :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcard : card ↥(H ⊓ K) = 1 := by
    apply Nat.dvd_one.mp
    have hdvd : card ↥(H ⊓ K) ∣ Nat.gcd (card H) (card K) :=
      Nat.dvd_gcd hdivH hdivK
    simpa [hHK.gcd_eq_one] using hdvd
  have hs : Subsingleton ↥(H ⊓ K) := by
    apply (Fintype.card_le_one_iff_subsingleton).mp
    simpa [hcard]
  letI : Subsingleton ↥(H ⊓ K) := hs
  apply le_antisymm
  · intro x hx
    change x = 1
    let y : ↥(H ⊓ K) := ⟨x, hx⟩
    exact congrArg Subtype.val (Subsingleton.elim y (1 : ↥(H ⊓ K)))
  · exact bot_le
