import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  let S := {x : G // x ∈ H ∧ x ∈ K}
  haveI : Finite S :=
    Finite.ofInjective
      (fun x : S => (⟨x.1, x.2.1⟩ : H))
      (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : H => (z : G)) hab)
  have hHK' : Nat.Coprime (Nat.card H) (Nat.card K) := by
    simpa [Nat.card_eq_fintype_card] using hHK
  have hdivH : Nat.card S ∣ Nat.card H := by
    simpa [S] using
      (Subgroup.card_dvd_of_le (H := H ⊓ K) (K := H) inf_le_left)
  have hdivK : Nat.card S ∣ Nat.card K := by
    simpa [S] using
      (Subgroup.card_dvd_of_le (H := H ⊓ K) (K := K) inf_le_right)
  have hcardS : Nat.card S = 1 := by
    apply Nat.dvd_one.mp
    have hdvd : Nat.card S ∣ Nat.gcd (Nat.card H) (Nat.card K) :=
      Nat.dvd_gcd hdivH hdivK
    simpa [hHK'.gcd_eq_one] using hdvd
  have hs : Subsingleton S :=
    (Nat.card_le_one_iff_subsingleton.mp <| by simpa [hcardS])
  apply le_antisymm
  · intro x hx
    change x = 1
    exact congrArg Subtype.val <|
      hs.elim (⟨x, hx⟩ : S) (⟨1, by constructor <;> simp⟩ : S)
  · exact bot_le
