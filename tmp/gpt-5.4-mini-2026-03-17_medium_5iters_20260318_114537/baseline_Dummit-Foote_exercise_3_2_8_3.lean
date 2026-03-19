import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  ext x
  constructor
  · intro hx
    let xH : H := ⟨x, hx.1⟩
    let xK : K := ⟨x, hx.2⟩
    have hpowH : (x : G) ^ Fintype.card H = 1 := by
      simpa using (pow_card_eq_one xH)
    have hpowK : (x : G) ^ Fintype.card K = 1 := by
      simpa using (pow_card_eq_one xK)
    have hordH : orderOf (x : G) ∣ Fintype.card H :=
      orderOf_dvd_of_pow_eq_one hpowH
    have hordK : orderOf (x : G) ∣ Fintype.card K :=
      orderOf_dvd_of_pow_eq_one hpowK
    have hdiv : orderOf (x : G) ∣ 1 := by
      simpa [hHK.gcd_eq_one] using (Nat.dvd_gcd hordH hordK)
    have horder : orderOf (x : G) = 1 := Nat.dvd_one.mp hdiv
    have hx1 : x = 1 := by
      simpa using (orderOf_eq_one_iff.mp horder)
    simpa [hx1] using (show (1 : G) ∈ H ⊓ K from ⟨H.one_mem, K.one_mem⟩)
  · intro hx
    subst hx
    exact ⟨H.one_mem, K.one_mem⟩
