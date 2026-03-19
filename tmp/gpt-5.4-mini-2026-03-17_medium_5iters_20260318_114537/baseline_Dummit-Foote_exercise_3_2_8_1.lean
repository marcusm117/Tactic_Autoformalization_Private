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
    have hH : orderOf xH = orderOf (x : G) := by
      simpa using
        (MonoidHom.map_orderOf_of_injective (H.subtype) Subtype.val_injective xH).symm
    have hK : orderOf xK = orderOf (x : G) := by
      simpa using
        (MonoidHom.map_orderOf_of_injective (K.subtype) Subtype.val_injective xK).symm
    have hEq : orderOf xH = orderOf xK := by
      calc
        orderOf xH = orderOf (x : G) := hH
        _ = orderOf xK := hK.symm
    have h1 : orderOf xH ∣ Fintype.card H := orderOf_dvd_card_univ xH
    have h2 : orderOf xH ∣ Fintype.card K := by
      simpa [hEq] using (orderOf_dvd_card_univ xK)
    have hdiv : orderOf xH ∣ 1 := by
      simpa [hHK.gcd_eq_one] using (Nat.dvd_gcd h1 h2)
    have hle : orderOf xH ≤ 1 := Nat.le_of_dvd (by decide) hdiv
    have hpos : 0 < orderOf xH := by
      apply Nat.pos_of_ne_zero
      intro h0
      have hcard0 : Fintype.card H = 0 := by
        simpa [h0] using h1
      exact (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1, by simp⟩)) hcard0
    have hord : orderOf xH = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hpos)
    have hx1 : xH = 1 := (orderOf_eq_one_iff.mp hord)
    have hxG : x = 1 := by
      simpa using congrArg Subtype.val hx1
    simpa [Subgroup.mem_bot] using hxG
  · intro hx
    simpa [Subgroup.mem_bot] using hx
