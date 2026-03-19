import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  let H : Subgroup G :=
    { carrier := {x | x.1 = 0}
      one_mem' := by simp [G]
      mul_mem' := by
        intro a b ha hb
        simp [G, ha, hb]
      inv_mem' := by
        intro a ha
        simp [G, ha] }
  refine ⟨G, inferInstance, H, ?_, ?_⟩
  · exact Subgroup.normalOfCommGroup H
  · intro hchar
    let φ : G ≃* G := MulEquiv.prodComm _ _
    have hφ : H.map φ.toMonoidHom = H := hchar φ
    let x : G := ((0 : ZMod 2), (1 : ZMod 2))
    have hx : x ∈ H := by
      simp [H, x]
    have hmem : φ.toMonoidHom x ∈ H.map φ.toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hmem' : φ.toMonoidHom x ∈ H := by
      simpa [hφ] using hmem
    have hbad : (1 : ZMod 2) = 0 := by
      simpa [H, x, φ] using hmem'
    exact (by decide : (1 : ZMod 2) ≠ 0) hbad
