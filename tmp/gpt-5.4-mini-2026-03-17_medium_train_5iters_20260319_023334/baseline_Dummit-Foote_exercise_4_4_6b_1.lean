import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let H : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    { carrier := {x | x.1 = 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp [ha, hb]
      inv_mem' := by
        intro a ha
        simp [ha] }
  refine ⟨Multiplicative (ZMod 2) × Multiplicative (ZMod 2), inferInstance, H, ?_, ?_⟩
  · infer_instance
  · intro hchar
    let u : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
    let φ : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      { toFun := fun x => (x.2, x.1)
        invFun := fun x => (x.2, x.1)
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro x
          cases x
          rfl
        map_mul' := by
          intro a b
          cases a <;> cases b <;> rfl }
    have hu : u ≠ 1 := by decide
    have hx : ((1 : Multiplicative (ZMod 2)), u) ∈ H := by
      simp [H, u]
    have hnot : φ ((1 : Multiplicative (ZMod 2)), u) ∉ H := by
      simpa [H, u, φ] using hu
    have hEq : H.map φ.toMonoidHom = H := hchar φ
    have hmem : φ ((1 : Multiplicative (ZMod 2)), u) ∈ H.map φ.toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨((1 : Multiplicative (ZMod 2)), u), hx, rfl⟩
    have hmem' : φ ((1 : Multiplicative (ZMod 2)), u) ∈ H := by
      simpa [hEq] using hmem
    exact hnot hmem'
