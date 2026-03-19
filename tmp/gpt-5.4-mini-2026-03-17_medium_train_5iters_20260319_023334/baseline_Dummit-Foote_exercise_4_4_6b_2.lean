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
        have ha' : a.1 = 1 := ha
        have hb' : b.1 = 1 := hb
        simp [ha', hb']
      inv_mem' := by
        intro a ha
        have ha' : a.1 = 1 := ha
        simp [ha'] }
  refine ⟨Multiplicative (ZMod 2) × Multiplicative (ZMod 2), inferInstance, H, ?_, ?_⟩
  · infer_instance
  · intro hchar
    let u : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)
    have hu : u ≠ 1 := by decide
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
    have hx : (1, u) ∈ H := by
      simp [H, u]
    have hEq := hchar φ
    have hmem : φ (1, u) ∈ H := by
      rw [← hEq]
      exact Subgroup.mem_map.mpr ⟨(1, u), hx, rfl⟩
    have hbad : u = 1 := by
      simpa [H, u, φ] using hmem
    exact hu hbad
