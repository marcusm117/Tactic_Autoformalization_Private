import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let p : (Multiplicative (Fin 2) × Multiplicative (Fin 2)) →* Multiplicative (Fin 2) :=
    { toFun := fun x => x.1
      map_one' := rfl
      map_mul' := by
        intro a b
        rfl }
  let H : Subgroup (Multiplicative (Fin 2) × Multiplicative (Fin 2)) := p.ker
  refine ⟨(Multiplicative (Fin 2) × Multiplicative (Fin 2)), inferInstance, H, ?_, ?_⟩
  · infer_instance
  · intro hchar
    let u : Multiplicative (Fin 2) := Multiplicative.ofAdd (1 : Fin 2)
    have hu : u ≠ 1 := by decide
    let φ : (Multiplicative (Fin 2) × Multiplicative (Fin 2)) ≃* (Multiplicative (Fin 2) × Multiplicative (Fin 2)) :=
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
      simp [H, p, u]
    have hEq : H.map φ.toMonoidHom = H := hchar φ
    have hmem : φ (1, u) ∈ H.map φ.toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨(1, u), hx, rfl⟩
    have hmem' : φ (1, u) ∈ H := by
      simpa [hEq] using hmem
    have hnot : φ (1, u) ∉ H := by
      intro h
      have : u = 1 := by
        simpa [H, p, φ, u] using h
      exact hu this
    exact hnot hmem'
