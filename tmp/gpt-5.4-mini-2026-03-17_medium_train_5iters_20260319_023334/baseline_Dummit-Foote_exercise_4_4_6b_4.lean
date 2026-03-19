import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let G := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)
  let H : Subgroup G := (MonoidHom.snd : G →* Equiv.Perm (Fin 2)).ker
  refine ⟨G, inferInstance, H, ?_, ?_⟩
  · infer_instance
  · intro hchar
    let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hσ : σ ≠ 1 := by
      intro h
      have h' := congrArg (fun f : Equiv.Perm (Fin 2) => f 0) h
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      exact h10 (by simpa [σ] using h')
    let φ : G ≃* G :=
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
    have hx : (σ, 1) ∈ H := by
      simp [H, σ]
    have hEq : H.map φ.toMonoidHom = H := hchar φ
    have hmem : φ (σ, 1) ∈ H.map φ.toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨(σ, 1), hx, rfl⟩
    have hmem' : φ (σ, 1) ∈ H := by
      simpa [hEq] using hmem
    have hnot : φ (σ, 1) ∉ H := by
      simp [H, φ, σ, hσ]
    exact hnot hmem'
