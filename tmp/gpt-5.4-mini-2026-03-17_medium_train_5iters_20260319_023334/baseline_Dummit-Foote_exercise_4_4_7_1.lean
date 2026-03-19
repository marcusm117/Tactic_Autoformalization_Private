import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_7 {G : Type*} [Group G] {H : Subgroup G} [Fintype H]
  (hH : ∀ (K : Subgroup G) (fK : Fintype K), card H = @card K fK → H = K) :
  H.Characteristic := by
  classical
  refine ⟨?_⟩
  intro e
  let e' : H ≃ H.map e.toMonoidHom :=
    { toFun := fun x => ⟨e x, ⟨x, x.2, rfl⟩⟩
      invFun := fun y => by
        rcases y.2 with ⟨x, hx, rfl⟩
        exact ⟨x, hx⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro y
        ext
        rcases y.2 with ⟨x, hx, rfl⟩
        simp }
  letI : Fintype (H.map e.toMonoidHom) := Fintype.ofEquiv H e'
  have hcard : card H = card (H.map e.toMonoidHom) := by
    simpa using (Fintype.card_congr e')
  exact (hH (H.map e.toMonoidHom) inferInstance hcard).symm
