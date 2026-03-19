import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_7 {G : Type*} [Group G] {H : Subgroup G} [Fintype H]
  (hH : ∀ (K : Subgroup G) (fK : Fintype K), card H = @card K fK → H = K) :
  H.Characteristic := by
  classical
  refine ⟨?_⟩
  intro e
  let e' : H ≃ Subgroup.comap e.toMonoidHom H :=
    { toFun := fun x => ⟨e.symm x, by
        simpa using x.2⟩
      invFun := fun y => ⟨e y, y.2⟩
      left_inv := by
        intro x
        ext
        simp
      right_inv := by
        intro y
        ext
        simp }
  letI : Fintype (Subgroup.comap e.toMonoidHom H) := Fintype.ofEquiv H e'
  have hcard : card H = card (Subgroup.comap e.toMonoidHom H) := by
    simpa using (Fintype.card_congr e')
  exact (hH (Subgroup.comap e.toMonoidHom H) inferInstance hcard).symm
