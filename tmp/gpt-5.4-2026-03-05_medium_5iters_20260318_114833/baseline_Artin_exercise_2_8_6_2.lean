import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ( ⟨z.1.1, by
            rw [Subgroup.mem_center_iff]
            intro g
            have hz := z.2
            rw [Subgroup.mem_center_iff] at hz
            simpa [eq_comm] using congrArg Prod.fst (hz (g, (1 : H)))⟩,
          ⟨z.1.2, by
            rw [Subgroup.mem_center_iff]
            intro h
            have hz := z.2
            rw [Subgroup.mem_center_iff] at hz
            simpa [eq_comm] using congrArg Prod.snd (hz ((1 : G), h))⟩ )
      invFun := fun w =>
        ⟨((w.1 : G), (w.2 : H)), by
          rw [Subgroup.mem_center_iff]
          have ha := w.1.2
          have hb := w.2.2
          rw [Subgroup.mem_center_iff] at ha hb
          rintro ⟨g, h⟩
          exact Prod.ext
            (by simpa [eq_comm] using ha g)
            (by simpa [eq_comm] using hb h)⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        rintro ⟨a, b⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
      map_mul' := by
        intro z z'
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl }⟩
