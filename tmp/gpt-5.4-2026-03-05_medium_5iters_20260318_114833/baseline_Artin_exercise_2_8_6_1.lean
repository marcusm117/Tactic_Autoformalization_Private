import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ( ⟨z.1.1, by
            change ∀ g : G, g * z.1.1 = z.1.1 * g
            intro g
            simpa [eq_comm] using congrArg Prod.fst (z.2 (g, (1 : H)))⟩,
          ⟨z.1.2, by
            change ∀ h : H, h * z.1.2 = z.1.2 * h
            intro h
            simpa [eq_comm] using congrArg Prod.snd (z.2 ((1 : G), h))⟩ )
      invFun := fun w =>
        ⟨((w.1 : G), (w.2 : H)), by
          change ∀ gh : G × H, gh * ((w.1 : G), (w.2 : H)) = ((w.1 : G), (w.2 : H)) * gh
          rintro ⟨g, h⟩
          exact Prod.ext
            (by simpa [eq_comm] using w.1.2 g)
            (by simpa [eq_comm] using w.2.2 h)⟩
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
