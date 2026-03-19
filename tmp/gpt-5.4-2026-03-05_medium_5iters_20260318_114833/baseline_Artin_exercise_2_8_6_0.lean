import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ( ⟨z.1.1, by
            intro g
            simpa [eq_comm] using congrArg Prod.fst (z.2 (g, 1))⟩,
          ⟨z.1.2, by
            intro h
            simpa [eq_comm] using congrArg Prod.snd (z.2 (1, h))⟩ )
      invFun := fun w =>
        ⟨(w.1, w.2), by
          intro gh
          rcases gh with ⟨g, h⟩
          exact Prod.ext
            (by simpa [eq_comm] using w.1.2 g)
            (by simpa [eq_comm] using w.2.2 h)⟩
      left_inv := by
        rintro ⟨⟨g, h⟩, hz⟩
        apply Subtype.ext
        rfl
      right_inv := by
        rintro ⟨a, b⟩
        ext <;> apply Subtype.ext <;> rfl
      map_mul' := by
        rintro ⟨⟨g, h⟩, hz⟩ ⟨⟨g', h'⟩, hz'⟩
        ext <;> apply Subtype.ext <;> rfl }⟩
