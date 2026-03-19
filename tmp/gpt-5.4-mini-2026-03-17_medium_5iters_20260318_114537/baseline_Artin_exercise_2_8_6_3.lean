import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ⟨⟨z.1.1, by
            simpa [Subgroup.center] using
              (by
                intro g
                simpa using congrArg Prod.fst (z.2 (g, 1)))⟩,
         ⟨z.1.2, by
            simpa [Subgroup.center] using
              (by
                intro h
                simpa using congrArg Prod.snd (z.2 (1, h)))⟩⟩,
      invFun := fun p =>
        ⟨(p.1, p.2), by
          simpa [Subgroup.center] using
            (by
              intro q
              rcases q with ⟨g, h⟩
              ext
              · simpa using p.1.2 g
              · simpa using p.2.2 h)⟩,
      left_inv := by
        intro z
        ext <;> rfl,
      right_inv := by
        intro p
        ext <;> rfl,
      map_mul' := by
        intro a b
        ext <;> rfl }⟩
