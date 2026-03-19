import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ⟨⟨z.1.1, by
            change ∀ g : G, g * z.1.1 = z.1.1 * g
            intro g
            simpa using congrArg Prod.fst (z.2 (g, 1))⟩,
         ⟨z.1.2, by
            change ∀ h : H, h * z.1.2 = z.1.2 * h
            intro h
            simpa using congrArg Prod.snd (z.2 (1, h))⟩⟩,
      invFun := fun p =>
        ⟨(p.1.1, p.2.1), by
          change ∀ q : G × H, q * (p.1.1, p.2.1) = (p.1.1, p.2.1) * q
          intro q
          rcases q with ⟨g, h⟩
          ext <;> exacts [p.1.2 g, p.2.2 h]⟩,
      left_inv := by
        intro z
        ext <;> rfl,
      right_inv := by
        intro p
        ext <;> rfl,
      map_mul' := by
        intro a b
        ext <;> rfl }⟩
