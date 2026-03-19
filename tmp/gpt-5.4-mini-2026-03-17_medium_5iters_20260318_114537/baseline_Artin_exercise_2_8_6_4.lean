import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  refine ⟨
    { toFun := fun z =>
        ⟨⟨z.1.1, by
            have hz : ∀ g : G, g * z.1.1 = z.1.1 * g := by
              intro g
              simpa using congrArg Prod.fst (z.2 (g, 1))
            simpa [Subgroup.center] using hz⟩,
         ⟨z.1.2, by
            have hz : ∀ h : H, h * z.1.2 = z.1.2 * h := by
              intro h
              simpa using congrArg Prod.snd (z.2 (1, h))
            simpa [Subgroup.center] using hz⟩⟩,
      invFun := fun p =>
        ⟨(p.1, p.2), by
          have hp : ∀ q : G × H, q * (p.1, p.2) = (p.1, p.2) * q := by
            intro q
            rcases q with ⟨g, h⟩
            ext
            · simpa using p.1.2 g
            · simpa using p.2.2 h
          simpa [Subgroup.center] using hp⟩,
      left_inv := by
        intro z
        ext <;> rfl,
      right_inv := by
        intro p
        ext <;> rfl,
      map_mul' := by
        intro a b
        ext <;> rfl }⟩
