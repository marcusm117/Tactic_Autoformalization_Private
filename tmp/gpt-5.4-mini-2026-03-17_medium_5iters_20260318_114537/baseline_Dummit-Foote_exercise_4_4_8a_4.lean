import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  constructor
  intro g hg x
  let φ : K ≃* K :=
  { toFun := fun y => ⟨x * (y : G) * x⁻¹, hK.conj_mem (y : G) y.property x⟩
    invFun := fun y => ⟨x⁻¹ * (y : G) * x, hK.conj_mem (y : G) y.property x⁻¹⟩
    left_inv := by
      intro y
      ext
      simp [mul_assoc]
    right_inv := by
      intro y
      ext
      simp [mul_assoc]
    map_mul' := by
      intro y z
      ext
      simp [mul_assoc] }
  have hmap : (H.subgroupOf K).map φ = H.subgroupOf K := by
    simpa using hHK1.1 φ
  have hmem : φ ⟨g, hHK hg⟩ ∈ (H.subgroupOf K).map φ := by
    exact ⟨⟨g, hHK hg⟩, by simpa using hg, rfl⟩
  simpa [hmap, φ] using hmem
