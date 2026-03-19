import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  constructor
  intro g x hx
  let φ : K ≃* K :=
  { toFun := fun y => ⟨g * (y : G) * g⁻¹, hK.conj_mem g y.property⟩
    invFun := fun y => ⟨g⁻¹ * (y : G) * g, hK.conj_mem g⁻¹ y.property⟩
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
    simpa using hHK1.map φ
  have hmem : φ ⟨x, hHK hx⟩ ∈ (H.subgroupOf K).map φ := by
    exact ⟨⟨x, hHK hx⟩, by simpa using hx, rfl⟩
  simpa [hmap] using hmem
