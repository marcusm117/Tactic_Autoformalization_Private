import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  refine ⟨?_⟩
  intro n hn g
  let φ : K ≃* K :=
    { toFun := fun k => ⟨g * (k : G) * g⁻¹, hK.1 (k : G) k.2 g⟩
      invFun := fun k => ⟨g⁻¹ * (k : G) * g, by
        simpa using hK.1 (k : G) k.2 g⁻¹⟩
      left_inv := by
        intro k
        ext
        simp [mul_assoc]
      right_inv := by
        intro k
        ext
        simp [mul_assoc]
      map_mul' := by
        intro a b
        ext
        simp [mul_assoc] }
  have hφ : Subgroup.comap φ.toMonoidHom (H.subgroupOf K) = H.subgroupOf K :=
    Characteristic.fixed hHK1 φ
  have hx : (⟨n, hHK hn⟩ : K) ∈ H.subgroupOf K := by
    simpa using hn
  rw [← hφ] at hx
  simpa [φ] using hx
