import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_4_8a {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : H ≤ K) [hHK1 : (H.subgroupOf K).Characteristic] [hK : K.Normal] :
  H.Normal := by
  constructor
  intro g x hx
  have hmap : (H.subgroupOf K).map (hK.conj g) = H.subgroupOf K :=
    hHK1.map_eq (hK.conj g)
  have hmem : (hK.conj g) ⟨x, hHK hx⟩ ∈ (H.subgroupOf K).map (hK.conj g) := by
    exact ⟨⟨x, hHK hx⟩, by simpa using hx, rfl⟩
  simpa [hmap] using hmem
