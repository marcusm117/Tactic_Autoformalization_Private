import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Sylow p G} (H : Subgroup G) (hH : P ≤ H) :
  IsPGroup p (P.subgroupOf H) ∧
  ∀ (Q : Subgroup H), IsPGroup p Q → (P.subgroupOf H) ≤ Q → Q = (P.subgroupOf H) := by
  constructor
  · intro x
    rcases P.isPGroup' ⟨(x : G), x.2⟩ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change ((x : G) ^ p ^ k = 1)
    simpa using hk
  · intro Q hQ hPQ
    have hQmap : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hle : (P : Subgroup G) ≤ Q.map H.subtype := by
      intro x hx
      have hxH : (⟨x, hH hx⟩ : H) ∈ P.subgroupOf H := by
        simpa [Subgroup.subgroupOf] using hx
      exact ⟨⟨x, hH hx⟩, hPQ hxH, rfl⟩
    have hEq : (P : Subgroup G) = Q.map H.subtype := P.3 hQmap hle
    ext x
    constructor
    · intro hx
      have hxmap : (x : G) ∈ Q.map H.subtype := ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        simpa [hEq] using hxmap
      simpa [Subgroup.subgroupOf] using hxP
    · intro hx
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        simpa [Subgroup.subgroupOf] using hx
      have hxmap : (x : G) ∈ Q.map H.subtype := by
        simpa [hEq] using hxP
      simpa using hxmap
