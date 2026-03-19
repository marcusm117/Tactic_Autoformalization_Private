import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Sylow p G} (H : Subgroup G) (hH : P ≤ H) :
  IsPGroup p (P.subgroupOf H) ∧
  ∀ (Q : Subgroup H), IsPGroup p Q → (P.subgroupOf H) ≤ Q → Q = (P.subgroupOf H) := by
  constructor
  · simpa using P.2.subgroupOf hH
  · intro Q hQ hPQ
    have hQmap : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hle : (P : Subgroup G) ≤ Q.map H.subtype := by
      intro x hx
      have hxPsub : (⟨x, hH hx⟩ : H) ∈ P.subgroupOf H := by
        simpa using hx
      exact ⟨⟨x, hH hx⟩, hPQ hxPsub, rfl⟩
    have hEq := P.3 hQmap hle
    ext x
    constructor
    · intro hx
      have hxmap : (x : G) ∈ Q.map H.subtype := by
        exact ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        simpa [hEq] using hxmap
      simpa using hxP
    · intro hx
      exact hPQ hx
