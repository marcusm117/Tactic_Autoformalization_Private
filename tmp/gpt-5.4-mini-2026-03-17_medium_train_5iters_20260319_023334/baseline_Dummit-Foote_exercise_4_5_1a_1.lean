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
    exact ⟨k, by simpa using hk⟩
  · intro Q hQ hPQ
    have hQmap : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hle : (P : Subgroup G) ≤ Q.map H.subtype := by
      intro x hx
      refine ⟨⟨x, hH hx⟩, ?_, rfl⟩
      exact hPQ ⟨⟨x, hH hx⟩, hx⟩
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
