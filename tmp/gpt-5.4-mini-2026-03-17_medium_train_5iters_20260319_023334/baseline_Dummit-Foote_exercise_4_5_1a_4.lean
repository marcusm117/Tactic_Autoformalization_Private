import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Sylow p G} (H : Subgroup G) (hH : P ≤ H) :
  IsPGroup p (P.subgroupOf H) ∧
  ∀ (Q : Subgroup H), IsPGroup p Q → (P.subgroupOf H) ≤ Q → Q = (P.subgroupOf H) := by
  constructor
  · intro x
    rcases P.isPGroup' ⟨x.1, x.2⟩ with ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · intro Q hQ hPQ
    have hQmap : IsPGroup p (Q.map H.subtype) := hQ.map H.subtype
    have hle : (P : Subgroup G) ≤ Q.map H.subtype := by
      intro x hx
      exact ⟨⟨x, hH hx⟩, by simpa using hPQ (by simpa using hx), rfl⟩
    have hEq : Q.map H.subtype = (P : Subgroup G) := P.3 hQmap hle
    ext x
    constructor
    · intro hx
      have hxmap : (x : G) ∈ Q.map H.subtype := ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        rw [hEq] at hxmap
        exact hxmap
      simpa using hxP
    · intro hx
      have hxP : (x : G) ∈ (P : Subgroup G) := by
        simpa using hx
      have hxmap : (x : G) ∈ Q.map H.subtype := by
        rw [hEq]
        exact hxP
      exact by simpa using hxmap
