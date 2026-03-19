import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_33 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (P : Sylow p G) [hP : P.Normal] (H : Subgroup G) [Fintype H] :
  (∀ R : Sylow p H, R.toSubgroup = (H ⊓ P.toSubgroup).subgroupOf H) ∧
  Nonempty (Sylow p H) := by
  classical
  constructor
  · intro R
    let Q : Subgroup H := (H ⊓ P.toSubgroup).subgroupOf H
    have hRmap : IsPGroup p (R.toSubgroup.map H.subtype) := by
      intro x
      rcases x with ⟨y, hy, rfl⟩
      rcases R.2 y with ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    rcases IsPGroup.exists_le hRmap with ⟨S, hS⟩
    have hSeq : S = P := P.eq_of_normal S
    have hRleP : R.toSubgroup ≤ P.toSubgroup := by
      intro x hx
      have hxmap : H.subtype x ∈ R.toSubgroup.map H.subtype := ⟨x, hx, rfl⟩
      simpa [hSeq] using hS hxmap
    have hRleQ : R.toSubgroup ≤ Q := by
      intro x hx
      exact ⟨hx, hRleP hx⟩
    have hQp : IsPGroup p Q := by
      intro x
      rcases P.2 ⟨x, x.2⟩ with ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    have hQleR : Q ≤ R.toSubgroup := by
      exact (R.3 hQp hRleQ).le
    exact le_antisymm hRleQ hQleR
  · exact inferInstance
