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
    let S : Subgroup G := R.toSubgroup.map H.subtype
    have hS : IsPGroup p S := by
      intro x
      rcases x.2 with ⟨y, hy, rfl⟩
      rcases R.2 ⟨y, hy⟩ with ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    haveI : IsPGroup p S := hS
    obtain ⟨T, hT⟩ := S.exists_le_sylow
    have hTeq : T = P := by
      simpa using hP.eq_of_normal T
    have hRleP : R.toSubgroup ≤ P.toSubgroup := by
      intro x hx
      have hxS : (x : G) ∈ S := ⟨x, hx, rfl⟩
      simpa [S, hTeq] using hT hxS
    let Q : Subgroup H := (H ⊓ P.toSubgroup).subgroupOf H
    have hRleQ : R.toSubgroup ≤ Q := by
      intro x hx
      exact ⟨x.2, hRleP hx⟩
    have hQp : IsPGroup p Q := by
      intro x
      have hxP : (x : G) ∈ P.toSubgroup := by
        have hxQ : (x : G) ∈ H ⊓ P.toSubgroup := by
          simpa [Q, Subgroup.mem_subgroupOf] using x.2
        exact hxQ.2
      rcases P.2 ⟨x, hxP⟩ with ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    simpa [Q] using (R.3 hQp hRleQ)
  · exact inferInstance
