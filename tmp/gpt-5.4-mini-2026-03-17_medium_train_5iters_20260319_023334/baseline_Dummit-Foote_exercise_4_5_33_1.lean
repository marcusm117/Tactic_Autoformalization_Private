import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_33 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (P : Sylow p G) [hP : P.Normal] (H : Subgroup G) [Fintype H] :
  (∀ R : Sylow p H, R.toSubgroup = (H ⊓ P.toSubgroup).subgroupOf H) ∧
  Nonempty (Sylow p H) := by
  constructor
  · intro R
    have hR : IsPGroup p R.toSubgroup := by infer_instance
    obtain ⟨Q, hQ⟩ := hR.exists_le
    have hQeq : Q = P := P.eq_of_normal Q
    have hRleP : R.toSubgroup ≤ P.toSubgroup := by
      simpa [hQeq] using hQ
    have hRleI : R.toSubgroup ≤ (H ⊓ P.toSubgroup).subgroupOf H := by
      intro x hx
      simp [Subgroup.mem_subgroupOf, hx, hRleP hx]
    have hIleR : (H ⊓ P.toSubgroup).subgroupOf H ≤ R.toSubgroup := by
      haveI : Normal ((H ⊓ P.toSubgroup).subgroupOf H) := by infer_instance
      haveI : IsPGroup p ((H ⊓ P.toSubgroup).subgroupOf H) := by infer_instance
      exact R.normal_le
    exact le_antisymm hRleI hIleR
  · exact ⟨(H ⊓ P.toSubgroup).subgroupOf H, inferInstance⟩
