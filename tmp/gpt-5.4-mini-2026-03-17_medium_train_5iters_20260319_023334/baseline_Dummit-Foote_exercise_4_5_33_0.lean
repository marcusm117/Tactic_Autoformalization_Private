import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_33 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (P : Sylow p G) [hP : P.Normal] (H : Subgroup G) [Fintype H] :
  (∀ R : Sylow p H, R.toSubgroup = (H ⊓ P.toSubgroup).subgroupOf H) ∧
  Nonempty (Sylow p H) := by
  constructor
  · intro R
    have hRleP : R.toSubgroup.map H.subtype ≤ P.toSubgroup := by
      obtain ⟨Q, hQ⟩ := Sylow.exists_le (R.toSubgroup.map H.subtype)
      have hQeq : Q = P := P.eq_of_normal Q
      simpa [hQeq] using hQ
    have hle : R.toSubgroup ≤ (H ⊓ P.toSubgroup).subgroupOf H := by
      intro x hx
      exact ⟨hx, by simpa using hRleP ⟨x, hx⟩⟩
    haveI : IsPGroup p ((H ⊓ P.toSubgroup).subgroupOf H) := by infer_instance
    simpa using R.eq_of_le hle
  · exact inferInstance
