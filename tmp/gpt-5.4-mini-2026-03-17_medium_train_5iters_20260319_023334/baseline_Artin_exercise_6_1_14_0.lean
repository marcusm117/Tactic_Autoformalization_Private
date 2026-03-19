import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_1_14 (G : Type*) [Group G]
  (hG : IsCyclic $ G ⧸ (center G)) :
  center G = ⊤  := by
  classical
  rcases hG.exists_generator with ⟨q, hq⟩
  rcases Quotient.exists_rep q with ⟨a, rfl⟩
  have hdecomp : ∀ x : G, ∃ n : ℤ, ∃ z ∈ center G, x = a ^ n * z := by
    intro x
    have hx : QuotientGroup.mk x ∈ Subgroup.closure ({QuotientGroup.mk a} : Set (G ⧸ center G)) := by
      rw [hq]
      trivial
    rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
    have hxq : QuotientGroup.mk x = QuotientGroup.mk (a ^ n) := by
      simpa using hn
    refine ⟨n, (a ^ n)⁻¹ * x, QuotientGroup.eq.mp hxq, ?_⟩
    simp [mul_assoc]
  refine le_antisymm le_top ?_
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  rcases hdecomp x with ⟨m, zx, hzx, rfl⟩
  rcases hdecomp y with ⟨n, zy, hzy, rfl⟩
  have hzxa : zx * a ^ n = a ^ n * zx := by
    simpa using (Subgroup.mem_center_iff.mp hzx) (a ^ n)
  have hzya : zy * a ^ m = a ^ m * zy := by
    simpa using (Subgroup.mem_center_iff.mp hzy) (a ^ m)
  have hpow : a ^ m * a ^ n = a ^ n * a ^ m := by
    exact (((Commute.refl a).zpow_right n).zpow_left m).eq
  calc
    (a ^ m * zx) * (a ^ n * zy) = a ^ m * a ^ n * zx * zy := by
      simp [mul_assoc, hzxa]
    _ = a ^ n * a ^ m * zy * zx := by
      simp [mul_assoc, hpow, (Subgroup.mem_center_iff.mp hzx) zy, (Subgroup.mem_center_iff.mp hzy) zx]
    _ = a ^ n * zy * a ^ m * zx := by
      rw [mul_assoc]
      rw [← hzya]
      simp [mul_assoc]
    _ = (a ^ n * zy) * (a ^ m * zx) := by
      simp [mul_assoc]
