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
    have hx : QuotientGroup.mk x ∈ Subgroup.zpowers (QuotientGroup.mk a) := hq (QuotientGroup.mk x)
    rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨n, hn⟩
    have hn' : QuotientGroup.mk (a ^ n) = QuotientGroup.mk x := by
      simpa using hn
    refine ⟨n, (a ^ n)⁻¹ * x, ?_, ?_⟩
    · exact QuotientGroup.eq.mp hn'
    · simp [mul_assoc]
  refine le_antisymm le_top ?_
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  rcases hdecomp x with ⟨m, zx, hzx, rfl⟩
  rcases hdecomp y with ⟨n, zy, hzy, rfl⟩
  have hzxa : zx * a ^ n = a ^ n * zx := by
    simpa using (Subgroup.mem_center_iff.mp hzx) (a ^ n)
  have hzya : zy * a ^ m = a ^ m * zy := by
    simpa using (Subgroup.mem_center_iff.mp hzy) (a ^ m)
  have hzcomm : zx * zy = zy * zx := by
    simpa using (Subgroup.mem_center_iff.mp hzx) zy
  have hpow : a ^ m * a ^ n = a ^ n * a ^ m := by
    rw [← zpow_add, add_comm, zpow_add]
  calc
    (a ^ m * zx) * (a ^ n * zy) = a ^ m * ((zx * a ^ n) * zy) := by
      rw [mul_assoc, mul_assoc]
    _ = a ^ m * ((a ^ n * zx) * zy) := by
      rw [hzxa]
    _ = (a ^ m * a ^ n) * (zx * zy) := by
      rw [mul_assoc, ← mul_assoc]
    _ = (a ^ n * a ^ m) * (zy * zx) := by
      rw [hpow, hzcomm]
    _ = a ^ n * ((zy * a ^ m) * zx) := by
      rw [← mul_assoc, mul_assoc]
    _ = a ^ n * ((a ^ m * zy) * zx) := by
      rw [← hzya]
    _ = (a ^ n * zy) * (a ^ m * zx) := by
      rw [← mul_assoc, mul_assoc]
