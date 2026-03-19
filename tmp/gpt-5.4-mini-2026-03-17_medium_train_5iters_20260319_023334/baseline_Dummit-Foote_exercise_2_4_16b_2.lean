import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16b {n : ℕ} {hn : n ≠ 0}
  {R : Subgroup (DihedralGroup n)}
  (hR : R = Subgroup.closure {DihedralGroup.r 1}) :
  R ≠ ⊤ ∧
  ∀ K : Subgroup (DihedralGroup n), R ≤ K → K = R ∨ K = ⊤ := by
  classical
  let Rot : Subgroup (DihedralGroup n) :=
  { carrier := {x : DihedralGroup n | ∃ k : ZMod n, x = DihedralGroup.r k}
    one_mem' := by
      exact ⟨0, by simp⟩
    mul_mem' := by
      intro a b ha hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with ⟨j, rfl⟩
      refine ⟨i + j, ?_⟩
      simpa using (DihedralGroup.r_mul_r i j)
    inv_mem' := by
      intro a ha
      rcases ha with ⟨i, rfl⟩
      exact ⟨-i, by simp⟩ }
  have hRrot : R ≤ Rot := by
    rw [hR]
    exact (Subgroup.closure_le (K := Rot)).2 (by
      intro x hx
      simp at hx
      subst hx
      exact ⟨1, rfl⟩)
  have hr1 : DihedralGroup.r 1 ∈ R := by
    rw [hR]
    exact Subgroup.subset_closure (by simp)
  have hrot_mem : ∀ k : ZMod n, DihedralGroup.r k ∈ R := by
    intro k
    refine ZMod.inductionOn k ?_ ?_
    · simpa using (R.one_mem : (1 : DihedralGroup n) ∈ R)
    · intro k hk
      have hmul : DihedralGroup.r k * DihedralGroup.r 1 ∈ R := R.mul_mem hk hr1
      simpa using hmul
  have hsr0not : DihedralGroup.sr 0 ∉ Rot := by
    intro h
    rcases h with ⟨k, hk⟩
    cases hk
  constructor
  · intro htop
    exact hsr0not (hRrot (by simpa [htop]))
  · intro K hRK
    by_cases hsub : K ≤ R
    · exact Or.inl (le_antisymm hsub hRK)
    · right
      have hnot : ∃ x : DihedralGroup n, x ∈ K ∧ x ∉ R := by
        classical
        by_contra h
        apply hsub
        intro x hxK
        by_contra hxR
        exact h ⟨x, hxK, hxR⟩
      rcases hnot with ⟨x, hxK, hxR⟩
      cases x with
      | r k =>
          exact False.elim (hxR (hrot_mem k))
      | sr k =>
          have hsr0 : DihedralGroup.sr 0 ∈ K := by
            have hrk : DihedralGroup.r (-k) ∈ K := hRK (hrot_mem (-k))
            simpa using K.mul_mem hxK hrk
          exact le_antisymm (by
            intro y hy
            cases y with
            | r l =>
                exact hRK (hrot_mem l)
            | sr l =>
                have hrl : DihedralGroup.r l ∈ K := hRK (hrot_mem l)
                simpa using K.mul_mem hsr0 hrl) le_top
