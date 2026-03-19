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
      exact ⟨i + j, by simp [add_comm, add_left_comm, add_assoc]⟩
    inv_mem' := by
      intro a ha
      rcases ha with ⟨i, rfl⟩
      exact ⟨-i, by simp⟩ }
  have hrot_mem : ∀ k : ZMod n, DihedralGroup.r k ∈ R := by
    intro k
    rw [hR]
    refine ZMod.induction_on k ?_ ?_
    · simp
    · intro k hk
      have hgen : DihedralGroup.r 1 ∈ Subgroup.closure ({DihedralGroup.r 1} : Set (DihedralGroup n)) :=
        Subgroup.subset_closure (by simp)
      simpa [add_comm, add_left_comm, add_assoc] using
        (Subgroup.mul_mem _ hk hgen)
  have hRot : R ≤ Rot := by
    rw [hR]
    exact Subgroup.closure_le.2 (by
      intro x hx
      rcases hx with rfl
      exact ⟨1, rfl⟩)
  have hsr0not : DihedralGroup.sr 0 ∉ Rot := by
    intro h
    rcases h with ⟨k, hk⟩
    cases hk
  constructor
  · intro htop
    have : DihedralGroup.sr 0 ∈ Rot := hRot (by rw [htop]; simp)
    exact hsr0not this
  · intro K hRK
    by_cases hsubset : K ≤ R
    · exact Or.inl (Subgroup.le_antisymm hsubset hRK)
    · right
      have hnot : ∃ x : DihedralGroup n, x ∈ K ∧ x ∉ R := by
        by_contra h
        apply hsubset
        intro x hxK
        by_contra hxR
        exact h ⟨x, hxK, hxR⟩
      rcases hnot with ⟨x, hxK, hxR⟩
      cases x with
      | r k =>
          exact False.elim (hxR (hrot_mem k))
      | sr k =>
          have hsr0 : DihedralGroup.sr 0 ∈ K := by
            have hrot : DihedralGroup.r (-k) ∈ K := hRK (hrot_mem (-k))
            simpa using K.mul_mem hxK hrot
          apply le_antisymm
          · exact le_top
          · intro y hy
            cases y with
            | r l =>
                exact hRK (hrot_mem l)
            | sr l =>
                have hrotl : DihedralGroup.r l ∈ K := hRK (hrot_mem l)
                simpa using K.mul_mem hsr0 hrotl
