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
      exact ⟨i + j, by simp⟩
    inv_mem' := by
      intro a ha
      rcases ha with ⟨i, rfl⟩
      exact ⟨-i, by simp⟩ }
  have hr1 : DihedralGroup.r 1 ∈ R := by
    rw [hR]
    exact Subgroup.subset_closure (by simp)
  have hpow : ∀ m : ℕ, DihedralGroup.r (m : ZMod n) = (DihedralGroup.r 1) ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        calc
          DihedralGroup.r ((m + 1 : ℕ) : ZMod n) = DihedralGroup.r (m : ZMod n) * DihedralGroup.r 1 := by
            simpa [Nat.cast_succ] using (DihedralGroup.r_mul_r (m : ZMod n) 1).symm
          _ = (DihedralGroup.r 1) ^ m * DihedralGroup.r 1 := by rw [ih]
          _ = (DihedralGroup.r 1) ^ (m + 1) := by simp [pow_succ]
  have hrot_mem : ∀ k : ZMod n, DihedralGroup.r k ∈ R := by
    intro k
    have hk' : DihedralGroup.r (k.val : ZMod n) ∈ R := by
      simpa [hpow k.val] using (Subgroup.pow_mem R hr1 k.val)
    simpa using hk'
  have hRrot : R ≤ Rot := by
    rw [hR]
    refine Subgroup.closure_le.2 ?_
    intro x hx
    simp at hx
    subst hx
    exact ⟨1, by simp⟩
  have hsr0not : DihedralGroup.sr 0 ∉ Rot := by
    intro h
    rcases h with ⟨k, hk⟩
    cases hk
  constructor
  · intro htop
    have hmem : DihedralGroup.sr 0 ∈ R := by
      simpa [htop]
    exact hsr0not (hRrot hmem)
  · intro K hRK
    by_cases hsub : K ≤ R
    · exact Or.inl (le_antisymm hsub hRK)
    · right
      have hnot := hsub
      push_neg at hnot
      rcases hnot with ⟨x, hxK, hxR⟩
      cases x with
      | r k =>
          exact False.elim (hxR (hrot_mem k))
      | sr k =>
          have hsr0 : DihedralGroup.sr 0 ∈ K := by
            have hrk : DihedralGroup.r (-k) ∈ K := hRK (hrot_mem (-k))
            simpa using K.mul_mem hxK hrk
          apply le_antisymm
          · exact le_top
          · intro y hy
            cases y with
            | r l =>
                exact hRK (hrot_mem l)
            | sr l =>
                have hrl : DihedralGroup.r l ∈ K := hRK (hrot_mem l)
                simpa using K.mul_mem hsr0 hrl
