import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x) := by
  rcases hx with ⟨n, hn⟩
  let y : R := -x
  have hpow : y ^ n = 0 := by
    dsimp [y]
    rw [neg_pow]
    simp [hn]
  have hgeom : ∀ m : ℕ, (1 - y) * Finset.sum (Finset.range m) (fun k => y ^ k) = 1 - y ^ m := by
    intro m
    induction m with
    | zero =>
        simp [y]
    | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul]
        rw [pow_succ]
        abel
  refine (isUnit_iff_exists_inv).2 ?_
  refine ⟨Finset.sum (Finset.range n) (fun k => y ^ k), ?_⟩
  simpa [y, hpow] using hgeom n
