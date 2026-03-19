import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x) := by
  rcases hx with ⟨n, hn⟩
  let a : R := -x
  have hpow : a ^ n = 0 := by
    simp [a, hn]
  have hgeom : ∀ m : ℕ, (1 - a) * (∑ k in Finset.range m, a ^ k : R) = 1 - a ^ m := by
    intro m
    induction m with
    | zero =>
        simp [a]
    | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, pow_succ']
        abel
  exact (isUnit_iff_exists_inv).2 ⟨∑ k in Finset.range n, a ^ k, by
    simpa [a, hpow] using hgeom n⟩
