import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x) := by
  rcases hx with ⟨n, hn⟩
  let s : R := Finset.sum (Finset.range n) (fun k => (-x) ^ k)
  have hpow : (-x) ^ n = 0 := by
    rw [neg_pow]
    simp [hn]
  have hgeom : (-x - 1) * s = -1 := by
    simpa [s, hpow] using (mul_geom_sum (-x) n)
  have h : (1 + x) * s = 1 := by
    have h' : -((1 + x) * s) = -1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_mul, neg_add_rev] using hgeom
    exact neg_injective h'
  exact (isUnit_iff_exists_inv).2 ⟨s, h⟩
