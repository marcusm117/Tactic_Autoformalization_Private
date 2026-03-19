import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_10_1_13 {R : Type*} [Ring R] {x : R}
  (hx : IsNilpotent x) : IsUnit (1 + x) := by
  rcases hx with ⟨n, hn⟩
  let s : R := Finset.sum (Finset.range n) (fun k => (-x) ^ k)
  have hpow : (-x) ^ n = 0 := by
    simpa [hn]
  have hL : (1 + x) * s = 1 := by
    have h := mul_geom_sum (-x) n
    have h' : -((1 + x) * s) = -1 := by
      simpa [s, hpow, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_mul] using h
    exact neg_inj.mp h'
  have hR : s * (1 + x) = 1 := by
    have h := geom_sum_mul (-x) n
    have h' : -(s * (1 + x)) = -1 := by
      simpa [s, hpow, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_neg] using h
    exact neg_inj.mp h'
  refine ⟨⟨1 + x, s, hL, hR⟩, rfl⟩
