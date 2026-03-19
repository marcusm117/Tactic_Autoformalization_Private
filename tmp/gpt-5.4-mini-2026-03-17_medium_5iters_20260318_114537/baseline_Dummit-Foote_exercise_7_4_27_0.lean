import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  have hnil : IsNilpotent (a * b) := by
    rcases ha with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [mul_pow, hn]
  have hneg : IsNilpotent (-(a * b)) := hnil.neg
  simpa [sub_eq_add_neg] using hneg.isUnit_one_add
