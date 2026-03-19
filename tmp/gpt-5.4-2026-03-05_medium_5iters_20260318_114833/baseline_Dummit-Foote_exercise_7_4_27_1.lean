import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  rcases ha with ⟨n, hn⟩
  let x : R := a * b
  have hna : a ^ (n + 1) = 0 := by
    simp [pow_succ, hn]
  have hx : x ^ (n + 1) = 0 := by
    dsimp [x]
    simpa [mul_pow, hna]
  have hgeom : ∀ m : ℕ, (1 - x) * (∑ i in Finset.range m, x ^ i) = 1 - x ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        rw [Finset.sum_range_succ, mul_add, hm, pow_succ]
        ring
  have h1 : (1 - x) * (∑ i in Finset.range (n + 1), x ^ i) = 1 := by
    rw [hgeom (n + 1), hx, sub_zero]
  have h2 : (∑ i in Finset.range (n + 1), x ^ i) * (1 - x) = 1 := by
    simpa [mul_comm] using h1
  refine ⟨⟨1 - x, (∑ i in Finset.range (n + 1), x ^ i), h1, h2⟩, ?_⟩
  dsimp [x]
