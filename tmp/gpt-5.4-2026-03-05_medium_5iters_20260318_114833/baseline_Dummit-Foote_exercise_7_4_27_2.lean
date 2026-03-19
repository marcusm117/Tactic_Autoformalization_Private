import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  rcases ha with ⟨n, hn⟩
  let x : R := a * b
  have hna : a ^ (n + 1) = 0 := by
    rw [pow_succ, hn, zero_mul]
  have hx : x ^ (n + 1) = 0 := by
    dsimp [x]
    rw [mul_pow, hna, zero_mul]
  let y : R := (Finset.range (n + 1)).sum (fun i : ℕ => x ^ i)
  have hgeom : ∀ m : ℕ, (1 - x) * ((Finset.range m).sum (fun i : ℕ => x ^ i)) = 1 - x ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        rw [Finset.sum_range_succ, mul_add, hm, pow_succ]
        ring
  have h1 : (1 - x) * y = 1 := by
    dsimp [y]
    rw [hgeom (n + 1), hx, sub_zero]
  have h2 : y * (1 - x) = 1 := by
    rw [mul_comm]
    exact h1
  refine ⟨⟨1 - x, y, h1, h2⟩, ?_⟩
  dsimp [x]
