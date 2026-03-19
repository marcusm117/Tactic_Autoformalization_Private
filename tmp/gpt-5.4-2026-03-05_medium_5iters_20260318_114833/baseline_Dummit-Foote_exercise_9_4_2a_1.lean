import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hdeg : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).natDegree = 4 := by
    decide
  have hlc : (X ^ 4 - 4 * X ^ 3 + 6 : Polynomial ℤ).leadingCoeff = 1 := by
    decide
  refine Polynomial.irreducible_of_eisenstein_criterion
    (P := Ideal.span ({(2 : ℤ)} : Set ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
  · first
    | exact Ideal.span_singleton_prime (show Prime (2 : ℤ) by norm_num)
    | exact Ideal.span_singleton_prime.mp (show Prime (2 : ℤ) by norm_num)
    | exact Ideal.span_singleton_prime.mpr (show Prime (2 : ℤ) by norm_num)
    | exact (Ideal.span_singleton_prime).1 (show Prime (2 : ℤ) by norm_num)
    | exact (Ideal.span_singleton_prime).2 (show Prime (2 : ℤ) by norm_num)
    | exact ⟨Ideal.span_singleton_prime (show Prime (2 : ℤ) by norm_num)⟩
    | exact ⟨Ideal.span_singleton_prime.mp (show Prime (2 : ℤ) by norm_num)⟩
    | exact ⟨Ideal.span_singleton_prime.mpr (show Prime (2 : ℤ) by norm_num)⟩
    | exact ⟨(Ideal.span_singleton_prime).1 (show Prime (2 : ℤ) by norm_num)⟩
    | exact ⟨(Ideal.span_singleton_prime).2 (show Prime (2 : ℤ) by norm_num)⟩
    | exact (Ideal.span_singleton_prime (show Prime (2 : ℤ) by norm_num)).ne_top
    | exact (Ideal.span_singleton_prime.mp (show Prime (2 : ℤ) by norm_num)).ne_top
    | exact (Ideal.span_singleton_prime.mpr (show Prime (2 : ℤ) by norm_num)).ne_top
    | exact ((Ideal.span_singleton_prime).1 (show Prime (2 : ℤ) by norm_num)).ne_top
    | exact ((Ideal.span_singleton_prime).2 (show Prime (2 : ℤ) by norm_num)).ne_top
  · first
    | simpa [hlc, Ideal.mem_span_singleton] using (show ¬ ((2 : ℤ) ∣ 1) by norm_num)
    | decide
  · intro n hn
    have hn' : n < 4 := by simpa [hdeg] using hn
    interval_cases n <;> norm_num [Ideal.mem_span_singleton]
  · first
    | simpa [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] using
        (show ¬ ((4 : ℤ) ∣ 6) by norm_num)
    | decide
  · first
    | norm_num
    | intro h
      have h' := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
      simp at h'
    | decide
  · first
    | simpa [hlc] using (isUnit_one : IsUnit (1 : ℤ))
    | decide
