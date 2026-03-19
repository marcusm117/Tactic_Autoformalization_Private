import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X ^ 4 + Polynomial.monomial 3 (-4 : ℤ) + Polynomial.C (6 : ℤ)
  have hP : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime := by
    rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 by norm_num)]
    norm_num
  have hdeg_le : f.natDegree ≤ 4 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 ?_
    intro n hn
    have h4 : n ≠ 4 := by omega
    have h3 : n ≠ 3 := by omega
    have h0 : n ≠ 0 := by omega
    simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_monomial, Polynomial.coeff_C, h4, h3, h0]
  have hcoeff4 : f.coeff 4 = 1 := by
    simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_monomial, Polynomial.coeff_C]
  have hcoeff4_ne : f.coeff 4 ≠ 0 := by
    rw [hcoeff4]
    norm_num
  have hdeg : f.natDegree = 4 := by
    exact le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hcoeff4_ne)
  have hf_ne : f ≠ 0 := by
    intro hf0
    have h := congrArg (fun p : Polynomial ℤ => p.coeff 4) hf0
    simp [hcoeff4] at h
  have hdegree : f.degree = (4 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hf_ne, hdeg]
  have hlc : f.leadingCoeff = 1 := by
    have hc := Polynomial.coeff_natDegree (p := f) hf_ne
    rw [hdeg] at hc
    simpa [hcoeff4] using hc.symm
  have hmonic : f.Monic := by
    change f.leadingCoeff = 1
    exact hlc
  have hirr : Irreducible f := by
    refine Polynomial.irreducible_of_eisenstein_criterion
      (P := Ideal.span ({(2 : ℤ)} : Set ℤ)) hP ?_ ?_ ?_ ?_ ?_
    · simpa [hlc, Ideal.mem_span_singleton] using (show ¬ ((2 : ℤ) ∣ 1) by norm_num)
    · intro n hn
      have hn4 : n < 4 := by
        rw [hdegree] at hn
        simpa using hn
      interval_cases n <;>
        norm_num [f, Ideal.mem_span_singleton, Polynomial.coeff_X_pow,
          Polynomial.coeff_monomial, Polynomial.coeff_C]
    · rw [hdegree]
      norm_num
    · simpa [f, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton,
        Polynomial.coeff_X_pow, Polynomial.coeff_monomial, Polynomial.coeff_C] using
        (show ¬ ((4 : ℤ) ∣ 6) by norm_num)
    · exact hmonic.isPrimitive
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    Polynomial.C_mul_X_pow_eq_monomial] using hirr
