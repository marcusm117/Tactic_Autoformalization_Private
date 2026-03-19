import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1
  let q : Polynomial ℤ := X^4 + 8 * X^3 + 24 * X^2 + 30 * X + 14
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hq : f.comp (X + 1) = q := by
    dsimp [f, q]
    simp
    ring
  have hPprime : P.IsPrime := by
    dsimp [P]
    simpa using (Ideal.span_singleton_prime.mpr (show Prime (2 : ℤ) by norm_num))
  have hdeg : q.natDegree = 4 := by
    apply Polynomial.natDegree_eq_of_coeff_ne_zero
    · dsimp [q]
      simp [Polynomial.coeff_X_pow]
    · intro m hm
      have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      have hm2 : m ≠ 2 := by omega
      have hm3 : m ≠ 3 := by omega
      have hm4 : m ≠ 4 := by omega
      dsimp [q]
      simp [Polynomial.coeff_X_pow, hm0, hm1, hm2, hm3, hm4]
  have hq_ne_zero : q ≠ 0 := by
    intro hz
    have hz' := congrArg (fun p : Polynomial ℤ => p.coeff 4) hz
    dsimp [q] at hz'
    simp [Polynomial.coeff_X_pow] at hz'
  have hlc : q.leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_eq_coeff_natDegree hq_ne_zero, hdeg]
    dsimp [q]
    simp [Polynomial.coeff_X_pow]
  have hq_irreducible : Irreducible q := by
    refine Polynomial.irreducible_of_eisenstein_criterion (f := q) (P := P) hPprime ?_ ?_ ?_ ?_ ?_
    · rw [hlc]
      dsimp [P]
      rw [Ideal.mem_span_singleton]
      norm_num
    · intro n hn
      rw [hdeg] at hn
      dsimp [P]
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> dsimp [q] <;> norm_num [Polynomial.coeff_X_pow]
    · have hmul :
          Ideal.span ({(2 : ℤ)} : Set ℤ) * Ideal.span ({(2 : ℤ)} : Set ℤ) =
            Ideal.span ({(4 : ℤ)} : Set ℤ) := by
        simpa using (Ideal.span_singleton_mul_span_singleton (2 : ℤ) (2 : ℤ))
      dsimp [P]
      rw [pow_two, hmul, Ideal.mem_span_singleton]
      norm_num
    · exact hq_ne_zero
    · rw [hlc]
      exact isUnit_one
  have hcomp_irreducible : Irreducible (f.comp (X + 1)) := by
    simpa [hq] using hq_irreducible
  rcases hcomp_irreducible with ⟨hcomp_nonunit, hcomp_fac⟩
  have hshift : ((X + 1 : Polynomial ℤ).comp (X - 1)) = X := by
    simp [sub_eq_add_neg]
    ring
  have hf_irreducible : Irreducible f := by
    refine ⟨?_, ?_⟩
    · intro hfu
      have : IsUnit (f.comp (X + 1)) := by
        simpa using hfu.map (Polynomial.compRingHom (X + 1 : Polynomial ℤ))
      exact hcomp_nonunit this
    · intro a b hab
      have hfac : f.comp (X + 1) = a.comp (X + 1) * b.comp (X + 1) := by
        simpa using congrArg (fun p : Polynomial ℤ => p.comp (X + 1)) hab
      have hu : IsUnit (a.comp (X + 1)) ∨ IsUnit (b.comp (X + 1)) := hcomp_fac hfac
      rcases hu with hau | hbu
      · left
        have : IsUnit ((a.comp (X + 1)).comp (X - 1)) := by
          simpa using hau.map (Polynomial.compRingHom (X - 1 : Polynomial ℤ))
        simpa [Polynomial.comp_assoc, hshift] using this
      · right
        have : IsUnit ((b.comp (X + 1)).comp (X - 1)) := by
          simpa using hbu.map (Polynomial.compRingHom (X - 1 : Polynomial ℤ))
        simpa [Polynomial.comp_assoc, hshift] using this
  simpa [f] using hf_irreducible
