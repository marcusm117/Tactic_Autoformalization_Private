import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 + C 4 * X^3 + C 6 * X^2 + C 2 * X + C 1
  let g : Polynomial ℤ := X^4 + C (-2) * X + C 2
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hfg : f.comp (X - 1) = g := by
    dsimp [f, g]
    simp [sub_eq_add_neg]
    ring
  have hPprime : P.IsPrime := by
    dsimp [P]
    rw [span_singleton_prime]
    norm_num
  have hg_degree_le : g.degree ≤ 4 := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn4 : n ≠ 4 := by omega
    dsimp [g]
    simp [Polynomial.coeff_X_pow, hn0, hn1, hn4]
  have hg_monic : g.Monic := by
    dsimp [g]
    simp [Polynomial.monic]
  have hg_coeff0 : g.coeff 0 = 2 := by
    dsimp [g]
    simp [Polynomial.coeff_X_pow]
  have hP2 : P ^ 2 = Ideal.span ({(4 : ℤ)} : Set ℤ) := by
    dsimp [P]
    rw [pow_two, Ideal.span_singleton_mul_span_singleton]
    norm_num
  have hg_irreducible : Irreducible g := by
    refine Polynomial.irreducible_of_eisenstein_criterion (f := g) (P := P) hPprime ?_ ?_ ?_ ?_ ?_
    · have h1 : (1 : ℤ) ∉ P := by
        dsimp [P]
        rw [Ideal.mem_span_singleton]
        norm_num
      simpa [hg_monic.leadingCoeff] using h1
    · intro n hn
      have hn' : (n : WithBot ℕ) < 4 := lt_of_lt_of_le hn hg_degree_le
      have hn4 : n < 4 := by
        simpa using hn'
      dsimp [P]
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> dsimp [g] <;> simp [Polynomial.coeff_X_pow] <;> norm_num
    · rw [hg_coeff0]
      norm_num
    · rw [hg_coeff0, hP2, Ideal.mem_span_singleton]
      norm_num
    · exact hg_monic.isPrimitive
  have hcomp_irreducible : Irreducible (f.comp (X - 1)) := by
    simpa [hfg] using hg_irreducible
  rcases hcomp_irreducible with ⟨hcomp_nonunit, hcomp_fac⟩
  have hshift : ((X - 1 : Polynomial ℤ).comp (X + 1)) = X := by
    simp [sub_eq_add_neg]
    ring
  have hf_irreducible : Irreducible f := by
    refine ⟨?_, ?_⟩
    · intro hfu
      have : IsUnit (f.comp (X - 1)) := by
        simpa using hfu.map (Polynomial.compRingHom (X - 1 : Polynomial ℤ))
      exact hcomp_nonunit this
    · intro a b hab
      have hfac : f.comp (X - 1) = a.comp (X - 1) * b.comp (X - 1) := by
        simpa using congrArg (fun p : Polynomial ℤ => p.comp (X - 1)) hab
      have hu : IsUnit (a.comp (X - 1)) ∨ IsUnit (b.comp (X - 1)) := hcomp_fac hfac
      rcases hu with hau | hbu
      · left
        have : IsUnit ((a.comp (X - 1)).comp (X + 1)) := by
          simpa using hau.map (Polynomial.compRingHom (X + 1 : Polynomial ℤ))
        simpa [Polynomial.comp_assoc, hshift] using this
      · right
        have : IsUnit ((b.comp (X - 1)).comp (X + 1)) := by
          simpa using hbu.map (Polynomial.compRingHom (X + 1 : Polynomial ℤ))
        simpa [Polynomial.comp_assoc, hshift] using this
  simpa [f] using hf_irreducible
