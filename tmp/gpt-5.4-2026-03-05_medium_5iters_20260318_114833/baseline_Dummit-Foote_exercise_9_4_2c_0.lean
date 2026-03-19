import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have hq :
      ((X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).comp (X + 1)) =
        (X^4 + 8 * X^3 + 24 * X^2 + 30 * X + 14 : Polynomial ℤ) := by
    native_decide
  have hdeg :
      (X^4 + 8 * X^3 + 24 * X^2 + 30 * X + 14 : Polynomial ℤ).natDegree = 4 := by
    native_decide
  have hq_irreducible :
      Irreducible
        (((X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).comp (X + 1))) := by
    rw [hq]
    refine Polynomial.irreducible_of_eisenstein_criterion (p := (2 : ℤ)) ?_ ?_ ?_ ?_
    · norm_num
    · norm_num
    · intro n hn
      rw [hdeg] at hn
      interval_cases n <;> norm_num
    · norm_num
  rcases hq_irreducible with ⟨hq_nonunit, hq_fac⟩
  refine ⟨?_, ?_⟩
  · intro hunit
    have hqunit :
        IsUnit
          (((X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).comp (X + 1))) := by
      simpa using hunit.map (Polynomial.compRingHom (X + 1 : Polynomial ℤ))
    exact hq_nonunit hqunit
  · intro a b hab
    have hfac :
        (((X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).comp (X + 1))) =
          a.comp (X + 1) * b.comp (X + 1) := by
      simpa using congrArg (fun r : Polynomial ℤ => r.comp (X + 1)) hab
    have hu : IsUnit (a.comp (X + 1)) ∨ IsUnit (b.comp (X + 1)) := hq_fac _ _ hfac
    have hshift : ((X + 1 : Polynomial ℤ).comp (X - 1)) = X := by
      native_decide
    rcases hu with hau | hbu
    · left
      have : IsUnit ((a.comp (X + 1)).comp (X - 1)) := by
        simpa using hau.map (Polynomial.compRingHom (X - 1 : Polynomial ℤ))
      simpa [Polynomial.comp_assoc, hshift] using this
    · right
      have : IsUnit ((b.comp (X + 1)).comp (X - 1)) := by
        simpa using hbu.map (Polynomial.compRingHom (X - 1 : Polynomial ℤ))
      simpa [Polynomial.comp_assoc, hshift] using this
