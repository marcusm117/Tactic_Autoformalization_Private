import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have hq : Irreducible ((X^4 - 2 * X + 2 : Polynomial ℤ)) := by
    have hE : Polynomial.Eisenstein ((X^4 - 2 * X + 2 : Polynomial ℤ)) (2 : ℤ) := by
      refine ⟨by norm_num, ?_, ?_, ?_⟩
      · intro n hn
        interval_cases n <;> norm_num
      · norm_num
      · norm_num
    exact hE.irreducible
  simpa [Polynomial.comp_X_add_C] using
    hq.map (Polynomial.compXAddCEquiv (1 : ℤ)).toMonoidHom
      (Polynomial.compXAddCEquiv (1 : ℤ)).injective
