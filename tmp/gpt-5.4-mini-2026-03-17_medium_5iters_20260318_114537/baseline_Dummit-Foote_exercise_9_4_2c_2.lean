import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have h : Irreducible ((X^4 - 2 * X + 2 : Polynomial ℤ)) := by
    refine Eisenstein.irreducible ?_
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  simpa [pow_four, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using
    h.comp (by simpa using (Polynomial.irreducible_X_add_C (1 : ℤ)))
