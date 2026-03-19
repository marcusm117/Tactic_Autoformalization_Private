import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hq : Irreducible (X^4 - 6 * X^2 - 8 * X + 3 : Polynomial ℤ) := by
    apply Polynomial.irreducible_of_eisenstein (p := 2)
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq.comp_X_add_C (-1 : ℤ)
