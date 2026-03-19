import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have hq : Irreducible ((X^4 - 2 * X + 2 : Polynomial ℤ)) := by
    refine IsEisenstein.irreducible ?_
    refine ⟨by norm_num, ?_, ?_, ?_⟩
    · intro n hn
      interval_cases n <;> norm_num
    · norm_num
    · norm_num
  have hinj : Function.Injective (Polynomial.aeval (X + 1 : Polynomial ℤ)) := by
    intro f g hfg
    have hfg' := congrArg (Polynomial.aeval (X - 1 : Polynomial ℤ)) hfg
    simpa [Polynomial.aeval_comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using hfg'
  have hmap := hq.map (Polynomial.aeval (X + 1 : Polynomial ℤ)) hinj
  have hEq :
      (Polynomial.aeval (X + 1 : Polynomial ℤ)) ((X^4 - 2 * X + 2 : Polynomial ℤ)) =
        (X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ) := by
    simp [Polynomial.aeval, sub_eq_add_neg]
    ring
  simpa [hEq] using hmap
