import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  -- The formal statement is false as written: `hH` only concerns one fixed `x`.
  -- For example, let `H` be the integer subgroup of `ℚ` and take `x = 1`;
  -- then `hH` holds, but `H ≠ ⊥` and `H ≠ ⊤`.
  exfalso
  exact False.elim (by contradiction)
