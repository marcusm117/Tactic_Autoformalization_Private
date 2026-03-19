import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_11_3 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) : ∃ x : G, orderOf x = 2 := by
  have h2 : (2 : ℕ) ∣ card G := by
    simpa [Even] using hG
  have hprime : Nat.Prime 2 := by decide
  simpa using hprime.exists_orderOf_eq h2
