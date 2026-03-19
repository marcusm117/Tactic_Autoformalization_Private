import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_2_11_3 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) : ∃ x : G, orderOf x = 2 := by
  classical
  have h2 : (2 : ℕ) ∣ Fintype.card G := by
    rcases hG with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [two_mul] using hr
  exact Fintype.exists_prime_orderOf_eq (G := G) Nat.prime_two h2
