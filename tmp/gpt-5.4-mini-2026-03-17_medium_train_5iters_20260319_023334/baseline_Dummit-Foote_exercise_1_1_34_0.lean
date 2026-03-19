import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_1_1_34 {G : Type*} [Group G] {x : G}
  (hx_inf : orderOf x = 0) (n m : ℤ) (hnm : n ≠ m) :
  x ^ n ≠ x ^ m := by
  intro h
  have h1 : x ^ (n - m) = 1 := by
    calc
      x ^ (n - m) = x ^ (n + -m) := by simp [sub_eq_add_neg]
      _ = x ^ n * x ^ (-m) := by rw [zpow_add]
      _ = x ^ m * x ^ (-m) := by rw [h]
      _ = 1 := by simp
  have hdiv : 0 ∣ n - m := by
    simpa [hx_inf] using (zpow_eq_one_iff.mp h1)
  have hzero : n - m = 0 := by
    rcases hdiv with ⟨k, hk⟩
    simpa using hk
  have hnm' : n = m := by
    exact sub_eq_zero.mp hzero
  exact hnm hnm'
