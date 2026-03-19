import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  rcases hfg 0 with ⟨a, ha⟩
  have hN : (f * g).coeff ((f * g).natDegree + 1) = (a : ℚ) := by
    simpa using congrArg (fun φ : ℕ → ℚ => φ ((f * g).natDegree + 1)) ha
  have hdeg : (f * g).coeff ((f * g).natDegree + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact Nat.lt_succ_self _
  have hacast : (a : ℚ) = 0 := by
    rw [hdeg] at hN
    exact hN.symm
  have ha0 : a = 0 := by
    exact_mod_cast hacast
  have hmul : f * g = 0 := by
    ext n
    have hn : (f * g).coeff n = (a : ℚ) := by
      simpa using congrArg (fun φ : ℕ → ℚ => φ n) ha
    simpa [ha0] using hn
  rcases mul_eq_zero.mp hmul with hf | hg
  · refine ⟨0, ?_⟩
    simp [hf]
  · refine ⟨0, ?_⟩
    simp [hg]
