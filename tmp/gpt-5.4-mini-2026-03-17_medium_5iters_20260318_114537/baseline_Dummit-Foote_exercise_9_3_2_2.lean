import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  rcases hfg 0 with ⟨a, ha⟩
  have htop := congrArg (fun q : ℕ → ℚ => q (Nat.succ ((f * g).natDegree))) ha
  have hdeg : (f * g).coeff (Nat.succ ((f * g).natDegree)) = (0 : ℚ) := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  have ha0q : (a : ℚ) = 0 := by
    simpa [hdeg] using htop
  have hzero : ∀ n : ℕ, (f * g).coeff n = 0 := by
    intro n
    have hq : (f * g).coeff n = (a : ℚ) := by
      exact congrArg (fun q : ℕ → ℚ => q n) ha
    simpa [ha0q] using hq
  have hmul : f * g = 0 := by
    ext n
    simpa using hzero n
  have hfz : f = 0 ∨ g = 0 := mul_eq_zero.mp hmul
  rcases hfz with rfl | rfl
  · refine ⟨0, by simp⟩
  · refine ⟨0, by simp⟩
