import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2d {p : ℕ} (hp : p.Prime ∧ p > 2)
  {f : Polynomial ℤ} (hf : f = (X + 2)^p):
  Irreducible (∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) :
  Polynomial ℤ) := by
  subst hf
  classical
  have hE : Eisenstein
      (∑ n ∈ (((X + 2) ^ p).support \ {0}),
        (((X + 2) ^ p).coeff n : Polynomial ℤ) * X ^ (n - 1))
      (p : ℤ) := by
    simpa [Eisenstein, hp.1, hp.2]
  exact hE.irreducible
