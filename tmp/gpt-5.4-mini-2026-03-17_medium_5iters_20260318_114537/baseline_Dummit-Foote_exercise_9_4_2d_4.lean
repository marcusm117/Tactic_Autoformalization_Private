import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_2d {p : ℕ} (hp : p.Prime ∧ p > 2)
  {f : Polynomial ℤ} (hf : f = (X + 2)^p):
  Irreducible (∑ n ∈ (f.support \ {0}), (f.coeff n : Polynomial ℤ) * X ^ (n-1) :
  Polynomial ℤ) := by
  subst hf
  classical
  simpa [Polynomial.geomSum₂] using
    (Polynomial.irreducible_geomSum₂ (x := X + 2) (y := (2 : Polynomial ℤ)) hp.1)
