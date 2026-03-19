import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_11 :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e : MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] Polynomial (Polynomial ℚ) := by
    refine (MvPolynomial.finSuccEquiv ℚ).trans ?_
    exact Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv ℚ)
  have hp : Prime (Polynomial.X + 1 : Polynomial ℚ) := by
    simpa using (Polynomial.irreducible_X_add_C (1 : ℚ)).prime
  have hpoly :
      Irreducible
        (Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)
          : Polynomial (Polynomial ℚ)) := by
    refine Polynomial.irreducible_of_eisenstein (p := Polynomial.X + 1) hp ?_ ?_ ?_
    · simp
    · intro n hn
      interval_cases n <;> simp [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    · intro hsq
      have hsq' : (Polynomial.X + 1 : Polynomial ℚ) ∣ Polynomial.X - 1 := by
        have hsq'' : (Polynomial.X + 1 : Polynomial ℚ) * (Polynomial.X + 1) ∣
            (Polynomial.X + 1 : Polynomial ℚ) * (Polynomial.X - 1) := by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq
        exact dvd_of_mul_left_dvd hsq''
      rcases hsq' with ⟨q, hq⟩
      have hval := congrArg (fun p : Polynomial ℚ => p.eval (-1 : ℚ)) hq
      simpa using hval
  simpa [e, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (e.irreducible_iff.mpr hpoly)
