import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_11 :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e0 : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
    (MvPolynomial.finSuccEquiv ℚ 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv (R := ℚ) (σ := Fin 0)))
  let e : MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] Polynomial (Polynomial ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ 1).trans (Polynomial.mapAlgEquiv e0)
  let f : Polynomial (Polynomial ℚ) :=
    Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ 2 - 1)
  have hp : Prime (Polynomial.X + 1 : Polynomial ℚ) := by
    simpa [sub_eq_add_neg] using (Polynomial.irreducible_X_sub_C (-1 : ℚ)).prime
  have hfdeg : f.natDegree = 2 := by
    simp [f, pow_two]
  have hE : Polynomial.Eisenstein (Polynomial.X + 1 : Polynomial ℚ) f := by
    refine ⟨hp, ?_, ?_, ?_⟩
    · intro n hn
      rw [hfdeg] at hn
      interval_cases n
      · refine ⟨Polynomial.X - 1, ?_⟩
        ring
      · simp [f]
    · simpa [f, hfdeg] using hp.not_dvd_one
    · intro h
      have h' : (Polynomial.X + 1 : Polynomial ℚ) * (Polynomial.X + 1) ∣ Polynomial.X ^ 2 - 1 := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
      have h'' : (Polynomial.X + 1 : Polynomial ℚ) ∣ Polynomial.X - 1 := by
        exact dvd_of_mul_left_dvd h'
      rcases h'' with ⟨q, hq⟩
      have hval := congrArg (fun p : Polynomial ℚ => p.eval (-1 : ℚ)) hq
      norm_num at hval
  have hpoly : Irreducible f := hE.irreducible
  have hmap : e ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) = f := by
    simp [e, e0, f, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  exact (MulEquiv.irreducible_iff e.toMulEquiv).2 <| by
    simpa [hmap] using hpoly
