import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_9_4_11 :
  Irreducible ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e0 : MvPolynomial (Fin 1) ℚ ≃ₐ[ℚ] Polynomial ℚ :=
    (MvPolynomial.finSuccEquiv ℚ 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv ℚ))
  let e : MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] Polynomial (Polynomial ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ 1).trans (Polynomial.mapAlgEquiv e0)
  have hp : Prime (Polynomial.X + 1 : Polynomial ℚ) := by
    simpa [sub_eq_add_neg] using (Polynomial.irreducible_X_sub_C (-1 : ℚ)).prime
  have hnsq : ¬ IsSquare (-(Polynomial.X ^ 2 - 1 : Polynomial ℚ)) := by
    rintro ⟨q, hq⟩
    have hLC := congrArg Polynomial.leadingCoeff hq
    simp [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] at hLC
    have hnonneg : 0 ≤ (Polynomial.leadingCoeff q : ℚ) ^ 2 := sq_nonneg _
    nlinarith
  have hpoly :
      Irreducible
        (Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1)
          : Polynomial (Polynomial ℚ)) := by
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Polynomial.irreducible_X_sq_add_C (a := (Polynomial.X ^ 2 - 1 : Polynomial ℚ)) hnsq)
  have hmap :
      e ((MvPolynomial.X 0)^2 + (MvPolynomial.X 1)^2 - 1 : MvPolynomial (Fin 2) ℚ) =
        Polynomial.X ^ 2 + Polynomial.C ((Polynomial.X : Polynomial ℚ)^2 - 1) := by
    simp [e, e0, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  exact (RingEquiv.irreducible_iff e.toRingEquiv).2 <| by
    simpa [hmap] using hpoly
