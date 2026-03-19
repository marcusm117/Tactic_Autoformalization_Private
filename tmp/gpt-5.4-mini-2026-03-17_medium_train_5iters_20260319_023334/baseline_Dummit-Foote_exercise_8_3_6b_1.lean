import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_6b {q : ℕ} (hq0 : q.Prime)
  (hq1 : q ≡ 3 [ZMOD 4]) {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({↑q} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = q^2 := by
  cases hR
  constructor
  · have hqG : Prime (q : GaussianInt) := by
      simpa using (GaussianInt.prime_natCast_iff q).2 ⟨hq0, hq1⟩
    haveI : Ideal.IsPrime (Ideal.span ({(q : GaussianInt)} : Set GaussianInt)) := by
      simpa using Ideal.span_singleton_prime hqG
    letI : Fintype (GaussianInt ⧸ Ideal.span ({(q : GaussianInt)} : Set GaussianInt)) :=
      GaussianInt.fintype_quotient_span q
    infer_instance
  · classical
    letI : Fintype (GaussianInt ⧸ Ideal.span ({(q : GaussianInt)} : Set GaussianInt)) :=
      GaussianInt.fintype_quotient_span q
    refine ⟨inferInstance, ?_⟩
    simpa using (GaussianInt.card_quotient_span q)
