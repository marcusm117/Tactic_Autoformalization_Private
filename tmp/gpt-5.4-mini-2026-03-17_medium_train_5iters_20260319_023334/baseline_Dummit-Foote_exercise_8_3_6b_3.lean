import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_3_6b {q : ℕ} (hq0 : q.Prime)
  (hq1 : q ≡ 3 [ZMOD 4]) {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({↑q} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = q^2 := by
  cases hR
  constructor
  · exact GaussianInt.instIsFieldQuotientSpanNatCast q hq0 hq1
  · classical
    letI : Fintype (GaussianInt ⧸ Ideal.span ({(q : GaussianInt)} : Set GaussianInt)) :=
      GaussianInt.instFintypeQuotientSpanNatCast q
    refine ⟨inferInstance, ?_⟩
    simpa using (GaussianInt.cardQuotientSpanNatCast q)
