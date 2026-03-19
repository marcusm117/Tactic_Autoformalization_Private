import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  have hcyc : IsCyclic G := IsSimpleGroup.isCyclic (G := G)
  have hprime : Nat.Prime (Nat.card G) := IsSimpleGroup.prime_card (G := G)
  have hfin : Finite G := by
    by_cases h : Finite G
    · exact h
    · haveI : Infinite G := not_finite_iff_infinite.mp h
      exact False.elim (hprime.ne_zero Nat.card_eq_zero_of_infinite)
  let G_fin : Fintype G := Fintype.ofFinite G
  letI : Fintype G := G_fin
  refine ⟨hcyc, ⟨G_fin, ?_⟩⟩
  simpa [Nat.card_eq_fintype_card] using hprime
