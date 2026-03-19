import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  rcases isSimpleGroup_iff_isCyclic_and_prime_card.mp ‹IsSimpleGroup G› with ⟨hcyc, hprime⟩
  have hfin : Finite G := by
    by_cases h : Finite G
    · exact h
    · haveI : Infinite G := not_finite_iff_infinite.mp h
      exact False.elim (hprime.ne_zero (show Nat.card G = 0 from Nat.card_eq_zero_of_infinite))
  letI : Finite G := hfin
  letI : Fintype G := Fintype.ofFinite G
  refine ⟨hcyc, ⟨inferInstance, ?_⟩⟩
  simpa [Nat.card_eq_fintype_card] using hprime
