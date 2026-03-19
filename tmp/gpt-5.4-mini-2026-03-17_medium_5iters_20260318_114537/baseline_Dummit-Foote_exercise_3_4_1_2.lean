import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  constructor
  · exact isCyclic_of_isSimpleGroup (G := G)
  · haveI : Finite G := finite_of_isSimpleGroup (G := G)
    refine ⟨Fintype.ofFinite G, ?_⟩
    simpa using Nat.prime_card_of_isSimpleGroup (G := G)
