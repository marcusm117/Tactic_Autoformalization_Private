import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  rcases (isSimpleGroup_iff (G := G)).mp inferInstance with ⟨hcyc, p, hp, he⟩
  constructor
  · exact hcyc
  · rcases he with ⟨e⟩
    refine ⟨Fintype.ofEquiv G (Multiplicative (ZMod p)) e, ?_⟩
    simpa [Fintype.card_zmod] using hp
