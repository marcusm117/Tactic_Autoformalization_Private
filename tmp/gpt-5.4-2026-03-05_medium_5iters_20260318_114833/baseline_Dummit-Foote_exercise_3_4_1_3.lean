import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  have hfin : Finite G := IsSimpleGroup.finite (α := G)
  letI : Finite G := hfin
  letI : Fintype G := Fintype.ofFinite G
  refine ⟨IsSimpleGroup.isCyclic (α := G), ⟨inferInstance, ?_⟩⟩
  simpa [Nat.card_eq_fintype_card] using (IsSimpleGroup.prime_card (α := G))
