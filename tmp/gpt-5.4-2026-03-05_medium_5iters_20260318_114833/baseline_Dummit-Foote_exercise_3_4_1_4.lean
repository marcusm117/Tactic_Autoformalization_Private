import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  have hcyc : IsCyclic G := IsSimpleGroup.isCyclic (α := G)
  by_cases hfin : Finite G
  · letI : Finite G := hfin
    letI : Fintype G := Fintype.ofFinite G
    refine ⟨hcyc, ⟨inferInstance, ?_⟩⟩
    simpa [Nat.card_eq_fintype_card] using (IsSimpleGroup.prime_card (α := G))
  · haveI : Infinite G := not_finite_iff_infinite.mp hfin
    letI : IsCyclic G := hcyc
    exact False.elim ((IsCyclic.not_isSimpleGroup (α := G)) ‹IsSimpleGroup G›)
