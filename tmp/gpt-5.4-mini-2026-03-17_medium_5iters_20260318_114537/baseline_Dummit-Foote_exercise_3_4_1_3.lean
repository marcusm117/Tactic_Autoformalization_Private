import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  constructor
  · have hsimple := (isSimpleGroup_iff (G := G)).mp inferInstance
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    refine ⟨g, ?_⟩
    have hnorm : (Subgroup.zpowers g).Normal := by infer_instance
    have h := hsimple (Subgroup.zpowers g) hnorm
    rcases h with hbot | htop
    · exfalso
      have hg' : g = 1 := by
        simpa [hbot] using (Subgroup.mem_zpowers g)
      exact hg hg'
    · exact htop
  · haveI : Finite G := IsSimpleGroup.finite (G := G)
    refine ⟨Fintype.ofFinite G, ?_⟩
    simpa using (IsSimpleGroup.card_prime (G := G))
