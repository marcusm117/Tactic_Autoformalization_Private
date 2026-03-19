import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_4_1 (G : Type*) [CommGroup G] [IsSimpleGroup G] :
    IsCyclic G ∧ ∃ G_fin : Fintype G, Nat.Prime (@card G G_fin) := by
  classical
  rcases (isSimpleGroup_iff (G := G)).mp inferInstance with ⟨hnontriv, hsimple⟩
  constructor
  · obtain ⟨g, hg⟩ := hnontriv.exists_ne (1 : G)
    refine ⟨g, ?_⟩
    have hnorm : (Subgroup.zpowers g).Normal := by infer_instance
    have h := hsimple (Subgroup.zpowers g) hnorm
    rcases h with hbot | htop
    · exfalso
      exact hg (by simpa [hbot] using (Subgroup.mem_zpowers g))
    · exact htop
  · haveI : Finite G := finite_of_isSimpleGroup (G := G)
    refine ⟨Fintype.ofFinite G, ?_⟩
    simpa using (Fintype.card_prime (G := G))
