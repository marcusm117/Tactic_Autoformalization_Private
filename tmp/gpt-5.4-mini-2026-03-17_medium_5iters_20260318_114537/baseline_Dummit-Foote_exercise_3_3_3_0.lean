import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_3_3 {p : Nat.Primes} {G : Type*} [Group G]
  {H : Subgroup G} [hH : H.Normal] (hH1 : H.index = p) :
  ∀ K : Subgroup G, K ≤ H ∨ (H ⊔ K = ⊤ ∧ (K ⊓ H).relindex K = p) := by
  intro K
  by_cases hKH : K ≤ H
  · exact Or.inl hKH
  · right
    have hneq : H ⊔ K ≠ H := by
      intro hEq
      exact hKH (by simpa [hEq] using (le_sup_right : K ≤ H ⊔ K))
    have hlt : H < H ⊔ K := lt_of_le_of_ne le_sup_left hneq
    have hsup : H ⊔ K = ⊤ := by
      exact Subgroup.eq_top_of_index_eq_prime (H := H) (K := H ⊔ K) hH1 p.2 hlt
    constructor
    · exact hsup
    · simpa [hsup, hH1] using (Subgroup.relindex_eq_relindex (H := H) (K := K))
