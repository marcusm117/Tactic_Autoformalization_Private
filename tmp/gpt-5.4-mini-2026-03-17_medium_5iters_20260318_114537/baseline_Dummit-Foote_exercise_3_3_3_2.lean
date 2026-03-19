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
    have hdiv : (H ⊔ K).index ∣ H.index := by
      exact Subgroup.index_dvd le_sup_left
    have hcases : (H ⊔ K).index = 1 ∨ (H ⊔ K).index = p := by
      rw [hH1] at hdiv
      exact Nat.Prime.eq_one_or_self_of_dvd p.2 hdiv
    have hsup : H ⊔ K = ⊤ := by
      rcases hcases with h1 | hp'
      · exact (Subgroup.index_eq_one.mp h1)
      · exfalso
        have hEq : H = H ⊔ K := Subgroup.eq_of_le_of_index_eq le_sup_left (by simpa [hH1] using hp'.symm)
        exact hKH (by simpa [hEq] using (le_sup_right : K ≤ H ⊔ K))
    constructor
    · exact hsup
    · simpa [hsup, hH1] using (Subgroup.relindex_eq_index (H := H) (K := K))
