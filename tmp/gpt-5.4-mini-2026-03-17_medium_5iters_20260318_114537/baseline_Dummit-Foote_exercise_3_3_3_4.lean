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
    have hne : H ≠ H ⊔ K := by
      intro hEq
      exact hKH (by simpa [hEq] using (le_sup_right : K ≤ H ⊔ K))
    have hlt : H < H ⊔ K := lt_of_le_of_ne le_sup_left hne
    have hdiv : (H ⊔ K).index ∣ (p : ℕ) := by
      simpa [hH1] using
        (Subgroup.index_dvd_of_le (H := H) (K := H ⊔ K) le_sup_left)
    have hltIndex : (H ⊔ K).index < (p : ℕ) := by
      simpa [hH1] using (Subgroup.index_lt_index hlt)
    have hcases : (H ⊔ K).index = 1 ∨ (H ⊔ K).index = p := by
      exact p.property.eq_one_or_self_of_dvd hdiv
    have hsup : H ⊔ K = ⊤ := by
      rcases hcases with h1 | hp'
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        exact (Nat.lt_irrefl _ (by simpa [hp'] using hltIndex))
    constructor
    · exact hsup
    · simpa [hsup, hH1] using (Subgroup.relIndex_eq_index (H := H) (K := K))
