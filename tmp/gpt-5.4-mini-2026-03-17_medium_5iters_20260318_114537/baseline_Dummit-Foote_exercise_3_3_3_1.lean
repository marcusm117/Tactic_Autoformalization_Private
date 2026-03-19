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
    have hdiv : (H ⊔ K).index ∣ p := by
      simpa [hH1] using (Subgroup.index_dvd_index (H := H) (K := H ⊔ K) le_sup_left)
    have htopIndex : (H ⊔ K).index = 1 := by
      rcases p.2.eq_one_or_eq_self_of_dvd hdiv with h1 | hp'
      · exact h1
      · exfalso
        have hEq : H = H ⊔ K := Subgroup.eq_of_le_of_index_eq le_sup_left (by rw [hH1, hp'])
        exact hKH (by simpa [hEq] using (le_sup_right : K ≤ H ⊔ K))
    have hsup : H ⊔ K = ⊤ := Subgroup.eq_top_of_index_eq_one htopIndex
    constructor
    · exact hsup
    · simpa [hsup, hH1] using (Subgroup.relIndex_eq_index (H := H) (K := K))
