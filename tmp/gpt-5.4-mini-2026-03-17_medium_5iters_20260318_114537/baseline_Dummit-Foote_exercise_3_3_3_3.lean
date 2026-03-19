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
    have hp : Nat.Prime (p : ℕ) := Nat.prime_iff.mpr p.property
    have hdiv : (H ⊔ K).index ∣ (p : ℕ) := by
      simpa [hH1] using (Subgroup.index_dvd_of_le (H := H) (K := H ⊔ K) le_sup_left)
    have hcases : (H ⊔ K).index = 1 ∨ (H ⊔ K).index = p := hp.eq_one_or_eq_self_of_dvd hdiv
    have hsup : H ⊔ K = ⊤ := by
      rcases hcases with h1 | hp'
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        have hEq : H = H ⊔ K := by
          apply Subgroup.relindex_eq_one.mp
          simp [Subgroup.relindex, hH1, hp']
        exact hKH (by simpa [hEq] using (le_sup_right : K ≤ H ⊔ K))
    constructor
    · exact hsup
    · simpa [hsup, hH1] using (Subgroup.relindex_eq_index (H := H) (K := K))
