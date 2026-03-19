import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_3_3_3 {p : Nat.Primes} {G : Type*} [Group G]
  {H : Subgroup G} [hH : H.Normal] (hH1 : H.index = p) :
  ∀ K : Subgroup G, K ≤ H ∨ (H ⊔ K = ⊤ ∧ (K ⊓ H).relindex K = p) := by
  intro K
  classical
  by_cases hKH : K ≤ H
  · exact Or.inl hKH
  · refine Or.inr ?_
    have hmul :
        H.relindex (H ⊔ K) * (H ⊔ K).index = H.index := by
      simpa using
        (Subgroup.relindex_mul_index (H := H) (K := H ⊔ K)
          (show H ≤ H ⊔ K from le_sup_left))
    have hrel_ne_one : H.relindex (H ⊔ K) ≠ 1 := by
      intro h1
      have hs : H = H ⊔ K := by
        exact (Subgroup.relindex_eq_one (H := H) (K := H ⊔ K)).1 h1
      exact hKH <| by
        simpa [hs] using (le_sup_right : K ≤ H ⊔ K)
    have hdiv : H.relindex (H ⊔ K) ∣ p := by
      refine ⟨(H ⊔ K).index, ?_⟩
      simpa [hH1] using hmul
    have hrel_eq_p : H.relindex (H ⊔ K) = p := by
      rcases p.2.eq_one_or_self_of_dvd hdiv with h1 | h2
      · exact (hrel_ne_one h1).elim
      · exact h2
    have hmul' : p * (H ⊔ K).index = p * 1 := by
      calc
        p * (H ⊔ K).index = H.relindex (H ⊔ K) * (H ⊔ K).index := by
          rw [hrel_eq_p]
        _ = H.index := hmul
        _ = p := hH1
        _ = p * 1 := by simp
    have hindex_eq_one : (H ⊔ K).index = 1 := by
      exact Nat.eq_of_mul_eq_mul_left p.2.pos hmul'
    have hsup_top : H ⊔ K = ⊤ := by
      exact (Subgroup.index_eq_one (H := H ⊔ K)).1 hindex_eq_one
    have hinf :
        (K ⊓ H).relindex K = H.relindex (H ⊔ K) := by
      simpa [inf_comm, sup_comm] using
        (Subgroup.inf_relindex_right (H := K) (K := H))
    exact ⟨hsup_top, by simpa [hinf] using hrel_eq_p⟩
