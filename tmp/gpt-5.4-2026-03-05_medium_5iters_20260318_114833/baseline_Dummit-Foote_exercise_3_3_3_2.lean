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
    have hmul : H.relIndex (H ⊔ K) * (H ⊔ K).index = H.index := by
      simpa using
        (Subgroup.relIndex_mul_index (show H ≤ H ⊔ K from le_sup_left))
    have hrel_ne_one : H.relIndex (H ⊔ K) ≠ 1 := by
      intro h1
      have hsup_le : H ⊔ K ≤ H := Subgroup.relIndex_eq_one.mp h1
      exact hKH (le_trans le_sup_right hsup_le)
    have hdiv : H.relIndex (H ⊔ K) ∣ (p : ℕ) := by
      refine ⟨(H ⊔ K).index, ?_⟩
      rw [← hH1]
      exact hmul.symm
    have hp : Nat.Prime (p : ℕ) := p.2
    have hrel_eq_p : H.relIndex (H ⊔ K) = (p : ℕ) := by
      rcases Nat.Prime.eq_one_or_self_of_dvd hp (H.relIndex (H ⊔ K)) hdiv with h1 | h2
      · exact (hrel_ne_one h1).elim
      · exact h2
    have hmul' : (p : ℕ) * (H ⊔ K).index = (p : ℕ) * 1 := by
      calc
        (p : ℕ) * (H ⊔ K).index = H.relIndex (H ⊔ K) * (H ⊔ K).index := by
          rw [hrel_eq_p]
        _ = H.index := hmul
        _ = (p : ℕ) := hH1
        _ = (p : ℕ) * 1 := by simp
    have hindex_eq_one : (H ⊔ K).index = 1 := by
      exact Nat.eq_of_mul_eq_mul_left hp.pos hmul'
    have hsup_top : H ⊔ K = ⊤ := by
      exact Subgroup.index_eq_one.mp hindex_eq_one
    have hinf : (K ⊓ H).relIndex K = H.relIndex (H ⊔ K) := by
      simpa [inf_comm] using (Subgroup.inf_relIndex_right H K)
    refine ⟨hsup_top, ?_⟩
    change (K ⊓ H).relIndex K = (p : ℕ)
    rw [hinf, hrel_eq_p]
