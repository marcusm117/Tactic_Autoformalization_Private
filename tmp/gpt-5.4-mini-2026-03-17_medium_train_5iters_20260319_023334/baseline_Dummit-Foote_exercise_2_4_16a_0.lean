import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  classical
  let S : Finset (Subgroup G) := Finset.univ.filter (fun K => H ≤ K ∧ K ≠ ⊤)
  have hS : S.Nonempty := by
    refine ⟨H, ?_⟩
    simp [S, hH]
  rcases S.exists_max_image (fun K : Subgroup G => Fintype.card K) hS with ⟨M, hMmem, hmax⟩
  have hMcond : H ≤ M ∧ M ≠ ⊤ := by
    simpa [S] using hMmem
  have hHM : H ≤ M := hMcond.1
  have hMneq : M ≠ ⊤ := hMcond.2
  refine ⟨M, hMneq, ?_, hHM⟩
  intro K hMK
  by_cases hKtop : K = ⊤
  · exact Or.inr hKtop
  · have hKcond : H ≤ K ∧ K ≠ ⊤ := ⟨le_trans hHM hMK, hKtop⟩
    have hKmem : K ∈ S := by
      simpa [S] using hKcond
    have hcardle : Fintype.card K ≤ Fintype.card M := hmax K hKmem
    by_cases hKeq : K = M
    · exact Or.inl hKeq
    · exfalso
      have hstrict : M < K := lt_of_le_of_ne hMK hKeq
      have hcardlt : Fintype.card M < Fintype.card K := Subgroup.card_lt_card hstrict
      exact not_lt_of_ge hcardle hcardlt
