import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  classical
  let S : Finset (Subgroup G) := Finset.univ.filter fun K => H ≤ K ∧ K ≠ ⊤
  have hS : S.Nonempty := by
    refine ⟨H, ?_⟩
    simp [S, hH]
  rcases S.exists_max_image (fun K : Subgroup G => Fintype.card K) hS with ⟨M, hMmem, hmax⟩
  have hHM : H ≤ M := by
    have h : H ≤ M ∧ M ≠ ⊤ := by simpa [S] using hMmem
    exact h.1
  have hMneq : M ≠ ⊤ := by
    have h : H ≤ M ∧ M ≠ ⊤ := by simpa [S] using hMmem
    exact h.2
  refine ⟨M, hMneq, ?_, hHM⟩
  intro K hMK
  by_cases hKtop : K = ⊤
  · exact Or.inr hKtop
  · by_cases hKM : K = M
    · exact Or.inl hKM
    · have hKmem : K ∈ S := by
        simp [S, le_trans hHM hMK, hKtop]
      have hcardle : Fintype.card K ≤ Fintype.card M := hmax K hKmem
      let f : M → K := fun x => ⟨x, hMK x.2⟩
      have hf : Injective f := by
        intro a b hab
        exact Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
      have hsurj : ¬ Surjective f := by
        intro hs
        apply hKM
        ext x
        constructor
        · intro hx
          exact hMK hx
        · intro hx
          obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
          have hxy : (y : G) = x := by
            simpa [f] using congrArg Subtype.val hy
          simpa [hxy] using y.2
      have hcardlt : Fintype.card M < Fintype.card K := Fintype.card_lt_of_injective_not_surjective hf hsurj
      exact False.elim (not_lt_of_ge hcardle hcardlt)
