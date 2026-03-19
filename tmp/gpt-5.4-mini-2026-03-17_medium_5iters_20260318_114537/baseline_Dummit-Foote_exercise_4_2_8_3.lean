import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  refine ⟨f.ker, ?_, ?_⟩
  · intro g hg
    have hg' : f g = 1 := by
      simpa [MonoidHom.mem_ker] using hg
    have hfix : g • (1 : G ⧸ H) = (1 : G ⧸ H) := by
      have := congrArg (fun p : Equiv.Perm (G ⧸ H) => p (1 : G ⧸ H)) hg'
      simpa [f] using this
    simpa using hfix
  · constructor
    · exact inferInstance
    · have hfinQ : Finite (G ⧸ H) := by
        apply Nat.finite_of_card_ne_zero
        simpa [hH] using (Nat.ne_of_gt hn : n ≠ 0)
      letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
      haveI : Fintype f.range := inferInstance
      have hfinK : Finite (G ⧸ f.ker) := by
        exact Finite.of_equiv _ (MonoidHom.quotientKerEquivRange f)
      letI : Fintype (G ⧸ f.ker) := Fintype.ofFinite (G ⧸ f.ker)
      have hqrange : Fintype.card (G ⧸ f.ker) = Fintype.card f.range := by
        simpa using Fintype.card_congr (MonoidHom.quotientKerEquivRange f)
      have hrange : Fintype.card f.range ≤ Fintype.card (Equiv.Perm (G ⧸ H)) := by
        exact Fintype.card_subtype_le
      have hperm : Fintype.card (Equiv.Perm (G ⧸ H)) = (Fintype.card (G ⧸ H)).factorial := by
        simpa using (Fintype.card_perm (G ⧸ H))
      have hle : Fintype.card (G ⧸ f.ker) ≤ (Fintype.card (G ⧸ H)).factorial := by
        rw [hqrange]
        simpa [hperm] using hrange
      simpa [Subgroup.index, hH] using hle
