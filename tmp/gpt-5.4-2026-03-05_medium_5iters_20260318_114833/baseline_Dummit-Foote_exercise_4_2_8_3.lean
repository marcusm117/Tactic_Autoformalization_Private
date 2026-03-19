import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  have hfin : Finite (G ⧸ H) := by
    cases finite_or_infinite (G ⧸ H) with
    | inl hfin => exact hfin
    | inr hinf =>
        exfalso
        letI := hinf
        have hzero : Nat.card (G ⧸ H) = 0 := Nat.card_eq_zero_of_infinite
        have : H.index = 0 := by
          simpa [Subgroup.index] using hzero
        rw [hH] at this
        exact Nat.ne_of_gt hn this
  haveI : Finite (G ⧸ H) := hfin
  letI := Fintype.ofFinite (G ⧸ H)
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  let K : Subgroup G := f.ker
  refine ⟨K, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : f g = 1 := by
      simpa [K] using hg
    have hfix :
        (f g) (QuotientGroup.mk (1 : G)) = (1 : Equiv.Perm (G ⧸ H)) (QuotientGroup.mk (1 : G)) := by
      exact congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ (QuotientGroup.mk (1 : G))) hg'
    have hq : QuotientGroup.mk g = QuotientGroup.mk (1 : G) := by
      simpa [f] using hfix
    have hrel : QuotientGroup.leftRel H g 1 := Quotient.exact hq
    have hginv : g⁻¹ ∈ H := by
      simpa [QuotientGroup.leftRel] using hrel
    exact H.inv_mem hginv
  · dsimp [K]
    infer_instance
  · have hindex : K.index ≤ Nat.card (Equiv.Perm (G ⧸ H)) := by
      calc
        K.index = Nat.card f.range := by
          change Nat.card (G ⧸ K) = Nat.card f.range
          simpa [K] using Nat.card_congr (f.quotientKerEquivRange.toEquiv)
        _ ≤ Nat.card (Equiv.Perm (G ⧸ H)) := by
          exact
            Nat.card_le_of_injective
              (Subtype.val : f.range → Equiv.Perm (G ⧸ H))
              Subtype.val_injective
    have hcardQ : Fintype.card (G ⧸ H) = n := by
      rw [← Nat.card_eq_fintype_card (G ⧸ H)]
      simpa [Subgroup.index] using hH
    have hperm : Nat.card (Equiv.Perm (G ⧸ H)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardQ]
    simpa [hperm] using hindex
