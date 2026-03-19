import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  have hfin : Finite (G ⧸ H) := by
    cases finite_or_infinite (G ⧸ H) with
    | inl h => exact h
    | inr h =>
        exfalso
        letI := h
        have hzero : Nat.card (G ⧸ H) = 0 := Nat.card_eq_zero_of_infinite
        have hindex0 : H.index = 0 := by
          simpa [Subgroup.index] using hzero
        rw [hH] at hindex0
        exact Nat.ne_of_gt hn hindex0
  haveI : Finite (G ⧸ H) := hfin
  letI := Fintype.ofFinite (G ⧸ H)
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  let K : Subgroup G := f.ker
  let ψ : G ⧸ K → Equiv.Perm (G ⧸ H) :=
    Quotient.lift
      (fun g : G => f g)
      (by
        intro a b hab
        have hk' : a⁻¹ * b ∈ K := by
          simpa [QuotientGroup.leftRel] using hab
        have hk : f (a⁻¹ * b) = 1 := by
          simpa [K] using hk'
        have hmul : (f a)⁻¹ * f b = 1 := by
          simpa using hk
        have hres : f b = f a := by
          have := congrArg (fun x => f a * x) hmul
          simpa [mul_assoc] using this
        exact hres.symm)
  refine ⟨K, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : f g = 1 := by
      simpa [K] using hg
    have hfix := congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ ((1 : G) : G ⧸ H)) hg'
    simp [f] at hfix
    have hrel : QuotientGroup.leftRel H g 1 := Quotient.exact hfix
    have hginv : g⁻¹ ∈ H := by
      simpa [QuotientGroup.leftRel] using hrel
    exact H.inv_mem hginv
  · dsimp [K]
    infer_instance
  · have hψinj : Function.Injective ψ := by
      intro x y hxy
      refine Quotient.inductionOn₂ x y ?_ 
      intro a b hab
      apply Quotient.sound
      have hEq : f a = f b := by
        simpa [ψ] using hab
      have hmul : (f a)⁻¹ * f b = 1 := by
        rw [hEq]
        simp
      have hk : f (a⁻¹ * b) = 1 := by
        simpa using hmul
      simpa [QuotientGroup.leftRel, K] using hk
    have hindex : K.index ≤ Nat.card (Equiv.Perm (G ⧸ H)) := by
      simpa [Subgroup.index] using (Nat.card_le_of_injective ψ hψinj)
    have hcardQ : Fintype.card (G ⧸ H) = n := by
      rw [← Nat.card_eq_fintype_card (G ⧸ H)]
      simpa [Subgroup.index] using hH
    have hperm : Nat.card (Equiv.Perm (G ⧸ H)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardQ]
    simpa [hperm] using hindex
