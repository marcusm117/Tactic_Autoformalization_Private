import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  let K : Subgroup G := f.ker
  refine ⟨K, ?_, ?_⟩
  · intro g hg
    have hg' : f g = 1 := by
      simpa [K, MonoidHom.mem_ker] using hg
    have hfix : g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      have := congrArg (fun p : Equiv.Perm (G ⧸ H) => p ((1 : G) : G ⧸ H)) hg'
      simpa [f] using this
    have hgq : ((g : G) : G ⧸ H) = 1 := by
      simpa using hfix
    exact (QuotientGroup.eq_one_iff.mp hgq)
  · constructor
    · exact f.ker_normal
    · have hcardH : Nat.card (G ⧸ H) = n := by
        simpa [Subgroup.index] using hH
      have hcardH_ne : Nat.card (G ⧸ H) ≠ 0 := by
        rw [hcardH]
        exact Nat.ne_of_gt hn
      have hfinH : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hcardH_ne
      letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
      let φ : G ⧸ K → Equiv.Perm (G ⧸ H) := QuotientGroup.lift f (by
        intro g hg
        exact hg)
      have hinj : Function.Injective φ := by
        intro a b hab
        refine QuotientGroup.inductionOn₂ a b ?_
        intro x y
        simp only [φ, QuotientGroup.lift_mk] at hab
        apply QuotientGroup.eq.mpr
        rw [MonoidHom.mem_ker]
        calc
          f (x⁻¹ * y) = f x⁻¹ * f y := by simp
          _ = f x⁻¹ * f x := by simp [hab]
          _ = 1 := by simp
      have hfinK : Finite (G ⧸ K) := Finite.of_injective φ hinj
      letI : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
      have hcardK : Fintype.card (G ⧸ K) ≤ Fintype.card (Equiv.Perm (G ⧸ H)) := by
        exact Fintype.card_le_of_injective φ hinj
      have hperm : Fintype.card (Equiv.Perm (G ⧸ H)) = n.factorial := by
        rw [hcardH]
        simpa using (Fintype.card_perm (α := G ⧸ H))
      calc
        K.index = Fintype.card (G ⧸ K) := by
          simpa [Subgroup.index]
        _ ≤ Fintype.card (Equiv.Perm (G ⧸ H)) := hcardK
        _ = n.factorial := hperm
