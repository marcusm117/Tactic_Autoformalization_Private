import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  classical
  intro hsimple
  have hsyl : Fintype.card (Sylow 2 G) ∣ 224 := by
    simpa [hG] using (Fintype.card_sylow_dvd_card (G := G) (p := 2))
  have hmod : Fintype.card (Sylow 2 G) ≡ 1 [MOD 2] := by
    simpa using (card_sylow_modEq_card (G := G) (p := 2))
  have hcases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
    rcases hsyl with ⟨k, hk⟩
    rcases hmod with ⟨m, hm⟩
    have hodd : Fintype.card (Sylow 2 G) = 2 * m + 1 := by
      omega
    omega
  rcases hcases with h1 | h7
  · haveI : Subsingleton (Sylow 2 G) := (Fintype.card_eq_one_iff.mp h1)
    let P : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have hPcard : Fintype.card (P : Type*) = 32 := by
      simpa [hG] using P.2.card
    have hnorm : P.1.Normal := by
      refine (Subgroup.normal_iff).2 ?_
      intro g
      simpa using congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) (Subsingleton.elim _ _)
    have hbottop := hsimple.eq_bot_or_eq_top P.1 hnorm
    rcases hbottop with hbot | htop
    · simpa [hbot] using hPcard
    · simpa [htop, hG] using hPcard
  · let P : Sylow 2 G := Classical.choice (Sylow.nonempty (p := 2) (G := G))
    have hPcard : Fintype.card (P : Type*) = 32 := by
      simpa [hG] using P.2.card
    let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
    have hker : φ.ker = ⊥ := by
      have htopbot : φ.ker = ⊥ ∨ φ.ker = ⊤ := hsimple.eq_bot_or_eq_top φ.ker inferInstance
      rcases htopbot with hbot | htop
      · exact hbot
      · exfalso
        have htriv : ∀ g : G, φ g = 1 := by
          intro g
          have hg : g ∈ φ.ker := by simpa [htop]
          simpa [MonoidHom.mem_ker] using hg
        have hfix : ∀ g : G, (g • P : Sylow 2 G) = P := by
          intro g
          have := congrArg (fun e : Equiv.Perm (Sylow 2 G) => e P) (htriv g)
          simpa [φ] using this
        have hnorm : P.1.Normal := by
          refine (Subgroup.normal_iff).2 ?_
          intro g
          simpa using congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) (hfix g)
        have hbottop := hsimple.eq_bot_or_eq_top P.1 hnorm
        rcases hbottop with hbot | htop
        · simpa [hbot] using hPcard
        · simpa [htop, hG] using hPcard
    have hinj : Function.Injective φ := by
      intro a b hab
      have hmem : a⁻¹ * b ∈ φ.ker := by
        simpa [MonoidHom.mem_ker, φ, hab]
      have heq : a⁻¹ * b = 1 := by simpa [hker] using hmem
      have := congrArg (fun x => a * x) heq
      simpa using this
    have hcard : Fintype.card G ∣ Fintype.card (Equiv.Perm (Sylow 2 G)) := by
      have hcongr : Fintype.card G = Fintype.card φ.range := by
        exact Fintype.card_congr (Equiv.ofInjective φ hinj)
      rw [hcongr]
      exact Subgroup.card_dvd_card φ.range
    have hperm : Fintype.card (Equiv.Perm (Sylow 2 G)) = 5040 := by
      simpa [h7] using (Fintype.card_perm (α := Sylow 2 G))
    have hdiv : 224 ∣ 5040 := by
      simpa [hG, hperm] using hcard
    norm_num at hdiv
