import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

/-
  ProofStrategyTactics_parameterized.lean

  Custom Lean 4 tactics encoding the top 10 proof strategies from
  ProofNet-V analysis. `sylow_counting`, `lagrange`, and `counterexample`
  accept optional user parameters and use `elab` for proof-state awareness.
  The rest use `macro`.

  Import this file to use all tactics in other proofs:

    import ProofStrategyTactics_parameterized

  Authors: marcusm117
  License: Apache 2.0
-/


open Lean Elab Tactic Meta


/-! ## algebraic_chain

Tries to close an algebraic equality/identity goal by attempting
`ring`, `group`, `field_simp; ring`, and `simp` with common algebraic lemmas
in sequence. Covers the "direct algebraic computation / chain of equalities"
proof pattern. -/

macro "algebraic_chain" : tactic =>
  `(tactic|
    first
    | ring
    | group
    | (field_simp; ring)
    | (ring_nf; simp [mul_comm, mul_assoc, add_comm, add_assoc,
                      mul_inv_cancel, inv_mul_cancel])
    | simp [mul_comm, mul_assoc, mul_left_comm,
            add_comm, add_assoc, add_left_comm])


/-! ## sylow_counting

Parameterized: `sylow_counting` scans all primes in context.
`sylow_counting p` targets a specific prime p.

Introduces Sylow counting constraints:
  (1) `card (Sylow p G) ≡ 1 [MOD p]`
  (2) `card (Sylow p G) ∣ card G`
Then attempts `omega`, `norm_num`, and `decide` to resolve the arithmetic. -/

/-- Helper: introduce Sylow constraints for a given prime expression and try to resolve. -/
private def sylowCountingForPrime (p : Expr) : TacticM Unit := do
  try
    let modStx ← `(tactic|
      have := @Sylow.card_sylow_modEq_one _ _ $(← Term.exprToSyntax p) _ _ _)
    evalTactic modStx
  catch _ => pure ()
  try
    let dvdStx ← `(tactic|
      have := @card_sylow_dvd_index _ _ $(← Term.exprToSyntax p) _ _)
    evalTactic dvdStx
  catch _ => pure ()

/-- Helper: try to resolve arithmetic after Sylow constraints are introduced. -/
private def sylowCountingResolve : TacticM Unit := do
  try evalTactic (← `(tactic| omega))
  catch _ =>
  try evalTactic (← `(tactic| (norm_num at *; omega)))
  catch _ =>
  try evalTactic (← `(tactic| decide))
  catch _ =>
    pure ()

-- Syntax: `sylow_counting` or `sylow_counting p`
syntax "sylow_counting" (ppSpace term)? : tactic

elab_rules : tactic
  | `(tactic| sylow_counting $[$pStx?]?) => do
    match pStx? with
    | some pStx =>
      -- User provided a specific prime
      let p ← Term.elabTerm pStx none
      sylowCountingForPrime p
      sylowCountingResolve
    | none =>
      -- No argument: scan context for all Fact (Nat.Prime p)
      let ctx ← getLCtx
      let mut found := false
      for decl in ctx do
        if decl.isAuxDecl then continue
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``Fact 1 then
          let arg := ty.getArg! 0
          if arg.isAppOfArity ``Nat.Prime 1 then
            let p := arg.getArg! 0
            sylowCountingForPrime p
            found := true
      -- Fallback if no primes found
      if !found then
        try evalTactic (← `(tactic| have := Sylow.card_sylow_modEq_one))
        catch _ => pure ()
        try evalTactic (← `(tactic| have := card_sylow_dvd_index))
        catch _ => pure ()
      sylowCountingResolve


/-! ## show_normal

Proves a subgroup is normal by unfolding the normality condition
and attempting to close the conjugation-closure goal.
Handles both single subgroups and intersections of normal subgroups. -/

/-- Helper: the inner normality proof after `constructor`. -/
private def showNormalCore : TacticM Unit := do
  evalTactic (← `(tactic| constructor))
  evalTactic (← `(tactic| intro g x hx))
  -- Try various approaches to close the conjugation goal
  try evalTactic (← `(tactic|
    simp only [Subgroup.mem_inf] at hx ⊢ <;>
    exact ⟨Subgroup.Normal.conj_mem ‹_› x hx.1 g,
           Subgroup.Normal.conj_mem ‹_› x hx.2 g⟩))
  catch _ =>
  try evalTactic (← `(tactic| exact Subgroup.Normal.conj_mem ‹_› x hx g))
  catch _ =>
  try
    evalTactic (← `(tactic| simp [mul_assoc, mul_inv_cancel, inv_mul_cancel] at *))
    evalTactic (← `(tactic| assumption))
  catch _ =>
  try evalTactic (← `(tactic| group))
  catch _ =>
    pure ()

elab "show_normal" : tactic => showNormalCore


/-! ## lagrange

Parameterized: `lagrange` scans all subgroups in context.
`lagrange H` targets a specific subgroup H.
`lagrange H K` targets subgroups H and K.

Introduces Lagrange-type divisibility facts:
  (1) `Subgroup.card_subgroup_dvd_card H`  — |H| ∣ |G|
  (2) `Subgroup.index_mul_card H`          — |G| = [G:H] * |H|
Also introduces `orderOf_dvd_card` for element-order divisibility.
Then attempts `omega`/`norm_num` to resolve the arithmetic. -/

/-- Helper: introduce Lagrange facts for a given subgroup expression. -/
private def lagrangeForSubgroup (hExpr : Expr) : TacticM Unit := do
  try
    let dvdStx ← `(tactic|
      have := Subgroup.card_subgroup_dvd_card $(← Term.exprToSyntax hExpr))
    evalTactic dvdStx
  catch _ => pure ()
  try
    let idxStx ← `(tactic|
      have := Subgroup.index_mul_card $(← Term.exprToSyntax hExpr))
    evalTactic idxStx
  catch _ => pure ()

/-- Helper: try to resolve arithmetic after Lagrange facts are introduced. -/
private def lagrangeResolve : TacticM Unit := do
  try evalTactic (← `(tactic| omega))
  catch _ =>
  try evalTactic (← `(tactic| (norm_num at *; omega)))
  catch _ =>
  try evalTactic (← `(tactic| (simp only [Nat.dvd_iff_mod_eq_zero] at *; omega)))
  catch _ =>
    pure ()

-- Syntax: `lagrange` or `lagrange H` or `lagrange H K` (up to 4 subgroups)
syntax "lagrange" (ppSpace term)* : tactic

elab_rules : tactic
  | `(tactic| lagrange $[$args]*) => do
    if args.size > 0 then
      -- User provided specific subgroups
      for argStx in args do
        let hExpr ← Term.elabTerm argStx none
        lagrangeForSubgroup hExpr
    else
      -- No arguments: scan context for all Subgroup hypotheses
      let ctx ← getLCtx
      let mut found := false
      for decl in ctx do
        if decl.isAuxDecl then continue
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``Subgroup 2 then
          lagrangeForSubgroup decl.toExpr
          found := true
      -- Fallback if no subgroups found
      if !found then
        try evalTactic (← `(tactic| have := Subgroup.card_subgroup_dvd_card ‹_›))
        catch _ => pure ()
        try evalTactic (← `(tactic| have := Subgroup.index_mul_card ‹_›))
        catch _ => pure ()
    -- Always introduce order-divides-card
    try evalTactic (← `(tactic| have := orderOf_dvd_card))
    catch _ => pure ()
    lagrangeResolve


/-! ## isomorphism_theorem

Tries to close the goal by applying the First, Second, or Third
Isomorphism Theorem (for groups or rings). Falls back to simplifying
quotient expressions. -/

macro "isomorphism_theorem" : tactic =>
  `(tactic|
    first
    -- First Isomorphism Theorem (groups)
    | exact QuotientGroup.quotientKerEquivRange ‹_›
    -- First Isomorphism Theorem (rings)
    | exact RingHom.quotientKerEquivOfSurjective ‹_› ‹_›
    -- Second Isomorphism Theorem
    | exact QuotientGroup.quotientInfEquivProdNormalQuotient ‹_› ‹_›
    -- Third Isomorphism Theorem
    | exact Subgroup.quotientQuotientEquivQuotient ‹_› ‹_› ‹_›
    -- Fallback: simplify quotient expressions
    | (simp only [QuotientGroup.eq', QuotientGroup.mk'_apply];
       assumption))


/-! ## elem_count

Simplifies `Fintype.card` / `Finset.card` expressions using
inclusion-exclusion and injection bounds, then tries to close the
resulting arithmetic via `omega` or `linarith`. -/

macro "elem_count" : tactic =>
  `(tactic| (
    try simp only [Fintype.card, Finset.card,
                   Finset.card_union_add_card_inter,
                   Finset.card_sdiff, Finset.card_filter]
    try simp only [Nat.add_sub_cancel, Nat.sub_self]
    first
    | omega
    | linarith
    | (norm_num at *; omega)
    | skip))


/-! ## double_inclusion

Proves set/subgroup/ideal equality by double inclusion (A ⊆ B ∧ B ⊆ A),
or iff by splitting into both directions. Detects the goal shape and
applies the appropriate splitting strategy. -/

macro "double_inclusion" : tactic =>
  `(tactic|
    first
    -- Iff goal: split into two implications
    | constructor
    -- Set equality: extensionality then iff
    | (ext; constructor)
    -- Subgroup/Ideal equality via lattice antisymmetry
    | apply le_antisymm
    -- Set equality via subset antisymmetry
    | apply Set.Subset.antisymm)


/-! ## counterexample

Parameterized: `counterexample` tries blind brute-force.
`counterexample e₁, e₂, ...` provides explicit witnesses for existential
goals (applies `use` with the witnesses, then verifies).

Tries `decide`, `native_decide`, `norm_num` for verification. -/

/-- Helper: blind brute-force verification without witnesses. -/
private def counterexampleBlind : TacticM Unit := do
  try evalTactic (← `(tactic| decide))
  catch _ =>
  try evalTactic (← `(tactic| native_decide))
  catch _ =>
  try evalTactic (← `(tactic| norm_num))
  catch _ =>
  try evalTactic (← `(tactic| (simp; decide)))
  catch _ =>
  try evalTactic (← `(tactic| (simp; native_decide)))
  catch _ =>
    pure ()

-- Syntax: `counterexample` or `counterexample e₁, e₂, ...`
syntax "counterexample" : tactic
syntax "counterexample" term,+ : tactic

elab "counterexample" : tactic => counterexampleBlind


theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  intro hs
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P11 : Sylow 11 G := Classical.choice inferInstance
  let P3 : Sylow 3 G := Classical.choice inferInstance
  have hcard11 (P : Sylow 11 G) : Fintype.card P = 11 := by
    have hpow : 11 ^ (Nat.factorization 132) 11 = 11 := by native_decide
    simpa [Nat.card_eq_fintype_card, hG, hpow] using P.card_eq_multiplicity
  have hcard3 (P : Sylow 3 G) : Fintype.card P = 3 := by
    have hpow : 3 ^ (Nat.factorization 132) 3 = 3 := by native_decide
    simpa [Nat.card_eq_fintype_card, hG, hpow] using P.card_eq_multiplicity
  have normal_of_card1_11 :
      Fintype.card (Sylow 11 G) = 1 → (P11 : Subgroup G).Normal := by
    intro h1
    have hidx : (P11 : Subgroup G).normalizer.index = 1 := by
      calc
        (P11 : Subgroup G).normalizer.index = Fintype.card (Sylow 11 G) := by
          simpa using P11.card_eq_index_normalizer.symm
        _ = 1 := h1
    have htop : (P11 : Subgroup G).normalizer = ⊤ := Subgroup.index_eq_one.mp hidx
    constructor
    intro x hx g
    have hg : g ∈ (P11 : Subgroup G).normalizer := by
      rw [htop]
      simp
    rw [Subgroup.mem_normalizer_iff] at hg
    exact hg x hx
  have normal_of_card1_3 :
      Fintype.card (Sylow 3 G) = 1 → (P3 : Subgroup G).Normal := by
    intro h1
    have hidx : (P3 : Subgroup G).normalizer.index = 1 := by
      calc
        (P3 : Subgroup G).normalizer.index = Fintype.card (Sylow 3 G) := by
          simpa using P3.card_eq_index_normalizer.symm
        _ = 1 := h1
    have htop : (P3 : Subgroup G).normalizer = ⊤ := Subgroup.index_eq_one.mp hidx
    constructor
    intro x hx g
    have hg : g ∈ (P3 : Subgroup G).normalizer := by
      rw [htop]
      simp
    rw [Subgroup.mem_normalizer_iff] at hg
    exact hg x hx
  have h11_ne_one : Fintype.card (Sylow 11 G) ≠ 1 := by
    intro h1
    have hnorm : (P11 : Subgroup G).Normal := normal_of_card1_11 h1
    letI : (P11 : Subgroup G).Normal := hnorm
    rcases hs.eq_bot_or_eq_top_of_normal (P11 : Subgroup G) with hbot | htop
    · have hP : Fintype.card P11 = 1 := by
        simpa [hbot]
      omega
    · have hP : Fintype.card P11 = 132 := by
        simpa [htop, hG]
      omega
  have h3_ne_one : Fintype.card (Sylow 3 G) ≠ 1 := by
    intro h1
    have hnorm : (P3 : Subgroup G).Normal := normal_of_card1_3 h1
    letI : (P3 : Subgroup G).Normal := hnorm
    rcases hs.eq_bot_or_eq_top_of_normal (P3 : Subgroup G) with hbot | htop
    · have hP : Fintype.card P3 = 1 := by
        simpa [hbot]
      omega
    · have hP : Fintype.card P3 = 132 := by
        simpa [htop, hG]
      omega
  have inj_toPerm :
      ∀ {α : Type*} [Fintype α] [MulAction G α] [MulAction.IsPretransitive G α],
        α → Fintype.card α ≠ 1 → Function.Injective (MulAction.toPermHom G α) := by
    intro α _ _ _ a hcardne1
    let φ : G →* Equiv.Perm α := MulAction.toPermHom G α
    have hker_ne_top : φ.ker ≠ ⊤ := by
      intro htop
      have hnot_sub : ¬ Subsingleton α := by
        intro hsub
        letI := hsub
        have h1 : Fintype.card α = 1 := by
          simpa using (Fintype.card_of_subsingleton α)
        exact hcardne1 h1
      rcases not_subsingleton_iff_exists_ne.mp hnot_sub with ⟨b, hb⟩
      rcases (MulAction.exists_smul_eq G a b) with ⟨g, hg⟩
      have hgker : g ∈ φ.ker := by
        rw [htop]
        simp
      have hφg : φ g = 1 := by
        simpa using hgker
      have hfix : g • a = a := by
        have h := congrArg (fun σ : Equiv.Perm α => σ a) hφg
        simpa using h
      exact hb (hg.symm.trans hfix)
    have hker_bot : φ.ker = ⊥ := by
      letI : φ.ker.Normal := by infer_instance
      rcases hs.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
      · exact hbot
      · exact (hker_ne_top htop).elim
    intro g h hgh
    have hmem : g⁻¹ * h ∈ φ.ker := by
      change φ (g⁻¹ * h) = 1
      rw [map_mul, hgh]
      simp
    have hone : g⁻¹ * h = 1 := by
      have : g⁻¹ * h ∈ (⊥ : Subgroup G) := by
        simpa [hker_bot] using hmem
      simpa using this
    calc
      g = g * 1 := by simp
      _ = g * (g⁻¹ * h) := by simpa [hone]
      _ = h := by group
  have card_perm_dvd :
      ∀ {α : Type*} [Fintype α] [MulAction G α],
        Function.Injective (MulAction.toPermHom G α) →
          Fintype.card G ∣ Fintype.card (Equiv.Perm α) := by
    intro α _ _ hinj
    let φ : G →* Equiv.Perm α := MulAction.toPermHom G α
    let e : G ≃ φ.range := Equiv.ofBijective φ hinj
    have hcardRange : Fintype.card φ.range = Fintype.card G := by
      exact Fintype.card_congr e.symm
    have hdvd : Fintype.card φ.range ∣ Fintype.card (Equiv.Perm α) :=
      Subgroup.card_subgroup_dvd_card φ.range
    exact hcardRange ▸ hdvd
  let N11 : Subgroup G := (P11 : Subgroup G).normalizer
  have hP11le : (P11 : Subgroup G) ≤ N11 := by
    simpa [N11] using (Subgroup.le_normalizer : (P11 : Subgroup G) ≤ (P11 : Subgroup G).normalizer)
  have hn11_dvd12 : Fintype.card (Sylow 11 G) ∣ 12 := by
    have hdvd : 11 ∣ Fintype.card N11 := by
      simpa [hcard11 P11] using
        (Subgroup.card_dvd_of_le hP11le : Fintype.card P11 ∣ Fintype.card N11)
    rcases hdvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hm : N11.index * Fintype.card N11 = Fintype.card G := by
      simpa using Subgroup.index_mul_card N11
    have hidx : Fintype.card (Sylow 11 G) = N11.index := by
      simpa [N11] using P11.card_eq_index_normalizer
    omega [hm, hk, hidx, hG]
  have hpos11 : 0 < Fintype.card (Sylow 11 G) := Fintype.card_pos_iff.mpr ⟨P11⟩
  have hn11_cases :
      Fintype.card (Sylow 11 G) = 1 ∨
        Fintype.card (Sylow 11 G) = 2 ∨
        Fintype.card (Sylow 11 G) = 3 ∨
        Fintype.card (Sylow 11 G) = 4 ∨
        Fintype.card (Sylow 11 G) = 6 ∨
        Fintype.card (Sylow 11 G) = 12 := by
    rcases hn11_dvd12 with ⟨k, hk⟩
    omega
  have hn11 : Fintype.card (Sylow 11 G) = 12 := by
    rcases hn11_cases with h1 | h2 | h3 | h4 | h6 | h12
    · exact (h11_ne_one h1).elim
    · have hne1 : Fintype.card (Sylow 11 G) ≠ 1 := by omega
      have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 11 G)) :=
        inj_toPerm P11 hne1
      have hdvd := card_perm_dvd (α := Sylow 11 G) hφinj
      have : 132 ∣ 2 := by
        simpa [hG, Fintype.card_perm, h2] using hdvd
      norm_num at this
    · have hne1 : Fintype.card (Sylow 11 G) ≠ 1 := by omega
      have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 11 G)) :=
        inj_toPerm P11 hne1
      have hdvd := card_perm_dvd (α := Sylow 11 G) hφinj
      have : 132 ∣ 6 := by
        simpa [hG, Fintype.card_perm, h3] using hdvd
      norm_num at this
    · have hne1 : Fintype.card (Sylow 11 G) ≠ 1 := by omega
      have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 11 G)) :=
        inj_toPerm P11 hne1
      have hdvd := card_perm_dvd (α := Sylow 11 G) hφinj
      have : 132 ∣ 24 := by
        simpa [hG, Fintype.card_perm, h4] using hdvd
      norm_num at this
    · have hne1 : Fintype.card (Sylow 11 G) ≠ 1 := by omega
      have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 11 G)) :=
        inj_toPerm P11 hne1
      have hdvd := card_perm_dvd (α := Sylow 11 G) hφinj
      have : 132 ∣ 720 := by
        simpa [hG, Fintype.card_perm, h6] using hdvd
      norm_num at this
    · exact h12
  have order11_of_mem :
      ∀ {P : Sylow 11 G} {g : G}, g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = 11 := by
    intro P g hg hg1
    let x : P := ⟨g, hg⟩
    have hxpow : g ^ 11 = 1 := by
      have hx : x ^ Fintype.card P = 1 := by
        simpa using (pow_card_eq_one (a := x))
      simpa [hcard11 P] using congrArg Subtype.val hx
    have hdiv : orderOf g ∣ 11 := orderOf_dvd_of_pow_eq_one hxpow
    rcases (Nat.dvd_prime (show Nat.Prime 11 by decide)).mp hdiv with h | h
    · exact (hg1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have order3_of_mem :
      ∀ {P : Sylow 3 G} {g : G}, g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = 3 := by
    intro P g hg hg1
    let x : P := ⟨g, hg⟩
    have hxpow : g ^ 3 = 1 := by
      have hx : x ^ Fintype.card P = 1 := by
        simpa using (pow_card_eq_one (a := x))
      simpa [hcard3 P] using congrArg Subtype.val hx
    have hdiv : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hxpow
    rcases (Nat.dvd_prime (show Nat.Prime 3 by decide)).mp hdiv with h | h
    · exact (hg1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have eq_sylow11 :
      ∀ {P Q : Sylow 11 G} {g : G},
        g ∈ (P : Subgroup G) → g ∈ (Q : Subgroup G) → g ≠ 1 → P = Q := by
    intro P Q g hgP hgQ hg1
    have horder : orderOf g = 11 := order11_of_mem hgP hg1
    have hcardz : Fintype.card (Subgroup.zpowers g) = 11 := by
      simpa [horder] using (card_zpowers (a := g))
    have hEqP : Subgroup.zpowers g = (P : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgP)
        (by simpa [hcard11 P] using hcardz.le)
    have hEqQ : Subgroup.zpowers g = (Q : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgQ)
        (by simpa [hcard11 Q] using hcardz.le)
    have hsub : (P : Subgroup G) = (Q : Subgroup G) := by
      calc
        (P : Subgroup G) = Subgroup.zpowers g := hEqP.symm
        _ = (Q : Subgroup G) := hEqQ
    cases P
    cases Q
    cases hsub
    rfl
  have eq_sylow3 :
      ∀ {P Q : Sylow 3 G} {g : G},
        g ∈ (P : Subgroup G) → g ∈ (Q : Subgroup G) → g ≠ 1 → P = Q := by
    intro P Q g hgP hgQ hg1
    have horder : orderOf g = 3 := order3_of_mem hgP hg1
    have hcardz : Fintype.card (Subgroup.zpowers g) = 3 := by
      simpa [horder] using (card_zpowers (a := g))
    have hEqP : Subgroup.zpowers g = (P : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgP)
        (by simpa [hcard3 P] using hcardz.le)
    have hEqQ : Subgroup.zpowers g = (Q : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgQ)
        (by simpa [hcard3 Q] using hcardz.le)
    have hsub : (P : Subgroup G) = (Q : Subgroup G) := by
      calc
        (P : Subgroup G) = Subgroup.zpowers g := hEqP.symm
        _ = (Q : Subgroup G) := hEqQ
    cases P
    cases Q
    cases hsub
    rfl
  let N3 : Subgroup G := (P3 : Subgroup G).normalizer
  have hP3le : (P3 : Subgroup G) ≤ N3 := by
    simpa [N3] using (Subgroup.le_normalizer : (P3 : Subgroup G) ≤ (P3 : Subgroup G).normalizer)
  have hn3_dvd44 : Fintype.card (Sylow 3 G) ∣ 44 := by
    have hdvd : 3 ∣ Fintype.card N3 := by
      simpa [hcard3 P3] using
        (Subgroup.card_dvd_of_le hP3le : Fintype.card P3 ∣ Fintype.card N3)
    rcases hdvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hm : N3.index * Fintype.card N3 = Fintype.card G := by
      simpa using Subgroup.index_mul_card N3
    have hidx : Fintype.card (Sylow 3 G) = N3.index := by
      simpa [N3] using P3.card_eq_index_normalizer
    omega [hm, hk, hidx, hG]
  have hpos3 : 0 < Fintype.card (Sylow 3 G) := Fintype.card_pos_iff.mpr ⟨P3⟩
  have hn3_cases :
      Fintype.card (Sylow 3 G) = 1 ∨
        Fintype.card (Sylow 3 G) = 2 ∨
        Fintype.card (Sylow 3 G) = 4 ∨
        Fintype.card (Sylow 3 G) = 11 ∨
        Fintype.card (Sylow 3 G) = 22 ∨
        Fintype.card (Sylow 3 G) = 44 := by
    rcases hn3_dvd44 with ⟨k, hk⟩
    omega
  let A11 := Σ P : Sylow 11 G, {x : P // ((x : G) ≠ 1)}
  let A3 := Σ P : Sylow 3 G, {x : P // ((x : G) ≠ 1)}
  let A := Sum Unit (Sum A11 A3)
  let f : A → G := fun a =>
    match a with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl u) => u.2.1
    | Sum.inr (Sum.inr u) => u.2.1
  have hf : Function.Injective f := by
    intro a b h
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · rcases b with b | b
      · exfalso
        exact b.2.2 (by simpa [f] using h.symm)
      · exfalso
        exact b.2.2 (by simpa [f] using h.symm)
    · rcases a with a | a
      · exfalso
        exact a.2.2 (by simpa [f] using h)
      · exfalso
        exact a.2.2 (by simpa [f] using h)
    · rcases a with ⟨P, x⟩
      rcases b with ⟨Q, y⟩
      dsimp [f] at h
      have hPQ : P = Q := eq_sylow11 x.1.2 (by simpa [h] using y.1.2) x.2
      cases hPQ
      have hxy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        exact h
      cases hxy
      rfl
    · rcases a with ⟨P, x⟩
      rcases b with ⟨Q, y⟩
      dsimp [f] at h
      have h11 : orderOf ((x.1 : P) : G) = 11 := order11_of_mem x.1.2 x.2
      have h3 : orderOf ((x.1 : P) : G) = 3 := by
        have hxQ : ((x.1 : P) : G) ∈ (Q : Subgroup G) := by
          simpa [h] using y.1.2
        exact order3_of_mem hxQ x.2
      omega
    · rcases a with ⟨P, x⟩
      rcases b with ⟨Q, y⟩
      dsimp [f] at h
      have h11 : orderOf ((y.1 : Q) : G) = 11 := by
        have hyP : ((y.1 : Q) : G) ∈ (P : Subgroup G) := by
          simpa [h] using x.1.2
        exact order11_of_mem hyP y.2
      have h3 : orderOf ((y.1 : Q) : G) = 3 := order3_of_mem y.1.2 y.2
      omega
    · rcases a with ⟨P, x⟩
      rcases b with ⟨Q, y⟩
      dsimp [f] at h
      have hPQ : P = Q := eq_sylow3 x.1.2 (by simpa [h] using y.1.2) x.2
      cases hPQ
      have hxy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        exact h
      cases hxy
      rfl
  have hA11 : Fintype.card A11 = 120 := by
    simp [A11, hcard11, hn11]
  rcases hn3_cases with h1 | h2 | h4 | h11 | h22 | h44
  · exact (h3_ne_one h1).elim
  · have hne1 : Fintype.card (Sylow 3 G) ≠ 1 := by omega
    have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 3 G)) :=
      inj_toPerm P3 hne1
    have hdvd := card_perm_dvd (α := Sylow 3 G) hφinj
    have : 132 ∣ 2 := by
      simpa [hG, Fintype.card_perm, h2] using hdvd
    norm_num at this
  · have hne1 : Fintype.card (Sylow 3 G) ≠ 1 := by omega
    have hφinj : Function.Injective (MulAction.toPermHom G (Sylow 3 G)) :=
      inj_toPerm P3 hne1
    have hdvd := card_perm_dvd (α := Sylow 3 G) hφinj
    have : 132 ∣ 24 := by
      simpa [hG, Fintype.card_perm, h4] using hdvd
    norm_num at this
  · have hA3 : Fintype.card A3 = 22 := by
      simp [A3, hcard3, h11]
    have hA : Fintype.card A = 143 := by
      simp [A, hA11, hA3]
    have hle : Fintype.card A ≤ Fintype.card G := Fintype.card_le_of_injective f hf
    omega
  · have hA3 : Fintype.card A3 = 44 := by
      simp [A3, hcard3, h22]
    have hA : Fintype.card A = 165 := by
      simp [A, hA11, hA3]
    have hle : Fintype.card A ≤ Fintype.card G := Fintype.card_le_of_injective f hf
    omega
  · have hA3 : Fintype.card A3 = 88 := by
      simp [A3, hcard3, h44]
    have hA : Fintype.card A = 209 := by
      simp [A, hA11, hA3]
    have hle : Fintype.card A ≤ Fintype.card G := Fintype.card_le_of_injective f hf
    omega
