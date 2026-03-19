import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
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


theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  intro hS
  by_cases hpeq : p = q
  · subst hpeq
    have hpg : IsPGroup p G := by
      refine ⟨3, ?_⟩
      simpa [hG, pow_succ] 
    exact (IsPGroup.not_isSimpleGroup (G := G) (p := p) hpg) hS
  · by_cases hqp : q < p
    · have hcard : Fintype.card (Sylow p G) = 1 := by
        sylow_counting p
        omega
      have hnorm : (Classical.choice (show Nonempty (Sylow p G) from inferInstance)).1.Normal := by
        simpa using (Sylow.normal_of_card_eq_one (p := p) (G := G) hcard)
      have hbot_or_top := hS.eq_bot_or_eq_top (Classical.choice (show Nonempty (Sylow p G) from inferInstance)).1 hnorm
      rcases hbot_or_top with hbot | htop
      · have hcardbot : Fintype.card ((⊥ : Subgroup G)) = Fintype.card ((Classical.choice (show Nonempty (Sylow p G) from inferInstance)).1) := by
          simpa [hbot]
        simpa using hcardbot
      · have hcardtop : Fintype.card G = Fintype.card ((Classical.choice (show Nonempty (Sylow p G) from inferInstance)).1) := by
          simpa [htop]
        have hcardP : Fintype.card ((Classical.choice (show Nonempty (Sylow p G) from inferInstance)).1) = p ^ 2 := by
          simpa using (Classical.choice (show Nonempty (Sylow p G) from inferInstance)).2.card_eq
        omega
    · have hle : p < q := by omega
      have hqcases : Fintype.card (Sylow q G) = 1 ∨ Fintype.card (Sylow q G) = p ^ 2 := by
        sylow_counting q
        omega
      rcases hqcases with hq1 | hq2
      · have hnorm : (Classical.choice (show Nonempty (Sylow q G) from inferInstance)).1.Normal := by
          simpa using (Sylow.normal_of_card_eq_one (p := q) (G := G) hq1)
        have hbot_or_top := hS.eq_bot_or_eq_top (Classical.choice (show Nonempty (Sylow q G) from inferInstance)).1 hnorm
        rcases hbot_or_top with hbot | htop
        · have hcardbot : Fintype.card ((⊥ : Subgroup G)) = Fintype.card ((Classical.choice (show Nonempty (Sylow q G) from inferInstance)).1) := by
            simpa [hbot]
          simpa using hcardbot
        · have hcardtop : Fintype.card G = Fintype.card ((Classical.choice (show Nonempty (Sylow q G) from inferInstance)).1) := by
            simpa [htop]
          have hcardQ : Fintype.card ((Classical.choice (show Nonempty (Sylow q G) from inferInstance)).1) = q := by
            simpa using (Classical.choice (show Nonempty (Sylow q G) from inferInstance)).2.card_eq
          omega
      · have hqdiv : q ∣ p ^ 2 - 1 := by
          have hmod := (Sylow.card_sylow_modEq_one (p := q) (G := G))
          have hdiv := (card_sylow_dvd_index (p := q) (G := G))
          omega
        have hp2 : p = 2 := by
          have hqle : q ≤ p + 1 := by
            omega
          have hqeq : q = p + 1 := by omega
          omega
        have hq3 : q = 3 := by omega
        subst hp2
        subst hq3
        have h2cases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 := by
          sylow_counting 2
          omega
        rcases h2cases with h21 | h23
        · have hnorm : (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1.Normal := by
            simpa using (Sylow.normal_of_card_eq_one (p := 2) (G := G) h21)
          have hbot_or_top := hS.eq_bot_or_eq_top (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1 hnorm
          rcases hbot_or_top with hbot | htop
          · have hcardbot : Fintype.card ((⊥ : Subgroup G)) = Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) := by
              simpa [hbot]
            simpa using hcardbot
          · have hcardtop : Fintype.card G = Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) := by
              simpa [htop]
            have hcardP : Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) = 4 := by
              simpa using (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).2.card_eq
            omega
        · have hcard3 : Fintype.card (Sylow 2 G) = 3 := h23
          let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPerm G (Sylow 2 G)
          have hker : φ.ker = ⊥ := by
            have hnorm := hS.eq_bot_or_eq_top φ.ker
            rcases hnorm with hbot | htop
            · exact hbot
            · have htriv : ∀ g : G, φ g = 1 := by
                intro g
                have hg : g ∈ φ.ker := by simpa [htop]
                simpa [MonoidHom.mem_ker] using hg
              have hfix : ∀ P : Sylow 2 G, ∀ g : G, g • P = P := by
                intro P g
                have := htriv g
                simpa [φ, MulAction.toPerm_apply] using congrArg (fun e : Equiv.Perm (Sylow 2 G) => e P) this
              have hPnorm : (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1.Normal := by
                classical
                refine Subgroup.normal_iff.mpr ?_
                intro g
                simpa [hfix (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)) g]
              have hbot_or_top' := hS.eq_bot_or_eq_top (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1 hPnorm
              rcases hbot_or_top' with hbot' | htop'
              · have hcardbot : Fintype.card ((⊥ : Subgroup G)) = Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) := by
                  simpa [hbot']
                simpa using hcardbot
              · have hcardtop : Fintype.card G = Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) := by
                  simpa [htop']
                have hcardP : Fintype.card ((Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).1) = 4 := by
                  simpa using (Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)).2.card_eq
                omega
          have hinj : Function.Injective φ := by
            exact MonoidHom.injective_iff_ker_eq_bot.mpr hker
          have hcardle : Fintype.card G ≤ Fintype.card (Equiv.Perm (Sylow 2 G)) := by
            exact Fintype.card_le_of_injective φ hinj
          have hperm : Fintype.card (Equiv.Perm (Sylow 2 G)) = 6 := by
            simpa [hcard3]
          have hG12 : Fintype.card G = 12 := by
            simpa [hG]
          omega
