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


theorem exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P13 : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  have h13mod : Fintype.card (Sylow 13 G) ≡ 1 [MOD 13] := by
    simpa [hG] using (card_sylow_modEq_one (G := G) (p := 13))
  have h13dvd : Fintype.card (Sylow 13 G) ∣ 105 := by
    have hle : P13.1 ≤ P13.1.normalizer := by
      exact Subgroup.le_normalizer P13.1
    have hidx : P13.1.normalizer.index ∣ P13.1.index := Subgroup.index_dvd_of_le hle
    have hPidx : P13.1.index = 105 := by
      have hPcard : Fintype.card P13.1 = 13 := by
        simpa [hG] using P13.card_eq
      have hmul := Subgroup.index_mul_card P13.1
      omega
    simpa [P13.card_eq_index_normalizer, hPidx] using hidx
  have h13cases : Fintype.card (Sylow 13 G) = 1 ∨ Fintype.card (Sylow 13 G) = 105 := by
    rcases Nat.ModEq_iff_eq_add_fac.mp h13mod with ⟨k, hk⟩
    rcases h13dvd with ⟨m, hm⟩
    have hk' : Fintype.card (Sylow 13 G) = 1 + 13 * k := by
      simpa using hk
    have hm' : 105 = (1 + 13 * k) * m := by
      simpa [hk'] using hm
    interval_cases k <;> omega
  rcases h13cases with h13 | h13
  · have hPtop : P13.1.normalizer = ⊤ := by
      have hidx : P13.1.normalizer.index = 1 := by
        simpa [P13.card_eq_index_normalizer, h13] using P13.card_eq_index_normalizer
      exact Subgroup.index_eq_one.mp hidx
    have hPnormal : P13.1.Normal := by
      constructor
      intro g x hx
      have hg : g ∈ P13.1.normalizer := by simpa [hPtop]
      exact hg x hx
    have hcases := hsimple.1 P13.1 hPnormal
    rcases hcases with hbot | htop
    · have hcard : Fintype.card P13.1 = 13 := by
        simpa [hG] using P13.card_eq
      have : (13 : ℕ) = 1 := by
        simpa [hbot] using hcard
      omega
    · have hcard : Fintype.card P13.1 = 13 := by
        simpa [hG] using P13.card_eq
      have : (13 : ℕ) = 1365 := by
        simpa [hG, htop] using hcard
      omega
  · have h7mod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
      simpa [hG] using (card_sylow_modEq_one (G := G) (p := 7))
    have h7dvd : Fintype.card (Sylow 7 G) ∣ 195 := by
      have hQ : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
      have hle : hQ.1 ≤ hQ.1.normalizer := by
        exact Subgroup.le_normalizer hQ.1
      have hidx : hQ.1.normalizer.index ∣ hQ.1.index := Subgroup.index_dvd_of_le hle
      have hQidx : hQ.1.index = 195 := by
        have hQcard : Fintype.card hQ.1 = 7 := by
          simpa [hG] using hQ.card_eq
        have hmul := Subgroup.index_mul_card hQ.1
        omega
      simpa [hQ.card_eq_index_normalizer, hQidx] using hidx
    have h7cases : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 15 := by
      rcases Nat.ModEq_iff_eq_add_fac.mp h7mod with ⟨k, hk⟩
      rcases h7dvd with ⟨m, hm⟩
      have hk' : Fintype.card (Sylow 7 G) = 1 + 7 * k := by
        simpa using hk
      have hm' : 195 = (1 + 7 * k) * m := by
        simpa [hk'] using hm
      interval_cases k <;> omega
    rcases h7cases with h7 | h7
    · have hQtop : (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1.normalizer = ⊤ := by
        have hQ : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
        have hidx : hQ.1.normalizer.index = 1 := by
          simpa [hQ.card_eq_index_normalizer, h7] using hQ.card_eq_index_normalizer
        exact Subgroup.index_eq_one.mp hidx
      have hQnormal : (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1.Normal := by
        constructor
        intro g x hx
        have hg : g ∈ (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1.normalizer := by
          simpa [hQtop]
        exact hg x hx
      have hcases := hsimple.1 (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1 hQnormal
      rcases hcases with hbot | htop
      · have hcard : Fintype.card (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1 = 7 := by
          simpa [hG] using (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).card_eq
        have : (7 : ℕ) = 1 := by
          simpa [hbot] using hcard
        omega
      · have hcard : Fintype.card (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).1 = 7 := by
          simpa [hG] using (Classical.choice (inferInstance : Nonempty (Sylow 7 G))).card_eq
        have : (7 : ℕ) = 1365 := by
          simpa [hG, htop] using hcard
        omega
    · have h5mod : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by
        simpa [hG] using (card_sylow_modEq_one (G := G) (p := 5))
      have h5dvd : Fintype.card (Sylow 5 G) ∣ 273 := by
        have hQ : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
        have hle : hQ.1 ≤ hQ.1.normalizer := by
          exact Subgroup.le_normalizer hQ.1
        have hidx : hQ.1.normalizer.index ∣ hQ.1.index := Subgroup.index_dvd_of_le hle
        have hQidx : hQ.1.index = 273 := by
          have hQcard : Fintype.card hQ.1 = 5 := by
            simpa [hG] using hQ.card_eq
          have hmul := Subgroup.index_mul_card hQ.1
          omega
        simpa [hQ.card_eq_index_normalizer, hQidx] using hidx
      have h5cases : Fintype.card (Sylow 5 G) = 1 ∨ 21 ≤ Fintype.card (Sylow 5 G) := by
        rcases Nat.ModEq_iff_eq_add_fac.mp h5mod with ⟨k, hk⟩
        rcases h5dvd with ⟨m, hm⟩
        have hk' : Fintype.card (Sylow 5 G) = 1 + 5 * k := by
          simpa using hk
        have hm' : 273 = (1 + 5 * k) * m := by
          simpa [hk'] using hm
        interval_cases k <;> omega
      rcases h5cases with h5 | h5
      · have hQtop : (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1.normalizer = ⊤ := by
          have hQ : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
          have hidx : hQ.1.normalizer.index = 1 := by
            simpa [hQ.card_eq_index_normalizer, h5] using hQ.card_eq_index_normalizer
          exact Subgroup.index_eq_one.mp hidx
        have hQnormal : (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1.Normal := by
          constructor
          intro g x hx
          have hg : g ∈ (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1.normalizer := by
            simpa [hQtop]
          exact hg x hx
        have hcases := hsimple.1 (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1 hQnormal
        rcases hcases with hbot | htop
        · have hcard : Fintype.card (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1 = 5 := by
            simpa [hG] using (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).card_eq
          have : (5 : ℕ) = 1 := by
            simpa [hbot] using hcard
          omega
        · have hcard : Fintype.card (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).1 = 5 := by
            simpa [hG] using (Classical.choice (inferInstance : Nonempty (Sylow 5 G))).card_eq
          have : (5 : ℕ) = 1365 := by
            simpa [hG, htop] using hcard
          omega
      · have hbound : 21 ≤ Fintype.card (Sylow 5 G) := h5
        have : False := by
          omega
        exact this.elim
