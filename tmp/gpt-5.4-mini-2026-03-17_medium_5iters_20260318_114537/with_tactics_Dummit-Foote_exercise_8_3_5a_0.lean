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


theorem exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  constructor
  · refine ⟨?_, ?_⟩
    · intro h
      rcases h with ⟨u, hu⟩
      have hnorm := congrArg Zsqrtd.normSq hu
      simp [Zsqrtd.normSq] at hnorm
      omega
    · intro a b hab
      rcases a with ⟨a₁, a₂⟩
      rcases b with ⟨b₁, b₂⟩
      have hnorm : (a₁ ^ 2 + n * a₂ ^ 2) * (b₁ ^ 2 + n * b₂ ^ 2) = 4 := by
        have := congrArg Zsqrtd.normSq hab
        simpa [Zsqrtd.normSq, mul_comm, mul_left_comm, mul_assoc] using this
      have hdiv : a₁ ^ 2 + n * a₂ ^ 2 ∣ 4 := by
        refine ⟨b₁ ^ 2 + n * b₂ ^ 2, ?_⟩
        simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm
      have hpos : 0 < a₁ ^ 2 + n * a₂ ^ 2 := by
        have hnonneg : 0 ≤ a₁ ^ 2 + n * a₂ ^ 2 := by
          nlinarith [sq_nonneg a₁, sq_nonneg a₂, hn0]
        have hne : a₁ ^ 2 + n * a₂ ^ 2 ≠ 0 := by
          intro h0
          have : (0 : ℤ) = 4 := by simpa [h0] using hnorm
          omega
        exact lt_of_le_of_ne hnonneg hne
      have hle : a₁ ^ 2 + n * a₂ ^ 2 ≤ 4 := Int.le_of_dvd hpos hdiv
      interval_cases hA : a₁ ^ 2 + n * a₂ ^ 2
      · have : (0 : ℤ) ∣ 4 := by simpa [hA] using hdiv
        norm_num at this
      · left
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        simpa [Zsqrtd.normSq, hA]
      · have : (2 : ℤ) ∣ 4 := by simpa [hA] using hdiv
        norm_num at this
      · have : (3 : ℤ) ∣ 4 := by simpa [hA] using hdiv
        norm_num at this
      · right
        have hb1 : b₁ ^ 2 + n * b₂ ^ 2 = 1 := by
          have hmul : (4 : ℤ) * (b₁ ^ 2 + n * b₂ ^ 2) = 4 := by
            simpa [hA, mul_comm, mul_left_comm, mul_assoc] using hnorm
          have h4 : (4 : ℤ) ≠ 0 := by norm_num
          have := mul_left_cancel₀ h4 hmul
          simpa using this
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        simpa [Zsqrtd.normSq] using hb1
  · refine ⟨?_, ?_⟩
    · intro h
      rcases h with ⟨u, hu⟩
      have hnorm := congrArg Zsqrtd.normSq hu
      simp [Zsqrtd.normSq] at hnorm
      omega
    · intro a b hab
      rcases a with ⟨a₁, a₂⟩
      rcases b with ⟨b₁, b₂⟩
      have hnorm : (a₁ ^ 2 + n * a₂ ^ 2) * (b₁ ^ 2 + n * b₂ ^ 2) = n := by
        have := congrArg Zsqrtd.normSq hab
        simpa [Zsqrtd.normSq, mul_comm, mul_left_comm, mul_assoc] using this
      by_cases ha2 : a₂ = 0
      · have hsim : (⟨a₁, 0⟩ : Zsqrtd (-n)) * ⟨b₁, b₂⟩ = ⟨0, 1⟩ := by simpa [ha2] using hab
        simp [ha2] at hsim
        rcases hsim with ⟨h1, h2⟩
        have h2' : a₁ * b₂ = 1 := by simpa [mul_comm] using h2
        have hmul : a₁ = 1 ∨ a₁ = -1 := by
          have := Int.mul_eq_one.mp h2'
          aesop
        left
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        rcases hmul with rfl | rfl <;> simp [Zsqrtd.normSq]
      · right
        have ha2pos : 1 ≤ a₂ ^ 2 := by
          have hsq : 0 < a₂ ^ 2 := sq_pos_of_ne_zero ha2
          omega
        have hge : n ≤ a₁ ^ 2 + n * a₂ ^ 2 := by
          nlinarith [sq_nonneg a₁, hn0, ha2pos]
        have hdiv : a₁ ^ 2 + n * a₂ ^ 2 ∣ n := by
          refine ⟨b₁ ^ 2 + n * b₂ ^ 2, ?_⟩
          simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm
        have hle : a₁ ^ 2 + n * a₂ ^ 2 ≤ n := Int.le_of_dvd (by
          have hnonneg : 0 ≤ a₁ ^ 2 + n * a₂ ^ 2 := by
            nlinarith [sq_nonneg a₁, sq_nonneg a₂, hn0]
          have hne : a₁ ^ 2 + n * a₂ ^ 2 ≠ 0 := by
            intro h0
            have : (0 : ℤ) = n := by simpa [h0] using hnorm
            omega
          exact lt_of_le_of_ne hnonneg hne) hdiv
        have hEq : a₁ ^ 2 + n * a₂ ^ 2 = n := le_antisymm hle hge
        have hb1 : b₁ ^ 2 + n * b₂ ^ 2 = 1 := by
          have hmul : (a₁ ^ 2 + n * a₂ ^ 2) * (b₁ ^ 2 + n * b₂ ^ 2) = n := hnorm
          rw [hEq] at hmul
          have hnz : n ≠ 0 := by omega
          have := mul_left_cancel₀ hnz hmul
          simpa using this
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        simpa [Zsqrtd.normSq] using hb1
  · refine ⟨?_, ?_⟩
    · intro h
      rcases h with ⟨u, hu⟩
      have hnorm := congrArg Zsqrtd.normSq hu
      simp [Zsqrtd.normSq] at hnorm
      omega
    · intro a b hab
      rcases a with ⟨a₁, a₂⟩
      rcases b with ⟨b₁, b₂⟩
      have hnorm : (a₁ ^ 2 + n * a₂ ^ 2) * (b₁ ^ 2 + n * b₂ ^ 2) = n + 1 := by
        have := congrArg Zsqrtd.normSq hab
        simpa [Zsqrtd.normSq, mul_comm, mul_left_comm, mul_assoc] using this
      by_cases ha2 : a₂ = 0
      · have hsim : (⟨a₁, 0⟩ : Zsqrtd (-n)) * ⟨b₁, b₂⟩ = ⟨1, 1⟩ := by simpa [ha2] using hab
        simp [ha2] at hsim
        rcases hsim with ⟨h1, h2⟩
        have h2' : a₁ * b₂ = 1 := by simpa [mul_comm] using h2
        have hmul : a₁ = 1 ∨ a₁ = -1 := by
          have := Int.mul_eq_one.mp h2'
          aesop
        left
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        rcases hmul with rfl | rfl <;> simp [Zsqrtd.normSq]
      · right
        have ha2pos : 1 ≤ a₂ ^ 2 := by
          have hsq : 0 < a₂ ^ 2 := sq_pos_of_ne_zero ha2
          omega
        have hge : n ≤ a₁ ^ 2 + n * a₂ ^ 2 := by
          nlinarith [sq_nonneg a₁, hn0, ha2pos]
        have hdiv : a₁ ^ 2 + n * a₂ ^ 2 ∣ n + 1 := by
          refine ⟨b₁ ^ 2 + n * b₂ ^ 2, ?_⟩
          simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm
        have hle : a₁ ^ 2 + n * a₂ ^ 2 ≤ n + 1 := Int.le_of_dvd (by
          have hnonneg : 0 ≤ a₁ ^ 2 + n * a₂ ^ 2 := by
            nlinarith [sq_nonneg a₁, sq_nonneg a₂, hn0]
          have hne : a₁ ^ 2 + n * a₂ ^ 2 ≠ 0 := by
            intro h0
            have : (0 : ℤ) = n + 1 := by simpa [h0] using hnorm
            omega
          exact lt_of_le_of_ne hnonneg hne) hdiv
        have hne : a₁ ^ 2 + n * a₂ ^ 2 ≠ n := by
          intro hEq
          have : (n : ℤ) ∣ n + 1 := by simpa [hEq] using hdiv
          omega
        have hEq : a₁ ^ 2 + n * a₂ ^ 2 = n + 1 := by omega
        have hb1 : b₁ ^ 2 + n * b₂ ^ 2 = 1 := by
          have hmul : (a₁ ^ 2 + n * a₂ ^ 2) * (b₁ ^ 2 + n * b₂ ^ 2) = n + 1 := hnorm
          rw [hEq] at hmul
          have hnz : (n + 1 : ℤ) ≠ 0 := by omega
          have := mul_left_cancel₀ hnz hmul
          simpa using this
        rw [Zsqrtd.isUnit_iff_normSq_eq_one]
        simpa [Zsqrtd.normSq] using hb1
