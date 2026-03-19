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


theorem exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  classical
  let p : Polynomial F := X ^ 2 + X + 1
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hx01 : ∀ x : F, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push_neg at hx
    have hcard3 : ({x, 0, 1} : Finset F).card = 3 := by
      simp [hx.1, hx.2, h01]
    have hle : ({x, 0, 1} : Finset F).card ≤ Fintype.card F := Finset.card_le_univ _
    rw [hcard3, hF] at hle
    omega
  have h11 : (1 : F) + 1 = 0 := by
    rcases hx01 ((1 : F) + 1) with h | h
    · exact h
    · exfalso
      have h' : (1 : F) + 1 = 0 + 1 := by
        simpa using h
      have : (1 : F) = 0 := add_right_cancel h'
      exact one_ne_zero this
  have hpdeg : p.natDegree = 2 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · intro n hn
      have h2 : n ≠ 2 := by omega
      have h2' : 2 ≠ n := by exact Ne.symm h2
      have h1 : n ≠ 1 := by omega
      have h1' : 1 ≠ n := by exact Ne.symm h1
      have h0 : n ≠ 0 := by omega
      have h0' : 0 ≠ n := by exact Ne.symm h0
      simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        h2, h2', h1, h1', h0, h0']
    · simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hpdeg
    simp at hpdeg
  have hunit_of_natDegree_zero :
      ∀ q : Polynomial F, q ≠ 0 → q.natDegree = 0 → IsUnit q := by
    intro q hq hqdeg
    have hqC : q = C (q.coeff 0) := by
      ext n
      cases n with
      | zero =>
          simp [Polynomial.coeff_C]
      | succ n =>
          have hlt : q.natDegree < n.succ := by
            simpa [hqdeg]
          have hz : q.coeff n.succ = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
          simp [Polynomial.coeff_C, hz]
    have hc : q.coeff 0 ≠ 0 := by
      intro hc0
      apply hq
      rw [hqC, hc0]
      simp
    rw [hqC]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  change Irreducible p
  constructor
  · intro hpunit
    have : p.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hpunit
    rw [hpdeg] at this
    omega
  · intro a b hab
    by_cases hua : IsUnit a
    · exact Or.inl hua
    by_cases hub : IsUnit b
    · exact Or.inr hub
    exfalso
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hab
      exact hp0 hab
    have hb0 : b ≠ 0 := by
      intro hb
      rw [hb, mul_zero] at hab
      exact hp0 hab
    have hmuldeg : (a * b).natDegree = a.natDegree + b.natDegree :=
      Polynomial.natDegree_mul' ha0 hb0
    have hsum : a.natDegree + b.natDegree = 2 := by
      rw [← hmuldeg, ← hab, hpdeg]
    have hapos : 0 < a.natDegree := by
      apply Nat.pos_of_ne_zero
      intro h0
      exact hua (hunit_of_natDegree_zero a ha0 h0)
    have hbpos : 0 < b.natDegree := by
      apply Nat.pos_of_ne_zero
      intro h0
      exact hub (hunit_of_natDegree_zero b hb0 h0)
    have hadeg1 : a.natDegree = 1 := by
      omega
    have hbdeg1 : b.natDegree = 1 := by
      omega
    have ha1_ne : a.coeff 1 ≠ 0 := by
      simpa [hadeg1] using Polynomial.coeff_natDegree_ne_zero ha0
    have hb1_ne : b.coeff 1 ≠ 0 := by
      simpa [hbdeg1] using Polynomial.coeff_natDegree_ne_zero hb0
    have ha1 : a.coeff 1 = 1 := by
      rcases hx01 (a.coeff 1) with h | h
      · exact False.elim (ha1_ne h)
      · exact h
    have hb1 : b.coeff 1 = 1 := by
      rcases hx01 (b.coeff 1) with h | h
      · exact False.elim (hb1_ne h)
      · exact h
    have hcoeff0 : (1 : F) = a.coeff 0 * b.coeff 0 := by
      have h := congrArg (fun q : Polynomial F => q.coeff 0) hab
      simpa [p, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_C] using h
    have hcoeff1 : (1 : F) = a.coeff 0 + b.coeff 0 := by
      have h := congrArg (fun q : Polynomial F => q.coeff 1) hab
      simpa [p, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_C, ha1, hb1] using h
    rcases hx01 (a.coeff 0) with ha0c | ha0c
    · rw [ha0c, zero_mul] at hcoeff0
      exact one_ne_zero hcoeff0
    · rcases hx01 (b.coeff 0) with hb0c | hb0c
      · rw [hb0c, mul_zero] at hcoeff0
        exact one_ne_zero hcoeff0
      · rw [ha0c, hb0c, h11] at hcoeff1
        exact one_ne_zero hcoeff1
