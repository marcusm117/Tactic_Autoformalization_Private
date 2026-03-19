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


theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  let f : Polynomial ℤ := X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1
  change Irreducible f
  have hf_monic : f.Monic := by
    simpa [f] using
      (show (X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).Monic by decide)
  have hf_deg : f.natDegree = 4 := by
    simpa [f] using
      (show (X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 : Polynomial ℤ).natDegree = 4 by decide)
  have unit_of_monic_natDegree_zero :
      ∀ {p : Polynomial ℤ}, p.Monic → p.natDegree = 0 → IsUnit p := by
    intro p hp hpdeg
    have hp1 : p = 1 := by
      ext n
      rcases n with _ | n
      · change p.coeff 0 = (1 : Polynomial ℤ).coeff 0
        simpa [hpdeg] using hp.coeff_natDegree
      · have hz : p.coeff (n + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        change p.coeff (n + 1) = (1 : Polynomial ℤ).coeff (n + 1)
        simpa [hz]
    simpa [hp1] using (isUnit_one : IsUnit (1 : Polynomial ℤ))
  have linear_impossible :
      ∀ {p q : Polynomial ℤ}, p.Monic → p.natDegree = 1 → f = p * q → False := by
    intro p q hp hpdeg hfac
    have hlin : p = X + C (p.coeff 0) := by
      ext n
      rcases n with _ | _ | n
      · change p.coeff 0 = (X + C (p.coeff 0)).coeff 0
        simp [Polynomial.coeff_add]
      · have h1c : p.coeff 1 = 1 := by
          simpa [hpdeg] using hp.coeff_natDegree
        change p.coeff 1 = (X + C (p.coeff 0)).coeff 1
        simp [Polynomial.coeff_add, h1c]
      · have hz : p.coeff (n + 2) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        change p.coeff (n + 2) = (X + C (p.coeff 0)).coeff (n + 2)
        simp [Polynomial.coeff_add, hz]
    have hconst : p.coeff 0 * q.coeff 0 = 1 := by
      have h0 := congrArg (fun r : Polynomial ℤ => r.coeff 0) hfac
      rw [hlin] at h0
      simp [Polynomial.coeff_add] at h0
      linarith
    have hpdiv : p.coeff 0 ∣ (1 : ℤ) := by
      refine ⟨q.coeff 0, ?_⟩
      simpa [mul_comm] using hconst
    have hc : p.coeff 0 = 1 ∨ p.coeff 0 = -1 := Int.eq_one_or_neg_one_of_dvd_one hpdiv
    cases hc with
    | inl hc =>
        have hroot : p.eval (-1) = 0 := by
          rw [hlin, hc]
          simp
        have hf0 : f.eval (-1) = 0 := by
          rw [hfac, Polynomial.eval_mul, hroot, zero_mul]
        have hne : f.eval (-1 : ℤ) ≠ 0 := by
          norm_num [f]
        exact hne hf0
    | inr hc =>
        have hroot : p.eval 1 = 0 := by
          rw [hlin, hc]
          simp
        have hf0 : f.eval (1 : ℤ) = 0 := by
          rw [hfac, Polynomial.eval_mul, hroot, zero_mul]
        have hne : f.eval (1 : ℤ) ≠ 0 := by
          norm_num [f]
        exact hne hf0
  have quadratic_impossible :
      ∀ {p q : Polynomial ℤ},
        p.Monic → q.Monic → p.natDegree = 2 → q.natDegree = 2 → f = p * q → False := by
    intro p q hp hq hpdeg hqdeg hfac
    have hpquad : p = X^2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      ext n
      rcases n with _ | _ | _ | n
      · change p.coeff 0 = (X^2 + C (p.coeff 1) * X + C (p.coeff 0)).coeff 0
        simp [Polynomial.coeff_add]
      · change p.coeff 1 = (X^2 + C (p.coeff 1) * X + C (p.coeff 0)).coeff 1
        simp [Polynomial.coeff_add]
      · have h2c : p.coeff 2 = 1 := by
          simpa [hpdeg] using hp.coeff_natDegree
        change p.coeff 2 = (X^2 + C (p.coeff 1) * X + C (p.coeff 0)).coeff 2
        simp [Polynomial.coeff_add, h2c]
      · have hz : p.coeff (n + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        change p.coeff (n + 3) = (X^2 + C (p.coeff 1) * X + C (p.coeff 0)).coeff (n + 3)
        simp [Polynomial.coeff_add, hz]
    have hqquad : q = X^2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      ext n
      rcases n with _ | _ | _ | n
      · change q.coeff 0 = (X^2 + C (q.coeff 1) * X + C (q.coeff 0)).coeff 0
        simp [Polynomial.coeff_add]
      · change q.coeff 1 = (X^2 + C (q.coeff 1) * X + C (q.coeff 0)).coeff 1
        simp [Polynomial.coeff_add]
      · have h2c : q.coeff 2 = 1 := by
          simpa [hqdeg] using hq.coeff_natDegree
        change q.coeff 2 = (X^2 + C (q.coeff 1) * X + C (q.coeff 0)).coeff 2
        simp [Polynomial.coeff_add, h2c]
      · have hz : q.coeff (n + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        change q.coeff (n + 3) = (X^2 + C (q.coeff 1) * X + C (q.coeff 0)).coeff (n + 3)
        simp [Polynomial.coeff_add, hz]
    have hfac' :
        f =
          X^4 + C (p.coeff 1 + q.coeff 1) * X^3 +
            C (p.coeff 1 * q.coeff 1 + p.coeff 0 + q.coeff 0) * X^2 +
            C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X +
            C (p.coeff 0 * q.coeff 0) := by
      calc
        f = p * q := hfac
        _ =
            (X^2 + C (p.coeff 1) * X + C (p.coeff 0)) *
              (X^2 + C (q.coeff 1) * X + C (q.coeff 0)) := by
              rw [hpquad, hqquad]
        _ =
            X^4 + C (p.coeff 1 + q.coeff 1) * X^3 +
              C (p.coeff 1 * q.coeff 1 + p.coeff 0 + q.coeff 0) * X^2 +
              C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X +
              C (p.coeff 0 * q.coeff 0) := by
              ring
    have h0 : p.coeff 0 * q.coeff 0 = 1 := by
      have h := congrArg (fun r : Polynomial ℤ => r.coeff 0) hfac'
      simp [f, Polynomial.coeff_add] at h
      linarith
    have h1 : p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1 = 2 := by
      have h := congrArg (fun r : Polynomial ℤ => r.coeff 1) hfac'
      simp [f, Polynomial.coeff_add] at h
      linarith
    have h3 : p.coeff 1 + q.coeff 1 = 4 := by
      have h := congrArg (fun r : Polynomial ℤ => r.coeff 3) hfac'
      simp [f, Polynomial.coeff_add] at h
      linarith
    have hpdiv : p.coeff 0 ∣ (1 : ℤ) := by
      refine ⟨q.coeff 0, ?_⟩
      simpa [mul_comm] using h0
    have hp0 : p.coeff 0 = 1 ∨ p.coeff 0 = -1 := Int.eq_one_or_neg_one_of_dvd_one hpdiv
    cases hp0 with
    | inl hp0 =>
        have hq0 : q.coeff 0 = 1 := by
          nlinarith [h0, hp0]
        have h1' := h1
        have h3' := h3
        simp [hp0, hq0] at h1' h3'
        nlinarith
    | inr hp0 =>
        have hq0 : q.coeff 0 = -1 := by
          nlinarith [h0, hp0]
        have h1' := h1
        have h3' := h3
        simp [hp0, hq0] at h1' h3'
        nlinarith
  constructor
  · intro hunit
    have h0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    have hmonic : (a * b).Monic := by
      simpa [hab] using hf_monic
    have ha_monic : a.Monic := hmonic.of_mul_right
    have hb_monic : b.Monic := hmonic.of_mul_left
    have hdeg' : (a * b).natDegree = a.natDegree + b.natDegree := by
      exact Polynomial.natDegree_mul' ha_monic.ne_zero hb_monic.ne_zero
    have hdeg : a.natDegree + b.natDegree = 4 := by
      simpa [hab, hf_deg] using hdeg'.symm
    have ha_le : a.natDegree ≤ 4 := by
      omega
    by_cases ha0 : a.natDegree = 0
    · left
      exact unit_of_monic_natDegree_zero ha_monic ha0
    · by_cases ha1 : a.natDegree = 1
      · exfalso
        exact linear_impossible ha_monic ha1 hab
      · by_cases ha2 : a.natDegree = 2
        · have hb2 : b.natDegree = 2 := by
            omega
          exfalso
          exact quadratic_impossible ha_monic hb_monic ha2 hb2 hab
        · by_cases ha3 : a.natDegree = 3
          · have hb1 : b.natDegree = 1 := by
              omega
            exfalso
            exact linear_impossible hb_monic hb1 (by simpa [mul_comm] using hab)
          · have hb0 : b.natDegree = 0 := by
              omega
            right
            exact unit_of_monic_natDegree_zero hb_monic hb0
