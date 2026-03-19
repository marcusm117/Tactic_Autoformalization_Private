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
  let q : Polynomial ℤ := X^4 + C (-2) * X + C 2
  change Irreducible f
  have hcomp : f.comp (X - 1) = q := by
    simp [f, q, sub_eq_add_neg]
    ring
  have hq_coeff4 : q.coeff 4 = 1 := by
    simp [q, Polynomial.coeff_add]
  have hq_ne : q ≠ 0 := by
    intro h
    have h4 := congrArg (fun p : Polynomial ℤ => p.coeff 4) h
    simpa [hq_coeff4] using h4
  have hq_coeff_gt : ∀ n : ℕ, 4 < n → q.coeff n = 0 := by
    intro n hn
    have h4 : n ≠ 4 := by omega
    have h1 : n ≠ 1 := by omega
    have h0 : n ≠ 0 := by omega
    simp [q, Polynomial.coeff_add, h4, h1, h0]
  have hq_deg_le : q.natDegree ≤ 4 := by
    by_contra hgt
    have hz : q.coeff q.natDegree = 0 := by
      apply hq_coeff_gt
      omega
    have hlc_ne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_ne
    have hlc0 : q.leadingCoeff = 0 := by
      rwa [← Polynomial.coeff_natDegree] at hz
    exact hlc_ne hlc0
  have hq_deg_ge : 4 ≤ q.natDegree := by
    exact Polynomial.le_natDegree_of_ne_zero hq_coeff4
  have hq_deg : q.natDegree = 4 := by
    omega
  have hq_monic : q.Monic := by
    unfold Polynomial.Monic
    rw [← Polynomial.coeff_natDegree q, hq_deg]
    simpa [q, Polynomial.coeff_add]
  have unit_of_monic_natDegree_zero :
      ∀ {p : Polynomial ℤ}, p.Monic → p.natDegree = 0 → IsUnit p := by
    intro p hp hpdeg
    have hp1 : p = 1 := by
      ext n
      rcases n with _ | n
      · simpa [hpdeg] using hp.coeff_natDegree
      · have hz : p.coeff (n + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        rw [hz]
        simp
    simpa [hp1] using (isUnit_one : IsUnit (1 : Polynomial ℤ))
  have linear_impossible :
      ∀ {p r : Polynomial ℤ}, p.Monic → p.natDegree = 1 → q = p * r → False := by
    intro p r hp hpdeg hfac
    set c : ℤ := p.coeff 0
    have hlin : p = X + C c := by
      ext n
      rcases n with _ | _ | n
      · simp [c, Polynomial.coeff_add]
      · have h1c : p.coeff 1 = 1 := by
          simpa [hpdeg] using hp.coeff_natDegree
        simp [c, Polynomial.coeff_add, h1c]
      · have hz : p.coeff (n + 2) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        rw [hz]
        simp [c, Polynomial.coeff_add]
    have hroot : p.eval (-c) = 0 := by
      rw [hlin]
      simp [c]
    have hqroot : q.eval (-c) = 0 := by
      rw [hfac, Polynomial.eval_mul, hroot, zero_mul]
    have hEq : c ^ 4 + 2 * c + 2 = 0 := by
      simpa [q, c] using hqroot
    have hc_cases : c ≤ -2 ∨ c = -1 ∨ 0 ≤ c := by
      omega
    rcases hc_cases with hc | hc | hc
    · nlinarith [hEq, hc]
    · nlinarith [hEq, hc]
    · nlinarith [hEq, hc]
  have quadratic_impossible :
      ∀ {p r : Polynomial ℤ},
        p.Monic → r.Monic → p.natDegree = 2 → r.natDegree = 2 → q = p * r → False := by
    intro p r hp hr hpdeg hrdeg hfac
    set b : ℤ := p.coeff 0
    set d : ℤ := r.coeff 0
    have hpquad : p = X^2 + C (p.coeff 1) * X + C b := by
      ext n
      rcases n with _ | _ | _ | n
      · simp [b, Polynomial.coeff_add]
      · simp [b, Polynomial.coeff_add]
      · have h2c : p.coeff 2 = 1 := by
          simpa [hpdeg] using hp.coeff_natDegree
        simp [b, Polynomial.coeff_add, h2c]
      · have hz : p.coeff (n + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        rw [hz]
        simp [b, Polynomial.coeff_add]
    have hrquad : r = X^2 + C (r.coeff 1) * X + C d := by
      ext n
      rcases n with _ | _ | _ | n
      · simp [d, Polynomial.coeff_add]
      · simp [d, Polynomial.coeff_add]
      · have h2c : r.coeff 2 = 1 := by
          simpa [hrdeg] using hr.coeff_natDegree
        simp [d, Polynomial.coeff_add, h2c]
      · have hz : r.coeff (n + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        rw [hz]
        simp [d, Polynomial.coeff_add]
    have hfac' :
        q =
          X^4 + C (p.coeff 1 + r.coeff 1) * X^3 +
            C (p.coeff 1 * r.coeff 1 + b + d) * X^2 +
            C (p.coeff 1 * d + b * r.coeff 1) * X +
            C (b * d) := by
      calc
        q = p * r := hfac
        _ =
            (X^2 + C (p.coeff 1) * X + C b) *
              (X^2 + C (r.coeff 1) * X + C d) := by
              rw [hpquad, hrquad]
        _ =
            X^4 + C (p.coeff 1 + r.coeff 1) * X^3 +
              C (p.coeff 1 * r.coeff 1 + b + d) * X^2 +
              C (p.coeff 1 * d + b * r.coeff 1) * X +
              C (b * d) := by
              ring
    have h0 : b * d = 2 := by
      have h := congrArg (fun s : Polynomial ℤ => s.coeff 0) hfac'
      simp [q, b, d, Polynomial.coeff_add] at h
      nlinarith
    have h1 : p.coeff 1 * d + b * r.coeff 1 = -2 := by
      have h := congrArg (fun s : Polynomial ℤ => s.coeff 1) hfac'
      simp [q, b, d, Polynomial.coeff_add] at h
      nlinarith
    have h2 : p.coeff 1 * r.coeff 1 + b + d = 0 := by
      have h := congrArg (fun s : Polynomial ℤ => s.coeff 2) hfac'
      simp [q, b, d, Polynomial.coeff_add] at h
      nlinarith
    have h3 : p.coeff 1 + r.coeff 1 = 0 := by
      have h := congrArg (fun s : Polynomial ℤ => s.coeff 3) hfac'
      simp [q, b, d, Polynomial.coeff_add] at h
      linarith
    set u : ℤ := p.coeff 1
    have hr1 : r.coeff 1 = -u := by
      dsimp [u] at *
      linarith
    have hsum : b + d = u ^ 2 := by
      rw [hr1] at h2
      dsimp [u] at h2
      nlinarith
    have hdiff : u * (d - b) = -2 := by
      rw [hr1] at h1
      dsimp [u] at h1
      nlinarith
    have hdbsq : (d - b) ^ 2 = u ^ 4 - 8 := by
      nlinarith [h0, hsum]
    have hsq : (u * (d - b)) ^ 2 = 4 := by
      have hs := congrArg (fun z : ℤ => z ^ 2) hdiff
      nlinarith
    have hpoly : u ^ 2 * (u ^ 4 - 8) = 4 := by
      nlinarith [hsq, hdbsq]
    have hu_cases : u ≤ -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ 2 ≤ u := by
      omega
    rcases hu_cases with hu | hu | hu | hu | hu <;> nlinarith [hpoly, hu]
  have hq_irred : Irreducible q := by
    constructor
    · intro hu
      have : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      have hab_monic : (a * b).Monic := by
        simpa [hab] using hq_monic
      have ha_monic : a.Monic := hab_monic.of_mul_right
      have hb_monic : b.Monic := hab_monic.of_mul_left
      have hdeg : a.natDegree + b.natDegree = 4 := by
        simpa [hab, hq_deg] using
          (Polynomial.natDegree_mul' ha_monic.ne_zero hb_monic.ne_zero).symm
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
  constructor
  · intro hf_unit
    have hq_unit : IsUnit q := by
      simpa [hcomp] using hf_unit.map (Polynomial.compRingHom (X - 1))
    exact hq_irred.1 hq_unit
  · intro a b hab
    have hcompab : q = a.comp (X - 1) * b.comp (X - 1) := by
      calc
        q = f.comp (X - 1) := hcomp.symm
        _ = (a * b).comp (X - 1) := by rw [hab]
        _ = a.comp (X - 1) * b.comp (X - 1) := by rw [Polynomial.comp_mul]
    have hcancel : ∀ p : Polynomial ℤ, (p.comp (X - 1)).comp (X + 1) = p := by
      intro p
      rw [Polynomial.comp_assoc]
      have hlin : ((X - 1 : Polynomial ℤ).comp (X + 1)) = X := by
        simp [sub_eq_add_neg]
        ring
      rw [hlin]
      simpa using (Polynomial.comp_X p)
    rcases hq_irred.2 _ _ hcompab with ha | hb
    · left
      have h : IsUnit ((a.comp (X - 1)).comp (X + 1)) := by
        simpa using ha.map (Polynomial.compRingHom (X + 1))
      simpa [hcancel a] using h
    · right
      have h : IsUnit ((b.comp (X - 1)).comp (X + 1)) := by
        simpa using hb.map (Polynomial.compRingHom (X + 1))
      simpa [hcancel b] using h
