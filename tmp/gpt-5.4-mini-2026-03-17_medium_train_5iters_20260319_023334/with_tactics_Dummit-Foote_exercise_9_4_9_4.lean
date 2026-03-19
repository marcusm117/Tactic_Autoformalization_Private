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


theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  constructor
  · intro hp
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hp
    have hpdeg :
        (X ^ 2 - C (Zsqrtd.sqrtd : Zsqrtd 2) : Polynomial (Zsqrtd 2)).natDegree = 2 := by
      simp [pow_two]
    rw [hpdeg] at hdeg
    omega
  · intro f g hfg
    have hpdeg :
        (X ^ 2 - C (Zsqrtd.sqrtd : Zsqrtd 2) : Polynomial (Zsqrtd 2)).natDegree = 2 := by
      simp [pow_two]
    have hleadp :
        leadingCoeff (X ^ 2 - C (Zsqrtd.sqrtd : Zsqrtd 2) : Polynomial (Zsqrtd 2)) = 1 := by
      simp [pow_two]
    have hpnz : (X ^ 2 - C (Zsqrtd.sqrtd : Zsqrtd 2) : Polynomial (Zsqrtd 2)) ≠ 0 := by
      intro h
      have hcoeff :=
        congrArg (fun q : Polynomial (Zsqrtd 2) => q.coeff 2) h
      have : (1 : Zsqrtd 2) = 0 := by
        simpa [pow_two] using hcoeff
      exact one_ne_zero this
    have hf0 : f ≠ 0 := by
      intro hf0
      apply hpnz
      simpa [hf0] using hfg
    have hg0 : g ≠ 0 := by
      intro hg0
      apply hpnz
      simpa [hg0] using hfg
    have hdeg : natDegree f + natDegree g = 2 := by
      have hm := natDegree_mul hf0 hg0
      simpa [hfg, hpdeg] using hm
    by_cases hfdeg0 : natDegree f = 0
    · have hfC : f = Polynomial.C (f.coeff 0) := by
        simpa [hfdeg0] using (Polynomial.eq_C_of_natDegree_eq_zero hfdeg0)
      have hlead : f.coeff 0 * leadingCoeff g = 1 := by
        have h := congrArg Polynomial.leadingCoeff hfg
        simpa [hfC, hfdeg0, hleadp] using h
      have hunitcoeff : IsUnit (f.coeff 0) := by
        refine ⟨⟨f.coeff 0, leadingCoeff g, hlead, ?_⟩, rfl⟩
        simpa [mul_comm] using hlead
      have hfunit : IsUnit f := by
        rw [hfC]
        exact Polynomial.isUnit_C.mpr hunitcoeff
      exact Or.inl hfunit
    · by_cases hgdeg0 : natDegree g = 0
      · have hgC : g = Polynomial.C (g.coeff 0) := by
          simpa [hgdeg0] using (Polynomial.eq_C_of_natDegree_eq_zero hgdeg0)
        have hlead : g.coeff 0 * leadingCoeff f = 1 := by
          have h := congrArg Polynomial.leadingCoeff hfg
          simpa [hgC, hgdeg0, hleadp] using h
        have hunitcoeff : IsUnit (g.coeff 0) := by
          refine ⟨⟨g.coeff 0, leadingCoeff f, by simpa [mul_comm] using hlead, hlead⟩, rfl⟩
        have hgunit : IsUnit g := by
          rw [hgC]
          exact Polynomial.isUnit_C.mpr hunitcoeff
        exact Or.inr hgunit
      · have hf1 : natDegree f = 1 := by
          have hfpos : 0 < natDegree f := Nat.pos_of_ne_zero hfdeg0
          have hgpos : 0 < natDegree g := Nat.pos_of_ne_zero hgdeg0
          omega
        have hg1 : natDegree g = 1 := by
          have hfpos : 0 < natDegree f := Nat.pos_of_ne_zero hfdeg0
          have hgpos : 0 < natDegree g := Nat.pos_of_ne_zero hgdeg0
          omega
        have hlead : leadingCoeff f * leadingCoeff g = 1 := by
          have h := congrArg Polynomial.leadingCoeff hfg
          simpa [hleadp] using h
        have hunit : IsUnit (leadingCoeff f) := by
          refine ⟨⟨leadingCoeff f, leadingCoeff g, hlead, ?_⟩, rfl⟩
          simpa [mul_comm] using hlead
        rcases hunit with ⟨u, rfl⟩
        let x : Zsqrtd 2 := - (f.coeff 0) * ↑u⁻¹
        have hfexp :
            f = Polynomial.C (↑u) * Polynomial.X + Polynomial.C (f.coeff 0) := by
          simpa using (Polynomial.eq_C_mul_X_add_C_of_natDegree_eq_one hf1)
        have hu : (↑u : Zsqrtd 2) * ↑u⁻¹ = 1 := u.val_inv
        have hfroot : Polynomial.eval x f = 0 := by
          rw [hfexp]
          simp [x, hu, mul_comm, mul_left_comm, mul_assoc]
        have hproot : Polynomial.eval x (X ^ 2 - C (Zsqrtd.sqrtd : Zsqrtd 2)) = 0 := by
          rw [hfg]
          simp [hfroot]
        have hx0 : x ^ 2 - (Zsqrtd.sqrtd : Zsqrtd 2) = 0 := by
          simpa [pow_two] using hproot
        have hx : x ^ 2 = (Zsqrtd.sqrtd : Zsqrtd 2) := sub_eq_zero.mp hx0
        have hre := congrArg Zsqrtd.re hx
        have him := congrArg Zsqrtd.im hx
        simp [pow_two] at hre him
        nlinarith [sq_nonneg (x.re : ℤ), sq_nonneg (x.im : ℤ)]
