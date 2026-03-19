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


theorem exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by
  classical
  have hpair :
      ∀ n : ℕ, ∀ s : Finset Kˣ, s.card ≤ n →
        (∀ x ∈ s, x⁻¹ ∈ s) →
        (∀ x ∈ s, x ≠ x⁻¹) →
        ∏ x in s, (x : K) = 1 := by
    intro n
    induction n with
    | zero =>
        intro s hs hsinv hsneq
        have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
        simp [hs0]
    | succ n ih =>
        intro s hs hsinv hsneq
        by_cases hle : s.card ≤ n
        · exact ih s hle hsinv hsneq
        · have hcard : s.card = n + 1 := by omega
          have hpos : 0 < s.card := by omega
          rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
          let b : Kˣ := a⁻¹
          have hb : b ∈ s := by
            simpa [b] using hsinv a ha
          have hab : b ≠ a := by
            intro h
            apply hsneq a ha
            simpa [b] using h
          have hb' : b ∈ s.erase a := by
            simpa [Finset.mem_erase, hab] using hb
          let s' : Finset Kˣ := (s.erase a).erase b
          have hs' : ∀ x ∈ s', x⁻¹ ∈ s' := by
            intro x hx
            have hx1 : x ∈ s.erase a := (Finset.mem_erase.mp hx).1
            have hxb : x ≠ b := (Finset.mem_erase.mp hx).2
            have hxa : x ≠ a := (Finset.mem_erase.mp hx1).2
            have hxS : x ∈ s := by
              simpa [Finset.mem_erase] using hx1
            have hxinvS : x⁻¹ ∈ s := hsinv x hxS
            have hxinv_a : x⁻¹ ≠ a := by
              intro h
              apply hxb
              have := congrArg Inv.inv h
              simpa [b] using this
            have hxinv_b : x⁻¹ ≠ b := by
              intro h
              apply hxa
              have := congrArg Inv.inv h
              simpa [b] using this
            have hxinv1 : x⁻¹ ∈ s.erase a := by
              simpa [Finset.mem_erase, hxinv_a] using hxinvS
            simpa [s', Finset.mem_erase, hxinv_b] using hxinv1
          have hs'neq : ∀ x ∈ s', x ≠ x⁻¹ := by
            intro x hx hxeq
            have hx1 : x ∈ s.erase a := (Finset.mem_erase.mp hx).1
            have hxS : x ∈ s := by
              simpa [Finset.mem_erase] using hx1
            exact hsneq x hxS hxeq
          have hs'card : s'.card ≤ n := by
            have h1 : (s.erase a).card + 1 = s.card := by
              simpa using (Finset.card_erase_add_one (s := s) (a := a) ha)
            have h2 : s'.card + 1 = (s.erase a).card := by
              simpa [s'] using
                (Finset.card_erase_add_one (s := s.erase a) (a := b) hb')
            omega
          have hprod' : ∏ x in s', (x : K) = 1 := ih s' hs'card hs' hs'neq
          have hprod1 : ∏ x in s, (x : K) = (a : K) * ∏ x in s.erase a, (x : K) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Finset.prod_erase (s := s) (a := a) (f := fun x : Kˣ => (x : K)) ha)
          have hprod2 : ∏ x in s.erase a, (x : K) = (b : K) * ∏ x in s', (x : K) := by
            simpa [s', mul_comm, mul_left_comm, mul_assoc, b] using
              (Finset.prod_erase (s := s.erase a) (a := b) (f := fun x : Kˣ => (x : K)) hb')
          calc
            ∏ x in s, (x : K) = (a : K) * ((b : K) * ∏ x in s', (x : K)) := by
              rw [hprod1, hprod2]
            _ = 1 := by
              simp [b, hprod']
  by_cases hneg : (-1 : Kˣ) = 1
  · have hnegK : (-1 : K) = 1 := congrArg (fun u : Kˣ => (u : K)) hneg
    let s : Finset Kˣ := (Finset.univ : Finset Kˣ).erase 1
    have hsinv : ∀ x ∈ s, x⁻¹ ∈ s := by
      intro x hx
      have hxne1 : x ≠ 1 := (Finset.mem_erase.mp hx).2
      have hxinvne1 : x⁻¹ ≠ 1 := by
        intro h
        exact hxne1 (by ext; simpa using congrArg Inv.inv h)
      simpa [s, Finset.mem_erase, hxinvne1] using (by simp : x⁻¹ ∈ (Finset.univ : Finset Kˣ))
    have hsneq : ∀ x ∈ s, x ≠ x⁻¹ := by
      intro x hx hxeq
      have hxne1 : x ≠ 1 := (Finset.mem_erase.mp hx).2
      have hxmul : (x : K) * x = 1 := by
        calc
          (x : K) * x = (x : K) * (x⁻¹ : K) := by rw [hxeq]
          _ = 1 := by simp
      have hfactor : ((x : K) - 1) * ((x : K) + 1) = 0 := by
        rw [show ((x : K) - 1) * ((x : K) + 1) = (x : K) * x - 1 by ring, hxmul]
        norm_num
      rcases mul_eq_zero.mp hfactor with hx1 | hxneg'
      · exact hxne1 (by ext; exact sub_eq_zero.mp hx1)
      · exact hxne1 (by
          ext
          simpa [hnegK] using (eq_neg_of_add_eq_zero_left hxneg'))
    have hsprod : ∏ x in s, (x : K) = 1 := hpair s.card s le_rfl hsinv hsneq
    have hfull : ∏ x : Kˣ, (x : K) = (1 : K) * ∏ x in s, (x : K) := by
      simpa [s, mul_comm, mul_left_comm, mul_assoc] using
        (Finset.prod_erase (s := (Finset.univ : Finset Kˣ)) (a := (1 : Kˣ))
          (f := fun x : Kˣ => (x : K)) (by simp))
    calc
      ∏ x : Kˣ, (x : K) = (1 : K) * ∏ x in s, (x : K) := hfull
      _ = -1 := by simp [hsprod, hnegK]
  · let t : Finset Kˣ := ((Finset.univ : Finset Kˣ).erase 1).erase (-1)
    have htinv : ∀ x ∈ t, x⁻¹ ∈ t := by
      intro x hx
      have hx1 : x ∈ (Finset.univ : Finset Kˣ).erase 1 := (Finset.mem_erase.mp hx).1
      have hxneNeg : x ≠ (-1 : Kˣ) := (Finset.mem_erase.mp hx).2
      have hxne1 : x ≠ 1 := (Finset.mem_erase.mp hx1).2
      have hxinvne1 : x⁻¹ ≠ 1 := by
        intro h
        exact hxne1 (by ext; simpa using congrArg Inv.inv h)
      have hxinvneNeg : x⁻¹ ≠ (-1 : Kˣ) := by
        intro h
        exact hxneNeg (by ext; simpa using congrArg Inv.inv h)
      have hxinv1 : x⁻¹ ∈ (Finset.univ : Finset Kˣ).erase 1 := by
        simpa [Finset.mem_erase, hxinvne1] using (by simp : x⁻¹ ∈ (Finset.univ : Finset Kˣ))
      simpa [t, Finset.mem_erase, hxinvneNeg] using hxinv1
    have htneq : ∀ x ∈ t, x ≠ x⁻¹ := by
      intro x hx hxeq
      have hx1 : x ∈ (Finset.univ : Finset Kˣ).erase 1 := (Finset.mem_erase.mp hx).1
      have hxne1 : x ≠ 1 := (Finset.mem_erase.mp hx1).2
      have hxneNeg : x ≠ (-1 : Kˣ) := (Finset.mem_erase.mp hx).2
      have hxmul : (x : K) * x = 1 := by
        calc
          (x : K) * x = (x : K) * (x⁻¹ : K) := by rw [hxeq]
          _ = 1 := by simp
      have hfactor : ((x : K) - 1) * ((x : K) + 1) = 0 := by
        rw [show ((x : K) - 1) * ((x : K) + 1) = (x : K) * x - 1 by ring, hxmul]
        norm_num
      rcases mul_eq_zero.mp hfactor with hx1' | hxneg'
      · exact hxne1 (by ext; exact sub_eq_zero.mp hx1')
      · exact hxneNeg (by ext; exact eq_neg_of_add_eq_zero_left hxneg')
    have htprod : ∏ x in t, (x : K) = 1 := hpair t.card t le_rfl htinv htneq
    have hfull1 : ∏ x : Kˣ, (x : K) = (1 : K) * ∏ x in (Finset.univ : Finset Kˣ).erase 1, (x : K) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.prod_erase (s := (Finset.univ : Finset Kˣ)) (a := (1 : Kˣ))
          (f := fun x : Kˣ => (x : K)) (by simp))
    have hmem : (-1 : Kˣ) ∈ (Finset.univ : Finset Kˣ).erase 1 := by
      simpa [Finset.mem_erase, hneg] using (by simp : (-1 : Kˣ) ∈ (Finset.univ : Finset Kˣ))
    have hfull2 : ∏ x in (Finset.univ : Finset Kˣ).erase 1, (x : K) = (-1 : K) * ∏ x in t, (x : K) := by
      simpa [t, mul_comm, mul_left_comm, mul_assoc] using
        (Finset.prod_erase (s := (Finset.univ : Finset Kˣ).erase 1) (a := (-1 : Kˣ))
          (f := fun x : Kˣ => (x : K)) hmem)
    calc
      ∏ x : Kˣ, (x : K) = (1 : K) * ∏ x in (Finset.univ : Finset Kˣ).erase 1, (x : K) := hfull1
      _ = (-1 : K) * ∏ x in t, (x : K) := by
        rw [hfull2]
        ring
      _ = -1 := by simp [htprod]
