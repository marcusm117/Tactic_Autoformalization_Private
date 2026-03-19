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


theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  have hprime3 : ∀ n, n ≡ 3 [MOD 4] → ∃ p, p ∣ n ∧ Nat.Prime p ∧ p ≡ 3 [MOD 4] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hnmod4 : n % 4 = 3 := by
        simpa [Nat.ModEq] using hn
      have hgt1 : 1 < n := by
        have hdecomp := Nat.mod_add_div n 4
        rw [hnmod4] at hdecomp
        omega
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hgt1
      have hnot2 : p ≠ 2 := by
        intro hp2
        have h2div : 2 ∣ n := by
          simpa [hp2] using hpdvd
        have hmod2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2div
        have hodd : n % 2 = 1 := by
          have htmp := congrArg (fun x => x % 2) hnmod4
          omega
        omega
      have hmod2 : p % 2 = 1 := by
        simpa [Nat.ModEq] using hpprime.mod_two_eq_one hnot2
      have h13 : p % 4 = 1 ∨ p % 4 = 3 := by
        omega
      rcases hpdvd with ⟨m, hm⟩
      rcases h13 with h1 | h3
      · have hmpos : 0 < m := by
          by_contra hm0
          have hm0' : m = 0 := Nat.eq_zero_of_not_pos hm0
          rw [hm0'] at hm
          omega
        have hm_lt : m < n := by
          rw [hm]
          omega
        have hm_mod3 : m ≡ 3 [MOD 4] := by
          have hpm : p * m ≡ m [MOD 4] := by
            simpa using h1.mul_right m
          have hpn : p * m ≡ 3 [MOD 4] := by
            simpa [hm] using hn
          exact hpm.symm.trans hpn
        rcases ih m hm_lt hm_mod3 with ⟨q, hqdivm, hqprime, hqmod3⟩
        refine ⟨q, ?_, hqprime, hqmod3⟩
        have hmdivn : m ∣ n := by
          rw [hm]
          exact dvd_mul_right _ _
        exact dvd_trans hqdivm hmdivn
      · exact ⟨p, hpdvd, hpprime, by simpa [Nat.ModEq] using h3⟩
  let s : Finset ℕ := (Finset.range N).filter (fun p => Nat.Prime p ∧ p % 4 = 3)
  let P : ℕ := s.prod id
  let a : ℕ := 4 * P - 1
  have hEq : a = 4 * (P - 1) + 3 := by
    dsimp [a]
    omega
  have ha3 : a ≡ 3 [MOD 4] := by
    rw [hEq]
    norm_num [Nat.ModEq]
  rcases hprime3 a ha3 with ⟨q, hqdiva, hqprime, hqmod3⟩
  have hqmod3eq : q % 4 = 3 := by
    simpa [Nat.ModEq] using hqmod3
  have hqge : q ≥ N := by
    by_contra hlt
    have hltq : q < N := lt_of_not_ge hlt
    have hqin : q ∈ s := by
      dsimp [s]
      simp [hqprime, hqmod3eq, hltq]
    have hqdivP : q ∣ P := by
      simpa [P] using (Finset.dvd_prod_of_mem (s := s) (f := id) hqin)
    have hqdiv4P : q ∣ 4 * P := by
      simpa [mul_comm] using (dvd_mul_of_dvd_right hqdivP 4)
    have hsub : q ∣ 4 * P - a := Nat.dvd_sub' hqdiv4P hqdiva
    have hEq1 : 4 * P - a = 1 := by
      dsimp [a]
      omega
    have hqdiv1 : q ∣ 1 := by
      simpa [hEq1] using hsub
    exact hqprime.not_dvd_one hqdiv1
  have hqmod0 : q + 1 ≡ 0 [MOD 4] := by
    have := hqmod3.add_right 1
    simpa using this
  exact ⟨q, hqge, hqprime, hqmod0⟩
