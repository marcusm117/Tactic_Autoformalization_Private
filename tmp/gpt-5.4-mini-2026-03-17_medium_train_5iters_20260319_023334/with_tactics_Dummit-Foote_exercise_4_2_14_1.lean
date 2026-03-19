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


theorem exercise_4_2_14 {G : Type*} [Fintype G] [Group G]
  (hG : ¬ (card G).Prime) (hG1 : ∀ k : ℕ, k ∣ card G →
  ∃ (H : Subgroup G) (fH : Fintype H), @card H fH = k) :
  ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  have hnontriv : Nontrivial G := hsimple.1
  have hgt1 : 1 < Fintype.card G := Fintype.one_lt_card_iff_nontrivial.mpr hnontriv
  let p : ℕ := Nat.minFac (Fintype.card G)
  have hp : Nat.Prime p := by
    simpa [p] using Nat.minFac_prime hgt1
  have hpdvd : p ∣ Fintype.card G := by
    simpa [p] using Nat.minFac_dvd (Fintype.card G)
  let m : ℕ := Fintype.card G / p
  have hm0 : p * m = Fintype.card G := by
    simpa [m] using Nat.mul_div_cancel' hpdvd
  have hm : Fintype.card G = p * m := hm0.symm
  have hmdiv : m ∣ Fintype.card G := by
    refine ⟨p, ?_⟩
    simpa [Nat.mul_comm] using hm
  rcases hG1 m hmdiv with ⟨H, fH, hcardH⟩
  letI : Fintype H := fH
  have hcardH' : Fintype.card H = m := by
    simpa using hcardH
  have hmpos : 0 < m := by
    by_contra hm0'
    have : Fintype.card G = 0 := by simpa [m, hm0'] using hm
    exact (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card G)) this
  have hindexH : H.index = p := by
    have hindexmul : H.index * m = p * m := by
      calc
        H.index * m = H.index * Fintype.card H := by rw [hcardH']
        _ = Fintype.card G := Subgroup.index_mul_card H
        _ = p * m := hm
    exact Nat.mul_right_cancel hmpos hindexmul
  let ρ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPerm (G := G) (α := G ⧸ H)
  let K : Subgroup G := ρ.ker
  have hker_le : K ≤ H := by
    intro g hg
    have hfix : g • (1 : G ⧸ H) = 1 := by
      simpa using congrArg (fun e : Equiv.Perm (G ⧸ H) => e (1 : G ⧸ H)) hg
    simpa using hfix
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKsubH : Subgroup H := Subgroup.ofLE hker_le
  have hcardK_dvd : Fintype.card K ∣ m := by
    have h := Subgroup.card_subgroup_dvd_card hKsubH
    simpa [hcardH'] using h
  rcases hcardK_dvd with ⟨t, ht⟩
  have hindexKmul : K.index * Fintype.card K = (p * t) * Fintype.card K := by
    calc
      K.index * Fintype.card K = Fintype.card G := Subgroup.index_mul_card K
      _ = p * m := hm
      _ = p * (Fintype.card K * t) := by rw [ht]
      _ = (p * t) * Fintype.card K := by ring
  have hindexK : K.index = p * t := by
    exact Nat.mul_right_cancel (Fintype.card_pos : 0 < Fintype.card K) hindexKmul
  have hrange_eq : Fintype.card ρ.range = K.index := by
    simpa [K, Subgroup.index] using (Fintype.card_congr (QuotientGroup.quotientKerEquivRange ρ))
  have hperm : Fintype.card (Equiv.Perm (G ⧸ H)) = p! := by
    simpa [hindexH] using (Fintype.card_perm (G ⧸ H))
  have hindexK_dvd : K.index ∣ p! := by
    have hsub : Fintype.card ρ.range ∣ Fintype.card (Equiv.Perm (G ⧸ H)) := by
      exact Subgroup.card_subgroup_dvd_card ρ.range
    simpa [hrange_eq, hperm] using hsub
  have hfact : p! = p * (p - 1)! := by
    have hp0 : 0 < p := hp.pos
    calc
      p! = (p - 1 + 1)! := by simp [Nat.succ_pred_eq_of_pos hp0]
      _ = (p - 1 + 1) * (p - 1)! := by simp [Nat.factorial_succ]
      _ = p * (p - 1)! := by simp [Nat.succ_pred_eq_of_pos hp0]
  have htdivfact : t ∣ (p - 1)! := by
    have hmul : p * t ∣ p * (p - 1)! := by
      simpa [hindexK, hfact, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hindexK_dvd
    exact Nat.dvd_of_mul_dvd_mul_left hmul
  have ht_eq_one : t = 1 := by
    by_contra htne1
    rcases Nat.exists_prime_and_dvd htne1 with ⟨q, hqprime, hqdvd⟩
    have hqfact : q ∣ (p - 1)! := dvd_trans hqdvd htdivfact
    have hqle : q ≤ p - 1 := hqprime.le_of_dvd_factorial hqfact
    have htdivm : t ∣ m := ⟨Fintype.card K, by simpa [Nat.mul_comm] using ht⟩
    have hqn : q ∣ Fintype.card G := by
      exact dvd_trans (dvd_trans hqdvd htdivm) hmdiv
    have hp_le_q : p ≤ q := by
      simpa [p] using Nat.minFac_le_of_dvd hgt1 hqprime hqn
    omega
  have hcardK : Fintype.card K = m := by
    rw [ht_eq_one, Nat.mul_one] at ht
    exact ht.symm
  have hKH : K = H := by
    apply Subgroup.eq_of_le_of_card_eq hker_le
    simpa [hcardH'] using hcardK
  have hnormal : H.Normal := by
    simpa [hKH] using hKnormal
  have hbottop := hsimple.2 H hnormal
  rcases hbottop with hbot | htop
  · have hm1 : m = 1 := by
      have := congrArg (fun K : Subgroup G => Fintype.card K) hbot
      simpa [hcardH'] using this
    have hprimeG : Nat.Prime (Fintype.card G) := by
      simpa [hm, hm1] using hp
    exact hG hprimeG
  · have hEq : 1 * m = p * m := by
      have := congrArg (fun K : Subgroup G => Fintype.card K) htop
      simpa [hcardH', hm] using this
    have hp1 : p = 1 := by
      have := Nat.mul_right_cancel hmpos hEq
      simpa using this.symm
    exact hp.ne_one hp1
