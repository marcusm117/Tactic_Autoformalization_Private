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


theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  cases hG
  constructor
  · rintro ⟨p, hp, hpn, rfl⟩
    have hcardG : Fintype.card G = n := by
      simpa [hx, Subgroup.closure_singleton] using
        (show Fintype.card (Subgroup.zpowers x) = orderOf x from Fintype.card_zpowers)
    have hcardH : Fintype.card H = n / p := by
      simpa [hx, orderOf_pow, Nat.gcd_eq_right hpn, Subgroup.closure_singleton] using
        (show Fintype.card (Subgroup.zpowers (x ^ p)) = orderOf (x ^ p) from Fintype.card_zpowers)
    have hindexH : Subgroup.index H = p := by
      have hmul := Subgroup.index_mul_card H
      omega
    refine ⟨?_, ?_⟩
    · intro htop
      have hcardEq : Fintype.card H = Fintype.card G := by
        rw [htop]
      rw [hcardH, hcardG] at hcardEq
      omega
    · intro K hHK
      have hdiv : Subgroup.index K ∣ p := Subgroup.index_dvd_index hHK
      rcases hp.eq_one_or_eq_self_of_dvd hdiv with h1 | h2
      · right
        have hcardK : Fintype.card K = Fintype.card G := by
          have hmul := Subgroup.index_mul_card K
          rw [h1] at hmul
          omega
        exact Subgroup.eq_top_of_card_eq hcardK
      · left
        have hcardK : Fintype.card K = Fintype.card H := by
          have hmulK := Subgroup.index_mul_card K
          have hmulH := Subgroup.index_mul_card H
          rw [h2, hindexH] at hmulK
          omega
        exact Subgroup.eq_of_le_of_card_eq hHK hcardK
  · intro hmax
    rcases hmax with ⟨hHtop, hinter⟩
    have hcardG : Fintype.card G = n := by
      simpa [hx, Subgroup.closure_singleton] using
        (show Fintype.card (Subgroup.zpowers x) = orderOf x from Fintype.card_zpowers)
    let d : ℕ := Subgroup.index H
    have hcardH : Fintype.card H = n / d := by
      have hmul := Subgroup.index_mul_card H
      omega
    have hdvdn : d ∣ n := by
      have hmul := Subgroup.index_mul_card H
      rw [hcardG] at hmul
      exact ⟨Fintype.card H, hmul⟩
    have hdiv : orderOf (QuotientGroup.mk H x) ∣ d := by
      simpa [d] using (orderOf_dvd_card (QuotientGroup.mk H x))
    have hxpowd : x ^ d ∈ H := by
      rw [← QuotientGroup.eq_one_iff]
      rcases hdiv with ⟨k, hk⟩
      rw [hk, pow_mul]
      exact pow_orderOf_eq_one (QuotientGroup.mk H x)
    have hleHd : Subgroup.closure ({x ^ d} : Set G) ≤ H := by
      exact Subgroup.closure_le.2 (by
        intro y hy
        simpa [Set.mem_singleton_iff] using hxpowd)
    have hcardCd : Fintype.card (Subgroup.closure ({x ^ d} : Set G)) = n / d := by
      simpa [hx, orderOf_pow, Nat.gcd_eq_right hdvdn, Subgroup.closure_singleton] using
        (show Fintype.card (Subgroup.zpowers (x ^ d)) = orderOf (x ^ d) from Fintype.card_zpowers)
    have hHd : H = Subgroup.closure ({x ^ d} : Set G) := by
      exact le_antisymm (by
        rw [← hcardCd, ← hcardH]
        exact hleHd) hleHd
    have hdne1 : d ≠ 1 := by
      intro hd1
      have hcardEq : Fintype.card H = Fintype.card G := by
        rw [hcardH, hd1, hcardG]
      exact hHtop (Subgroup.eq_top_of_card_eq hcardEq)
    have hdgt1 : 1 < d := by omega
    rcases Nat.exists_prime_and_dvd hdgt1 with ⟨p, hp, hpdvd⟩
    by_cases hpd : p = d
    · refine ⟨d, ?_, hdvdn, hHd⟩
      simpa [hpd] using hp
    · have hpdlt : p < d := by
        exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_gt hdgt1) hpdvd) hpd
      have hpdvdn : p ∣ n := dvd_trans hpd hdvdn
      have hcardCp : Fintype.card (Subgroup.closure ({x ^ p} : Set G)) = n / p := by
        simpa [hx, orderOf_pow, Nat.gcd_eq_right hpdvdn, Subgroup.closure_singleton] using
          (show Fintype.card (Subgroup.zpowers (x ^ p)) = orderOf (x ^ p) from Fintype.card_zpowers)
      have hxpd : x ^ d ∈ Subgroup.closure ({x ^ p} : Set G) := by
        rcases hpdvd with ⟨k, rfl⟩
        simpa [pow_mul] using
          (pow_mem (Subgroup.closure ({x ^ p} : Set G)) k
            (Subgroup.subset_closure (by simp)))
      have hle : H ≤ Subgroup.closure ({x ^ p} : Set G) := by
        rw [hHd]
        exact Subgroup.closure_le.2 (by
          intro y hy
          simpa [Set.mem_singleton_iff] using hxpd)
      have hnotTop : Subgroup.closure ({x ^ p} : Set G) ≠ ⊤ := by
        intro htop
        have hcardTop : Fintype.card (Subgroup.closure ({x ^ p} : Set G)) = Fintype.card G := by
          rw [htop]
        rw [hcardCp, hcardG] at hcardTop
        omega
      have hcase := hinter (Subgroup.closure ({x ^ p} : Set G)) hle
      rcases hcase with hEq | hTop
      · have hcardEq : n / p = n / d := by
          have := congrArg Fintype.card hEq
          rw [hcardCp, hcardH] at this
          exact this
        omega
      · exact hnotTop hTop
