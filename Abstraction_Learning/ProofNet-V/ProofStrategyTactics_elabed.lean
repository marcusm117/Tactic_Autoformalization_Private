/-
  ProofStrategyTacticsElab.lean

  Custom Lean 4 tactics encoding the top 10 proof strategies from
  ProofNet-V analysis. `sylow_counting` and `lagrange` use `elab`
  (TacticM) for proof-state awareness; the rest use `macro` since
  they don't benefit from inspecting the context.

  Import this file to use the tactics in other proofs:

    import ProofStrategyTacticsElab

  Authors: marcusm117
  License: Apache 2.0
-/

import Mathlib


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


open Lean Elab Tactic Meta in
/-! ## sylow_counting

Scans the local context for `Fact (Nat.Prime p)` and `Group G` /
`Fintype G` instances, then introduces Sylow counting constraints
for each discovered prime:
  (1) `card (Sylow p G) ≡ 1 [MOD p]`
  (2) `card (Sylow p G) ∣ card G`
Finally attempts `omega`, `norm_num`, and `decide` to resolve the
forced arithmetic. -/

elab "sylow_counting" : tactic => do
  let ctx ← getLCtx
  -- Collect all local hypotheses whose type mentions Nat.Prime
  let mut primeDecls : Array LocalDecl := #[]
  for decl in ctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``Fact 1 then
      let arg := ty.getArg! 0
      if arg.isAppOfArity ``Nat.Prime 1 then
        primeDecls := primeDecls.push decl
  -- For each discovered prime, introduce Sylow constraints
  for decl in primeDecls do
    let primeTy := decl.type.getArg! 0  -- `Nat.Prime p`
    let p := primeTy.getArg! 0           -- the actual prime `p`
    -- Try to introduce: card (Sylow p G) ≡ 1 [MOD p]
    try
      let modStx ← `(tactic|
        have := @Sylow.card_sylow_modEq_one _ _ $(← Term.exprToSyntax p) _ _ _)
      evalTactic modStx
    catch _ => pure ()
    -- Try to introduce: card (Sylow p G) divides index
    try
      let dvdStx ← `(tactic|
        have := @card_sylow_dvd_index _ _ $(← Term.exprToSyntax p) _ _)
      evalTactic dvdStx
    catch _ => pure ()
  -- If no primes found in context, fall back to blind introduction
  if primeDecls.isEmpty then
    try evalTactic (← `(tactic| have := Sylow.card_sylow_modEq_one))
    catch _ => pure ()
    try evalTactic (← `(tactic| have := card_sylow_dvd_index))
    catch _ => pure ()
  -- Try to resolve the arithmetic
  try evalTactic (← `(tactic| omega))
  catch _ =>
  try evalTactic (← `(tactic| (norm_num at *; omega)))
  catch _ =>
  try evalTactic (← `(tactic| decide))
  catch _ =>
    pure ()


/-! ## show_normal

Proves a subgroup is normal by unfolding the normality condition
and attempting to close the conjugation-closure goal.
Handles both single subgroups and intersections of normal subgroups. -/

macro "show_normal" : tactic =>
  `(tactic|
    constructor
    · intro g x hx
      first
      | (simp only [Subgroup.mem_inf] at hx ⊢;
         exact ⟨Subgroup.Normal.conj_mem ‹_› x hx.1 g,
                Subgroup.Normal.conj_mem ‹_› x hx.2 g⟩)
      | (exact Subgroup.Normal.conj_mem ‹_› x hx g)
      | (simp [mul_assoc, mul_inv_cancel, inv_mul_cancel] at *;
         assumption)
      | group)


open Lean Elab Tactic Meta in
/-! ## lagrange

Scans the local context for ALL hypotheses whose type is a `Subgroup`,
then introduces Lagrange-type divisibility facts for each:
  (1) `Subgroup.card_subgroup_dvd_card H`  — |H| ∣ |G|
  (2) `Subgroup.index_mul_card H`          — |G| = [G:H] * |H|
Also introduces `orderOf_dvd_card` for element-order divisibility.
Finally attempts `omega`/`norm_num` to resolve the arithmetic. -/

elab "lagrange" : tactic => do
  let ctx ← getLCtx
  -- Collect all local hypotheses whose type is a Subgroup
  let mut subgroupDecls : Array LocalDecl := #[]
  for decl in ctx do
    if decl.isAuxDecl then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``Subgroup 2 then
      subgroupDecls := subgroupDecls.push decl
  -- For each discovered subgroup, introduce Lagrange facts
  for decl in subgroupDecls do
    let hExpr := decl.toExpr
    -- Try: |H| ∣ |G|
    try
      let dvdStx ← `(tactic|
        have := Subgroup.card_subgroup_dvd_card $(← Term.exprToSyntax hExpr))
      evalTactic dvdStx
    catch _ => pure ()
    -- Try: |G| = [G:H] * |H|
    try
      let idxStx ← `(tactic|
        have := Subgroup.index_mul_card $(← Term.exprToSyntax hExpr))
      evalTactic idxStx
    catch _ => pure ()
  -- Also introduce order-divides-card (not subgroup-specific)
  try evalTactic (← `(tactic| have := orderOf_dvd_card))
  catch _ => pure ()
  -- If no subgroups found, fall back to blind introduction
  if subgroupDecls.isEmpty then
    try evalTactic (← `(tactic| have := Subgroup.card_subgroup_dvd_card ‹_›))
    catch _ => pure ()
    try evalTactic (← `(tactic| have := Subgroup.index_mul_card ‹_›))
    catch _ => pure ()
  -- Try to resolve the arithmetic
  try evalTactic (← `(tactic| omega))
  catch _ =>
  try evalTactic (← `(tactic| (norm_num at *; omega)))
  catch _ =>
  try evalTactic (← `(tactic| (simp only [Nat.dvd_iff_mod_eq_zero] at *; omega)))
  catch _ =>
    pure ()


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

Tries to close the goal by brute-force evaluation over a finite/decidable
domain. For existential goals, tries `norm_num` (which can find numeric
witnesses). Falls back to `native_decide` for larger finite checks. -/

macro "counterexample" : tactic =>
  `(tactic|
    first
    | decide
    | native_decide
    | norm_num
    | (simp; decide)
    | (simp; native_decide))
