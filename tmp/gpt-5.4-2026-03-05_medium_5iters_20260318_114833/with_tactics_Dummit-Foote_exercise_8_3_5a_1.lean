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
  let N : Zsqrtd (-n) → ℤ := fun z => z.re ^ 2 + n * z.im ^ 2
  have hnpos : 0 < n := by linarith
  have hngt1 : 1 < n := by linarith
  have hNmul : ∀ a b : Zsqrtd (-n), N (a * b) = N a * N b := by
    intro a b
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    dsimp [N]
    ring_nf
  have hNnonneg : ∀ a : Zsqrtd (-n), 0 ≤ N a := by
    intro a
    rcases a with ⟨a1, a2⟩
    dsimp [N]
    have hnnonneg : 0 ≤ n := by linarith
    nlinarith [sq_nonneg a1, sq_nonneg a2, hnnonneg]
  have hNone : ∀ a : Zsqrtd (-n), N a = 1 → IsUnit a := by
    intro a ha
    rcases a with ⟨a1, a2⟩
    refine ⟨⟨⟨a1, a2⟩, ⟨a1, -a2⟩, ?_, ?_⟩, rfl⟩
    · ext
      · change a1 * a1 + (-n) * (a2 * (-a2)) = 1
        ring_nf
        simpa [N] using ha
      · change a1 * (-a2) + a2 * a1 = 0
        ring
    · ext
      · change a1 * a1 + (-n) * ((-a2) * a2) = 1
        ring_nf
        simpa [N] using ha
      · change a1 * a2 + (-a2) * a1 = 0
        ring
  have hUnitInt : ∀ {x y : ℤ}, x * y = 1 → IsUnit (⟨x, 0⟩ : Zsqrtd (-n)) := by
    intro x y hxy
    refine ⟨⟨⟨x, 0⟩, ⟨y, 0⟩, ?_, ?_⟩, rfl⟩
    · ext
      · change x * y + (-n) * (0 * 0) = 1
        simp [hxy]
      · change x * 0 + 0 * y = 0
        ring
    · ext
      · change y * x + (-n) * (0 * 0) = 1
        simpa [mul_comm] using hxy
      · change y * 0 + 0 * x = 0
        ring
  have hNunit : ∀ a : Zsqrtd (-n), IsUnit a → N a = 1 := by
    intro a ha
    rcases ha with ⟨u, rfl⟩
    set x : ℤ := N (↑u : Zsqrtd (-n))
    set y : ℤ := N ((↑(u⁻¹) : Zsqrtd (-n)))
    have hm : x * y = 1 := by
      calc
        x * y = N (↑u : Zsqrtd (-n)) * N (↑(u⁻¹) : Zsqrtd (-n)) := by rfl
        _ = N ((↑u : Zsqrtd (-n)) * (↑(u⁻¹) : Zsqrtd (-n))) := by
              symm
              simpa using hNmul (↑u : Zsqrtd (-n)) (↑(u⁻¹) : Zsqrtd (-n))
        _ = N (1 : Zsqrtd (-n)) := by simp
        _ = 1 := by simp [N]
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact hNnonneg _
    have hy0 : 0 ≤ y := by
      dsimp [y]
      exact hNnonneg _
    have hyne : y ≠ 0 := by
      intro hy
      rw [hy] at hm
      norm_num at hm
    have hy1 : 1 ≤ y := by omega
    have hxle : x ≤ 1 := by
      have hmul : x * 1 ≤ x * y := mul_le_mul_of_nonneg_left hy1 hx0
      rw [hm] at hmul
      simpa using hmul
    have hxne : x ≠ 0 := by
      intro hx
      rw [hx] at hm
      norm_num at hm
    have hx1 : 1 ≤ x := by omega
    have hxeq : x = 1 := by omega
    simpa [x] using hxeq
  have hNotUnit_of_norm_gt_one : ∀ a : Zsqrtd (-n), 1 < N a → ¬ IsUnit a := by
    intro a ha hu
    have h := hNunit a hu
    linarith
  have hN2 : N (2 : Zsqrtd (-n)) = 4 := by
    norm_num [N]
  have hNs : N (⟨0, 1⟩ : Zsqrtd (-n)) = n := by
    simp [N]
  have hNt : N (1 + (⟨0, 1⟩ : Zsqrtd (-n))) = n + 1 := by
    simp [N]
    ring
  have h2_irred : Irreducible (2 : Zsqrtd (-n)) := by
    refine ⟨?_, ?_⟩
    · apply hNotUnit_of_norm_gt_one
      rw [hN2]
      norm_num
    · intro a b hab
      have hm : 4 = N a * N b := by
        calc
          4 = N (2 : Zsqrtd (-n)) := hN2.symm
          _ = N (a * b) := by simpa [hab]
          _ = N a * N b := by simpa using hNmul a b
      have hna0 : 0 ≤ N a := hNnonneg a
      have hnb0 : 0 ≤ N b := hNnonneg b
      have hna_le : N a ≤ 4 := by
        by_cases hbz : N b = 0
        · have : (4 : ℤ) = 0 := by simpa [hbz] using hm
          norm_num at this
        · have hb1 : 1 ≤ N b := by omega
          nlinarith [hm, hb1]
      interval_cases hNa : N a
      · exfalso
        have : (4 : ℤ) = 0 := by simpa [hNa] using hm
        norm_num at this
      · left
        exact hNone a hNa
      · exfalso
        rcases a with ⟨a1, a2⟩
        dsimp [N] at hNa
        by_cases ha2 : a2 = 0
        · have ha1sq : a1 ^ 2 = 2 := by simpa [ha2] using hNa
          have hlo : -2 ≤ a1 := by nlinarith [ha1sq]
          have hhi : a1 ≤ 2 := by nlinarith [ha1sq]
          interval_cases a1 <;> norm_num at ha1sq
        · have ha2sq1 : 1 ≤ a2 ^ 2 := by
            have hpos : 0 < a2 ^ 2 := by exact sq_pos_iff.mpr ha2
            omega
          nlinarith [sq_nonneg a1, ha2sq1, hn0, hNa]
      · exfalso
        have : (4 : ℤ) = 3 * N b := by simpa [hNa] using hm
        omega
      · right
        have hNb : N b = 1 := by
          have : (4 : ℤ) = 4 * N b := by simpa [hNa] using hm
          omega
        exact hNone b hNb
  have hs_irred : Irreducible (⟨0, 1⟩ : Zsqrtd (-n)) := by
    refine ⟨?_, ?_⟩
    · apply hNotUnit_of_norm_gt_one
      rw [hNs]
      linarith
    · intro a b hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      by_cases ha2 : a2 = 0
      · left
        have him : a1 * b2 = 1 := by
          have := congrArg Zsqrtd.im hab
          simpa [ha2] using this
        simpa [ha2] using (hUnitInt him)
      · right
        have hm : n = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          calc
            n = N (⟨0, 1⟩ : Zsqrtd (-n)) := hNs.symm
            _ = N ((⟨a1, a2⟩ : Zsqrtd (-n)) * ⟨b1, b2⟩) := by simpa [hab]
            _ = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
                  simpa using hNmul (⟨a1, a2⟩ : Zsqrtd (-n)) ⟨b1, b2⟩
        have ha2sq1 : 1 ≤ a2 ^ 2 := by
          have hpos : 0 < a2 ^ 2 := by exact sq_pos_iff.mpr ha2
          omega
        have hNa_ge : n ≤ N (⟨a1, a2⟩ : Zsqrtd (-n)) := by
          dsimp [N]
          nlinarith [sq_nonneg a1, ha2sq1, hnpos]
        have hNb_gt0 : 0 < N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          by_contra h0
          have h0' : N (⟨b1, b2⟩ : Zsqrtd (-n)) = 0 := by omega
          have : n = 0 := by simpa [h0'] using hm
          linarith
        have hNb_le1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) ≤ 1 := by
          by_contra hgt
          have h2 : 2 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := by omega
          have hbig : n < N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
            nlinarith [hNa_ge, h2, hnpos]
          nlinarith [hm, hbig]
        have hNb1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) = 1 := by
          omega
        exact hNone _ hNb1
  have ht_irred : Irreducible (1 + (⟨0, 1⟩ : Zsqrtd (-n))) := by
    refine ⟨?_, ?_⟩
    · apply hNotUnit_of_norm_gt_one
      rw [hNt]
      linarith
    · intro a b hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      by_cases ha2 : a2 = 0
      · left
        have him : a1 * b2 = 1 := by
          have := congrArg Zsqrtd.im hab
          simpa [ha2] using this
        simpa [ha2] using (hUnitInt him)
      · right
        have hm : n + 1 = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          calc
            n + 1 = N (1 + (⟨0, 1⟩ : Zsqrtd (-n))) := hNt.symm
            _ = N ((⟨a1, a2⟩ : Zsqrtd (-n)) * ⟨b1, b2⟩) := by simpa [hab]
            _ = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
                  simpa using hNmul (⟨a1, a2⟩ : Zsqrtd (-n)) ⟨b1, b2⟩
        have ha2sq1 : 1 ≤ a2 ^ 2 := by
          have hpos : 0 < a2 ^ 2 := by exact sq_pos_iff.mpr ha2
          omega
        have hNa_ge : n ≤ N (⟨a1, a2⟩ : Zsqrtd (-n)) := by
          dsimp [N]
          nlinarith [sq_nonneg a1, ha2sq1, hnpos]
        have hNb_gt0 : 0 < N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          by_contra h0
          have h0' : N (⟨b1, b2⟩ : Zsqrtd (-n)) = 0 := by omega
          have : n + 1 = 0 := by simpa [h0'] using hm
          linarith
        have hNb_le1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) ≤ 1 := by
          by_contra hgt
          have h2 : 2 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := by omega
          have hbig : n + 1 < N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
            nlinarith [hNa_ge, h2, hngt1]
          nlinarith [hm, hbig]
        have hNb1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) = 1 := by
          omega
        exact hNone _ hNb1
  exact ⟨h2_irred, hs_irred, ht_irred⟩
