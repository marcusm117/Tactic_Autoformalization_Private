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
    ring
  have hNnonneg : ∀ a : Zsqrtd (-n), 0 ≤ N a := by
    intro a
    rcases a with ⟨a1, a2⟩
    dsimp [N]
    have hn0 : 0 ≤ n := by linarith
    nlinarith [sq_nonneg a1, sq_nonneg a2, hn0]
  have hNone : ∀ a : Zsqrtd (-n), N a = 1 → IsUnit a := by
    intro a ha
    rcases a with ⟨a1, a2⟩
    refine ⟨⟨⟨a1, a2⟩, ⟨a1, -a2⟩, ?_, ?_⟩, rfl⟩
    · ext
      · dsimp [N] at ha ⊢
        ring_nf
        exact ha
      · ring
    · ext
      · dsimp [N] at ha ⊢
        ring_nf
        exact ha
      · ring
  have hUnitInt : ∀ {x y : ℤ}, x * y = 1 → IsUnit (⟨x, 0⟩ : Zsqrtd (-n)) := by
    intro x y hxy
    refine ⟨⟨⟨x, 0⟩, ⟨y, 0⟩, ?_, ?_⟩, rfl⟩
    · ext
      · simpa using hxy
      · simp
    · ext
      · simpa [mul_comm] using hxy
      · simp
  have hInt_not_unit : ∀ {m : ℤ}, 1 < m → ¬ IsUnit m := by
    intro m hm h
    rcases h with ⟨u, rfl⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;> omega
  have hN2 : N (2 : Zsqrtd (-n)) = 4 := by
    norm_num [N]
  have hNs : N (⟨0, 1⟩ : Zsqrtd (-n)) = n := by
    simp [N]
  have hNt : N (1 + (⟨0, 1⟩ : Zsqrtd (-n))) = n + 1 := by
    norm_num [N]
    ring
  have h2_irred : Irreducible (2 : Zsqrtd (-n)) := by
    refine ⟨?_, ?_⟩
    · intro h
      rcases h with ⟨u, hu⟩
      let v : Zsqrtd (-n) := ↑(u⁻¹)
      have hmul : (2 : Zsqrtd (-n)) * v = 1 := by
        simpa [hu, v] using Units.mul_inv u
      have hdiv : (2 : ℤ) ∣ 1 := by
        refine ⟨v.re, ?_⟩
        have hre : 2 * v.re = 1 := by
          have := congrArg Zsqrtd.re hmul
          simpa [v] using this
        simpa [eq_comm] using hre
      exact hInt_not_unit (by norm_num) (dvd_one.mp hdiv)
    · intro a b hab
      have hm : 4 = N a * N b := by
        calc
          4 = N (2 : Zsqrtd (-n)) := hN2.symm
          _ = N (a * b) := by simpa [hab]
          _ = N a * N b := by simpa using hNmul a b
      have hnb0 : 0 ≤ N b := hNnonneg b
      have hna0 : 0 ≤ N a := hNnonneg a
      have hna_le : N a ≤ 4 := by
        by_contra hgt
        have hx5 : 5 ≤ N a := by omega
        by_cases hzero : N b = 0
        · have : (4 : ℤ) = 0 := by simpa [hzero] using hm
          norm_num at this
        · have hy1 : 1 ≤ N b := by omega
          have : 5 ≤ N a * N b := by nlinarith [hx5, hy1]
          nlinarith [hm, this]
      interval_cases hNa : N a
      · exfalso
        have : (4 : ℤ) = 0 := by simpa [hNa] using hm
        norm_num at this
      · left
        exact hNone a hNa
      · exfalso
        rcases a with ⟨a1, a2⟩
        dsimp [N] at hNa
        have hn4 : 4 ≤ n := by omega
        have h4le : 4 * a2 ^ 2 ≤ n * a2 ^ 2 := by
          nlinarith [sq_nonneg a2, hn4]
        have hsmall : 4 * a2 ^ 2 ≤ 2 := by
          nlinarith [sq_nonneg a1, hNa, h4le]
        have ha2sq : a2 ^ 2 = 0 := by
          have hsq0 : 0 ≤ a2 ^ 2 := sq_nonneg a2
          omega
        have ha2z : a2 = 0 := by
          nlinarith [ha2sq]
        have ha1sq : a1 ^ 2 = 2 := by
          nlinarith [hNa, ha2z]
        have ha1lo : -2 ≤ a1 := by
          nlinarith [ha1sq]
        have ha1hi : a1 ≤ 2 := by
          nlinarith [ha1sq]
        interval_cases a1 <;> norm_num at ha1sq
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
    · intro h
      rcases h with ⟨u, hu⟩
      let v : Zsqrtd (-n) := ↑(u⁻¹)
      have hmul : (⟨0, 1⟩ : Zsqrtd (-n)) * v = 1 := by
        simpa [hu, v] using Units.mul_inv u
      have hre : (-n) * v.im = 1 := by
        have := congrArg Zsqrtd.re hmul
        simpa [v, mul_comm, mul_left_comm, mul_assoc] using this
      have hdiv : n ∣ (1 : ℤ) := by
        refine ⟨-v.im, ?_⟩
        nlinarith [hre]
      exact hInt_not_unit hngt1 (dvd_one.mp hdiv)
    · intro a b hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      by_cases ha2 : a2 = 0
      · have him : a1 * b2 = 1 := by
          have := congrArg Zsqrtd.im hab
          simpa [eq_comm, ha2] using this
        left
        simpa [ha2] using (hUnitInt him)
      · have hm : n = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          calc
            n = N (⟨0, 1⟩ : Zsqrtd (-n)) := hNs.symm
            _ = N ((⟨a1, a2⟩ : Zsqrtd (-n)) * ⟨b1, b2⟩) := by simpa [hab]
            _ = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
                  simpa using hNmul (⟨a1, a2⟩ : Zsqrtd (-n)) ⟨b1, b2⟩
        have ha2sq1 : 1 ≤ a2 ^ 2 := by
          have hpos : 0 < a2 ^ 2 := by
            exact sq_pos_iff.mpr ha2
          omega
        have hNa_ge_n : n ≤ N (⟨a1, a2⟩ : Zsqrtd (-n)) := by
          dsimp [N]
          nlinarith [sq_nonneg a1, ha2sq1, hnpos]
        have hNb0 : 0 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := hNnonneg ⟨b1, b2⟩
        have hNb_le1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) ≤ 1 := by
          by_contra hgt
          have h2 : 2 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := by omega
          have hbig : n < N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
            nlinarith [hNa_ge_n, h2, hngt1]
          nlinarith [hm, hbig]
        interval_cases hNb : N (⟨b1, b2⟩ : Zsqrtd (-n))
        · exfalso
          have : n = 0 := by simpa [hNb] using hm
          linarith
        · right
          exact hNone (⟨b1, b2⟩ : Zsqrtd (-n)) hNb
  have ht_irred : Irreducible (1 + (⟨0, 1⟩ : Zsqrtd (-n))) := by
    refine ⟨?_, ?_⟩
    · intro h
      rcases h with ⟨u, hu⟩
      let v : Zsqrtd (-n) := ↑(u⁻¹)
      have hmul : (1 + (⟨0, 1⟩ : Zsqrtd (-n))) * v = 1 := by
        simpa [hu, v] using Units.mul_inv u
      have hre : v.re - n * v.im = 1 := by
        have := congrArg Zsqrtd.re hmul
        simpa [v, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
          add_assoc] using this
      have him : v.re + v.im = 0 := by
        have := congrArg Zsqrtd.im hmul
        simpa [v, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
          eq_comm] using this
      have hdiv : n + 1 ∣ (1 : ℤ) := by
        refine ⟨-v.im, ?_⟩
        nlinarith [hre, him]
      exact hInt_not_unit (by linarith) (dvd_one.mp hdiv)
    · intro a b hab
      rcases a with ⟨a1, a2⟩
      rcases b with ⟨b1, b2⟩
      by_cases ha2 : a2 = 0
      · have him : a1 * b2 = 1 := by
          have := congrArg Zsqrtd.im hab
          simpa [eq_comm, ha2, add_comm, add_left_comm, add_assoc] using this
        left
        simpa [ha2] using (hUnitInt him)
      · have hm : n + 1 = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
          calc
            n + 1 = N (1 + (⟨0, 1⟩ : Zsqrtd (-n))) := hNt.symm
            _ = N ((⟨a1, a2⟩ : Zsqrtd (-n)) * ⟨b1, b2⟩) := by simpa [hab]
            _ = N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
                  simpa using hNmul (⟨a1, a2⟩ : Zsqrtd (-n)) ⟨b1, b2⟩
        have ha2sq1 : 1 ≤ a2 ^ 2 := by
          have hpos : 0 < a2 ^ 2 := by
            exact sq_pos_iff.mpr ha2
          omega
        have hNa_ge_n : n ≤ N (⟨a1, a2⟩ : Zsqrtd (-n)) := by
          dsimp [N]
          nlinarith [sq_nonneg a1, ha2sq1, hnpos]
        have hNb0 : 0 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := hNnonneg ⟨b1, b2⟩
        have hNb_le1 : N (⟨b1, b2⟩ : Zsqrtd (-n)) ≤ 1 := by
          by_contra hgt
          have h2 : 2 ≤ N (⟨b1, b2⟩ : Zsqrtd (-n)) := by omega
          have hbig : n + 1 <
              N (⟨a1, a2⟩ : Zsqrtd (-n)) * N (⟨b1, b2⟩ : Zsqrtd (-n)) := by
            nlinarith [hNa_ge_n, h2, hngt1]
          nlinarith [hm, hbig]
        interval_cases hNb : N (⟨b1, b2⟩ : Zsqrtd (-n))
        · exfalso
          have : n + 1 = 0 := by simpa [hNb] using hm
          linarith
        · right
          exact hNone (⟨b1, b2⟩ : Zsqrtd (-n)) hNb
  exact ⟨h2_irred, hs_irred, ht_irred⟩
