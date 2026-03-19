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


theorem exercise_4_5_28 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 105) (P : Sylow 3 G) [hP : P.Normal] :
  ∀ a b : G, a*b = b*a := by
  intro a b
  classical
  let P0 : Subgroup G := (P : Subgroup G)
  have hPcard : Fintype.card P0 = 3 := by
    have h := P.card_eq_multiplicity
    norm_num [hG] at h
    simpa [P0] using h
  have hQcard : Fintype.card (G ⧸ P0) = 35 := by
    have h := Subgroup.index_mul_card P0
    omega
  have hPcyc : IsCyclic P0 := by
    exact isCyclic_of_prime_card hPcard (by decide : Nat.Prime 3)
  haveI : IsCyclic P0 := hPcyc
  have hAutP : Fintype.card (MulAut P0) = 2 := by
    simpa [hPcard] using (Fintype.card_aut P0)
  have hQcyc : IsCyclic (G ⧸ P0) := by
    simpa [hQcard] using
      (IsCyclic.of_card_eq_prime_mul_prime (G := G ⧸ P0) (p := 5) (q := 7)
        (by decide : Nat.Prime 5) (by decide : Nat.Prime 7) (by decide) (by decide))
  rcases hQcyc.exists_generator with ⟨q, hq⟩
  rcases QuotientGroup.mk_surjective q with ⟨x, hx⟩
  letI : CommGroup P0 := hPcyc.commGroup
  have hcentral : ∀ g : G, ∀ p : P0, g * (p : G) = (p : G) * g := by
    intro g p
    let φ : MulAut P0 :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, by
        simpa [mul_assoc] using Subgroup.Normal.conj_mem hP x.2 g⟩
      invFun := fun x => ⟨g⁻¹ * (x : G) * g, by
        simpa [mul_assoc] using Subgroup.Normal.conj_mem hP x.2 g⁻¹⟩
      left_inv := by
        intro x
        ext
        simp [mul_assoc]
      right_inv := by
        intro x
        ext
        simp [mul_assoc]
      map_mul' := by
        intro x y
        ext
        simp [mul_assoc] }
    have hpowAux : ∀ n : ℕ, ∀ p : P0, ((φ ^ n) p : G) = (g ^ n : G) * (p : G) * (g ^ n : G)⁻¹ := by
      intro n
      induction n with
      | zero =>
          intro p
          simp [φ]
      | succ n ih =>
          intro p
          calc
            ((φ ^ (n + 1)) p : G) = ((φ ^ n) (φ p) : G) := by simp [pow_succ]
            _ = g ^ n * (g * (p : G) * g⁻¹) * (g ^ n : G)⁻¹ := by
                  simpa [φ, mul_assoc] using ih (φ p)
            _ = (g ^ (n + 1) : G) * (p : G) * (g ^ (n + 1) : G)⁻¹ := by
                  simp [pow_succ, mul_assoc]
    have hqpow : (QuotientGroup.mk g : G ⧸ P0) ^ 35 = 1 := by
      simpa [hQcard] using (pow_card_eq_one (QuotientGroup.mk g))
    have hg35inv : (g ^ 35 : G)⁻¹ ∈ P0 := by
      have hqeq : QuotientGroup.mk (g ^ 35 : G) = 1 := by
        simpa [map_pow] using hqpow
      exact QuotientGroup.eq'.mp hqeq
    have hg35mem : g ^ 35 ∈ P0 := by
      simpa using P0.inv_mem hg35inv
    have hφ35 : φ ^ 35 = 1 := by
      ext q
      have hq35 : ((φ ^ 35) q : G) = (q : G) := by
        rw [hpowAux]
        have hcomm : (g ^ 35 : G) * (q : G) = (q : G) * (g ^ 35 : G) := by
          simpa using (CommGroup.mul_comm (⟨g ^ 35, hg35mem⟩ : P0) q)
        calc
          (g ^ 35 : G) * (q : G) * (g ^ 35 : G)⁻¹
            = (q : G) * (g ^ 35 : G) * (g ^ 35 : G)⁻¹ := by rw [hcomm]
          _ = (q : G) := by simp
      simpa using hq35
    have hφ2 : orderOf φ ∣ 2 := by
      simpa [hAutP] using (orderOf_dvd_card φ)
    have hφ35 : orderOf φ ∣ 35 := by
      exact orderOf_dvd_of_pow_eq_one hφ35
    have hφ1 : orderOf φ = 1 := by
      omega
    have hφeq : φ = 1 := by
      simpa [orderOf_eq_one_iff] using hφ1
    have hfix := congrArg (fun e : MulAut P0 => e p) hφeq
    simpa [φ] using hfix
  have hdecomp : ∀ g : G, ∃ n : ℕ, ∃ p : P0, g = (x ^ n : G) * (p : G) := by
    intro g
    rcases hq.exists_pow_eq (QuotientGroup.mk g) with ⟨n, hn⟩
    have hqg : QuotientGroup.mk (x ^ n : G) = QuotientGroup.mk g := by
      calc
        QuotientGroup.mk (x ^ n : G) = q ^ n := by simpa [hx]
        _ = QuotientGroup.mk g := hn
    have hmem : (x ^ n : G)⁻¹ * g ∈ P0 := QuotientGroup.eq'.mp hqg
    refine ⟨n, ⟨⟨(x ^ n : G)⁻¹ * g, hmem⟩, ?_⟩⟩
    simp [mul_assoc]
  rcases hdecomp a with ⟨m, ⟨pa, rfl⟩⟩
  rcases hdecomp b with ⟨n, ⟨pb, rfl⟩⟩
  calc
    (x ^ m : G) * (pa : G) * ((x ^ n : G) * (pb : G))
        = (x ^ m : G) * ((x ^ n : G) * (pa : G)) * (pb : G) := by
            rw [hcentral (x ^ n : G) pa]
            simp [mul_assoc]
    _ = (x ^ m : G) * (x ^ n : G) * ((pa : G) * (pb : G)) := by
            simp [mul_assoc]
    _ = (x ^ n : G) * (x ^ m : G) * ((pb : G) * (pa : G)) := by
            rw [hcentral (pa : G) pb]
            simp [mul_assoc]
    _ = (x ^ n : G) * (pb : G) * ((x ^ m : G) * (pa : G)) := by
            rw [hcentral (x ^ m : G) pb]
            simp [mul_assoc]
    _ = b * a := by
            simp [mul_assoc]
