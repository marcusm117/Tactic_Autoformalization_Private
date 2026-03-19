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


theorem exercise_4_5_13 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 56) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧ P.Normal := by
  classical
  have h2prime : Nat.Prime 2 := by decide
  have h7prime : Nat.Prime 7 := by decide
  letI : Fact (Nat.Prime 2) := ⟨h2prime⟩
  letI : Fact (Nat.Prime 7) := ⟨h7prime⟩
  have h7nonempty : Nonempty (Sylow 7 G) := Sylow.nonempty (G := G) (p := 7)
  have h2nonempty : Nonempty (Sylow 2 G) := Sylow.nonempty (G := G) (p := 2)
  have h7mod : Fintype.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    simpa using (Fintype.card_sylow_modEq_one (G := G) (p := 7))
  have h7dvd : Fintype.card (Sylow 7 G) ∣ 8 := by
    have h := (Fintype.card_sylow_dvd_index (G := G) (p := 7))
    simpa [hG] using h
  have h7cases : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    omega
  rcases h7cases with h7one | h7eight
  · let P : Sylow 7 G := Classical.choice h7nonempty
    refine ⟨7, P, h7prime, ?_, ?_⟩
    · omega
    ·
      have hsub : Subsingleton (Sylow 7 G) := by
        exact (Fintype.card_eq_one_iff.mp h7one)
      constructor
      intro g x hx
      have hxg : g * x * g⁻¹ ∈ (g • P : Sylow 7 G) := by
        simpa using hx
      have hfix : g • P = P := by
        exact Subsingleton.elim _ _
      simpa [hfix] using hxg
  · have h2mod : Fintype.card (Sylow 2 G) ≡ 1 [MOD 2] := by
      simpa using (Fintype.card_sylow_modEq_one (G := G) (p := 2))
    have h2dvd : Fintype.card (Sylow 2 G) ∣ 7 := by
      have h := (Fintype.card_sylow_dvd_index (G := G) (p := 2))
      simpa [hG] using h
    have h2cases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
      omega
    rcases h2cases with h2one | h2seven
    · let P : Sylow 2 G := Classical.choice h2nonempty
      refine ⟨2, P, h2prime, ?_, ?_⟩
      · omega
      ·
        have hsub : Subsingleton (Sylow 2 G) := by
          exact (Fintype.card_eq_one_iff.mp h2one)
        constructor
        intro g x hx
        have hxg : g * x * g⁻¹ ∈ (g • P : Sylow 2 G) := by
          simpa using hx
        have hfix : g • P = P := by
          exact Subsingleton.elim _ _
        simpa [hfix] using hxg
    · exfalso
      have hcard7P : ∀ P : Sylow 7 G, Fintype.card P = 7 := by
        intro P
        have h := P.card_eq_multiplicity
        simpa [hG] using h
      have hcard2P : ∀ P : Sylow 2 G, Fintype.card P = 8 := by
        intro P
        have h := P.card_eq_multiplicity
        simpa [hG] using h
      have hsubcard : ∀ P : Sylow 7 G, Fintype.card {x : P // (x : G) ≠ 1} = 6 := by
        intro P
        have hcardP := hcard7P P
        simpa [hcardP] using (Fintype.card_subtype_neq (1 : P))
      let T := Σ P : Sylow 7 G, {x : P // (x : G) ≠ 1}
      let f : T → G := fun t => (t.2.1 : G)
      have hTcard : Fintype.card T = 48 := by
        dsimp [T]
        rw [Fintype.card_sigma]
        simp [hsubcard, h7eight]
      have hf_inj : Function.Injective f := by
        intro a b hab
        rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at hab
        have hxord : orderOf (x : G) = 7 := by
          have hxdiv : orderOf (x : G) ∣ 7 := by
            simpa [hcard7P P] using (orderOf_dvd_card (x := (x : P)))
          rcases Nat.dvd_prime h7prime hxdiv with h1 | h7
          · exfalso
            have hx1 : (x : G) = 1 := by
              exact (orderOf_eq_one_iff.mp h1)
            exact x.2 hx1
          · exact h7
        have hyQ : (x : G) ∈ (Q : Set G) := by
          simpa [hab] using y.1.2
        have hIntcard : Fintype.card ((P : Subgroup G) ⊓ Q) = 7 := by
          have hIntdiv : Fintype.card ((P : Subgroup G) ⊓ Q) ∣ 7 := by
            simpa [hcard7P P] using (Subgroup.card_subgroup_dvd_card ((P : Subgroup G) ⊓ Q))
          have hIntne1 : Fintype.card ((P : Subgroup G) ⊓ Q) ≠ 1 := by
            intro h1
            have hsub : Subsingleton ((P : Subgroup G) ⊓ Q) := by
              exact (Fintype.card_eq_one_iff.mp h1)
            have hxEq : (⟨x : G, ⟨x.1.2, hyQ⟩⟩ : (P : Subgroup G) ⊓ Q) = ⟨1, ⟨by simp, by simp⟩⟩ := by
              exact hsub.elim _ _
            have hx1 : (x : G) = 1 := by
              simpa using congrArg Subtype.val hxEq
            exact x.2 hx1
          rcases Nat.dvd_prime h7prime hIntdiv with h1 | h7
          · exfalso
            exact hIntne1 h1
          · exact h7
        have hEqP : (P : Subgroup G) ⊓ Q = P := by
          apply Subgroup.eq_of_le_of_card_eq inf_le_left
          simpa [hcard7P P] using hIntcard
        have hPQ : (P : Subgroup G) ≤ Q := by
          simpa [hEqP] using (inf_le_right : (P : Subgroup G) ⊓ Q ≤ Q)
        have hEqQ : Q ⊓ P = Q := by
          apply Subgroup.eq_of_le_of_card_eq inf_le_left
          have hIntcard' : Fintype.card (Q ⊓ P) = 7 := by
            simpa [inf_comm] using hIntcard
          simpa [hcard7P Q] using hIntcard'
        have hQP : Q ≤ P := by
          simpa [hEqQ] using (inf_le_right : Q ⊓ P ≤ P)
        have hPQeq : P = Q := by
          ext
          exact le_antisymm hPQ hQP
        subst hPQeq
        ext
        · rfl
        · exact Subtype.ext hab
      have hAcard : Fintype.card (Set.range f) = 48 := by
        simpa [T, hTcard] using (Fintype.card_range_of_injective f hf_inj)
      have hdisj : Disjoint (Set.range f) (H1 : Set G) := by
        refine Set.disjoint_left.mpr ?_
        intro z hzR hzH1
        rcases hzR with ⟨t, rfl⟩
        rcases t with ⟨P, y⟩
        have hyord : orderOf (y : G) = 7 := by
          have hydiv : orderOf (y : G) ∣ 7 := by
            simpa [hcard7P P] using (orderOf_dvd_card (x := (y : P)))
          rcases Nat.dvd_prime h7prime hydiv with h1 | h7
          · exfalso
            have hy1 : (y : G) = 1 := by
              exact (orderOf_eq_one_iff.mp h1)
            exact y.2 hy1
          · exact h7
        have hydiv8 : orderOf (y : G) ∣ 8 := by
          simpa [hcard2P H1] using (orderOf_dvd_card (x := (⟨y, hzH1⟩ : H1)))
        rw [hyord] at hydiv8
        norm_num at hydiv8
      have hUcard : Fintype.card (Set.range f ∪ (H1 : Set G)) = 56 := by
        simp [hAcard, hcard2P H1, hdisj]
      have hUeq : Set.range f ∪ (H1 : Set G) = Set.univ := by
        apply Set.eq_of_subset_of_card_eq
        · intro x hx
          trivial
        · simpa [hG] using hUcard
      have hQexists : ∃ Q : Sylow 2 G, Q ≠ H1 := by
        by_contra hQexists
        have hsub : Subsingleton (Sylow 2 G) := by
          intro Q R
          have hQ : Q = H1 := by
            by_contra h
            exact hQexists ⟨Q, h⟩
          have hR : R = H1 := by
            by_contra h
            exact hQexists ⟨R, h⟩
          simp [hQ, hR]
        have hcard1 : Fintype.card (Sylow 2 G) = 1 := by
          exact Fintype.card_eq_one_iff.mpr hsub
        omega
      rcases hQexists with ⟨Q, hQneq⟩
      have hQnotSub : ¬ ((Q : Set G) ⊆ H1) := by
        intro hsubset
        apply hQneq
        ext
        exact Subgroup.eq_of_le_of_card_eq hsubset (by simpa [hcard2P Q, hcard2P H1])
      rcases not_subset.mp hQnotSub with ⟨z, hzQ, hzH1⟩
      have hznotRange : z ∉ Set.range f := by
        intro hzR
        rcases hzR with ⟨t, rfl⟩
        rcases t with ⟨P, y⟩
        have hyord : orderOf (y : G) = 7 := by
          have hydiv : orderOf (y : G) ∣ 7 := by
            simpa [hcard7P P] using (orderOf_dvd_card (x := (y : P)))
          rcases Nat.dvd_prime h7prime hydiv with h1 | h7
          · exfalso
            have hy1 : (y : G) = 1 := by
              exact (orderOf_eq_one_iff.mp h1)
            exact y.2 hy1
          · exact h7
        have hzdiv8 : orderOf (y : G) ∣ 8 := by
          simpa [hcard2P Q] using (orderOf_dvd_card (x := (⟨y, hzQ⟩ : Q)))
        rw [hyord] at hzdiv8
        norm_num at hzdiv8
      have hznotUnion : z ∉ Set.range f ∪ (H1 : Set G) := by
        intro hzU
        cases hzU with
        | inl hz => exact hznotRange hz
        | inr hz => exact hzH1 hz
      have hzU : z ∈ (Set.univ : Set G) := by trivial
      have hzContr : z ∈ Set.range f ∪ (H1 : Set G) := by
        simpa [hUeq] using hzU
      exact hznotUnion hzContr
