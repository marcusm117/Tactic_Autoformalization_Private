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
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hcard7 (P : Sylow 7 G) : Fintype.card P = 7 := by
    simpa [Nat.card_eq_fintype_card, hG, show Nat.factorization 56 7 = 1 by native_decide] using
      P.card_eq_multiplicity
  have hcard2 (P : Sylow 2 G) : Fintype.card P = 8 := by
    simpa [Nat.card_eq_fintype_card, hG, show Nat.factorization 56 2 = 3 by native_decide] using
      P.card_eq_multiplicity
  have hpow7 {P : Sylow 7 G} {g : G} (hg : g ∈ (P : Subgroup G)) : g ^ 7 = 1 := by
    let gP : P := ⟨g, hg⟩
    have h : gP ^ Fintype.card P = 1 := by
      simpa using (pow_card_eq_one (x := gP))
    have h' := congrArg Subtype.val h
    simpa [hcard7 P] using h'
  have hpow8 {P : Sylow 2 G} {g : G} (hg : g ∈ (P : Subgroup G)) : g ^ 8 = 1 := by
    let gP : P := ⟨g, hg⟩
    have h : gP ^ Fintype.card P = 1 := by
      simpa using (pow_card_eq_one (x := gP))
    have h' := congrArg Subtype.val h
    simpa [hcard2 P] using h'
  have hnot_both {P : Sylow 7 G} {Q : Sylow 2 G} {g : G}
      (hgP : g ∈ (P : Subgroup G)) (hgQ : g ∈ (Q : Subgroup G)) (hg1 : g ≠ 1) : False := by
    have hdiv7 : orderOf g ∣ 7 := orderOf_dvd_of_pow_eq_one (hpow7 hgP)
    have hdiv8 : orderOf g ∣ 8 := orderOf_dvd_of_pow_eq_one (hpow8 hgQ)
    have hdiv1 : orderOf g ∣ 1 := by
      simpa using Nat.dvd_gcd hdiv7 hdiv8
    have hord : orderOf g = 1 := Nat.dvd_one.mp hdiv1
    exact hg1 (orderOf_eq_one_iff.mp hord)
  have hord7_of_mem {P : Sylow 7 G} {g : G}
      (hgP : g ∈ (P : Subgroup G)) (hg1 : g ≠ 1) : orderOf g = 7 := by
    have hdiv7 : orderOf g ∣ 7 := orderOf_dvd_of_pow_eq_one (hpow7 hgP)
    have hneq : orderOf g ≠ 1 := by
      intro h1
      exact hg1 (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime (show Nat.Prime 7 by decide)).1 hdiv7 with h1 | h7
    · exact (hneq h1).elim
    · exact h7
  have hsame_sylow7 {P P' : Sylow 7 G} {g : G}
      (hgP : g ∈ (P : Subgroup G)) (hgP' : g ∈ (P' : Subgroup G)) (hg1 : g ≠ 1) :
      P = P' := by
    have horder : orderOf g = 7 := hord7_of_mem hgP hg1
    have hzcard : Nat.card (Subgroup.zpowers g) = 7 := by
      simpa [horder] using (Nat.card_zpowers g)
    have hzleP : Subgroup.zpowers g ≤ (P : Subgroup G) := by
      exact (Subgroup.zpowers_le).2 hgP
    have hzleP' : Subgroup.zpowers g ≤ (P' : Subgroup G) := by
      exact (Subgroup.zpowers_le).2 hgP'
    have hEqP : Subgroup.zpowers g = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hzleP
      rw [Nat.card_eq_fintype_card, hcard7 P, hzcard]
    have hEqP' : Subgroup.zpowers g = (P' : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hzleP'
      rw [Nat.card_eq_fintype_card, hcard7 P', hzcard]
    ext x
    change x ∈ (P : Subgroup G) ↔ x ∈ (P' : Subgroup G)
    simpa [hEqP, hEqP']
  have hs7cases : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    sylow_counting 7
  rcases hs7cases with h7one | h7eight
  · haveI : Subsingleton (Sylow 7 G) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
    refine ⟨7, P, by decide, ?_, ?_⟩
    · norm_num [hG]
    · exact P.normal_of_subsingleton
  · have hs2cases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
      sylow_counting 2
    rcases hs2cases with h2one | h2seven
    · haveI : Subsingleton (Sylow 2 G) :=
        Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let Q : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
      refine ⟨2, Q, by decide, ?_, ?_⟩
      · norm_num [hG]
      · exact Q.normal_of_subsingleton
    · exfalso
      have hfiber : ∀ P : Sylow 7 G, Fintype.card {x : P // x ≠ 1} = 6 := by
        intro P
        simpa [hcard7 P] using (Fintype.card_subtype_compl (p := fun x : P => x = 1))
      have hsigma :
          Fintype.card (Σ P : Sylow 7 G, {x : P // x ≠ 1}) = 48 := by
        rw [Fintype.card_sigma]
        simp [hfiber, h7eight]
      have hnotsub2 : ¬ Subsingleton (Sylow 2 G) := by
        intro hsub
        have hle : Fintype.card (Sylow 2 G) ≤ 1 :=
          Fintype.card_le_one_iff_subsingleton.mpr hsub
        omega
      rcases not_subsingleton_iff_exists_ne.mp hnotsub2 with ⟨Q, Q', hQQ'⟩
      have hex : ∃ t : G, t ∈ (Q' : Subgroup G) ∧ t ∉ (Q : Subgroup G) := by
        by_contra h
        have hle : (Q' : Subgroup G) ≤ (Q : Subgroup G) := by
          intro g hg
          by_contra hgQ
          exact h ⟨g, hg, hgQ⟩
        have hEqSub : (Q' : Subgroup G) = (Q : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge hle
          rw [Nat.card_eq_fintype_card, hcard2 Q, Nat.card_eq_fintype_card, hcard2 Q']
        apply hQQ'
        ext g
        change g ∈ (Q : Subgroup G) ↔ g ∈ (Q' : Subgroup G)
        simpa [hEqSub]
      rcases hex with ⟨t, htQ', htQ⟩
      let f : (((Σ P : Sylow 7 G, {x : P // x ≠ 1}) ⊕ Q) ⊕ PUnit) → G
        | Sum.inl (Sum.inl a) => a.2.1
        | Sum.inl (Sum.inr q) => q
        | Sum.inr _ => t
      have hf : Function.Injective f := by
        intro a b h
        rcases a with (a | q) | u <;> rcases b with (b | q') | u' <;> dsimp [f] at h
        · rcases a with ⟨P, x⟩
          rcases b with ⟨P', x'⟩
          have hxgneq : (((x.1 : P) : G)) ≠ 1 := by
            intro hx1
            exact x.2 (Subtype.ext hx1)
          have hxP' : (((x.1 : P) : G)) ∈ (P' : Subgroup G) := by
            simpa [h] using x'.1.property
          have hPP' : P = P' := hsame_sylow7 x.1.property hxP' hxgneq
          subst hPP'
          have hx1 : x.1 = x'.1 := by
            apply Subtype.ext
            simpa using h
          have hx : x = x' := by
            apply Subtype.ext
            exact hx1
          subst hx
          rfl
        · rcases a with ⟨P, x⟩
          exfalso
          have hxgneq : (((x.1 : P) : G)) ≠ 1 := by
            intro hx1
            exact x.2 (Subtype.ext hx1)
          have hxQ : (((x.1 : P) : G)) ∈ (Q : Subgroup G) := by
            simpa [h] using q'.property
          exact hnot_both x.1.property hxQ hxgneq
        · rcases a with ⟨P, x⟩
          exfalso
          have hxgneq : (((x.1 : P) : G)) ≠ 1 := by
            intro hx1
            exact x.2 (Subtype.ext hx1)
          have hxt : (((x.1 : P) : G)) ∈ (Q' : Subgroup G) := by
            simpa [h] using htQ'
          exact hnot_both x.1.property hxt hxgneq
        · rcases b with ⟨P, x⟩
          exfalso
          have hxgneq : (((x.1 : P) : G)) ≠ 1 := by
            intro hx1
            exact x.2 (Subtype.ext hx1)
          have hxQ : (((x.1 : P) : G)) ∈ (Q : Subgroup G) := by
            simpa [h.symm] using q.property
          exact hnot_both x.1.property hxQ hxgneq
        · have hqq' : q = q' := by
            apply Subtype.ext
            simpa using h
          subst hqq'
          rfl
        · exfalso
          have htQ'' : t ∈ (Q : Subgroup G) := by
            simpa [h] using q.property
          exact htQ htQ''
        · rcases b with ⟨P, x⟩
          exfalso
          have hxgneq : (((x.1 : P) : G)) ≠ 1 := by
            intro hx1
            exact x.2 (Subtype.ext hx1)
          have hxt : (((x.1 : P) : G)) ∈ (Q' : Subgroup G) := by
            simpa [h.symm] using htQ'
          exact hnot_both x.1.property hxt hxgneq
        · exfalso
          have htQ'' : t ∈ (Q : Subgroup G) := by
            simpa [h.symm] using q'.property
          exact htQ htQ''
        · cases u
          cases u'
          rfl
      have h57 : Fintype.card (((Σ P : Sylow 7 G, {x : P // x ≠ 1}) ⊕ Q) ⊕ PUnit) = 57 := by
        simp [hsigma, hcard2 Q]
      have hle : 57 ≤ Fintype.card G := by
        simpa [h57] using Fintype.card_le_of_injective f hf
      omega [hle, hG]
