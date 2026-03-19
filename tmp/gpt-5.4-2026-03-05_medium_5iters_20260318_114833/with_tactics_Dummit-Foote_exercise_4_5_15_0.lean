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


theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  have hp13 : Nat.Prime 13 := by decide
  have hp3 : Nat.Prime 3 := by decide
  have h13dvd : 13 ∣ card G := by
    rw [hG]
    norm_num
  have h3dvd : 3 ∣ card G := by
    rw [hG]
    norm_num
  letI : Fact (Nat.Prime 13) := ⟨hp13⟩
  let P13 : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  by_cases h13one : card (Sylow 13 G) = 1
  · refine ⟨13, P13, hp13, h13dvd, ?_⟩
    exact P13.normal_of_card_eq_one h13one
  · have h13card : card (Sylow 13 G) = 27 := by
      have hmod := Sylow.card_sylow_modEq_one (G := G) (p := 13)
      have hdvd := card_sylow_dvd_index (G := G) (p := 13)
      rw [hG] at hdvd
      norm_num at hmod
      have : card (Sylow 13 G) = 1 ∨ card (Sylow 13 G) = 27 := by
        omega
      omega
    have hP13ord : ∀ P : Sylow 13 G, Fintype.card ↥(P : Subgroup G) = 13 := by
      intro P
      simpa [hG] using P.card_eq
    have huniq13 :
        ∀ {P Q : Sylow 13 G} {g : G},
          g ≠ 1 → g ∈ (P : Subgroup G) → g ∈ (Q : Subgroup G) → P = Q := by
      intro P Q g hg hPg hQg
      let H : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
      have hPcard : Fintype.card ↥(P : Subgroup G) = 13 := hP13ord P
      have hQcard : Fintype.card ↥(Q : Subgroup G) = 13 := hP13ord Q
      have hHdvdP : Fintype.card ↥H ∣ 13 := by
        have : Fintype.card ↥H ∣ Fintype.card ↥(P : Subgroup G) :=
          Subgroup.card_dvd_of_le (show H ≤ (P : Subgroup G) by
            intro x hx
            exact hx.1)
        simpa [hPcard] using this
      have hHne1 : Fintype.card ↥H ≠ 1 := by
        intro h1
        let xH : H := ⟨g, by exact ⟨hPg, hQg⟩⟩
        rcases Fintype.card_eq_one_iff.mp h1 with ⟨a, ha⟩
        have hxa : xH = a := ha xH
        have h1a : (1 : H) = a := ha 1
        have hx1 : xH = 1 := hxa.trans h1a.symm
        exact hg (Subtype.ext_iff.mp hx1)
      have hHcard : Fintype.card ↥H = 13 := by
        rcases (Nat.dvd_prime hp13).mp hHdvdP with h1 | h13
        · exact False.elim (hHne1 h1)
        · exact h13
      have hHeqP : H = (P : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge
        · intro x hx
          exact hx.1
        · omega [hHcard, hPcard]
      have hHeqQ : H = (Q : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge
        · intro x hx
          exact hx.2
        · omega [hHcard, hQcard]
      apply Subtype.ext
      exact hHeqP.trans hHeqQ.symm
    have hFiber : ∀ P : Sylow 13 G, Fintype.card {x : ↥(P : Subgroup G) // x ≠ 1} = 12 := by
      intro P
      simpa [hP13ord P] using Fintype.card_subtype_neq (1 : ↥(P : Subgroup G))
    let X := Σ P : Sylow 13 G, {x : ↥(P : Subgroup G) // x ≠ 1}
    have hXcard : Fintype.card X = 324 := by
      rw [show X = Σ P : Sylow 13 G, {x : ↥(P : Subgroup G) // x ≠ 1} by rfl]
      rw [Fintype.card_sigma]
      simp [hFiber, h13card]
    let f : X → G := fun z => z.2.1.1
    have hf_inj : Function.Injective f := by
      intro a b hab
      rcases a with ⟨P, x⟩
      rcases b with ⟨Q, y⟩
      dsimp [f] at hab
      have hPQ : P = Q := by
        apply huniq13 (P := P) (Q := Q) (g := x.1.1)
        · simpa using x.2
        · exact x.1.2
        · simpa [hab] using y.1.2
      subst hPQ
      have hxy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hab
      cases hxy
      rfl
    let R13 : Set G := Set.range f
    have hR13card : Fintype.card R13 = 324 := by
      let fr : X → R13 := fun x => ⟨f x, ⟨x, rfl⟩⟩
      have hfr : Function.Bijective fr := by
        constructor
        · intro a b h
          apply hf_inj
          exact Subtype.ext_iff.mp h
        · intro y
          rcases y.2 with ⟨x, rfl⟩
          exact ⟨x, rfl⟩
      exact Fintype.card_of_bijective fr hfr
    let T : Set G := R13ᶜ
    have hTcard : Fintype.card T = 27 := by
      rw [show T = {x : G | ¬ x ∈ R13} by rfl]
      rw [Fintype.card_subtype_compl]
      rw [hG, hR13card]
      norm_num
    letI : Fact (Nat.Prime 3) := ⟨hp3⟩
    let Q : Sylow 3 G := Classical.choice (inferInstance : Nonempty (Sylow 3 G))
    have hQcard : Fintype.card ↥(Q : Subgroup G) = 27 := by
      simpa [hG] using Q.card_eq
    have hSyl3_intoT :
        ∀ {R : Sylow 3 G} (r : ↥(R : Subgroup G)), (r : G) ∈ T := by
      intro R r
      change (r : G) ∉ Set.range f
      intro hr
      rcases hr with ⟨⟨P, x⟩, hx⟩
      have hRcard : Fintype.card ↥(R : Subgroup G) = 27 := by
        simpa [hG] using R.card_eq
      have hPcard : Fintype.card ↥(P : Subgroup G) = 13 := hP13ord P
      have hrP : (r : G) ∈ (P : Subgroup G) := by
        simpa [hx] using x.1.2
      have hrne : (r : G) ≠ 1 := by
        have : (x.1.1 : G) ≠ 1 := by simpa using x.2
        simpa [hx] using this
      let H : Subgroup G := (R : Subgroup G) ⊓ (P : Subgroup G)
      have hHdR : Fintype.card ↥H ∣ 27 := by
        have : Fintype.card ↥H ∣ Fintype.card ↥(R : Subgroup G) :=
          Subgroup.card_dvd_of_le (show H ≤ (R : Subgroup G) by
            intro y hy
            exact hy.1)
        simpa [hRcard] using this
      have hHdP : Fintype.card ↥H ∣ 13 := by
        have : Fintype.card ↥H ∣ Fintype.card ↥(P : Subgroup G) :=
          Subgroup.card_dvd_of_le (show H ≤ (P : Subgroup G) by
            intro y hy
            exact hy.2)
        simpa [hPcard] using this
      have hHcard : Fintype.card ↥H = 1 := by
        omega
      let rH : H := ⟨r, by exact ⟨r.2, hrP⟩⟩
      rcases Fintype.card_eq_one_iff.mp hHcard with ⟨a, ha⟩
      have hra : rH = a := ha rH
      have h1a : (1 : H) = a := ha 1
      have hr1 : rH = 1 := hra.trans h1a.symm
      exact hrne (Subtype.ext_iff.mp hr1)
    let eQ : ↥(Q : Subgroup G) → T := fun q => ⟨q, hSyl3_intoT q⟩
    have hRangeeQ : Fintype.card (Set.range eQ) = 27 := by
      let er : ↥(Q : Subgroup G) → Set.range eQ := fun q => ⟨eQ q, ⟨q, rfl⟩⟩
      have her : Function.Bijective er := by
        constructor
        · intro a b h
          apply Subtype.ext
          exact Subtype.ext_iff.mp (Subtype.ext_iff.mp h)
        · intro y
          rcases y.2 with ⟨x, rfl⟩
          exact ⟨x, rfl⟩
      exact Fintype.card_of_bijective er her
    have hcompRange0 : Fintype.card (((Set.range eQ)ᶜ : Set T)) = 0 := by
      rw [Fintype.card_subtype_compl]
      rw [hTcard, hRangeeQ]
      norm_num
    have hTsurj : Function.Surjective eQ := by
      intro t
      by_contra ht
      have hne : Nonempty (((Set.range eQ)ᶜ : Set T)) := ⟨⟨t, ht⟩⟩
      have hcardne : Fintype.card (((Set.range eQ)ᶜ : Set T)) ≠ 0 := Fintype.card_ne_zero
      exact hcardne hcompRange0
    have hSyl3_unique : ∀ R : Sylow 3 G, R = Q := by
      intro R
      have hRcard : Fintype.card ↥(R : Subgroup G) = 27 := by
        simpa [hG] using R.card_eq
      have hRleQ : (R : Subgroup G) ≤ (Q : Subgroup G) := by
        intro r hr
        let tr : T := ⟨r, hSyl3_intoT ⟨r, hr⟩⟩
        rcases hTsurj tr with ⟨q, hq⟩
        have hval : (q : G) = r := by
          exact congrArg Subtype.val hq
        simpa [hval] using q.2
      have hEqSub : (R : Subgroup G) = (Q : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge hRleQ
        omega [hRcard, hQcard]
      apply Subtype.ext
      exact hEqSub
    have hsub3 : Subsingleton (Sylow 3 G) := by
      refine ⟨?_⟩
      intro R S
      calc
        R = Q := hSyl3_unique R
        _ = S := (hSyl3_unique S).symm
    letI : Subsingleton (Sylow 3 G) := hsub3
    refine ⟨3, Q, hp3, h3dvd, ?_⟩
    exact Q.normal_of_subsingleton
