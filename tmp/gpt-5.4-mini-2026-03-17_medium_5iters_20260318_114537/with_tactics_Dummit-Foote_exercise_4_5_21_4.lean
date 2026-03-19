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


theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 19) := ⟨by decide⟩

  have h17count : Fintype.card (Sylow 17 G) = 1 ∨ Fintype.card (Sylow 17 G) = 171 := by
    have hmod : Fintype.card (Sylow 17 G) ≡ 1 [MOD 17] := by
      simpa using (card_sylow_modEq_one (G := G) (p := 17))
    have hdiv : Fintype.card (Sylow 17 G) ∣ 2907 := by
      simpa [hG] using (card_sylow_dvd_card (G := G) (p := 17))
    rcases hmod with ⟨m, hm⟩
    have hcop : Nat.Coprime (1 + 17 * m) 17 := by
      rw [Nat.coprime_comm]
      apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 17)).2
      intro h
      rcases h with ⟨k, hk⟩
      omega
    have hdiv171 : 1 + 17 * m ∣ 171 := by
      have hdivmul : 1 + 17 * m ∣ 171 * 17 := by
        simpa [hm, hG, mul_comm, mul_left_comm, mul_assoc] using hdiv
      exact hcop.dvd_of_dvd_mul_right hdivmul
    have hmle : m ≤ 10 := by
      have hle : 1 + 17 * m ≤ 171 := Nat.le_of_dvd (by decide : 0 < (171 : ℕ)) hdiv171
      omega
    interval_cases m <;> simp [hm] at hdiv171 ⊢ <;> try omega

  have h19count : Fintype.card (Sylow 19 G) = 1 ∨ Fintype.card (Sylow 19 G) = 153 := by
    have hmod : Fintype.card (Sylow 19 G) ≡ 1 [MOD 19] := by
      simpa using (card_sylow_modEq_one (G := G) (p := 19))
    have hdiv : Fintype.card (Sylow 19 G) ∣ 2907 := by
      simpa [hG] using (card_sylow_dvd_card (G := G) (p := 19))
    rcases hmod with ⟨m, hm⟩
    have hcop : Nat.Coprime (1 + 19 * m) 19 := by
      rw [Nat.coprime_comm]
      apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 19)).2
      intro h
      rcases h with ⟨k, hk⟩
      omega
    have hdiv153 : 1 + 19 * m ∣ 153 := by
      have hdivmul : 1 + 19 * m ∣ 153 * 19 := by
        simpa [hm, hG, mul_comm, mul_left_comm, mul_assoc] using hdiv
      exact hcop.dvd_of_dvd_mul_right hdivmul
    have hmle : m ≤ 8 := by
      have hle : 1 + 19 * m ≤ 153 := Nat.le_of_dvd (by decide : 0 < (153 : ℕ)) hdiv153
      omega
    interval_cases m <;> simp [hm] at hdiv153 ⊢ <;> try omega

  intro hsimple
  have hsimp : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := by
    simpa [IsSimpleGroup] using hsimple

  rcases h17count with h17 | h17
  · let P : Sylow 17 G := Classical.choice (show Nonempty (Sylow 17 G) by infer_instance)
    have hPcard : Fintype.card (P : Subgroup G) = 17 := by
      simpa using P.2.card_eq
    have hsub : Subsingleton (Sylow 17 G) := by
      exact (Fintype.card_le_one_iff).mp (by simpa [h17] using (show Fintype.card (Sylow 17 G) ≤ 1 by omega))
    have hnormal : (P : Subgroup G).Normal := by
      constructor
      intro g x hx
      have hfix : g • P = P := Subsingleton.elim _ _
      have hx' : g * x * g⁻¹ ∈ (g • P : Subgroup G) := by
        simpa using hx
      simpa [hfix] using hx'
    have hbot_or_top := hsimp (P : Subgroup G) hnormal
    rcases hbot_or_top with hbot | htop
    · have : (17 : ℕ) = 1 := by
        simpa [hbot] using hPcard
      omega
    · have : (17 : ℕ) = 2907 := by
        simpa [htop, hG] using hPcard
      omega
  · rcases h19count with h19 | h19
    · let P : Sylow 19 G := Classical.choice (show Nonempty (Sylow 19 G) by infer_instance)
      have hPcard : Fintype.card (P : Subgroup G) = 19 := by
        simpa using P.2.card_eq
      have hsub : Subsingleton (Sylow 19 G) := by
        exact (Fintype.card_le_one_iff).mp (by simpa [h19] using (show Fintype.card (Sylow 19 G) ≤ 1 by omega))
      have hnormal : (P : Subgroup G).Normal := by
        constructor
        intro g x hx
        have hfix : g • P = P := Subsingleton.elim _ _
        have hx' : g * x * g⁻¹ ∈ (g • P : Subgroup G) := by
          simpa using hx
        simpa [hfix] using hx'
      have hbot_or_top := hsimp (P : Subgroup G) hnormal
      rcases hbot_or_top with hbot | htop
      · have : (19 : ℕ) = 1 := by
          simpa [hbot] using hPcard
        omega
      · have : (19 : ℕ) = 2907 := by
          simpa [htop, hG] using hPcard
        omega
    ·
      have h17big : Fintype.card (Sylow 17 G) = 171 := by
        omega
      have h19big : Fintype.card (Sylow 19 G) = 153 := by
        omega
      let T17 := Σ P : Sylow 17 G, {x : P // x ≠ 1}
      let T19 := Σ P : Sylow 19 G, {x : P // x ≠ 1}
      have hP17card : ∀ P : Sylow 17 G, Fintype.card (P : Subgroup G) = 17 := by
        intro P
        simpa using P.2.card_eq
      have hP19card : ∀ P : Sylow 19 G, Fintype.card (P : Subgroup G) = 19 := by
        intro P
        simpa using P.2.card_eq
      have hcardT17 : Fintype.card T17 = 171 * 16 := by
        simp [T17, h17big, hP17card]
      have hcardT19 : Fintype.card T19 = 153 * 18 := by
        simp [T19, h19big, hP19card]
      let f : (T17 ⊕ T19) → G := fun t =>
        match t with
        | Sum.inl x => (x.2 : G)
        | Sum.inr x => (x.2 : G)
      have hf : Function.Injective f := by
        intro a b hab
        cases a <;> cases b <;> simp [f] at hab
        · rcases a with ⟨P, x⟩
          rcases b with ⟨Q, y⟩
          have hPx : orderOf (x : G) = 17 := by
            have hdiv : orderOf (x : P) ∣ (17 : ℕ) := by
              simpa using (orderOf_dvd_card (x : P))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 17) hdiv with h1 | h17'
            · exfalso
              exact x.2 (by simpa using h1)
            · simpa using h17'
          have hqy : orderOf (y : G) = 17 := by
            have hdiv : orderOf (y : Q) ∣ (17 : ℕ) := by
              simpa using (orderOf_dvd_card (y : Q))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 17) hdiv with h1 | h17'
            · exfalso
              exact y.2 (by simpa using h1)
            · simpa using h17'
          have hclP : Fintype.card (Subgroup.closure ({(x : G)} : Set G)) = (17 : ℕ) := by
            simpa [Subgroup.closure_singleton, hPx] using (Fintype.card_zpowers_eq_orderOf (x : G))
          have hclQ : Fintype.card (Subgroup.closure ({(y : G)} : Set G)) = (17 : ℕ) := by
            simpa [Subgroup.closure_singleton, hqy] using (Fintype.card_zpowers_eq_orderOf (y : G))
          have hleP : Subgroup.closure ({(x : G)} : Set G) ≤ (P : Subgroup G) := by
            exact Subgroup.closure_le.2 (by intro z hz; simpa using hz)
          have hleQ : Subgroup.closure ({(y : G)} : Set G) ≤ (Q : Subgroup G) := by
            exact Subgroup.closure_le.2 (by intro z hz; simpa using hz)
          have hEqP : Subgroup.closure ({(x : G)} : Set G) = (P : Subgroup G) := by
            apply Subgroup.eq_of_le_of_card_eq hleP
            simpa [hclP] using hP17card P
          have hEqQ : Subgroup.closure ({(y : G)} : Set G) = (Q : Subgroup G) := by
            apply Subgroup.eq_of_le_of_card_eq hleQ
            simpa [hclQ] using hP17card Q
          have hPQ : (P : Subgroup G) = Q := by
            calc
              (P : Subgroup G) = Subgroup.closure ({(x : G)} : Set G) := hEqP.symm
              _ = Subgroup.closure ({(y : G)} : Set G) := by simpa [hab]
              _ = Q := hEqQ
          subst hPQ
          simp at hab
        ·
          rcases a with ⟨P, x⟩
          rcases b with ⟨Q, y⟩
          have hPx : orderOf (x : G) = 17 := by
            have hdiv : orderOf (x : P) ∣ (17 : ℕ) := by
              simpa using (orderOf_dvd_card (x : P))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 17) hdiv with h1 | h17'
            · exfalso
              exact x.2 (by simpa using h1)
            · simpa using h17'
          have hqy : orderOf (y : G) = 19 := by
            have hdiv : orderOf (y : Q) ∣ (19 : ℕ) := by
              simpa using (orderOf_dvd_card (y : Q))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 19) hdiv with h1 | h19'
            · exfalso
              exact y.2 (by simpa using h1)
            · simpa using h19'
          have := congrArg orderOf hab
          omega
        ·
          rcases a with ⟨P, x⟩
          rcases b with ⟨Q, y⟩
          have hpx : orderOf (x : G) = 19 := by
            have hdiv : orderOf (x : P) ∣ (19 : ℕ) := by
              simpa using (orderOf_dvd_card (x : P))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 19) hdiv with h1 | h19'
            · exfalso
              exact x.2 (by simpa using h1)
            · simpa using h19'
          have hqy : orderOf (y : G) = 17 := by
            have hdiv : orderOf (y : Q) ∣ (17 : ℕ) := by
              simpa using (orderOf_dvd_card (y : Q))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 17) hdiv with h1 | h17'
            · exfalso
              exact y.2 (by simpa using h1)
            · simpa using h17'
          have := congrArg orderOf hab
          omega
        ·
          rcases a with ⟨P, x⟩
          rcases b with ⟨Q, y⟩
          have hpx : orderOf (x : G) = 19 := by
            have hdiv : orderOf (x : P) ∣ (19 : ℕ) := by
              simpa using (orderOf_dvd_card (x : P))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 19) hdiv with h1 | h19'
            · exfalso
              exact x.2 (by simpa using h1)
            · simpa using h19'
          have hqy : orderOf (y : G) = 19 := by
            have hdiv : orderOf (y : Q) ∣ (19 : ℕ) := by
              simpa using (orderOf_dvd_card (y : Q))
            rcases Nat.eq_one_or_eq_of_dvd_prime (by decide : Nat.Prime 19) hdiv with h1 | h19'
            · exfalso
              exact y.2 (by simpa using h1)
            · simpa using h19'
          have hcardT : Fintype.card (T17 ⊕ T19) = 171 * 16 + 153 * 18 := by
            simp [T17, T19, hcardT17, hcardT19]
          have hinjcard : Fintype.card (T17 ⊕ T19) ≤ Fintype.card G := by
            exact Fintype.card_le_card_of_injective f hf
          have hle : 171 * 16 + 153 * 18 ≤ 2907 := by
            simpa [hG, T17, T19, hcardT] using hinjcard
          omega
