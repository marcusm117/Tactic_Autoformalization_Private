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


theorem exercise_4_5_22 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 132) : ¬ IsSimpleGroup G := by
  classical
  intro hs
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P11 : Sylow 11 G := Classical.choice inferInstance
  let P3 : Sylow 3 G := Classical.choice inferInstance
  let P2 : Sylow 2 G := Classical.choice inferInstance
  have hcard11 (P : Sylow 11 G) : Fintype.card P = 11 := by
    have h := P.card_eq_multiplicity
    rw [hG] at h
    have hfac : 11 ^ (Nat.factorization 132) 11 = 11 := by native_decide
    exact h.trans hfac
  have hcard3 (P : Sylow 3 G) : Fintype.card P = 3 := by
    have h := P.card_eq_multiplicity
    rw [hG] at h
    have hfac : 3 ^ (Nat.factorization 132) 3 = 3 := by native_decide
    exact h.trans hfac
  have hcard2 (P : Sylow 2 G) : Fintype.card P = 4 := by
    have h := P.card_eq_multiplicity
    rw [hG] at h
    have hfac : 2 ^ (Nat.factorization 132) 2 = 4 := by native_decide
    exact h.trans hfac
  have normal_of_card1_11 :
      Fintype.card (Sylow 11 G) = 1 → (P11 : Subgroup G).Normal := by
    intro h1
    have hidx : (P11 : Subgroup G).normalizer.index = 1 := by
      calc
        (P11 : Subgroup G).normalizer.index = Fintype.card (Sylow 11 G) := by
          simpa using P11.card_eq_index_normalizer.symm
        _ = 1 := h1
    have htop : (P11 : Subgroup G).normalizer = ⊤ := Subgroup.index_eq_one.mp hidx
    constructor
    intro g x hx
    have hg : g ∈ (P11 : Subgroup G).normalizer := by
      rw [htop]
      simp
    rw [Subgroup.mem_normalizer_iff] at hg
    exact hg x hx
  have normal_of_card1_3 :
      Fintype.card (Sylow 3 G) = 1 → (P3 : Subgroup G).Normal := by
    intro h1
    have hidx : (P3 : Subgroup G).normalizer.index = 1 := by
      calc
        (P3 : Subgroup G).normalizer.index = Fintype.card (Sylow 3 G) := by
          simpa using P3.card_eq_index_normalizer.symm
        _ = 1 := h1
    have htop : (P3 : Subgroup G).normalizer = ⊤ := Subgroup.index_eq_one.mp hidx
    constructor
    intro g x hx
    have hg : g ∈ (P3 : Subgroup G).normalizer := by
      rw [htop]
      simp
    rw [Subgroup.mem_normalizer_iff] at hg
    exact hg x hx
  have normal_of_card1_2 :
      Fintype.card (Sylow 2 G) = 1 → (P2 : Subgroup G).Normal := by
    intro h1
    have hidx : (P2 : Subgroup G).normalizer.index = 1 := by
      calc
        (P2 : Subgroup G).normalizer.index = Fintype.card (Sylow 2 G) := by
          simpa using P2.card_eq_index_normalizer.symm
        _ = 1 := h1
    have htop : (P2 : Subgroup G).normalizer = ⊤ := Subgroup.index_eq_one.mp hidx
    constructor
    intro g x hx
    have hg : g ∈ (P2 : Subgroup G).normalizer := by
      rw [htop]
      simp
    rw [Subgroup.mem_normalizer_iff] at hg
    exact hg x hx
  have h11_ne_one : Fintype.card (Sylow 11 G) ≠ 1 := by
    intro h1
    have hnorm : (P11 : Subgroup G).Normal := normal_of_card1_11 h1
    rcases hs.eq_bot_or_eq_top_of_normal hnorm with hbot | htop
    · have hP : Fintype.card P11 = 1 := by
        simpa [hbot]
      omega
    · have hP : Fintype.card P11 = 132 := by
        simpa [htop, hG]
      omega
  have h3_ne_one : Fintype.card (Sylow 3 G) ≠ 1 := by
    intro h1
    have hnorm : (P3 : Subgroup G).Normal := normal_of_card1_3 h1
    rcases hs.eq_bot_or_eq_top_of_normal hnorm with hbot | htop
    · have hP : Fintype.card P3 = 1 := by
        simpa [hbot]
      omega
    · have hP : Fintype.card P3 = 132 := by
        simpa [htop, hG]
      omega
  have h2_ne_one : Fintype.card (Sylow 2 G) ≠ 1 := by
    intro h1
    have hnorm : (P2 : Subgroup G).Normal := normal_of_card1_2 h1
    rcases hs.eq_bot_or_eq_top_of_normal hnorm with hbot | htop
    · have hP : Fintype.card P2 = 1 := by
        simpa [hbot]
      omega
    · have hP : Fintype.card P2 = 132 := by
        simpa [htop, hG]
      omega
  have hn11' : Fintype.card (Sylow 11 G) = 1 ∨ Fintype.card (Sylow 11 G) = 12 := by
    sylow_counting 11
  have hn11 : Fintype.card (Sylow 11 G) = 12 := by
    rcases hn11' with h | h
    · exact (h11_ne_one h).elim
    · exact h
  have hn3' :
      Fintype.card (Sylow 3 G) = 1 ∨
        Fintype.card (Sylow 3 G) = 4 ∨ Fintype.card (Sylow 3 G) = 22 := by
    sylow_counting 3
  have hn3 : Fintype.card (Sylow 3 G) = 4 ∨ Fintype.card (Sylow 3 G) = 22 := by
    rcases hn3' with h | h | h
    · exact (h3_ne_one h).elim
    · exact Or.inl h
    · exact Or.inr h
  have order11_of_mem :
      ∀ {P : Sylow 11 G} {g : G}, g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = 11 := by
    intro P g hg hg1
    let x : P := ⟨g, hg⟩
    have hxpow : g ^ 11 = 1 := by
      have hx : x ^ Fintype.card P = 1 := by
        simpa using (pow_card_eq_one (a := x))
      simpa [hcard11 P] using congrArg Subtype.val hx
    have hdiv : orderOf g ∣ 11 := orderOf_dvd_of_pow_eq_one hxpow
    rcases (Nat.dvd_prime (show Nat.Prime 11 by decide)).mp hdiv with h | h
    · exact (hg1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have order3_of_mem :
      ∀ {P : Sylow 3 G} {g : G}, g ∈ (P : Subgroup G) → g ≠ 1 → orderOf g = 3 := by
    intro P g hg hg1
    let x : P := ⟨g, hg⟩
    have hxpow : g ^ 3 = 1 := by
      have hx : x ^ Fintype.card P = 1 := by
        simpa using (pow_card_eq_one (a := x))
      simpa [hcard3 P] using congrArg Subtype.val hx
    have hdiv : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hxpow
    rcases (Nat.dvd_prime (show Nat.Prime 3 by decide)).mp hdiv with h | h
    · exact (hg1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have order_dvd4_of_mem :
      ∀ {P : Sylow 2 G} {g : G}, g ∈ (P : Subgroup G) → orderOf g ∣ 4 := by
    intro P g hg
    let x : P := ⟨g, hg⟩
    have hxpow : g ^ 4 = 1 := by
      have hx : x ^ Fintype.card P = 1 := by
        simpa using (pow_card_eq_one (a := x))
      simpa [hcard2 P] using congrArg Subtype.val hx
    exact orderOf_dvd_of_pow_eq_one hxpow
  have eq_sylow11 :
      ∀ {P Q : Sylow 11 G} {g : G},
        g ∈ (P : Subgroup G) → g ∈ (Q : Subgroup G) → g ≠ 1 → P = Q := by
    intro P Q g hgP hgQ hg1
    have horder : orderOf g = 11 := order11_of_mem hgP hg1
    have hcardz : Fintype.card (Subgroup.zpowers g) = 11 := by
      simpa [horder] using (card_zpowers (a := g))
    have hEqP : Subgroup.zpowers g = (P : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgP)
        (by simpa [hcard11 P] using hcardz.le)
    have hEqQ : Subgroup.zpowers g = (Q : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgQ)
        (by simpa [hcard11 Q] using hcardz.le)
    have hsub : (P : Subgroup G) = (Q : Subgroup G) := by
      calc
        (P : Subgroup G) = Subgroup.zpowers g := hEqP.symm
        _ = (Q : Subgroup G) := hEqQ
    cases P
    cases Q
    cases hsub
    rfl
  have eq_sylow3 :
      ∀ {P Q : Sylow 3 G} {g : G},
        g ∈ (P : Subgroup G) → g ∈ (Q : Subgroup G) → g ≠ 1 → P = Q := by
    intro P Q g hgP hgQ hg1
    have horder : orderOf g = 3 := order3_of_mem hgP hg1
    have hcardz : Fintype.card (Subgroup.zpowers g) = 3 := by
      simpa [horder] using (card_zpowers (a := g))
    have hEqP : Subgroup.zpowers g = (P : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgP)
        (by simpa [hcard3 P] using hcardz.le)
    have hEqQ : Subgroup.zpowers g = (Q : Subgroup G) := by
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.2 hgQ)
        (by simpa [hcard3 Q] using hcardz.le)
    have hsub : (P : Subgroup G) = (Q : Subgroup G) := by
      calc
        (P : Subgroup G) = Subgroup.zpowers g := hEqP.symm
        _ = (Q : Subgroup G) := hEqQ
    cases P
    cases Q
    cases hsub
    rfl
  rcases hn3 with hn3 | hn3
  · have hexQ2 : ∃ Q : Sylow 2 G, Q ≠ P2 := by
      by_contra hno
      push_neg at hno
      have hsub : Subsingleton (Sylow 2 G) := ⟨by
        intro a b
        calc
          a = P2 := hno a
          _ = b := (hno b).symm⟩
      letI := hsub
      have h1 : Fintype.card (Sylow 2 G) = 1 := by
        simpa using (Fintype.card_of_subsingleton (Sylow 2 G))
      exact h2_ne_one h1
    rcases hexQ2 with ⟨Q2, hQ2ne⟩
    have hnotle : ¬ ((Q2 : Subgroup G) ≤ (P2 : Subgroup G)) := by
      intro hle
      have hsub : (Q2 : Subgroup G) = (P2 : Subgroup G) := by
        exact Subgroup.eq_of_le_of_card_ge hle (by
          have hq := hcard2 Q2
          have hp := hcard2 P2
          omega)
      apply hQ2ne
      cases P2
      cases Q2
      cases hsub
      rfl
    have hxexist : ∃ x : G, x ∈ (Q2 : Subgroup G) ∧ x ∉ (P2 : Subgroup G) := by
      by_contra hnone
      apply hnotle
      intro x hx
      by_contra hxP
      exact hnone ⟨x, hx, hxP⟩
    rcases hxexist with ⟨x2, hx2Q, hx2P⟩
    have hx2ne : x2 ≠ 1 := by
      intro hx
      exact hx2P (by simpa [hx] using (show (1 : G) ∈ (P2 : Subgroup G) from (P2 : Subgroup G).one_mem))
    have hx2div4 : orderOf x2 ∣ 4 := order_dvd4_of_mem hx2Q
    let A11 := Σ P : Sylow 11 G, {x : P // ((x : G) ≠ 1)}
    let A3 := Σ P : Sylow 3 G, {x : P // ((x : G) ≠ 1)}
    let B2 := {x : P2 // ((x : G) ≠ 1)}
    let A := Sum Unit (Sum A11 (Sum A3 (Sum B2 Unit)))
    let f : A → G := fun a =>
      match a with
      | Sum.inl _ => 1
      | Sum.inr (Sum.inl u) => u.2.1
      | Sum.inr (Sum.inr (Sum.inl u)) => u.2.1
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl u))) => u.1
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => x2
    have hf : Function.Injective f := by
      intro a b h
      rcases a with _ | a <;> rcases b with _ | b
      · rfl
      · rcases b with b | b
        · exfalso
          exact b.2.2 (by simpa [f] using h.symm)
        · rcases b with b | b
          · exfalso
            exact b.2.2 (by simpa [f] using h.symm)
          · rcases b with b | _
            · exfalso
              exact b.2 (by simpa [f] using h.symm)
            · exfalso
              exact hx2ne (by simpa [f] using h.symm)
      · rcases a with a | a
        · exfalso
          exact a.2.2 (by simpa [f] using h)
        · rcases a with a | a
          · exfalso
            exact a.2.2 (by simpa [f] using h)
          · rcases a with a | _
            · exfalso
              exact a.2 (by simpa [f] using h)
            · exfalso
              exact hx2ne (by simpa [f] using h)
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        have hPQ : P = Q := eq_sylow11 x.1.2 (by simpa [h] using y.1.2) x.2
        cases hPQ
        have hxy : x = y := by
          apply Subtype.ext
          apply Subtype.ext
          exact h
        cases hxy
        rfl
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        exfalso
        have h11 : orderOf ((x.1 : P) : G) = 11 := order11_of_mem x.1.2 x.2
        have hdiv4 : orderOf ((x.1 : P) : G) ∣ 4 := by
          have hxmem : ((x.1 : P) : G) ∈ (Q : Subgroup G) := by
            simpa [h] using y.1.2
          have h3 : orderOf ((x.1 : P) : G) = 3 := order3_of_mem hxmem x.2
          have : 11 = 3 := by simpa [h11] using h3.symm
          omega
        have : 11 ∣ 4 := by
          simpa [h11] using hdiv4
        norm_num at this
      · rcases a with ⟨P, x⟩
        rcases b with b | _
        · dsimp [f] at h
          exfalso
          have h11 : orderOf ((x.1 : P) : G) = 11 := order11_of_mem x.1.2 x.2
          have hdiv4 : orderOf ((x.1 : P) : G) ∣ 4 := by
            have hxmem : ((x.1 : P) : G) ∈ (P2 : Subgroup G) := by
              simpa [h] using b.1.2
            exact order_dvd4_of_mem hxmem
          have : 11 ∣ 4 := by
            simpa [h11] using hdiv4
          norm_num at this
        · dsimp [f] at h
          exfalso
          have h11 : orderOf x2 = 11 := by
            have hxmem : x2 ∈ (P : Subgroup G) := by
              simpa [h] using x.1.2
            exact order11_of_mem hxmem hx2ne
          have : 11 ∣ 4 := by
            simpa [h11] using hx2div4
          norm_num at this
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        exfalso
        have h11 : orderOf ((y.1 : Q) : G) = 11 := by
          have hymem : ((y.1 : Q) : G) ∈ (P : Subgroup G) := by
            simpa [h] using x.1.2
          exact order11_of_mem hymem y.2
        have h3 : orderOf ((y.1 : Q) : G) = 3 := order3_of_mem y.1.2 y.2
        have : 11 = 3 := by simpa [h11] using h3.symm
        omega
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        have hPQ : P = Q := eq_sylow3 x.1.2 (by simpa [h] using y.1.2) x.2
        cases hPQ
        have hxy : x = y := by
          apply Subtype.ext
          apply Subtype.ext
          exact h
        cases hxy
        rfl
      · rcases a with ⟨P, x⟩
        rcases b with b | _
        · dsimp [f] at h
          exfalso
          have h3 : orderOf ((x.1 : P) : G) = 3 := order3_of_mem x.1.2 x.2
          have hdiv4 : orderOf ((x.1 : P) : G) ∣ 4 := by
            have hxmem : ((x.1 : P) : G) ∈ (P2 : Subgroup G) := by
              simpa [h] using b.1.2
            exact order_dvd4_of_mem hxmem
          have : 3 ∣ 4 := by
            simpa [h3] using hdiv4
          norm_num at this
        · dsimp [f] at h
          exfalso
          have h3 : orderOf x2 = 3 := by
            have hxmem : x2 ∈ (P : Subgroup G) := by
              simpa [h] using x.1.2
            exact order3_of_mem hxmem hx2ne
          have : 3 ∣ 4 := by
            simpa [h3] using hx2div4
          norm_num at this
      · rcases a with a | _
        · rcases b with b | _
          · dsimp [f] at h
            have hxy : a = b := by
              apply Subtype.ext
              apply Subtype.ext
              exact h
            cases hxy
            rfl
          · exfalso
            have hmem : ((a.1 : P2) : G) ∈ (P2 : Subgroup G) := a.1.2
            have : x2 ∈ (P2 : Subgroup G) := by
              rwa [h] at hmem
            exact hx2P this
        · rcases b with b | _
          · exfalso
            have hmem : ((b.1 : P2) : G) ∈ (P2 : Subgroup G) := b.1.2
            have : x2 ∈ (P2 : Subgroup G) := by
              rwa [h.symm] at hmem
            exact hx2P this
          · rfl
    have hA11 : Fintype.card A11 = 120 := by
      simp [A11, hcard11, hn11]
    have hA3 : Fintype.card A3 = 8 := by
      simp [A3, hcard3, hn3]
    have hB2 : Fintype.card B2 = 3 := by
      simp [B2, hcard2 P2]
    have hA : Fintype.card A = 133 := by
      simp [A, hA11, hA3, hB2]
    have hle : Fintype.card A ≤ Fintype.card G := Fintype.card_le_of_injective f hf
    omega
  · let A11 := Σ P : Sylow 11 G, {x : P // ((x : G) ≠ 1)}
    let A3 := Σ P : Sylow 3 G, {x : P // ((x : G) ≠ 1)}
    let A := Sum Unit (Sum A11 A3)
    let f : A → G := fun a =>
      match a with
      | Sum.inl _ => 1
      | Sum.inr (Sum.inl u) => u.2.1
      | Sum.inr (Sum.inr u) => u.2.1
    have hf : Function.Injective f := by
      intro a b h
      rcases a with _ | a <;> rcases b with _ | b
      · rfl
      · rcases b with b | b
        · exfalso
          exact b.2.2 (by simpa [f] using h.symm)
        · exfalso
          exact b.2.2 (by simpa [f] using h.symm)
      · rcases a with a | a
        · exfalso
          exact a.2.2 (by simpa [f] using h)
        · exfalso
          exact a.2.2 (by simpa [f] using h)
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        have hPQ : P = Q := eq_sylow11 x.1.2 (by simpa [h] using y.1.2) x.2
        cases hPQ
        have hxy : x = y := by
          apply Subtype.ext
          apply Subtype.ext
          exact h
        cases hxy
        rfl
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        exfalso
        have h11 : orderOf ((x.1 : P) : G) = 11 := order11_of_mem x.1.2 x.2
        have h3 : orderOf ((x.1 : P) : G) = 3 := by
          have hxmem : ((x.1 : P) : G) ∈ (Q : Subgroup G) := by
            simpa [h] using y.1.2
          exact order3_of_mem hxmem x.2
        have : 11 = 3 := by simpa [h11] using h3.symm
        omega
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        exfalso
        have h11 : orderOf ((y.1 : Q) : G) = 11 := by
          have hymem : ((y.1 : Q) : G) ∈ (P : Subgroup G) := by
            simpa [h] using x.1.2
          exact order11_of_mem hymem y.2
        have h3 : orderOf ((y.1 : Q) : G) = 3 := order3_of_mem y.1.2 y.2
        have : 11 = 3 := by simpa [h11] using h3.symm
        omega
      · rcases a with ⟨P, x⟩
        rcases b with ⟨Q, y⟩
        dsimp [f] at h
        have hPQ : P = Q := eq_sylow3 x.1.2 (by simpa [h] using y.1.2) x.2
        cases hPQ
        have hxy : x = y := by
          apply Subtype.ext
          apply Subtype.ext
          exact h
        cases hxy
        rfl
    have hA11 : Fintype.card A11 = 120 := by
      simp [A11, hcard11, hn11]
    have hA3 : Fintype.card A3 = 44 := by
      simp [A3, hcard3, hn3]
    have hA : Fintype.card A = 165 := by
      simp [A, hA11, hA3]
    have hle : Fintype.card A ≤ Fintype.card G := Fintype.card_le_of_injective f hf
    omega
