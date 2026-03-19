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


theorem exercise_4_5_16 {p q r : ℕ} {G : Type*} [Group G]
  [Fintype G]  (hpqr : p < q ∧ q < r)
  (hpqr1 : p.Prime ∧ q.Prime ∧ r.Prime)(hG : card G = p*q*r) :
  (∃ (P : Sylow p G), P.Normal) ∨ (∃ (P : Sylow q G), P.Normal) ∨ (∃ (P : Sylow r G), P.Normal) := by
  classical
  rcases hpqr with ⟨hpq, hqr⟩
  rcases hpqr1 with ⟨hp, hq, hr⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact r.Prime := ⟨hr⟩
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hqr_ne : q ≠ r := ne_of_lt hqr
  have hpr_ne : p ≠ r := ne_of_lt (lt_trans hpq hqr)
  have hfacq : (p * q * r).factorization q = 1 := by
    simp [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hr.ne_zero,
      hpq_ne, hqr_ne, hpr_ne, mul_assoc, mul_left_comm, mul_comm]
  have hfacr : (p * q * r).factorization r = 1 := by
    simp [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hr.ne_zero,
      hpq_ne, hqr_ne, hpr_ne, mul_assoc, mul_left_comm, mul_comm]
  have hq_card (Q : Sylow q G) : Fintype.card Q = q := by
    simpa [hG, hfacq, mul_assoc, mul_left_comm, mul_comm] using Q.card_eq_multiplicity
  have hr_card (R : Sylow r G) : Fintype.card R = r := by
    simpa [hG, hfacr, mul_assoc, mul_left_comm, mul_comm] using R.card_eq_multiplicity
  by_cases hnr1 : Fintype.card (Sylow r G) = 1
  · rcases Fintype.card_eq_one_iff.mp hnr1 with ⟨R, hR⟩
    haveI : Subsingleton (Sylow r G) := ⟨by
      intro A B
      rw [hR A, hR B]⟩
    exact Or.inr <| Or.inr <| ⟨R, Sylow.normal_of_subsingleton R⟩
  · by_cases hnq1 : Fintype.card (Sylow q G) = 1
    · rcases Fintype.card_eq_one_iff.mp hnq1 with ⟨Q, hQ⟩
      haveI : Subsingleton (Sylow q G) := ⟨by
        intro A B
        rw [hQ A, hQ B]⟩
      exact Or.inr <| Or.inl <| ⟨Q, Sylow.normal_of_subsingleton Q⟩
    · have hdivG_r : Fintype.card (Sylow r G) ∣ Fintype.card G := by
        simpa using (card_sylow_dvd_card (G := G) (p := r))
      have hmodr : Fintype.card (Sylow r G) ≡ 1 [MOD r] := by
        simpa using (card_sylow_modEq_one (G := G) (p := r))
      have hcardr : Fintype.card (Sylow r G) = p * q := by
        let n := Fintype.card (Sylow r G)
        have hn0 : 0 < n := by
          dsimp [n]
          exact Fintype.card_pos_iff.mpr inferInstance
        have h1le : 1 ≤ n := Nat.succ_le_of_lt hn0
        have hn1 : 1 < n := by
          have hne : 1 ≠ n := by
            intro h
            exact hnr1 h.symm
          exact lt_of_le_of_ne h1le hne
        have hr_not_dvd_n : ¬ r ∣ n := by
          intro hdiv
          have hz : n ≡ 0 [MOD r] := by
            exact Nat.modEq_zero_iff_dvd.mpr hdiv
          have h01 : (0 : Nat) ≡ 1 [MOD r] := hz.symm.trans (by simpa [n] using hmodr)
          have : r ∣ 1 := Nat.modEq_zero_iff_dvd.mp h01.symm
          exact hr.not_dvd_one this
        have hcopr : Nat.Coprime n r := ((hr.coprime_iff_not_dvd).2 hr_not_dvd_n).symm
        have hdivpq : n ∣ p * q := by
          rw [hG] at hdivG_r
          exact hcopr.dvd_of_dvd_mul_left (by simpa [n, mul_assoc, mul_left_comm, mul_comm] using hdivG_r)
        by_cases hpn : p ∣ n
        · rcases hpn with ⟨m, hm⟩
          have hmdivq : m ∣ q := by
            have hpmul : p * m ∣ p * q := by
              simpa [n, hm, mul_assoc, mul_left_comm, mul_comm] using hdivpq
            exact (Nat.mul_dvd_mul_iff_left hp.pos).1 hpmul
          rcases (Nat.dvd_prime hq).1 hmdivq with hm1 | hmq
          · have hnp : n = p := by simpa [n, hm, hm1]
            have hp1 : p ≡ 1 [MOD r] := by simpa [n, hnp] using hmodr
            have : p = 1 := hp1.eq_of_lt_of_lt (lt_trans hpq hqr) hr.one_lt
            exact (hp.ne_one this).elim
          · simpa [n, hm, hmq, mul_comm]
        · have hcop : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).2 hpn).symm
          have hdivq : n ∣ q := by
            exact hcop.dvd_of_dvd_mul_left (by simpa [n, mul_assoc, mul_left_comm, mul_comm] using hdivpq)
          rcases (Nat.dvd_prime hq).1 hdivq with h1 | hq'
          · exact (hnr1 (by simpa [n] using h1.symm)).elim
          · have hnq : n = q := hq'
            have hq1 : q ≡ 1 [MOD r] := by simpa [n, hnq] using hmodr
            have : q = 1 := hq1.eq_of_lt_of_lt hqr hr.one_lt
            exact (hq.ne_one this).elim
      have hdivG_q : Fintype.card (Sylow q G) ∣ Fintype.card G := by
        simpa using (card_sylow_dvd_card (G := G) (p := q))
      have hmodq : Fintype.card (Sylow q G) ≡ 1 [MOD q] := by
        simpa using (card_sylow_modEq_one (G := G) (p := q))
      have hq_lower : r ≤ Fintype.card (Sylow q G) := by
        let n := Fintype.card (Sylow q G)
        have hn0 : 0 < n := by
          dsimp [n]
          exact Fintype.card_pos_iff.mpr inferInstance
        have h1le : 1 ≤ n := Nat.succ_le_of_lt hn0
        have hn1 : 1 < n := by
          have hne : 1 ≠ n := by
            intro h
            exact hnq1 h.symm
          exact lt_of_le_of_ne h1le hne
        have hq_not_dvd_n : ¬ q ∣ n := by
          intro hdiv
          have hz : n ≡ 0 [MOD q] := by
            exact Nat.modEq_zero_iff_dvd.mpr hdiv
          have h01 : (0 : Nat) ≡ 1 [MOD q] := hz.symm.trans (by simpa [n] using hmodq)
          have : q ∣ 1 := Nat.modEq_zero_iff_dvd.mp h01.symm
          exact hq.not_dvd_one this
        have hcopq : Nat.Coprime n q := ((hq.coprime_iff_not_dvd).2 hq_not_dvd_n).symm
        have hdivpr : n ∣ p * r := by
          rw [hG] at hdivG_q
          exact hcopq.dvd_of_dvd_mul_left (by simpa [n, mul_assoc, mul_left_comm, mul_comm] using hdivG_q)
        by_cases hpn : p ∣ n
        · rcases hpn with ⟨m, hm⟩
          have hmdivr : m ∣ r := by
            have hpmul : p * m ∣ p * r := by
              simpa [n, hm, mul_assoc, mul_left_comm, mul_comm] using hdivpr
            exact (Nat.mul_dvd_mul_iff_left hp.pos).1 hpmul
          rcases (Nat.dvd_prime hr).1 hmdivr with hm1 | hmr
          · have hnp : n = p := by simpa [n, hm, hm1]
            have hp1 : p ≡ 1 [MOD q] := by simpa [n, hnp] using hmodq
            have : p = 1 := hp1.eq_of_lt_of_lt hpq hq.one_lt
            exact (hp.ne_one this).elim
          · omega
        · have hcop : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).2 hpn).symm
          have hdivr : n ∣ r := by
            exact hcop.dvd_of_dvd_mul_left (by simpa [n, mul_assoc, mul_left_comm, mul_comm] using hdivpr)
          rcases (Nat.dvd_prime hr).1 hdivr with h1 | hr'
          · exact (hnq1 (by simpa [n] using h1.symm)).elim
          · omega
      have same_q {Q Q' : Sylow q G} {x : G}
          (hx : x ∈ (↑Q : Subgroup G)) (hx' : x ∈ (↑Q' : Subgroup G)) (hxn : x ≠ 1) :
          Q = Q' := by
        let I : Subgroup G := (↑Q : Subgroup G) ⊓ ↑Q'
        have hzmem : x ∈ I := ⟨hx, hx'⟩
        let z : I := ⟨x, hzmem⟩
        have hIgt : 1 < Fintype.card I := by
          refine Fintype.one_lt_card_iff.mpr ?_
          refine ⟨1, z, ?_⟩
          intro hz
          exact hxn ((congrArg Subtype.val hz).symm)
        have hIdvdq : Fintype.card I ∣ q := by
          simpa [I, hq_card Q] using
            (Subgroup.card_dvd_of_le (show I ≤ (↑Q : Subgroup G) by
              exact inf_le_left))
        have hIcard : Fintype.card I = q := by
          rcases (Nat.dvd_prime hq).1 hIdvdq with h1 | hq'
          · omega
          · exact hq'
        have hIeqQ : I = (↑Q : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge
          · exact inf_le_left
          · simpa [I, hIcard, hq_card Q]
        have hIeqQ' : I = (↑Q' : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge
          · exact inf_le_right
          · simpa [I, hIcard, hq_card Q']
        have hQQ' : (↑Q : Subgroup G) = ↑Q' := by
          exact hIeqQ.symm.trans hIeqQ'
        apply Subtype.ext
        simpa using hQQ'
      have same_r {R R' : Sylow r G} {x : G}
          (hx : x ∈ (↑R : Subgroup G)) (hx' : x ∈ (↑R' : Subgroup G)) (hxn : x ≠ 1) :
          R = R' := by
        let I : Subgroup G := (↑R : Subgroup G) ⊓ ↑R'
        have hzmem : x ∈ I := ⟨hx, hx'⟩
        let z : I := ⟨x, hzmem⟩
        have hIgt : 1 < Fintype.card I := by
          refine Fintype.one_lt_card_iff.mpr ?_
          refine ⟨1, z, ?_⟩
          intro hz
          exact hxn ((congrArg Subtype.val hz).symm)
        have hIdvdr : Fintype.card I ∣ r := by
          simpa [I, hr_card R] using
            (Subgroup.card_dvd_of_le (show I ≤ (↑R : Subgroup G) by
              exact inf_le_left))
        have hIcard : Fintype.card I = r := by
          rcases (Nat.dvd_prime hr).1 hIdvdr with h1 | hr'
          · omega
          · exact hr'
        have hIeqR : I = (↑R : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge
          · exact inf_le_left
          · simpa [I, hIcard, hr_card R]
        have hIeqR' : I = (↑R' : Subgroup G) := by
          apply Subgroup.eq_of_le_of_card_ge
          · exact inf_le_right
          · simpa [I, hIcard, hr_card R']
        have hRR' : (↑R : Subgroup G) = ↑R' := by
          exact hIeqR.symm.trans hIeqR'
        apply Subtype.ext
        simpa using hRR'
      have absurd_qr {Q : Sylow q G} {R : Sylow r G} {x : G}
          (hxQ : x ∈ (↑Q : Subgroup G)) (hxR : x ∈ (↑R : Subgroup G)) (hxn : x ≠ 1) :
          False := by
        let I : Subgroup G := (↑Q : Subgroup G) ⊓ ↑R
        have hzmem : x ∈ I := ⟨hxQ, hxR⟩
        let z : I := ⟨x, hzmem⟩
        have hIgt : 1 < Fintype.card I := by
          refine Fintype.one_lt_card_iff.mpr ?_
          refine ⟨1, z, ?_⟩
          intro hz
          exact hxn ((congrArg Subtype.val hz).symm)
        have hIdvdq : Fintype.card I ∣ q := by
          simpa [I, hq_card Q] using
            (Subgroup.card_dvd_of_le (show I ≤ (↑Q : Subgroup G) by
              exact inf_le_left))
        have hIdvdr : Fintype.card I ∣ r := by
          simpa [I, hr_card R] using
            (Subgroup.card_dvd_of_le (show I ≤ (↑R : Subgroup G) by
              exact inf_le_right))
        have hIcardq : Fintype.card I = q := by
          rcases (Nat.dvd_prime hq).1 hIdvdq with h1 | hq'
          · omega
          · exact hq'
        have hqdr : q ∣ r := by
          simpa [hIcardq] using hIdvdr
        rcases (Nat.dvd_prime hr).1 hqdr with h1 | h2
        · exact (hq.ne_one h1).elim
        · exact (hqr_ne h2).elim
      let A : Type _ := Σ Q : Sylow q G, {x : Q // x ≠ 1}
      let B : Type _ := Σ R : Sylow r G, {x : R // x ≠ 1}
      let f : A ⊕ B → {x : G // x ≠ 1}
        | Sum.inl ⟨Q, x⟩ => ⟨x, x.2⟩
        | Sum.inr ⟨R, x⟩ => ⟨x, x.2⟩
      have hf : Function.Injective f := by
        intro a b hab
        cases a with
        | inl a =>
            cases b with
            | inl b =>
                rcases a with ⟨Q, x⟩
                rcases b with ⟨Q', y⟩
                have hxy : (((x : Q) : G)) = (((y : Q') : G)) := by
                  simpa [f] using congrArg Subtype.val hab
                have hxQ : (((x : Q) : G)) ∈ (↑Q : Subgroup G) := (x : Q).2
                have hxQ' : (((x : Q) : G)) ∈ (↑Q' : Subgroup G) := by
                  simpa [hxy] using (y : Q').2
                have hQQ' : Q = Q' := same_q hxQ hxQ' x.2
                subst hQQ'
                have hxy' : x = y := by
                  apply Subtype.ext
                  simpa using hxy
                subst hxy'
                rfl
            | inr b =>
                rcases a with ⟨Q, x⟩
                rcases b with ⟨R, y⟩
                have hxy : (((x : Q) : G)) = (((y : R) : G)) := by
                  simpa [f] using congrArg Subtype.val hab
                have hxQ : (((x : Q) : G)) ∈ (↑Q : Subgroup G) := (x : Q).2
                have hxR : (((x : Q) : G)) ∈ (↑R : Subgroup G) := by
                  simpa [hxy] using (y : R).2
                exact (absurd_qr hxQ hxR x.2).elim
        | inr a =>
            cases b with
            | inl b =>
                rcases a with ⟨R, x⟩
                rcases b with ⟨Q, y⟩
                have hxy : (((x : R) : G)) = (((y : Q) : G)) := by
                  simpa [f] using congrArg Subtype.val hab
                have hxR : (((x : R) : G)) ∈ (↑R : Subgroup G) := (x : R).2
                have hxQ : (((x : R) : G)) ∈ (↑Q : Subgroup G) := by
                  simpa [hxy] using (y : Q).2
                exact (absurd_qr hxQ hxR x.2).elim
            | inr b =>
                rcases a with ⟨R, x⟩
                rcases b with ⟨R', y⟩
                have hxy : (((x : R) : G)) = (((y : R') : G)) := by
                  simpa [f] using congrArg Subtype.val hab
                have hxR : (((x : R) : G)) ∈ (↑R : Subgroup G) := (x : R).2
                have hxR' : (((x : R) : G)) ∈ (↑R' : Subgroup G) := by
                  simpa [hxy] using (y : R').2
                have hRR' : R = R' := same_r hxR hxR' x.2
                subst hRR'
                have hxy' : x = y := by
                  apply Subtype.ext
                  simpa using hxy
                subst hxy'
                rfl
      have hAcard : Fintype.card A = Fintype.card (Sylow q G) * (q - 1) := by
        simp [A, Fintype.card_sigma, hq_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hBcard : Fintype.card B = Fintype.card (Sylow r G) * (r - 1) := by
        simp [B, Fintype.card_sigma, hr_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hcod : Fintype.card {x : G // x ≠ 1} = Fintype.card G - 1 := by
        simpa using Fintype.card_subtype_neq (1 : G)
      have hle :
          Fintype.card (Sylow q G) * (q - 1) + Fintype.card (Sylow r G) * (r - 1) ≤
            Fintype.card G - 1 := by
        simpa [hAcard, hBcard, hcod, Fintype.card_sum, add_comm, add_left_comm, add_assoc] using
          (Fintype.card_le_of_injective f hf)
      have hqterm : r * (q - 1) ≤ Fintype.card (Sylow q G) * (q - 1) := by
        exact Nat.mul_le_mul_right (q - 1) hq_lower
      have hle' : p * q * (r - 1) + Fintype.card (Sylow q G) * (q - 1) ≤ Fintype.card G - 1 := by
        simpa [hcardr, add_comm, add_left_comm, add_assoc] using hle
      have hbig : p * q * (r - 1) + r * (q - 1) ≤ Fintype.card G - 1 := by
        exact le_trans (add_le_add_left hqterm (p * q * (r - 1))) hle'
      have hp_le_qm1 : p ≤ q - 1 := Nat.le_pred_of_lt hpq
      have hcomp : p * q ≤ r * (q - 1) := by
        have h1 : p * q ≤ q * (q - 1) := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hp_le_qm1
        have h2 : q * (q - 1) ≤ r * (q - 1) := by
          exact Nat.mul_le_mul_right (q - 1) (Nat.le_of_lt hqr)
        exact le_trans h1 h2
      have hr1 : r = (r - 1) + 1 := by
        exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne_zero)
      have hpqr_le :
          p * q * r ≤ p * q * (r - 1) + r * (q - 1) := by
        calc
          p * q * r = p * q * ((r - 1) + 1) := by rw [hr1]
          _ = p * q * (r - 1) + p * q := by
            rw [Nat.mul_add]
            simp [mul_assoc]
          _ ≤ p * q * (r - 1) + r * (q - 1) := by
            exact add_le_add_left hcomp (p * q * (r - 1))
      have hpqr_pos : 0 < p * q * r := by
        exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
      have hlt : p * q * r - 1 < p * q * (r - 1) + r * (q - 1) := by
        exact lt_of_lt_of_le (Nat.sub_lt hpqr_pos (by decide)) hpqr_le
      have : ¬ p * q * (r - 1) + r * (q - 1) ≤ p * q * r - 1 := by
        exact not_le_of_gt hlt
      exact (this (by simpa [hG] using hbig)).elim
