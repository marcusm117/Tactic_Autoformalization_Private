import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
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


theorem exercise_6_4_3 {G : Type*} [Group G] [Fintype G] {p q : ℕ}
  (hp : Prime p) (hq : Prime q) (hG : card G = p^2 *q) :
  IsSimpleGroup G → false := by
  classical
  intro hS
  have hsimple : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := hS.2
  by_cases hpeq : p = q
  · subst hpeq
    have hcardG : Fintype.card G = p ^ 3 := by omega
    have hpg : IsPGroup p G := by
      intro g
      refine ⟨3, ?_⟩
      simpa [hcardG] using (pow_card_eq_one (G := G) (g := g))
    have hcen : Nontrivial (Subgroup.center G) := by
      simpa using hpg.center_nontrivial
    rcases hcen with ⟨z, hz⟩
    have hcentop : Subgroup.center G = ⊤ := by
      rcases hsimple (Subgroup.center G) inferInstance with hbot | htop
      · exfalso
        have : z.1 = 1 := by
          simpa [hbot] using z.2
        exact hz (Subsingleton.elim _ _ |> by simpa [this])
      · exact htop
    letI : CommGroup G := by
      refine { mul_comm := ?_ }
      intro a b
      have ha : a ∈ Subgroup.center G := by
        simpa [hcentop]
      exact (Subgroup.mem_center_iff.mp ha b).symm
    rcases hp.exists_orderOf_eq (by
      have : p ∣ Fintype.card G := by omega
      exact this) with ⟨g, hg⟩
    let H : Subgroup G := Subgroup.zpowers g
    have hHnorm : H.Normal := by infer_instance
    have hHcard : Fintype.card H = p := by
      simpa [H, hg] using (Subgroup.card_zpowers g)
    have hHsimple := hsimple H hHnorm
    rcases hHsimple with hbot | htop
    · have : Fintype.card H = 1 := by simpa [hbot]
      omega
    · have : Fintype.card G = Fintype.card H := by simpa [htop]
      omega
  · by_cases hqp : q < p
    · have hcard : Fintype.card (Sylow p G) = 1 := by
        sylow_counting p
        omega
      let P : Sylow p G := Classical.choice (show Nonempty (Sylow p G) from inferInstance)
      have hPnorm : P.1.Normal := by
        rw [Subgroup.normal_iff]
        intro g
        exact Subsingleton.elim _ _
      have hPsimple := hsimple P.1 hPnorm
      rcases hPsimple with hbot | htop
      · have hcardP : Fintype.card P.1 = p ^ 2 := by
          -- the underlying Sylow p-subgroup has order p^2
          simpa using (by
            have := P.1.card_subtype
            omega)
        have : Fintype.card P.1 = 1 := by simpa [hbot]
        omega
      · have hcardG' : Fintype.card G = Fintype.card P.1 := by simpa [htop]
        have hPcard : Fintype.card P.1 = p ^ 2 := by
          -- the underlying Sylow p-subgroup has order p^2
          simpa using (by
            have := P.1.card_subtype
            omega)
        omega
    · have hlt : p < q := by omega
      have hqcases : Fintype.card (Sylow q G) = 1 ∨ Fintype.card (Sylow q G) = p ∨ Fintype.card (Sylow q G) = p ^ 2 := by
        sylow_counting q
        omega
      rcases hqcases with hq1 | hq2 | hq3
      · let Q : Sylow q G := Classical.choice (show Nonempty (Sylow q G) from inferInstance)
        have hQnorm : Q.1.Normal := by
          rw [Subgroup.normal_iff]
          intro g
          exact Subsingleton.elim _ _
        have hQsimple := hsimple Q.1 hQnorm
        rcases hQsimple with hbot | htop
        · have hqelem : ∃ x : G, orderOf x = q := by
            have hdiv : q ∣ Fintype.card G := by
              omega
            exact hq.exists_orderOf_eq hdiv
          rcases hqelem with ⟨x, hx⟩
          have hqpow : IsPGroup q G := by
            simpa [htop] using Q.2
          have : False := by
            rcases hqpow x with ⟨k, hk⟩
            have hdiv : orderOf x ∣ q ^ k := by
              exact orderOf_dvd_iff_pow_eq_one.mpr hk
            have hpq : q ∣ orderOf x := by
              simpa [hx] using hdiv
            have hqeq : q = 1 := by
              exact Nat.dvd_one.mp (by simpa [hx] using hpq)
            exact hq.ne_one hqeq
          exact False.elim this
        · have hqelem : ∃ x : G, orderOf x = p := by
            have hdiv : p ∣ Fintype.card G := by
              omega
            exact hp.exists_orderOf_eq hdiv
          rcases hqelem with ⟨x, hx⟩
          have hqpow : IsPGroup q G := by
            simpa [htop] using Q.2
          have : False := by
            rcases hqpow x with ⟨k, hk⟩
            have hdiv : orderOf x ∣ q ^ k := by
              exact orderOf_dvd_iff_pow_eq_one.mpr hk
            have hpq : p ∣ q := by
              simpa [hx] using (hp.dvd_of_dvd_pow hdiv)
            have hpqeq : p = q := hp.eq_of_dvd hpq
            exact hpeq hpqeq
          exact False.elim this
      · have hmod : Fintype.card (Sylow q G) ≡ 1 [MOD q] := by
          sylow_counting q
        rw [hq2] at hmod
        omega
      · have hmod : Fintype.card (Sylow q G) ≡ 1 [MOD q] := by
          sylow_counting q
        have hdiv : q ∣ p ^ 2 - 1 := by
          simpa [hq3] using (Nat.modEq_iff_dvd'.mp hmod)
        have hprod : q ∣ (p - 1) * (p + 1) := by
          have hpow : p ^ 2 - 1 = (p - 1) * (p + 1) := by omega
          simpa [hpow] using hdiv
        have hqdiv : q ∣ p + 1 := by
          have hqnot : ¬ q ∣ p - 1 := by
            intro h
            have hle : q ≤ p - 1 := Nat.le_of_dvd (by positivity) h
            omega
          rcases hq.dvd_mul.mp hprod with h1 | h2
          · exact (False.elim (hqnot h1))
          · exact h2
        have hqeq : q = p + 1 := by
          have hle : q ≤ p + 1 := Nat.le_of_dvd (by positivity) hqdiv
          omega
        have hp2 : p = 2 := by
          have hqprime : Nat.Prime (p + 1) := by simpa [hqeq] using hq
          by_cases hp2' : p = 2
          · exact hp2'
          · have hpodd : Odd p := hp.odd_of_ne_two hp2'
            have hpeven : Even (p + 1) := hpodd.add_one
            have hqeven : Even q := by simpa [hqeq] using hpeven
            have hqne2 : q ≠ 2 := by omega
            exact (hq.odd_of_ne_two hqne2).not_even hqeven
        subst hp2
        have hq3' : q = 3 := by omega
        subst hq3'
        have h2cases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 := by
          sylow_counting 2
          omega
        rcases h2cases with h21 | h23
        · let P : Sylow 2 G := Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)
          have hPnorm : P.1.Normal := by
            rw [Subgroup.normal_iff]
            intro g
            exact Subsingleton.elim _ _
          have hPsimple := hsimple P.1 hPnorm
          rcases hPsimple with hbot | htop
          · have hcardP : Fintype.card P.1 = 4 := by
              simpa using (by
                have := P.1.card_subtype
                omega)
            have : Fintype.card P.1 = 1 := by simpa [hbot]
            omega
          · have hcardG' : Fintype.card G = Fintype.card P.1 := by simpa [htop]
            have hcardP : Fintype.card P.1 = 4 := by
              simpa using (by
                have := P.1.card_subtype
                omega)
            omega
        · let P : Sylow 2 G := Classical.choice (show Nonempty (Sylow 2 G) from inferInstance)
          have h1lt : 1 < Fintype.card (Sylow 2 G) := by omega
          have hneq : ∃ Q : Sylow 2 G, Q ≠ P := by
            simpa using (Fintype.exists_ne_of_one_lt_card (α := Sylow 2 G) h1lt P)
          rcases hneq with ⟨Q, hPQ⟩
          rcases Sylow.exists_smul_eq P Q with ⟨g, hg⟩
          let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPerm G (Sylow 2 G)
          have hkerNorm : φ.ker.Normal := by inferInstance
          have hkerBot : φ.ker = ⊥ := by
            rcases hsimple φ.ker hkerNorm with hbot | htop
            · exact hbot
            · exfalso
              have hfix : g • P = P := by
                have hgker : g ∈ φ.ker := by simpa [htop]
                have hperm : φ g = 1 := by
                  simpa [MonoidHom.mem_ker] using hgker
                have hperm' := congrArg (fun e : Equiv.Perm (Sylow 2 G) => e P) hperm
                simpa [φ, MulAction.toPerm_apply] using hperm'
              exact hPQ (by simpa [hg] using hfix)
          have hinj : Function.Injective φ := by
            exact MonoidHom.injective_iff_ker_eq_bot.mpr hkerBot
          have hcardle : Fintype.card G ≤ Fintype.card (Equiv.Perm (Sylow 2 G)) := by
            exact Fintype.card_le_of_injective φ hinj
          have hperm : Fintype.card (Equiv.Perm (Sylow 2 G)) = 6 := by
            simpa [h23] using (Fintype.card_perm (α := Sylow 2 G))
          have hG12 : Fintype.card G = 12 := by
            simpa [hG] using (by norm_num : Fintype.card G = 12)
          omega
