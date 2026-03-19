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


theorem exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : G = Subgroup.closure {x}) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  classical
  let N : ℕ := n
  have hxN : orderOf x = N := by
    simpa [N] using hx
  have hxgen : ∀ g : G, g ∈ Subgroup.closure ({x} : Set G) := by
    intro g
    let e : G ≃ Subgroup.closure ({x} : Set G) := Equiv.cast hG
    have hmem : (((e g : Subgroup.closure ({x} : Set G)) : G) ∈ Subgroup.closure ({x} : Set G)) :=
      (e g).2
    simpa using hmem
  have htop : Subgroup.closure ({x} : Set G) = ⊤ := by
    ext g
    constructor
    · intro _
      trivial
    · intro _
      exact hxgen g
  have hcyc : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨x, ?_⟩
    simpa [Subgroup.zpowers_eq_closure] using htop
  letI : IsCyclic G := hcyc
  letI : CommGroup G := hcyc.commGroup
  have hclass :
      ∀ K : Subgroup G,
        K = Subgroup.closure ({x ^ orderOf ((QuotientGroup.mk' K) x)} : Set G) := by
    intro K
    letI : K.Normal := by infer_instance
    let y : G ⧸ K := QuotientGroup.mk' K x
    let r : ℕ := orderOf y
    have hyr : y ^ r = 1 := by
      simpa [r] using pow_orderOf_eq_one y
    have hqxr : QuotientGroup.mk' K (x ^ r) = 1 := by
      simpa [y, r] using hyr
    have hxr : x ^ r ∈ K := by
      simpa using hqxr
    apply le_antisymm
    · intro g hg
      have hgz : g ∈ Subgroup.zpowers x := by
        simpa [Subgroup.zpowers_eq_closure] using hxgen g
      rcases Subgroup.mem_zpowers_iff.mp hgz with ⟨z, rfl⟩
      have hqz : QuotientGroup.mk' K (x ^ z) = 1 := by
        simpa using hg
      have hyz : y ^ z = 1 := by
        simpa [y] using hqz
      have hzdiv : (r : ℤ) ∣ z := by
        exact (orderOf_dvd_iff_zpow_eq_one).2 (by simpa [r] using hyz)
      rcases hzdiv with ⟨t, rfl⟩
      have hxrin : x ^ r ∈ Subgroup.closure ({x ^ r} : Set G) := Subgroup.subset_closure (by simp)
      have hzmem : (x ^ r) ^ t ∈ Subgroup.closure ({x ^ r} : Set G) :=
        Subgroup.zpow_mem _ hxrin t
      simpa [zpow_mul, r] using hzmem
    · rw [Subgroup.closure_le]
      intro g hg
      simp at hg
      rcases hg with rfl
      exact hxr
  have hpow_ne_top :
      ∀ {p : ℕ}, Prime p → p ∣ N → Subgroup.closure ({x ^ p} : Set G) ≠ ⊤ := by
    intro p hp hpdvd hEq
    have hpnat : Nat.Prime p := by
      simpa [Nat.prime_iff] using hp
    have hxmem : x ∈ Subgroup.closure ({x ^ p} : Set G) := by
      rw [hEq]
      trivial
    have hxzp : x ∈ Subgroup.zpowers (x ^ p) := by
      simpa [Subgroup.zpowers_eq_closure] using hxmem
    rcases Subgroup.mem_zpowers_iff.mp hxzp with ⟨z, hz⟩
    have hpoweq : x ^ ((p : ℤ) * z) = x := by
      simpa [zpow_mul] using hz
    have hpow1 : x ^ (((p : ℤ) * z) - 1) = 1 := by
      rw [zpow_sub, hpoweq, zpow_one]
      simp
    have hndiv : ((N : ℤ) ∣ ((p : ℤ) * z - 1)) := by
      simpa [hxN] using (orderOf_dvd_iff_zpow_eq_one.2 hpow1)
    rcases hpdvd with ⟨m, hm⟩
    have hpdivN : ((p : ℤ) ∣ (N : ℤ)) := by
      refine ⟨m, ?_⟩
      exact_mod_cast hm
    have hpdivA : ((p : ℤ) ∣ ((p : ℤ) * z - 1)) := dvd_trans hpdivN hndiv
    have hpdivB : ((p : ℤ) ∣ (p : ℤ) * z) := by
      exact ⟨z, by ring⟩
    have hpdiv1' : ((p : ℤ) ∣ ((p : ℤ) * z - ((p : ℤ) * z - 1))) := dvd_sub hpdivB hpdivA
    have hpdiv1 : ((p : ℤ) ∣ (1 : ℤ)) := by
      convert hpdiv1' using 1 <;> ring
    have hpdiv1_nat : p ∣ 1 := by
      exact_mod_cast hpdiv1
    exact hpnat.not_dvd_one hpdiv1_nat
  constructor
  · rintro ⟨p, hp, hpdvdn, rfl⟩
    have hpdvdN : p ∣ N := by
      simpa [N] using hpdvdn
    have hpnat : Nat.Prime p := by
      simpa [Nat.prime_iff] using hp
    refine ⟨hpow_ne_top hp hpdvdN, ?_⟩
    intro K hHK
    letI : K.Normal := by infer_instance
    let y : G ⧸ K := QuotientGroup.mk' K x
    let r : ℕ := orderOf y
    have hxpk : x ^ p ∈ K := hHK (Subgroup.subset_closure (by simp))
    have hq : QuotientGroup.mk' K (x ^ p) = 1 := by
      simpa using hxpk
    have hyppow : y ^ p = 1 := by
      simpa [y] using hq
    have hrdvp : r ∣ p := by
      exact orderOf_dvd_iff_pow_eq_one.2 (by simpa [r] using hyppow)
    have hr_cases : r = 1 ∨ r = p := (Nat.dvd_prime hpnat).1 hrdvp
    cases hr_cases with
    | inl hr1 =>
        right
        calc
          K = Subgroup.closure ({x ^ orderOf ((QuotientGroup.mk' K) x)} : Set G) := hclass K
          _ = Subgroup.closure ({x} : Set G) := by simp [r, y, hr1]
          _ = ⊤ := htop
    | inr hrp =>
        left
        calc
          K = Subgroup.closure ({x ^ orderOf ((QuotientGroup.mk' K) x)} : Set G) := hclass K
          _ = Subgroup.closure ({x ^ p} : Set G) := by simp [r, y, hrp]
  · rintro ⟨hHne, hmax⟩
    letI : H.Normal := by infer_instance
    let y : G ⧸ H := QuotientGroup.mk' H x
    let r : ℕ := orderOf y
    have hHr : H = Subgroup.closure ({x ^ r} : Set G) := by
      simpa [y, r] using hclass H
    have hryn : y ^ N = 1 := by
      have hxpow : x ^ N = 1 := by
        simpa [hxN] using pow_orderOf_eq_one x
      have hq : QuotientGroup.mk' H (x ^ N) = 1 := by
        rw [hxpow]
        simp
      simpa [y] using hq
    have hrdvN : r ∣ N := by
      exact orderOf_dvd_iff_pow_eq_one.2 (by simpa [r] using hryn)
    have hr_ne_one : r ≠ 1 := by
      intro hr1
      apply hHne
      calc
        H = Subgroup.closure ({x ^ r} : Set G) := hHr
        _ = Subgroup.closure ({x} : Set G) := by simp [hr1]
        _ = ⊤ := htop
    have hr_prime_nat : Nat.Prime r := by
      by_contra hnr
      have hrpos : 0 < r := orderOf_pos y
      have hr_ge_two : 2 ≤ r := by
        omega
      rcases Nat.exists_prime_and_dvd hr_ge_two with ⟨p, hp, hpdvr⟩
      have hpr_ne : p ≠ r := by
        intro hpr
        exact hnr (hpr ▸ hp)
      have hp_le_r : p ≤ r := Nat.le_of_dvd hrpos hpdvr
      have hp_lt_r : p < r := lt_of_le_of_ne hp_le_r hpr_ne
      rcases hpdvr with ⟨m, hm⟩
      let K : Subgroup G := Subgroup.closure ({x ^ p} : Set G)
      have hHK : H ≤ K := by
        rw [hHr, Subgroup.closure_le]
        intro g hg
        simp at hg
        rcases hg with rfl
        have hxp : x ^ p ∈ K := Subgroup.subset_closure (by simp)
        have hxpm : (x ^ p) ^ m ∈ K := Subgroup.pow_mem K hxp m
        have : x ^ (p * m) ∈ K := by
          simpa [pow_mul] using hxpm
        simpa [hm] using this
      have hxp_notin : x ^ p ∉ H := by
        intro hxpH
        have hq : QuotientGroup.mk' H (x ^ p) = 1 := by
          simpa using hxpH
        have hyp : y ^ p = 1 := by
          simpa [y] using hq
        have hrdvp : r ∣ p := by
          exact orderOf_dvd_iff_pow_eq_one.2 (by simpa [r] using hyp)
        have hr_le_p : r ≤ p := Nat.le_of_dvd hp.pos hrdvp
        omega
      have hK_ne_H : K ≠ H := by
        intro hKH
        have hxpK : x ^ p ∈ K := Subgroup.subset_closure (by simp)
        have hxpH : x ^ p ∈ H := by simpa [hKH] using hxpK
        exact hxp_notin hxpH
      have hpdvN : p ∣ N := dvd_trans ⟨m, hm⟩ hrdvN
      have hp' : Prime p := by
        simpa [Nat.prime_iff] using hp
      have hK_ne_top : K ≠ ⊤ := hpow_ne_top hp' hpdvN
      have hcase := hmax K hHK
      cases hcase with
      | inl hKH => exact hK_ne_H hKH
      | inr hKt => exact hK_ne_top hKt
    have hr_prime : Prime r := by
      simpa [Nat.prime_iff] using hr_prime_nat
    refine ⟨r, hr_prime, ?_, hHr⟩
    simpa [N] using hrdvN
