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


theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  by_contra hcov
  let P : Nat → Prop := fun n =>
    ∃ s : Finset ι, (Set.univ ⊆ ⋃ i ∈ s, (γ i : Set V)) ∧ s.card = n
  have hP : ∃ n, P n := by
    refine ⟨Finset.univ.card, ?_⟩
    refine ⟨Finset.univ, ?_, rfl⟩
    simpa [hcov]
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  rcases hm with ⟨s, hscover, rfl⟩
  have hmin : ∀ n, P n → m ≤ n := Nat.find_min' hP
  have hsne : s.Nonempty := by
    by_contra hsne
    have hs0 : s = ∅ := by
      ext j
      constructor
      · intro hj
        exact False.elim (hsne ⟨j, hj⟩)
      · intro hj
        cases hj
    have h0 : (0 : V) ∈ (⋃ i ∈ s, (γ i : Set V)) := hscover (by simp)
    simpa [hs0] using h0
  rcases hsne with ⟨i, hi⟩
  have hex : ∃ i ∈ s, ¬ γ i ≤ ⋃ j ∈ s.erase i, (γ j : Set V) := by
    by_contra hhex
    have hred : ∀ i ∈ s, γ i ≤ ⋃ j ∈ s.erase i, (γ j : Set V) := by
      intro j hj
      by_contra hj'
      exact hhex ⟨j, hj, hj'⟩
    have hcoverErase : Set.univ ⊆ ⋃ j ∈ s.erase i, (γ j : Set V) := by
      intro x hx
      rcases hscover hx with ⟨j, hj, hjx⟩
      by_cases hji : j = i
      · subst hji
        exact hred i hi hjx
      · exact ⟨j, by simpa [Finset.mem_erase, hji] using hj, hjx⟩
    have hPerase : P (s.erase i).card := by
      refine ⟨s.erase i, hcoverErase, rfl⟩
    have hle : m ≤ (s.erase i).card := hmin _ hPerase
    have hlt : (s.erase i).card < m := by
      have hlt' : (s.erase i).card < s.card := Finset.card_erase_lt.mpr hi
      omega
    omega
  rcases hex with ⟨i, hi, hnotsub⟩
  have herase_nonempty : (s.erase i).Nonempty := by
    by_contra hne
    have hs0 : s.erase i = ∅ := by
      ext j
      constructor
      · intro hj
        exact False.elim (hne ⟨j, hj⟩)
      · intro hj
        cases hj
    have htop : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        have hxunion : x ∈ ⋃ j ∈ s, (γ j : Set V) := hscover (by simp)
        rcases hxunion with ⟨j, hj, hjx⟩
        have hji : j = i := by
          by_contra hji
          have hjerase : j ∈ s.erase i := by
            simpa [Finset.mem_erase, hji] using hj
          simpa [hs0] using hjerase
        subst hji
        simpa [hs0] using hjx
    exact h i htop
  rcases not_subset.mp hnotsub with ⟨u, hu, hu_other⟩
  have hu0 : u ≠ 0 := by
    intro h0
    have h0mem : (0 : V) ∈ ⋃ j ∈ s.erase i, (γ j : Set V) := by
      rcases herase_nonempty with ⟨j, hj⟩
      exact ⟨j, hj, by simp [h0]⟩
    exact hu_other h0mem
  have hv : ∃ v : V, v ∉ (γ i : Set V) := by
    by_contra hv
    have hmem : ∀ x : V, x ∈ (γ i : Set V) := by
      intro x
      by_contra hx
      exact hv ⟨x, hx⟩
    have htop : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        exact hmem x
    exact h i htop
  rcases hv with ⟨v, hv⟩
  let f : K → V := fun a => v + a • u
  let L : Set V := Set.range f
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : a • u = b • u := by
      have := congrArg (fun z => z - v) hab
      simpa [f, add_comm, add_left_comm, add_assoc] using this
    have hsub : (a - b) • u = 0 := by
      calc
        (a - b) • u = a • u - b • u := by simpa [sub_eq_add_neg, smul_sub]
        _ = 0 := by simpa [hab']
    have hzero : a - b = 0 := by
      by_contra hneq
      have hcase := smul_eq_zero.mp hsub
      cases hcase with
      | inl ha => exact hneq ha
      | inr hu' => exact hu0 hu'
    exact sub_eq_zero.mp hzero
  have hLnot : ∀ a : K, f a ∉ (γ i : Set V) := by
    intro a hfa
    have hvmem : v ∈ (γ i : Set V) := by
      have hsub : f a - a • u ∈ (γ i : Set V) := (γ i).sub_mem hfa ((γ i).smul_mem a hu)
      simpa [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, smul_sub] using hsub
    exact hv hvmem
  have hEq : L = ⋃ j ∈ s.erase i, (L ∩ (γ j : Set V)) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, rfl⟩
      have hxunion : f a ∈ ⋃ j ∈ s, (γ j : Set V) := hscover (by simp [L, f])
      rcases hxunion with ⟨j, hj, hjx⟩
      by_cases hji : j = i
      · subst hji
        exact False.elim (hLnot a hjx)
      · exact ⟨j, by simpa [Finset.mem_erase, hji] using hj, ⟨⟨a, rfl⟩, hjx⟩⟩
    · intro hx
      rcases hx with ⟨j, hj, hxj⟩
      exact hxj.1
  have hfinInter : ∀ j ∈ (s.erase i : Set ι), Set.Finite (L ∩ (γ j : Set V)) := by
    intro j hj
    have hss : Set.Subsingleton (L ∩ (γ j : Set V)) := by
      intro x hx y hy
      rcases hx.1 with ⟨a, rfl⟩
      rcases hy.1 with ⟨b, rfl⟩
      have ha : f a ∈ (γ j : Set V) := hx.2
      have hb : f b ∈ (γ j : Set V) := hy.2
      by_cases hab : a = b
      · subst hab
        simp
      · have hdiff : (a - b) • u ∈ (γ j : Set V) := by
          have hsub := (γ j).sub_mem ha hb
          simpa [f, sub_eq_add_neg, smul_sub, smul_add, add_comm, add_left_comm, add_assoc] using hsub
        have hneq : a - b ≠ 0 := sub_ne_zero.mpr hab
        have hu_mem : u ∈ (γ j : Set V) := by
          have hscaled := (γ j).smul_mem (a - b)⁻¹ hdiff
          simpa [smul_smul, hneq] using hscaled
        have hnot : u ∉ (γ j : Set V) := by
          intro huj
          exact hu_other ⟨j, hj, huj⟩
        exact (hnot hu_mem).elim
    by_cases hnonempty : (L ∩ (γ j : Set V)).Nonempty
    · rcases hnonempty with ⟨x, hx⟩
      refine Set.Finite.subset (Set.finite_singleton x) ?_
      intro y hy
      exact hss hy hx
    · simpa using Set.finite_empty
  have hfinIdx : Set.Finite ((s.erase i : Finset ι) : Set ι) := by
    simpa using (s.erase i).finite_toSet
  have hfinUnion : Set.Finite (⋃ j ∈ (s.erase i : Set ι), (L ∩ (γ j : Set V))) := by
    exact hfinIdx.biUnion hfinInter
  have hLfin : Set.Finite L := by
    simpa [hEq] using hfinUnion
  have hLtype : Finite L := hLfin.toFinite
  haveI : Finite L := hLtype
  let g : K → L := fun a => ⟨f a, by exact ⟨a, rfl⟩⟩
  have hg : Function.Injective g := by
    intro a b hab
    exact hf (congrArg Subtype.val hab)
  have hKfin : Finite K := Finite.of_injective g hg
  have hKnf : ¬ Finite K := by
    infer_instance
  exact hKnf hKfin
