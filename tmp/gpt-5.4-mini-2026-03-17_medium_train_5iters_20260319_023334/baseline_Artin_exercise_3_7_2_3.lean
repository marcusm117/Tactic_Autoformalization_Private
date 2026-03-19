import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  intro hcover
  let U : Finset ι → Set V := fun s => ⋃ j ∈ s, (γ j : Set V)
  have hUtop : U Finset.univ = (⊤ : Set V) := by
    simpa [U] using hcover
  have hp : ∃ n : ℕ, ∃ s : Finset ι, U s = (⊤ : Set V) ∧ s.card = n := by
    refine ⟨Finset.univ.card, Finset.univ, ?_, rfl⟩
    simpa [U] using hUtop
  let n : ℕ := Nat.find hp
  have hn_spec : ∃ s : Finset ι, U s = (⊤ : Set V) ∧ s.card = n := Nat.find_spec hp
  rcases hn_spec with ⟨s, hs_top, hs_card⟩
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := by
      simpa using hne
    have h0 : (0 : V) ∈ U s := by
      simpa [hs_top] using (show (0 : V) ∈ (⊤ : Set V) by trivial)
    simpa [U, hs_empty] at h0
  rcases hs_nonempty with ⟨i, hi⟩
  have hv : ∃ v : V, v ∉ γ i := by
    by_contra h
    have htopi : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        by_contra hx'
        exact h ⟨x, hx'⟩
    exact h i htopi
  rcases hv with ⟨v, hv⟩
  have hnotsubset : ¬ γ i ≤ U (s.erase i) := by
    intro hsub
    have hsame : U s = U (s.erase i) := by
      ext x
      constructor
      · intro hx
        simp [U] at hx ⊢
        rcases hx with ⟨j, hj, hxj⟩
        by_cases hji : j = i
        · subst hji
          exact hsub hxj
        · exact ⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩, hxj⟩
      · intro hx
        simp [U] at hx ⊢
        rcases hx with ⟨j, hj, hxj⟩
        exact ⟨j, Finset.erase_subset hj, hxj⟩
    have htop' : U (s.erase i) = (⊤ : Set V) := by
      simpa [hsame] using hs_top
    have hmin : n ≤ (s.erase i).card := Nat.find_min' hp ⟨s.erase i, htop', rfl⟩
    have hlt : (s.erase i).card < n := by
      simpa [hs_card] using Finset.card_erase_lt_of_mem hi
    exact (lt_irrefl _ (lt_of_lt_of_le hlt hmin))
  have hu_exists : ∃ u : V, u ∈ γ i ∧ u ∉ U (s.erase i) := by
    by_contra h
    apply hnotsubset
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  rcases hu_exists with ⟨u, hu_mem, hu_not⟩
  have herase_nonempty : (s.erase i).Nonempty := by
    by_contra hempty
    have hs_eq : s = {i} := by
      ext j
      constructor
      · intro hj
        by_cases hji : j = i
        · simpa [hji] using hj
        · exact False.elim (hempty ⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩⟩)
      · intro hj
        have hji : j = i := by simpa using hj
        simpa [hji] using hi
    have hs' : U ({i} : Finset ι) = (⊤ : Set V) := by
      simpa [U, hs_eq] using hs_top
    have htopi : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        have hxU : x ∈ U ({i} : Finset ι) := by
          simpa [hs'] using hx
        simpa [U] using hxU
    exact h i htopi
  have hu_ne : u ≠ 0 := by
    intro hu0
    have h0 : u ∈ U (s.erase i) := by
      rcases herase_nonempty with ⟨j, hj⟩
      exact ⟨j, hj, by simpa [hu0] using (γ j).zero_mem⟩
    exact hu_not h0
  have hx_exists : ∀ t : K, ∃ j : {j : ι // j ∈ s.erase i}, (v + t • u : V) ∈ γ j.1 := by
    intro t
    have hnoti : (v + t • u : V) ∉ γ i := by
      intro hxmem
      have hu_t : t • u ∈ γ i := (γ i).smul_mem t hu_mem
      have hv_mem : v ∈ γ i := by
        have htmp := (γ i).sub_mem hxmem hu_t
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
      exact hv hv_mem
    have hxU : (v + t • u : V) ∈ U s := by
      simpa [hs_top] using (show (v + t • u : V) ∈ (⊤ : Set V) by trivial)
    simp [U] at hxU
    rcases hxU with ⟨j, hj, hxj⟩
    by_cases hji : j = i
    · subst hji
      exact False.elim (hnoti hxj)
    · exact ⟨⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩⟩, hxj⟩
  let f : K → {j : ι // j ∈ s.erase i} := fun t => Classical.choose (hx_exists t)
  have hf : Function.Injective f := by
    intro a b hab
    have hval : (v + a • u : V) = v + b • u := by
      simpa [f] using congrArg Subtype.val hab
    have hs : a • u = b • u := by
      exact add_left_cancel hval
    have hdiff : (a - b) • u = 0 := by
      rw [sub_smul, hs, sub_self]
    rcases smul_eq_zero.mp hdiff with hscalar | hu0
    · exact sub_eq_zero.mp hscalar
    · exact (hu_ne hu0).elim
  have hfin : Finite K := Finite.of_injective f hf
  exact (Infinite.not_finite (α := K)) hfin
