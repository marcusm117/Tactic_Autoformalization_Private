import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  intro hcover
  let U : Finset ι → Set V := fun s => {x : V | ∃ j ∈ s, x ∈ γ j}
  have hUtop : U Finset.univ = (⊤ : Set V) := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      have hx' : x ∈ (⋃ i, (γ i : Set V)) := by simpa [hcover] using hx
      simpa [U] using hx'
  let p : ℕ → Prop := fun n => ∃ s : Finset ι, U s = (⊤ : Set V) ∧ s.card = n
  have hp : ∃ n, p n := by
    refine ⟨Finset.univ.card, ?_⟩
    exact ⟨Finset.univ, hUtop, rfl⟩
  let n : ℕ := Nat.find hp
  have hn_spec : p n := Nat.find_spec hp
  rcases hn_spec with ⟨s, hs_top, hs_card⟩
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := by
      by_contra hsne
      exact hne (Finset.nonempty_iff_ne_empty.mpr hsne)
    have h0 : (0 : V) ∈ U s := by
      simpa [hs_top]
    simp [U, hs_empty] at h0
  rcases hs_nonempty with ⟨i, hi⟩
  have hv : ∃ v : V, v ∉ γ i := by
    by_contra hv
    have htopi : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        by_contra hx'
        exact hv ⟨x, hx'⟩
    exact h i htopi
  rcases hv with ⟨v, hv⟩
  have hnotsubset : ¬ γ i ≤ U (s.erase i) := by
    intro hsub
    have hsame : U s = U (s.erase i) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨j, hj, hxj⟩
        by_cases hji : j = i
        · subst hji
          exact hsub hxj
        · exact ⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩, hxj⟩
      · intro hx
        rcases hx with ⟨j, hj, hxj⟩
        exact ⟨j, Finset.mem_of_mem_erase hj, hxj⟩
    have htop' : U (s.erase i) = (⊤ : Set V) := by
      simpa [hsame] using hs_top
    have hmin : n ≤ (s.erase i).card := Nat.find_min' hp ⟨s.erase i, htop', rfl⟩
    have hlt : (s.erase i).card < n := by
      simpa [hs_card] using Finset.card_erase_lt_of_mem hi
    exact (lt_irrefl _ (lt_of_lt_of_le hlt hmin))
  have hnot : ¬ ∀ x : V, x ∈ γ i → x ∈ U (s.erase i) := by
    intro h
    exact hnotsubset h
  rcases not_forall.mp hnot with ⟨u, hu⟩
  have hu' : u ∈ γ i ∧ u ∉ U (s.erase i) := by
    simpa [not_imp] using hu
  rcases hu' with ⟨hu_mem, hu_not⟩
  have hu_ne : u ≠ 0 := by
    intro hu0
    have h0 : u ∈ U (s.erase i) := by
      rcases hs_nonempty with ⟨j, hj⟩
      exact ⟨j, hj, by simpa [hu0] using (γ j).zero_mem⟩
    exact hu_not h0
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
    have htopi : γ i = ⊤ := by
      have hs' : U ({i} : Finset ι) = (⊤ : Set V) := by
        simpa [U, hs_eq] using hs_top
      simpa [U] using hs'
    exact h i htopi
  have hx_exists : ∀ t : K, ∃ j : {j : ι // j ∈ s.erase i}, (v + t • u : V) ∈ γ j.1 := by
    intro t
    have hnoti : (v + t • u : V) ∉ γ i := by
      intro hxmem
      have hu_t : t • u ∈ γ i := (γ i).smul_mem t hu_mem
      have hv_mem : v ∈ γ i := by
        exact (γ i).sub_mem hxmem hu_t
      exact hv hv_mem
    have hxU : (v + t • u : V) ∈ U s := by
      have : (v + t • u : V) ∈ (⊤ : Set V) := by trivial
      simpa [hs_top] using this
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
  exact hfin.not_infinite inferInstance
