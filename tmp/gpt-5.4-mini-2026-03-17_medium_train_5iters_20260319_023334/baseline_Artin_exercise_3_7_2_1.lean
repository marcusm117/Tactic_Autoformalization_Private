import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  intro htop
  let U : Finset ι → Set V := fun s => ⋃ j ∈ s, (γ j : Set V)
  let p : ℕ → Prop := fun n => ∃ s : Finset ι, U s = (⊤ : Set V) ∧ s.card = n
  have hp : ∃ n, p n := by
    refine ⟨Finset.univ.card, ?_⟩
    refine ⟨Finset.univ, ?_, rfl⟩
    simpa [U] using htop
  let n : ℕ := Nat.find hp
  have hn_spec : p n := Nat.find_spec hp
  rcases hn_spec with ⟨s, hs_top, hs_card⟩
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := by simpa using hne
    simpa [U, hs_empty] using hs_top
  rcases hs_nonempty with ⟨i, hi⟩
  have hv : ∃ v : V, v ∉ γ i := by
    by_contra hv
    have hmem : ∀ v : V, v ∈ γ i := by
      intro v
      by_contra hv'
      exact hv ⟨v, hv'⟩
    have htopi : γ i = ⊤ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        exact hmem x
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
        exact ⟨j, Finset.mem_of_mem_erase hj, hxj⟩
    have htop' : U (s.erase i) = (⊤ : Set V) := by
      simpa [hsame] using hs_top
    have hmin : n ≤ (s.erase i).card := Nat.find_min' hp ⟨s.erase i, htop', rfl⟩
    have hlt : (s.erase i).card < n := by
      simpa [hs_card] using Finset.card_erase_lt_of_mem hi
    exact (lt_irrefl _ (lt_of_lt_of_le hlt hmin))
  rcases not_subset.mp hnotsubset with ⟨u, hu_mem, hu_not⟩
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
        · exfalso
          have : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hj, hji⟩
          simpa [hempty] using this
      · intro hj
        simp at hj
        simpa [hj] using hi
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
        simpa using (γ i).sub_mem hxmem hu_t
      exact hv hv_mem
    have hxU : (v + t • u : V) ∈ U s := by
      rw [hs_top]
      trivial
    simp [U] at hxU
    rcases hxU with ⟨j, hj, hxj⟩
    by_cases hji : j = i
    · subst hji
      exact False.elim (hnoti hxj)
    · exact ⟨⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩⟩, hxj⟩
  let f : K → {j : ι // j ∈ s.erase i} := fun t => Classical.choose (hx_exists t)
  have hf : Function.Injective f := by
    intro a b hab
    have hJ : (f a).1 = (f b).1 := by
      simpa using congrArg Subtype.val hab
    have ha : (v + a • u : V) ∈ γ (f a).1 := by
      simpa using (Classical.choose_spec (hx_exists a))
    have hb : (v + b • u : V) ∈ γ (f a).1 := by
      simpa [hJ] using (Classical.choose_spec (hx_exists b))
    by_contra hne
    have hsub : (a - b) • u ∈ γ (f a).1 := by
      simpa [sub_smul] using (γ (f a).1).sub_mem ha hb
    have hnonzero : a - b ≠ 0 := sub_ne_zero.mpr hne
    have huj : u ∈ γ (f a).1 := by
      have htmp := (γ (f a).1).smul_mem (a - b)⁻¹ hsub
      simpa [hnonzero] using htmp
    exact hu_not ⟨(f a).1, (f a).2, huj⟩
  have hfin : Finite K := Finite.of_injective f hf
  exact hfin.not_infinite inferInstance
