import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  by_contra htop
  let U : Finset ι → Set V := fun s => ⋃ j in s, (γ j : Set V)
  let p : ℕ → Prop := fun n => ∃ s : Finset ι, U s = (⊤ : Set V) ∧ s.card = n
  have hp : ∃ n, p n := by
    refine ⟨Fintype.card ι, ?_⟩
    refine ⟨Finset.univ, ?_, by simp⟩
    simpa [U] using htop
  rcases Nat.find_spec hp with ⟨s, hs_top, hs_card⟩
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := by simpa using hne
    simpa [U, hs_empty] using hs_top
  rcases hs_nonempty with ⟨i, hi⟩
  have hv : ∃ v : V, v ∉ γ i := by
    by_contra hv
    have hsubset : (⊤ : Submodule K V) ≤ γ i := by
      intro x hx
      by_contra hx'
      exact hv ⟨x, hx'⟩
    exact h i (le_antisymm hsubset le_top)
  rcases hv with ⟨v, hv⟩
  have herase_nonempty : (s.erase i).Nonempty := by
    by_contra hempty
    have hs_eq : s = {i} := by
      ext j
      constructor
      · intro hj
        by_cases hji : j = i
        · simpa [hji] using hj
        · exfalso
          have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hj, hji⟩
          simpa [hempty] using hj'
      · intro hj
        simp at hj
        simpa [hj] using hi
    have htop' : (γ i : Submodule K V) = ⊤ := by
      simpa [U, hs_eq] using hs_top
    exact h i htop'
  have hnot : ¬ γ i ≤ U (s.erase i) := by
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
    have hle : Nat.find hp ≤ (s.erase i).card := Nat.find_min' hp ⟨s.erase i, htop', rfl⟩
    have hlt : (s.erase i).card < Nat.find hp := by
      have htmp : (s.erase i).card < s.card := by
        have hcard' := Finset.card_erase_add_one hi
        simpa [hcard'] using Nat.lt_succ_self (s.erase i).card
      simpa [hs_card] using htmp
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  rcases not_subset.mp hnot with ⟨u, hu_mem, hu_not⟩
  have hu_ne : u ≠ 0 := by
    intro hu0
    have h0 : u ∈ U (s.erase i) := by
      rcases herase_nonempty with ⟨j, hj⟩
      exact ⟨j, hj, by simpa [hu0] using (γ j).zero_mem⟩
    exact hu_not h0
  let L : Type* := {x : V // ∃ t : K, x = v + t • u}
  let f : K → L := fun t => ⟨v + t • u, ⟨t, rfl⟩⟩
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
  have hinfL : Infinite L := Infinite.of_injective f hf
  have hx_exists : ∀ x : L, ∃ j : {j : ι // j ∈ s.erase i}, (x : V) ∈ γ j.1 := by
    intro x
    rcases x.2 with ⟨t, rfl⟩
    have hxnoti : (v + t • u : V) ∉ γ i := by
      intro hxmem
      have hv_mem : v ∈ γ i := by
        have hu_t : t • u ∈ γ i := (γ i).smul_mem t hu_mem
        exact (γ i).sub_mem hxmem hu_t
      exact hv hv_mem
    have hxU : (v + t • u : V) ∈ U s := by
      simpa [U, hs_top]
    simp [U] at hxU
    rcases hxU with ⟨j, hj, hxj⟩
    by_cases hji : j = i
    · subst hji
      exact False.elim (hxnoti hxj)
    · exact ⟨⟨j, Finset.mem_erase.mpr ⟨hj, hji⟩⟩, hxj⟩
  haveI : Fintype {j : ι // j ∈ s.erase i} := by infer_instance
  let g : L → {j : ι // j ∈ s.erase i} := fun x => Classical.choose (hx_exists x)
  have hg : Function.Injective g := by
    intro x y hxy
    have hJ : (g x).1 = (g y).1 := by
      simpa using congrArg Subtype.val hxy
    apply Subtype.ext
    rcases x.2 with ⟨tx, rfl⟩
    rcases y.2 with ⟨ty, rfl⟩
    have hjx : (v + tx • u : V) ∈ γ (g x).1 := by
      simpa using (Classical.choose_spec (hx_exists x))
    have hjy : (v + ty • u : V) ∈ γ (g x).1 := by
      simpa [hJ] using (Classical.choose_spec (hx_exists y))
    have hscalar : tx = ty := by
      by_contra hneq
      have hdiff_mem : (tx - ty) • u ∈ γ (g x).1 := by
        have hsub := (γ (g x).1).sub_mem hjx hjy
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_smul] using hsub
      have hnonzero : tx - ty ≠ 0 := sub_ne_zero.mpr hneq
      have huj : u ∉ γ (g x).1 := by
        intro huj
        exact hu_not ⟨(g x).1, (g x).2, huj⟩
      have hu_mem' : u ∈ γ (g x).1 := by
        have htmp := (γ (g x).1).smul_mem (tx - ty)⁻¹ hdiff_mem
        simpa [smul_smul, hnonzero] using htmp
      exact huj hu_mem'
    simpa [hscalar]
  have hfinL : Finite L := Finite.of_injective g hg
  exact hfinL.not_infinite hinfL
