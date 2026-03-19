import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · refine ⟨0, ?_⟩
    rw [hI]
    simp
  · have hI' : ∃ a : R, a ∈ I ∧ a ≠ 0 := by
      by_contra h
      apply hI
      apply le_antisymm
      · intro x hx
        change x = 0
        by_contra hx0
        exact h ⟨x, hx, hx0⟩
      · exact bot_le
    obtain ⟨a0, ha0I, ha0ne⟩ := hI'
    have hmin_exists :
        ∃ a : R, a ∈ I ∧ a ≠ 0 ∧ ∀ b : R, b ∈ I → b ≠ 0 → b ∣ a → a ∣ b := by
      by_contra hno
      have hstep :
          ∀ a : R, a ∈ I → a ≠ 0 → ∃ b : R, b ∈ I ∧ b ≠ 0 ∧ b ∣ a ∧ ¬ a ∣ b := by
        intro a ha ha0
        by_contra h
        apply hno
        refine ⟨a, ha, ha0, ?_⟩
        intro b hb hb0 hba
        by_contra hab
        exact h ⟨b, hb, hb0, hba, hab⟩
      choose next hnextI hnext0 hnextdvd hnextndvd using hstep
      let S : Type _ := {x : R // x ∈ I ∧ x ≠ 0}
      let start : S := ⟨a0, ha0I, ha0ne⟩
      let step : S → S := fun x =>
        ⟨next x.1 x.2.1 x.2.2, hnextI x.1 x.2.1 x.2.2, hnext0 x.1 x.2.1 x.2.2⟩
      let f : ℕ → S := fun n => Nat.rec start (fun _ x => step x) n
      have hf_succ : ∀ n : ℕ, f (n + 1) = step (f n) := by
        intro n
        rfl
      have hf_dvd : ∀ n : ℕ, (f (n + 1)).1 ∣ (f n).1 := by
        intro n
        rw [hf_succ]
        exact hnextdvd (f n).1 (f n).2.1 (f n).2.2
      have hf_ndvd : ∀ n : ℕ, ¬ (f n).1 ∣ (f (n + 1)).1 := by
        intro n
        rw [hf_succ]
        exact hnextndvd (f n).1 (f n).2.1 (f n).2.2
      have hseq : ∀ i : ℕ, (f i).1 ≠ 0 ∧ (f (i + 1)).1 ∣ (f i).1 := by
        intro i
        exact ⟨(f i).2.2, hf_dvd i⟩
      rcases h2 (fun n => (f n).1) hseq with ⟨N, hN⟩
      rcases hN (N + 1) (Nat.le_succ N) with ⟨u, hu, huEq⟩
      have hdiv : (f N).1 ∣ (f (N + 1)).1 := by
        refine ⟨u, ?_⟩
        simpa [mul_comm] using huEq
      exact hf_ndvd N hdiv
    obtain ⟨a, haI, ha0, hmin⟩ := hmin_exists
    refine ⟨a, le_antisymm ?_ ?_⟩
    · refine Ideal.span_le.2 ?_
      intro x hx
      have hx' : x = a := by simpa using hx
      rw [hx']
      exact haI
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Ideal.zero_mem _
      · rcases h1 a x ha0 hx0 with ⟨r, s, hbez⟩
        have hra : r * a ∈ I := I.mul_mem_left r haI
        have hsx : s * x ∈ I := I.mul_mem_left s hx
        have hdI : gcd a x ∈ I := by
          rw [hbez]
          exact I.add_mem hra hsx
        have hd0 : gcd a x ≠ 0 := by
          intro hd
          rcases gcd_dvd_left a x with ⟨c, hc⟩
          rw [hd] at hc
          simp at hc
          exact ha0 hc
        have had : a ∣ gcd a x := hmin (gcd a x) hdI hd0 (gcd_dvd_left a x)
        have hax : a ∣ x := by
          rcases had with ⟨d, hd⟩
          rcases gcd_dvd_right a x with ⟨e, he⟩
          refine ⟨d * e, ?_⟩
          rw [he, hd, mul_assoc]
        rcases hax with ⟨c, rfl⟩
        have ha_span : a ∈ Ideal.span ({a} : Set R) := Ideal.subset_span (by simp)
        have hc_span : c * a ∈ Ideal.span ({a} : Set R) := Ideal.mul_mem_left _ c ha_span
        simpa [mul_comm] using hc_span
