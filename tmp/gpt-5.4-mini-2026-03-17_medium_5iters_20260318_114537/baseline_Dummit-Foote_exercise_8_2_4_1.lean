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
  · subst hI
    refine ⟨0, ?_⟩
    simp
  · have hnonzero : ∃ a : R, a ∈ I ∧ a ≠ 0 := by
      by_contra h
      have hsubset : I ≤ (⊥ : Ideal R) := by
        intro x hx
        by_cases hx0 : x = 0
        · simpa [hx0]
        · exfalso
          exact h ⟨x, hx, hx0⟩
      exact hI (le_antisymm hsubset bot_le)
    rcases hnonzero with ⟨a0, ha0I, ha0nz⟩
    let S := {x : R // x ∈ I ∧ x ≠ 0}
    have hmin : ∃ m : S, ∀ y : S, y.1 ∣ m.1 → m.1 ∣ y.1 := by
      by_contra hno
      have hstep : ∀ x : S, ∃ y : S, y.1 ∣ x.1 ∧ ¬ x.1 ∣ y.1 := by
        intro x
        by_contra hx
        have hx' : ∀ y : S, y.1 ∣ x.1 → x.1 ∣ y.1 := by
          intro y hy
          by_contra hxy
          exact hx ⟨y, hy, hxy⟩
        exact hno ⟨x, hx'⟩
      let f : S → S := fun x => Classical.choose (hstep x)
      have hf : ∀ x : S, (f x).1 ∣ x.1 ∧ ¬ x.1 ∣ (f x).1 := by
        intro x
        simpa [f] using Classical.choose_spec (hstep x)
      let a : ℕ → S := fun n => Nat.recOn n ⟨a0, ha0I, ha0nz⟩ (fun _ ih => f ih)
      have ha_succ : ∀ n : ℕ, a (n + 1) = f (a n) := by
        intro n
        simp [a]
      have hdivsucc : ∀ n : ℕ, (a (n + 1) : R) ∣ (a n : R) := by
        intro n
        simpa [a, ha_succ n] using (hf (a n)).1
      have hnotdivsucc : ∀ n : ℕ, ¬ (a n : R) ∣ (a (n + 1) : R) := by
        intro n
        simpa [a, ha_succ n] using (hf (a n)).2
      have h2seq : ∀ i : ℕ, (fun n : ℕ => (a n : R)) i ≠ 0 ∧
          (fun n : ℕ => (a n : R)) (i + 1) ∣ (fun n : ℕ => (a n : R)) i := by
        intro i
        refine ⟨(a i).2.2, ?_⟩
        simpa using hdivsucc i
      obtain ⟨N, hN⟩ := h2 (fun n : ℕ => (a n : R)) h2seq
      have hassoc := hN (N + 1) (Nat.le_succ N)
      rcases hassoc with ⟨u, hu, hEq⟩
      have hdiv : (a N : R) ∣ (a (N + 1) : R) := by
        refine ⟨u, ?_⟩
        simpa [mul_comm] using hEq
      exact (hnotdivsucc N) hdiv
    rcases hmin with ⟨m, hm⟩
    refine ⟨m.1, ?_⟩
    apply le_antisymm
    · intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · let d : R := gcd m.1 x
        have hdmem : d ∈ I := by
          rcases h1 m.1 x m.2.2 hx0 with ⟨r, s, hr⟩
          rw [hr]
          exact I.add_mem (I.mul_mem_left r m.2.1) (I.mul_mem_left s hx)
        have hddivm : d ∣ m.1 := by
          simpa [d] using gcd_dvd_left m.1 x
        have hddivx : d ∣ x := by
          simpa [d] using gcd_dvd_right m.1 x
        have hdne : d ≠ 0 := by
          intro hd0
          have h0 : (0 : R) ∣ m.1 := by
            simpa [d, hd0] using hddivm
          rcases h0 with ⟨c, hc⟩
          exact m.2.2 (by simpa using hc)
        have hdS : S := ⟨d, ⟨hdmem, hdne⟩⟩
        have hmdivd : m.1 ∣ d := hm hdS hddivm
        have hmdivx : m.1 ∣ x := dvd_trans hmdivd hddivx
        exact (Ideal.mem_span_singleton.2 hmdivx)
    · refine Ideal.span_le.2 ?_
      intro x hx
      have hx' : x = m.1 := by simpa using hx
      simpa [hx'] using m.2.1
