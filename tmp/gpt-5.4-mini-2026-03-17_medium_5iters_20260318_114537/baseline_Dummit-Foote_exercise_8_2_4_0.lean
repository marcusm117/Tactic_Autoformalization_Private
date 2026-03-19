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
  by_cases hbot : I = ⊥
  · subst hbot
    refine ⟨0, ?_⟩
    simp
  · have hnonzero : ∃ a : R, a ∈ I ∧ a ≠ 0 := by
      by_contra h
      have hle : I ≤ ⊥ := by
        intro x hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · exfalso
          exact h ⟨x, hx, hx0⟩
      have : I = ⊥ := le_antisymm hle bot_le
      exact hbot this
    rcases hnonzero with ⟨a0, ha0I, ha0nz⟩
    let S : Type := {x : R // x ∈ I ∧ x ≠ 0}
    have hmin : ∃ x : S, ∀ y : S, y.1 ∣ x.1 → x.1 ∣ y.1 := by
      by_contra hno
      have hstep : ∀ x : S, ∃ y : S, y.1 ∣ x.1 ∧ ¬ x.1 ∣ y.1 := by
        intro x
        by_contra hx
        have hxgood : ∀ y : S, y.1 ∣ x.1 → x.1 ∣ y.1 := by
          intro y hy
          by_contra hxy
          exact hx ⟨y, hy, hxy⟩
        exact hno ⟨x, hxgood⟩
      choose f hf using hstep
      let a : ℕ → S := fun n => Nat.rec a0 (fun _ ih => f ih) n
      have ha_succ : ∀ n : ℕ, a (n + 1) = f (a n) := by
        intro n
        simp [a]
      have hchain : ∀ n : ℕ, (a (n + 1)).1 ∣ (a n).1 ∧ ¬ (a n).1 ∣ (a (n + 1)).1 := by
        intro n
        rw [ha_succ n]
        exact hf (a n)
      have h2seq : ∀ i : ℕ, (a i : R) ≠ 0 ∧ a (i + 1) ∣ a i := by
        intro i
        exact ⟨(a i).2.2, by simpa using (hchain i).1⟩
      obtain ⟨N, hN⟩ := h2 (fun i : ℕ => (a i : R)) h2seq
      have hunit := hN (N + 1) (Nat.le_succ N)
      rcases hunit with ⟨u, hu, hEq⟩
      have hdiv : a N ∣ a (N + 1) := by
        refine ⟨u, ?_⟩
        simpa [mul_comm] using hEq
      exact (hchain N).2 hdiv
    rcases hmin with ⟨m, hm⟩
    refine ⟨m.1, ?_⟩
    apply le_antisymm
    · intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxS : S := ⟨x, ⟨hx, hx0⟩⟩
        let d : R := gcd m.1 x
        have hdmem : d ∈ I := by
          dsimp [d]
          rcases h1 m.1 x m.2.2 hx0 with ⟨r, s, hr⟩
          rw [hr]
          exact I.add_mem (I.mul_mem_left _ m.2.1) (I.mul_mem_left _ hx)
        have hddivm : d ∣ m.1 := by
          simpa [d] using gcd_dvd_left m.1 x
        have hddivx : d ∣ x := by
          simpa [d] using gcd_dvd_right m.1 x
        have hdne : d ≠ 0 := by
          intro hd0
          have h0 : (0 : R) ∣ m.1 := by
            simpa [d, hd0] using hddivm
          have hm0 : m.1 = 0 := by simpa using h0
          exact m.2.2 hm0
        have hdS : S := ⟨d, ⟨hdmem, hdne⟩⟩
        have hmdivd : m.1 ∣ d := hm hdS hddivm
        have hmdivx : m.1 ∣ x := dvd_trans hmdivd hddivx
        exact Ideal.mem_span_singleton.mpr hmdivx
    · refine Ideal.span_le.mpr ?_
      intro x hx
      have hx' : x = m.1 := by simpa using hx
      simpa [hx'] using m.2.1
