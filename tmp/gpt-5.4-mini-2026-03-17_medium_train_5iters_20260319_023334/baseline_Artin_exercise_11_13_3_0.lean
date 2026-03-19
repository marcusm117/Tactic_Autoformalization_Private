import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  let f : ℕ → ℕ := fun x => if Nat.Prime x ∧ x ≡ 3 [MOD 4] ∧ x ≠ 3 then x else 1
  let P : ℕ := ∏ x in Finset.range (N + 1), f x
  let a : ℕ := 4 * P + 3
  have hno3 : ∀ x, ¬ 3 ∣ f x := by
    intro x
    dsimp [f]
    split_ifs with h
    · intro h3
      have hxeq := Nat.Prime.dvd_prime (by decide : Nat.Prime 3) h.1 h3
      exact h.2.2 (by simpa using hxeq)
    · simp
  have hprod_not_dvd : ∀ s : Finset ℕ, (∀ x ∈ s, ¬ 3 ∣ f x) → ¬ 3 ∣ ∏ x in s, f x := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp
    · intro x s hx ih hs
      have hfx : ¬ 3 ∣ f x := hs x (by simp [hx])
      have hs' : ∀ y ∈ s, ¬ 3 ∣ f y := by
        intro y hy
        exact hs y (by simp [hy, hx])
      have hrest : ¬ 3 ∣ ∏ y in s, f y := ih hs'
      intro hdiv
      have hmul : 3 ∣ f x * ∏ y in s, f y := by
        simpa [Finset.prod_insert hx, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have h3prime : Nat.Prime 3 := by decide
      rcases h3prime.dvd_mul.mp hmul with hleft | hright
      · exact hfx hleft
      · exact hrest hright
  have hP3 : ¬ 3 ∣ P := by
    dsimp [P]
    exact hprod_not_dvd _ hno3
  have hmodP3 : a % 3 = P % 3 := by
    dsimp [a, P]
    norm_num
  have ha3 : ¬ 3 ∣ a := by
    intro hdiv
    have h0 : a % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hP0 : P % 3 = 0 := by
      rw [← hmodP3] at h0
      exact h0
    exact hP3 (Nat.mod_eq_zero_iff_dvd.mp hP0)
  have hlist : ∀ l : List ℕ, (∀ p ∈ l, p ≡ 1 [MOD 4]) → l.prod ≡ 1 [MOD 4] := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons x xs ih =>
        intro hx
        have hx1 : x ≡ 1 [MOD 4] := hx x (by simp)
        have hxs : ∀ p ∈ xs, p ≡ 1 [MOD 4] := by
          intro p hp
          exact hx p (by simp [hp])
        have hxs1 : xs.prod ≡ 1 [MOD 4] := ih hxs
        simpa [List.prod_cons] using hx1.mul hxs1
  have hnotall : ¬ (∀ p ∈ a.primeFactorsList, p ≡ 1 [MOD 4]) := by
    intro hall
    have hprod1 : a.primeFactorsList.prod ≡ 1 [MOD 4] := hlist _ hall
    have h1a : a ≡ 1 [MOD 4] := by
      simpa [Nat.primeFactorsList_prod] using hprod1
    have h13 : (1 : ℕ) ≡ 3 [MOD 4] := h1a.symm.trans (by
      dsimp [a]
      norm_num)
    norm_num at h13
  have hex : ∃ p ∈ a.primeFactorsList, ¬ p ≡ 1 [MOD 4] := by
    push_neg at hnotall
    exact hnotall
  rcases hex with ⟨p, hp_mem, hpnot1⟩
  have hpprime : Nat.Prime p := (Nat.mem_primeFactorsList.mp hp_mem).1
  have hpdiva : p ∣ a := (Nat.mem_primeFactorsList.mp hp_mem).2
  have hpne2 : p ≠ 2 := by
    intro h2
    have h2div : 2 ∣ a := by simpa [h2] using hpdiva
    rcases h2div with ⟨k, hk⟩
    dsimp [a] at hk
    omega
  have hpodd : Nat.Odd p := (Nat.Prime.odd_iff).2 hpne2
  rcases hpodd with ⟨k, hk⟩
  have hpmod2 : p % 2 = 1 := by
    rw [hk]
    norm_num
  have hpmod4eq : p % 4 = 3 := by
    have hmod2 : (p % 4) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4), hpmod2]
    interval_cases h : p % 4
    · have : False := by simpa [h] using hmod2
      exact False.elim this
    · exact False.elim (hpnot1 (by simpa [h]))
    · have : False := by simpa [h] using hmod2
      exact False.elim this
    · simpa [h]
  have hpmod4 : p ≡ 3 [MOD 4] := by
    simpa [Nat.ModEq] using hpmod4eq
  have hpne3 : p ≠ 3 := by
    intro h3
    have h3div : 3 ∣ a := by simpa [h3] using hpdiva
    exact ha3 h3div
  have hpgt : p > N := by
    by_contra hle
    have hle' : p ≤ N := le_of_not_gt hle
    have hp_in : p ∈ Finset.range (N + 1) := by
      simpa [Nat.lt_succ_iff] using hle'
    have hpdivP : p ∣ P := by
      dsimp [P]
      simpa [f, hpprime, hpmod4, hpne3] using Finset.dvd_prod_of_mem hp_in
    have hpdiv4P : p ∣ 4 * P := dvd_mul_of_dvd_right hpdivP 4
    have hle4P : 4 * P ≤ a := by
      dsimp [a]
      omega
    have hpdiv3 : p ∣ 3 := by
      have hsub : p ∣ a - 4 * P := Nat.dvd_sub' hpdiva hpdiv4P hle4P
      have hsub3 : a - 4 * P = 3 := by
        dsimp [a]
        omega
      simpa [hsub3] using hsub
    have hp_eq3 : p = 3 := hpprime.dvd_prime (by decide : Nat.Prime 3) hpdiv3
    exact hpne3 hp_eq3
  have hpcong : p + 1 ≡ 0 [MOD 4] := by
    dsimp [Nat.ModEq]
    rw [Nat.add_mod_right_left, hpmod4eq]
    norm_num
  exact ⟨p, le_of_lt hpgt, hpprime, hpcong⟩
