import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  let f : ℕ → ℕ := fun x => if Nat.Prime x ∧ x % 4 = 3 ∧ x ≠ 3 then x else 1
  let P : ℕ := (Finset.range (N + 1)).prod f
  let a : ℕ := 4 * P + 3
  have h3prime : Nat.Prime 3 := by decide
  have hf3 : ∀ x, ¬ 3 ∣ f x := by
    intro x
    dsimp [f]
    split_ifs with hx
    · intro hdiv
      have hx3 : x = 3 := by
        simpa using Nat.Prime.dvd_prime h3prime hx.1 hdiv
      exact hx.2.2 hx3
    · simp
  have hprod_not_dvd : ∀ s : Finset ℕ, (∀ x ∈ s, ¬ 3 ∣ f x) → ¬ 3 ∣ s.prod f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro hs
      simp
    · intro x s hx ih hs
      have hx' : ¬ 3 ∣ f x := hs x (by simp [hx])
      have hs' : ∀ y ∈ s, ¬ 3 ∣ f y := by
        intro y hy
        exact hs y (by simp [hy, hx])
      have hrest : ¬ 3 ∣ s.prod f := ih hs'
      intro hdiv
      have hmul : 3 ∣ f x * s.prod f := by
        simpa [Finset.prod_insert hx, mul_comm, mul_left_comm, mul_assoc] using hdiv
      rcases h3prime.dvd_mul.mp hmul with hfx | hrest'
      · exact hx' hfx
      · exact hrest hrest'
  have hP3 : ¬ 3 ∣ P := by
    dsimp [P]
    exact hprod_not_dvd (Finset.range (N + 1)) (by
      intro x hx
      exact hf3 x)
  have ha3 : ¬ 3 ∣ a := by
    intro hdiv
    have hle : 3 ≤ a := by
      dsimp [a]
      omega
    have hsub : 3 ∣ a - 3 := Nat.dvd_sub' hdiv (by simp) hle
    have hsub' : 3 ∣ 4 * P := by
      simpa [a] using hsub
    rcases h3prime.dvd_mul.mp hsub' with h4 | hP
    · exact (by norm_num at h4) h4
    · exact hP3 hP
  have hlist : ∀ l : List ℕ, (∀ p ∈ l, p % 4 = 1) → l.prod % 4 = 1 := by
    intro l
    induction l with
    | nil =>
        intro _
        norm_num
    | cons x xs ih =>
        intro hx
        have hx1 : x % 4 = 1 := hx x (by simp)
        have hxs : ∀ p ∈ xs, p % 4 = 1 := by
          intro p hp
          exact hx p (by simp [hp])
        have hxs1 : xs.prod % 4 = 1 := ih hxs
        have hxM : x ≡ 1 [MOD 4] := by
          simpa [Nat.ModEq] using hx1
        have hxsM : xs.prod ≡ 1 [MOD 4] := by
          simpa [Nat.ModEq] using hxs1
        have hprodM : x * xs.prod ≡ 1 [MOD 4] := hxM.mul hxsM
        simpa [Nat.ModEq, List.prod_cons] using hprodM
  have hnotall : ¬ ∀ p ∈ a.primeFactorsList, p % 4 = 1 := by
    intro hall
    have hprod1 : a.primeFactorsList.prod % 4 = 1 := hlist _ hall
    have hprod_eq : a.primeFactorsList.prod = a := Nat.primeFactorsList_prod a
    have ha1 : a % 4 = 1 := by
      simpa [hprod_eq] using hprod1
    have ha3 : a % 4 = 3 := by
      dsimp [a]
      norm_num
    have h13 : (1 : ℕ) = 3 := by
      calc
        1 = a % 4 := by simpa using ha1.symm
        _ = 3 := ha3
    omega
  have hex : ∃ p ∈ a.primeFactorsList, ¬ p % 4 = 1 := by
    push_neg at hnotall
    exact hnotall
  rcases hex with ⟨p, hp_mem, hpnot1⟩
  have hpprime : Nat.Prime p := (Nat.mem_primeFactorsList.mp hp_mem).1
  have hpdiva : p ∣ a := (Nat.mem_primeFactorsList.mp hp_mem).2
  have hpne2 : p ≠ 2 := by
    intro h2
    have h2div : 2 ∣ a := by simpa [h2] using hpdiva
    have h0 : a % 2 = 0 := Nat.mod_eq_zero_of_dvd h2div
    have h1 : a % 2 = 1 := by
      dsimp [a]
      norm_num
    omega
  have hpodd : Nat.Odd p := (hpprime.odd_iff).2 hpne2
  rcases hpodd with ⟨k, hk⟩
  have hpmod2 : p % 2 = 1 := by
    rw [hk]
    norm_num
  have hmod2 : (p % 4) % 2 = 1 := by
    simpa [hpmod2] using (Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4))
  have hpmod4 : p % 4 = 3 := by
    interval_cases h : p % 4
    · have : False := by simpa [h] using hmod2
      exact False.elim this
    · exact False.elim (hpnot1 (by simpa [Nat.ModEq, h]))
    · have : False := by simpa [h] using hmod2
      exact False.elim this
    · simpa [h]
  have hpne3 : p ≠ 3 := by
    intro h3
    have h3div : 3 ∣ a := by simpa [h3] using hpdiva
    exact ha3 h3div
  have hpgt : p > N := by
    by_contra hle
    have hp_le : p ≤ N := le_of_not_gt hle
    have hp_in : p ∈ Finset.range (N + 1) := by
      simpa [Nat.lt_succ_iff] using hp_le
    have hpdivP : p ∣ P := by
      dsimp [P]
      have hfp : f p = p := by
        dsimp [f]
        simp [hpprime, hpmod4, hpne3]
      simpa [hfp] using Finset.dvd_prod_of_mem hp_in
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
    have hp_eq3 : p = 3 := Nat.Prime.dvd_prime (by decide : Nat.Prime 3) hpdiv3
    exact hpne3 hp_eq3
  have hpcong : p + 1 ≡ 0 [MOD 4] := by
    dsimp [Nat.ModEq]
    rw [Nat.add_mod_right_left, hpmod4]
    norm_num
  exact ⟨p, le_of_lt hpgt, hpprime, hpcong⟩
