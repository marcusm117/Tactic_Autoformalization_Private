import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_15 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ (p : ℕ) (P : Sylow p G), p.Prime ∧ (p ∣ card G) ∧  P.Normal := by
  classical
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  have h13dvd : 13 ∣ card G := by omega
  have hpow13 : 13 ^ (Nat.factorization 351 13) = 13 := by native_decide
  have hPcard : card P = 13 := by
    have h := P.card_eq_multiplicity
    simpa [Nat.card_eq_fintype_card, hG, hpow13] using h
  have hidx_mul : (P : Subgroup G).index * card P = card G := by
    simpa [Nat.card_eq_fintype_card] using (Subgroup.index_mul_card (H := (P : Subgroup G)))
  have hidx : (P : Subgroup G).index = 27 := by
    omega
  set n : ℕ := card (Sylow 13 G)
  have hdiv : n ∣ 27 := by
    simpa [n, Nat.card_eq_fintype_card, hidx] using P.card_dvd_index
  have hmod : n ≡ 1 [MOD 13] := by
    simpa [n, Nat.card_eq_fintype_card] using (card_sylow_modEq_one (G := G) (p := 13))
  have hcases : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
    rcases hdiv with ⟨k, hk⟩
    have hk0 : 0 < k := by
      by_contra hk0
      omega
    have hk_le : k ≤ 27 := by
      omega
    interval_cases k <;> omega
  have hneq3 : n ≠ 3 := by
    intro hn
    have h' : (3 : ℕ) ≡ 1 [MOD 13] := by simpa [hn] using hmod
    have hfalse : ¬ ((3 : ℕ) ≡ 1 [MOD 13]) := by native_decide
    exact hfalse h'
  have hneq9 : n ≠ 9 := by
    intro hn
    have h' : (9 : ℕ) ≡ 1 [MOD 13] := by simpa [hn] using hmod
    have hfalse : ¬ ((9 : ℕ) ≡ 1 [MOD 13]) := by native_decide
    exact hfalse h'
  have hneq27 : n ≠ 27 := by
    intro hn
    have h' : (27 : ℕ) ≡ 1 [MOD 13] := by simpa [hn] using hmod
    have hfalse : ¬ ((27 : ℕ) ≡ 1 [MOD 13]) := by native_decide
    exact hfalse h'
  have hone : n = 1 := by
    rcases hcases with h1 | h3 | h9 | h27
    · exact h1
    · exact (hneq3 h3).elim
    · exact (hneq9 h9).elim
    · exact (hneq27 h27).elim
  have hone' : card (Sylow 13 G) = 1 := by
    simpa [n] using hone
  have hsub : Subsingleton (Sylow 13 G) := by
    rw [Fintype.card_eq_one_iff] at hone'
    rcases hone' with ⟨S, hS⟩
    exact ⟨fun a b => by
      calc
        a = S := hS a
        _ = b := (hS b).symm⟩
  letI : Subsingleton (Sylow 13 G) := hsub
  refine ⟨13, P, by decide, h13dvd, ?_⟩
  infer_instance
