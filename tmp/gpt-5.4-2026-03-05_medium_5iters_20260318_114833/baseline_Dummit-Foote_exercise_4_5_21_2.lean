import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  intro hs
  have hpow17 : 17 ^ Nat.factorization 2907 17 = 17 := by native_decide
  have hpow19 : 19 ^ Nat.factorization 2907 19 = 19 := by native_decide
  have hcard17n : ∀ P : Sylow 17 G, Nat.card P = 17 := by
    intro P
    have h := P.card_eq_multiplicity
    rw [hG] at h
    exact h.trans hpow17
  have hcard19n : ∀ P : Sylow 19 G, Nat.card P = 19 := by
    intro P
    have h := P.card_eq_multiplicity
    rw [hG] at h
    exact h.trans hpow19
  have hcard17 : ∀ P : Sylow 17 G, Fintype.card P = 17 := by
    intro P
    simpa [Nat.card_eq_fintype_card] using hcard17n P
  have hcard19 : ∀ P : Sylow 19 G, Fintype.card P = 19 := by
    intro P
    simpa [Nat.card_eq_fintype_card] using hcard19n P
  let P17 : Sylow 17 G := Classical.choice (inferInstance : Nonempty (Sylow 17 G))
  let P19 : Sylow 19 G := Classical.choice (inferInstance : Nonempty (Sylow 19 G))
  have hindex17 : (P17 : Subgroup G).index = 171 := by
    have h := (P17 : Subgroup G).index_mul_card
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hcard17 P17] at h
    norm_num at h
  have hindex19 : (P19 : Subgroup G).index = 153 := by
    have h := (P19 : Subgroup G).index_mul_card
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hcard19 P19] at h
    norm_num at h
  set n17 : Nat := Nat.card (Sylow 17 G)
  have h17dvd : n17 ∣ 171 := by
    subst n17
    simpa [hindex17] using P17.card_sylow_dvd_index
  have h17mod : n17 ≡ 1 [MOD 17] := by
    subst n17
    simpa using (card_sylow_modEq_one (G := G) (p := 17))
  have h17small : n17 = 1 ∨ n17 = 171 := by
    have h17le : n17 ≤ 171 := Nat.le_of_dvd (by norm_num) h17dvd
    let m : Fin 172 := ⟨n17, Nat.lt_succ_iff.mpr h17le⟩
    have harith :
        ∀ m : Fin 172, (m : Nat) ∣ 171 → (m : Nat) ≡ 1 [MOD 17] →
          (m : Nat) = 1 ∨ (m : Nat) = 171 := by
      native_decide
    simpa [m] using harith m h17dvd h17mod
  set n19 : Nat := Nat.card (Sylow 19 G)
  have h19dvd : n19 ∣ 153 := by
    subst n19
    simpa [hindex19] using P19.card_sylow_dvd_index
  have h19mod : n19 ≡ 1 [MOD 19] := by
    subst n19
    simpa using (card_sylow_modEq_one (G := G) (p := 19))
  have h19small : n19 = 1 ∨ n19 = 153 := by
    have h19le : n19 ≤ 153 := Nat.le_of_dvd (by norm_num) h19dvd
    let m : Fin 154 := ⟨n19, Nat.lt_succ_iff.mpr h19le⟩
    have harith :
        ∀ m : Fin 154, (m : Nat) ∣ 153 → (m : Nat) ≡ 1 [MOD 19] →
          (m : Nat) = 1 ∨ (m : Nat) = 153 := by
      native_decide
    simpa [m] using harith m h19dvd h19mod
  have hn17_ne_one : n17 ≠ 1 := by
    intro h1
    have hPnormal : (P17 : Subgroup G).Normal := by
      have : Nat.card (Sylow 17 G) = 1 := by simpa [n17] using h1
      exact P17.normal_of_card_eq_one this
    letI : (P17 : Subgroup G).Normal := hPnormal
    have hne_bot : (P17 : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hp := hcard17 P17
      rw [hbot] at hp
      norm_num at hp
    have hne_top : (P17 : Subgroup G) ≠ ⊤ := by
      intro htop
      have hp := hcard17 P17
      rw [htop, hG] at hp
      norm_num at hp
    exact (hs.eq_bot_or_eq_top (P17 : Subgroup G)).elim hne_bot hne_top
  have hn19_ne_one : n19 ≠ 1 := by
    intro h1
    have hPnormal : (P19 : Subgroup G).Normal := by
      have : Nat.card (Sylow 19 G) = 1 := by simpa [n19] using h1
      exact P19.normal_of_card_eq_one this
    letI : (P19 : Subgroup G).Normal := hPnormal
    have hne_bot : (P19 : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hp := hcard19 P19
      rw [hbot] at hp
      norm_num at hp
    have hne_top : (P19 : Subgroup G) ≠ ⊤ := by
      intro htop
      have hp := hcard19 P19
      rw [htop, hG] at hp
      norm_num at hp
    exact (hs.eq_bot_or_eq_top (P19 : Subgroup G)).elim hne_bot hne_top
  have hn17 : n17 = 171 := by
    rcases h17small with h | h
    · exact (hn17_ne_one h).elim
    · exact h
  have hn19 : n19 = 153 := by
    rcases h19small with h | h
    · exact (hn19_ne_one h).elim
    · exact h
  have h_eq17 :
      ∀ {P Q : Sylow 17 G} {g : P} {h : Q},
        (g : G) = h → (g : G) ≠ 1 → P = Q := by
    intro P Q g h hgh hne
    let R : Subgroup G := (P : Subgroup G) ⊓ Q
    have hx : (g : G) ∈ R := by
      constructor
      · exact g.2
      · simpa [hgh] using h.2
    have hRdvd : Nat.card R ∣ 17 := by
      have hdiv : Nat.card R ∣ Nat.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard17n P] using hdiv
    have hRne1 : Nat.card R ≠ 1 := by
      intro hR1
      have hR1' : Fintype.card R = 1 := by
        simpa [Nat.card_eq_fintype_card] using hR1
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1'
      have : (⟨(g : G), hx⟩ : R) = 1 := by simp
      exact hne (congrArg Subtype.val this)
    have hR17 : Nat.card R = 17 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 17)).mp hRdvd with hR1 | hR17
      · exact (hRne1 hR1).elim
      · exact hR17
    have hRP : R = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (P : Subgroup G) by exact inf_le_left)
      rw [hR17, hcard17n P]
    have hRQ : R = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      rw [hR17, hcard17n Q]
    apply Subtype.ext
    simpa [hRP, hRQ]
  have h_eq19 :
      ∀ {P Q : Sylow 19 G} {g : P} {h : Q},
        (g : G) = h → (g : G) ≠ 1 → P = Q := by
    intro P Q g h hgh hne
    let R : Subgroup G := (P : Subgroup G) ⊓ Q
    have hx : (g : G) ∈ R := by
      constructor
      · exact g.2
      · simpa [hgh] using h.2
    have hRdvd : Nat.card R ∣ 19 := by
      have hdiv : Nat.card R ∣ Nat.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard19n P] using hdiv
    have hRne1 : Nat.card R ≠ 1 := by
      intro hR1
      have hR1' : Fintype.card R = 1 := by
        simpa [Nat.card_eq_fintype_card] using hR1
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1'
      have : (⟨(g : G), hx⟩ : R) = 1 := by simp
      exact hne (congrArg Subtype.val this)
    have hR19 : Nat.card R = 19 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 19)).mp hRdvd with hR1 | hR19
      · exact (hRne1 hR1).elim
      · exact hR19
    have hRP : R = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (P : Subgroup G) by exact inf_le_left)
      rw [hR19, hcard19n P]
    have hRQ : R = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      rw [hR19, hcard19n Q]
    apply Subtype.ext
    simpa [hRP, hRQ]
  have h_disjoint :
      ∀ {P : Sylow 17 G} {Q : Sylow 19 G} {g : P} {h : Q},
        (g : G) = h → (g : G) ≠ 1 → False := by
    intro P Q g h hgh hne
    let R : Subgroup G := (P : Subgroup G) ⊓ Q
    have hx : (g : G) ∈ R := by
      constructor
      · exact g.2
      · simpa [hgh] using h.2
    have hRdvd17 : Nat.card R ∣ 17 := by
      have hdiv : Nat.card R ∣ Nat.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard17n P] using hdiv
    have hRdvd19 : Nat.card R ∣ 19 := by
      have hdiv : Nat.card R ∣ Nat.card Q :=
        Subgroup.card_dvd_of_le (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      simpa [hcard19n Q] using hdiv
    have hR1 : Nat.card R = 1 := by
      apply Nat.eq_one_of_dvd_one
      have : Nat.card R ∣ Nat.gcd 17 19 := Nat.dvd_gcd hRdvd17 hRdvd19
      norm_num at this
      exact this
    have hRne1 : Nat.card R ≠ 1 := by
      intro hR1'
      have hR1'' : Fintype.card R = 1 := by
        simpa [Nat.card_eq_fintype_card] using hR1'
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1''
      have : (⟨(g : G), hx⟩ : R) = 1 := by simp
      exact hne (congrArg Subtype.val this)
    exact hRne1 hR1
  have hfiber17 : ∀ P : Sylow 17 G, Fintype.card {g : P // (g : G) ≠ 1} = 16 := by
    intro P
    simpa [hcard17 P] using Fintype.card_ne (1 : P)
  have hfiber19 : ∀ P : Sylow 19 G, Fintype.card {g : P // (g : G) ≠ 1} = 18 := by
    intro P
    simpa [hcard19 P] using Fintype.card_ne (1 : P)
  have hS17 :
      Fintype.card (Σ P : Sylow 17 G, {g : P // (g : G) ≠ 1}) =
        Nat.card (Sylow 17 G) * 16 := by
    rw [Fintype.card_sigma]
    simp [hfiber17, Nat.card_eq_fintype_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hS19 :
      Fintype.card (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1}) =
        Nat.card (Sylow 19 G) * 18 := by
    rw [Fintype.card_sigma]
    simp [hfiber19, Nat.card_eq_fintype_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  let f :
      (Σ P : Sylow 17 G, {g : P // (g : G) ≠ 1}) ⊕
        (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1}) → G
    | Sum.inl ⟨_, ⟨g, _⟩⟩ => g
    | Sum.inr ⟨_, ⟨g, _⟩⟩ => g
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            rcases a with ⟨P, ⟨g, hg⟩⟩
            rcases b with ⟨Q, ⟨h, hh⟩⟩
            dsimp [f] at hab
            have hPQ : P = Q := h_eq17 hab hg
            subst hPQ
            have : g = h := Subtype.ext hab
            cases this
            rfl
        | inr b =>
            rcases a with ⟨P, ⟨g, hg⟩⟩
            rcases b with ⟨Q, ⟨h, hh⟩⟩
            dsimp [f] at hab
            exact (h_disjoint hab hg).elim
    | inr a =>
        cases b with
        | inl b =>
            rcases a with ⟨P, ⟨g, hg⟩⟩
            rcases b with ⟨Q, ⟨h, hh⟩⟩
            dsimp [f] at hab
            exact (h_disjoint hab.symm hh).elim
        | inr b =>
            rcases a with ⟨P, ⟨g, hg⟩⟩
            rcases b with ⟨Q, ⟨h, hh⟩⟩
            dsimp [f] at hab
            have hPQ : P = Q := h_eq19 hab hg
            subst hPQ
            have : g = h := Subtype.ext hab
            cases this
            rfl
  have hcardDom :
      Fintype.card ((Σ P : Sylow 17 G, {g : P // (g : G) ≠ 1}) ⊕
        (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1})) = 5472 := by
    rw [Fintype.card_sum, hS17, hS19, hn17, hn19]
    norm_num
  have hle := Fintype.card_le_of_injective f hf
  rw [hcardDom, hG] at hle
  norm_num at hle
