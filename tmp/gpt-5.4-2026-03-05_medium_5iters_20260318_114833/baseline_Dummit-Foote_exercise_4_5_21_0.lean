import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  intro hs
  have hcard17 : ∀ P : Sylow 17 G, Fintype.card P = 17 := by
    intro P
    have h := P.card_eq
    norm_num [hG] at h
    exact h
  have hcard19 : ∀ P : Sylow 19 G, Fintype.card P = 19 := by
    intro P
    have h := P.card_eq
    norm_num [hG] at h
    exact h
  set n17 : Nat := Fintype.card (Sylow 17 G)
  have h17dvd : n17 ∣ 171 := by
    subst n17
    simpa [hG] using (Sylow.card_sylow_dvd_index (α := G) (p := 17))
  have h17mod : n17 ≡ 1 [MOD 17] := by
    subst n17
    simpa using (Sylow.card_sylow_modEq_one (α := G) (p := 17))
  have h17pos : 0 < n17 := by
    subst n17
    exact Fintype.card_pos_iff.mpr inferInstance
  have h17le : n17 ≤ 171 := Nat.le_of_dvd (by norm_num) h17dvd
  have h17small : n17 = 1 ∨ n17 = 171 := by
    interval_cases n17 <;> norm_num at h17dvd h17mod ⊢
  set n19 : Nat := Fintype.card (Sylow 19 G)
  have h19dvd : n19 ∣ 153 := by
    subst n19
    simpa [hG] using (Sylow.card_sylow_dvd_index (α := G) (p := 19))
  have h19mod : n19 ≡ 1 [MOD 19] := by
    subst n19
    simpa using (Sylow.card_sylow_modEq_one (α := G) (p := 19))
  have h19pos : 0 < n19 := by
    subst n19
    exact Fintype.card_pos_iff.mpr inferInstance
  have h19le : n19 ≤ 153 := Nat.le_of_dvd (by norm_num) h19dvd
  have h19small : n19 = 1 ∨ n19 = 153 := by
    interval_cases n19 <;> norm_num at h19dvd h19mod ⊢
  have hn17_ne_one : n17 ≠ 1 := by
    intro h1
    let P : Sylow 17 G := Classical.choice (inferInstance : Nonempty (Sylow 17 G))
    have hPnormal : (P : Subgroup G).Normal := by
      have : Fintype.card (Sylow 17 G) = 1 := by simpa [n17] using h1
      exact P.normal_of_card_eq_one this
    letI : (P : Subgroup G).Normal := hPnormal
    have hne_bot : (P : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hp := hcard17 P
      rw [hbot] at hp
      norm_num at hp
    have hne_top : (P : Subgroup G) ≠ ⊤ := by
      intro htop
      have hp := hcard17 P
      rw [htop, hG] at hp
      norm_num at hp
    exact (hs.eq_bot_or_eq_top (P : Subgroup G)).elim hne_bot hne_top
  have hn19_ne_one : n19 ≠ 1 := by
    intro h1
    let P : Sylow 19 G := Classical.choice (inferInstance : Nonempty (Sylow 19 G))
    have hPnormal : (P : Subgroup G).Normal := by
      have : Fintype.card (Sylow 19 G) = 1 := by simpa [n19] using h1
      exact P.normal_of_card_eq_one this
    letI : (P : Subgroup G).Normal := hPnormal
    have hne_bot : (P : Subgroup G) ≠ ⊥ := by
      intro hbot
      have hp := hcard19 P
      rw [hbot] at hp
      norm_num at hp
    have hne_top : (P : Subgroup G) ≠ ⊤ := by
      intro htop
      have hp := hcard19 P
      rw [htop, hG] at hp
      norm_num at hp
    exact (hs.eq_bot_or_eq_top (P : Subgroup G)).elim hne_bot hne_top
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
    have hRdvd : Fintype.card R ∣ 17 := by
      have hdiv : Fintype.card R ∣ Fintype.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard17 P] using hdiv
    have hRne1 : Fintype.card R ≠ 1 := by
      intro hR1
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1
      have : (⟨(g : G), hx⟩ : R) = 1 := by simp
      exact hne (congrArg Subtype.val this)
    have hR17 : Fintype.card R = 17 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 17)).mp hRdvd with hR1 | hR17
      · exact (hRne1 hR1).elim
      · exact hR17
    have hRP : R = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (P : Subgroup G) by exact inf_le_left)
      rw [hR17, hcard17 P]
    have hRQ : R = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      rw [hR17, hcard17 Q]
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
    have hRdvd : Fintype.card R ∣ 19 := by
      have hdiv : Fintype.card R ∣ Fintype.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard19 P] using hdiv
    have hRne1 : Fintype.card R ≠ 1 := by
      intro hR1
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1
      have : (⟨(g : G), hx⟩ : R) = 1 := by simp
      exact hne (congrArg Subtype.val this)
    have hR19 : Fintype.card R = 19 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 19)).mp hRdvd with hR1 | hR19
      · exact (hRne1 hR1).elim
      · exact hR19
    have hRP : R = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (P : Subgroup G) by exact inf_le_left)
      rw [hR19, hcard19 P]
    have hRQ : R = (Q : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      rw [hR19, hcard19 Q]
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
    have hRdvd17 : Fintype.card R ∣ 17 := by
      have hdiv : Fintype.card R ∣ Fintype.card P :=
        Subgroup.card_dvd_of_le (show R ≤ (P : Subgroup G) by exact inf_le_left)
      simpa [hcard17 P] using hdiv
    have hRdvd19 : Fintype.card R ∣ 19 := by
      have hdiv : Fintype.card R ∣ Fintype.card Q :=
        Subgroup.card_dvd_of_le (show R ≤ (Q : Subgroup G) by exact inf_le_right)
      simpa [hcard19 Q] using hdiv
    have hR1 : Fintype.card R = 1 := by
      apply Nat.eq_one_of_dvd_one
      have : Fintype.card R ∣ Nat.gcd 17 19 := Nat.dvd_gcd hRdvd17 hRdvd19
      norm_num at this
      exact this
    have hRne1 : Fintype.card R ≠ 1 := by
      intro hR1'
      letI : Unique R := Fintype.card_eq_one_iff.mp hR1'
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
        Fintype.card (Sylow 17 G) * 16 := by
    rw [Fintype.card_sigma]
    simp [hfiber17, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hS19 :
      Fintype.card (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1}) =
        Fintype.card (Sylow 19 G) * 18 := by
    rw [Fintype.card_sigma]
    simp [hfiber19, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  let f :
      (Σ P : Sylow 17 G, {g : P // (g : G) ≠ 1}) ⊕
        (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1}) → G
    | Sum.inl ⟨P, ⟨g, _⟩⟩ => g
    | Sum.inr ⟨P, ⟨g, _⟩⟩ => g
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
        (Σ P : Sylow 19 G, {g : P // (g : G) ≠ 1})) = 5490 := by
    rw [Fintype.card_sum, hS17, hS19, hn17, hn19]
    norm_num
  have hle := Fintype.card_le_of_injective f hf
  rw [hcardDom, hG] at hle
  norm_num at hle
