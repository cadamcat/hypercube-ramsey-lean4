import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S06.Prob

namespace HypercubeRamsey.S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

theorem restricted_weight_formula6 {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) (a₀ a : α) (hA : 0 < P.pr A) :
    (restrictOr6 P A a₀).w a = (if A a then P.w a else 0) / P.pr A := by
  have hsum : (∑ x, max 0 (if A x then P.w x else 0)) = P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases ha : A x
    · simp [ha, max_eq_right (P.nonneg x)]
    · simp [ha]
  unfold restrictOr6 normalize6
  rw [dif_pos (by simpa [hsum] using hA)]
  change max 0 (if A a then P.w a else 0) /
      (∑ x, max 0 (if A x then P.w x else 0)) = _
  rw [hsum]
  by_cases ha : A a
  · simp [ha, max_eq_right (P.nonneg a)]
  · simp [ha]

theorem restricted_weight_le_div6 {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) (a₀ a : α) (hA : 0 < P.pr A) :
    (restrictOr6 P A a₀).w a ≤ P.w a / P.pr A := by
  rw [restricted_weight_formula6 P A a₀ a hA]
  by_cases ha : A a
  · simp [ha]
  · simp [ha]
    exact div_nonneg (P.nonneg a) hA.le

theorem mass_ge_from_average6 {α : Type*} [Fintype α] (P : FinProb α)
    (f : α → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (havg : 2 * c ≤ ∑ a, P.w a * f a)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    c ≤ ∑ a, if c ≤ f a then P.w a else 0 := by
  let good : α → ℝ := fun a => if c ≤ f a then P.w a else 0
  let bad : α → ℝ := fun a => if c ≤ f a then 0 else P.w a
  have hsplit : (∑ a, good a) + ∑ a, bad a = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ a, (good a + bad a)) = ∑ a, P.w a := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : c ≤ f a <;> simp [good, bad, h]
      _ = 1 := P.sum_eq_one
  have hbad : 0 ≤ ∑ a, bad a := Finset.sum_nonneg fun a ha => by
    simp only [bad]
    split_ifs <;> [exact le_rfl; exact P.nonneg a]
  have hgood : 0 ≤ ∑ a, good a := Finset.sum_nonneg fun a ha => by
    simp only [good]
    split_ifs <;> [exact P.nonneg a; exact le_rfl]
  have hbad_le : ∑ a, bad a ≤ 1 := by linarith
  have hpoint : ∀ a, P.w a * f a ≤ good a + c * bad a := by
    intro a
    by_cases h : c ≤ f a
    · simp [good, bad, h]
      exact mul_le_of_le_one_right (P.nonneg a) (hf1 a)
    · have hfa : f a ≤ c := le_of_not_ge h
      simp [good, bad, h]
      calc
        P.w a * f a ≤ P.w a * c := mul_le_mul_of_nonneg_left hfa (P.nonneg a)
        _ = c * P.w a := by ring
  have havg' : (∑ a, P.w a * f a) ≤ (∑ a, good a) + c * ∑ a, bad a := by
    calc
      (∑ a, P.w a * f a) ≤ ∑ a, (good a + c * bad a) := Finset.sum_le_sum fun a ha => hpoint a
      _ = (∑ a, good a) + c * ∑ a, bad a := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have : 2 * c ≤ (∑ a, good a) + c := by
    calc
      2 * c ≤ ∑ a, P.w a * f a := havg
      _ ≤ (∑ a, good a) + c * ∑ a, bad a := havg'
      _ ≤ (∑ a, good a) + c := by nlinarith [mul_le_mul_of_nonneg_left hbad_le hc]
  have hfinal : c ≤ ∑ a, good a := by linarith
  simpa [good] using hfinal

theorem colDeg_mix6 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (ρ : FinProb ι) (μ : ι → Law N) (y : Fin N) :
    colDeg E G (Law.mix ρ μ) y = ∑ i, ρ.w i * colDeg E G (μ i) y := by
  classical
  simp only [colDeg, Law.mix]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem colDeg_nonneg6 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : 0 ≤ colDeg E G μ y := by
  unfold colDeg
  apply Finset.sum_nonneg
  intro x hx
  by_cases h : Hits E G x y
  · simp [h]
    exact μ.nonneg x
  · simp [h]

theorem colDeg_le_one6 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : colDeg E G μ y ≤ 1 := by
  unfold colDeg
  calc
    (∑ x, μ.w x * (if Hits E G x y then 1 else 0)) ≤ ∑ x, μ.w x := by
      apply Finset.sum_le_sum
      intro x hx
      split_ifs <;> simp [μ.nonneg x]
    _ = 1 := μ.sum_eq_one

theorem restricted_tag_bound6 {n N : ℕ} (M : TagMix N)
    (y : Fin N) (z : M.ι) (fallback : M.ι) (A : M.ι → Prop)
    (hgood : c₁ ≤ (tagPosterior6 M y).pr A)
    (hcap : ∀ i, (tagPosterior6 M y).w i ≤ (n : ℝ) ^ (2 * Dstar₆) * M.Λ i)
    (hn1 : 1 ≤ (n : ℝ))
    (hn : (n : ℝ) ^ (d₀ - 2 * Dstar₆) ≥ 1 / c₁) :
    (restrictOr6 (tagPosterior6 M y) A fallback).w z ≤ (n : ℝ) ^ d₀ * M.Λ z := by
  have hc : 0 < c₁ := by norm_num [c₁, c₀]
  have hpos : 0 < (tagPosterior6 M y).pr A := lt_of_lt_of_le hc hgood
  have hdiv := restricted_weight_le_div6 (tagPosterior6 M y) A fallback z hpos
  have hnum : (tagPosterior6 M y).w z ≤ (n : ℝ) ^ (2 * Dstar₆) * M.Λ z := hcap z
  have hratio : (n : ℝ) ^ (2 * Dstar₆) * (1 / c₁) ≤ (n : ℝ) ^ d₀ := by
    have hN : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have he : d₀ = 2 * Dstar₆ + (d₀ - 2 * Dstar₆) := by ring
    rw [he, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hΛ : 0 ≤ M.Λ z := M.Λ_nonneg z
  have hstep : (tagPosterior6 M y).w z / (tagPosterior6 M y).pr A ≤
      ((n : ℝ) ^ (2 * Dstar₆) * M.Λ z) / c₁ := by
    calc
      (tagPosterior6 M y).w z / (tagPosterior6 M y).pr A ≤
          ((n : ℝ) ^ (2 * Dstar₆) * M.Λ z) / (tagPosterior6 M y).pr A :=
            div_le_div_of_nonneg_right hnum hpos.le
      _ ≤ ((n : ℝ) ^ (2 * Dstar₆) * M.Λ z) / c₁ :=
            div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hΛ) hc hgood
  have hden : ((n : ℝ) ^ (2 * Dstar₆) * M.Λ z) / c₁ ≤
      (n : ℝ) ^ d₀ * M.Λ z := by
    rw [div_eq_mul_inv]
    calc
      (n : ℝ) ^ (2 * Dstar₆) * M.Λ z * c₁⁻¹ =
          (((n : ℝ) ^ (2 * Dstar₆) * (1 / c₁)) * M.Λ z) := by ring
      _ ≤ (n : ℝ) ^ d₀ * M.Λ z := mul_le_mul_of_nonneg_right hratio hΛ
  exact hdiv.trans (hstep.trans hden)

theorem normalize6_weight_formula {α : Type*} [Fintype α]
    (f : α → ℝ) (ω₀ a : α) (hf : ∀ x, 0 ≤ f x) (hm : 0 < ∑ x, f x) :
    (normalize6 f ω₀).w a = f a / ∑ x, f x := by
  have hsum : (∑ x, max 0 (f x)) = ∑ x, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact max_eq_right (hf x)
  unfold normalize6
  rw [dif_pos (by simpa [hsum] using hm)]
  change max 0 (f a) / (∑ x, max 0 (f x)) = f a / ∑ x, f x
  rw [hsum, max_eq_right (hf a)]

theorem safeRatio6_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ safeRatio6 a b := by
  unfold safeRatio6
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg ha hb

theorem safeRatio6_le_of_le_mul {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hab : a ≤ C * b) : safeRatio6 a b ≤ C := by
  unfold safeRatio6
  by_cases hz : b = 0
  · simp [hz, hC]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hz)
    rw [if_neg hz]
    apply (div_le_iff₀ hbpos).2
    simpa [mul_comm] using hab

theorem prod_le_const_pow_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf0 : ∀ a ∈ s, 0 ≤ f a) (hfC : ∀ a ∈ s, f a ≤ C) :
    ∏ a ∈ s, f a ≤ C ^ s.card := by
  calc
    ∏ a ∈ s, f a ≤ ∏ a ∈ s, C := Finset.prod_le_prod₀ hf0 hfC
    _ = C ^ s.card := by simp

theorem lowObservations_card_le {W : Type*} [Fintype W] {m : ℕ}
    (binAdjacent : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m)
    (F : Finset (Fin m)) :
    (lowObservations6 binAdjacent h t F).card ≤
      (keyNeighborhood6 binAdjacent h).card + F.card := by
  classical
  unfold lowObservations6
  calc
    _ ≤ ((keyNeighborhood6 binAdjacent h).image (fun s => (s, t))).card +
          (F.image (fun a => (h, Function.update t a (!t a)))).card := Finset.card_union_le _ _
    _ ≤ (keyNeighborhood6 binAdjacent h).card + F.card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le

theorem parent_heavy_related_of_local_support
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (h : X.Key) (b : X.Base)
    (hinit : 0 < X.initLaw.w b.1)
    (hcand : 0 < (X.candLaw b.1).w (b.2.1 h.1)) :
    (X.parOf b).val (primaryName6 h) ∈ X.par.heavy ∧
      related6 E G M ((X.parOf b).val (primaryName6 h)) ((X.parOf b).val (otherPrimaryName6 h)) := by
  let pv := X.parOf b
  have hs₀mass : 0 < X.par.piPrime.pr (fun y => y ∈ X.par.S₀) := by
    linarith [X.par.S₀_mass]
  have hinitSupp : b.1 ∈ X.par.S₀ ∧ X.par.piPrime.w b.1 ≠ 0 :=
    restrictOr6_supp hs₀mass (by simpa only [Ctx6.initLaw] using (ne_of_gt hinit))
  have hrelMass : 0 < X.par.piPrime.pr (fun y => related6 E G M b.1 y) := by
    linarith [X.par.partner_mass b.1 hinitSupp.1]
  have hcandSupp : related6 E G M b.1 (b.2.1 h.1) ∧
      X.par.piPrime.w (b.2.1 h.1) ≠ 0 := by
    have hcandne : (partnerLaw6 X.par.piPrime (related6 E G M) b.1 X.y₀).w
        (b.2.1 h.1) ≠ 0 := by simpa only [Ctx6.candLaw] using (ne_of_gt hcand)
    exact restrictOr6_supp hrelMass hcandne
  have hheavyPrime : ∀ y, X.par.piPrime.w y ≠ 0 → y ∈ X.par.heavy := by
    intro y hy
    have heq := X.par.piPrime_eq y
    by_contra hnot
    rw [if_neg hnot] at heq
    simp [heq] at hy
  cases hflag : h.2 with
  | interior =>
      have hheavy := hheavyPrime _ hcandSupp.2
      rcases hcandSupp.1 with ⟨hrel₁, hrel₂⟩
      have hrel : related6 E G M (b.2.1 h.1) b.1 := ⟨hrel₂, hrel₁⟩
      simpa [primaryName6, otherPrimaryName6, hflag, Par6.val, pv] using ⟨hheavy, hrel⟩
  | boundary =>
      have hheavy := hheavyPrime _ hinitSupp.2
      have hrel := hcandSupp.1
      simpa [primaryName6, otherPrimaryName6, hflag, Par6.val, pv] using ⟨hheavy, hrel⟩

theorem occType_obs_card_le {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty)
    (hβ : β ∈ X.occTypes) : β.obs.card ≤ 602 * β.u := by
  unfold Ctx6.occTypes at hβ
  rcases Finset.mem_image.mp hβ with ⟨x, hx, htype⟩
  have htype' : β = X.evenType x := htype.symm
  subst β
  let L := X.g.L
  by_cases hlow : L.severity x ≤ X.J
  · have hFsub : L.flippable x ⊆ Finset.univ.filter
        (fun i : Fin L.m => Nat.dist (2 * L.fineCount x i) L.fineLength ≤ 11) := by
      intro i hi
      have hi' : Nat.dist (2 * L.fineCount x i) L.fineLength = 1 := by
        simpa [ChunkLayout6.flippable] using hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hFcard : (L.flippable x).card ≤ L.severity x := by
      unfold ChunkLayout6.severity
      exact Finset.card_le_card hFsub
    have hObs : (X.evenType x).obs =
        lowObservations6 binAdjacent6 (L.key x) (L.sign x) (L.flippable x) := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs]
    have hcard : (X.evenType x).obs.card ≤ 602 + L.severity x := by
      rw [hObs]
      exact (lowObservations_card_le binAdjacent6 (L.key x) (L.sign x) (L.flippable x)).trans
        (Nat.add_le_add (X.g.flips.key_neighborhood_card (L.key x)) hFcard)
    have hsevM : L.severity x ≤ L.m := by
      unfold ChunkLayout6.severity
      exact (Finset.card_le_univ _).trans_eq (by simp)
    have hu : (X.evenType x).u = L.severity x + 1 := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.u, Type6.sev, sevFin6,
        Type6.mode, modeOf6, Nat.min_eq_left hsevM]
    rw [hu]
    omega
  · have hhigh : L.severity x > X.J := lt_of_not_ge hlow
    have hobs : ((X.evenType x).obs).card ≤ 1 := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs, highObservations6]
      split_ifs <;> simp
    have hu : (X.evenType x).u = 1 := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.u, Type6.mode, modeOf6]
    rw [hu]
    omega

end HypercubeRamsey.S06
