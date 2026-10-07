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

theorem pr_forall_lower6 {Ω Name : Type*} [Fintype Ω] [DecidableEq Name]
    (P : FinProb Ω) (S : Finset Name) (Hit : Name → Ω → Prop) (e : Name)
    (c ε : ℝ) (hε : 0 ≤ ε) (he : e ∈ S) (hc : c ≤ P.pr (Hit e))
    (hmiss : ∀ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω) ≤ ε) :
    c - (S.card : ℝ) * ε ≤ P.pr (fun ω => ∀ a ∈ S, Hit a ω) := by
  classical
  let All : Ω → Prop := fun ω => ∀ a ∈ S, Hit a ω
  have hbad_nonneg (ω : Ω) :
      0 ≤ ∑ a ∈ S.erase e, if ¬ Hit a ω then P.w ω else 0 := by
    apply Finset.sum_nonneg
    intro a ha
    by_cases h : ¬ Hit a ω
    · rw [if_pos h]
      exact P.nonneg ω
    · have hh : Hit a ω := not_not.mp h
      simp [hh]
  have hbad_of_missing (ω : Ω) (a : Name) (ha : a ∈ S.erase e) (hnot : ¬ Hit a ω) :
      P.w ω ≤ ∑ b ∈ S.erase e, if ¬ Hit b ω then P.w ω else 0 := by
    have hs : (if ¬ Hit a ω then P.w ω else 0) ≤
        ∑ b ∈ S.erase e, if ¬ Hit b ω then P.w ω else 0 := Finset.single_le_sum
      (s := S.erase e) (f := fun b => if ¬ Hit b ω then P.w ω else 0)
      (fun b hb => by
        by_cases h : ¬ Hit b ω
        · rw [if_pos h]
          exact P.nonneg ω
        · have hh : Hit b ω := not_not.mp h
          simp [hh]) ha
    simpa [hnot] using hs
  have hmissing (ω : Ω) (hnotAll : ¬ All ω) (heHit : Hit e ω) :
      ∃ a ∈ S.erase e, ¬ Hit a ω := by
    change ¬ (∀ a ∈ S, Hit a ω) at hnotAll
    push_neg at hnotAll
    rcases hnotAll with ⟨a, ha, hnot⟩
    have hae : a ≠ e := by
      intro hEq
      subst a
      exact hnot heHit
    exact ⟨a, Finset.mem_erase.mpr ⟨hae, ha⟩, hnot⟩
  have hpoint (ω : Ω) :
      (if All ω then P.w ω else 0) +
          (∑ a ∈ S.erase e, if ¬ Hit a ω then P.w ω else 0) ≥
        (if Hit e ω then P.w ω else 0) := by
    by_cases heHit : Hit e ω
    · by_cases hAll : All ω
      · rw [if_pos hAll, if_pos heHit]
        exact le_add_of_nonneg_right (hbad_nonneg ω)
      · obtain ⟨a, ha, hnot⟩ := hmissing ω hAll heHit
        have hs := hbad_of_missing ω a ha hnot
        rw [if_neg hAll, if_pos heHit]
        simpa using hs
    · have hfirst : 0 ≤ if All ω then P.w ω else 0 := by
        by_cases hAll : All ω
        · simp [hAll]
          exact P.nonneg ω
        · simp [hAll]
      rw [if_neg heHit]
      exact add_nonneg hfirst (hbad_nonneg ω)
  have hbadSum :
      (∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω)) =
        ∑ ω, ∑ a ∈ S.erase e, if ¬ Hit a ω then P.w ω else 0 := by
    unfold FinProb.pr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : ¬ Hit a ω <;> simp [h]
  have hprob : P.pr (Hit e) ≤ P.pr All +
      ∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω) := by
    unfold FinProb.pr
    calc
      (∑ ω, if Hit e ω then P.w ω else 0) ≤
          ∑ ω, ((if All ω then P.w ω else 0) +
            ∑ a ∈ S.erase e, if ¬ Hit a ω then P.w ω else 0) :=
        Finset.sum_le_sum fun ω hω => hpoint ω
      _ = P.pr All + ∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω) := by
        rw [Finset.sum_add_distrib, ← hbadSum]
        simp [FinProb.pr]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hAll : All ω <;> simp [hAll]
  have hmissSum :
      (∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω)) ≤
        ((S.erase e).card : ℝ) * ε := by
    calc
      (∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω)) ≤
          ∑ a ∈ S.erase e, ε := Finset.sum_le_sum fun a ha => hmiss a ha
      _ = ((S.erase e).card : ℝ) * ε := by simp
  have hcardN : (S.erase e).card ≤ S.card := Finset.card_erase_le
  have hcard : ((S.erase e).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcardN
  have hlast : c ≤ P.pr All + (S.card : ℝ) * ε := by
    calc
      c ≤ P.pr (Hit e) := hc
      _ ≤ P.pr All + ∑ a ∈ S.erase e, P.pr (fun ω => ¬ Hit a ω) := hprob
      _ ≤ P.pr All + ((S.erase e).card : ℝ) * ε := by linarith
      _ ≤ P.pr All + (S.card : ℝ) * ε := by nlinarith [hcard, hε]
  linarith

theorem baseTag_accept_mass6 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N)
    (y z : Fin N) (havg : c₀ ≤ colDeg E G (broadLaw6 M y) z) :
    c₁ ≤ (tagPosterior6 M y).pr (fun i => c₁ ≤ colDeg E G (M.μ i) z) := by
  let P := tagPosterior6 M y
  let f : M.ι → ℝ := fun i => colDeg E G (M.μ i) z
  have hc : 0 ≤ c₁ := by norm_num [c₁, c₀]
  have htwoc : 2 * c₁ = c₀ := by norm_num [c₁, c₀]
  have hmix : c₀ ≤ ∑ i, P.w i * f i := by
    calc
      c₀ ≤ colDeg E G (broadLaw6 M y) z := havg
      _ = ∑ i, P.w i * f i := by
        simpa [P, f, broadLaw6] using colDeg_mix6 E G (tagPosterior6 M y) M.μ z
  have hmass : c₁ ≤ ∑ i, if c₁ ≤ f i then P.w i else 0 :=
    mass_ge_from_average6 P f c₁ hc
      (by rw [htwoc]; exact hmix)
      (fun i => colDeg_nonneg6 E G (M.μ i) z)
      (fun i => colDeg_le_one6 E G (M.μ i) z)
  simpa [FinProb.pr, P, f] using hmass

theorem normalize6_pos_atom_implies_weight_pos {α : Type*} [Fintype α]
    (f : α → ℝ) (ω₀ x : α) (hf : ∀ y, 0 ≤ f y)
    (hex : ∃ y, 0 < f y) (hpos : 0 < (normalize6 f ω₀).w x) : 0 < f x := by
  obtain ⟨y, hy⟩ := hex
  have hsum : 0 < ∑ y, f y := by
    have hle : f y ≤ ∑ z, f z :=
      Finset.single_le_sum (fun z hz => hf z) (Finset.mem_univ y)
    linarith
  have hformula := normalize6_weight_formula f ω₀ x hf hsum
  rw [hformula] at hpos
  exact (div_pos_iff_of_pos_right hsum).1 hpos

theorem binAdjacent6_symm {n : ℕ} {u w : BinVector6 n}
    (h : binAdjacent6 u w) : binAdjacent6 w u := by
  rcases h with ⟨i, hEq, hdist⟩
  refine ⟨i, ?_, ?_⟩
  · intro j hji
    exact (hEq j hji).symm
  · simpa [Nat.dist_comm] using hdist

theorem keyAdjacent6_symm {n : ℕ} {a b : CoarseKey6 (BinVector6 n)}
    (h : keyAdjacent6 binAdjacent6 a b) : keyAdjacent6 binAdjacent6 b a := by
  unfold keyAdjacent6 at h ⊢
  rcases h with hab | hab | ⟨ha, hb, hadj⟩
  · exact Or.inl hab.symm
  · exact Or.inr (Or.inl hab.symm)
  · exact Or.inr (Or.inr ⟨hb, ha, binAdjacent6_symm hadj⟩)

theorem occObs_key_mem_C {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty)
    (hβ : β ∈ X.occTypes) (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) : β.key ∈ X.C ℓ.1 := by
  unfold Ctx6.occTypes at hβ
  rcases Finset.mem_image.mp hβ with ⟨x, hx, htype⟩
  have htype' : β = X.evenType x := htype.symm
  subst β
  let L := X.g.L
  have hevenKey : (X.evenType x).key = L.key x := by
    simp only [Ctx6.evenType, Type6.key, makeType6]
    split_ifs <;> rfl
  by_cases hlow : L.severity x ≤ X.J
  · letI : DecidableEq X.Bin := Classical.decEq _
    letI : DecidableEq X.Key := instDecidableEqProd
    letI : DecidableEq X.HKey := instDecidableEqProd
    have hObs : (X.evenType x).obs =
        lowObservations6 binAdjacent6 (L.key x) (L.sign x) (L.flippable x) := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs]
    rw [hObs] at hℓ
    unfold lowObservations6 at hℓ
    rcases Finset.mem_union.mp hℓ with hNbr | hFlip
    · rcases Finset.mem_image.mp hNbr with ⟨s, hs, hEq⟩
      cases hEq
      have hsC : s ∈ X.C (L.key x) := by simpa [Ctx6.C] using hs
      have hrel : keyAdjacent6 binAdjacent6 (L.key x) s :=
        (Finset.mem_filter.mp hsC).2
      have hrel' : keyAdjacent6 binAdjacent6 s (L.key x) := keyAdjacent6_symm hrel
      have hsC' : L.key x ∈ X.C s := by
        change L.key x ∈ Finset.univ.filter (keyAdjacent6 binAdjacent6 s)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel'⟩
      rw [hevenKey]
      exact hsC'
    · rcases Finset.mem_image.mp hFlip with ⟨a, ha, hEq⟩
      cases hEq
      rw [hevenKey]
      simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  · letI : DecidableEq X.Bin := Classical.decEq _
    letI : DecidableEq X.Key := instDecidableEqProd
    letI : DecidableEq X.HKey := instDecidableEqProd
    have hObs : (X.evenType x).obs =
        highObservations6 (L.key x) (L.sign x) (L.severity x) X.J := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs]
    rw [hObs] at hℓ
    by_cases hsev : L.severity x = X.J + 1
    · simp [highObservations6, hsev] at hℓ
      cases hℓ
      rw [hevenKey]
      simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
    · simp [highObservations6, hsev] at hℓ

namespace Lane_q_s06_steps1

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

theorem normalize6_pos_weight_of_pos_mass {α : Type*} [Fintype α]
    (f : α → ℝ) (ω₀ x : α) (hf : ∀ y, 0 ≤ f y)
    (hsum : 0 < ∑ y, f y) (hpos : 0 < (normalize6 f ω₀).w x) : 0 < f x := by
  rw [normalize6_weight_formula f ω₀ x hf hsum] at hpos
  exact (div_pos_iff_of_pos_right hsum).1 hpos

theorem safeRatio6_pos_num {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : 0 < safeRatio6 a b) : 0 < a := by
  unfold safeRatio6 at h
  split_ifs at h with hz
  · norm_num at h
  · have hmul : 0 < a := (div_pos_iff_of_pos_right (lt_of_le_of_ne hb (Ne.symm hz))).1 h
    exact hmul

theorem hidWeight_nonneg {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (h : X.Key) (obs : Finset X.Key) (y : Fin N) :
    0 ≤ X.hidWeight b h obs y := by
  cases hflag : h.2
  · simp only [Ctx6.hidWeight, hflag]
    apply mul_nonneg
    · exact (X.candLaw b.1).nonneg y
    · apply Finset.prod_nonneg
      intro s hs
      exact (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).nonneg (b.2.2 s)
  · simp only [Ctx6.hidWeight, hflag]
    apply mul_nonneg
    · apply mul_nonneg
      · exact X.initLaw.nonneg y
      · apply Finset.prod_nonneg
        intro u hu
        exact (X.candLaw y).nonneg (b.2.1 u)
    · apply Finset.prod_nonneg
      intro s hs
      exact (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).nonneg (b.2.2 s)

theorem hidWeight_pos_tagFactor {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (h : X.Key) (obs : Finset X.Key) (y : Fin N)
    (s : X.Key) (hs : s ∈ obs) (hw : 0 < X.hidWeight b h obs y) :
    0 < (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w (b.2.2 s) := by
  unfold Ctx6.hidWeight at hw
  dsimp at hw
  have hfactor_ne : (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w (b.2.2 s) ≠ 0 := by
    intro hz
    have hzprod : (∏ t ∈ obs,
        (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) t).w (b.2.2 t)) = 0 :=
      Finset.prod_eq_zero hs hz
    rw [hzprod] at hw
    simp [hzprod] at hw
  exact lt_of_le_of_ne
    ((X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).nonneg (b.2.2 s))
    (Ne.symm hfactor_ne)

theorem baseTag_pos_accept_of_average {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (pv : Par6 X.Bin N) (h : X.Key) (havg : c₀ ≤
      colDeg E G (broadLaw6 M (pv.val (primaryName6 h))) (pv.val (otherPrimaryName6 h)))
    (i : X.ι) (hi : 0 < (X.tagLawAt pv h).w i) :
    c₁ ≤ colDeg E G (M.μ i) (pv.val (otherPrimaryName6 h)) ∧
      0 < (tagPosterior6 M (pv.val (primaryName6 h))).w i := by
  have hmass := baseTag_accept_mass6 (N := N) (ι := X.ι) E G M (pv.val (primaryName6 h))
      (pv.val (otherPrimaryName6 h)) havg
  have hposMass : 0 < (tagPosterior6 M (pv.val (primaryName6 h))).pr
      (fun j => c₁ ≤ colDeg E G (M.μ j) (pv.val (otherPrimaryName6 h))) := by
    have hc : 0 < c₁ := by norm_num [c₁, c₀]
    linarith
  have hsupp := restrictOr6_supp hposMass (ne_of_gt hi)
  have heta : 0 < (tagPosterior6 M (pv.val (primaryName6 h))).w i :=
    lt_of_le_of_ne ((tagPosterior6 M (pv.val (primaryName6 h))).nonneg i) (Ne.symm hsupp.2)
  exact ⟨hsupp.1, heta⟩

theorem tagPosterior_pos_nu_of_positive_mixture {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (y : Fin N) (i : X.ι)
    (hmix : 0 < (secondMixture6 M).w y)
    (hi : 0 < (tagPosterior6 M y).w i) : 0 < (M.ν i).w y := by
  have hformula : (tagPosterior6 M y).w i = M.Λ i * (M.ν i).w y / (secondMixture6 M).w y := by
    simp [tagPosterior6, hmix]
  rw [hformula] at hi
  have hprod : 0 < M.Λ i * (M.ν i).w y := (div_pos_iff_of_pos_right hmix).1 hi
  have hνne : (M.ν i).w y ≠ 0 := by
    intro hz
    simp [hz] at hprod
  exact lt_of_le_of_ne ((M.ν i).nonneg y) (Ne.symm hνne)

theorem posterior_heavy_pos_mixture {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (hn : 1 ≤ n) (y : Fin N) (hy : y ∈ X.par.heavy) :
    0 < (secondMixture6 M).w y := by
  have hmem : y ∈ heavySet6 (n := n) Dstar₆ (secondMixture6 M) := by
    rw [← X.par.heavy_eq]
    exact hy
  have hbound : (n : ℝ) ^ (-Dstar₆) ≤ (N : ℝ) * (secondMixture6 M).w y := by
    simpa [heavySet6] using (Finset.mem_filter.mp hmem).2
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hpow : 0 < (n : ℝ) ^ (-Dstar₆) := Real.rpow_pos_of_pos hnpos _
  have hprod : 0 < (N : ℝ) * (secondMixture6 M).w y := lt_of_lt_of_le hpow hbound
  have hN : 0 < (N : ℝ) := by
    by_contra hN
    have : (N : ℝ) = 0 := le_antisymm (le_of_not_gt hN) (Nat.cast_nonneg _)
    simp [this] at hprod
  have hmixNe : (secondMixture6 M).w y ≠ 0 := by
    intro hz
    simp [hz] at hprod
  exact lt_of_le_of_ne ((secondMixture6 M).nonneg y) (Ne.symm hmixNe)

end Lane_q_s06_steps1

end HypercubeRamsey.S06
