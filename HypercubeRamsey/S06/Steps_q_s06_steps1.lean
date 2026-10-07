import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S06.Prob

namespace HypercubeRamsey.S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

def matchesPrimaryName6 {W : Type*} {m : ℕ} (β : Type6 W m) : VarName6 W m → Prop
  | .par p => p = primaryName6 β.key
  | .hid ℓ => primaryName6 ℓ.1 = primaryName6 β.key

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

def oppositeKeyFlag6 : KeyFlag6 → KeyFlag6
  | .interior => .boundary
  | .boundary => .interior

noncomputable def posteriorTypeKeys6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty) : Finset X.Key :=
  insert β.key (β.obs.biUnion fun ℓ => X.C ℓ.1)

theorem keyAdjacent_primary_mismatch_eq_opposite {W : Type*} {binAdjacent : W → W → Prop}
    (h s : CoarseKey6 W) (hadj : keyAdjacent6 binAdjacent h s)
    (hneq : primaryName6 s ≠ primaryName6 h) :
    s = (h.1, oppositeKeyFlag6 h.2) := by
  cases hh : h.2 <;> cases hs : s.2
  · rcases hadj with heq | hbin | hthird
    · have heqName : primaryName6 s = primaryName6 h := by rw [heq]
      exact (hneq heqName).elim
    · have heqName : primaryName6 s = primaryName6 h := by simp [primaryName6, hh, hs, hbin]
      exact (hneq heqName).elim
    · rcases hthird with ⟨hhb, _, _⟩
      simp [hh] at hhb
  · have hbin : h.1 = s.1 := by
      rcases hadj with heq | hbin | hthird
      · have hflags := congrArg Prod.snd heq
        simp [hh, hs] at hflags
      · exact hbin
      · rcases hthird with ⟨hhb, _, _⟩
        simp [hh] at hhb
    apply Prod.ext
    · exact hbin.symm
    · simp [hh, hs, oppositeKeyFlag6]
  · have hbin : h.1 = s.1 := by
      rcases hadj with heq | hbin | hthird
      · have hflags := congrArg Prod.snd heq
        simp [hh, hs] at hflags
      · exact hbin
      · rcases hthird with ⟨_, hsb, _⟩
        simp [hs] at hsb
    apply Prod.ext
    · exact hbin.symm
    · simp [hh, hs, oppositeKeyFlag6]
  · simp [primaryName6, hh, hs] at hneq

theorem neighbor_primary_eq_or_other {W : Type*} {binAdjacent : W → W → Prop}
    (source target : CoarseKey6 W) (hadj : keyAdjacent6 binAdjacent source target) :
    primaryName6 source = primaryName6 target ∨
      primaryName6 source = otherPrimaryName6 target := by
  cases hs : source.2 <;> cases ht : target.2
  · have hbin : source.1 = target.1 := by
      rcases hadj with heq | hbin | hthird
      · exact congrArg Prod.fst heq
      · exact hbin
      · rcases hthird with ⟨hbound, _, _⟩
        simp [hs] at hbound
    exact Or.inl (by simp [primaryName6, hs, ht, hbin])
  · have hbin : source.1 = target.1 := by
      rcases hadj with heq | hbin | hthird
      · have hflags := congrArg Prod.snd heq
        simp [hs, ht] at hflags
      · exact hbin
      · rcases hthird with ⟨hbound, _, _⟩
        simp [hs] at hbound
    exact Or.inr (by simp [primaryName6, otherPrimaryName6, hs, ht, hbin])
  · have hbin : source.1 = target.1 := by
      rcases hadj with heq | hbin | hthird
      · have hflags := congrArg Prod.snd heq
        simp [hs, ht] at hflags
      · exact hbin
      · rcases hthird with ⟨_, hbound, _⟩
        simp [ht] at hbound
    exact Or.inr (by simp [primaryName6, otherPrimaryName6, hs, ht, hbin])
  · exact Or.inl (by simp [primaryName6, hs, ht])

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

theorem hidWeight_pos_localPrior {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (h : X.Key) (z : Fin N) (hw : 0 < X.hidWeight b h (X.C h) z) :
    (h.2 = .interior → 0 < (X.candLaw b.1).w z) ∧
      (h.2 = .boundary → 0 < X.initLaw.w z ∧ 0 < (X.candLaw z).w (b.2.1 h.1)) := by
  cases hflag : h.2
  · have hcand : 0 < (X.candLaw b.1).w z := by
      by_contra hnot
      have hz : (X.candLaw b.1).w z = 0 := le_antisymm (le_of_not_gt hnot) ((X.candLaw b.1).nonneg z)
      simp [Ctx6.hidWeight, hflag, hz] at hw
    constructor
    · intro _
      exact hcand
    · intro hb
      simp [hflag] at hb
  · have hinit : 0 < X.initLaw.w z := by
      by_contra hnot
      have hz : X.initLaw.w z = 0 := le_antisymm (le_of_not_gt hnot) (X.initLaw.nonneg z)
      simp [Ctx6.hidWeight, hflag, hz] at hw
    have hself : h ∈ X.C h := by simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
    have hbin : h.1 ∈ X.binsOf (X.C h) := by
      exact Finset.mem_image.mpr ⟨h, hself, rfl⟩
    have hcand : 0 < (X.candLaw z).w (b.2.1 h.1) := by
      by_contra hnot
      have hz : (X.candLaw z).w (b.2.1 h.1) = 0 :=
        le_antisymm (le_of_not_gt hnot) ((X.candLaw z).nonneg (b.2.1 h.1))
      have hprod : (∏ u ∈ X.binsOf (X.C h), (X.candLaw z).w (b.2.1 u)) = 0 :=
        Finset.prod_eq_zero hbin hz
      simp [Ctx6.hidWeight, hflag, hprod] at hw
    constructor
    · intro hi
      simp [hflag] at hi
    · intro _
      exact ⟨hinit, hcand⟩

theorem hidWeight_parent_heavy_related {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (h : X.Key) (z : Fin N) (hinit : 0 < X.initLaw.w b.1)
    (hw : 0 < X.hidWeight b h (X.C h) z) :
    let pv := (X.parOf b).set (primaryName6 h) z
    pv.val (primaryName6 h) ∈ X.par.heavy ∧
      related6 E G M (pv.val (primaryName6 h)) (pv.val (otherPrimaryName6 h)) := by
  cases hflag : h.2
  · have hprior := hidWeight_pos_localPrior X b h z hw
    have hcand0 : 0 < (X.candLaw b.1).w z := hprior.1 hflag
    let b' : X.Base := (b.1, Function.update b.2.1 h.1 z, b.2.2)
    have hcand : 0 < (X.candLaw b'.1).w (b'.2.1 h.1) := by simpa [b'] using hcand0
    have hrel := parent_heavy_related_of_local_support X h b' hinit hcand
    simpa [b', Ctx6.parOf, hflag, primaryName6, otherPrimaryName6, Par6.set, Function.update] using hrel
  · have hprior := hidWeight_pos_localPrior X b h z hw
    have hboundary := hprior.2 hflag
    have hzinit : 0 < X.initLaw.w z := hboundary.1
    have hzcand : 0 < (X.candLaw z).w (b.2.1 h.1) := hboundary.2
    let b' : X.Base := (z, b.2.1, b.2.2)
    have hrel := parent_heavy_related_of_local_support X h b' hzinit hzcand
    simpa [b', Ctx6.parOf, hflag, primaryName6, otherPrimaryName6, Par6.set] using hrel

theorem hidWeight_pos_boundary_candidate {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (h : X.Key) (z : Fin N)
    (hw : 0 < X.hidWeight b h (X.C h) z) (hflag : h.2 = .boundary)
    (u : X.Bin) (hu : u ∈ X.binsOf (X.C h)) : 0 < (X.candLaw z).w (b.2.1 u) := by
  have hne : (X.candLaw z).w (b.2.1 u) ≠ 0 := by
    intro hz
    have hprod : (∏ v ∈ X.binsOf (X.C h), (X.candLaw z).w (b.2.1 v)) = 0 :=
      Finset.prod_eq_zero hu hz
    simp [Ctx6.hidWeight, hflag, hprod] at hw
  exact lt_of_le_of_ne ((X.candLaw z).nonneg (b.2.1 u)) (Ne.symm hne)

theorem hidWeight_parent_related_at_neighbor {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (target source : X.Key) (z : Fin N)
    (hinit : 0 < X.initLaw.w b.1)
    (hw : 0 < X.hidWeight b source (X.C source) z)
    (hts : target ∈ X.C source) :
    let pv := (X.parOf b).set (primaryName6 source) z
    pv.val (primaryName6 target) ∈ X.par.heavy ∧
      related6 E G M (pv.val (primaryName6 target)) (pv.val (otherPrimaryName6 target)) := by
  have hadj : keyAdjacent6 binAdjacent6 source target := by
    change target ∈ Finset.univ.filter (keyAdjacent6 binAdjacent6 source) at hts
    exact (Finset.mem_filter.mp hts).2
  cases hsource : source.2
  · have hprior := hidWeight_pos_localPrior X b source z hw
    have hpriorCand : 0 < (X.candLaw b.1).w z := hprior.1 hsource
    have hbin : source.1 = target.1 := by
      rcases hadj with heq | hEq | hthird
      · exact congrArg Prod.fst heq
      · exact hEq
      · rcases hthird with ⟨hbound, _, _⟩
        simp [hsource] at hbound
    let b' : X.Base := (b.1, Function.update b.2.1 target.1 z, b.2.2)
    have hcand : 0 < (X.candLaw b'.1).w (b'.2.1 target.1) := by
      simpa [b'] using hpriorCand
    have hrel := parent_heavy_related_of_local_support X target b' hinit hcand
    have hparEq : X.parOf b' = (X.parOf b).set (primaryName6 source) z := by
      cases htarget : target.2 <;>
        simp [b', Ctx6.parOf, primaryName6, Par6.set, hsource, htarget, hbin, Function.update]
    cases htarget : target.2 <;>
      exact (show
        (((X.parOf b).set (primaryName6 source) z).val (primaryName6 target) ∈ X.par.heavy) ∧
          related6 E G M (((X.parOf b).set (primaryName6 source) z).val (primaryName6 target))
            (((X.parOf b).set (primaryName6 source) z).val (otherPrimaryName6 target)) from by
        rw [← hparEq]
        simpa [Ctx6.parOf, primaryName6, otherPrimaryName6, Par6.val, htarget] using hrel)
  · have hprior := hidWeight_pos_localPrior X b source z hw
    have hpriorSource := hprior.2 hsource
    have hzinit : 0 < X.initLaw.w z := hpriorSource.1
    have htargetBin : target.1 ∈ X.binsOf (X.C source) := by
      exact Finset.mem_image.mpr ⟨target, hts, rfl⟩
    have htargetCand := hidWeight_pos_boundary_candidate X b source z hw hsource
      target.1 htargetBin
    let b' : X.Base := (z, b.2.1, b.2.2)
    have hcand : 0 < (X.candLaw b'.1).w (b'.2.1 target.1) := by simpa [b'] using htargetCand
    have hrel := parent_heavy_related_of_local_support X target b' hzinit hcand
    have hparEq : X.parOf b' = (X.parOf b).set (primaryName6 source) z := by
      cases htarget : target.2 <;>
        simp [b', Ctx6.parOf, primaryName6, Par6.set, hsource, htarget]
    cases htarget : target.2 <;>
      exact (show
        (((X.parOf b).set (primaryName6 source) z).val (primaryName6 target) ∈ X.par.heavy) ∧
          related6 E G M (((X.parOf b).set (primaryName6 source) z).val (primaryName6 target))
            (((X.parOf b).set (primaryName6 source) z).val (otherPrimaryName6 target)) from by
        rw [← hparEq]
        simpa [Ctx6.parOf, primaryName6, otherPrimaryName6, Par6.val, htarget] using hrel)

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
    (hi : 0 < (tagPosterior6 M y).w i) :
    0 < M.Λ i ∧ 0 < (M.ν i).w y := by
  have hformula : (tagPosterior6 M y).w i = M.Λ i * (M.ν i).w y / (secondMixture6 M).w y := by
    simp [tagPosterior6, hmix]
  rw [hformula] at hi
  have hprod : 0 < M.Λ i * (M.ν i).w y := (div_pos_iff_of_pos_right hmix).1 hi
  have hΛne : M.Λ i ≠ 0 := by
    intro hz
    simp [hz] at hprod
  have hνne : (M.ν i).w y ≠ 0 := by
    intro hz
    simp [hz] at hprod
  exact ⟨lt_of_le_of_ne (M.Λ_nonneg i) (Ne.symm hΛne),
    lt_of_le_of_ne ((M.ν i).nonneg y) (Ne.symm hνne)⟩

theorem hidWeight_positive_at_actual_parent {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (β : X.Ty)
    (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs)
    (hKeys : 0 < X.initLaw.w b.1 ∧
      (∀ u ∈ X.binsOf (posteriorTypeKeys6 X β), 0 < (X.candLaw b.1).w (b.2.1 u)) ∧
      ∀ s ∈ posteriorTypeKeys6 X β, 0 < (X.tagLawAt (X.parOf b) s).w (b.2.2 s))
    (hβkey : β.key ∈ X.C ℓ.1)
    (i : X.ι) (hi : 0 < (X.tagLawAt (X.parOf b) β.key).w i) :
    0 < X.hidWeight (X.withTag b β.key i) ℓ.1 (X.C ℓ.1)
      ((X.parOf b).val (primaryName6 ℓ.1)) := by
  letI : DecidableEq X.Key := X.instDecEqKey
  letI : DecidableEq X.HKey := X.instDecEqHKey
  rcases hKeys with ⟨hinit, hcands, htags⟩
  have hCsub : X.C ℓ.1 ⊆ posteriorTypeKeys6 X β := by
    intro s hs
    unfold posteriorTypeKeys6
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hs⟩)
  have hbinSub : X.binsOf (X.C ℓ.1) ⊆ X.binsOf (posteriorTypeKeys6 X β) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨s, hs, rfl⟩
    exact Finset.mem_image.mpr ⟨s, hCsub hs, rfl⟩
  have hset : (X.parOf b).set (primaryName6 ℓ.1)
      ((X.parOf b).val (primaryName6 ℓ.1)) = X.parOf b := by
    cases hflag : ℓ.1.2 <;>
      simp [Ctx6.parOf, Par6.val, primaryName6, Par6.set, hflag, Function.update_self]
  have htagprod : 0 < ∏ s ∈ X.C ℓ.1,
      (X.tagLawAt (X.parOf b) s).w ((X.withTag b β.key i).2.2 s) := by
    apply Finset.prod_pos
    intro s hs
    by_cases hsβ : s = β.key
    · subst s
      simpa [Ctx6.withTag] using hi
    · have ht := htags s (hCsub hs)
      simpa [Ctx6.withTag, hsβ] using ht
  cases hflag : ℓ.1.2
  · have hself : ℓ.1 ∈ X.C ℓ.1 := by
      simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
    have hbin : ℓ.1.1 ∈ X.binsOf (posteriorTypeKeys6 X β) := by
      apply Finset.mem_image.mpr
      exact ⟨ℓ.1, hCsub hself, rfl⟩
    have hprior : 0 < (X.candLaw b.1).w (b.2.1 ℓ.1.1) := hcands _ hbin
    have hmass : 0 < (X.candLaw b.1).w (b.2.1 ℓ.1.1) *
        ∏ s ∈ X.C ℓ.1, (X.tagLawAt (X.parOf b) s).w ((X.withTag b β.key i).2.2 s) :=
      mul_pos hprior htagprod
    simpa [Ctx6.withTag, Ctx6.hidWeight, Ctx6.parOf, Par6.val, Par6.set,
      hflag, primaryName6, hset] using hmass
  · have hpriorCand : 0 < ∏ u ∈ X.binsOf (X.C ℓ.1), (X.candLaw b.1).w (b.2.1 u) := by
      apply Finset.prod_pos
      intro u hu
      exact hcands u (hbinSub hu)
    have hprior : 0 < X.initLaw.w b.1 *
        ∏ u ∈ X.binsOf (X.C ℓ.1), (X.candLaw b.1).w (b.2.1 u) :=
      mul_pos hinit hpriorCand
    have hmass : 0 < (X.initLaw.w b.1 *
        ∏ u ∈ X.binsOf (X.C ℓ.1), (X.candLaw b.1).w (b.2.1 u)) *
        ∏ s ∈ X.C ℓ.1, (X.tagLawAt (X.parOf b) s).w ((X.withTag b β.key i).2.2 s) :=
      mul_pos hprior htagprod
    simpa [Ctx6.withTag, Ctx6.hidWeight, Ctx6.parOf, Par6.val, Par6.set,
      hflag, primaryName6, hset] using hmass

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

theorem tagWeight_pos_tagLaw {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι)
    (hw : 0 < X.tagWeight H β S i) : 0 < (X.tagLawAt (X.parOf H.1) β.key).w i := by
  have htag0 := (X.tagLawAt (X.parOf H.1) β.key).nonneg i
  have hgate : X.tagGate H.1 β i := by
    by_contra hg
    simp [Ctx6.tagWeight, hg] at hw
  have htagNe : (X.tagLawAt (X.parOf H.1) β.key).w i ≠ 0 := by
    intro hz
    simp [Ctx6.tagWeight, hgate, hz] at hw
  exact lt_of_le_of_ne htag0 (Ne.symm htagNe)

theorem tagWeight_nonneg {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι) :
    0 ≤ X.tagWeight H β S i := by
  unfold Ctx6.tagWeight
  have hgate : 0 ≤ if X.tagGate H.1 β i then (1 : ℝ) else 0 := by
    split_ifs <;> norm_num
  apply mul_nonneg
  · exact mul_nonneg ((X.tagLawAt (X.parOf H.1) β.key).nonneg i) hgate
  · apply Finset.prod_nonneg
    intro ℓ hℓ
    exact safeRatio6_nonneg ((X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ))
      ((X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ))

theorem Tβ_pos_tagWeight {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (β : X.Ty) (i : X.ι)
    (hmass : 0 < X.tagMass H β β.obs) (hi : 0 < (X.Tβ H β).w i) :
    0 < X.tagWeight H β β.obs i := by
  have hsum : 0 < ∑ j, X.tagWeight H β β.obs j := by simpa [Ctx6.tagMass] using hmass
  have hformula : (X.Tβ H β).w i =
      X.tagWeight H β β.obs i / X.tagMass H β β.obs := by
    simpa [Ctx6.Tβ, Ctx6.tagPost, Ctx6.tagMass] using
      (normalize6_weight_formula (fun j => X.tagWeight H β β.obs j) X.i₀ i
        (fun j => tagWeight_nonneg X H β β.obs j) hsum)
  rw [hformula] at hi
  exact (div_pos_iff_of_pos_right hmass).1 hi

theorem tagWeight_pos_ratio {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι)
    (ℓ : X.HKey) (hℓ : ℓ ∈ S) (hw : 0 < X.tagWeight H β S i) :
    0 < safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
      ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) := by
  have hgate : X.tagGate H.1 β i := by
    by_contra hg
    simp [Ctx6.tagWeight, hg] at hw
  let r : X.HKey → ℝ := fun s => safeRatio6
    ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))
  have hrne : r ℓ ≠ 0 := by
    intro hz
    have hprod : (∏ s ∈ S, r s) = 0 := Finset.prod_eq_zero hℓ hz
    simp [Ctx6.tagWeight, hgate, r, hprod] at hw
  have hr0 : 0 ≤ r ℓ := safeRatio6_nonneg
    ((X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ))
    ((X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ))
  exact lt_of_le_of_ne hr0 (Ne.symm hrne)

theorem hidPostRep_pos_weight {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.Base) (β : X.Ty) (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs)
    (hKeys : 0 < X.initLaw.w b.1 ∧
      (∀ u ∈ X.binsOf (posteriorTypeKeys6 X β), 0 < (X.candLaw b.1).w (b.2.1 u)) ∧
      ∀ s ∈ posteriorTypeKeys6 X β, 0 < (X.tagLawAt (X.parOf b) s).w (b.2.2 s))
    (hβkey : β.key ∈ X.C ℓ.1)
    (i : X.ι) (hi : 0 < (X.tagLawAt (X.parOf b) β.key).w i)
    (z : Fin N) (hpost : 0 < (X.hidPostRep b ℓ.1 β.key i).w z) :
    0 < X.hidWeight (X.withTag b β.key i) ℓ.1 (X.C ℓ.1) z := by
  letI : DecidableEq X.Key := X.instDecEqKey
  letI : DecidableEq X.HKey := X.instDecEqHKey
  have hactual := hidWeight_positive_at_actual_parent X b β ℓ hℓ hKeys hβkey i hi
  have hnonneg : ∀ y, 0 ≤ X.hidWeight (X.withTag b β.key i) ℓ.1 (X.C ℓ.1) y :=
    fun y => hidWeight_nonneg X (X.withTag b β.key i) ℓ.1 (X.C ℓ.1) y
  have hsum : 0 < ∑ y, X.hidWeight (X.withTag b β.key i) ℓ.1 (X.C ℓ.1) y := by
    have hle := Finset.single_le_sum (fun y hy => hnonneg y) (Finset.mem_univ
      ((X.parOf b).val (primaryName6 ℓ.1)))
    linarith [hactual]
  have hweight := normalize6_pos_weight_of_pos_mass
    (fun y => X.hidWeight (X.withTag b β.key i) ℓ.1 (X.C ℓ.1) y) X.y₀ z hnonneg hsum
      (by simpa [Ctx6.hidPostRep, Ctx6.hidPost] using hpost)
  exact hweight

theorem colDeg_eq_pr6 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) :
    colDeg E G μ y = μ.pr (fun x => Hits E G x y) := by
  unfold colDeg FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : Hits E G x y <;> simp [h]

theorem pr_not_eq_one_sub_pr6 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr (fun ω => ¬ A ω) = 1 - P.pr A := by
  classical
  have hsum : P.pr (fun ω => ¬ A ω) + P.pr A = 1 := by
    unfold FinProb.pr
    calc
      _ = ∑ ω, P.w ω := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases h : A ω <;> simp [h]
      _ = 1 := P.sum_eq_one
  linarith

theorem reqNames_card_le6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty) :
    (reqNames6 β).card ≤ β.obs.card + 2 := by
  letI : DecidableEq X.HKey := X.instDecEqHKey
  letI : DecidableEq X.Name := @instDecidableEqVarName6 X.Bin X.g.L.m X.instDecEqBin
  let obsNames : Finset X.Name := β.obs.image VarName6.hid
  have hSetEq : reqNames6 β = (insert (VarName6.par (primaryName6 β.key)) obsNames ∪
      if β.mode = Mode6.high then {VarName6.par (otherPrimaryName6 β.key)} else ∅) := by
    ext nm
    simp [reqNames6, obsNames]
  rw [hSetEq]
  have hImage : obsNames.card ≤ β.obs.card := Finset.card_image_le
  have hFirst : (insert (VarName6.par (primaryName6 β.key)) obsNames).card ≤
      β.obs.card + 1 := by
    calc
      (insert (VarName6.par (primaryName6 β.key)) obsNames).card ≤ obsNames.card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ β.obs.card + 1 := Nat.add_le_add_right hImage _
  have hOther :
      (if β.mode = Mode6.high then
          ({VarName6.par (otherPrimaryName6 β.key)} : Finset X.Name)
        else (∅ : Finset X.Name)).card ≤ 1 := by
    by_cases hm : β.mode = Mode6.high
    · rw [if_pos hm]
      simp
    · rw [if_neg hm]
      simp
  calc
    (insert (VarName6.par (primaryName6 β.key)) obsNames ∪
        if β.mode = Mode6.high then {VarName6.par (otherPrimaryName6 β.key)} else ∅).card ≤
      (insert (VarName6.par (primaryName6 β.key)) obsNames).card +
      Finset.card (if β.mode = Mode6.high then {VarName6.par (otherPrimaryName6 β.key)} else ∅) :=
          Finset.card_union_le _ _
    _ ≤ β.obs.card + 2 := by omega

theorem reqNames_nonmatching_card_le_one {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty) (hβ : β ∈ X.occTypes) :
    ((reqNames6 β).filter fun nm => ¬ matchesPrimaryName6 β nm).card ≤ 1 := by
  letI : DecidableEq X.Key := X.instDecEqKey
  letI : DecidableEq X.HKey := X.instDecEqHKey
  letI : DecidableEq X.Name := @instDecidableEqVarName6 X.Bin X.g.L.m X.instDecEqBin
  unfold Ctx6.occTypes at hβ
  rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
  let L := X.g.L
  have hkey : (X.evenType x).key = L.key x := by
    simp only [Ctx6.evenType, Type6.key, makeType6]
    split_ifs <;> rfl
  by_cases hlow : L.severity x ≤ X.J
  · have hmode : (X.evenType x).mode = .low := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.mode, modeOf6]
    have hobs : (X.evenType x).obs =
        lowObservations6 binAdjacent6 (L.key x) (L.sign x) (L.flippable x) := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs]
    let kOther : X.Key := ((L.key x).1, oppositeKeyFlag6 (L.key x).2)
    let ex : X.Name := .hid (kOther, L.sign x)
    have hsub : ((reqNames6 (X.evenType x)).filter fun nm =>
        ¬ matchesPrimaryName6 (X.evenType x) nm) ⊆ {ex} := by
      intro nm hnm
      rcases Finset.mem_filter.mp hnm with ⟨hnm, hbad⟩
      unfold reqNames6 at hnm
      rw [hkey, hmode, hobs] at hnm
      have hmodeNe : Mode6.low ≠ Mode6.high := by decide
      simp only [Finset.mem_union, if_neg hmodeNe, Finset.notMem_empty, or_false] at hnm
      simp only [Finset.mem_insert] at hnm
      rcases hnm with hpar | hhid
      · subst nm
        simp [matchesPrimaryName6, hkey] at hbad
      · simp only [Finset.mem_image] at hhid
        rcases hhid with ⟨ℓ, hℓ, hEq⟩
        subst nm
        have hprimary : primaryName6 ℓ.1 ≠ primaryName6 (L.key x) := by
          simpa [matchesPrimaryName6, hkey] using hbad
        unfold lowObservations6 at hℓ
        simp only [Finset.mem_union, Finset.mem_image] at hℓ
        rcases hℓ with hNbr | hFlip
        · rcases hNbr with ⟨s, hs, rfl⟩
          have hAdj : keyAdjacent6 binAdjacent6 (L.key x) s := by
            simpa [keyNeighborhood6] using hs
          have hOther := keyAdjacent_primary_mismatch_eq_opposite (L.key x) s hAdj hprimary
          simp [ex, kOther, hOther]
        · rcases hFlip with ⟨a, ha, rfl⟩
          exact (hprimary rfl).elim
    have hcard := Finset.card_le_card hsub
    simpa [ex] using hcard
  · have hhigh : ¬ L.severity x ≤ X.J := hlow
    have hmode : (X.evenType x).mode = .high := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.mode, modeOf6]
    have hobs : (X.evenType x).obs =
        highObservations6 (L.key x) (L.sign x) (L.severity x) X.J := by
      simp [Ctx6.evenType, L, makeType6, hlow, Type6.obs]
    let ex : X.Name := .par (otherPrimaryName6 (L.key x))
    have hsub : ((reqNames6 (X.evenType x)).filter fun nm =>
        ¬ matchesPrimaryName6 (X.evenType x) nm) ⊆ {ex} := by
      intro nm hnm
      rcases Finset.mem_filter.mp hnm with ⟨hnm, hbad⟩
      unfold reqNames6 at hnm
      rw [hkey, hmode, hobs] at hnm
      simp only [Finset.mem_union, if_pos rfl] at hnm
      rcases hnm with hleft | hright
      · simp only [Finset.mem_insert] at hleft
        rcases hleft with hpar | hhid
        · subst nm
          simp [matchesPrimaryName6, hkey] at hbad
        · simp only [Finset.mem_image] at hhid
          rcases hhid with ⟨ℓ, hℓ, hEq⟩
          subst nm
          by_cases hsev : L.severity x = X.J + 1
          · simp [highObservations6, hsev] at hℓ
            rcases hℓ with hℓ
            cases hℓ
            have hmatch : matchesPrimaryName6 (X.evenType x) (.hid (L.key x, L.sign x)) := by
              simp [matchesPrimaryName6, hkey]
            exact (hbad hmatch).elim
          · simp [highObservations6, hsev] at hℓ
      · have hEq : nm = VarName6.par (otherPrimaryName6 (L.key x)) := by simpa using hright
        subst nm
        simp [ex]
    have hcard := Finset.card_le_card hsub
    simpa [ex] using hcard

theorem exists_req_except_matching6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (β : X.Ty) (hβ : β ∈ X.occTypes) :
    ∃ e ∈ reqNames6 β, ∀ nm ∈ (reqNames6 β).erase e, matchesPrimaryName6 β nm := by
  letI : DecidableEq X.HKey := X.instDecEqHKey
  letI : DecidableEq X.Name := @instDecidableEqVarName6 X.Bin X.g.L.m X.instDecEqBin
  let S := reqNames6 β
  let Bad := S.filter fun nm => ¬ matchesPrimaryName6 β nm
  have hBadCard : Bad.card ≤ 1 := by
    simpa [Bad, S] using reqNames_nonmatching_card_le_one X β hβ
  by_cases hBad : Bad.Nonempty
  · rcases hBad with ⟨e, he⟩
    refine ⟨e, (Finset.mem_filter.mp he).1, ?_⟩
    intro nm hmem
    rcases Finset.mem_erase.mp hmem with ⟨hne, hnm⟩
    by_contra hmatch
    have hnmbad : nm ∈ Bad := Finset.mem_filter.mpr ⟨hnm, hmatch⟩
    have heq : e = nm := Finset.card_le_one_iff.mp hBadCard he hnmbad
    exact hne heq.symm
  · refine ⟨.par (primaryName6 β.key), ?_, ?_⟩
    · simp [S, reqNames6]
    · intro nm hmem
      rcases Finset.mem_erase.mp hmem with ⟨hne, hnm⟩
      have hnmbad : nm ∉ Bad := by
        intro hbad
        exact hBad ⟨nm, hbad⟩
      exact not_not.mp (fun hnot => hnmbad (Finset.mem_filter.mpr ⟨hnm, hnot⟩))

theorem eventually_m6_req_error {p₀ : ℝ} (hp₀ : 0 < p₀) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (602 * ((m₆ p₀ n : ℝ) + 1) + 2) * ε₆ p₀ n ≤ c₁ / 2 := by
  obtain ⟨hα, hαp, hαsmall, _, _, _⟩ := height_exponents6_admissible p₀ hp₀
  let a := p₀ - α₆ p₀
  have ha : 0 < a := by dsimp [a]; linarith
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ a) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hC : 0 < 3620 / c₁ := by norm_num [c₁, c₀]
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (htend.eventually (Filter.eventually_ge_atTop (3620 / c₁)))
  refine Filter.eventually_atTop.2 ⟨max 1 n₀, ?_⟩
  intro n hn
  have hn1Nat : 1 ≤ n := le_trans (le_max_left 1 n₀) hn
  have hnn₀ : n₀ ≤ n := le_trans (le_max_right 1 n₀) hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1Nat
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hpow : 3620 / c₁ ≤ (n : ℝ) ^ a := hn₀ n hnn₀
  have hαnonneg : 0 ≤ α₆ p₀ := le_of_lt hα
  have hpowα : 1 ≤ (n : ℝ) ^ α₆ p₀ := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1 hαnonneg
    simpa using h
  have hmceil : (m₆ p₀ n : ℝ) ≤ (n : ℝ) ^ α₆ p₀ + 1 := by
    change (⌈(n : ℝ) ^ α₆ p₀⌉₊ : ℝ) ≤ _
    calc
      (⌈(n : ℝ) ^ α₆ p₀⌉₊ : ℝ) ≤ (⌊(n : ℝ) ^ α₆ p₀⌋₊ + 1 : ℕ) := by
        exact_mod_cast Nat.ceil_le_floor_add_one ((n : ℝ) ^ α₆ p₀)
      _ = (⌊(n : ℝ) ^ α₆ p₀⌋₊ : ℝ) + 1 := by norm_num
      _ ≤ (n : ℝ) ^ α₆ p₀ + 1 := by
        have hnonneg : 0 ≤ (n : ℝ) ^ α₆ p₀ := Real.rpow_nonneg (Nat.cast_nonneg n) _
        linarith [Nat.floor_le hnonneg]
  have hfac : 602 * ((m₆ p₀ n : ℝ) + 1) + 2 ≤ 1810 * (n : ℝ) ^ α₆ p₀ := by
    nlinarith [hmceil, hpowα]
  have hε : 0 < ε₆ p₀ n := by
    dsimp [ε₆]
    exact Real.rpow_pos_of_pos hnpos _
  have hexp : (n : ℝ) ^ α₆ p₀ * (n : ℝ) ^ (-p₀) = (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    dsimp [a]
    ring
  calc
    (602 * ((m₆ p₀ n : ℝ) + 1) + 2) * ε₆ p₀ n ≤
        (1810 * (n : ℝ) ^ α₆ p₀) * ε₆ p₀ n :=
          mul_le_mul_of_nonneg_right hfac (le_of_lt hε)
    _ = 1810 * (n : ℝ) ^ (-a) := by
      rw [show ε₆ p₀ n = (n : ℝ) ^ (-p₀) by rfl]
      calc
        (1810 * (n : ℝ) ^ α₆ p₀) * (n : ℝ) ^ (-p₀) =
            1810 * ((n : ℝ) ^ α₆ p₀ * (n : ℝ) ^ (-p₀)) := by ring
        _ = 1810 * (n : ℝ) ^ (-a) := by rw [hexp]
    _ = 1810 * ((n : ℝ) ^ a)⁻¹ := by rw [Real.rpow_neg hnpos.le]
    _ = 1810 / (n : ℝ) ^ a := by rw [div_eq_mul_inv]
    _ ≤ 1810 / (3620 / c₁) := by
      exact div_le_div_of_nonneg_left (by norm_num) hC hpow
    _ = c₁ / 2 := by field_simp [show c₁ ≠ 0 by norm_num [c₁, c₀]]; norm_num

end Lane_q_s06_steps1

end HypercubeRamsey.S06
