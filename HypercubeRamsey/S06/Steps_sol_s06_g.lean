import HypercubeRamsey.S06.Steps_q_s06_steps1
import HypercubeRamsey.S06.Steps_q_s06_steps2

namespace HypercubeRamsey.S06.Lane_sol_s06_g
open OAI.HypercubeRamsey Classical Filter Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

 theorem stType_mode (a : X.State) : (X.stType a).mode = X.stMode a := by
  simp only [Ctx6.stType, ChunkLayout6.stType, Ctx6.stMode, modeOf6, makeType6]
  split_ifs <;> rfl

 theorem stType_key (a : X.State) : (X.stType a).key = X.g.L.stKey a := by
  simp only [Ctx6.stType, ChunkLayout6.stType, makeType6]
  split_ifs <;> rfl

 theorem desc_filter_card {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id) (P : X.Ty → Prop) [DecidablePred P] :
    ((X.descOf b φ).filter fun e => P e.2).card ≤
      ((X.g.L.stNbr b).filter fun a => P (X.stType a)).card := by
  let A := (Finset.univ : Finset (X.g.L.stNbr b)).filter fun a => P (X.stType a.1)
  have himage : (X.descOf b φ).filter (fun e => P e.2) =
      A.image (fun a => (φ a, X.stType a.1)) := by
    ext e
    simp only [Ctx6.descOf, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, A]
    constructor
    · rintro ⟨⟨a, rfl⟩, h⟩
      exact ⟨a, h, rfl⟩
    · rintro ⟨a, h, rfl⟩
      exact ⟨⟨a, rfl⟩, h⟩
  have hstates : A.image (fun a => a.1) = (X.g.L.stNbr b).filter (fun a => P (X.stType a)) := by
    ext a
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, h, rfl⟩
      exact ⟨v.2, h⟩
    · rintro ⟨ha, hp⟩
      exact ⟨⟨a, ha⟩, hp, rfl⟩
  have hcard : (A.image fun a => a.1).card = A.card :=
    Finset.card_image_of_injective A Subtype.val_injective
  rw [himage]
  exact Finset.card_image_le.trans (by rw [← hcard, hstates])

 theorem desc_nonmatching_card {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id) :
    ((X.descOf b φ).filter fun e => primaryName6 e.2.key ≠ X.tgtName b).card ≤ 1 := by
  have hc := desc_filter_card X b φ (fun β => primaryName6 β.key ≠ X.tgtName b)
  simp_rw [stType_key] at hc
  simpa only [Ctx6.tgtName] using hc.trans (X.facts.nonmatching_one b)

 theorem desc_low_card {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id) (hb : X.stMode b = .high) :
    ((X.descOf b φ).filter fun e => e.2.mode = .low).card ≤ 1 := by
  have hc := desc_filter_card X b φ (fun β => β.mode = .low)
  simp_rw [stType_mode] at hc
  have heq : ((X.g.L.stNbr b).filter fun a => X.stMode a = .low) =
      (X.g.L.stNbr b).filter (fun a => modeOf6 X.J (X.g.L.stSeverity a) ≠
        modeOf6 X.J (X.g.L.stSeverity b)) := by
    ext a
    have hbb : modeOf6 X.J (X.g.L.stSeverity b) = .high := hb
    simp only [Finset.mem_filter, hbb]
    change (a ∈ X.g.L.stNbr b ∧ X.stMode a = .low) ↔
      (a ∈ X.g.L.stNbr b ∧ X.stMode a ≠ .high)
    cases X.stMode a <;> simp
  rw [heq] at hc
  simpa only [Ctx6.J] using hc.trans (X.facts.low_high_one b)

 theorem high_obs_card (β : X.Ty) (hβ : β ∈ X.occTypes) (hm : β.mode = .high) : β.obs.card ≤ 1 := by
  rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
  by_cases hj : X.g.L.severity x ≤ X.J
  · simp only [Ctx6.evenType, makeType6, if_pos hj, Type6.mode] at hm
    cases hm
  · simp only [Ctx6.evenType, makeType6, if_neg hj, Type6.obs]
    unfold highObservations6
    split_ifs <;> simp

 theorem desc_u_sum {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id) (hb : X.stMode b = .high)
    (hu : ∀ e ∈ X.descOf b φ, e.2.u ≤ X.J + 1) :
    (∑ e ∈ X.descOf b φ, e.2.u) ≤ (X.descOf b φ).card + X.J := by
  let D := X.descOf b φ
  have hpoint : ∀ e ∈ D, e.2.u ≤ 1 + if e.2.mode = .low then X.J else 0 := by
    intro e he
    by_cases hm : e.2.mode = .low
    · simpa [hm, Nat.add_comm] using hu e he
    · have hhigh : e.2.mode = .high := by cases h : e.2.mode <;> simp_all
      simp [Type6.u, hhigh]
  calc
    (∑ e ∈ D, e.2.u) ≤ ∑ e ∈ D, (1 + if e.2.mode = .low then X.J else 0) :=
      Finset.sum_le_sum hpoint
    _ = D.card + ((D.filter fun e => e.2.mode = .low).card * X.J) := by
      rw [Finset.sum_add_distrib]
      simp [← Finset.sum_filter]
    _ ≤ D.card + X.J := by
      have hc := desc_low_card X b φ hb
      have hh := Nat.mul_le_mul_right X.J hc
      simpa [D] using Nat.add_le_add_left hh D.card

 theorem locHid_card {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id) (hb : X.stMode b = .high)
    (hocc : ∀ e ∈ X.descOf b φ, e.2 ∈ X.occTypes)
    (hu : ∀ e ∈ X.descOf b φ, e.2.u ≤ X.J + 1) :
    (X.locHid (X.descOf b φ)).card ≤ (X.descOf b φ).card + 602 * (X.J + 1) := by
  let D := X.descOf b φ
  have hpoint : ∀ e ∈ D, e.2.obs.card ≤ 1 + if e.2.mode = .low then 602 * (X.J + 1) else 0 := by
    intro e he
    by_cases hm : e.2.mode = .low
    · have ho := Lane_q_s06_steps1.occType_obs_card_le X e.2 (hocc e he)
      have hs := Nat.mul_le_mul_left 602 (hu e he)
      simp only [if_pos hm]
      omega
    · have hhigh : e.2.mode = .high := by cases h : e.2.mode <;> simp_all
      simpa [hm] using high_obs_card X e.2 (hocc e he) hhigh
  calc
    (X.locHid D).card ≤ ∑ e ∈ D, e.2.obs.card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ D, (1 + if e.2.mode = .low then 602 * (X.J + 1) else 0) :=
      Finset.sum_le_sum hpoint
    _ = D.card + ((D.filter fun e => e.2.mode = .low).card * (602 * (X.J + 1))) := by
      rw [Finset.sum_add_distrib]
      simp [← Finset.sum_filter]
    _ ≤ D.card + 602 * (X.J + 1) := by
      have hc := desc_low_card X b φ hb
      have hh := Nat.mul_le_mul_right (602 * (X.J + 1)) hc
      simpa [D] using Nat.add_le_add_left hh D.card

 theorem C_self (h : X.Key) : h ∈ X.C h := by
  simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]

 theorem C_symm {h s : X.Key} (hs : s ∈ X.C h) : h ∈ X.C s := by
  simp only [Ctx6.C, keyNeighborhood6, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact Lane_q_s06_steps1.keyAdjacent6_symm hs

 theorem locKeys_card {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty))
    (hocc : ∀ e ∈ D, e.2 ∈ X.occTypes)
    (hkeys : ∀ e ∈ D, e.2.key ∈ X.C (X.g.L.stKey b)) :
    (X.locKeys D).card ≤ 602 ^ 3 + 602 := by
  let S₀ := X.C (X.g.L.stKey b)
  let S₁ := S₀.biUnion X.C
  let S₂ := S₁.biUnion X.C
  have hC (h : X.Key) : (X.C h).card ≤ 602 := X.g.flips.key_neighborhood_card h
  have hS₀ : S₀.card ≤ 602 := hC _
  have hS₁ : S₁.card ≤ 602 ^ 2 := by
    calc
      S₁.card ≤ ∑ h ∈ S₀, (X.C h).card := Finset.card_biUnion_le
      _ ≤ ∑ h ∈ S₀, 602 := Finset.sum_le_sum fun h hh => hC h
      _ = S₀.card * 602 := by simp
      _ ≤ 602 ^ 2 := by nlinarith [hS₀]
  have hS₂ : S₂.card ≤ 602 ^ 3 := by
    calc
      S₂.card ≤ ∑ h ∈ S₁, (X.C h).card := Finset.card_biUnion_le
      _ ≤ ∑ h ∈ S₁, 602 := Finset.sum_le_sum fun h hh => hC h
      _ = S₁.card * 602 := by simp
      _ ≤ 602 ^ 3 := by nlinarith [hS₁]
  have hsub : X.locKeys D ⊆ S₂ ∪ S₀ := by
    intro s hs
    rcases Finset.mem_union.mp hs with hhid | htype
    · rcases Finset.mem_biUnion.mp hhid with ⟨ℓ, hℓ, hs⟩
      rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hℓ⟩
      have hℓkey : ℓ.1 ∈ X.C e.2.key :=
        C_symm X (Lane_q_s06_steps1.occObs_key_mem_C X e.2 (hocc e he) ℓ hℓ)
      have hS₁ℓ : ℓ.1 ∈ S₁ := Finset.mem_biUnion.mpr ⟨e.2.key, hkeys e he, hℓkey⟩
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ.1, hS₁ℓ, hs⟩)
    · rcases Finset.mem_image.mp htype with ⟨e, he, rfl⟩
      exact Finset.mem_union_right _ (hkeys e he)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le S₂ S₀).trans (Nat.add_le_add hS₂ hS₀))


 theorem parameter_scales (p₀ : ℝ) (hp₀ : 0 < p₀) (C : ℕ) :
    ∃ n₀, ∀ n ≥ n₀,
      let m := m₆ p₀ n
      let J := J₆ m
      4 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ 10000 * (C + 1) ≤ J ∧ T₆ m + 1 ≤ J ∧
        (J : ℝ) * (n : ℝ) ^ (-p₀) ≤ 1 / 10 ^ 9 := by
  have hα := height_exponents6_admissible p₀ hp₀
  have hnTrend := tendsto_natCast_atTop_atTop (R := ℝ)
  have hmTrend : Filter.Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop ?_ ((tendsto_rpow_atTop hα.1).comp hnTrend)
    filter_upwards [] with n
    exact Nat.le_ceil ((n : ℝ) ^ α₆ p₀)
  have hJTrend : Filter.Tendsto (fun n : ℕ => J₆ (m₆ p₀ n)) Filter.atTop Filter.atTop := by
    have hfloor : Filter.Tendsto (fun x : ℝ => Nat.floor x) Filter.atTop Filter.atTop :=
      (Nat.floor_mono (R := ℝ)).tendsto_atTop_atTop (fun b => ⟨(b : ℝ), by simp⟩)
    exact hfloor.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 25)).comp hmTrend)
  have hSmall : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (α₆ p₀ - p₀))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hα.2.1)).comp hnTrend
    simpa only [Function.comp_def, neg_sub, mul_zero] using Filter.Tendsto.const_mul 2 h
  have hlog := (Real.tendsto_log_atTop.comp hnTrend).eventually_ge_atTop (1 : ℝ)
  have hJ := hJTrend.eventually_ge_atTop (10000 * (C + 1))
  have hT := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp hmTrend).eventually_ge_atTop (2 : ℝ)
  have hsmall := hSmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10 ^ 9))
  have hAll : ∀ᶠ n : ℕ in Filter.atTop,
      let m := m₆ p₀ n
      let J := J₆ m
      4 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ 10000 * (C + 1) ≤ J ∧ T₆ m + 1 ≤ J ∧
        (J : ℝ) * (n : ℝ) ^ (-p₀) ≤ 1 / 10 ^ 9 := by
    filter_upwards [Filter.eventually_ge_atTop 4, hlog, hJ, hT, hsmall] with n hn hl hj ht hs
    refine ⟨hn, hl, hj, ?_, ?_⟩
    · let x : ℝ := (m₆ p₀ n : ℝ) ^ (1 / 1000 : ℝ)
      have hx : 2 ≤ x := ht
      have hpow : (m₆ p₀ n : ℝ) ^ (1 / 25 : ℝ) = x ^ 40 := by
        calc
          _ = (m₆ p₀ n : ℝ) ^ ((1 / 1000 : ℝ) * 40) := by congr 1 <;> norm_num
          _ = ((m₆ p₀ n : ℝ) ^ (1 / 1000 : ℝ)) ^ (40 : ℝ) :=
            Real.rpow_mul (Nat.cast_nonneg _) _ _
          _ = x ^ 40 := by simpa [x] using Real.rpow_natCast ((m₆ p₀ n : ℝ) ^ (1 / 1000 : ℝ)) 40
      have hceil : (T₆ (m₆ p₀ n) : ℝ) ≤ x + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)).le
      have hx2 : x + 2 ≤ x ^ 2 := by nlinarith
      have hx40 : x ^ 2 ≤ x ^ 40 := pow_le_pow_right₀ (by linarith) (by norm_num)
      apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
      rw [hpow, Nat.cast_add, Nat.cast_one]
      nlinarith [hceil, hx2, hx40]
    · have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
      have hpow1 : 1 ≤ (n : ℝ) ^ α₆ p₀ := Real.one_le_rpow hnR hα.1.le
      have hmLower : 1 ≤ (m₆ p₀ n : ℝ) := hpow1.trans (Nat.le_ceil _)
      have hmUpper : (m₆ p₀ n : ℝ) ≤ 2 * (n : ℝ) ^ α₆ p₀ := by
        have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hnp.le (α₆ p₀))
        change (m₆ p₀ n : ℝ) < (n : ℝ) ^ α₆ p₀ + 1 at hc
        linarith
      have hJm : (J₆ (m₆ p₀ n) : ℝ) ≤ (m₆ p₀ n : ℝ) := by
        exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
          (by simpa only [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le hmLower (by norm_num : (1 / 25 : ℝ) ≤ 1)))
      calc
        (J₆ (m₆ p₀ n) : ℝ) * (n : ℝ) ^ (-p₀) ≤
            (2 * (n : ℝ) ^ α₆ p₀) * (n : ℝ) ^ (-p₀) :=
          mul_le_mul_of_nonneg_right (hJm.trans hmUpper) (Real.rpow_nonneg hnp.le _)
        _ = 2 * (n : ℝ) ^ (α₆ p₀ - p₀) := by rw [mul_assoc, ← Real.rpow_add hnp]; congr 2 <;> ring
        _ ≤ 1 / 10 ^ 9 := hs.le
  exact Filter.eventually_atTop.1 hAll


 theorem absolute_exponent_budget {n J k q z C : ℕ} {ε : ℝ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hJ : 10000 * (C + 1) ≤ J)
    (hq : q ≤ 20000 * J) (hz : z ≤ q + 602 * (J + 1))
    (hk : (k : ℝ) ≤ κ₆ * J * Real.log (n : ℝ) + 1)
    (hε : 0 ≤ ε) (hsmall : (J : ℝ) * ε ≤ 1 / 10 ^ 9) :
    ((C + 1 : ℕ) : ℝ) * (Real.log 20 + Dstar₆ * Real.log (n : ℝ)) +
      (C : ℝ) * d₀ * Real.log (n : ℝ) + (z : ℝ) * d₁ * Real.log (n : ℝ) +
      d₂ * ((q : ℝ) + J) * Real.log (n : ℝ) + (q : ℝ) * k * (4 * ε / c₁) +
      (k : ℝ) * Real.log (2 / c₁) + (2 / 100 : ℝ) * k ≤
        (5 / 100 : ℝ) * J * Real.log (n : ℝ) := by
  let L := Real.log (n : ℝ)
  have hL : 1 ≤ L := hlog
  have hJR : (10000 : ℝ) * ((C : ℝ) + 1) ≤ J := by exact_mod_cast hJ
  have hJ1 : 10000 ≤ (J : ℝ) := by nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  have hk' : (k : ℝ) ≤ 2 * κ₆ * J * L := by
    dsimp [L] at *
    have hlmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (J : ℝ))
    norm_num [κ₆] at *
    nlinarith
  have hqR : (q : ℝ) ≤ 20000 * J := by exact_mod_cast hq
  have hzR : (z : ℝ) ≤ (q : ℝ) + 602 * ((J : ℝ) + 1) := by exact_mod_cast hz
  have hz' : (z : ℝ) ≤ 21204 * J := by nlinarith
  have hqε : (q : ℝ) * ε ≤ 1 / 50000 := by
    have hm := mul_le_mul_of_nonneg_right hqR hε
    nlinarith [hm, hsmall]
  have hcoarse : ((C : ℝ) + 1) * (Real.log 20 + Dstar₆ * L) + (C : ℝ) * d₀ * L ≤
      (21 / 10000 : ℝ) * J * L := by
    have hl20 : Real.log (20 : ℝ) ≤ 19 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
      norm_num at hh
      exact hh
    have hc : (C : ℝ) ≤ (C : ℝ) + 1 := by linarith
    have hCL := mul_le_mul_of_nonneg_right hJR (show (0 : ℝ) ≤ L by linarith)
    have hD : Dstar₆ + d₀ ≤ 1 := by norm_num [Dstar₆, d₀]
    have hlog20 : Real.log (20 : ℝ) ≤ 20 * L := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hlog20 (show 0 ≤ (C : ℝ) + 1 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
      (show 0 ≤ d₀ by norm_num [d₀])) (show (0 : ℝ) ≤ L by linarith)
    have h₃ := mul_le_mul_of_nonneg_left hD (show 0 ≤ ((C : ℝ) + 1) * L by positivity)
    nlinarith
  have hhidden : (z : ℝ) * d₁ * L ≤ (21204 / 10 ^ 10 : ℝ) * J * L := by
    have h := mul_le_mul_of_nonneg_right hz' (show 0 ≤ d₁ * L by norm_num [d₁]; positivity)
    norm_num [d₁] at h ⊢
    nlinarith [h]
  have htags : d₂ * ((q : ℝ) + J) * L ≤ (20001 / 10 ^ 6 : ℝ) * J * L := by
    have h := mul_le_mul_of_nonneg_left (add_le_add_right hqR (J : ℝ))
      (show 0 ≤ d₂ * L by norm_num [d₂]; positivity)
    norm_num [d₂] at h ⊢
    nlinarith
  have hlabelsGood : (q : ℝ) * k * (4 * ε / c₁) ≤ (16 / 1000 : ℝ) * k := by
    have h := mul_le_mul_of_nonneg_right hqε (show 0 ≤ (k : ℝ) by positivity)
    norm_num [c₁, c₀] at *
    nlinarith
  have hl400 : Real.log (2 / c₁) ≤ 38 := by
    have h20 : Real.log (20 : ℝ) ≤ 19 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
      norm_num at hh
      exact hh
    have heq : Real.log (2 / c₁) = 2 * Real.log 20 := by
      norm_num [c₁, c₀]
      rw [show (400 : ℝ) = 20 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    linarith
  have hlabels : (q : ℝ) * k * (4 * ε / c₁) + (k : ℝ) * Real.log (2 / c₁) +
      (2 / 100 : ℝ) * k ≤ (8 / 1000 : ℝ) * J * L := by
    have hbad := mul_le_mul_of_nonneg_left hl400 (show 0 ≤ (k : ℝ) by positivity)
    have hks := mul_le_mul_of_nonneg_left hk' (by norm_num : (0 : ℝ) ≤ 38 + 16 / 1000 + 2 / 100)
    norm_num [κ₆] at hks
    nlinarith
  have hjl : 0 ≤ (J : ℝ) * L := by positivity
  push_cast
  nlinarith [hcoarse, hhidden, htags, hlabels, hjl]


end
end HypercubeRamsey.S06.Lane_sol_s06_g
