import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.Framework.FinProbLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S06.Lane_q_s06_ev_d

open Classical
open Filter
open OAI.HypercubeRamsey

/-! Geometry used by the separated even-row estimates. -/

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}

private theorem pow_find_scale_le (m r t : ℕ) (hm : 1 ≤ m) (h : ∃ i, t ≤ m ^ i * r) :
    m ^ Nat.find h * r ≤ m * (t + r) := by
  by_cases hzero : Nat.find h = 0
  · rw [hzero, pow_zero, one_mul]
    calc
      r ≤ t + r := Nat.le_add_left r t
      _ = 1 * (t + r) := by simp
      _ ≤ m * (t + r) := Nat.mul_le_mul_right _ hm
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hi]
    have hprev : ¬ t ≤ m ^ i * r := Nat.find_min h (by omega)
    have hprev' : m ^ i * r < t := Nat.lt_of_not_ge hprev
    calc
      m ^ (i + 1) * r = m * (m ^ i * r) := by rw [pow_succ]; ring
      _ ≤ m * t := Nat.mul_le_mul_left m hprev'.le
      _ ≤ m * (t + r) := Nat.mul_le_mul_left m (Nat.le_add_right t r)

private theorem index_le_pow (m : ℕ) (hm : 2 ≤ m) : ∀ t : ℕ, t ≤ m ^ t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      by_cases ht : t = 0
      · subst t
        simpa using le_trans (by norm_num : 1 ≤ 2) hm
      · have htpos : 1 ≤ t := by omega
        calc
          t + 1 ≤ 2 * t := by omega
          _ ≤ m * t := Nat.mul_le_mul_right t hm
          _ ≤ m * m ^ t := Nat.mul_le_mul_left m ih
          _ = m ^ (t + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

private theorem topScale_le (n : ℕ) (σ ζ : ℝ) :
    topScale n σ ζ ≤ max 2 ⌈(n : ℝ) ^ σ⌉₊ *
      (⌈(n : ℝ) ^ (1 - ζ)⌉₊ + max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) := by
  unfold topScale
  let r : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let m : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let t : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hm : 2 ≤ m := by dsimp [m]; exact le_max_left _ _
  have hr : 1 ≤ r := by dsimp [r]; exact le_max_left _ _
  have hscale : ∃ i, t ≤ m ^ i * r := by
    refine ⟨t, ?_⟩
    calc
      t ≤ m ^ t := index_le_pow m hm t
      _ = m ^ t * 1 := by simp
      _ ≤ m ^ t * r := Nat.mul_le_mul_left _ hr
  have hbound := pow_find_scale_le m r t (by omega) hscale
  simpa [r, m, t] using hbound

private theorem topScale_div_tendsto_zero {σ ζ : ℝ} (hσ : 0 < σ) (hgap : σ < ζ)
    (hζ : ζ < 1) (h2σ : 2 * σ < 1) :
    Tendsto (fun n : ℕ => (topScale n σ ζ : ℝ) / n) atTop (nhds 0) := by
  have hlogBoundReal : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ ‖x ^ (σ / 2)‖ := by
    have h := (isLittleO_log_rpow_atTop (div_pos hσ (by norm_num : (0 : ℝ) < 2))).bound
      (by norm_num : (0 : ℝ) < 1)
    simpa using h
  have hlogBoundNat : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ)‖ ≤ ‖(n : ℝ) ^ (σ / 2)‖ :=
    tendsto_natCast_atTop_atTop.eventually hlogBoundReal
  have hsigmaT : Tendsto (fun n : ℕ => (n : ℝ) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop
  have htargetExp : 0 < 1 - ζ := by linarith
  have htargetT : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - ζ)) atTop atTop :=
    (tendsto_rpow_atTop htargetExp).comp tendsto_natCast_atTop_atTop
  have hsigLarge : ∀ᶠ n : ℕ in atTop, 3 ≤ (n : ℝ) ^ σ :=
    hsigmaT.eventually_ge_atTop 3
  have htargetLarge : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ^ (1 - ζ) :=
    htargetT.eventually_ge_atTop 1
  have hpoint : ∀ᶠ n : ℕ in atTop,
      (topScale n σ ζ : ℝ) / n ≤ 4 * (n : ℝ) ^ (-(ζ - σ)) +
        4 * (n : ℝ) ^ (-(1 - 2 * σ)) := by
    filter_upwards [hlogBoundNat, hsigLarge, htargetLarge,
      Filter.eventually_gt_atTop (1 : ℕ)] with n hlogBound hsigLarge htargetLarge hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnRone : 1 < (n : ℝ) := by exact_mod_cast hn
    have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hpowPos : 0 < (n : ℝ) ^ (σ / 2) := Real.rpow_pos_of_pos hnR _
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (σ / 2) := by
      simpa [Real.norm_of_nonneg hlogNonneg, Real.norm_of_nonneg hpowPos.le] using hlogBound
    have hpowSq : ((n : ℝ) ^ (σ / 2)) ^ 2 = (n : ℝ) ^ σ := by
      calc
        ((n : ℝ) ^ (σ / 2)) ^ 2 = (n : ℝ) ^ ((σ / 2) * 2) :=
          (Real.rpow_mul_natCast hnR.le (σ / 2) 2).symm
        _ = (n : ℝ) ^ σ := by congr 1 <;> ring
    have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ σ := by
      nlinarith [hlog, hpowSq]
    have hceilLog : ((⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) < (n : ℝ) ^ σ + 1 := by
      calc
        ((⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) < (Real.log (n : ℝ)) ^ 2 + 1 :=
          Nat.ceil_lt_add_one (sq_nonneg _)
        _ ≤ (n : ℝ) ^ σ + 1 := by nlinarith [hlogSq]
    have hceilTarget : ((⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℕ) : ℝ) ≤
        2 * (n : ℝ) ^ (1 - ζ) := by
      have hc := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hnR (1 - ζ)))
      have hc' : ((⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℕ) : ℝ) < (n : ℝ) ^ (1 - ζ) + 1 := hc
      linarith
    have hceilCenters : ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤
        2 * (n : ℝ) ^ σ := by
      rw [Nat.cast_max]
      apply max_le
      · have hone : ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ σ :=
          le_trans (by norm_num : ((1 : ℕ) : ℝ) ≤ 3) hsigLarge
        calc
          ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ σ := hone
          _ ≤ 2 * (n : ℝ) ^ σ := by nlinarith [Real.rpow_pos_of_pos hnR σ]
      · calc
          ((⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ σ + 1 := le_of_lt hceilLog
          _ ≤ 2 * (n : ℝ) ^ σ := by nlinarith [hsigLarge]
    have hceilM : ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
      rw [Nat.cast_max]
      apply max_le
      · calc
          ((2 : ℕ) : ℝ) ≤ 6 := by norm_num
          _ = 2 * 3 := by norm_num
          _ ≤ 2 * (n : ℝ) ^ σ := mul_le_mul_of_nonneg_left hsigLarge (by norm_num)
      · have hc := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hnR σ))
        have hc' : ((⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) < (n : ℝ) ^ σ + 1 := hc
        calc
          ((⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ σ + 1 := le_of_lt hc'
          _ ≤ 2 * (n : ℝ) ^ σ := by nlinarith [hsigLarge]
    have htop0 : (topScale n σ ζ : ℝ) ≤
        4 * (n : ℝ) ^ (1 + σ - ζ) + 4 * (n : ℝ) ^ (2 * σ) := by
      have htop := topScale_le n σ ζ
      have htopCast : (topScale n σ ζ : ℝ) ≤
          ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) *
            (((⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℕ) : ℝ) +
              ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ)) := by
        exact_mod_cast htop
      have hsum : (((⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℕ) : ℝ) +
          ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ)) ≤
          2 * (n : ℝ) ^ (1 - ζ) + 2 * (n : ℝ) ^ σ :=
        add_le_add hceilTarget hceilCenters
      calc
        (topScale n σ ζ : ℝ) ≤
          ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) *
            (((⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℕ) : ℝ) +
              ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ)) := htopCast
        _ ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ) + 2 * (n : ℝ) ^ σ) :=
          mul_le_mul hceilM hsum (by positivity) (by positivity)
        _ = 4 * (n : ℝ) ^ (1 + σ - ζ) + 4 * (n : ℝ) ^ (2 * σ) := by
          calc
            _ = 4 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) +
                4 * ((n : ℝ) ^ σ * (n : ℝ) ^ σ) := by ring
            _ = _ := by
              rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
              congr 1 <;> ring
    have hdiv (e : ℝ) : (n : ℝ) ^ e / n = (n : ℝ) ^ (e - 1) := by
      have hs := Real.rpow_sub hnR e 1
      simpa using hs.symm
    have hratio : (topScale n σ ζ : ℝ) / n ≤
        4 * (n : ℝ) ^ (-(ζ - σ)) + 4 * (n : ℝ) ^ (-(1 - 2 * σ)) := by
      calc
        (topScale n σ ζ : ℝ) / n ≤
            (4 * (n : ℝ) ^ (1 + σ - ζ) + 4 * (n : ℝ) ^ (2 * σ)) / n :=
          div_le_div_of_nonneg_right htop0 hnR.le
        _ = 4 * (n : ℝ) ^ (1 + σ - ζ) / n + 4 * (n : ℝ) ^ (2 * σ) / n := by rw [add_div]
        _ = _ := by
          rw [mul_div_assoc, mul_div_assoc, hdiv, hdiv]
          rw [show (1 + σ - ζ) - 1 = -(ζ - σ) by ring]
          rw [show 2 * σ - 1 = -(1 - 2 * σ) by ring]
    exact hratio
  have hpow₁ : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(ζ - σ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hgap)).comp tendsto_natCast_atTop_atTop
  have hpow₂ : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - 2 * σ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr h2σ)).comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto
      (fun n : ℕ => 4 * (n : ℝ) ^ (-(ζ - σ)) + 4 * (n : ℝ) ^ (-(1 - 2 * σ)))
      atTop (nhds 0) := by
    simpa using (hpow₁.const_mul 4).add (hpow₂.const_mul 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall fun n => by positivity
  · exact hpoint

private theorem binEntropy_oneFortieth_le : Real.binEntropy (1 / 40 : ℝ) ≤ 13 / 100 := by
  have hlog2 : Real.log 2 < 7 / 10 := by
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog40 : Real.log 40 < 21 / 5 := by
    calc
      Real.log 40 < Real.log 64 := Real.log_lt_log (by norm_num) (by norm_num)
      _ = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, Real.log_pow]
        norm_num
      _ < 6 * (7 / 10) := by nlinarith
      _ = 21 / 5 := by norm_num
  have hfirst : (1 / 40 : ℝ) * Real.log 40 < 21 / 200 := by nlinarith
  have hy : 0 < (1 - 1 / 40 : ℝ)⁻¹ := by norm_num
  have hyne : (1 - 1 / 40 : ℝ)⁻¹ ≠ 1 := by norm_num
  have hlogy := Real.log_lt_sub_one_of_pos hy hyne
  have hsecond : (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤ 1 / 40 := by
    calc
      (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤
          (1 - 1 / 40 : ℝ) * ((1 - 1 / 40 : ℝ)⁻¹ - 1) :=
        (mul_lt_mul_of_pos_left hlogy (by norm_num)).le
      _ = 1 / 40 := by norm_num
  change (1 / 40 : ℝ) * Real.log ((1 / 40 : ℝ)⁻¹) +
      (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤ 13 / 100
  rw [show (1 / 40 : ℝ)⁻¹ = 40 by norm_num]
  linarith

private theorem binEntropy_le_oneFortieth {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 40) :
    Real.binEntropy q ≤ 13 / 100 := by
  have hqmem : q ∈ Set.Icc (0 : ℝ) (2⁻¹) := ⟨hq0, by linarith⟩
  have h40mem : (1 / 40 : ℝ) ∈ Set.Icc (0 : ℝ) (2⁻¹) := by norm_num
  calc
    Real.binEntropy q ≤ Real.binEntropy (1 / 40 : ℝ) :=
      Real.binEntropy_strictMonoOn.monotoneOn hqmem h40mem hq
    _ ≤ 13 / 100 := binEntropy_oneFortieth_le

private theorem hammingDist_le_residualDist_add_complement_aux {n : ℕ} (L : ChunkLayout6 n)
    (v w : CubeVertex n) :
    _root_.hammingDist v w ≤ L.residualDist v w + (Finset.univ \ L.residual).card := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter fun i => v i ≠ w i
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun i => i ∈ L.residual)
  have hres : (D.filter fun i => i ∈ L.residual).card = L.residualDist v w := by
    apply congrArg Finset.card
    ext i
    simp [D, and_comm]
  have hother : (D.filter fun i => i ∉ L.residual).card ≤ (Finset.univ \ L.residual).card :=
    Finset.card_le_card (by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  change D.card ≤ _
  omega

private theorem residualNear_card_le_ball_aux {n : ℕ} (L : ChunkLayout6 n)
    (v : CubeVertex n) (R : ℕ) :
    (Finset.univ.filter fun w : CubeVertex n => L.residualDist v w ≤ R).card ≤
      (hammingBall v (R + (Finset.univ \ L.residual).card)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  have hdist := hammingDist_le_residualDist_add_complement_aux L v w
  have hnear : L.residualDist v w ≤ R := (Finset.mem_filter.mp hw).2
  simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans hdist (Nat.add_le_add_right hnear _)

private theorem residual_near_volume_bound {n : ℕ} (hn : 0 < n) (L : ChunkLayout6 n)
    (v : CubeVertex n) (R : ℕ)
    (hR : (((R + (Finset.univ \ L.residual).card : ℕ) : ℝ) / n) ≤ 1 / 40)
    (hRnat : R + (Finset.univ \ L.residual).card ≤ n / 2) :
    ((Finset.univ.filter fun w : CubeVertex n => L.residualDist v w ≤ R).card : ℝ) ≤
      Real.exp ((13 / 100 : ℝ) * n) := by
  have hball := hammingBall_volume_bound hn hRnat v
  have hcard : (Finset.univ.filter fun w : CubeVertex n => L.residualDist v w ≤ R).card ≤
      (hammingBall v (R + (Finset.univ \ L.residual).card)).card :=
    residualNear_card_le_ball_aux L v R
  have hq0 : 0 ≤ ((R + (Finset.univ \ L.residual).card : ℕ) : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hentropy := binEntropy_le_oneFortieth hq0 hR
  calc
    ((Finset.univ.filter fun w : CubeVertex n => L.residualDist v w ≤ R).card : ℝ) ≤
        (hammingBall v (R + (Finset.univ \ L.residual).card)).card := by exact_mod_cast hcard
    _ ≤ Real.exp (Real.binEntropy (((R + (Finset.univ \ L.residual).card : ℕ) : ℝ) / n) * n) := hball
    _ ≤ Real.exp ((13 / 100 : ℝ) * n) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hentropy (Nat.cast_nonneg _))

theorem hammingDist_le_residualDist_add_complement {n : ℕ} (L : ChunkLayout6 n)
    (v w : CubeVertex n) :
    _root_.hammingDist v w ≤ L.residualDist v w + (Finset.univ \ L.residual).card := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter fun i => v i ≠ w i
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun i => i ∈ L.residual)
  have hres : (D.filter fun i => i ∈ L.residual).card = L.residualDist v w := by
    apply congrArg Finset.card
    ext i
    simp [D, ChunkLayout6.residualDist, and_comm]
  have hother : (D.filter fun i => i ∉ L.residual).card ≤ (Finset.univ \ L.residual).card :=
    Finset.card_le_card (by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  change D.card ≤ _
  omega

private theorem residualNear_card_le_ball {n : ℕ} (L : ChunkLayout6 n)
    (v : CubeVertex n) (R : ℕ) :
    (Finset.univ.filter fun w : CubeVertex n => L.residualDist v w ≤ R).card ≤
      (hammingBall v (R + (Finset.univ \ L.residual).card)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  have hdist := hammingDist_le_residualDist_add_complement L v w
  have hnear : L.residualDist v w ≤ R := (Finset.mem_filter.mp hw).2
  simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans hdist (Nat.add_le_add_right hnear _)

private theorem residual_complement_eq_occupied {n : ℕ} (L : ChunkLayout6 n) :
    Finset.univ \ L.residual =
      (Finset.univ.biUnion L.coarseChunks) ∪ (Finset.univ.biUnion L.fineChunks) := by
  classical
  ext i
  constructor
  · intro hi
    have hiuniv : i ∈ Finset.univ := Finset.mem_univ _
    rw [← L.chunks_cover] at hiuniv
    rcases Finset.mem_union.mp hiuniv with hoccupied | hres
    · exact hoccupied
    · exact False.elim ((Finset.mem_sdiff.mp hi).2 hres)
  · intro hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hres
    rcases Finset.mem_union.mp hi with hcoarse | hfine
    · obtain ⟨j, hj, hmem⟩ := Finset.mem_biUnion.mp hcoarse
      exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.1 j)) hmem hres
    · obtain ⟨j, hj, hmem⟩ := Finset.mem_biUnion.mp hfine
      exact (Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.2 j)) hmem hres

noncomputable def separationRadius {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) : ℕ :=
  2 * X.hp.r + 8 * X.hp.Rlong + 100

theorem residual_near_bounds_eventually {γ p₀ K : ℝ} (hp₀ : 0 < p₀) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N)
        (X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n),
        ((Finset.univ.filter fun w : CubeVertex n =>
          X.g.L.residualDist v w ≤ separationRadius X).card : ℝ) ≤
            Real.exp (-(56 / 100 : ℝ) * n) * (Fintype.card (CubeVertex n) : ℝ) ∧
          (n : ℝ) * Real.exp (-(56 / 100 : ℝ) * n) *
            (10 * Real.exp ((55 / 100 : ℝ) * n)) ≤ 1 := by
  let α : ℝ := α₆ p₀
  let σ : ℝ := σ₆ α
  let ζ : ℝ := ζ₆ α
  have hα := height_exponents6_admissible p₀ hp₀
  have hαpos : 0 < α := by simpa [α] using hα.1
  have hαsmall : α ≤ 1 / 10 ^ 12 := by simpa [α] using hα.2.2.1
  have hσ : 0 < σ := by
    dsimp [σ, σ₆]
    positivity
  have hgap : σ < ζ := by
    dsimp [σ, ζ, σ₆, ζ₆]
    nlinarith [hαpos]
  have hζ : ζ < 1 := by
    dsimp [ζ, ζ₆]
    nlinarith [hαsmall]
  have h2σ : 2 * σ < 1 := by
    dsimp [σ, σ₆]
    nlinarith [hαsmall]
  have htopT : Tendsto (fun n : ℕ => (topScale n σ ζ : ℝ) / n) atTop (nhds 0) :=
    topScale_div_tendsto_zero hσ hgap hζ h2σ
  have htopSmall : ∀ᶠ n : ℕ in atTop,
      (topScale n σ ζ : ℝ) / n < 1 / 100000 :=
    htopT.eventually (Iio_mem_nhds (by norm_num))
  have hrootT : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hrootSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 1000 :=
    hrootT.eventually (Iio_mem_nhds (by norm_num))
  have hdecayT : Tendsto
      (fun n : ℕ => 10 * (n : ℝ) * Real.exp (-(1 / 100 : ℝ) * n)) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (1 / 100 : ℝ) (by norm_num)).comp tendsto_natCast_atTop_atTop
    simpa [Real.rpow_one, mul_assoc] using h.const_mul 10
  have hdecaySmall : ∀ᶠ n : ℕ in atTop,
      10 * (n : ℝ) * Real.exp (-(1 / 100 : ℝ) * n) < 1 :=
    hdecayT.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [htopSmall, hrootSmall, Filter.eventually_ge_atTop (100000 : ℕ),
    hdecaySmall] with n htop hroot hn hdecay
  intro N E G M X v
  have hnNat : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnNat
  have hnearCast : (separationRadius X : ℝ) =
      2 * (X.hp.r : ℝ) + 8 * (X.hp.Rlong : ℝ) + 100 := by
    rw [separationRadius]
    push_cast
    ring
  have hfloor : (X.hp.r : ℝ) ≤ (1 / 100 : ℝ) * n := by
    change ((⌊(1 / 100 : ℝ) * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ _
    exact Nat.floor_le (by positivity)
  have hlongEq : (X.hp.Rlong : ℝ) = 20 * (topScale n σ ζ : ℝ) := by
    simp [Ctx6.hp, HDParams.Rlong, D₀₆, α, σ, ζ]
  have hlong : 8 * (X.hp.Rlong : ℝ) ≤ (2 / 1000 : ℝ) * n := by
    rw [hlongEq]
    have hT : (topScale n σ ζ : ℝ) < (n : ℝ) / 100000 := by
      calc
        (topScale n σ ζ : ℝ) < (1 / 100000 : ℝ) * n :=
          (div_lt_iff₀ hnR).mp htop
        _ = (n : ℝ) / 100000 := by ring
    nlinarith
  have h100 : (100 : ℝ) ≤ (1 / 1000 : ℝ) * n := by
    have hnRlarge : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hnear : (separationRadius X : ℝ) ≤ (24 / 1000 : ℝ) * n := by
    rw [hnearCast]
    have hresid : 2 * (X.hp.r : ℝ) ≤ (20 / 1000 : ℝ) * n := by
      nlinarith [hfloor]
    nlinarith [hresid, hlong, h100]
  have hoccupied : ((Finset.univ \ X.g.L.residual).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [residual_complement_eq_occupied]
    exact X.g.L.occupied_sublinear
  have hrootMul : (n : ℝ) ^ (-(1 / 2 : ℝ)) * n =
      (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * n =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 : ℝ) :=
        congrArg (fun x : ℝ => (n : ℝ) ^ (-(1 / 2 : ℝ)) * x) (Real.rpow_one (n : ℝ)).symm
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by congr 1 <;> norm_num
  have hoccupiedSmall :
      ((Finset.univ \ X.g.L.residual).card : ℝ) ≤ (1 / 1000 : ℝ) * n := by
    calc
      ((Finset.univ \ X.g.L.residual).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hoccupied
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) * n := hrootMul.symm
      _ ≤ (1 / 1000 : ℝ) * n :=
        mul_le_mul_of_nonneg_right hroot.le (Nat.cast_nonneg _)
  let R : ℕ := separationRadius X + (Finset.univ \ X.g.L.residual).card
  have hRreal : ((R : ℝ) / n) ≤ 1 / 40 := by
    have hsum : (R : ℝ) ≤ (1 / 40 : ℝ) * n := by
      dsimp [R]
      rw [Nat.cast_add]
      nlinarith [hnear, hoccupiedSmall]
    exact (div_le_iff₀ hnR).2 hsum
  have hRle : (R : ℝ) ≤ (1 / 40 : ℝ) * n := (div_le_iff₀ hnR).mp hRreal
  have hRtwice : (2 : ℝ) * (R : ℝ) ≤ n := by
    nlinarith [hRle]
  have hRtwiceNat : 2 * R ≤ n := by exact_mod_cast hRtwice
  have hRnat : R ≤ n / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by simpa [Nat.mul_comm] using hRtwiceNat)
  have hvolume : ((Finset.univ.filter fun w : CubeVertex n =>
      X.g.L.residualDist v w ≤ separationRadius X).card : ℝ) ≤ Real.exp ((13 / 100 : ℝ) * n) :=
    residual_near_volume_bound hnNat X.g.L v (separationRadius X) hRreal hRnat
  have hlog2 : 69 / 100 < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  have hpow2 : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hexpProduct :
      Real.exp (-(56 / 100 : ℝ) * n) * (2 : ℝ) ^ n =
        Real.exp ((Real.log 2 - 56 / 100) * n) := by
    rw [hpow2, ← Real.exp_add]
    congr 1
    ring
  have hexpBound : Real.exp ((13 / 100 : ℝ) * n) ≤
      Real.exp (-(56 / 100 : ℝ) * n) * (2 : ℝ) ^ n := by
    rw [hexpProduct]
    apply Real.exp_le_exp.mpr
    have hcoeff : (13 / 100 : ℝ) ≤ Real.log 2 - 56 / 100 := by linarith
    exact mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
  have hcardCube : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by simp
  refine ⟨?_, ?_⟩
  · calc
      ((Finset.univ.filter fun w : CubeVertex n =>
        X.g.L.residualDist v w ≤ separationRadius X).card : ℝ) ≤ Real.exp ((13 / 100 : ℝ) * n) :=
        hvolume
      _ ≤ Real.exp (-(56 / 100 : ℝ) * n) * (Fintype.card (CubeVertex n) : ℝ) := by
        rw [hcardCube]
        exact hexpBound
  · have hdecay' : 10 * (n : ℝ) * Real.exp (-(1 / 100 : ℝ) * n) < 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdecay
    calc
      (n : ℝ) * Real.exp (-(56 / 100 : ℝ) * n) *
          (10 * Real.exp ((55 / 100 : ℝ) * n)) =
        10 * (n : ℝ) * Real.exp (-(1 / 100 : ℝ) * n) := by
          calc
            _ = 10 * (n : ℝ) *
                (Real.exp (-(56 / 100 : ℝ) * n) *
                  Real.exp ((55 / 100 : ℝ) * n)) := by ring
            _ = 10 * (n : ℝ) * Real.exp (-(1 / 100 : ℝ) * n) := by rw [← Real.exp_add]; congr 1 <;> ring
      _ ≤ 1 := hdecay'.le

noncomputable def oddStar (v : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter fun u => ¬ IsEvenRole u ∧ (cube n).Adj v u

theorem residualDist_le_hammingDist (X : Ctx6 γ p₀ K n N E G M) (v w : CubeVertex n) :
    X.g.L.residualDist v w ≤ _root_.hammingDist v w := by
  unfold ChunkLayout6.residualDist _root_.hammingDist
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨_, hd⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩

theorem pow_two_dominates_100 {q : ℕ} (hq : 10 ≤ q) : 100 * q ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      calc
        100 * (q + 1) ≤ 2 * (100 * q) := by omega
        _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

theorem natSquare_le_powTwo_point025_eventually :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := (1 / 40 : ℝ) * Real.log 2
  have hc : 0 < c := mul_pos (by norm_num) hlog2
  have hsmallT : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-c * n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) c hc).comp
        tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 * Real.exp (-c * n) < 1 :=
    hsmallT.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℕ)] with n hsmall hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpow : ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) = Real.exp (c * n) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    dsimp [c]
    ring
  have hexpCancel : Real.exp (-c * n) * Real.exp (c * n) = 1 := by
    rw [← Real.exp_add, show -c * (n : ℝ) + c * n = 0 by ring, Real.exp_zero]
  have hsmall' : (n : ℝ) ^ 2 < Real.exp (c * n) := by
    calc
      (n : ℝ) ^ 2 = (n : ℝ) ^ 2 *
          (Real.exp (-c * n) * Real.exp (c * n)) := by rw [hexpCancel, mul_one]
      _ = ((n : ℝ) ^ 2 * Real.exp (-c * n)) * Real.exp (c * n) := by ring
      _ < 1 * Real.exp (c * n) := mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
      _ = Real.exp (c * n) := by ring
  rw [hpow]
  exact hsmall'.le

theorem residualDist_comm (X : Ctx6 γ p₀ K n N E G M) (v w : CubeVertex n) :
    X.g.L.residualDist v w = X.g.L.residualDist w v := by
  change (X.g.L.residual.filter (fun a => v a ≠ w a)).card =
    (X.g.L.residual.filter (fun a => w a ≠ v a)).card
  apply congrArg (fun s : Finset (Fin n) => s.card)
  ext a
  simp [ne_comm]

theorem oddStar_card_le (X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n) (hn : 0 < n) :
    (oddStar (n := n) v).card ≤ n := by
  let adj : Finset (CubeVertex n) := Finset.univ.filter fun u => (cube n).Adj v u
  have hsub : oddStar (n := n) v ⊆ adj := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2⟩
  calc
    (oddStar (n := n) v).card ≤ adj.card := Finset.card_le_card hsub
    _ ≤ n := Lane_q_s06_even.adjacent_card_le_dimension_even v hn

theorem oddStar_disjoint_of_residualDist (X : Ctx6 γ p₀ K n N E G M)
    (v w : CubeVertex n) (hvw : 2 < X.g.L.residualDist v w) :
    Disjoint (oddStar (n := n) v) (oddStar (n := n) w) := by
  rw [Finset.disjoint_left]
  intro u huv huw
  have hadj₁ : (cube n).Adj v u := (Finset.mem_filter.mp huv).2.2
  have hadj₂ : (cube n).Adj w u := (Finset.mem_filter.mp huw).2.2
  have hdist₁ : _root_.hammingDist v u = 1 := hadj₁
  have hdist₂ : _root_.hammingDist w u = 1 := hadj₂
  have hdist₂' : _root_.hammingDist u w = 1 := by
    rw [_root_.hammingDist_comm u w]
    exact hdist₂
  have htri := _root_.hammingDist_triangle v u w
  have hdist : _root_.hammingDist v w ≤ 2 := by omega
  have := residualDist_le_hammingDist X v w
  omega

/-- Under a product law, a finite product of functions on pairwise disjoint coordinate sets has a factored mean. -/
theorem pi_expect_finset_prod_disjoint {ι ξ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ξ] [DecidableEq ξ] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ξ)
    (f : ξ → (∀ i, Ω i) → ℝ) (scope : ξ → Finset ι)
    (hf : ∀ j, FinProb.DependsOn (f j) (scope j))
    (hdisj : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (scope j) (scope k)) :
    (FinProb.pi P).expect (fun ω => ∏ j ∈ s, f j ω) =
      ∏ j ∈ s, (FinProb.pi P).expect (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect, (FinProb.pi P).sum_eq_one]
  | @insert j s hj ih =>
      let otherScope := s.biUnion scope
      have hOther : FinProb.DependsOn (fun ω => ∏ k ∈ s, f k ω) otherScope := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro k hk
        apply hf k
        intro i hi
        exact hagree i (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)
      have hSeparate : Disjoint (scope j) otherScope := by
        rw [Finset.disjoint_left]
        intro i hi hrest
        rcases Finset.mem_biUnion.mp hrest with ⟨k, hk, hik⟩
        have hjk : j ≠ k := by
          intro heq
          subst k
          exact hj hk
        exact (Finset.disjoint_left.mp
          (hdisj j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hjk)) hi hik
      have hdisjS : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Disjoint (scope k) (scope l) := by
        intro k hk l hl hkl
        exact hdisj k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl
      calc
        (FinProb.pi P).expect (fun ω => ∏ k ∈ insert j s, f k ω) =
            (FinProb.pi P).expect (fun ω => f j ω * ∏ k ∈ s, f k ω) := by
          congr 1
          funext ω
          rw [Finset.prod_insert hj]
        _ = (FinProb.pi P).expect (f j) *
              (FinProb.pi P).expect (fun ω => ∏ k ∈ s, f k ω) :=
          FinProb.pi_expect_mul_of_disjoint P (f j) (fun ω => ∏ k ∈ s, f k ω)
            (scope j) otherScope (hf j) hOther hSeparate
        _ = ∏ k ∈ insert j s, (FinProb.pi P).expect (f k) := by
          rw [ih hdisjS]
          rw [Finset.prod_insert hj]

theorem expect_le_of_atomBound {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (P : FinProb Ω) (f : Ω → α) (g q : α → ℝ)
    (hg : ∀ a, 0 ≤ g a)
    (hAtom : ∀ a, P.pr (fun ω => f ω = a) ≤ q a) :
    P.expect (fun ω => g (f ω)) ≤ ∑ a, q a * g a := by
  classical
  have hmass (a : α) : (FinProb.map P f).w a = P.pr (fun ω => f ω = a) := by
    unfold FinProb.map FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : f ω = a <;> simp [h]
  calc
    P.expect (fun ω => g (f ω)) = (FinProb.map P f).expect g :=
      (FinProb.map_expect P f g).symm
    _ = ∑ a, (FinProb.map P f).w a * g a := rfl
    _ ≤ ∑ a, q a * g a := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_right _ (hg a)
      rw [hmass]
      exact hAtom a

end HypercubeRamsey.S06.Lane_q_s06_ev_d
