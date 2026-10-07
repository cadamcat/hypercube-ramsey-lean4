import HypercubeRamsey.S05.Centres_sol_s05_centres

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical Filter Real OAI.HypercubeRamsey
open scoped BigOperators Topology

set_option maxHeartbeats 400000
noncomputable section
variable {γ K' χ : ℝ}

def loadRequest : ParamReq5 where
  Kcap _ := 0
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 _ := 0
  KD _ := 0
  Ks _ := 0
  KB _ := 0
  alpha x := 1 / (100 * (|x.1.1.2| + 1))
  alpha_pos x := by positivity

theorem high_budget (p : Params5 γ K' χ) (hp : loadRequest.Holds p) :
    2 * p.KD * p.alpha ≤ 1 / 50 := by
  have ha : p.alpha ≤ 1 / (100 * (p.KD + 1)) := by
    simpa [loadRequest, Params5.pre6, Params5.pre5, Params5.pre4,
      abs_of_pos p.hKD] using hp.2.2.2.2.2.2.2.2
  have hden : 0 < 100 * (p.KD + 1) := by have := p.hKD; positivity
  have hmul := (le_div_iff₀ hden).1 ha
  nlinarith [p.halpha.1]

theorem log_m_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 < p.m n ∧
      log (p.m n : ℝ) ≤ 2 * p.alpha * log (n : ℝ) := by
  have hlogTop : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop (log 2 / p.alpha),
    (Lane_sol_s05_h1.tendsto_m p).eventually_gt_atTop 1, eventually_ge_atTop (1 : ℕ)]
    with n hl hm hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hpow : 1 ≤ (n : ℝ) ^ p.alpha := one_le_rpow hnR p.halpha.1.le
  have hmupper : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ p.alpha := by
    have hh := Nat.ceil_lt_add_one (rpow_nonneg hnpos.le p.alpha)
    change (⌈(n : ℝ) ^ p.alpha⌉₊ : ℝ) ≤ _
    linarith
  have hh := log_le_log (by linarith : (0 : ℝ) < p.m n) hmupper
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), log_rpow hnpos] at hh
  have hsmall := (div_le_iff₀ p.halpha.1).1 hl
  refine ⟨hn, by exact_mod_cast hm, ?_⟩
  linarith

theorem high_fraction_eventually (p : Params5 γ K' χ) (hp : loadRequest.Holds p) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ p.J n ∧ p.J n + 1 ≤ p.m n ∧ 0 < p.s n ∧
      8 * exp (p.DH n) * (n : ℝ) ^ (-(13 / 100 : ℝ) * (p.J n + 1)) ≤ 1 := by
  have hmTop := Lane_sol_s05_h1.tendsto_m p
  have hjTop : Tendsto (fun n : ℕ => (p.m n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hmTop
  have hTail : ∀ᶠ n : ℕ in atTop, 8 * (n : ℝ) ^ (-(11 / 100 : ℝ)) ≤ 1 := by
    have h : Tendsto (fun n : ℕ => 8 * (n : ℝ) ^ (-(11 / 100 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using
        ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp
          tendsto_natCast_atTop_atTop).const_mul 8
    simpa using h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)) |>.mono (fun _ h => h.le)
  filter_upwards [log_m_eventually p, hjTop.eventually_ge_atTop 2, hTail,
    hmTop.eventually_ge_atTop 4] with n hlog hpow htail hm4
  obtain ⟨hn, hm, hlogm⟩ := hlog
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  have hJ : 1 ≤ p.J n := by
    have hh : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh' : (1 : ℝ) < p.J n := by linarith
    exact_mod_cast hh'.le
  have hJm : p.J n + 1 ≤ p.m n := by
    have hM : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm.le
    have hpw : (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ (p.m n : ℝ) / 2 := by
      have hb : (2 : ℝ) ≤ (p.m n : ℝ) ^ (19 / 20 : ℝ) := by
        have hs : (2 : ℝ) ≤ (p.m n : ℝ) ^ (1 / 2 : ℝ) := by
          calc
            (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by norm_num [← sqrt_eq_rpow]
            _ ≤ _ := rpow_le_rpow (by norm_num) hm4 (by norm_num)
        exact hs.trans (rpow_le_rpow_of_exponent_le hM (by norm_num))
      have heq : (p.m n : ℝ) ^ (1 / 20 : ℝ) * (p.m n : ℝ) ^ (19 / 20 : ℝ) = p.m n := by
        rw [← rpow_add (by positivity)]
        norm_num
      have h0 : 0 ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith [mul_le_mul_of_nonneg_left hb h0]
    have hfloor : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)
    have hh : (p.J n : ℝ) + 1 ≤ p.m n := by linarith
    exact_mod_cast hh
  have hs : 0 < p.s n := by
    have hraw : 0 < p.Ks * (p.J n : ℝ) * log (p.m n : ℝ) :=
      mul_pos (mul_pos p.hKs (by exact_mod_cast (show 0 < p.J n by omega)))
        (log_pos (by exact_mod_cast hm))
    exact_mod_cast hraw.trans_le (Nat.le_ceil _)
  refine ⟨hJ, hJm, hs, ?_⟩
  have hdh : p.DH n ≤ (1 / 50 : ℝ) * (p.J n : ℝ) * log (n : ℝ) := by
    unfold Params5.DH
    have hh := mul_le_mul_of_nonneg_left hlogm (mul_nonneg p.hKD.le (Nat.cast_nonneg (p.J n)))
    have hh' := mul_le_mul_of_nonneg_right (high_budget p hp)
      (mul_nonneg (Nat.cast_nonneg (p.J n)) hln)
    nlinarith only [hh, hh']
  have hexp : exp (p.DH n) * (n : ℝ) ^ (-(13 / 100 : ℝ) * (p.J n + 1)) ≤
      (n : ℝ) ^ (-(11 / 100 : ℝ)) := by
    rw [rpow_def_of_pos hnpos, ← exp_add, rpow_def_of_pos hnpos]
    apply exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (p.J n) : (0 : ℝ) ≤ p.J n) hln]
  calc
    _ = 8 * (exp (p.DH n) * (n : ℝ) ^ (-(13 / 100 : ℝ) * (p.J n + 1))) := by ring
    _ ≤ 8 * (n : ℝ) ^ (-(11 / 100 : ℝ)) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 1 := htail

theorem sublinear_power_eventually (e c : ℝ) (he : e < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ e ≤ c * n := by
  have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr he)).comp
    tendsto_natCast_atTop_atTop).eventually (Iio_mem_nhds hc)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (n : ℝ) ^ e = (n : ℝ) ^ (-(1 - e)) * n := by
      calc
        _ = (n : ℝ) ^ (-(1 - e) + 1) := by congr 1; ring
        _ = (n : ℝ) ^ (-(1 - e)) * (n : ℝ) ^ (1 : ℝ) := rpow_add hnpos _ _
        _ = _ := by rw [rpow_one]
    _ ≤ c * n := mul_le_mul_of_nonneg_right hn.le (Nat.cast_nonneg _)

theorem row_caps_sublinear (p : Params5 γ K' χ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, p.DL n ≤ c * n ∧ p.DH n ≤ c * n := by
  let CL : ℝ := 2 ^ (15 / 100 : ℝ)
  let CH : ℝ := p.KD * 2 ^ (1 / 20 : ℝ) * (2 * p.alpha)
  have hCL : 0 < CL := by dsimp [CL]; positivity
  have hCH : 0 < CH := by have := p.hKD; have := p.halpha.1; dsimp [CH]; positivity
  have heL : p.alpha * (15 / 100 : ℝ) < 1 := by linarith [p.halpha.2]
  have heH : p.alpha * (1 / 20 : ℝ) + 1 / 2 < 1 := by linarith [p.halpha.2]
  have hlog : ∀ᶠ n : ℕ in atTop, log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hh := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hl0 : 0 ≤ log (n : ℝ) := log_nonneg hnR
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg hl0,
      abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) (1 / 2 : ℝ))] using hn
  filter_upwards [log_m_eventually p, hlog,
    sublinear_power_eventually (p.alpha * (15 / 100)) (c / CL) heL (div_pos hc hCL),
    sublinear_power_eventually (p.alpha * (1 / 20) + 1 / 2) (c / CH) heH (div_pos hc hCH)]
    with n hlogm hlogn hL hH
  obtain ⟨hn, hm, hlogm⟩ := hlogm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmupper : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ p.alpha := by
    have hpow : 1 ≤ (n : ℝ) ^ p.alpha := one_le_rpow (by exact_mod_cast hn) p.halpha.1.le
    have hh := Nat.ceil_lt_add_one (rpow_nonneg hnpos.le p.alpha)
    change (⌈(n : ℝ) ^ p.alpha⌉₊ : ℝ) ≤ _
    linarith
  have hpower (e : ℝ) (he : 0 ≤ e) : (p.m n : ℝ) ^ e ≤ 2 ^ e * (n : ℝ) ^ (p.alpha * e) := by
    calc
      _ ≤ (2 * (n : ℝ) ^ p.alpha) ^ e := rpow_le_rpow (Nat.cast_nonneg _) hmupper he
      _ = _ := by rw [mul_rpow (by norm_num) (rpow_nonneg hnpos.le _), ← rpow_mul hnpos.le]
  constructor
  · calc
      p.DL n ≤ CL * (n : ℝ) ^ (p.alpha * (15 / 100)) := hpower _ (by norm_num)
      _ ≤ CL * ((c / CL) * n) := mul_le_mul_of_nonneg_left hL hCL.le
      _ = c * n := by field_simp
  · have hJ : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)
    have hlog0 : 0 ≤ log (p.m n : ℝ) := log_nonneg (by exact_mod_cast hm.le)
    have hln0 : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
    calc
      p.DH n ≤ p.KD * (2 ^ (1 / 20 : ℝ) * (n : ℝ) ^ (p.alpha * (1 / 20))) *
          (2 * p.alpha * (n : ℝ) ^ (1 / 2 : ℝ)) := by
        unfold Params5.DH
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hJ.trans (hpower _ (by norm_num))) p.hKD.le
        · exact hlogm.trans (mul_le_mul_of_nonneg_left hlogn (mul_nonneg (by norm_num) p.halpha.1.le))
        · exact hlog0
        · exact mul_nonneg p.hKD.le (mul_nonneg (by positivity) (rpow_nonneg hnpos.le _))
      _ = CH * (n : ℝ) ^ (p.alpha * (1 / 20) + 1 / 2) := by
        rw [rpow_add hnpos]
        dsimp [CH]
        ring
      _ ≤ CH * ((c / CH) * n) := mul_le_mul_of_nonneg_left hH hCH.le
      _ = c * n := by field_simp

theorem scope_radius_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      2 * (p.rho * n) + 2 * (n : ℝ) ^ (1 - 9 * p.alpha / 4000000) +
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (p.rho + 1 / 4) * n := by
  let c : ℝ := (1 / 4 - p.rho) / 3
  have hc : 0 < c := by dsimp [c]; linarith [p.hrho.2]
  filter_upwards [sublinear_power_eventually (1 - 9 * p.alpha / 4000000) c
    (by linarith [p.halpha.1]) hc,
    sublinear_power_eventually (1 / 2) c (by norm_num) hc] with n h1 h2
  dsimp [c] at h1 h2
  linarith

theorem near_cap_eventually (p : Params5 γ K' χ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (2 * exp (-c * n)) * (exp (p.DL n) + 4 * exp (p.DH n)) ≤ 1 := by
  have ht : Tendsto (fun n : ℕ => 10 * ((n : ℝ) * exp (-(3 * c / 4) * n))) atTop (𝓝 0) := by
    simpa only [rpow_one, mul_zero, Function.comp_apply] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3 * c / 4) (by positivity)).comp
        tendsto_natCast_atTop_atTop).const_mul 10
  filter_upwards [row_caps_sublinear p (c / 4) (by positivity),
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn ht
  have hcap : exp (p.DL n) + 4 * exp (p.DH n) ≤ 5 * exp (c / 4 * n) := by
    have h1 := exp_le_exp.mpr hn.1
    have h2 := exp_le_exp.mpr hn.2
    linarith
  calc
    _ ≤ (n : ℝ) * (2 * exp (-c * n)) * (5 * exp (c / 4 * n)) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = 10 * ((n : ℝ) * exp (-(3 * c / 4) * n)) := by
      rw [show (n : ℝ) * (2 * exp (-c * n)) * (5 * exp (c / 4 * n)) =
        10 * n * (exp (-c * n) * exp (c / 4 * n)) by ring, ← exp_add]
      rw [show -c * (n : ℝ) + c / 4 * n = -(3 * c / 4) * n by ring]
      ring
    _ ≤ 1 := ht.le

theorem high_role_mean_bound (p : Params5 γ K' χ) {n : ℕ} (hn : 0 < n)
    (g : ChunkGeometry5 n (p.m n)) (hG : ChunkEstimates5 g)
    (hJ : p.J n + 1 ≤ p.m n)
    (htail : 8 * exp (p.DH n) * (n : ℝ) ^ (-(13 / 100 : ℝ) * (p.J n + 1)) ≤ 1) :
    (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
      ∑ r : OddRole5 n, (if ¬ g.low (p.J n) r.1 then 4 * exp (p.DH n) else 0) ≤ 1 := by
  let A : Finset (OddRole5 n) := Finset.univ.filter fun r => ¬ g.low (p.J n) r.1
  let B : Finset (CubeVertex n) := Finset.univ.filter fun v => p.J n + 1 ≤ g.severity v
  have hcard : A.card ≤ B.card := by
    rw [← Finset.card_image_of_injective A Subtype.val_injective]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hh := (Finset.mem_filter.mp hr).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold ChunkGeometry5.low at hh
    omega
  have hsum : (∑ r : OddRole5 n, (if ¬ g.low (p.J n) r.1 then 4 * exp (p.DH n) else 0)) =
      (A.card : ℝ) * (4 * exp (p.DH n)) := by
    rw [← Finset.sum_filter]
    simp [A, nsmul_eq_mul]
  have hodd : 2 * (Fintype.card (OddRole5 n) : ℝ) = (2 : ℝ) ^ n := by
    rw [odd_card n hn]
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  have hoddpos : (0 : ℝ) < Fintype.card (OddRole5 n) := by
    rw [odd_card n hn]
    positivity
  have hfrac := hG.severity_tail (p.J n + 1) (by omega) hJ
  change (B.card : ℝ) / (2 : ℝ) ^ n ≤ _ at hfrac
  push_cast at hfrac
  rw [hsum]
  calc
    _ ≤ (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ((B.card : ℝ) * (4 * exp (p.DH n))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)) (by positivity)
    _ = 8 * exp (p.DH n) * ((B.card : ℝ) / (2 : ℝ) ^ n) := by
      rw [← hodd]
      field_simp
      <;> ring
    _ ≤ 8 * exp (p.DH n) * (n : ℝ) ^ (-(13 / 100 : ℝ) * (p.J n + 1)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ ≤ 1 := htail

end
end HypercubeRamsey.Lane_sol_s05_centres
