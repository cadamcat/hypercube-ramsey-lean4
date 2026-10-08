import HypercubeRamsey.S18.Nodes_sol_s18_2lm_witnesses

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.Parameters

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def sizeBound (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  (8 * κ.A0 + 1) * Real.log (T.S.n k : ℝ) ^ 2
noncomputable def cutoff (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.exp (-κ.α * T.S.n k / 8)
noncomputable def additive (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 4))
noncomputable def patchWidth (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.log 400 + (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι
noncomputable def profileWidth (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.log 11 + patchWidth κ T k
noncomputable def discrepancyError (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  4 * Real.exp (patchWidth κ T k - Real.rpow (T.S.n k : ℝ) κ.xs)
noncomputable def windowError (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 2))
noncomputable def rawError (κ : CConsts) (T : Stage) (k : ℕ) : ℝ :=
  Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 4))

structure Valid (κ : CConsts) (T : Stage) (k : ℕ) : Prop where
  n_one : 1 ≤ (T.S.n k : ℝ)
  log_four : 4 ≤ Real.log (T.S.n k : ℝ)
  KB_large : 512 ≤ κ.KB
  tuple_density : ∀ m : ℕ, (m : ℝ) ≤ sizeBound κ T k →
    (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m ≤ Real.exp 1
  width_margin : profileWidth κ T k + 1 ≤ κ.α * T.S.n k / 4
  pair_slack : Real.log 4 ≤ κ.α * T.S.n k / 2
  bstar_small : bstar T k ≤ 1 / 16
  additive_small : ∀ m : ℕ, (m : ℝ) ≤ sizeBound κ T k →
    additive κ T k * (4 : ℝ) ^ m ≤ bstar T k
  window_exception : ∀ m : ℕ, (m : ℝ) ≤ sizeBound κ T k →
    m * (cutoff κ T k + discrepancyError κ T k) / additive κ T k ≤ windowError κ T k
  small_cylinder : Real.exp (Real.rpow (T.S.n k : ℝ) 0.4) * cutoff κ T k ≤ windowError κ T k
  raw_assembly : 6 * (T.S.n k : ℝ) * windowError κ T k ≤ rawError κ T k

theorem log_power_margin (T : Stage) (q : ℕ) (C b d : ℝ) (hb : 0 < b) (hd : 0 < d) :
    ∀ᶠ k in atTop, C * Real.log (T.S.n k : ℝ) ^ q ≤ b * Real.rpow (T.S.n k : ℝ) d := by
  filter_upwards [polylog_le_power_eventually T q (C / b) d hd] with k hk
  have h := mul_le_mul_of_nonneg_left hk hb.le
  have he : b * ((C / b) * Real.log (T.S.n k : ℝ) ^ q) = C * Real.log (T.S.n k : ℝ) ^ q := by
    field_simp
  rw [he] at h
  exact h

theorem valid_eventually {κ : CConsts} (hκ : κ.Admissible) (T : Stage) : ∀ᶠ k in atTop, Valid κ T k := by
  let M := 8 * κ.A0 + 1
  let C := 1 + |κ.a|
  have hA : 0 ≤ κ.A0 := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.A0_big
  have hKB : 0 ≤ κ.KB := (show (0 : ℝ) ≤ 10 ^ 6 * (κ.R : ℝ) by positivity).trans hκ.KB_big
  have hKBlarge : 512 ≤ κ.KB := by
    have hP : 1 ≤ κ.P := by have h := hκ.P_big.2; rw [hκ.Ac_eq] at h; omega
    have hR : (1 : ℝ) ≤ κ.R := by
      exact_mod_cast (show 1 ≤ κ.R by rw [hκ.R_eq]; exact Nat.one_le_pow _ _ hP)
    nlinarith [hκ.KB_big]
  have hx : 0 < κ.xs := hκ.xs_rng.1
  have hιxs : κ.ι < κ.xs := by
    have hi := hκ.ι_rng.2
    have hm := min_le_left κ.xs (min κ.η0 (0.01 : ℝ))
    linarith
  have hι1 : κ.ι < 1 := hιxs.trans (by linarith [hκ.xs_rng.2])
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hL := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 4
  have hM := polylog_le_power_eventually T 2 M 1 (by norm_num)
  have hKM := polylog_le_power_eventually T 2 (κ.KB * M) 1 (by norm_num)
  have hw := hn.eventually (Lane_sol_consts_adm.eventually_power_sum κ.ι 0 1 C 0
    (Real.log 11 + Real.log 400 + 1) (κ.α / 4) hι1 (by norm_num) (by norm_num) (by positivity [hκ.α_rng.1]))
  have hp := hn.eventually (Lane_sol_consts_adm.eventually_power_sum 0 0 1 0 0
    (Real.log 4) (κ.α / 2) (by norm_num) (by norm_num) (by norm_num) (by positivity [hκ.α_rng.1]))
  have hb := (polylog_bstar_tendsto T 0 1).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have ha := (barrier_error_tendsto T 0 2 (M * Real.log 4) (κ.xs / 8) (κ.xs / 4)
    (by positivity) (by linarith)).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hεp := hn.eventually (Lane_sol_consts_adm.eventually_power_sum (κ.xs / 4) (κ.xs / 2) 1
    1 1 (Real.log 2) (κ.α / 16) (by linarith [hκ.xs_rng.2]) (by linarith [hκ.xs_rng.2])
    (by norm_num) (by positivity [hκ.α_rng.1]))
  have hεL := log_power_margin T 1 1 (κ.α / 16) 1 (by positivity [hκ.α_rng.1]) (by norm_num)
  have hηp := hn.eventually (Lane_sol_consts_adm.eventually_power_sum κ.ι (κ.xs / 4) κ.xs C 1
    (Real.log 400 + Real.log 8) (1 / 2) hιxs (by linarith) hx (by norm_num))
  have hηq := hn.eventually (Lane_sol_consts_adm.eventually_power_bound (κ.xs / 2) κ.xs 1 (1 / 4)
    (by linarith) (by norm_num))
  have hηL := log_power_margin T 1 1 (1 / 4) κ.xs (by norm_num) hx
  have hSmall := hn.eventually (Lane_sol_consts_adm.eventually_power_sum 0.4 (κ.xs / 2) 1 1 1 0
    (κ.α / 8) (by norm_num) (by linarith [hκ.xs_rng.2]) (by norm_num) (by positivity [hκ.α_rng.1]))
  have hRaw := hn.eventually (Lane_sol_consts_adm.eventually_power_sum (κ.xs / 4) 0 (κ.xs / 2) 1 0
    (Real.log 6) (1 / 2) (by linarith) (by positivity) (by positivity) (by norm_num))
  have hRawL := log_power_margin T 1 1 (1 / 2) (κ.xs / 2) (by norm_num) (by positivity)
  filter_upwards [hn.eventually_ge_atTop 1, hL, hM, hKM, hw, hp, hb, ha,
    hεp, hεL, hηp, hηq, hηL, hSmall, hRaw, hRawL] with k hn1 hL hM hKM hw hp hb ha
      hεp hεL hηp hηq hηL hSmall hRaw hRawL
  simp only [Function.comp_def, Real.rpow_eq_pow, Real.rpow_one, Real.rpow_zero, pow_zero,
    pow_one, one_mul, mul_one, zero_mul, add_zero] at hn1 hL hM hKM hw hp hb ha hεp hεL hηp hηq hηL hSmall hRaw hRawL
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hMnon : 0 ≤ M := by dsimp [M]; positivity
  have hprofile : profileWidth κ T k + 1 ≤ κ.α * T.S.n k / 4 := by
    dsimp [profileWidth, patchWidth]
    dsimp [C] at hw
    nlinarith only [hw]
  have hslack : Real.log 4 ≤ κ.α * T.S.n k / 2 := by nlinarith only [hp]
  have hbstar : bstar T k ≤ 1 / 16 := hb.le
  have hcut : Real.log 2 + Real.log (T.S.n k : ℝ) + Real.rpow (T.S.n k : ℝ) (κ.xs / 4) +
      Real.rpow (T.S.n k : ℝ) (κ.xs / 2) ≤ κ.α * T.S.n k / 8 := by
    simp only [Real.rpow_eq_pow]
    nlinarith only [hεp, hεL]
  have hdisc : Real.log 8 + Real.log (T.S.n k : ℝ) + patchWidth κ T k +
      Real.rpow (T.S.n k : ℝ) (κ.xs / 4) + Real.rpow (T.S.n k : ℝ) (κ.xs / 2) ≤
        Real.rpow (T.S.n k : ℝ) κ.xs := by
    dsimp [patchWidth]
    dsimp [C] at hηp
    nlinarith only [hηp, hηq, hηL]
  refine ⟨hn1, hL, hKBlarge, ?_, hprofile, hslack, hbstar, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hmk : (m : ℝ) * κ.KB ≤ (T.S.n k : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hm hKB
      dsimp [sizeBound, M] at *
      nlinarith only [hh, hKM]
    have hnr : Real.rpow (T.S.n k : ℝ) (-3) ≤ (T.S.n k : ℝ)⁻¹ := by
      have hh := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-3 : ℝ) ≤ -1)
      simpa only [Real.rpow_eq_pow, Real.rpow_neg_one] using hh
    have hsmall : (m : ℝ) * (κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hnr (show 0 ≤ (m : ℝ) * κ.KB by positivity)
      have h2 := mul_le_mul_of_nonneg_right hmk (inv_nonneg.mpr hnpos.le)
      rw [mul_inv_cancel₀ hnpos.ne'] at h2
      nlinarith only [h1, h2]
    have hbase := Real.add_one_le_exp (κ.KB * Real.rpow (T.S.n k : ℝ) (-3))
    have hnr0 : 0 ≤ Real.rpow (T.S.n k : ℝ) (-3) := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_nonneg hnpos.le (-3)
    have hbase0 : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) :=
      add_nonneg (by norm_num) (mul_nonneg hKB hnr0)
    have hpow := pow_le_pow_left₀ hbase0
      (by simpa [add_comm] using hbase) m
    apply hpow.trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by simpa [Real.rpow_eq_pow] using hsmall)
  · intro m hm
    have hpow : (4 : ℝ) ^ m ≤ Real.exp (M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hm (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      dsimp [sizeBound, M] at *
      have he : (4 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 4) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      rw [he]
      exact Real.exp_le_exp.mpr (by nlinarith only [hh])
    have hneg : 0 ≤ Real.rpow (T.S.n k : ℝ) (κ.xs / 8) := Real.rpow_nonneg hnpos.le _
    have hreduce : (T.S.n k : ℝ) * Real.exp (M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2 -
        Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) ≤ 1 := by
      have he := Real.exp_le_exp.mpr (show M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2 -
          Real.rpow (T.S.n k : ℝ) (κ.xs / 4) ≤ M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2 +
          2 * Real.rpow (T.S.n k : ℝ) (κ.xs / 8) - Real.rpow (T.S.n k : ℝ) (κ.xs / 4) by linarith)
      have hmul := mul_le_mul_of_nonneg_left he hnpos.le
      simp only [Real.rpow_eq_pow] at hmul
      exact hmul.trans ha.le
    have hexp : Real.exp (M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2 -
        Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) ≤ (T.S.n k : ℝ)⁻¹ := by
      rw [← one_div (T.S.n k : ℝ)]
      apply (le_div_iff₀ hnpos).mpr
      simpa [one_div, mul_comm] using hreduce
    have hroot : (T.S.n k : ℝ)⁻¹ ≤ bstar T k := by
      have hh := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1 + 0.04)
      simpa only [bstar, Real.rpow_neg_one] using hh
    calc
      _ ≤ additive κ T k * Real.exp (M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (M * Real.log 4 * Real.log (T.S.n k : ℝ) ^ 2 - Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) := by
        unfold additive; rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp.trans hroot
  · intro m hm
    have hmn : (m : ℝ) ≤ (T.S.n k : ℝ) := hm.trans (by simpa [sizeBound, M, Real.rpow_one] using hM)
    have hε : (T.S.n k : ℝ) * cutoff κ T k / additive κ T k ≤ windowError κ T k / 2 := by
      have he : (T.S.n k : ℝ) * cutoff κ T k / additive κ T k =
          Real.exp (Real.log (T.S.n k : ℝ) - κ.α * T.S.n k / 8 + Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) := by
        unfold cutoff additive
        nth_rw 1 [← Real.exp_log hnpos]
        rw [← Real.exp_add, ← Real.exp_sub]
        congr 1; ring
      rw [he]
      have hr : windowError κ T k / 2 = Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 2) - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; rfl
      rw [hr]
      exact Real.exp_le_exp.mpr (by linarith only [hcut])
    have hη : (T.S.n k : ℝ) * discrepancyError κ T k / additive κ T k ≤ windowError κ T k / 2 := by
      have he : (T.S.n k : ℝ) * discrepancyError κ T k / additive κ T k =
          Real.exp (Real.log 4 + Real.log (T.S.n k : ℝ) + patchWidth κ T k -
            Real.rpow (T.S.n k : ℝ) κ.xs + Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) := by
        unfold discrepancyError additive
        nth_rw 1 [← Real.exp_log hnpos]
        nth_rw 1 [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1; ring
      rw [he]
      have hr : windowError κ T k / 2 = Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 2) - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; rfl
      rw [hr]
      apply Real.exp_le_exp.mpr
      have hlog8 : Real.log 8 = Real.log 4 + Real.log 2 := by
        rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
      linarith only [hdisc, hlog8]
    have hmono := mul_le_mul_of_nonneg_right hmn (show 0 ≤
      (cutoff κ T k + discrepancyError κ T k) / additive κ T k by
        unfold cutoff discrepancyError additive; positivity)
    have hsum : (T.S.n k : ℝ) * ((cutoff κ T k + discrepancyError κ T k) / additive κ T k) =
        (T.S.n k : ℝ) * cutoff κ T k / additive κ T k +
          (T.S.n k : ℝ) * discrepancyError κ T k / additive κ T k := by ring
    rw [hsum] at hmono
    have hm' : m * (cutoff κ T k + discrepancyError κ T k) / additive κ T k =
        (m : ℝ) * ((cutoff κ T k + discrepancyError κ T k) / additive κ T k) := by ring
    rw [hm']
    nlinarith only [hmono, hε, hη]
  · unfold cutoff windowError
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.rpow_eq_pow]
    nlinarith only [hSmall]
  · have he : 6 * (T.S.n k : ℝ) * windowError κ T k =
        Real.exp (Real.log 6 + Real.log (T.S.n k : ℝ) - Real.rpow (T.S.n k : ℝ) (κ.xs / 2)) := by
      unfold windowError
      nth_rw 1 [← Real.exp_log (by norm_num : (0 : ℝ) < 6)]
      nth_rw 1 [← Real.exp_log hnpos]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring
    rw [he]
    unfold rawError
    apply Real.exp_le_exp.mpr
    simp only [Real.rpow_eq_pow]
    nlinarith only [hRaw, hRawL]

end HypercubeRamsey.S18.Lane_sol_s18_2lm.Parameters
