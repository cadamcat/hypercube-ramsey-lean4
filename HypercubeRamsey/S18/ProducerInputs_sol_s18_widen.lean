import HypercubeRamsey.S14.Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds

namespace HypercubeRamsey.S18.Lane_sol_s18_widen

open Filter
open scoped BigOperators Topology

theorem power_dominates (C c p q : ℝ) (hc : 0 < c) (hpq : p < q) :
    ∀ᶠ x : ℝ in atTop, C * x ^ p ≤ c * x ^ q := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually_ge_atTop (C / c),
    eventually_ge_atTop (1 : ℝ)] with x hgap hx
  have hx0 : 0 < x := by linarith
  have hC : C ≤ c * x ^ (q - p) := by simpa [mul_comm] using (div_le_iff₀ hc).mp hgap
  calc
    C * x ^ p ≤ (c * x ^ (q - p)) * x ^ p :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ = c * x ^ q := by rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring

theorem power_log_dominates (C c p q : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hpq : p < q) :
    ∀ᶠ x : ℝ in atTop, C * x ^ p * Real.log x ≤ c * x ^ q := by
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hpq)).bound
    (show 0 < c / (C + 1) by positivity)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with x hlog hx
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg hx0.le (q - p))] at hlog
  have hcoeff : C * (c / (C + 1)) ≤ c := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (show 0 < C + 1 by linarith)).mpr (by nlinarith)
  calc
    C * x ^ p * Real.log x ≤ C * x ^ p * ((c / (C + 1)) * x ^ (q - p)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hC (Real.rpow_nonneg hx0.le _))
    _ = (C * (c / (C + 1))) * x ^ q := by
      rw [show C * x ^ p * ((c / (C + 1)) * x ^ (q - p)) =
        (C * (c / (C + 1))) * (x ^ p * x ^ (q - p)) by ring,
        ← Real.rpow_add hx0]
      congr 2
      ring
    _ ≤ c * x ^ q := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hx0.le _)

theorem stretched_decay (C p c q e : ℝ) (hc : 0 < c) (hq : 0 < q) (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, C * x ^ p * Real.exp (-c * x ^ q) ≤ e := by
  have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / q) c hc).comp
    (tendsto_rpow_atTop hq)).const_mul C
  have ht' : Tendsto (fun x : ℝ => C * x ^ p * Real.exp (-c * x ^ q))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun x : ℝ => C * ((x ^ q) ^ (p / q) * Real.exp (-c * x ^ q)))
      atTop (𝓝 0) by simpa only [Function.comp_apply, mul_zero] using ht).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.rpow_mul (by linarith : 0 ≤ x),
      show q * (p / q) = p by field_simp]
    ring
  exact ht'.eventually (eventually_le_nhds he)

theorem polynomial_exp_bound (C p c q : ℝ) (hc : 0 < c) (hq : 0 < q) :
    ∀ᶠ x : ℝ in atTop, C * x ^ p ≤ Real.exp (c * x ^ q) := by
  filter_upwards [stretched_decay C p c q 1 hc hq (by norm_num)] with x hx
  have hh := mul_le_mul_of_nonneg_right hx (Real.exp_pos (c * x ^ q)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
    one_mul, neg_mul, neg_add_cancel] using hh

theorem exp_power_bound (C c r s : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hs : 0 < s) (hrs : s < r) :
    ∀ᶠ x : ℝ in atTop,
      C * Real.exp (-c * x ^ r) ≤ Real.exp (-x ^ s) := by
  filter_upwards [power_dominates 1 (c / 2) s r (by positivity) hrs,
    stretched_decay C 0 (c / 2) r 1 (by positivity) (lt_trans hs hrs) (by norm_num)]
    with x hpower hdecay
  simp only [Real.rpow_zero, mul_one, one_mul] at hdecay hpower
  have h := mul_le_mul_of_nonneg_right hdecay (Real.exp_pos (-x ^ s)).le
  calc
    C * Real.exp (-c * x ^ r) ≤
        C * Real.exp (-(c / 2) * x ^ r - x ^ s) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (C * Real.exp (-(c / 2) * x ^ r)) * Real.exp (-x ^ s) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ ≤ Real.exp (-x ^ s) := by simpa using h

theorem ceil_power_bounds {x p : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) :
    x ^ p ≤ (⌈x ^ p⌉₊ : ℝ) ∧ (⌈x ^ p⌉₊ : ℝ) ≤ 2 * x ^ p := by
  have hpow : 1 ≤ x ^ p := Real.one_le_rpow hx hp
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ p)).le.trans
    (by linarith)⟩

private theorem first_scale_le (M R target : ℕ) (hex : ∃ i : ℕ, target ≤ M ^ i * R) :
    M ^ Nat.find hex * R ≤ max R (M * target) := by
  cases hi : Nat.find hex with
  | zero => simp [hi]
  | succ i =>
    have hbefore : M ^ i * R < target := by
      apply Nat.lt_of_not_ge
      apply Nat.find_min hex
      rw [hi]
      exact Nat.lt_succ_self i
    calc
      M ^ (i + 1) * R = M * (M ^ i * R) := by rw [pow_succ]; ring
      _ ≤ M * target := Nat.mul_le_mul_left _ hbefore.le
      _ ≤ max R (M * target) := le_max_right _ _

theorem topScale_power_bound (σ ζ : ℝ) (hσ : 0 < σ) (hζ : ζ < 1) :
    ∀ᶠ n : ℕ in atTop,
      (topScale n σ ζ : ℝ) ≤ 4 * (n : ℝ) ^ (1 - ζ + σ) := by
  have hp : 0 < 1 - ζ + σ := by linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 hp).bound (by norm_num : (0 : ℝ) < 1)
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hncast.eventually hlog, hncast.eventually (eventually_ge_atTop (1 : ℝ)),
    hncast.eventually ((tendsto_rpow_atTop hσ).eventually_ge_atTop (2 : ℝ))]
    with n hlog hn hM
  have hn0 : 0 < (n : ℝ) := by linarith
  simp only [Real.norm_eq_abs, Real.rpow_two, one_mul] at hlog
  rw [abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
    abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hlog
  have hR : ((max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (1 - ζ + σ) := by
    rw [Nat.cast_max]
    apply max_le
    · have := Real.one_le_rpow hn hp.le
      norm_num
      linarith
    · have := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
      have := Real.one_le_rpow hn hp.le
      linarith
  have hM' : ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      linarith
    · exact (ceil_power_bounds hn hσ.le).2
  have htarget := (ceil_power_bounds hn (by linarith : 0 ≤ 1 - ζ)).2
  have hbound : topScale n σ ζ ≤
      max (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊)
        ((max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊) := by
    unfold topScale
    exact first_scale_le _ _ _ _
  have hboundR := (Nat.cast_le (α := ℝ)).mpr hbound
  rw [Nat.cast_max, Nat.cast_mul] at hboundR
  apply hboundR.trans
  apply max_le
  · nlinarith [Real.rpow_nonneg hn0.le (1 - ζ + σ)]
  · calc
      _ ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
        mul_le_mul hM' htarget (by positivity) (by positivity)
      _ = 4 * (n : ℝ) ^ (1 - ζ + σ) := by
        rw [show (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) =
          4 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) by ring, ← Real.rpow_add hn0]
        congr 2
        ring

theorem volume_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 10 ≤ ((∑ j ∈ Finset.range (⌊ρ * n⌋₊ + 1), Nat.choose n j : ℕ) : ℝ) / 2 ∧
      (∑ j ∈ Finset.range (⌊ρ * n⌋₊ + 1), Nat.choose n j : ℕ) ≤ 2 ^ n := by
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (20 : ℕ),
    hncast.eventually (eventually_ge_atTop (11 / ρ)),
    hncast.eventually (power_dominates (2 * 2 ^ 11 * (Nat.factorial 11 : ℝ)) 1 10 11
      (by norm_num) (by norm_num))] with n hn hrad hpoly
  have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have h11 : 11 ≤ ⌊ρ * n⌋₊ := by
    apply Nat.le_floor
    simpa [mul_comm] using (div_le_iff₀ hρ).mp hrad
  have hsub : (n : ℝ) / 2 ≤ ((n + 1 - 11 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith
  have hchoose := Nat.pow_le_choose (α := ℝ) 11 n
  have hpow : ((n : ℝ) / 2) ^ 11 / (Nat.factorial 11 : ℝ) ≤ (Nat.choose n 11 : ℝ) :=
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsub 11)
      (by positivity)).trans hchoose
  have hvol : Nat.choose n 11 ≤
      ∑ j ∈ Finset.range (⌊ρ * n⌋₊ + 1), Nat.choose n j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hfloor : ⌊ρ * n⌋₊ ≤ n := by
    have := Nat.floor_mono ((mul_le_mul_of_nonneg_right hρ1 (by positivity)).trans_eq
      (one_mul (n : ℝ)))
    simpa using this
  constructor
  · have hV : (Nat.choose n 11 : ℝ) ≤
        ((∑ j ∈ Finset.range (⌊ρ * n⌋₊ + 1), Nat.choose n j : ℕ) : ℝ) := by
      exact_mod_cast hvol
    norm_num only [Real.rpow_ofNat, one_mul] at hpoly
    have hlow : 2 * (n : ℝ) ^ 10 ≤ ((n : ℝ) / 2) ^ 11 / (Nat.factorial 11 : ℝ) := by
      apply (le_div_iff₀ (by positivity : 0 < (Nat.factorial 11 : ℝ))).mpr
      rw [div_pow]
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 11)).mpr
      norm_num
      nlinarith only [hpoly]
    exact (by linarith [hlow.trans (hpow.trans hV)])
  · calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), Nat.choose n j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro _ _ _
        exact Nat.zero_le _
      _ = 2 ^ n := Nat.sum_range_choose n

theorem omega_small {κ : CConsts} (hκ : κ.Admissible) : 0 < κ.ω ∧ κ.ω < 1 / 100 := by
  have hω0 := hκ.ω_rng.1
  have hMhi : 1 ≤ κ.Mhi := by
    by_contra h
    have hz : κ.Mhi = 0 := by omega
    have hm := hκ.Mhi_big.2
    rw [hz] at hm
    norm_num at hm
  have hMhiR : 1 ≤ (κ.Mhi : ℝ) := by exact_mod_cast hMhi
  have haC : κ.aC < 1 := by
    have := hκ.aC_rng.2
    have := min_le_right κ.η0 1
    linarith
  have := mul_le_mul_of_nonneg_left hMhiR (by positivity : 0 ≤ 5 * κ.ω)
  exact ⟨hκ.ω_rng.1, by nlinarith [hκ.ω_rng.2]⟩

set_option maxHeartbeats 800000 in
theorem section14_numerics_eventually (κ : CConsts) (cg cp cs : ℝ)
    (hω : 0 < κ.ω ∧ κ.ω < 1 / 100) (ha : 0 < κ.a) (hc5 : 0 < κ.c5)
    (hρ : 0 < κ.ρ ∧ κ.ρ < 1) (hcp : 0 < cp)
    (hc14 : 0 < κ.c14 ∧ κ.c14 < cs) (hcs : cs < cg ∧ cs < κ.ω / 1000) :
    ∀ᶠ h : ℕ in atTop, S14.Section14Numerics κ cg cp cs h := by
  have hω0 := hω.1
  have hρ0 := hρ.1
  let γ := κ.c5 * κ.a ^ 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have h3ω : 0 < 3 * κ.ω := by positivity
  have hcs0 : 0 < cs := hc14.1.trans hc14.2
  have hcs1 : cs < 1 := by linarith [hω.2, hcs.2]
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hradius := power_dominates 4 (κ.ρ / 4)
    (1 - κ.ω / 30 + κ.ω / 100) 1 (by positivity) (by linarith [hω.1])
  have hB := power_log_dominates 60 (γ / 8) κ.ω (3 * κ.ω)
    (by norm_num) (by positivity) (by linarith [hω.1])
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    topScale_power_bound (κ.ω / 100) (κ.ω / 30) (by positivity) (by linarith [hω.2]),
    hncast.eventually hradius, hncast.eventually (eventually_ge_atTop (6 / κ.ρ)),
    volume_bounds κ.ρ hρ.1 hρ.2.le,
    hncast.eventually (power_dominates 2 1 (κ.ω / 2) κ.ω (by norm_num) (by linarith [hω.1])),
    hncast.eventually (power_dominates 32 1 (4 + κ.ω) 10 (by norm_num) (by linarith [hω.2])),
    hncast.eventually (power_dominates 5 1 14 20 (by norm_num) (by norm_num)),
    hncast.eventually hB,
    hncast.eventually (polynomial_exp_bound 6 κ.ω (γ / 8) (3 * κ.ω) (by positivity) h3ω),
    hncast.eventually (power_dominates (Real.log 2) (γ / 4) 0 (3 * κ.ω) (by positivity) h3ω),
    hncast.eventually (exp_power_bound 1 (γ / 2) (1 + 3 * κ.ω) (1 + cs)
      (by norm_num) (by positivity) (by linarith) (by linarith [hcs.2, hω.1])),
    hncast.eventually (polynomial_exp_bound 4 1 (1 / 192) 10 (by norm_num) (by norm_num)),
    hncast.eventually (power_dominates (Real.log 2) (1 / 192) 1 10 (by norm_num) (by norm_num)),
    hncast.eventually (exp_power_bound 1 (1 / 96) 10 (1 + cs)
      (by norm_num) (by norm_num) (by linarith) (by linarith)),
    hncast.eventually (polynomial_exp_bound 2 1 (0.001 * κ.a) (1 + 3 * κ.ω)
      (by positivity) (by linarith)),
    hncast.eventually (power_dominates (2 * Real.log 2) (0.001 * κ.a) 1 (1 + 3 * κ.ω)
      (by positivity) (by linarith [hω.1])),
    hncast.eventually (exp_power_bound 1 (0.007 * κ.a) (1 + 3 * κ.ω) (1 + cs)
      (by norm_num) (by positivity) (by linarith) (by linarith [hcs.2, hω.1])),
    hncast.eventually (stretched_decay 2 11 1 cp 1 (by norm_num) hcp (by norm_num)),
    hncast.eventually (stretched_decay 1 0 1 (3 * κ.ω) (1 / 4)
      (by norm_num) h3ω (by norm_num)),
    hncast.eventually (stretched_decay 2 κ.ω (0.24 * κ.a) (3 * κ.ω) (1 / 4)
      (by positivity) h3ω (by norm_num)),
    hncast.eventually (exp_power_bound 6 1 (1 + cs) (1 + κ.c14)
      (by norm_num) (by norm_num) (by linarith [hc14.1]) (by linarith [hc14.2]))]
    with h hh hH hradius hrad hV hT hdel hbase hB hfac htwo hbad
      hpoly hlin hposcount hpoly' hlin' heven hpositive hact hact' hfinal
  simp only [Real.rpow_zero, Real.rpow_one, Real.rpow_ofNat, one_mul, neg_one_mul] at hbase hpoly hlin hposcount hpoly' hlin' hpositive hact hfinal htwo hdel
  let x : ℝ := h
  let K : ℝ := sliceK κ h
  let T : ℝ := sliceT κ h
  let H : ℝ := topScale h (κ.ω / 100) (κ.ω / 30)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ h by omega)
  have hx0 : 0 < x := by linarith only [hx]
  have hk := ceil_power_bounds hx (by linarith only [hω0] : 0 ≤ 3 * κ.ω)
  have ht := ceil_power_bounds hx hω.1.le
  change x ^ (3 * κ.ω) ≤ K ∧ K ≤ 2 * x ^ (3 * κ.ω) at hk
  change x ^ κ.ω ≤ T ∧ T ≤ 2 * x ^ κ.ω at ht
  have hK1 : 1 ≤ K := (Real.one_le_rpow hx h3ω.le).trans hk.1
  have hT1 : 1 ≤ T := (Real.one_le_rpow hx hω.1.le).trans ht.1
  have hHsmall : H ≤ κ.ρ / 4 * x := by
    change H ≤ 4 * x ^ (1 - κ.ω / 30 + κ.ω / 100) at hH
    exact hH.trans (by simpa [Real.rpow_one] using hradius)
  have hHle : H ≤ x := by
    have hρx := mul_le_mul_of_nonneg_right hρ.2.le hx0.le
    nlinarith only [hHsmall, hρx, hx0]
  have hHplus : H + 1 ≤ 2 * x := by linarith only [hHle, hx]
  have hTplus : T + 1 ≤ 3 * x ^ κ.ω := by
    have := Real.one_le_rpow hx hω.1.le
    linarith only [ht.2, this]
  have hprod : x ^ (3 * κ.ω) * x = x ^ (1 + 3 * κ.ω) := by
    calc
      _ = x ^ (3 * κ.ω) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  have htwoexp : (2 : ℝ) ^ h = Real.exp (x * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  let A : ℝ := 2 * x ^ 3 * x ^ 10 * (H + 1) + 1
  have hAbound : A ≤ x ^ 20 := by
    have hA : A ≤ 5 * x ^ 14 := by
      have hp : 1 ≤ x ^ (14 : ℕ) := one_le_pow₀ hx
      calc
        A ≤ 2 * x ^ 3 * x ^ 10 * (2 * x) + 1 := by
          dsimp [A]
          gcongr
        _ = 4 * x ^ 14 + 1 := by ring
        _ ≤ 5 * x ^ 14 := by linarith only [hp]
    exact hA.trans (by simpa only [Real.rpow_ofNat, one_mul] using hbase)
  have hBbound : A ^ (sliceT κ h + 1) ≤ Real.exp ((γ / 8) * x ^ (3 * κ.ω)) := by
    have hb0 : 0 ≤ A := by dsimp [A]; positivity
    have hab : A ^ (sliceT κ h + 1) ≤
        (Real.exp (20 * Real.log x)) ^ (sliceT κ h + 1) := by
      apply pow_le_pow_left₀ hb0
      simpa [show (20 : ℝ) * Real.log x = (20 : ℕ) * Real.log x by norm_num,
        Real.exp_nat_mul, Real.exp_log hx0] using hAbound
    rw [← Real.exp_nat_mul] at hab
    apply hab.trans
    apply Real.exp_le_exp.mpr
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hbudget : 20 * (T + 1) * Real.log x ≤ 60 * x ^ κ.ω * Real.log x := by
      calc
        _ ≤ 20 * (3 * x ^ κ.ω) * Real.log x := by gcongr
        _ = _ := by ring
    exact (by simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm, mul_left_comm]
      using hbudget.trans hB)
  have hbadlist : (2 : ℝ) ^ h *
      (A ^ (sliceT κ h + 1) * (2 * (T + 1) * Real.exp (-γ * K))) ^ h ≤
      Real.exp (-x ^ (1 + cs)) := by
    have hfac' : 2 * (T + 1) ≤ Real.exp ((γ / 8) * x ^ (3 * κ.ω)) := by
      apply le_trans (show 2 * (T + 1) ≤ 6 * x ^ κ.ω by linarith only [hTplus])
      exact hfac
    have hinside : A ^ (sliceT κ h + 1) * (2 * (T + 1) * Real.exp (-γ * K)) ≤
        Real.exp (-(3 * γ / 4) * x ^ (3 * κ.ω)) := by
      calc
        _ ≤ Real.exp ((γ / 8) * x ^ (3 * κ.ω)) *
            (Real.exp ((γ / 8) * x ^ (3 * κ.ω)) * Real.exp (-γ * K)) := by
          gcongr
        _ = Real.exp (γ / 4 * x ^ (3 * κ.ω) - γ * K) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          nlinarith only [hk.1, hγ]
    calc
      _ ≤ (2 : ℝ) ^ h * Real.exp (-(3 * γ / 4) * x ^ (3 * κ.ω)) ^ h := by
        gcongr
      _ = Real.exp (x * Real.log 2 - x * (3 * γ / 4) * x ^ (3 * κ.ω)) := by
        rw [htwoexp, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(γ / 2) * x ^ (1 + 3 * κ.ω)) := by
        apply Real.exp_le_exp.mpr
        have htwo' : Real.log 2 ≤ γ / 4 * x ^ (3 * κ.ω) := by simpa using htwo
        rw [← hprod]
        nlinarith only [mul_le_mul_of_nonneg_right htwo' hx0.le]
      _ ≤ _ := by simpa using hbad
  have hpositions : (2 : ℝ) ^ h * (H + 1) * 2 * Real.exp (-x ^ 10 / 48) ≤
      Real.exp (-x ^ (1 + cs)) := by
    calc
      _ ≤ Real.exp (x * Real.log 2) * (4 * x) * Real.exp (-x ^ 10 / 48) := by
        rw [htwoexp]
        have hh : (H + 1) * 2 ≤ 4 * x := by linarith only [hHplus]
        rw [mul_assoc (Real.exp (x * Real.log 2)) (H + 1) 2]
        gcongr
      _ ≤ Real.exp (x * Real.log 2) * Real.exp (1 / 192 * x ^ (10 : ℝ)) *
          Real.exp (-x ^ (10 : ℕ) / 48) := by
        gcongr <;> simpa only [Real.rpow_ofNat] using hpoly
      _ = Real.exp (x * Real.log 2 + x ^ (10 : ℕ) / 192 - x ^ (10 : ℕ) / 48) := by
        rw [← Real.exp_add, ← Real.exp_add]
        simp only [Real.rpow_ofNat]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / 96) * x ^ (10 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hhlin : Real.log 2 * x ≤ x ^ (10 : ℕ) / 192 := by
          convert hlin using 1 <;> ring
        simp only [Real.rpow_ofNat]
        linarith only [hhlin]
      _ ≤ _ := by simpa using hposcount
  have hevenroles : (2 : ℝ) ^ h *
      ((∑ j ∈ Finset.range (⌊κ.ρ * h⌋₊ + 1), Nat.choose h j : ℕ) : ℝ) *
        (H + 1) * Real.exp (-0.01 * κ.a * K * x) / sliceEps κ h ≤
      Real.exp (-x ^ (1 + cs)) := by
    have hv : ((∑ j ∈ Finset.range (⌊κ.ρ * h⌋₊ + 1), Nat.choose h j : ℕ) : ℝ) ≤
        (2 : ℝ) ^ h := by exact_mod_cast hV.2
    have herr : Real.exp (-0.01 * κ.a * K * x) / sliceEps κ h =
        Real.exp (-0.009 * κ.a * K * x) := by
      dsimp [sliceEps, K, x]
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      _ = (2 : ℝ) ^ h *
          ((∑ j ∈ Finset.range (⌊κ.ρ * h⌋₊ + 1), Nat.choose h j : ℕ) : ℝ) *
          (H + 1) * Real.exp (-0.009 * κ.a * K * x) := by
        rw [mul_div_assoc, herr]
      _ ≤ Real.exp (2 * Real.log 2 * x) * (2 * x) *
          Real.exp (-0.009 * κ.a * K * x) := by
        have hexp : (2 : ℝ) ^ h * (2 : ℝ) ^ h = Real.exp (2 * Real.log 2 * x) := by
          rw [htwoexp, ← Real.exp_add]
          congr 1
          ring
        rw [← hexp]
        gcongr
      _ ≤ Real.exp (2 * Real.log 2 * x) * Real.exp (0.001 * κ.a * x ^ (1 + 3 * κ.ω)) *
          Real.exp (-0.009 * κ.a * K * x) := by
        gcongr <;> exact hpoly'
      _ = Real.exp (2 * Real.log 2 * x + 0.001 * κ.a * x ^ (1 + 3 * κ.ω) -
          0.009 * κ.a * K * x) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-0.007 * κ.a * x ^ (1 + 3 * κ.ω)) := by
        apply Real.exp_le_exp.mpr
        have hlin'' : 2 * Real.log 2 * x ≤ 0.001 * κ.a * x ^ (1 + 3 * κ.ω) := by
          simpa [Real.rpow_one] using hlin'
        have hKx := mul_le_mul_of_nonneg_right hk.1 hx0.le
        rw [hprod] at hKx
        have hKxa := mul_le_mul_of_nonneg_left hKx ha.le
        nlinarith only [hKxa, hlin'']
      _ ≤ _ := by simpa using heven
  have hpos : (H + 1) * x ^ 10 * Real.exp (-x ^ cp) ≤ 1 := by
    calc
      _ ≤ 2 * x ^ (11 : ℕ) * Real.exp (-x ^ cp) := by
        have hhprod := mul_le_mul_of_nonneg_right hHplus (by positivity : 0 ≤ x ^ (10 : ℕ))
        have : (H + 1) * x ^ (10 : ℕ) ≤ 2 * x ^ (11 : ℕ) := by nlinarith only [hhprod]
        gcongr
      _ ≤ _ := by simpa [Real.rpow_natCast, Real.rpow_ofNat] using hpositive
  have hactivation : Real.exp (-K) + T * Real.exp (-0.24 * κ.a * K) ≤ 1 / 2 := by
    have h1 : Real.exp (-K) ≤ 1 / 4 := by
      apply le_trans (Real.exp_le_exp.mpr (neg_le_neg hk.1))
      simpa using hact
    have h2 : T * Real.exp (-0.24 * κ.a * K) ≤ 1 / 4 := by
      calc
        _ ≤ 2 * x ^ κ.ω * Real.exp (-0.24 * κ.a * x ^ (3 * κ.ω)) := by
          apply mul_le_mul ht.2 (Real.exp_le_exp.mpr ?_) (by positivity) (by positivity)
          exact mul_le_mul_of_nonpos_left hk.1 (by nlinarith only [ha])
        _ ≤ _ := by simpa using hact'
    linarith only [h1, h2]
  have hfinal' : 2 * Real.exp (-x ^ (1 + cg)) + 4 * Real.exp (-x ^ (1 + cs)) ≤
      Real.exp (-x ^ (1 + κ.c14)) := by
    have hcmp : Real.exp (-x ^ (1 + cg)) ≤ Real.exp (-x ^ (1 + cs)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hcs.1])
    exact (by linarith only [hcmp] : 2 * Real.exp (-x ^ (1 + cg)) + 4 * Real.exp (-x ^ (1 + cs)) ≤
      6 * Real.exp (-x ^ (1 + cs))).trans (by simpa using hfinal)
  have hradius' : 12 * H + 4 * (⌊κ.ρ * h⌋₊ : ℝ) + 6 < 10 * κ.ρ * x := by
    have hfloor := Nat.floor_le (show 0 ≤ κ.ρ * h by positivity)
    have h6 : 6 ≤ κ.ρ * x := by simpa [mul_comm] using (div_le_iff₀ hρ.1).mp hrad
    nlinarith only [hHsmall, hfloor, h6]
  have hdeletion : 4 * x ^ 4 * T ≤ x ^ 10 / 4 := by
    have hpre : 4 * x ^ (4 : ℕ) * T ≤ 8 * x ^ (4 + κ.ω : ℝ) := by
      calc
        _ ≤ 4 * x ^ (4 : ℕ) * (2 * x ^ κ.ω) := by gcongr <;> exact ht.2
        _ = _ := by rw [← Real.rpow_natCast x 4, Real.rpow_add hx0]; ring
    have hdel' : 32 * x ^ (4 + κ.ω : ℝ) ≤ x ^ (10 : ℕ) := by
      simpa [Real.rpow_natCast, Real.rpow_ofNat] using hdel
    linarith only [hpre, hdel']
  have hkpos : 0 < sliceK κ h := by
    have hKposR : (0 : ℝ) < (sliceK κ h : ℝ) := by
      change 0 < K
      linarith only [hK1]
    exact_mod_cast hKposR
  have hsmallpow : x ^ (κ.ω / 8) ≤ x ^ (10 : ℕ) := by
    rw [← Real.rpow_natCast x 10]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hω.2])
  have htlarge : 2 * x ^ (κ.ω / 2) ≤ T := by
    have hT' : 2 * x ^ (κ.ω / 2) ≤ x ^ κ.ω := by simpa only [one_mul] using hT
    exact hT'.trans ht.1
  exact ⟨hh, hkpos, hV.1, hsmallpow, hradius', htlarge, hdeletion,
    hpositions, by simpa only [A, γ, x, K, T, H, neg_mul, mul_assoc, Real.rpow_eq_pow] using hbadlist,
    hevenroles, hpos, hactivation, hfinal'⟩

set_option maxHeartbeats 800000 in
theorem calibration_eventually (κ : CConsts) (hω : 0 < κ.ω) (ha : 0 < κ.a)
    (hM : 1 < (κ.Mlo : ℝ)) (hωM : 4 * κ.ω * κ.Mlo < 1) :
    ∀ᶠ q : ℝ in atTop, ∀ h : ℕ, q ^ (κ.Mlo : ℝ) ≤ (h : ℝ) →
      (h : ℝ) < 2 * q ^ (κ.Mlo : ℝ) →
      let d := ⌊Real.exp (q / 2)⌋₊
      κ.d0 ≤ d ∧ (10 ^ 100 : ℕ) ≤ d ∧
      4 * Real.exp (1.5 * (sliceK κ h : ℝ) * sliceT κ h) ≤ (d : ℝ) ^ (0.05 : ℝ) ∧
      2 * (h : ℝ) ^ 2 ≤ (d : ℝ) ^ (0.01 : ℝ) ∧
      (h + 1 : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) ∧
      16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * (sliceEps κ h) ^ (1 / 16 : ℝ) ≤
        (d : ℝ) ^ (-20 : ℝ) := by
  let m : ℝ := κ.Mlo
  let p : ℝ := 4 * κ.ω * m
  let r : ℝ := m * (1 + 3 * κ.ω)
  have hp : 0 < p := by dsimp [p, m]; positivity
  have hr : 1 < r := by
    dsimp [r, m]
    nlinarith
  have he : Tendsto (fun q : ℝ => Real.exp (q / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  filter_upwards [eventually_ge_atTop (1 : ℝ), he.eventually_ge_atTop 2,
    he.eventually_ge_atTop (max (κ.d0 : ℝ) ((10 ^ 100 : ℕ) : ℝ)),
    power_dominates (6 * (2 : ℝ) ^ (4 * κ.ω)) (1 / 160) p 1
      (by norm_num) hωM,
    polynomial_exp_bound 4 0 (1 / 160) 1 (by norm_num) (by norm_num),
    polynomial_exp_bound 8 (2 * m) (1 / 400) 1 (by norm_num) (by norm_num),
    polynomial_exp_bound 3 m (1 / 160) 1 (by norm_num) (by norm_num),
    polynomial_exp_bound 144 (2 * m) 1 1 (by norm_num) (by norm_num),
    power_dominates 12 (κ.a / 16000) 1 r (by positivity) hr]
    with q hq he2 hed hkt hfour hh2 hh1 hfront htail
  simp only [Real.rpow_zero, Real.rpow_one, one_mul] at hkt hfour hh2 hh1 hfront htail
  intro h hlow hhigh
  let x : ℝ := h
  let d : ℕ := ⌊Real.exp (q / 2)⌋₊
  have hx1 : 1 ≤ x := (Real.one_le_rpow hq (by dsimp [m]; linarith only [hM] : 0 ≤ m)).trans hlow
  have hx0 : 0 < x := by linarith only [hx1]
  have hq0 : 0 < q := by linarith only [hq]
  have hdhi : (d : ℝ) ≤ Real.exp (q / 2) := Nat.floor_le (Real.exp_pos _).le
  have hdlo : Real.exp (q / 4) ≤ (d : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (q / 2))
    have hexp : Real.exp (q / 2) = Real.exp (q / 4) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change Real.exp (q / 2) < (d : ℝ) + 1 at hh
    rw [hexp] at hh
    nlinarith only [hh, he2]
  have hd0 : 0 < (d : ℝ) := (Real.exp_pos _).trans_le hdlo
  have hdlarge : max (κ.d0 : ℝ) ((10 ^ 100 : ℕ) : ℝ) ≤ (d : ℝ) := hed.trans hdlo
  have hdsmall (s : ℝ) (hs : 0 ≤ s) : Real.exp (q / 4 * s) ≤ (d : ℝ) ^ s := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hdlo hs
  have hk := ceil_power_bounds hx1 (by linarith only [hω] : 0 ≤ 3 * κ.ω)
  have ht := ceil_power_bounds hx1 hω.le
  change x ^ (3 * κ.ω) ≤ (sliceK κ h : ℝ) ∧ (sliceK κ h : ℝ) ≤ 2 * x ^ (3 * κ.ω) at hk
  change x ^ κ.ω ≤ (sliceT κ h : ℝ) ∧ (sliceT κ h : ℝ) ≤ 2 * x ^ κ.ω at ht
  have hxhigh : x ≤ 2 * q ^ m := hhigh.le
  have hkt' : (sliceK κ h : ℝ) * sliceT κ h ≤ 4 * (2 : ℝ) ^ (4 * κ.ω) * q ^ p := by
    calc
      _ ≤ (2 * x ^ (3 * κ.ω)) * (2 * x ^ κ.ω) :=
        mul_le_mul hk.2 ht.2 (by positivity) (by positivity)
      _ = 4 * x ^ (4 * κ.ω) := by
        rw [show 4 * κ.ω = 3 * κ.ω + κ.ω by ring, Real.rpow_add hx0]
        ring
      _ ≤ 4 * (2 * q ^ m) ^ (4 * κ.ω) := by gcongr
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hq0.le,
          show m * (4 * κ.ω) = p by dsimp [p]; ring]
        ring
  have hdim2 : 2 * x ^ (2 : ℕ) ≤ 8 * q ^ (2 * m) := by
    calc
      _ ≤ 2 * (2 * q ^ m) ^ (2 : ℕ) := by gcongr
      _ = _ := by rw [mul_pow, ← Real.rpow_natCast (q ^ m) 2, ← Real.rpow_mul hq0.le]; ring
  have hxplus : x + 1 ≤ 3 * q ^ m := by
    have := Real.one_le_rpow hq (by dsimp [m]; linarith only [hM] : 0 ≤ m)
    linarith only [this, hxhigh]
  have htailpow : q ^ r ≤ (sliceK κ h : ℝ) * x := by
    calc
      q ^ r = (q ^ m) ^ (1 + 3 * κ.ω) := Real.rpow_mul hq0.le _ _
      _ ≤ x ^ (1 + 3 * κ.ω) := Real.rpow_le_rpow (by positivity) hlow (by positivity)
      _ = x ^ (3 * κ.ω) * x := by rw [show 1 + 3 * κ.ω = 3 * κ.ω + 1 by ring,
        Real.rpow_add hx0, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hk.1 hx0.le
  have heps : (sliceEps κ h) ^ (1 / 16 : ℝ) =
      Real.exp (-(κ.a / 16000) * (sliceK κ h : ℝ) * x) := by
    dsimp [sliceEps, x]
    rw [← Real.exp_mul]
    congr 1
    ring
  have hcharge : 16 * (d : ℝ) ^ 2 * (x + 1) ^ 2 * (sliceEps κ h) ^ (1 / 16 : ℝ) ≤
      (d : ℝ) ^ (-20 : ℝ) := by
    have hd2 : (d : ℝ) ^ (2 : ℕ) ≤ Real.exp q := by
      calc
        _ ≤ Real.exp (q / 2) ^ (2 : ℕ) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    have hxplus2 : (x + 1) ^ (2 : ℕ) ≤ 9 * q ^ (2 * m) := by
      calc
        _ ≤ (3 * q ^ m) ^ (2 : ℕ) := by gcongr
        _ = _ := by rw [mul_pow, ← Real.rpow_natCast (q ^ m) 2, ← Real.rpow_mul hq0.le]; ring
    have hdneg : Real.exp (-10 * q) ≤ (d : ℝ) ^ (-20 : ℝ) := by
      have h := Real.rpow_le_rpow_of_nonpos hd0 hdhi (by norm_num : (-20 : ℝ) ≤ 0)
      rw [← Real.exp_mul] at h
      convert h using 1 <;> congr 1 <;> ring
    calc
      _ ≤ 144 * q ^ (2 * m) * Real.exp q * Real.exp (-(κ.a / 16000) * q ^ r) := by
        rw [heps]
        have hdec : Real.exp (-(κ.a / 16000) * (sliceK κ h : ℝ) * x) ≤
            Real.exp (-(κ.a / 16000) * q ^ r) := by
          apply Real.exp_le_exp.mpr
          have h := mul_le_mul_of_nonneg_left htailpow
            (div_pos ha (by norm_num : (0 : ℝ) < 16000)).le
          nlinarith only [h]
        have hmul := mul_le_mul hd2 hxplus2 (by positivity) (Real.exp_pos q).le
        have : 16 * (d : ℝ) ^ (2 : ℕ) * (x + 1) ^ (2 : ℕ) ≤
            144 * q ^ (2 * m) * Real.exp q := by nlinarith only [hmul]
        gcongr
      _ ≤ Real.exp q * Real.exp q * Real.exp (-(κ.a / 16000) * q ^ r) := by
        gcongr <;> simpa [Real.rpow_one] using hfront
      _ = Real.exp (2 * q - (κ.a / 16000) * q ^ r) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-10 * q) := by
        apply Real.exp_le_exp.mpr
        have : 12 * q ≤ κ.a / 16000 * q ^ r := by simpa [Real.rpow_one] using htail
        linarith only [this]
      _ ≤ _ := hdneg
  have hfour' : 4 ≤ Real.exp (q / 160) := by convert hfour using 1 <;> congr 1 <;> ring
  have hkt'' : 1.5 * (sliceK κ h : ℝ) * sliceT κ h ≤ q / 160 := by
    have : 6 * (2 : ℝ) ^ (4 * κ.ω) * q ^ p ≤ q / 160 := by
      convert hkt using 1 <;> ring
    nlinarith only [hkt', this]
  refine ⟨?_, ?_, ?_, ?_, ?_, hcharge⟩
  · exact_mod_cast (le_max_left _ _).trans hdlarge
  · exact_mod_cast (le_max_right _ _).trans hdlarge
  · calc
      _ ≤ Real.exp (q / 160) * Real.exp (q / 160) := by gcongr
      _ = Real.exp (q / 4 * 0.05) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hdsmall _ (by norm_num)
  · calc
      _ ≤ 8 * q ^ (2 * m) := hdim2
      _ ≤ Real.exp (1 / 400 * q) := hh2
      _ ≤ _ := by convert hdsmall 0.01 (by norm_num) using 1 <;> congr 1 <;> ring
  · calc
      _ ≤ 3 * q ^ m := hxplus
      _ ≤ Real.exp (1 / 160 * q) := hh1
      _ ≤ _ := by convert hdsmall 0.025 (by norm_num) using 1 <;> congr 1 <;> ring

theorem height_witness (κ : CConsts) (hκ : κ.Admissible) :
    ∃ c : ℝ, ∃ h0 : ℕ, 0 < c ∧ c ≤ κ.c14 ∧ 0 < h0 ∧
      Nonempty (S14.HeightConstantContract {κ with c14 := c, h0 := h0}) := by
  have hω := omega_small hκ
  have hω0 := hω.1
  have hρ0 := hκ.ρ_rng.1
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hp : HDAdmissible 10 (κ.ω / 8) (κ.ω / 2) (κ.ω / 100) (κ.ω / 30)
      (1 - κ.ω / 30) (κ.ω / 12) 1 1 6 := by
    refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, by norm_num⟩
    · exact ⟨by positivity, by linarith, by linarith [hω.2]⟩
    · exact ⟨by positivity, by linarith, by linarith [hω.2], by linarith [hω.2], by linarith⟩
    · exact ⟨by linarith, by linarith, by linarith⟩
  have hρ : 0 < κ.ρ / 2 ∧ κ.ρ / 2 ≤ 1 / 4 :=
    ⟨by positivity, by linarith [hκ.ρ_rng.2.1]⟩
  let reg : HDRegime (κ.ω / 8) (κ.ω / 2) 6 := .lin (κ.ρ / 2) hρ
  obtain ⟨cg, hcg, ng, hg⟩ := height_selection_global 10
    (κ.ω / 8) (κ.ω / 2) (κ.ω / 100) (κ.ω / 30) (1 - κ.ω / 30)
    (κ.ω / 12) 1 1 6 hp reg
  obtain ⟨cp, hcp, np, hpos⟩ := height_selection_positive 10
    (κ.ω / 8) (κ.ω / 2) (κ.ω / 100) (κ.ω / 30) (1 - κ.ω / 30)
    (κ.ω / 12) 1 1 6 hp reg
  let cs := min (cg / 2) (κ.ω / 2000)
  have hcs0 : 0 < cs := lt_min (by positivity) (by positivity)
  have hcsg : cs < cg := (min_le_left _ _).trans_lt (by linarith)
  have hcsω : cs < κ.ω / 1000 := (min_le_right _ _).trans_lt (by linarith)
  let c := min (κ.c14 / 2) (cs / 2)
  have hc0 : 0 < c := lt_min (by exact div_pos hκ.c14_pos (by norm_num)) (by positivity)
  have hcc : c ≤ κ.c14 := (min_le_left _ _).trans (by linarith [hκ.c14_pos])
  have hccs : c < cs := (min_le_right _ _).trans_lt (by linarith)
  have he := section14_numerics_eventually {κ with c14 := c} cg cp cs hω ha hκ.c5_pos
    ⟨hρ0, by linarith [hκ.ρ_rng.2.1]⟩ hcp ⟨hc0, hccs⟩ ⟨hcsg, hcsω⟩
  obtain ⟨ns, hns⟩ := eventually_atTop.mp he
  let h0 := max 1 (max ng (max np ns))
  have h0pos : 0 < h0 := by dsimp [h0]; omega
  have hng : ng ≤ h0 := by dsimp [h0]; omega
  have hnp : np ≤ h0 := by dsimp [h0]; omega
  have hns0 : ns ≤ h0 := by dsimp [h0]; omega
  refine ⟨c, h0, hc0, hcc, h0pos, ⟨?_⟩⟩
  refine {
    J₀ := 10, b₀ := κ.ω / 8, b := κ.ω / 2, σ := κ.ω / 100,
    ζ := κ.ω / 30, θ := 1 - κ.ω / 30, a := κ.ω / 12, c_d := 1,
    C_d := 1, α := 1 / 2, admissible := hp, regime := reg,
    regime_linear := ⟨hρ, rfl⟩,
    exponents_match := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    theta_large := by linarith [hω.2],
    alpha_range := ⟨by norm_num, by linarith [hω.2]⟩,
    globalExponent := cg, globalThreshold := ng, global_exponent_pos := hcg,
    global_bound := by simpa [S14.Section14GlobalHeightBound] using hg,
    global_c14 := hccs.trans hcsg, global_h0 := hng,
    positiveExponent := cp, positiveThreshold := np, positive_exponent_pos := hcp,
    positive_bound := by simpa [S14.Section14PositiveHeightBound] using hpos,
    positive_h0 := hnp, sliceExponent := cs,
    slice_exponent := ⟨hccs, hcsg, hcsω⟩,
    threshold_slack := ?_ }
  intro h hh
  exact hns h (hns0.trans hh)

theorem qcond_update_eventually (κ : CConsts) (hκ : κ.Admissible)
    (c : ℝ) (hc : 0 < c) (h0 : ℕ) (hM : 0 < (κ.Mlo : ℝ)) :
    ∀ᶠ q : ℝ in atTop, QCond {κ with c14 := c, h0 := h0} q := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herr : ∀ᶠ h : ℕ in atTop,
      Real.exp (-(h : ℝ) ^ (1 + c)) +
        2 * (h : ℝ) ^ 2 * Real.sqrt (sliceEps κ h) ≤ Real.rpow 10 (-5) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hncast.eventually (stretched_decay 1 0 1 (1 + c) (1 / 200000)
        (by norm_num) (by linarith) (by norm_num)),
      hncast.eventually (stretched_decay 2 2 (0.0005 * κ.a) 1 (1 / 200000)
        (by positivity) (by norm_num) (by norm_num))] with h hh h1 h2
    simp only [Real.rpow_zero, Real.rpow_one, Real.rpow_ofNat, one_mul, neg_one_mul] at h1 h2
    have h1' : Real.exp (-(h : ℝ) ^ (1 + c)) ≤ 1 / 200000 := by simpa using h1
    have hpow : 1 ≤ (h : ℝ) ^ (3 * κ.ω) :=
      Real.one_le_rpow (by exact_mod_cast hh) (by linarith [hκ.ω_rng.1])
    have hk : 1 ≤ (sliceK κ h : ℝ) := hpow.trans (Nat.le_ceil _)
    have hsqrt : Real.sqrt (sliceEps κ h) =
        Real.exp (-0.0005 * κ.a * (sliceK κ h : ℝ) * h) := by
      rw [sliceEps, show Real.exp (-0.001 * κ.a * (sliceK κ h : ℝ) * h) =
        Real.exp (-0.0005 * κ.a * (sliceK κ h : ℝ) * h) ^ (2 : ℕ) by
          rw [← Real.exp_nat_mul]; congr 1; ring]
      exact Real.sqrt_sq (Real.exp_pos _).le
    have h2' : 2 * (h : ℝ) ^ (2 : ℕ) * Real.sqrt (sliceEps κ h) ≤ 1 / 200000 := by
      rw [hsqrt]
      calc
        _ ≤ 2 * (h : ℝ) ^ (2 : ℕ) * Real.exp (-0.0005 * κ.a * h) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hkh : (h : ℝ) ≤ (sliceK κ h : ℝ) * h := by
            simpa using mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ (h : ℝ))
          have hw := mul_le_mul_of_nonpos_left hkh (by nlinarith only [ha] : -0.0005 * κ.a ≤ 0)
          convert hw using 1 <;> ring
        _ ≤ _ := by simpa using h2
    norm_num [Real.rpow_neg_ofNat, zpow_neg] at ⊢
    linarith only [h1', h2']
  obtain ⟨ne, hne⟩ := eventually_atTop.mp herr
  filter_upwards [eventually_ge_atTop κ.Q0,
    (tendsto_rpow_atTop hM).eventually_ge_atTop (max (ne : ℝ) h0)] with q hq hscale
  rcases hκ.Q0_large q hq with ⟨h1, h2, h3, h4, h5, h6, h7, h8, hall⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  intro h hl hh
  have hne' : ne ≤ h := by
    exact_mod_cast ((le_max_left (ne : ℝ) (h0 : ℝ)).trans (hscale.trans hl))
  have hh0 : h0 ≤ h := by
    exact_mod_cast ((le_max_right (ne : ℝ) (h0 : ℝ)).trans (hscale.trans hl))
  rcases hall h hl hh with ⟨_, ht, hnorm, hexp, hdec, hsqrt, _, hd, hdneg, hhd, hch⟩
  exact ⟨hh0, ht, hnorm, hexp, hdec, hsqrt, hne h hne', hd, hdneg, hhd, hch⟩

theorem transfer_height {κ κ' : CConsts}
    (hω : κ.ω = κ'.ω) (hρ : κ.ρ = κ'.ρ) (ha : κ.a = κ'.a)
    (hc5 : κ.c5 = κ'.c5) (hc14 : κ.c14 = κ'.c14) (hh0 : κ.h0 = κ'.h0)
    (h : Nonempty (S14.HeightConstantContract κ)) :
    Nonempty (S14.HeightConstantContract κ') := by
  obtain ⟨H⟩ := h
  refine ⟨{
    J₀ := H.J₀, b₀ := H.b₀, b := H.b, σ := H.σ, ζ := H.ζ, θ := H.θ,
    a := H.a, c_d := H.c_d, C_d := H.C_d, α := H.α,
    admissible := H.admissible, regime := H.regime,
    regime_linear := by simpa only [hρ] using H.regime_linear,
    exponents_match := by simpa only [hω] using H.exponents_match,
    theta_large := H.theta_large, alpha_range := H.alpha_range,
    globalExponent := H.globalExponent, globalThreshold := H.globalThreshold,
    global_exponent_pos := H.global_exponent_pos, global_bound := H.global_bound,
    global_c14 := by simpa only [hc14] using H.global_c14,
    global_h0 := by simpa only [hh0] using H.global_h0,
    positiveExponent := H.positiveExponent, positiveThreshold := H.positiveThreshold,
    positive_exponent_pos := H.positive_exponent_pos, positive_bound := H.positive_bound,
    positive_h0 := by simpa only [hh0] using H.positive_h0,
    sliceExponent := H.sliceExponent,
    slice_exponent := by simpa only [hc14, hω] using H.slice_exponent,
    threshold_slack := ?_ }⟩
  simpa only [S14.Section14Numerics, sliceK, sliceT, sliceEps, hω, ha, hc5, hc14, hρ, hh0]
    using H.threshold_slack

end HypercubeRamsey.S18.Lane_sol_s18_widen
