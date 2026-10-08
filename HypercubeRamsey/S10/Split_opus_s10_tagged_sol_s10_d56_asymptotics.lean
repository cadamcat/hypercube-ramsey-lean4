import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_weights

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical HypercubeRamsey.S10 HypercubeRamsey.Lane_p_height_main Filter
open scoped BigOperators

/-- A polynomial bound for the final height scale is enough for both error budgets. -/
theorem s10_height_poly (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ) / 8)
    (n : ℕ) (hn : 2 ≤ n) :
    (topScale n δ (8 * δ) : ℝ) ≤ 2 * (3 : ℝ) ^ ⌈1 / δ⌉₊ * (n : ℝ) ^ 4 := by
  let C := ⌈1 / δ⌉₊
  let M := hdScaleMultiplier n δ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := hn1.trans' zero_le_one
  have hx1 : 1 ≤ (n : ℝ) ^ δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hδ.le
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlog : Real.log (n : ℝ) ≤ n := by
    simpa using Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1)
  have hlog2 : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hn2 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hR : (heightBaseRadius n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    have hceil := (Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))).le
    simp only [heightBaseRadius, Nat.cast_max, Nat.cast_one]
    exact max_le (by nlinarith) (by nlinarith)
  have hM : (M : ℝ) ≤ 3 * (n : ℝ) ^ δ := by
    have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hn0 δ)).le
    simp only [M, hdScaleMultiplier, Nat.cast_max, Nat.cast_ofNat]
    exact max_le (by nlinarith) (by nlinarith)
  have hM1 : 1 ≤ (M : ℝ) := by
    exact_mod_cast (show 1 ≤ M by dsimp [M, hdScaleMultiplier]; omega)
  have hidx : hdScaleIndex n δ (8 * δ) ≤ C :=
    hdScaleIndex_le_ceil_inv_sigma hn hδ ⟨by positivity, by linarith⟩
  have hceilC : (C : ℝ) ≤ 1 / δ + 1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / δ)).le
  have hδC : δ * (C : ℝ) ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hceilC hδ.le
    have hdiv : δ * (1 / δ) = 1 := by field_simp
    nlinarith
  have hxC : ((n : ℝ) ^ δ) ^ C ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hδC
  calc
    (topScale n δ (8 * δ) : ℝ) = (M : ℝ) ^ hdScaleIndex n δ (8 * δ) * (heightBaseRadius n : ℝ) := by
      rw [topScale_eq_hdScaleRadius]
      simp [hdScaleRadius, M]
    _ ≤ (M : ℝ) ^ C * (2 * (n : ℝ) ^ 2) :=
      mul_le_mul (pow_le_pow_right₀ hM1 hidx) hR (by positivity) (by positivity)
    _ ≤ (3 * (n : ℝ) ^ δ) ^ C * (2 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg M) hM C) (by positivity)
    _ = (3 : ℝ) ^ C * ((n : ℝ) ^ δ) ^ C * (2 * (n : ℝ) ^ 2) := by rw [mul_pow]
    _ ≤ (3 : ℝ) ^ C * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC (by positivity)) (by positivity)
    _ = _ := by ring


/-- Any fixed polynomial is dominated by the stretched exponential height error. -/
theorem nat_poly_exp_decay (c p : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p * Real.exp (-(n : ℝ) ^ c)) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (_root_.tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have ht := (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / c) 1 (by norm_num)).comp hp
  have heq (n : ℕ) : ((n : ℝ) ^ c) ^ (p / c) = (n : ℝ) ^ p := by
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    field_simp
  simpa only [Function.comp_def, heq, neg_one_mul] using ht

noncomputable def candidateBase (n m : ℕ) (δ : ℝ) : ℝ :=
  (m + (n - m + 1) ^ 3 : ℕ) * (topScale n δ (8 * δ) + 1 : ℕ) * (2 * (n : ℝ) ^ 10) + 1

/-- The candidate-count bound has a fixed polynomial degree. -/
theorem candidateBase_poly (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ) / 8)
    (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    candidateBase n m δ ≤ (18 * (2 * (3 : ℝ) ^ ⌈1 / δ⌉₊ + 1) + 1) * (n : ℝ) ^ 17 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := le_trans zero_le_one hn1
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hrem : ((n - m + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le n m) 1
  have hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ (3 : ℕ))
  have hcube : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by ring
  have henv : ((m + (n - m + 1) ^ 3 : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 := by
    push_cast
    have hr := pow_le_pow_left₀ (Nat.cast_nonneg (n - m + 1)) hrem 3
    push_cast at hr
    nlinarith
  let Q : ℝ := 2 * (3 : ℝ) ^ ⌈1 / δ⌉₊ + 1
  have hH : ((topScale n δ (8 * δ) + 1 : ℕ) : ℝ) ≤ Q * (n : ℝ) ^ 4 := by
    have hh := s10_height_poly δ hδ hδsmall n hn
    have hfour : 1 ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
    dsimp [Q]
    push_cast
    nlinarith
  have h17 : 1 ≤ (n : ℝ) ^ 17 := one_le_pow₀ hn1
  calc
    candidateBase n m δ ≤ (9 * (n : ℝ) ^ 3) * (Q * (n : ℝ) ^ 4) * (2 * (n : ℝ) ^ 10) + 1 := by
      unfold candidateBase
      gcongr
    _ = 18 * Q * (n : ℝ) ^ 17 + 1 := by ring
    _ ≤ (18 * Q + 1) * (n : ℝ) ^ 17 := by nlinarith
    _ = _ := rfl


/-- The enumeration price is negligible compared with the number of special coordinates. -/
theorem own_cost_eventually (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ) / 2000) :
    ∀ᶠ n : ℕ in atTop,
      let m := ⌊(n : ℝ) ^ (200 * δ)⌋₊
      candidateBase n m δ ^ p10_1kHeightCount n δ ≤ Real.exp ((m : ℝ) / 25) := by
  let D : ℝ := 18 * (2 * (3 : ℝ) ^ ⌈1 / δ⌉₊ + 1) + 1
  let A : ℝ := 2 * (|Real.log D| + 17 / δ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have hh : 0 ≤ 18 * (2 * (3 : ℝ) ^ ⌈1 / δ⌉₊ + 1) := by positivity
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h58 : 0 < 58 * δ := by positivity
  have h200 : 0 < 200 * δ := by positivity
  have hlarge : ∀ᶠ n : ℕ in atTop, 50 * A ≤ (n : ℝ) ^ (58 * δ) :=
    ((_root_.tendsto_rpow_atTop h58).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hmass : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (200 * δ) :=
    ((_root_.tendsto_rpow_atTop h200).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n := Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hlarge, hmass, hnlarge] with n hlarge hmass hn
  dsimp only
  let x : ℝ := n
  let m := ⌊x ^ (200 * δ)⌋₊
  let T := p10_1kHeightCount n δ
  let b := candidateBase n m δ
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hmlo : x ^ (200 * δ) / 2 ≤ (m : ℝ) := by
    have hf : x ^ (200 * δ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith
  have hpowle : x ^ (200 * δ) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith : 200 * δ ≤ 1)
  have hm : m ≤ n := by
    have hf : (m : ℝ) ≤ x := (Nat.floor_le (Real.rpow_nonneg hx.le _)).trans hpowle
    change (m : ℝ) ≤ (n : ℝ) at hf
    exact_mod_cast hf
  have hb : b ≤ D * x ^ 17 := candidateBase_poly δ hδ (by linarith) n m hn hm
  have hbpos : 0 < b := by dsimp [b, candidateBase]; positivity
  have hlog : Real.log b ≤ Real.log D + 17 * Real.log x := by
    calc
      Real.log b ≤ Real.log (D * x ^ 17) := Real.log_le_log hbpos hb
      _ = _ := by rw [Real.log_mul hD.ne' (pow_ne_zero _ hx.ne'), Real.log_pow]; norm_num
  have hxδ : 1 ≤ x ^ δ := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hδ.le
  have hx141 : 1 ≤ x ^ (141 * δ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show 0 ≤ 141 * δ by positivity)
  have hT : (T : ℝ) ≤ 2 * x ^ (141 * δ) := by
    have ht := (Nat.ceil_lt_add_one (Real.rpow_nonneg hx.le (141 * δ))).le
    dsimp [T, p10_1kHeightCount]
    nlinarith
  have hcoef : Real.log D + 17 * Real.log x ≤ (|Real.log D| + 17 / δ) * x ^ δ := by
    have hl := Real.log_natCast_le_rpow_div n hδ
    change Real.log x ≤ x ^ δ / δ at hl
    have hd := le_abs_self (Real.log D)
    have ha := mul_le_mul_of_nonneg_left hxδ (abs_nonneg (Real.log D))
    calc
      _ ≤ |Real.log D| * x ^ δ + 17 * (x ^ δ / δ) :=
        add_le_add (hd.trans (by simpa only [mul_one] using ha))
          (mul_le_mul_of_nonneg_left hl (by norm_num))
      _ = _ := by ring
  have hcoef0 : 0 ≤ Real.log D + 17 * Real.log x := by
    have hl0 := Real.log_nonneg hx1
    have hd0 := Real.log_nonneg hD1
    positivity
  have hexponent : (T : ℝ) * Real.log b ≤ A * x ^ (142 * δ) := by
    calc
      _ ≤ (T : ℝ) * (Real.log D + 17 * Real.log x) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ ≤ (2 * x ^ (141 * δ)) * ((|Real.log D| + 17 / δ) * x ^ δ) :=
        mul_le_mul hT hcoef hcoef0 (by positivity)
      _ = A * x ^ (142 * δ) := by
        have hr : x ^ (141 * δ) * x ^ δ = x ^ (142 * δ) := by
          rw [← Real.rpow_add hx]; congr 1; ring
        dsimp [A]
        calc
          _ = 2 * (|Real.log D| + 17 / δ) * (x ^ (141 * δ) * x ^ δ) := by ring
          _ = _ := by rw [hr]
  have habsorb : A * x ^ (142 * δ) ≤ (m : ℝ) / 25 := by
    have hp := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hx.le (142 * δ))
    have hr : x ^ (58 * δ) * x ^ (142 * δ) = x ^ (200 * δ) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [hr] at hp
    nlinarith
  calc
    b ^ T = Real.exp ((T : ℝ) * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hbpos]
    _ ≤ Real.exp ((m : ℝ) / 25) := Real.exp_le_exp.mpr (hexponent.trans habsorb)


/-- The menu width exponent uses only a small fraction of the special-coordinate budget. -/
theorem width_cost_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ δ ≤ (⌊(n : ℝ) ^ (200 * δ)⌋₊ : ℝ) / 100 := by
  have hg : ∀ᶠ n : ℕ in atTop, 200 ≤ (n : ℝ) ^ (199 * δ) :=
    ((_root_.tendsto_rpow_atTop (by positivity : 0 < 199 * δ)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hm : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (200 * δ) :=
    ((_root_.tendsto_rpow_atTop (by positivity : 0 < 200 * δ)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n := Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩
  filter_upwards [hg, hm, hn] with n hg hm hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hf : (n : ℝ) ^ (200 * δ) < (⌊(n : ℝ) ^ (200 * δ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : (n : ℝ) ^ (200 * δ) / 2 ≤ (⌊(n : ℝ) ^ (200 * δ)⌋₊ : ℝ) := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx.le δ)
  have hr : (n : ℝ) ^ (199 * δ) * (n : ℝ) ^ δ = (n : ℝ) ^ (200 * δ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [hr] at hp
  nlinarith

/-- Higher-level selection weights leave a uniformly small per-slice enumeration price. -/
theorem external_cost_eventually (δ c : ℝ) (hδ : 0 < δ) (hδsmall : δ < (1 : ℝ) / 2000)
    (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      1 / (99 / 100 : ℝ) + (topScale n δ (8 * δ) : ℝ) * (n : ℝ) ^ 10 * Real.exp (-(n : ℝ) ^ c) ≤
        Real.exp (1 / 25 : ℝ) := by
  let Hc : ℝ := 2 * (3 : ℝ) ^ ⌈1 / δ⌉₊
  have hlimit : Tendsto (fun n : ℕ => Hc * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c)) atTop (nhds 0) := by
    have hh := (tendsto_const_nhds (x := Hc)).mul (nat_poly_exp_decay c 14 hc)
    have hnum (x : ℝ) : x ^ (14 : ℝ) = x ^ (14 : ℕ) := Real.rpow_natCast x 14
    simpa only [mul_zero, hnum, mul_assoc] using hh
  have hsmall : ∀ᶠ n : ℕ in atTop, Hc * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c) ≤ 1 / 100 :=
    (hlimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100))).mono (fun _ h => h.le)
  have hn : ∀ᶠ n : ℕ in atTop, 2 ≤ n := Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hsmall, hn] with n hsmall hn
  intro m
  have hheight := s10_height_poly δ hδ (by linarith) n hn
  have herr : (topScale n δ (8 * δ) : ℝ) * (n : ℝ) ^ 10 * Real.exp (-(n : ℝ) ^ c) ≤ 1 / 100 := by
    calc
      _ ≤ (Hc * (n : ℝ) ^ 4) * (n : ℝ) ^ 10 * Real.exp (-(n : ℝ) ^ c) := by
        gcongr
      _ = Hc * (n : ℝ) ^ 14 * Real.exp (-(n : ℝ) ^ c) := by ring
      _ ≤ _ := hsmall
  have he : 1 + (1 / 25 : ℝ) ≤ Real.exp (1 / 25 : ℝ) := by
    simpa only [add_comm] using Real.add_one_le_exp (1 / 25 : ℝ)
  calc
    _ ≤ 1 / (99 / 100 : ℝ) + 1 / 100 := add_le_add le_rfl herr
    _ ≤ 1 + (1 / 25 : ℝ) := by norm_num
    _ ≤ _ := he

end HypercubeRamsey.Lane_sol_s10_d56
