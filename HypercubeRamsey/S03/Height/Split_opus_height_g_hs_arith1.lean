import HypercubeRamsey.S03.Height.Selection_p_height_main

namespace HypercubeRamsey

namespace Lane_g_hs_arith1

open Lane_p_height_main

/-- Product of positive prefactor and exp(-X) is bounded by exp(-W)
when log(w) - X ≤ -W. -/
lemma mul_exp_neg_le_exp_neg {w X Z W : ℝ} (hw : 0 < w) (hlog : Real.log w ≤ Z) (hdiff : Z - X ≤ -W) :
    w * Real.exp (-X) ≤ Real.exp (-W) := by
  have hw_le : w ≤ Real.exp Z := by
    rw [← Real.exp_log hw]
    exact Real.exp_le_exp.2 hlog
  have hprod : w * Real.exp (-X) ≤ Real.exp Z * Real.exp (-X) :=
    mul_le_mul_of_nonneg_right hw_le (Real.exp_pos (-X)).le
  rw [← Real.exp_add] at hprod
  have hsum : Z + -X ≤ -W := by linarith [hdiff]
  exact hprod.trans (Real.exp_le_exp.2 hsum)

/-- LEAF (arithmetic, TeX 03:544–547). -/
theorem global_arith_proof (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ)) ≤
        Real.exp (-(n : ℝ) ^ (1 + c)) := by
  have hsz := hp.hsz
  have ha := hp.ha
  have hcd := hp.hd
  have hσ : 0 < σ := hsz.1
  have hζ : 0 < ζ ∧ ζ < 1 := ⟨lt_trans hsz.1 hsz.2.1, hsz.2.2.1⟩
  have hθ : 0 < θ ∧ θ < 1 := ⟨hsz.2.2.2.1, hsz.2.2.2.2⟩
  let c : ℝ := σ / 2
  have hc : 0 < c := half_pos hσ
  have h1c : 1 < 1 + c := by linarith [hc]
  let δ : ℝ := (a + (1 - ζ) * θ) - (1 + c)
  have hδ : 0 < δ := by
    dsimp [δ, c]
    have ha_gt : ζ + σ + (1 - θ) < a := ha.1
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ.2
    have hζpos : 0 < ζ := hζ.1
    calc
      0 < σ / 2 + ζ * (1 - θ) := add_pos (half_pos hσ) (mul_pos hζpos h1θ)
      _ = (ζ + σ + (1 - θ)) + (1 - ζ) * θ - (1 + σ / 2) := by ring
      _ < a + (1 - ζ) * θ - (1 + σ / 2) := by linarith [ha_gt]
  let C_bound : ℝ := C_d * Real.log 2 + 1
  obtain ⟨N_δ, hN_δ⟩ := exists_nat_rpow_ge (e := δ) (C := C_bound) hδ
  let n₀ := max 2 N_δ
  refine ⟨c, hc, n₀, ?_⟩
  intro n d hn hd
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn_δ : N_δ ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have htarget := (hdScaleIndex_spec n σ ζ).1
  have htopScale_eq : topScale n σ ζ = hdScaleRadius n σ (hdScaleIndex n σ ζ) :=
    topScale_eq_hdScaleRadius n σ ζ
  have hceil : (n : ℝ) ^ (1 - ζ) ≤ (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := Nat.le_ceil _
  have htopScale_ge : (n : ℝ) ^ (1 - ζ) ≤ (topScale n σ ζ : ℝ) := by
    rw [htopScale_eq]
    exact hceil.trans (by exact_mod_cast htarget)
  have htopScale_pow : ((n : ℝ) ^ (1 - ζ)) ^ θ ≤ (topScale n σ ζ : ℝ) ^ θ := by
    exact Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) htopScale_ge hθ.1.le
  have hrpow_mul : ((n : ℝ) ^ (1 - ζ)) ^ θ = (n : ℝ) ^ ((1 - ζ) * θ) := by
    rw [← Real.rpow_mul hnpos.le]
  have hscale_lower : (n : ℝ) ^ ((1 - ζ) * θ) ≤ (topScale n σ ζ : ℝ) ^ θ := by
    rw [← hrpow_mul]
    exact htopScale_pow
  have hpow_add : (n : ℝ) ^ a * (n : ℝ) ^ ((1 - ζ) * θ) = (n : ℝ) ^ (a + (1 - ζ) * θ) := by
    rw [← Real.rpow_add hnpos]
  have htotal_lower : (n : ℝ) ^ (a + (1 - ζ) * θ) ≤ (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ := by
    rw [← hpow_add]
    exact mul_le_mul_of_nonneg_left hscale_lower (Real.rpow_nonneg hnpos.le _)
  have hsplit_exp : (n : ℝ) ^ (a + (1 - ζ) * θ) = (n : ℝ) ^ (1 + c) * (n : ℝ) ^ δ := by
    have heq : a + (1 - ζ) * θ = (1 + c) + δ := by dsimp [δ]; ring
    rw [heq, Real.rpow_add hnpos]
  have htotal_lower' : (n : ℝ) ^ (1 + c) * (n : ℝ) ^ δ ≤ (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ := by
    rw [← hsplit_exp]
    exact htotal_lower
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hlog2d : Real.log ((2 : ℝ) ^ d) = (d : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlog2pos : 0 ≤ Real.log 2 := by positivity
  have hd_bound : (d : ℝ) * Real.log 2 ≤ C_d * (n : ℝ) * Real.log 2 := by
    nlinarith [hd, hlog2pos]
  have hn_le_rpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + c) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 h1c.le
  have hd_bound' : Real.log ((2 : ℝ) ^ d) ≤ (C_d * Real.log 2) * (n : ℝ) ^ (1 + c) := by
    rw [hlog2d]
    calc
      (d : ℝ) * Real.log 2 ≤ C_d * (n : ℝ) * Real.log 2 := hd_bound
      _ = (C_d * Real.log 2) * (n : ℝ) := by ring
      _ ≤ (C_d * Real.log 2) * (n : ℝ) ^ (1 + c) := by
        have hCpos : 0 ≤ C_d * Real.log 2 := by
          have hCd : 0 ≤ C_d := hcd.1.le.trans hcd.2
          positivity
        exact mul_le_mul_of_nonneg_left hn_le_rpow hCpos
  have hN_bound : C_bound ≤ (n : ℝ) ^ δ := hN_δ n hn_δ
  have hdiff : (C_d * Real.log 2) * (n : ℝ) ^ (1 + c) - (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ ≤ - (n : ℝ) ^ (1 + c) := by
    calc
      (C_d * Real.log 2) * (n : ℝ) ^ (1 + c) - (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ
        ≤ (C_d * Real.log 2) * (n : ℝ) ^ (1 + c) - (n : ℝ) ^ (1 + c) * (n : ℝ) ^ δ := by
          linarith [htotal_lower']
      _ = ((C_d * Real.log 2) - (n : ℝ) ^ δ) * (n : ℝ) ^ (1 + c) := by ring
      _ ≤ -1 * (n : ℝ) ^ (1 + c) := by
        have hfactor : (C_d * Real.log 2) - (n : ℝ) ^ δ ≤ -1 := by
          dsimp [C_bound] at hN_bound
          linarith [hN_bound]
        exact mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnpos.le _)
      _ = - (n : ℝ) ^ (1 + c) := by ring
  have hdiff' : Real.log ((2 : ℝ) ^ d) - (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ ≤ - (n : ℝ) ^ (1 + c) := by
    linarith [hd_bound', hdiff]
  exact mul_exp_neg_le_exp_neg h2pos le_rfl hdiff'

lemma top_scale_exp_le (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ)) ≤
        Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
  obtain ⟨c, hc, n_g, h_g⟩ := global_arith_proof J₀ b₀ b σ ζ θ a c_d C_d D hp
  have ha1 : a < 1 := hp.ha.2.1.trans (hp.hb.2.1.trans hp.hb.2.2)
  have h1c : 1 < 1 + c := by linarith [hc]
  have hac : a < 1 + c := ha1.trans h1c
  refine ⟨max 2 n_g, ?_⟩
  intro n d hn hd
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hng : n_g ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have h_top := h_g n d hng hd
  have h_mono : (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 + c) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hac.le
  have h_half : (1 / 2 : ℝ) * (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 + c) := by
    have hnpos : (0 : ℝ) ≤ (n : ℝ) ^ a := by positivity
    linarith [h_mono]
  have h_neg : - (n : ℝ) ^ (1 + c) ≤ - ((1 / 2 : ℝ) * (n : ℝ) ^ a) := by
    linarith [h_half]
  exact h_top.trans (Real.exp_le_exp.2 h_neg)

lemma const_mul_exp_neg_le_exp_neg {a c : ℝ} (ha : 0 < a) (_hc : 0 < c) (hca : c < a) (N : ℝ) (hN : 0 < N) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      N * Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) ≤ Real.exp (- (n : ℝ) ^ c) := by
  have hdiff : 0 < a - c := sub_pos.mpr hca
  obtain ⟨N_log, hN_log⟩ := exists_nat_rpow_ge (e := a) (C := 4 * Real.log N) ha
  obtain ⟨N_sub, hN_sub⟩ := exists_nat_rpow_ge (e := a - c) (C := 4) hdiff
  let n₀ := max 2 (max N_log N_sub)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn_log : N_log ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right 2 _) hn)
  have hn_sub : N_sub ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right 2 _) hn)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog_bound : Real.log N ≤ (1 / 4) * (n : ℝ) ^ a := by
    have h1 := hN_log n hn_log
    linarith
  have hsub_bound : (n : ℝ) ^ c ≤ (1 / 4) * (n : ℝ) ^ a := by
    have h1 := hN_sub n hn_sub
    have hmul : 4 * (n : ℝ) ^ c ≤ (n : ℝ) ^ (a - c) * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
    have hpow : (n : ℝ) ^ (a - c) * (n : ℝ) ^ c = (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnpos]
      have : a - c + c = a := by ring
      rw [this]
    linarith [hmul, hpow]
  have hsum_diff : Real.log N - (1 / 2) * (n : ℝ) ^ a ≤ - (n : ℝ) ^ c := by
    linarith [hlog_bound, hsub_bound]
  exact mul_exp_neg_le_exp_neg hN le_rfl hsum_diff

lemma hdScaleMultiplier_le_n {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ1 : σ ≤ 1) :
    hdScaleMultiplier n σ ≤ n := by
  dsimp [hdScaleMultiplier]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have h_rpow : (n : ℝ) ^ σ ≤ (n : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hσ1
    simpa only [Real.rpow_one] using this
  have h_ceil : ⌈(n : ℝ) ^ σ⌉₊ ≤ n := Nat.ceil_le.2 h_rpow
  exact max_le hn h_ceil

lemma hdScaleRadius_lt_n {n : ℕ} {σ ζ : ℝ} (hn : 2 ≤ n) (hζ : 0 < ζ ∧ ζ < 1)
    {k : ℕ} (hk : k < hdScaleIndex n σ ζ) :
    hdScaleRadius n σ k < n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have h_rpow : (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hζ.1] : 1 - ζ ≤ 1)
    simpa only [Real.rpow_one] using this
  have h_ceil : ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ n := Nat.ceil_le.2 h_rpow
  have h_spec := (hdScaleIndex_spec n σ ζ).2 k hk
  exact lt_of_lt_of_le h_spec h_ceil

lemma heightBaseRadius_le_sq :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → heightBaseRadius n ≤ n ^ 2 := by
  obtain ⟨N1, hN1⟩ := heightBaseRadius_le_logsq
  obtain ⟨N2, hN2⟩ := log_le_rpow_eventually (1 / 2) (by norm_num)
  refine ⟨max 4 (max N1 N2), ?_⟩
  intro n hn
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right 4 _) hn)
  have hnN2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right 4 _) hn)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_log : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hN2 n hnN2
  have hlogpos : 0 ≤ Real.log (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.log_nonneg this
  have hlog_sq : (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogpos hn_log 2
  have hrpow_sq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := by
    calc
      ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 1 / 2) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (1 : ℝ) := by
        have : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
        rw [this]
      _ = (n : ℝ) := Real.rpow_one (n : ℝ)
  rw [hrpow_sq] at hlog_sq
  have hR0 := hN1 n hnN1
  have hR0_real : (heightBaseRadius n : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      (heightBaseRadius n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hR0
      _ ≤ 2 * (n : ℝ) := by nlinarith [hlog_sq]
      _ ≤ (n : ℝ) * (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
        nlinarith
      _ = (n : ℝ) ^ 2 := by ring
  exact_mod_cast hR0_real

lemma topScale_le_sq {n : ℕ} {σ ζ : ℝ} (hn : 2 ≤ n) (hσ1 : σ ≤ 1) (hζ : 0 < ζ ∧ ζ < 1)
    (hR0 : heightBaseRadius n ≤ n ^ 2) :
    topScale n σ ζ ≤ n ^ 2 := by
  rw [topScale_eq_hdScaleRadius]
  cases hk : hdScaleIndex n σ ζ with
  | zero =>
      dsimp [hdScaleRadius]
      rw [one_mul]
      exact hR0
  | succ k =>
      rw [hdScaleRadius_succ]
      have hM := hdScaleMultiplier_le_n hn hσ1
      have hR := (hdScaleRadius_lt_n hn hζ (by omega : k < hdScaleIndex n σ ζ)).le
      calc
        hdScaleMultiplier n σ * hdScaleRadius n σ k ≤ n * n := Nat.mul_le_mul hM hR
        _ = n ^ 2 := (sq n).symm

lemma base_scale_exp_le (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      ((topScale n σ ζ + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (2 * D * heightBaseRadius n) *
          Real.exp (-((n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ)) ≤
        Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
  have hsz := hp.hsz
  have ha := hp.ha
  have hσ : 0 < σ := hsz.1
  have hσ1 : σ ≤ 1 := (hsz.2.1.trans hsz.2.2.1).le
  have hζ : 0 < ζ ∧ ζ < 1 := ⟨lt_trans hsz.1 hsz.2.1, hsz.2.2.1⟩
  have hθ : 0 < θ ∧ θ < 1 := ⟨hsz.2.2.2.1, hsz.2.2.2.2⟩
  have ha_pos : 0 < a := by
    have : 0 < ζ + σ + (1 - θ) := by
      have : 0 < 1 - θ := sub_pos.mpr hθ.2
      linarith [hζ.1, hσ]
    linarith [ha.1]
  obtain ⟨N_sq, hN_sq⟩ := heightBaseRadius_le_sq
  obtain ⟨N_rad, hN_rad⟩ := heightBaseRadius_le_logsq
  let t : ℝ := a / 6
  have ht : 0 < t := by dsimp [t]; linarith [ha_pos]
  obtain ⟨N_log, hN_log⟩ := log_le_rpow_eventually t ht
  obtain ⟨N_pow, hN_pow⟩ := exists_nat_rpow_ge (e := a / 2) (C := 2 * (8 * (D : ℝ) + 3)) (by linarith [ha_pos])
  obtain ⟨N_log1, hN_log1⟩ := exists_nat_log_ge 1
  obtain ⟨N_Cd, hN_Cd⟩ := exists_nat_rpow_ge (e := 1) (C := C_d + 1) (by norm_num)
  let n₀ := max 3 (max N_sq (max N_rad (max N_log (max N_pow (max N_log1 N_Cd)))))
  refine ⟨n₀, ?_⟩
  intro n d hn hd
  have hn3 : 3 ≤ n := le_trans (le_max_left 3 _) hn
  have hn2 : 2 ≤ n := by omega
  have hn_sq : N_sq ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right 3 _) hn)
  have hn_rad : N_rad ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_sq _) (le_trans (le_max_right 3 _) hn))
  have hn_log : N_log ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_rad _) (le_trans (le_max_right N_sq _) (le_trans (le_max_right 3 _) hn)))
  have hn_pow : N_pow ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_log _) (le_trans (le_max_right N_rad _) (le_trans (le_max_right N_sq _) (le_trans (le_max_right 3 _) hn))))
  have hn_log1 : N_log1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_pow _) (le_trans (le_max_right N_log _) (le_trans (le_max_right N_rad _) (le_trans (le_max_right N_sq _) (le_trans (le_max_right 3 _) hn)))))
  have hn_Cd : N_Cd ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right N_pow _) (le_trans (le_max_right N_log _) (le_trans (le_max_right N_rad _) (le_trans (le_max_right N_sq _) (le_trans (le_max_right 3 _) hn)))))
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hCd_le : C_d + 1 ≤ (n : ℝ) := by
    have := hN_Cd n hn_Cd
    simpa only [Real.rpow_one] using this
  have hR0_le_sq := hN_sq n hn_sq
  have htop_le_sq : topScale n σ ζ ≤ n ^ 2 := topScale_le_sq hn2 hσ1 hζ hR0_le_sq
  have htop1_le : ((topScale n σ ζ + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h1 : (topScale n σ ζ + 1 : ℕ) ≤ n ^ 3 := by
      calc
        topScale n σ ζ + 1 ≤ n ^ 2 + 1 := Nat.succ_le_succ htop_le_sq
        _ ≤ 2 * n ^ 2 := by
          have : 1 ≤ n ^ 2 := by nlinarith
          omega
        _ ≤ n * n ^ 2 := by
          have : 2 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hn2
          exact this
        _ = n ^ 3 := by ring
    exact_mod_cast h1
  have hd1_le : (d : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
    calc
      (d : ℝ) + 1 ≤ C_d * (n : ℝ) + 1 := by linarith [hd]
      _ ≤ C_d * (n : ℝ) + (n : ℝ) := by linarith [hn1]
      _ = (C_d + 1) * (n : ℝ) := by ring
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hCd_le hnpos.le
      _ = (n : ℝ) ^ 2 := by ring
  have hlog_top : Real.log ((topScale n σ ζ + 1 : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have hpos : 0 < ((topScale n σ ζ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < topScale n σ ζ + 1)
    have hlog := Real.log_le_log hpos htop1_le
    have hpow : Real.log ((n : ℝ) ^ 3) = 3 * Real.log (n : ℝ) := by
      have := Real.log_pow (n : ℝ) 3
      exact_mod_cast this
    rw [hpow] at hlog
    exact hlog
  have hd_le_sq : ((d + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; rfl
    rw [this]
    exact hd1_le
  have hlog_d : Real.log ((d + 1 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hdpos : 0 < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d + 1)
    have hlog := Real.log_le_log hdpos hd_le_sq
    have hpow : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      have := Real.log_pow (n : ℝ) 2
      exact_mod_cast this
    rw [hpow] at hlog
    exact hlog
  let R₀ := heightBaseRadius n
  have hR0_log : (R₀ : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hN_rad n hn_rad
  have hlog_pow_d : Real.log (((d + 1 : ℕ) : ℝ) ^ (2 * D * R₀)) ≤ (8 * (D : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by
    have hdpos : ((d + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d + 1 ≠ 0)
    rw [Real.log_pow]
    have hlogdpos : 0 ≤ Real.log ((d + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d + 1)
      exact Real.log_nonneg this
    calc
      ((2 * D * R₀ : ℕ) : ℝ) * Real.log ((d + 1 : ℕ) : ℝ)
        ≤ ((2 * D * R₀ : ℕ) : ℝ) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_d (by positivity)
      _ = (4 * (D : ℝ)) * (R₀ : ℝ) * Real.log (n : ℝ) := by push_cast; ring
      _ ≤ (4 * (D : ℝ)) * (2 * (Real.log (n : ℝ)) ^ 2) * Real.log (n : ℝ) := by
        have hnonneg : 0 ≤ (4 * (D : ℝ)) * Real.log (n : ℝ) := by
          have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
          have hlog : 0 ≤ Real.log (n : ℝ) := by
            have : 1 ≤ Real.log (n : ℝ) := hN_log1 n hn_log1
            linarith
          positivity
        calc
          (4 * (D : ℝ)) * (R₀ : ℝ) * Real.log (n : ℝ)
            = (R₀ : ℝ) * ((4 * (D : ℝ)) * Real.log (n : ℝ)) := by ring
          _ ≤ (2 * (Real.log (n : ℝ)) ^ 2) * ((4 * (D : ℝ)) * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hR0_log hnonneg
          _ = (4 * (D : ℝ)) * (2 * (Real.log (n : ℝ)) ^ 2) * Real.log (n : ℝ) := by ring
      _ = (8 * (D : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by ring
  let w : ℝ := ((topScale n σ ζ + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (2 * D * R₀)
  have hw_pos : 0 < w := by
    dsimp [w]
    have h1 : 0 < ((topScale n σ ζ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < topScale n σ ζ + 1)
    have h2 : 0 < ((d + 1 : ℕ) : ℝ) ^ (2 * D * R₀) := by positivity
    exact mul_pos h1 h2
  have hw1_ne : ((topScale n σ ζ + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : topScale n σ ζ + 1 ≠ 0)
  have hw2_ne : ((d + 1 : ℕ) : ℝ) ^ (2 * D * R₀) ≠ 0 := by positivity
  have hlog_w : Real.log w ≤ (8 * (D : ℝ) + 3) * (Real.log (n : ℝ)) ^ 3 := by
    dsimp [w]
    rw [Real.log_mul hw1_ne hw2_ne]
    have hlog1 : 1 ≤ Real.log (n : ℝ) := hN_log1 n hn_log1
    have hlog_le_cube : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      calc
        Real.log (n : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by nlinarith [hlog1]
        _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by nlinarith [hlog1]
        _ = (Real.log (n : ℝ)) ^ 3 := by ring
    calc
      Real.log ((topScale n σ ζ + 1 : ℕ) : ℝ) + Real.log (((d + 1 : ℕ) : ℝ) ^ (2 * D * R₀))
        ≤ 3 * Real.log (n : ℝ) + (8 * (D : ℝ)) * (Real.log (n : ℝ)) ^ 3 := add_le_add hlog_top hlog_pow_d
      _ ≤ 3 * (Real.log (n : ℝ)) ^ 3 + (8 * (D : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by nlinarith [hlog_le_cube]
      _ = (8 * (D : ℝ) + 3) * (Real.log (n : ℝ)) ^ 3 := by ring
  have hlog_n_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ (a / 6) := hN_log n hn_log
  have hcube_le : (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ (a / 2) := by
    have hlogpos : 0 ≤ Real.log (n : ℝ) := by
      have : 1 ≤ Real.log (n : ℝ) := hN_log1 n hn_log1
      linarith
    have hpow3 := pow_le_pow_left₀ hlogpos hlog_n_le 3
    have heq : ((n : ℝ) ^ (a / 6)) ^ 3 = (n : ℝ) ^ (a / 2) := by
      calc
        ((n : ℝ) ^ (a / 6)) ^ 3 = (n : ℝ) ^ (a / 6) * (n : ℝ) ^ (a / 6) * (n : ℝ) ^ (a / 6) := by ring
        _ = (n : ℝ) ^ (a / 6 + a / 6 + a / 6) := by
          rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
        _ = (n : ℝ) ^ (a / 2) := by
          have : a / 6 + a / 6 + a / 6 = a / 2 := by ring
          rw [this]
    rw [heq] at hpow3
    exact hpow3
  have hlog_w_le_half : Real.log w ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a := by
    have hDpos : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
    have hcoeff_pos : 0 ≤ 8 * (D : ℝ) + 3 := by linarith
    calc
      Real.log w ≤ (8 * (D : ℝ) + 3) * (Real.log (n : ℝ)) ^ 3 := hlog_w
      _ ≤ (8 * (D : ℝ) + 3) * (n : ℝ) ^ (a / 2) :=
        mul_le_mul_of_nonneg_left hcube_le hcoeff_pos
      _ ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ (a / 2)) * (n : ℝ) ^ (a / 2) := by
        have hC := hN_pow n hn_pow
        have : 8 * (D : ℝ) + 3 ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (a / 2) := by linarith [hC]
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hnpos.le _)
      _ = (1 / 2 : ℝ) * ((n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2)) := by ring
      _ = (1 / 2 : ℝ) * (n : ℝ) ^ a := by
        have : (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) = (n : ℝ) ^ a := by
          rw [← Real.rpow_add hnpos]
          have : a / 2 + a / 2 = a := by ring
          rw [this]
        rw [this]
  let X : ℝ := (n : ℝ) ^ a * (R₀ : ℝ) ^ θ
  have hX_ge : (n : ℝ) ^ a ≤ X := by
    dsimp [X]
    have hR0_ge1 : (1 : ℝ) ≤ (R₀ : ℝ) := by
      have : 1 ≤ R₀ := by dsimp [R₀, heightBaseRadius]; omega
      exact_mod_cast this
    have hR0_pow : 1 ≤ (R₀ : ℝ) ^ θ := by
      simpa using Real.one_le_rpow hR0_ge1 hθ.1.le
    calc
      (n : ℝ) ^ a = (n : ℝ) ^ a * 1 := by ring
      _ ≤ (n : ℝ) ^ a * (R₀ : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_left hR0_pow (Real.rpow_nonneg hnpos.le _)
  have hdiff : Real.log w - X ≤ - ((1 / 2 : ℝ) * (n : ℝ) ^ a) := by
    linarith [hlog_w_le_half, hX_ge]
  exact mul_exp_neg_le_exp_neg hw_pos le_rfl hdiff

lemma hdScaleRadius_ge_one (n : ℕ) (σ : ℝ) (i : ℕ) : 1 ≤ hdScaleRadius n σ i := by
  dsimp [hdScaleRadius]
  have hR0 : 1 ≤ heightBaseRadius n := by dsimp [heightBaseRadius]; omega
  have hM : 1 ≤ hdScaleMultiplier n σ := by dsimp [hdScaleMultiplier]; omega
  have hpow : 1 ≤ (hdScaleMultiplier n σ) ^ i := one_le_pow₀ hM
  nlinarith

lemma hdScaleMultiplier_le_two_rpow {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    (hdScaleMultiplier n σ : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
  dsimp [hdScaleMultiplier]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h1_le_pow : (1 : ℝ) ≤ (n : ℝ) ^ σ := by
    simpa using Real.one_le_rpow hn1 hσ
  have hceil : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos σ)
    linarith [hlt, h1_le_pow]
  have h2 : (2 : ℝ) ≤ 2 * (n : ℝ) ^ σ := by linarith [h1_le_pow]
  have hmax : ((max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℕ) : ℝ) = max (2 : ℝ) (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := by
    push_cast; rfl
  rw [hmax]
  exact max_le h2 hceil

lemma hdScaleRadius_le_two_rpow {n : ℕ} {σ ζ : ℝ} (hn : 2 ≤ n) (hζ : 0 < ζ ∧ ζ < 1)
    {i : ℕ} (hi : i < hdScaleIndex n σ ζ) :
    (hdScaleRadius n σ i : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h1_le_pow : (1 : ℝ) ≤ (n : ℝ) ^ (1 - ζ) := by
    have : 0 ≤ 1 - ζ := by linarith [hζ.2]
    simpa using Real.one_le_rpow hn1 this
  have hceil : (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
    have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos (1 - ζ))
    linarith [hlt, h1_le_pow]
  have hspec := (hdScaleIndex_spec n σ ζ).2 i hi
  have hcast : (hdScaleRadius n σ i : ℝ) ≤ (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := by
    exact_mod_cast hspec.le
  exact hcast.trans hceil

lemma mid_scale_sum_exp_le (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      (∑ i ∈ Finset.range (hdScaleIndex n σ ζ),
        ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
          Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ))) ≤
      (⌈1 / σ⌉₊ : ℝ) * Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
  have hsz := hp.hsz
  have ha := hp.ha
  have hσ : 0 < σ := hsz.1
  have hζ : 0 < ζ ∧ ζ < 1 := ⟨lt_trans hsz.1 hsz.2.1, hsz.2.2.1⟩
  have hθ : 0 < θ ∧ θ < 1 := ⟨hsz.2.2.2.1, hsz.2.2.2.2⟩
  have ha_pos : 0 < a := by
    have : 0 < ζ + σ + (1 - θ) := by
      have : 0 < 1 - θ := sub_pos.mpr hθ.2
      linarith [hζ.1, hσ]
    linarith [ha.1]
  let γ : ℝ := σ + (1 - ζ) * (1 - θ)
  have hγ_lt_a : γ < a := by
    dsimp [γ]
    have ha_gt : ζ + σ + (1 - θ) < a := ha.1
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ.2
    have hζpos : 0 < ζ := hζ.1
    calc
      σ + (1 - ζ) * (1 - θ) < σ + (1 - θ) := by
        have : (1 - ζ) * (1 - θ) < 1 - θ := by
          have : 1 - ζ < 1 := by linarith [hζ.1]
          nlinarith
        linarith
      _ < ζ + σ + (1 - θ) := by linarith [hζpos]
      _ < a := ha_gt
  let δ : ℝ := a - γ
  have hδ : 0 < δ := sub_pos.mpr hγ_lt_a
  let t : ℝ := δ / 2
  have ht : 0 < t := half_pos hδ
  obtain ⟨N_log, hN_log⟩ := log_le_rpow_eventually t ht
  obtain ⟨N_pow, hN_pow⟩ := exists_nat_rpow_ge (e := δ / 2) (C := 2 * (8 * (D : ℝ))) (half_pos hδ)
  obtain ⟨N_log1, hN_log1⟩ := exists_nat_log_ge 1
  obtain ⟨N_Cd, hN_Cd⟩ := exists_nat_rpow_ge (e := 1) (C := C_d + 1) (by norm_num)
  let n₀ := max 2 (max N_log (max N_pow (max N_log1 N_Cd)))
  refine ⟨n₀, ?_⟩
  intro n d hn hd
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 _) hn
  have hn_log : N_log ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right 2 _) hn)
  have hn_pow : N_pow ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_log _) (le_trans (le_max_right 2 _) hn))
  have hn_log1 : N_log1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right N_pow _) (le_trans (le_max_right N_log _) (le_trans (le_max_right 2 _) hn)))
  have hn_Cd : N_Cd ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right N_pow _) (le_trans (le_max_right N_log _) (le_trans (le_max_right 2 _) hn)))
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hCd_le : C_d + 1 ≤ (n : ℝ) := by
    have := hN_Cd n hn_Cd
    simpa only [Real.rpow_one] using this
  have hd1_le : (d : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
    calc
      (d : ℝ) + 1 ≤ C_d * (n : ℝ) + 1 := by linarith [hd]
      _ ≤ C_d * (n : ℝ) + (n : ℝ) := by linarith [hn1]
      _ = (C_d + 1) * (n : ℝ) := by ring
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hCd_le hnpos.le
      _ = (n : ℝ) ^ 2 := by ring
  have hd_le_sq : ((d + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; rfl
    rw [this]
    exact hd1_le
  have hlog_d : Real.log ((d + 1 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hdpos : 0 < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d + 1)
    have hlog := Real.log_le_log hdpos hd_le_sq
    have hpow : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      have := Real.log_pow (n : ℝ) 2
      exact_mod_cast this
    rw [hpow] at hlog
    exact hlog
  have h_term_le : ∀ i, i < hdScaleIndex n σ ζ →
      ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
        Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) ≤
      Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
    intro i hi
    let R_i := hdScaleRadius n σ i
    let R_next := hdScaleRadius n σ (i + 1)
    have hRi_pos : 0 < (R_i : ℝ) := by
      have : 1 ≤ R_i := hdScaleRadius_ge_one n σ i
      exact_mod_cast (by omega : 0 < R_i)
    have hRi1_cast : (R_next : ℝ) = (hdScaleMultiplier n σ : ℝ) * (R_i : ℝ) := by
      dsimp [R_next, R_i]
      rw [hdScaleRadius_succ]
      push_cast
      rfl
    have hM_le : (hdScaleMultiplier n σ : ℝ) ≤ 2 * (n : ℝ) ^ σ :=
      hdScaleMultiplier_le_two_rpow hn2 hsz.1.le
    have hRi_le : (R_i : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) :=
      hdScaleRadius_le_two_rpow hn2 hζ hi
    have hRi_split : (R_i : ℝ) = (R_i : ℝ) ^ (1 - θ) * (R_i : ℝ) ^ θ := by
      rw [← Real.rpow_add hRi_pos]
      have : 1 - θ + θ = 1 := by ring
      rw [this, Real.rpow_one]
    have hRi_1_θ : (R_i : ℝ) ^ (1 - θ) ≤ 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by
      have h1θ_pos : 0 ≤ 1 - θ := by linarith [hθ.2]
      have h1θ_le1 : 1 - θ ≤ 1 := by linarith [hθ.1]
      have hRi_nonneg : 0 ≤ (R_i : ℝ) := by positivity
      have hpow := Real.rpow_le_rpow hRi_nonneg hRi_le h1θ_pos
      have hmul : (2 * (n : ℝ) ^ (1 - ζ)) ^ (1 - θ) = (2 : ℝ) ^ (1 - θ) * ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := by
        exact Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le _)
      have h2_pow : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1θ_le1
      have hrpow_mul : ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) = (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by
        rw [← Real.rpow_mul hnpos.le]
      calc
        (R_i : ℝ) ^ (1 - θ) ≤ (2 * (n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := hpow
        _ = (2 : ℝ) ^ (1 - θ) * ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := hmul
        _ ≤ 2 * ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) :=
          mul_le_mul_of_nonneg_right h2_pow (by positivity)
        _ = 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by rw [hrpow_mul]
    have hRi_bound : (R_i : ℝ) ≤ 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) * (R_i : ℝ) ^ θ := by
      calc
        (R_i : ℝ) = (R_i : ℝ) ^ (1 - θ) * (R_i : ℝ) ^ θ := hRi_split
        _ ≤ 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) * (R_i : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right hRi_1_θ (by positivity)
    have hRi1_bound : (R_next : ℝ) ≤ 4 * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ := by
      rw [hRi1_cast]
      have hprod : (hdScaleMultiplier n σ : ℝ) * (R_i : ℝ)
          ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) * (R_i : ℝ) ^ θ) := by
        have h1 := mul_le_mul hM_le hRi_bound (by positivity) (by positivity)
        exact h1
      have hpow_add : (n : ℝ) ^ σ * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) = (n : ℝ) ^ γ := by
        dsimp [γ]
        rw [← Real.rpow_add hnpos]
      calc
        (hdScaleMultiplier n σ : ℝ) * (R_i : ℝ)
          ≤ (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) * (R_i : ℝ) ^ θ) := hprod
        _ = 4 * ((n : ℝ) ^ σ * (n : ℝ) ^ ((1 - ζ) * (1 - θ))) * (R_i : ℝ) ^ θ := by ring
        _ = 4 * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ := by rw [hpow_add]
    let w_i : ℝ := ((d + 1 : ℕ) : ℝ) ^ (D * R_next)
    have hw_pos : 0 < w_i := by positivity
    have hlog_pow : Real.log w_i ≤ (8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ := by
      dsimp [w_i]
      have hdpos : ((d + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d + 1 ≠ 0)
      rw [Real.log_pow]
      calc
        ((D * R_next : ℕ) : ℝ) * Real.log ((d + 1 : ℕ) : ℝ)
          ≤ ((D * R_next : ℕ) : ℝ) * (2 * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_d (by positivity)
        _ = (2 * Real.log (n : ℝ) * (D : ℝ)) * (R_next : ℝ) := by push_cast; ring
        _ ≤ (2 * Real.log (n : ℝ) * (D : ℝ)) * (4 * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ) := by
          have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
            have : 1 ≤ Real.log (n : ℝ) := hN_log1 n hn_log1
            linarith
          have hD_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
          exact mul_le_mul_of_nonneg_left hRi1_bound (by positivity)
        _ = (8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ := by ring
    have hlog_n_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ (δ / 2) := hN_log n hn_log
    have hlog_mul_γ : Real.log (n : ℝ) * (n : ℝ) ^ γ ≤ (n : ℝ) ^ (a - δ / 2) := by
      have hlogpos : 0 ≤ Real.log (n : ℝ) := by
        have : 1 ≤ Real.log (n : ℝ) := hN_log1 n hn_log1
        linarith
      have hγ_nonneg : 0 ≤ (n : ℝ) ^ γ := by positivity
      have h1 := mul_le_mul_of_nonneg_right hlog_n_le hγ_nonneg
      have hpow_add : (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ γ = (n : ℝ) ^ (a - δ / 2) := by
        rw [← Real.rpow_add hnpos]
        have : δ / 2 + γ = a - δ / 2 := by
          dsimp [δ]
          ring
        rw [this]
      exact h1.trans (by rw [hpow_add])
    have hcoeff_bound : (8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a := by
      have hDpos : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
      calc
        (8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ
          = (8 * (D : ℝ)) * (Real.log (n : ℝ) * (n : ℝ) ^ γ) := by ring
        _ ≤ (8 * (D : ℝ)) * (n : ℝ) ^ (a - δ / 2) :=
          mul_le_mul_of_nonneg_left hlog_mul_γ (by positivity)
        _ ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ (δ / 2)) * (n : ℝ) ^ (a - δ / 2) := by
          have hC := hN_pow n hn_pow
          have : 8 * (D : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (δ / 2) := by linarith [hC]
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hnpos.le _)
        _ = (1 / 2 : ℝ) * ((n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (a - δ / 2)) := by ring
        _ = (1 / 2 : ℝ) * (n : ℝ) ^ a := by
          have : (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (a - δ / 2) = (n : ℝ) ^ a := by
            rw [← Real.rpow_add hnpos]
            have : δ / 2 + (a - δ / 2) = a := by ring
            rw [this]
          rw [this]
    have hlog_wi_le : Real.log w_i ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ := by
      calc
        Real.log w_i ≤ (8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ * (R_i : ℝ) ^ θ := hlog_pow
        _ = ((8 * (D : ℝ)) * Real.log (n : ℝ) * (n : ℝ) ^ γ) * (R_i : ℝ) ^ θ := by ring
        _ ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ a) * (R_i : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right hcoeff_bound (by positivity)
        _ = (1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ := by ring
    let X_i : ℝ := (n : ℝ) ^ a * (R_i : ℝ) ^ θ
    have hdiff_Ri : Real.log w_i - X_i ≤ - ((1 / 2 : ℝ) * (n : ℝ) ^ a) := by
      dsimp [X_i]
      have hRi_ge1 : 1 ≤ (R_i : ℝ) := by
        have : 1 ≤ R_i := hdScaleRadius_ge_one n σ i
        exact_mod_cast this
      have hRi_θ_ge1 : 1 ≤ (R_i : ℝ) ^ θ := by
        simpa using Real.one_le_rpow hRi_ge1 hθ.1.le
      have hsub : (1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ - (n : ℝ) ^ a * (R_i : ℝ) ^ θ
          = - ((1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ) := by ring
      have hneg_mono : - ((1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ) ≤ - ((1 / 2 : ℝ) * (n : ℝ) ^ a) := by
        have : (1 / 2 : ℝ) * (n : ℝ) ^ a ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ := by
          calc
            (1 / 2 : ℝ) * (n : ℝ) ^ a = (1 / 2 : ℝ) * (n : ℝ) ^ a * 1 := by ring
            _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ a * (R_i : ℝ) ^ θ :=
              mul_le_mul_of_nonneg_left hRi_θ_ge1 (by positivity)
        linarith
      linarith [hlog_wi_le]
    exact mul_exp_neg_le_exp_neg hw_pos le_rfl hdiff_Ri
  have hterms : ∀ i ∈ Finset.range (hdScaleIndex n σ ζ),
      ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
        Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) ≤
      Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
    intro i hi
    have hilt : i < hdScaleIndex n σ ζ := Finset.mem_range.mp hi
    exact h_term_le i hilt
  have hsum_le := Finset.sum_le_sum hterms
  have hcard : (Finset.range (hdScaleIndex n σ ζ)).card = hdScaleIndex n σ ζ :=
    Finset.card_range _
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum_le
  have h_h_le : (hdScaleIndex n σ ζ : ℝ) ≤ (⌈1 / σ⌉₊ : ℝ) := by
    exact_mod_cast hdScaleIndex_le_ceil_inv_sigma hn2 hsz.1 ⟨lt_trans hsz.1 hsz.2.1, hsz.2.2.1⟩
  have hexp_nonneg : 0 ≤ Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) :=
    (Real.exp_pos _).le
  exact hsum_le.trans (mul_le_mul_of_nonneg_right h_h_le hexp_nonneg)

/-- LEAF (arithmetic, TeX 03:555–569). -/
theorem positive_arith_proof (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      ((topScale n σ ζ + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (2 * D * heightBaseRadius n) *
          Real.exp (-((n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ)) +
        (∑ i ∈ Finset.range (hdScaleIndex n σ ζ),
          ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
            Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) +
        (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ))) ≤
      Real.exp (-(n : ℝ) ^ c) := by
  have ha_pos : 0 < a := by
    have : 0 < ζ + σ + (1 - θ) := by
      have : 0 < 1 - θ := sub_pos.mpr hp.hsz.2.2.2.2
      linarith [hp.hsz.2.1, hp.hsz.1]
    linarith [hp.ha.1]
  let c : ℝ := a / 2
  have hc : 0 < c := half_pos ha_pos
  have hca : c < a := by dsimp [c]; linarith [ha_pos]
  let N : ℝ := (⌈1 / σ⌉₊ : ℝ) + 2
  have hN : 0 < N := by
    dsimp [N]
    have : 0 ≤ (⌈1 / σ⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨n_base, hn_base⟩ := base_scale_exp_le J₀ b₀ b σ ζ θ a c_d C_d D hp
  obtain ⟨n_mid, hn_mid⟩ := mid_scale_sum_exp_le J₀ b₀ b σ ζ θ a c_d C_d D hp
  obtain ⟨n_top, hn_top⟩ := top_scale_exp_le J₀ b₀ b σ ζ θ a c_d C_d D hp
  obtain ⟨n_const, hn_const⟩ := const_mul_exp_neg_le_exp_neg ha_pos hc hca N hN
  let n₀ := max n_base (max n_mid (max n_top n_const))
  refine ⟨c, hc, n₀, ?_⟩
  intro n d hn hd
  have hnb : n_base ≤ n := le_trans (le_max_left _ _) hn
  have hnm : n_mid ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right n_base _) hn)
  have hnt : n_top ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right n_mid _) (le_trans (le_max_right n_base _) hn))
  have hnc : n_const ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right n_mid _) (le_trans (le_max_right n_base _) hn))
  have hb := hn_base n d hnb hd
  have hm := hn_mid n d hnm hd
  have ht := hn_top n d hnt hd
  have hc_bound := hn_const n hnc
  have hsum :
      ((topScale n σ ζ + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (2 * D * heightBaseRadius n) *
          Real.exp (-((n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ)) +
        (∑ i ∈ Finset.range (hdScaleIndex n σ ζ),
          ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
            Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) +
        (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ))) ≤
      N * Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by
    dsimp [N]
    calc
      _ ≤ Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) +
          ((⌈1 / σ⌉₊ : ℝ) * Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) +
            Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a))) :=
        add_le_add hb (add_le_add hm ht)
      _ = ((⌈1 / σ⌉₊ : ℝ) + 2) * Real.exp (- ((1 / 2 : ℝ) * (n : ℝ) ^ a)) := by ring
  exact hsum.trans hc_bound

end Lane_g_hs_arith1


end HypercubeRamsey
