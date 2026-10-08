import HypercubeRamsey.S05.Centres_sol_s05_centres_height

namespace HypercubeRamsey.Lane_sol_s05_j5

open Classical Filter Real OAI.HypercubeRamsey
open scoped Topology

noncomputable section
set_option maxHeartbeats 400000
variable {γ K' χ : ℝ}

theorem power_small (p : Params5 γ K' χ) (D c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, D * (p.m n : ℝ) ^ a ≤ c * (p.m n : ℝ) ^ b := by
  filter_upwards [Lane_sol_s05_h5l.fixed_power_margin p (D / c) a b hab] with n hn
  have hh : D * (p.m n : ℝ) ^ a / c ≤ (p.m n : ℝ) ^ b := by
    simpa only [div_mul_eq_mul_div] using hn
  simpa only [mul_comm] using (div_le_iff₀ hc).mp hh

theorem id_cost_eventually (p : Params5 γ K' χ) (cL cH : ℝ) (hL : 0 < cL) (hH : 0 < cH) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (p.T n : ℝ) * log (8 * (n : ℝ) ^ 11) ≤ cL / 8 * (p.kPrime n j : ℝ) ∧
        (p.T n : ℝ) * log (8 * (n : ℝ) ^ 11) ≤ cH / 12 * (p.s n : ℝ) := by
  let A : ℝ := log 8 + 11 / p.alpha
  have hA : 0 < A := by dsimp [A]; have := p.halpha.1; positivity
  have hK2 := p.hK2
  have hKs := p.hKs
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hlog := Real.tendsto_log_atTop.comp hm
  have hj := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [eventually_ge_atTop (1 : ℕ), hm.eventually_gt_atTop 1,
    hlog.eventually_ge_atTop 1, hj.eventually_ge_atTop 2,
    power_small p (2000 * A) (cL * p.K2 / 8) (1 / 500) (1 / 50)
      (by positivity) (by norm_num),
    power_small p (2000 * A) (cH * p.Ks / 24) (1 / 500) (1 / 20)
      (by positivity) (by norm_num)] with n hn hm1 hlog1 hJraw hlow hhigh j
  dsimp only [Function.comp_apply] at hlog1 hJraw
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmnat : 1 < p.m n := by exact_mod_cast hm1
  have hM : (1 : ℝ) ≤ p.m n := hm1.le
  have hlog0 : 0 ≤ log (p.m n : ℝ) := log_nonneg hM
  have hloglo : p.alpha * log (n : ℝ) ≤ log (p.m n : ℝ) := by
    have hh := log_le_log (rpow_pos_of_pos hnpos p.alpha) (Nat.le_ceil ((n : ℝ) ^ p.alpha))
    simpa only [Params5.m, log_rpow hnpos] using hh
  have hlogn : log (n : ℝ) ≤ log (p.m n : ℝ) / p.alpha :=
    (le_div_iff₀ p.halpha.1).mpr (by simpa only [mul_comm] using hloglo)
  have hU : log (8 * (n : ℝ) ^ 11) ≤ A * log (p.m n : ℝ) := by
    rw [log_mul (by norm_num) (by positivity), log_pow]
    have h8 := mul_le_mul_of_nonneg_left hlog1 (log_pos (by norm_num : (1 : ℝ) < 8)).le
    have h11 := mul_le_mul_of_nonneg_left hlogn (by norm_num : (0 : ℝ) ≤ 11)
    dsimp only [A]
    have hdiv : 11 / p.alpha * log (p.m n : ℝ) = 11 * (log (p.m n : ℝ) / p.alpha) := by ring
    rw [add_mul, hdiv]
    norm_num at *
    linarith
  have hlogpow : log (p.m n : ℝ) ≤ 1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) := by
    have hh := log_le_rpow_div (Nat.cast_nonneg (p.m n)) (by norm_num : (0 : ℝ) < 1 / 1000)
    convert hh using 1 <;> ring
  have hT := Lane_sol_s05_h5l.T_upper p n hM
  have hcost : (p.T n : ℝ) * log (8 * (n : ℝ) ^ 11) ≤
      2000 * A * (p.m n : ℝ) ^ (1 / 500 : ℝ) := by
    calc
      _ ≤ (p.T n : ℝ) * (A * log (p.m n : ℝ)) :=
        mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg _)
      _ ≤ (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) *
          (A * (1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ))) := by gcongr
      _ = _ := by
        rw [show (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) *
          (A * (1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ))) =
            2000 * A * ((p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) by ring,
          ← rpow_add (by linarith : (0 : ℝ) < p.m n)]
        norm_num
  have hk := Lane_sol_s05_h5l.kPrime_lower p n j hmnat
  have hk0 : p.K2 * (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (p.kPrime n j : ℝ) := by
    have hrest : 0 ≤ ((j : ℝ) + 3) * log (p.m n : ℝ) := by positivity
    nlinarith [p.hK2]
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJ : (p.m n : ℝ) ^ (1 / 20 : ℝ) / 2 ≤ (p.J n : ℝ) := by linarith
  have hs : p.Ks * (p.J n : ℝ) * log (p.m n : ℝ) ≤ (p.s n : ℝ) := Nat.le_ceil _
  have hs0 : p.Ks / 2 * (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ (p.s n : ℝ) := by
    have hJl := mul_le_mul_of_nonneg_left hlog1 (mul_nonneg p.hKs.le (Nat.cast_nonneg (p.J n)))
    have hJK := mul_le_mul_of_nonneg_left hJ p.hKs.le
    nlinarith
  constructor
  · exact (hcost.trans hlow).trans (by nlinarith [mul_le_mul_of_nonneg_left hk0 hL.le])
  · exact (hcost.trans hhigh).trans (by nlinarith [mul_le_mul_of_nonneg_left hs0 hH.le])

def familyRequest (C : ℝ) (cL cH : Pre15 → ℝ) : ParamReq5 :=
  Lane_sol_s05_h5l.stage5Request C (fun x => cL x / 6) (fun x => cH x / 3)

theorem family_budget_eventually (p : Params5 γ K' χ) (C : ℝ) (cL cH : Pre15 → ℝ)
    (hc : ∀ x, 0 < cL x ∧ 0 < cH x) (hp : (familyRequest C cL cH).Holds p) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (8 * (n : ℝ) ^ 11) ^ p.T n *
        exp (C * ((p.T n : ℝ) * log (p.T n) + ((j : ℝ) + 1) * log (p.m n) +
          (if j = p.J n then (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) else 0))) *
        exp (-(cL p.pre1 / 4 * p.kPrime n j)) ≤ exp (-4) ∧
      (8 * (n : ℝ) ^ 11) ^ p.T n *
        exp (C * ((p.T n : ℝ) * log (p.T n) + ((p.J n : ℝ) + 1) * log (p.m n))) *
        exp (-(cH p.pre1 / 6 * p.s n)) ≤ exp (-4) := by
  have hcd : ∀ x, 0 < cL x / 6 ∧ 0 < cH x / 3 := fun x =>
    ⟨div_pos (hc x).1 (by norm_num), div_pos (hc x).2 (by norm_num)⟩
  have hb := Lane_sol_s05_h5l.stage5_request_budgets p C
    (fun x => cL x / 6) (fun x => cH x / 3) hcd hp
  have hlow := Lane_sol_s05_h5l.low_group_budget_eventually p C (cL p.pre1 / 6) (hcd p.pre1).1 hb.2.1
  have hhigh := Lane_sol_s05_h5l.high_group_budget_eventually p C (cH p.pre1 / 3) (hcd p.pre1).2 hb.2.2
  have hsmall : ∀ᶠ n : ℕ in atTop, Lane_sol_s05_h5l.groupEps p n / 3 ≤ exp (-4) := by
    filter_upwards [(Real.tendsto_log_atTop.comp (Lane_sol_s05_h1.tendsto_m p)).eventually_ge_atTop 1] with n hn
    dsimp only [Function.comp_apply] at hn
    have hh : exp (-12 * log (p.m n : ℝ)) ≤ exp (-4) := by gcongr; linarith
    unfold Lane_sol_s05_h5l.groupEps
    linarith [exp_pos (-12 * log (p.m n : ℝ))]
  filter_upwards [id_cost_eventually p (cL p.pre1) (cH p.pre1) (hc p.pre1).1 (hc p.pre1).2,
    hlow, hhigh, hsmall, eventually_ge_atTop (1 : ℕ)] with n hi hl hh hs hn j
  have hU : 0 < 8 * (n : ℝ) ^ 11 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have heL : (8 * (n : ℝ) ^ 11) ^ p.T n * exp (-(cL p.pre1 / 4 * p.kPrime n j)) ≤
      exp (-(cL p.pre1 / 8 * p.kPrime n j)) := by
    rw [Lane_sol_s05_h5l.nat_power_exp _ hU, ← exp_add]
    apply exp_le_exp.mpr
    linarith [(hi j).1]
  have heH : (8 * (n : ℝ) ^ 11) ^ p.T n * exp (-(cH p.pre1 / 6 * p.s n)) ≤
      exp (-(cH p.pre1 / 12 * p.s n)) := by
    rw [Lane_sol_s05_h5l.nat_power_exp _ hU, ← exp_add]
    apply exp_le_exp.mpr
    linarith [(hi j).2]
  constructor
  · have hl' := hl j
    have hrate : 3 * (cL p.pre1 / 6) / 4 = cL p.pre1 / 8 := by ring
    rw [hrate] at hl'
    have hc0 := exp_pos (C * ((p.T n : ℝ) * log (p.T n) + ((j : ℝ) + 1) * log (p.m n) +
      (if j = p.J n then (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) else 0)))
    have hmul := mul_le_mul_of_nonneg_left heL hc0.le
    nlinarith [exp_pos (-(cL p.pre1 / 8 * p.kPrime n j))]
  · have hrate : -(cH p.pre1 / 3 * (p.s n : ℝ)) / 4 = -(cH p.pre1 / 12 * p.s n) := by ring
    rw [hrate] at hh
    have hmul := mul_le_mul_of_nonneg_left heH
      (exp_pos (C * ((p.T n : ℝ) * log (p.T n) + ((p.J n : ℝ) + 1) * log (p.m n)))).le
    nlinarith

theorem family_global_tail (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n * ((topScale n (p.alpha / 1000000) (p.alpha / 100000) : ℝ) + 1) *
        exp (-4) ^ n ≤ exp (-sqrt n) / 3 := by
  have hσ : 0 < p.alpha / 1000000 := by linarith [p.halpha.1]
  have hζ : p.alpha / 100000 < 1 := by linarith [p.halpha.2]
  have ht := Lane_sol_s05_centres.topScale_power_bound (p.alpha / 1000000) (p.alpha / 100000) hσ hζ
  have he : Tendsto (fun n : ℕ => 15 * (n : ℝ) * exp (-(n : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, pow_one, mul_assoc, mul_zero] using hh.const_mul 15
  filter_upwards [ht, he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℕ)] with n htop hsmall hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hH : (topScale n (p.alpha / 1000000) (p.alpha / 100000) : ℝ) + 1 ≤ 5 * n := by
    have hh := rpow_le_rpow_of_exponent_le hnR
      (show 1 + p.alpha / 1000000 - p.alpha / 100000 ≤ 1 by linarith [p.halpha.1])
    rw [rpow_one] at hh
    linarith
  have h15 : 15 * (n : ℝ) ≤ exp n := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le (exp_pos (n : ℝ)).le
    rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at hh
    exact hh
  have hsqrt : sqrt (n : ℝ) ≤ n := by
    rw [sqrt_le_iff]
    exact ⟨hnpos.le, by nlinarith⟩
  have hlog2 : log 2 ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hnum : (2 : ℝ) ^ n * (5 * n) * exp (-4) ^ n ≤ exp (-sqrt n) / 3 := by
    rw [Lane_sol_s05_h5l.nat_power_exp 2 (by norm_num), ← exp_nat_mul]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    calc
      _ = (15 * (n : ℝ)) * exp ((n : ℝ) * log 2 + (n : ℝ) * (-4)) := by rw [exp_add]; ring
      _ ≤ exp n * exp ((n : ℝ) * log 2 + (n : ℝ) * (-4)) :=
        mul_le_mul_of_nonneg_right h15 (exp_pos _).le
      _ = exp ((n : ℝ) + (n : ℝ) * log 2 + (n : ℝ) * (-4)) := by rw [← exp_add]; congr 1; ring
      _ ≤ exp (-sqrt n) := by
        apply exp_le_exp.mpr
        nlinarith
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by positivity))
    (pow_nonneg (exp_pos _).le n)).trans hnum

theorem family_size_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 0 < p.T n ∧ (p.T n : ℝ) ≤ (n : ℝ) ^ (10 : ℕ) / 2 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 1,
    Lane_sol_s05_centres.nat_power_margin 2 1 10 (by norm_num)] with n hn hm hp
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM : 1 ≤ p.m n := by exact_mod_cast hm
  have hmle : p.m n ≤ n := by
    change ⌈(n : ℝ) ^ p.alpha⌉₊ ≤ n
    apply Nat.ceil_le.mpr
    exact (rpow_le_rpow_of_exponent_le hnR (by linarith [p.halpha.2])).trans_eq (rpow_one _)
  have ht : p.T n ≤ p.m n := by
    change ⌈(p.m n : ℝ) ^ (1 / 1000 : ℝ)⌉₊ ≤ p.m n
    apply Nat.ceil_le.mpr
    exact (rpow_le_rpow_of_exponent_le hm (by norm_num)).trans_eq (rpow_one _)
  have hT : 0 < p.T n := by
    have hh : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.T n : ℝ) := Nat.le_ceil _
    have hpos : (0 : ℝ) < p.m n := by linarith
    exact_mod_cast (rpow_pos_of_pos hpos (1 / 1000 : ℝ)).trans_le hh
  have htn : (p.T n : ℝ) ≤ n := by exact_mod_cast ht.trans hmle
  rw [rpow_one] at hp
  simp only [Real.rpow_ofNat] at hp
  refine ⟨hn, hT, (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_right htn (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by simpa only [mul_comm] using hp)

end
end HypercubeRamsey.Lane_sol_s05_j5
