import HypercubeRamsey.S05.Centres_sol_s05_k1_lookup

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical Filter Real
open scoped Topology

noncomputable section
set_option maxHeartbeats 400000

variable {γ K' χ : ℝ}

def positionBudget (n H : ℕ) : ℝ :=
  (n : ℝ) * (H + 1 : ℕ) * (2 * (n : ℝ) ^ (10 : ℝ))

theorem positionBudget_nonneg (n H : ℕ) : 0 ≤ positionBudget n H := by
  unfold positionBudget
  positivity

theorem positionBudget_log (n H : ℕ) (hn : 4 ≤ n) (hH : H ≤ n) :
    log (positionBudget n H + 1) ≤ 14 * log (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hHR : (H : ℝ) ≤ n := by exact_mod_cast hH
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h12 : (1 : ℝ) ≤ (n : ℝ) ^ 12 := one_le_pow₀ hn1
  have hb : positionBudget n H + 1 ≤ (n : ℝ) ^ 14 := by
    unfold positionBudget
    rw [show (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ (10 : ℕ) from rpow_natCast _ _]
    push_cast
    have hh : (n : ℝ) * ((H : ℝ) + 1) * (2 * (n : ℝ) ^ 10) ≤ 4 * (n : ℝ) ^ 12 := by
      have h := mul_le_mul_of_nonneg_left (show (H : ℝ) + 1 ≤ 2 * n by linarith)
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * (n : ℝ) ^ 10)
      convert h' using 1 <;> ring
    have he : (n : ℝ) ^ 14 = (n : ℝ) ^ 12 * (n : ℝ) ^ 2 := by ring
    rw [he]
    have h2 : (16 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    calc
      _ ≤ 4 * (n : ℝ) ^ 12 + 1 := by simpa only [add_comm] using add_le_add_right hh 1
      _ ≤ 5 * (n : ℝ) ^ 12 := by linarith
      _ ≤ 16 * (n : ℝ) ^ 12 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (n : ℝ) ^ 12)
  have hp : 0 < positionBudget n H + 1 := by linarith [positionBudget_nonneg n H]
  have hl := log_le_log hp hb
  simpa only [log_pow, Nat.cast_ofNat] using hl

theorem position_overhead_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, H ≤ n →
      (p.T n : ℝ) * log (positionBudget n H + 1) ≤ (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
  have ha : 0 < p.alpha * (19 / 1000 : ℝ) := mul_pos p.halpha.1 (by norm_num)
  have hsmall := ((isLittleO_log_rpow_atTop ha).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 28)
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℕ),
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 1] with n hs hn hm H hH
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogsmall : log (n : ℝ) ≤ (1 / 28 : ℝ) * (p.m n : ℝ) ^ (19 / 1000 : ℝ) := by
    have hh : log (n : ℝ) ≤ (1 / 28 : ℝ) * (n : ℝ) ^ (p.alpha * (19 / 1000 : ℝ)) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlog,
        abs_of_nonneg (rpow_nonneg hnpos.le _)] using hs
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [rpow_mul hnpos.le]
    exact rpow_le_rpow (rpow_nonneg hnpos.le _) (Nat.le_ceil _) (by norm_num)
  have ht := Lane_sol_s05_h5l.T_upper p n hm
  have hB := (positionBudget_log n H hn hH).trans
    (mul_le_mul_of_nonneg_left hlogsmall (by norm_num : (0 : ℝ) ≤ 14))
  have hmul := mul_le_mul ht hB
    (by linarith [log_nonneg (show 1 ≤ positionBudget n H + 1 by linarith [positionBudget_nonneg n H])])
    (by positivity : 0 ≤ 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ))
  have hmpos : (0 : ℝ) < p.m n := by linarith
  calc
    _ ≤ (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) *
      (14 * ((1 / 28 : ℝ) * (p.m n : ℝ) ^ (19 / 1000 : ℝ))) := hmul
    _ = (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
      rw [show (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) *
          (14 * ((1 / 28 : ℝ) * (p.m n : ℝ) ^ (19 / 1000 : ℝ))) =
          (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (19 / 1000 : ℝ) by ring,
        ← rpow_add hmpos]
      norm_num

def recordRequest (C : ℝ) : ParamReq5 where
  Kcap _ := 0
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 x := (C + 1) / x.1.1.2.2.2.1
  KD _ := 0
  Ks _ := 0
  KB _ := 0
  alpha _ := 1
  alpha_pos _ := by norm_num

theorem recordRequest_coefficient (C : ℝ) (p : Params5 γ K' χ) (hp : (recordRequest C).Holds p) :
    C + 1 ≤ p.delta * p.K2 := by
  have hh : (C + 1) / p.delta ≤ p.K2 := by
    simpa only [recordRequest, Params5.pre2, Params5.pre1, Params5.pre0] using hp.2.2.2.2.1
  simpa only [mul_comm] using (div_le_iff₀ p.hdelta.1).mp hh

theorem record_budget_eventually (C : ℝ) (hC : 0 ≤ C) (p : Params5 γ K' χ)
    (hp : (recordRequest C).Holds p) :
    ∀ᶠ n : ℕ in atTop, ∀ H : ℕ, H ≤ n → ∀ j : ℕ,
      exp (-(p.delta * p.kPrime n j)) *
        (exp (C * ((p.T n : ℝ) * log (p.T n) + ((j : ℝ) + 1) * log (p.m n) +
          (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ))) *
            (positionBudget n H + 1) ^ p.T n) ≤ 1 := by
  filter_upwards [position_overhead_eventually p, Lane_sol_s05_h5l.low_pattern_overhead_eventually p,
    (Lane_sol_s05_h1.tendsto_m p).eventually_gt_atTop 1] with n hpos hpat hm H hH j
  have hmnat : 1 < p.m n := by exact_mod_cast hm
  have hlog : 0 ≤ log (p.m n : ℝ) := (log_pos hm).le
  have hpow : 0 ≤ (p.m n : ℝ) ^ (1 / 50 : ℝ) := rpow_nonneg (Nat.cast_nonneg _) _
  have h0 : 0 ≤ ((j : ℝ) + 3) * log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ) := by positivity
  have hcoeff := mul_le_mul_of_nonneg_right (recordRequest_coefficient C p hp) h0
  have hk := mul_le_mul_of_nonneg_left (Lane_sol_s05_h5l.kPrime_lower p n j hmnat) p.hdelta.1.le
  have hpatt := mul_le_mul_of_nonneg_left hpat hC
  have hposn := hpos H hH
  have hbudget : C * ((p.T n : ℝ) * log (p.T n) + ((j : ℝ) + 1) * log (p.m n) +
      (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ)) +
        (p.T n : ℝ) * log (positionBudget n H + 1) ≤ p.delta * p.kPrime n j := by
    nlinarith [mul_nonneg hC hlog]
  have hb : 0 < positionBudget n H + 1 := by linarith [positionBudget_nonneg n H]
  rw [show (positionBudget n H + 1) ^ p.T n =
      exp ((p.T n : ℝ) * log (positionBudget n H + 1)) by
        rw [exp_nat_mul, exp_log hb], ← exp_add, ← exp_add]
  exact exp_le_one_iff.mpr (by linarith)

theorem uSeg_upper (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 < p.m n) :
    (p.q0 : ℝ) * p.uSeg n j ≤ p.K1 * ((j : ℝ) + 4) * log (p.m n : ℝ) + p.q0 := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hK1 := p.hK1
  have hl : 0 ≤ log (p.m n : ℝ) := (log_pos (by exact_mod_cast hm)).le
  have hceil : (p.uSeg n j : ℝ) ≤ p.K1 * ((j : ℝ) + 4) * log (p.m n : ℝ) / p.q0 + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by positivity) hq.le)).le
  have hh := mul_le_mul_of_nonneg_left hceil hq.le
  rw [mul_add, mul_div_cancel₀ _ hq.ne', mul_one] at hh
  exact hh

theorem lowEntries_upper (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 < p.m n) :
    (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) ≤
      (p.K1 + p.K2) * ((j : ℝ) + 4) * log (p.m n : ℝ) +
        p.K2 * (p.m n : ℝ) ^ (1 / 50 : ℝ) + p.q0 := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hK2 := p.hK2
  have hu : (0 : ℝ) < p.uSeg n j := by exact_mod_cast Lane_sol_s05_h5l.uSeg_positive p n j hm
  have hl : 0 ≤ log (p.m n : ℝ) := (log_pos (by exact_mod_cast hm)).le
  have hd : 0 < (p.q0 : ℝ) * p.uSeg n j := mul_pos hq hu
  have hceil : (p.lowBlocks n j : ℝ) ≤
      p.K2 * (((j : ℝ) + 4) * log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
        ((p.q0 : ℝ) * p.uSeg n j) + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by positivity) hd.le)).le
  have hh := mul_le_mul_of_nonneg_left hceil hd.le
  rw [mul_add, mul_div_cancel₀ _ hd.ne', mul_one] at hh
  have hU := uSeg_upper p n j hm
  push_cast
  nlinarith

theorem low_length_scales_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ p.J n + 2 →
      (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ) ∧
        p.Kcap * ((p.q0 : ℝ) * p.uSeg n j) ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ) := by
  let A : ℝ := 7000 * (p.K1 + p.K2) + p.K2 + p.q0
  let B : ℝ := p.Kcap * (7000 * p.K1 + p.q0)
  filter_upwards [Lane_sol_s05_h5l.fixed_power_margin p A (51 / 1000) (3 / 50) (by norm_num),
    Lane_sol_s05_h5l.fixed_power_margin p B (51 / 1000) (3 / 50) (by norm_num),
    (Lane_sol_s05_h1.tendsto_m p).eventually_gt_atTop 1] with n hA hB hm j hj
  have hmnat : 1 < p.m n := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ p.m n := hm.le
  have hl : 0 ≤ log (p.m n : ℝ) := (log_pos hm).le
  have hlog : log (p.m n : ℝ) ≤ 1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) := by
    have hh := log_le_rpow_div (Nat.cast_nonneg (p.m n)) (by norm_num : (0 : ℝ) < 1 / 1000)
    convert hh using 1 <;> ring
  have hJ : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)
  have hpow1 : 1 ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := one_le_rpow hm1 (by norm_num)
  have hjR : (j : ℝ) ≤ (p.J n : ℝ) + 2 := by exact_mod_cast hj
  have hj4 : (j : ℝ) + 4 ≤ 7 * (p.m n : ℝ) ^ (1 / 20 : ℝ) := by linarith
  have hprod : ((j : ℝ) + 4) * log (p.m n : ℝ) ≤ 7000 * (p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    calc
      _ ≤ (7 * (p.m n : ℝ) ^ (1 / 20 : ℝ)) * (1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) :=
        mul_le_mul hj4 hlog hl (by positivity)
      _ = _ := by
        rw [show (7 * (p.m n : ℝ) ^ (1 / 20 : ℝ)) * (1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) =
          7000 * ((p.m n : ℝ) ^ (1 / 20 : ℝ) * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) by ring,
          ← rpow_add (by linarith : (0 : ℝ) < p.m n)]
        norm_num
  have hp20 : (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (p.m n : ℝ) ^ (51 / 1000 : ℝ) :=
    rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hp1 : 1 ≤ (p.m n : ℝ) ^ (51 / 1000 : ℝ) := one_le_rpow hm1 (by norm_num)
  have hlower := lowEntries_upper p n j hmnat
  have hU := uSeg_upper p n j hmnat
  have hentry : (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) ≤ A * (p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hprod (add_nonneg p.hK1.le p.hK2.le)
    have h20 := mul_le_mul_of_nonneg_left hp20 p.hK2.le
    have hq := mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg p.q0 : (0 : ℝ) ≤ p.q0)
    dsimp [A]
    nlinarith
  have hprefix : p.Kcap * ((p.q0 : ℝ) * p.uSeg n j) ≤ B * (p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hprod p.hK1.le
    have hq := mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg p.q0 : (0 : ℝ) ≤ p.q0)
    have hh' : (p.q0 : ℝ) * p.uSeg n j ≤ (7000 * p.K1 + p.q0) * (p.m n : ℝ) ^ (51 / 1000 : ℝ) := by nlinarith
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left hh' p.hKcap.le
  exact ⟨hentry.trans hA, hprefix.trans hB⟩

theorem cap_scales_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ p.T n ∧ (p.T n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 500 : ℝ) ∧
      (∀ j : ℕ, j ≤ p.J n + 2 →
        (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ) ∧
          p.Kcap * ((p.q0 : ℝ) * p.uSeg n j) ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ)) ∧
        (1 + 2 * p.delta + |p.a 2|) * (p.m n : ℝ) ^ (61 / 500 : ℝ) ≤ p.DL n := by
  have ht : Tendsto (fun n => (p.m n : ℝ) ^ (1 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp (Lane_sol_s05_h1.tendsto_m p)
  filter_upwards [ht.eventually_ge_atTop 2, (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 1,
    Lane_sol_s05_h5l.fixed_power_margin p 2 (1 / 1000) (1 / 500) (by norm_num),
    low_length_scales_eventually p,
    Lane_sol_s05_h5l.fixed_power_margin p (1 + 2 * p.delta + |p.a 2|) (61 / 500) (15 / 100) (by norm_num)]
    with n ht2 hm hTs hlen hbudget
  have hT : 2 ≤ p.T n := by
    have hraw : (2 : ℝ) ≤ p.T n := ht2.trans (Nat.le_ceil _)
    exact_mod_cast hraw
  exact ⟨hT, (Lane_sol_s05_h5l.T_upper p n hm).trans hTs, hlen, hbudget⟩

theorem cap_budget_of_scales (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 ≤ (p.m n : ℝ))
    (hk : (p.kPrime n j : ℝ) ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ))
    (B O : ℝ) (hB : B ≤ (p.m n : ℝ) ^ (3 / 50 : ℝ)) (hO : 0 ≤ O)
    (hOb : O ≤ (p.m n : ℝ) ^ (61 / 500 : ℝ))
    (hbudget : (1 + 2 * p.delta + |p.a 2|) * (p.m n : ℝ) ^ (61 / 500 : ℝ) ≤ p.DL n) :
    B + 2 * p.delta * p.kPrime n j + p.a 2 * O ≤ p.DL n := by
  have hcoeff : 0 ≤ 2 * p.delta := by have := p.hdelta.1; positivity
  have hh := mul_le_mul_of_nonneg_left hk hcoeff
  have hp := rpow_le_rpow_of_exponent_le hm (by norm_num : (3 / 50 : ℝ) ≤ 61 / 500)
  have hmain := mul_le_mul_of_nonneg_left hp (by have := p.hdelta.1; positivity : 0 ≤ 1 + 2 * p.delta)
  have ho := (mul_le_mul_of_nonneg_right (le_abs_self (p.a 2)) hO).trans
    (mul_le_mul_of_nonneg_left hOb (abs_nonneg (p.a 2)))
  nlinarith

end
end HypercubeRamsey.Lane_sol_s05_k1
