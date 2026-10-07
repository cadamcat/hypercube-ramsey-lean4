import HypercubeRamsey.S05.Shapes_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h1

open Classical Filter Real
open scoped Topology BigOperators

set_option maxHeartbeats 400000

noncomputable section

variable {γ K' χ : ℝ}

theorem tendsto_m (p : Params5 γ K' χ) : Tendsto (fun n => (p.m n : ℝ)) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono _ hp
  intro n
  dsimp only [Params5.m]
  exact Nat.le_ceil _

theorem J_le_m (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n) : p.J n ≤ p.m n := by
  have hm' : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hr : (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ p.m n := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hm' (by norm_num : (1 / 20 : ℝ) ≤ 1)
  have hf : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := by
    dsimp only [Params5.J]
    exact Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast hf.trans hr

def regularEps (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  exp (-(p.delta * (p.q0 * p.uSeg n 0)) / 2)

def highEps (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2)

theorem uSeg0_lower (p : Params5 γ K' χ) (n : ℕ) :
    4 * p.K1 * log (p.m n : ℝ) ≤ (p.q0 : ℝ) * p.uSeg n 0 := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have h : p.K1 * (0 + 4 : ℝ) * log (p.m n : ℝ) / p.q0 ≤ (p.uSeg n 0 : ℝ) := by
    dsimp only [Params5.uSeg]
    simpa only [Nat.cast_zero] using Nat.le_ceil
      (p.K1 * ((0 : ℝ) + 4) * log (p.m n : ℝ) / (p.q0 : ℝ))
  have h' := (div_le_iff₀ hq).1 h
  nlinarith

theorem regularEps_le (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n)
    (hk : (Fintype.card KeyCode : ℝ) + 3 ≤ p.delta * p.K1) :
    regularEps p n ≤ (p.m n : ℝ) ^ (-((Fintype.card KeyCode : ℝ) + 3)) := by
  let M := (p.m n : ℝ)
  have hM : 1 ≤ M := by dsimp only [M]; exact_mod_cast hm
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hl : 0 ≤ log M := log_nonneg hM
  have hδ : 0 ≤ p.delta := p.hdelta.1.le
  have hu := mul_le_mul_of_nonneg_left (uSeg0_lower p n) hδ
  have hb : ((Fintype.card KeyCode : ℝ) + 3) * log M ≤ p.delta * (p.q0 * p.uSeg n 0) / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hk hl
    have h2 : 0 ≤ p.delta * p.K1 * log M := mul_nonneg (mul_nonneg p.hdelta.1.le p.hK1.le) hl
    nlinarith
  unfold regularEps
  rw [rpow_def_of_pos hMpos]
  apply exp_le_exp.mpr
  nlinarith

def lowAlarmConstant : ℝ :=
  2 * (fixedShapeCount : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) * (2 : ℝ) ^ Fintype.card KeyCode

theorem lowAlarm_le (p : Params5 γ K' χ) (n : ℕ)
    (hm : coarseKeyBound + 3 ≤ p.m n)
    (hk : (Fintype.card KeyCode : ℝ) + 3 ≤ p.delta * p.K1) :
    (Fintype.card (LowShape (p.m n) (p.J n)) : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) *
        regularEps p n ≤ lowAlarmConstant * (p.m n : ℝ) ^ (-2 : ℝ) := by
  let D := Fintype.card KeyCode
  let M := (p.m n : ℝ)
  have hm1 : 1 ≤ p.m n := by omega
  have hM : 1 ≤ M := by dsimp only [M]; exact_mod_cast hm1
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hlarge : (coarseKeyBound : ℝ) + 3 ≤ M := by dsimp only [M]; exact_mod_cast hm
  have hJ : (p.J n : ℝ) ≤ M := by dsimp only [M]; exact_mod_cast J_le_m p n hm1
  have hcard : (Fintype.card (LowShape (p.m n) (p.J n)) : ℝ) ≤
      2 * M * (fixedShapeCount : ℝ) * (2 * M) ^ D := by
    rw [lowShape_card]
    push_cast
    gcongr
    · linarith
    · linarith
  have hp : M ^ D * M ^ (-((D : ℝ) + 3)) * M = M ^ (-2 : ℝ) := by
    calc
      _ = M ^ ((D : ℝ) + (-((D : ℝ) + 3)) + 1) := by
        rw [rpow_add hMpos, rpow_add hMpos, rpow_natCast, rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (2 * M * (fixedShapeCount : ℝ) * (2 * M) ^ D) * ((D : ℝ) + 2) *
        M ^ (-((D : ℝ) + 3)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ (D : ℝ) + 2))
        (regularEps_le p n hm1 hk) (exp_pos _).le (by positivity)
    _ = lowAlarmConstant * (M ^ D * M ^ (-((D : ℝ) + 3)) * M) := by
      rw [mul_pow]
      unfold lowAlarmConstant
      ring
    _ = _ := by rw [hp]

theorem highEps_tendsto (p : Params5 γ K' χ) : Tendsto (highEps p) atTop (𝓝 0) := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hc : 0 < p.delta * (p.q0 : ℝ) / 2 := div_pos (mul_pos p.hdelta.1 hq) (by norm_num)
  have h := tendsto_exp_neg_atTop_nhds_zero.comp
    ((p.tendsto_uStarSeg_atTop5).const_mul_atTop hc)
  refine h.congr' ?_
  filter_upwards with n
  unfold highEps
  apply congrArg exp
  push_cast
  ring

def stage1Request : ParamReq5 where
  Kcap := fun _ => 0
  Kpp := fun _ => 0
  Kh := fun _ => 0
  K1 := fun x => ((Fintype.card KeyCode : ℝ) + 3) / x.1.2.2.2.1
  K2 := fun _ => 0
  KD := fun _ => 0
  Ks := fun _ => 0
  KB := fun _ => 0
  alpha := fun _ => 1
  alpha_pos := by intro x; norm_num

theorem request_budget (p : Params5 γ K' χ) (hp : stage1Request.Holds p) :
    (Fintype.card KeyCode : ℝ) + 3 ≤ p.delta * p.K1 := by
  have hk := hp.2.2.2.1
  change ((Fintype.card KeyCode : ℝ) + 3) / p.delta ≤ p.K1 at hk
  simpa only [mul_comm] using (div_le_iff₀ p.hdelta.1).1 hk

theorem eventually_alarm_small (p : Params5 γ K' χ)
    (hk : (Fintype.card KeyCode : ℝ) + 3 ≤ p.delta * p.K1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, coarseKeyBound + 3 ≤ p.m n ∧
      (Fintype.card (LowShape (p.m n) (p.J n)) : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) *
          regularEps p n ≤ 1 / 200 ∧
      (Fintype.card HighShape : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) * highEps p n ≤ 1 / 200 := by
  have hm := tendsto_m p
  have hl : Tendsto (fun n => lowAlarmConstant * (p.m n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hm).const_mul lowAlarmConstant
  have hh : Tendsto (fun n => (Fintype.card HighShape : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) *
      highEps p n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (highEps_tendsto p).const_mul
      ((Fintype.card HighShape : ℝ) * ((Fintype.card KeyCode : ℝ) + 2))
  have hsmall : Set.Iio (1 / 200 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
  have hlarge : ∀ᶠ n in atTop, coarseKeyBound + 3 ≤ p.m n := by
    have h := hm.eventually (eventually_ge_atTop ((coarseKeyBound + 3 : ℕ) : ℝ))
    filter_upwards [h] with n hn
    exact_mod_cast hn
  apply eventually_atTop.1
  filter_upwards [hlarge, hl.eventually hsmall, hh.eventually hsmall] with n hn hln hhn
  exact ⟨hn, (lowAlarm_le p n hn hk).trans hln.le, hhn.le⟩

theorem uSeg_mono (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n) {j j' : ℕ} (hj : j ≤ j') :
    p.uSeg n j ≤ p.uSeg n j' := by
  have hl : 0 ≤ log (p.m n : ℝ) := log_nonneg (by exact_mod_cast hm)
  have hk : 0 ≤ p.K1 := p.hK1.le
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  unfold Params5.uSeg
  apply Nat.ceil_mono
  gcongr

theorem regular_threshold_le (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n) (j : ℕ) :
    exp (-(p.delta * (p.q0 * p.uSeg n j)) / 2) ≤ regularEps p n := by
  have hu : (p.uSeg n 0 : ℝ) ≤ p.uSeg n j := by exact_mod_cast uSeg_mono p n hm (Nat.zero_le j)
  have hq : 0 ≤ (p.q0 : ℝ) := Nat.cast_nonneg _
  have hδ : 0 ≤ p.delta := p.hdelta.1.le
  have h := mul_le_mul_of_nonneg_left hu (mul_nonneg hδ hq)
  unfold regularEps
  apply exp_le_exp.mpr
  push_cast
  nlinarith

end
end HypercubeRamsey.Lane_sol_s05_h1
