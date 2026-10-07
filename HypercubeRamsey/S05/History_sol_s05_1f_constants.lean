import HypercubeRamsey.S05.History_sol_s05_1f_budgets
import HypercubeRamsey.S05.History_sol_s05_1f_scales

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
variable {γ K' χ : ℝ}

/-- Prefix segment rounding has only one extra segment. -/
theorem uSeg_length_upper (p : Params5 γ K' χ) (n j : ℕ) (hm : 1 ≤ p.m n) :
    (p.q0 : ℝ) * p.uSeg n j ≤ p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) + p.q0 := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hM : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hnum : 0 ≤ p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) :=
    mul_nonneg (mul_nonneg p.hK1.le (by positivity)) (Real.log_nonneg hM)
  have hh := Nat.ceil_lt_add_one (div_nonneg hnum hq.le)
  change (p.uSeg n j : ℝ) < p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / p.q0 + 1 at hh
  have hmul := mul_le_mul_of_nonneg_left hh.le hq.le
  rw [mul_add, mul_div_cancel₀ _ hq.ne', mul_one] at hmul
  exact hmul

/-- The interface low tuple length has a constant multiple of J log m. -/
theorem interface_low_length_upper (p : Params5 γ K' χ) (n : ℕ)
    (hm : 1 < p.m n) (hJ : 1 ≤ p.J n) (hlog : 1 ≤ Real.log (p.m n : ℝ))
    (hpow : (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ p.J n) :
    (p.lowBlocks n (p.J n) : ℝ) * ((p.q0 : ℝ) * p.uSeg n (p.J n)) ≤
      (6 * p.K2 + 5 * p.K1 + p.q0) * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
  have hu : 0 < p.uSeg n (p.J n) := Lane_sol_s05_h5l.uSeg_positive p n (p.J n) hm
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hden : 0 < (p.q0 : ℝ) * p.uSeg n (p.J n) :=
    mul_pos hq (by exact_mod_cast hu)
  have htarget : 0 ≤ p.K2 * (((p.J n : ℝ) + 4) * Real.log (p.m n : ℝ) +
      (p.m n : ℝ) ^ (1 / 50 : ℝ)) := mul_nonneg p.hK2.le
    (add_nonneg (mul_nonneg (by positivity) (by linarith)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hh := Nat.ceil_lt_add_one (div_nonneg htarget hden.le)
  change (p.lowBlocks n (p.J n) : ℝ) < p.K2 *
    (((p.J n : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
      ((p.q0 : ℝ) * p.uSeg n (p.J n)) + 1 at hh
  have hmul := mul_le_mul_of_nonneg_right hh.le hden.le
  rw [add_mul, div_mul_cancel₀ _ hden.ne', one_mul] at hmul
  have huBound := uSeg_length_upper p n (p.J n) (Nat.le_of_lt hm)
  have hJr : (1 : ℝ) ≤ p.J n := by exact_mod_cast hJ
  have hJL : (p.J n : ℝ) ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hlog
  have h1JL : 1 ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) := by nlinarith
  have hK1 := mul_le_mul_of_nonneg_left (show ((p.J n : ℝ) + 4) * Real.log (p.m n : ℝ) ≤
      5 * (p.J n : ℝ) * Real.log (p.m n : ℝ) by
        have hh := mul_le_mul_of_nonneg_right (show (p.J n : ℝ) + 4 ≤ 5 * p.J n by linarith)
          (by linarith : 0 ≤ Real.log (p.m n : ℝ)); nlinarith) p.hK1.le
  have hK2 := mul_le_mul_of_nonneg_left (show ((p.J n : ℝ) + 4) * Real.log (p.m n : ℝ) +
      (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ 6 * (p.J n : ℝ) * Real.log (p.m n : ℝ) by
        have hh := mul_le_mul_of_nonneg_right (show (p.J n : ℝ) + 4 ≤ 5 * p.J n by linarith)
          (by linarith : 0 ≤ Real.log (p.m n : ℝ)); nlinarith) p.hK2.le
  have hqBound := mul_le_mul_of_nonneg_left h1JL hq.le
  nlinarith

/-- The prior-cap prefix at a high key has the same J log m budget. -/
theorem high_prefix_length_upper (p : Params5 γ K' χ) (n : ℕ)
    (hm : 1 ≤ p.m n) (hJ : 1 ≤ p.J n) (hlog : 1 ≤ Real.log (p.m n : ℝ)) :
    (p.q0 : ℝ) * p.uSeg n (p.J n + 1) ≤
      (6 * p.K1 + p.q0) * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
  have hh := uSeg_length_upper p n (p.J n + 1) hm
  have hJr : (1 : ℝ) ≤ p.J n := by exact_mod_cast hJ
  have hJL : 1 ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
    have hmul := mul_le_mul hJr hlog (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (p.J n : ℝ))
    simpa using hmul
  have hlevel : ((p.J n : ℝ) + 5) * Real.log (p.m n : ℝ) ≤
      6 * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show (p.J n : ℝ) + 5 ≤ 6 * p.J n by linarith)
      (by linarith : 0 ≤ Real.log (p.m n : ℝ))
    nlinarith
  have hK := mul_le_mul_of_nonneg_left hlevel p.hK1.le
  have hq := mul_le_mul_of_nonneg_left hJL (Nat.cast_nonneg p.q0)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  nlinarith


/-- All observed full pools together cost at most J log m eventually. -/
theorem high_pools_length_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      ((p.T n * highTypeBudget : ℕ) : ℝ) *
        ((p.poolBlocks n * (p.q0 * p.uStarSeg n) : ℕ) : ℝ) ≤
          (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
  let C := 2 * Real.exp (p.Kh * p.q0) + 1
  let A := 4 * (highTypeBudget : ℝ) * C * (p.eta + p.q0)
  have hmargin := Lane_sol_s05_h5l.fixed_power_margin p A (31 / 1000) (1 / 20) (by norm_num)
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [hm.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hm).eventually_ge_atTop 1,
    hp.eventually_ge_atTop 2, hmargin] with n hm2 hlog hpow hmargin
  dsimp only [Function.comp_apply] at hlog hpow
  have hM : (1 : ℝ) ≤ p.m n := by linarith
  have hMpos : (0 : ℝ) < p.m n := by linarith
  have hmNat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hT := Lane_sol_s05_h5l.T_upper p n hM
  have hPool := poolBlocks_power_upper p n hmNat
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hU : (p.q0 : ℝ) * p.uStarSeg n ≤ (p.eta + p.q0) * Real.log (p.m n : ℝ) := by
    have hh := Nat.ceil_lt_add_one (div_nonneg
      (mul_nonneg p.heta.1.le (by linarith : 0 ≤ Real.log (p.m n : ℝ))) hq.le)
    change (p.uStarSeg n : ℝ) < p.eta * Real.log (p.m n : ℝ) / p.q0 + 1 at hh
    have hh' := mul_le_mul_of_nonneg_left hh.le hq.le
    rw [mul_add, mul_div_cancel₀ _ hq.ne', mul_one] at hh'
    have hq' := mul_le_mul_of_nonneg_left hlog hq.le
    nlinarith
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJ : (p.m n : ℝ) ^ (1 / 20 : ℝ) / 2 ≤ p.J n := by linarith
  have hlen := mul_le_mul (mul_le_mul hT hPool (Nat.cast_nonneg _)
      (by positivity : 0 ≤ 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ))) hU
      (mul_nonneg (Nat.cast_nonneg p.q0) (Nat.cast_nonneg _))
      (by positivity : 0 ≤ 2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) *
        (C * (p.m n : ℝ) ^ (3 / 100 : ℝ)))
  have hpowers : (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (3 / 100 : ℝ) =
      (p.m n : ℝ) ^ (31 / 1000 : ℝ) := by
    rw [← Real.rpow_add hMpos]; norm_num
  have hlen' := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg highTypeBudget)
  have hsmall := mul_le_mul_of_nonneg_right hmargin (by linarith : 0 ≤ Real.log (p.m n : ℝ))
  have hJlog := mul_le_mul_of_nonneg_right hJ (by linarith : 0 ≤ Real.log (p.m n : ℝ))
  have hlenEq : (highTypeBudget : ℝ) *
      (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (C * (p.m n : ℝ) ^ (3 / 100 : ℝ)) *
        ((p.eta + p.q0) * Real.log (p.m n : ℝ))) =
      (A / 2) * (p.m n : ℝ) ^ (31 / 1000 : ℝ) * Real.log (p.m n : ℝ) := by
    calc
      _ = (A / 2) * ((p.m n : ℝ) ^ (1 / 1000 : ℝ) *
          (p.m n : ℝ) ^ (3 / 100 : ℝ)) * Real.log (p.m n : ℝ) := by dsimp [A]; ring
      _ = _ := by rw [hpowers]
  have hbound := hlen'.trans_eq hlenEq
  simp only [Nat.cast_mul]
  nlinarith only [hbound, hsmall, hJlog]

/-- A joint posterior atom cap with a coefficient fixed before K_D and K_s. -/
def highAtomCoefficient (p : Params5 γ K' χ) : ℝ :=
  p.Kcap * (6 * p.K1 + p.q0) + p.a 2 * (1 + 6 * p.K2 + 5 * p.K1 + p.q0) + p.delta

/-- The finite observation and prior budgets imply the paper's atom exponent. -/
theorem high_atom_exponent_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ r : X.AbsRecord,
      X.RecOccurs r → r.1.isRight →
      p.Kcap * ((p.q0 : ℝ) * p.uSeg n (p.J n + 1)) +
        p.a 2 * observedLength X r + p.delta ≤
          highAtomCoefficient p * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  have hmargin := Lane_sol_s05_h5l.fixed_power_margin p 2 (1 / 50) (1 / 20) (by norm_num)
  filter_upwards [hm.eventually_ge_atTop 2, hp.eventually_ge_atTop 2, hmargin,
    (Real.tendsto_log_atTop.comp hm).eventually_ge_atTop 1,
    high_pools_length_eventually p] with n hm2 hp2 hmargin hlog hpools
  dsimp only [Function.comp_apply] at hp2 hlog
  have hmNat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJr : (1 : ℝ) ≤ p.J n := by linarith
  have hJ : 1 ≤ p.J n := by exact_mod_cast hJr
  have hpow : (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ p.J n := by linarith
  have hJL : 1 ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) := by nlinarith
  have hpre := high_prefix_length_upper p n (Nat.le_of_lt hmNat) hJ hlog
  have hlow := interface_low_length_upper p n hmNat hJ hlog hpow
  intro N E G X hXp r hr hh
  have hobs := high_observed_length X r hr hh
  rw [hXp] at hobs
  have hobsR : (observedLength X r : ℝ) ≤
      (1 + 6 * p.K2 + 5 * p.K1 + p.q0) * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
    have hobsCast : (observedLength X r : ℝ) ≤
        ((p.T n * highTypeBudget : ℕ) : ℝ) * ((p.poolBlocks n * (p.q0 * p.uStarSeg n) : ℕ) : ℝ) +
        (p.lowBlocks n (p.J n) : ℝ) * ((p.q0 : ℝ) * p.uSeg n (p.J n)) := by
      exact_mod_cast hobs
    nlinarith
  have ha : 0 ≤ p.a 2 := by
    have hh := p.ha_order (0 : Fin 9) (2 : Fin 9) (by decide)
    rw [p.ha0] at hh; linarith
  have h1 := mul_le_mul_of_nonneg_left hpre p.hKcap.le
  have h2 := mul_le_mul_of_nonneg_left hobsR ha
  have hδ := mul_le_mul_of_nonneg_left hJL p.hdelta.1.le
  dsimp [highAtomCoefficient]
  nlinarith


/-- A positive logarithmic scale tends to infinity uniformly above a fixed bound. -/
theorem high_scales_eventually (p : Params5 γ K' χ) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 < p.m n ∧ 1 ≤ p.J n ∧ 1 ≤ Real.log (p.m n : ℝ) ∧
      A ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) ∧
      A ≤ (p.usedBlocks n * (p.q0 * p.uStarSeg n) : ℕ) ∧ A ≤ p.s n := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  have hk := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp hm
  have hl := Real.tendsto_log_atTop.comp hm
  filter_upwards [hm.eventually_ge_atTop 2, hp.eventually_ge_atTop 2,
    hl.eventually_ge_atTop 1, hl.eventually_ge_atTop A,
    hl.eventually_ge_atTop (A / p.Ks), hk.eventually_ge_atTop A] with n hm2 hp2 hl1 hlA hlS hkA
  dsimp only [Function.comp_apply] at hp2 hl1 hlA hlS hkA
  have hmNat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJr : (1 : ℝ) ≤ p.J n := by linarith
  have hJ : 1 ≤ p.J n := by exact_mod_cast hJr
  have hu : (0 : ℝ) < p.uStarSeg n := by exact_mod_cast Lane_sol_s05_h5l.uStarSeg_positive p n hmNat
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hd : 0 < (p.q0 : ℝ) * p.uStarSeg n := mul_pos hq hu
  have hused : (p.m n : ℝ) ^ (1 / 200 : ℝ) / ((p.q0 : ℝ) * p.uStarSeg n) ≤ p.usedBlocks n := Nat.le_ceil _
  have hused' := (div_le_iff₀ hd).mp hused
  have hJL : A ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    hlA.trans (le_mul_of_one_le_left (by linarith : 0 ≤ Real.log (p.m n : ℝ)) hJr)
  have hS : A ≤ p.s n := by
    have ha := (div_le_iff₀ p.hKs).mp hlS
    have hprod := mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (by linarith : 0 ≤ Real.log (p.m n : ℝ)) hJr) p.hKs.le
    have hceil : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ p.s n := Nat.le_ceil _
    nlinarith
  refine ⟨hmNat, hJ, hl1, hJL, ?_, hS⟩
  simp only [Nat.cast_mul]
  nlinarith


/-- A box grid is sufficient once K_s pays its O(J log m) logarithm. -/
theorem finite_box_grid_budget (r J m : ℕ) (A ε : ℝ)
    (hA : 1 ≤ A) (hε : 0 < ε) (hJ : 1 ≤ J) (hm : 1 ≤ Real.log (m : ℝ))
    (hJm : J ≤ m) (hr : (r : ℝ) ≤ A * J) :
    (((⌈(1 + ε⁻¹) * r⌉₊ + 1) ^ r * (r + 1) : ℕ) : ℝ) ≤
      Real.exp (A * (Real.log ((3 + ε⁻¹) * A) + 2) * (J : ℝ) * Real.log (m : ℝ)) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hmr : (0 : ℝ) < m := by
    by_contra h
    have hmz : (m : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hmz, Real.log_zero] at hm
    linarith
  have hlog : 0 ≤ Real.log (m : ℝ) := by linarith
  have hcoef : 1 ≤ (3 + ε⁻¹) * A := by
    have hi := (inv_pos.mpr hε).le
    nlinarith
  have hcoefLog : 0 ≤ Real.log ((3 + ε⁻¹) * A) := Real.log_nonneg hcoef
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.cast_zero, mul_zero, Nat.ceil_zero, zero_add, pow_zero, zero_add, mul_one, Nat.cast_one]
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg _)) hlog
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
    have hceil := Nat.ceil_lt_add_one (mul_nonneg (by positivity : 0 ≤ 1 + ε⁻¹) (Nat.cast_nonneg r))
    have hbox : (⌈(1 + ε⁻¹) * r⌉₊ + 1 : ℕ) ≤ ((3 + ε⁻¹) * A) * (m : ℝ) := by
      have hJmr : (J : ℝ) ≤ m := by exact_mod_cast hJm
      have hRm := hr.trans (mul_le_mul_of_nonneg_left hJmr (by linarith : 0 ≤ A))
      have hb : (⌈(1 + ε⁻¹) * r⌉₊ + 1 : ℕ) ≤ (3 + ε⁻¹) * (r : ℝ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith
      exact hb.trans (by have hh := mul_le_mul_of_nonneg_left hRm (by positivity : 0 ≤ 3 + ε⁻¹); nlinarith)
    have hbp : (0 : ℝ) < (⌈(1 + ε⁻¹) * r⌉₊ + 1 : ℕ) := by positivity
    have hbl : Real.log (⌈(1 + ε⁻¹) * r⌉₊ + 1 : ℕ) ≤
        Real.log ((3 + ε⁻¹) * A) + Real.log (m : ℝ) := by
      have hh := Real.log_le_log hbp hbox
      rwa [Real.log_mul (by linarith : (3 + ε⁻¹) * A ≠ 0) hmr.ne'] at hh
    have hrl : Real.log (r + 1 : ℕ) ≤ (r : ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (r + 1 : ℕ) by positivity)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hh
    have hG : (0 : ℝ) < (((⌈(1 + ε⁻¹) * r⌉₊ + 1) ^ r * (r + 1) : ℕ) : ℝ) := by positivity
    rw [← Real.exp_log hG]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (pow_pos hbp _).ne' (by positivity), Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left hbl (Nat.cast_nonneg r)
    have h1 := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ Real.log ((3 + ε⁻¹) * A) + Real.log (m : ℝ) + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hm (mul_nonneg (by linarith : 0 ≤ A) (Nat.cast_nonneg J))
    have h3 := mul_le_mul_of_nonneg_left hm hcoefLog
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith : 0 ≤ A) (Nat.cast_nonneg J))
    nlinarith

/-- The computed reference count has a fixed multiple of J once T ≤ J. -/
theorem high_reference_count_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ r : X.AbsRecord,
      X.RecOccurs r → r.1.isRight →
      ((r.2.2.1.card : ℕ) : ℝ) ≤ ((2 * highTypeBudget : ℕ) + 6) * (p.J n : ℝ) := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  have hmargin := Lane_sol_s05_h5l.fixed_power_margin p 4 (1 / 1000) (1 / 20) (by norm_num)
  filter_upwards [hm.eventually_ge_atTop 1, hp.eventually_ge_atTop 2, hmargin]
    with n hm1 hp2 hmargin
  dsimp only [Function.comp_apply] at hp2
  have hT := Lane_sol_s05_h5l.T_upper p n hm1
  have hfloor : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJ : (1 : ℝ) ≤ p.J n := by linarith
  have hTJ : (p.T n : ℝ) ≤ p.J n := by linarith
  intro N E G X hXp r hr hh
  have hc := high_designations_card X r hr hh
  simp only [hXp] at hc
  have hcR : (r.2.2.1.card : ℝ) ≤ (p.T n : ℝ) * (2 * highTypeBudget : ℕ) + 2 * ((p.J n : ℝ) + 2) := by
    exact_mod_cast hc
  have hprod := mul_le_mul_of_nonneg_right hTJ (Nat.cast_nonneg (2 * highTypeBudget))
  nlinarith

end
end HypercubeRamsey.Lane_sol_s05_1f
