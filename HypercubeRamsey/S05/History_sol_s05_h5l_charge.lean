import HypercubeRamsey.S05.History_sol_s05_h5l_bounds

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical Filter
open scoped Topology

noncomputable section
set_option maxHeartbeats 800000

variable {γ K' χ : ℝ}

def groupEps (p : Params5 γ K' χ) (n : ℕ) : ℝ := Real.exp (-12 * Real.log (p.m n))

theorem uSeg_lower (p : Params5 γ K' χ) (n j : ℕ) :
    p.K1 * ((j : ℝ) + 4) * Real.log (p.m n) ≤ (p.q0 : ℝ) * p.uSeg n j := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hh : p.K1 * ((j : ℝ) + 4) * Real.log (p.m n) / p.q0 ≤ (p.uSeg n j : ℝ) := Nat.le_ceil _
  simpa only [mul_comm] using (div_le_iff₀ hq).1 hh

theorem nat_power_exp (M : ℝ) (hM : 0 < M) (k : ℕ) : M ^ k = Real.exp ((k : ℝ) * Real.log M) := by
  calc
    _ = (Real.exp (Real.log M)) ^ k := by rw [Real.exp_log hM]
    _ = _ := by rw [← Real.exp_nat_mul]

theorem regular_group_budget_eventually (p : Params5 γ K' χ) (D d : ℕ)
    (hK : 160 ≤ p.delta * p.K1) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ p.J n →
      (2 : ℝ) ^ D * ((j : ℝ) + 1) * ((p.m n : ℝ) + 1) ^ j *
        (2 : ℝ) ^ (d + j) * ((d + j : ℕ) + 1) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 8) ≤ groupEps p n / 3 := by
  let A : ℝ := (2 : ℝ) ^ D * (2 : ℝ) ^ d * ((d : ℝ) + 1)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hm := Lane_sol_s05_h1.tendsto_m p
  filter_upwards [hm.eventually_ge_atTop 2, hm.eventually_ge_atTop (3 * A)] with n hM hA j hj
  let M : ℝ := p.m n
  have hM0 : 0 < M := by dsimp [M]; linarith
  have hjM : (j : ℝ) ≤ M := by
    have hmnat : 1 ≤ p.m n := by exact_mod_cast (show (1 : ℝ) ≤ p.m n by linarith)
    dsimp only [M]
    exact_mod_cast hj.trans (Lane_sol_s05_h1.J_le_m p n hmnat)
  have hMplus : M + 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  have h1 : (j : ℝ) + 1 ≤ M ^ 2 := by nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h2 : (d : ℝ) + j + 1 ≤ ((d : ℝ) + 1) * M ^ 2 := by nlinarith
  have hp1 : (M + 1) ^ j ≤ (M ^ 2) ^ j := pow_le_pow_left₀ (by linarith) hMplus j
  have hp2 : (2 : ℝ) ^ j ≤ M ^ j := pow_le_pow_left₀ (by norm_num) hM j
  have hprod : (2 : ℝ) ^ D * ((j : ℝ) + 1) * (M + 1) ^ j *
      (2 : ℝ) ^ (d + j) * ((d : ℝ) + j + 1) ≤ A * M ^ (3 * j + 4) := by
    rw [pow_add]
    calc
      _ ≤ (2 : ℝ) ^ D * (M ^ 2) * (M ^ 2) ^ j * ((2 : ℝ) ^ d * M ^ j) *
          (((d : ℝ) + 1) * M ^ 2) := by gcongr
      _ = _ := by
        have he : (M ^ 2) ^ j = (M ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
        rw [he, pow_add, show 3 * j = j * 3 by omega, pow_mul]
        dsimp only [A]
        ring
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by dsimp [M]; linarith)
  have hu := mul_le_mul_of_nonneg_left (uSeg_lower p n j) p.hdelta.1.le
  have hcoef := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ ((j : ℝ) + 4) * Real.log M by positivity)
  have hraw : Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 8) ≤
      Real.exp (-20 * ((j : ℝ) + 4) * Real.log M) := by
    apply Real.exp_le_exp.mpr
    change p.delta * (p.K1 * ((j : ℝ) + 4) * Real.log M) ≤ _ at hu
    push_cast
    nlinarith
  let z : ℝ := ((3 * j + 4 : ℕ) : ℝ) * Real.log M - 20 * ((j : ℝ) + 4) * Real.log M
  have hz : z ≤ -13 * Real.log M := by
    dsimp [z]
    push_cast
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have hweight := mul_le_mul hprod hraw (Real.exp_pos _).le (by positivity : 0 ≤ A * M ^ (3 * j + 4))
  have he : A * M ^ (3 * j + 4) * Real.exp (-20 * ((j : ℝ) + 4) * Real.log M) = A * Real.exp z := by
    rw [nat_power_exp M hM0]
    dsimp [z]
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [he] at hweight
  have hlast : 3 * (A * Real.exp z) ≤ groupEps p n := by
    calc
      _ = (3 * A) * Real.exp z := by ring
      _ ≤ M * Real.exp (-13 * Real.log M) :=
        mul_le_mul hA (Real.exp_le_exp.mpr hz) (Real.exp_pos _).le hM0.le
      _ = groupEps p n := by
        calc
          _ = Real.exp (Real.log M) * Real.exp (-13 * Real.log M) := by rw [Real.exp_log hM0]
          _ = Real.exp (Real.log M + -13 * Real.log M) := (Real.exp_add _ _).symm
          _ = groupEps p n := by
            change Real.exp (Real.log M + -13 * Real.log M) = Real.exp (-12 * Real.log M)
            congr 1
            ring
  change (2 : ℝ) ^ D * ((j : ℝ) + 1) * (M + 1) ^ j * (2 : ℝ) ^ (d + j) *
    ((d + j : ℕ) + 1) * Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 8) ≤ _
  push_cast
  linarith

theorem low_group_budget_eventually (p : Params5 γ K' χ) (C c : ℝ) (hc : 0 < c)
    (hK : max C 0 + 20 ≤ 3 * c * p.K2 / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      Real.exp (C * ((p.T n : ℝ) * Real.log (p.T n) + ((j : ℝ) + 1) * Real.log (p.m n) +
        (if j = p.J n then (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) else 0))) *
      (2 * Real.exp (-(3 * c / 4 * p.kPrime n j))) ≤ groupEps p n / 3 := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  filter_upwards [hm.eventually_ge_atTop 6, low_pattern_overhead_eventually p] with n hM ho j
  have hmnat : 1 < p.m n := by exact_mod_cast (show (1 : ℝ) < p.m n by linarith)
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by linarith)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hpow : 0 ≤ (p.m n : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT0 : 0 ≤ (p.T n : ℝ) * Real.log (p.T n) := by
    have hp : (0 : ℝ) < p.T n := by
      have hh : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.T n : ℝ) := Nat.le_ceil _
      exact (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < p.m n) _).trans_le hh
    have hone : (1 : ℝ) ≤ p.T n := by exact_mod_cast (show 1 ≤ p.T n by exact_mod_cast hp)
    exact mul_nonneg hp.le (Real.log_nonneg hone)
  have hmask0 : 0 ≤ (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) := by positivity
  let A : ℝ := (p.T n : ℝ) * Real.log (p.T n) + ((j : ℝ) + 1) * Real.log (p.m n) +
    (if j = p.J n then (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) else 0)
  have hA0 : 0 ≤ A := by dsimp [A]; split_ifs <;> positivity
  have hA : A ≤ ((j : ℝ) + 1) * Real.log (p.m n) + (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
    dsimp [A]
    split_ifs <;> linarith
  have hcount := (mul_le_mul_of_nonneg_right (le_max_left C 0) hA0).trans
    (mul_le_mul_of_nonneg_left hA hC0)
  have hk := kPrime_lower p n j hmnat
  have hraw := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 3 * c / 4)
  have hcoef := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ ((j : ℝ) + 3) * Real.log (p.m n) + (p.m n : ℝ) ^ (1 / 50 : ℝ) by positivity)
  have hcost : (max C 0 + 20) * (((j : ℝ) + 3) * Real.log (p.m n) +
      (p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤ 3 * c / 4 * (p.kPrime n j : ℝ) := by
    nlinarith
  have hlog6 : Real.log 6 ≤ Real.log (p.m n : ℝ) := Real.log_le_log (by norm_num) hM
  have hexp : C * A - 3 * c / 4 * (p.kPrime n j : ℝ) + Real.log 6 ≤
      -12 * Real.log (p.m n) := by
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    nlinarith
  have hh := Real.exp_le_exp.mpr hexp
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 6)] at hh
  have he : Real.exp (C * A) * (2 * Real.exp (-(3 * c / 4 * p.kPrime n j))) =
      2 * Real.exp (C * A - 3 * c / 4 * (p.kPrime n j : ℝ)) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  change Real.exp (C * A) * (2 * Real.exp (-(3 * c / 4 * p.kPrime n j))) ≤ _
  rw [he]
  dsimp [groupEps]
  linarith

theorem high_group_budget_eventually (p : Params5 γ K' χ) (C c : ℝ) (hc : 0 < c)
    (hK : 3 * max C 0 + 20 ≤ c * p.Ks / 4) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (C * ((p.T n : ℝ) * Real.log (p.T n) +
        ((p.J n : ℝ) + 1) * Real.log (p.m n))) * Real.exp (-(c * p.s n) / 4) ≤ groupEps p n / 3 := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hpow : Tendsto (fun n => (p.m n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hm
  filter_upwards [hm.eventually_ge_atTop 3, hpow.eventually_ge_atTop 2,
    high_pattern_overhead_eventually p] with n hM hp ho
  have hJ : (1 : ℝ) ≤ p.J n := by
    have hh : (p.m n : ℝ) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hlog : 0 ≤ Real.log (p.m n) := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ (p.T n : ℝ) * Real.log (p.T n) := by
    have hpT : (0 : ℝ) < p.T n := by
      have hh : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.T n : ℝ) := Nat.le_ceil _
      exact (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < p.m n) _).trans_le hh
    have hone : (1 : ℝ) ≤ p.T n := by exact_mod_cast (show 1 ≤ p.T n by exact_mod_cast hpT)
    exact mul_nonneg hpT.le (Real.log_nonneg hone)
  let A : ℝ := (p.T n : ℝ) * Real.log (p.T n) + ((p.J n : ℝ) + 1) * Real.log (p.m n)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ 3 * (p.J n : ℝ) * Real.log (p.m n) := by
    dsimp [A]
    nlinarith
  have hcount := (mul_le_mul_of_nonneg_right (le_max_left C 0) hA0).trans
    (mul_le_mul_of_nonneg_left hA (le_max_right C 0))
  have hs : p.Ks * (p.J n : ℝ) * Real.log (p.m n) ≤ (p.s n : ℝ) := Nat.le_ceil _
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ c / 4)
  have hcoef := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ (p.J n : ℝ) * Real.log (p.m n) by positivity)
  have hJl := mul_le_mul_of_nonneg_right hJ hlog
  have hlog3 : Real.log 3 ≤ Real.log (p.m n : ℝ) := Real.log_le_log (by norm_num) hM
  have hexp : C * A - c * (p.s n : ℝ) / 4 + Real.log 3 ≤ -12 * Real.log (p.m n) := by
    nlinarith
  have hh := Real.exp_le_exp.mpr hexp
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hh
  change Real.exp (C * A) * Real.exp (-(c * p.s n) / 4) ≤ _
  rw [← Real.exp_add]
  have he : C * A + -(c * (p.s n : ℝ)) / 4 = C * A - c * (p.s n : ℝ) / 4 := by ring
  rw [he]
  dsimp [groupEps]
  linarith

theorem group_cost_eventually (p : Params5 γ K' χ) (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * groupEps p n < 1 ∧
      2 * ((D * (p.m n + 1) ^ 2 * (p.J n + 3) : ℕ) : ℝ) ^ 2 * groupEps p n ≤ 1 / 2 := by
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hlog := Real.tendsto_log_atTop.comp hm
  have heps : Tendsto (groupEps p) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 12))
    change Tendsto (fun n => Real.exp (-12 * Real.log (p.m n))) atTop (𝓝 0)
    simpa only [Function.comp_def, mul_zero, zero_mul, neg_mul, mul_comm] using hh
  have hcost : Tendsto (fun n => 512 * (D : ℝ) ^ 2 * Real.exp (-6 * Real.log (p.m n))) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 6))).const_mul (512 * (D : ℝ) ^ 2)
    simpa only [Function.comp_def, mul_zero, zero_mul, neg_mul, mul_comm] using hh
  filter_upwards [hm.eventually_ge_atTop 1,
    heps.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hcost.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hM hε hsmall
  refine ⟨by linarith, ?_⟩
  have hmnat : 1 ≤ p.m n := by exact_mod_cast hM
  have hJ : (p.J n : ℝ) ≤ p.m n := by exact_mod_cast Lane_sol_s05_h1.J_le_m p n hmnat
  let M : ℝ := p.m n
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hB : (D : ℝ) * (M + 1) ^ 2 * ((p.J n : ℝ) + 3) ≤ 16 * D * M ^ 3 := by
    calc
      _ ≤ (D : ℝ) * (2 * M) ^ 2 * (4 * M) := by
        gcongr <;> dsimp [M] <;> linarith
      _ = _ := by ring
  have hB0 : 0 ≤ (D : ℝ) * (M + 1) ^ 2 * ((p.J n : ℝ) + 3) := by positivity
  have hε0 : 0 ≤ groupEps p n := (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ hB0 hB 2
  have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 2 * groupEps p n)
  have he : 2 * (16 * (D : ℝ) * M ^ 3) ^ 2 * groupEps p n =
      512 * (D : ℝ) ^ 2 * Real.exp (-6 * Real.log M) := by
    rw [show 2 * (16 * (D : ℝ) * M ^ 3) ^ 2 * groupEps p n =
      512 * (D : ℝ) ^ 2 * (M ^ 6 * groupEps p n) by ring]
    rw [nat_power_exp M hM0]
    change 512 * (D : ℝ) ^ 2 * (Real.exp ((6 : ℝ) * Real.log M) * Real.exp (-12 * Real.log M)) = _
    rw [← Real.exp_add]
    congr 2
    ring
  have hh : 2 * ((D : ℝ) * (M + 1) ^ 2 * ((p.J n : ℝ) + 3)) ^ 2 * groupEps p n ≤
      512 * (D : ℝ) ^ 2 * Real.exp (-6 * Real.log M) := by
    rw [← he]
    nlinarith
  push_cast
  exact hh.trans hsmall.le

def stage5Request (C : ℝ) (cL cH : Pre15 → ℝ) : ParamReq5 where
  Kcap := fun _ => 0
  Kpp := fun _ => 0
  Kh := fun _ => 0
  K1 := fun x => 160 / x.1.2.2.2.1
  K2 := fun x => 4 * (max C 0 + 20) / (3 * cL x.1)
  KD := fun _ => 0
  Ks := fun x => 4 * (3 * max C 0 + 20) / cH x.1.1.1
  KB := fun _ => 0
  alpha := fun _ => 1
  alpha_pos := by intro x; norm_num

theorem stage5_request_budgets (p : Params5 γ K' χ) (C : ℝ) (cL cH : Pre15 → ℝ)
    (hc : ∀ x, 0 < cL x ∧ 0 < cH x) (hp : (stage5Request C cL cH).Holds p) :
    160 ≤ p.delta * p.K1 ∧ max C 0 + 20 ≤ 3 * cL p.pre1 * p.K2 / 4 ∧
      3 * max C 0 + 20 ≤ cH p.pre1 * p.Ks / 4 := by
  have h1 := hp.2.2.2.1
  have h2 := hp.2.2.2.2.1
  have hs := hp.2.2.2.2.2.2.1
  change 160 / p.delta ≤ p.K1 at h1
  change 4 * (max C 0 + 20) / (3 * cL p.pre1) ≤ p.K2 at h2
  change 4 * (3 * max C 0 + 20) / cH p.pre1 ≤ p.Ks at hs
  have hL := (hc p.pre1).1
  have hh1 := (div_le_iff₀ p.hdelta.1).1 h1
  have hh2 := (div_le_iff₀ (by positivity : 0 < 3 * cL p.pre1)).1 h2
  have hhs := (div_le_iff₀ (hc p.pre1).2).1 hs
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

end
end HypercubeRamsey.Lane_sol_s05_h5l
