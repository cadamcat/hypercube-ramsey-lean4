import HypercubeRamsey.S05.Even_posterior_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000

variable {γ K' χ : ℝ}

theorem tau_positive (p : Params5 γ K' χ) : 0 < p.tau0 ∧ 0 < p.tau1 := by
  have h08 := p.ha_order 0 8 (by decide)
  rw [p.ha0] at h08
  constructor <;> linarith [p.hgap.1, p.hgap.2.1]

def truncGap (p : Params5 γ K' χ) : ℝ := p.tau1 * p.nu1 - p.tau0

theorem truncGap_positive (p : Params5 γ K' χ) : 0 < truncGap p := by
  obtain ⟨hτ0, hτ1⟩ := tau_positive p
  have hh := (div_lt_iff₀ hτ1).mp p.hnu1.1
  unfold truncGap
  nlinarith

theorem heavy_mass_bound {N k n : ℕ} (p : Params5 γ K' χ) (P : FinProb (Fin k → Fin N))
    (hN : 0 < N) (hk : 0 < k) (hn : 1 ≤ n)
    (hklarge : 4 * p.tau1 / truncGap p ≤ (k : ℝ))
    (hnlarge : 4 * Real.log 2 / truncGap p ≤ (n : ℝ))
    (hcap : ∀ z, (N : ℝ) ^ k * P.w z ≤ Real.exp (p.tau0 * k * n)) :
    ∑ x ∈ heavyCoordinateSet P (p.tau1 * n), averageCoordinateMarginal P x ≤
      p.nu1 + Real.exp (-(truncGap p * n / 2)) := by
  let q := ⌊p.nu1 * k⌋₊
  have hg : 0 < truncGap p := truncGap_positive p
  obtain ⟨hτ0, hτ1⟩ := tau_positive p
  have hν : 0 < p.nu1 := (div_pos hτ0 hτ1).trans p.hnu1.1
  have hν1 : p.nu1 < 1 := by linarith [p.hnu0, p.hnu1.2]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hq : (q : ℝ) ≤ p.nu1 * k := Nat.floor_le (mul_nonneg hν.le hkR.le)
  have hqk : q ≤ k := by
    exact_mod_cast hq.trans (by nlinarith : p.nu1 * (k : ℝ) ≤ k)
  have hqratio : (q : ℝ) / k ≤ p.nu1 := (div_le_iff₀ hkR).mpr hq
  have hqlo : p.nu1 * k < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have ht := (heavyTruncation hN hk P (p.tau0 * k * n) (p.tau1 * n) hcap).2 q hqk
  have hpow2 : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hkn := (div_le_iff₀ hg).mp hklarge
  have hnn := (div_le_iff₀ hg).mp hnlarge
  have h1 := mul_le_mul_of_nonneg_right hnn hkR.le
  have h2 := mul_le_mul_of_nonneg_right hkn hnR.le
  have hqterm := mul_lt_mul_of_pos_left hqlo (mul_pos hτ1 hnR)
  have hexponent : (k : ℝ) * Real.log 2 + p.tau0 * k * n - (p.tau1 * n) * q ≤
      -(truncGap p * (k : ℝ) * n / 2) := by
    unfold truncGap at *
    nlinarith
  have htail : (2 : ℝ) ^ k * Real.exp (p.tau0 * k * n) * Real.exp (-(p.tau1 * n) * q) ≤
      Real.exp (-(truncGap p * n / 2)) := by
    rw [hpow2, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show -(p.tau1 * (n : ℝ)) * q = -((p.tau1 * (n : ℝ)) * q) by ring, ← sub_eq_add_neg]
    refine hexponent.trans ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hh := mul_le_mul_of_nonneg_right hk1 (mul_nonneg hg.le hnR.le)
    nlinarith
  exact ht.trans (add_le_add hqratio htail)

theorem eventual_trunc_threshold (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 4 * Real.log 2 / truncGap p ≤ (n : ℝ) ∧
      Real.exp (-(truncGap p * n / 2)) ≤ (1 - p.nu0 - p.nu1) / 2 := by
  have hg : 0 < truncGap p := truncGap_positive p
  have htol : 0 < (1 - p.nu0 - p.nu1) / 2 := by linarith [p.hnu1.2]
  have ht : Tendsto (fun n : ℕ => Real.exp (-(truncGap p * n / 2))) atTop (nhds 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (div_pos hg (by norm_num : (0 : ℝ) < 2)))
    convert hh using 1
    ext n
    congr 1
    ring
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * Real.log 2 / truncGap p),
    (tendsto_order.mp ht).2 _ htol] with n hn hlarge hsmall
  exact ⟨hn, hlarge, hsmall.le⟩

end
end HypercubeRamsey.Lane_sol_s05_even
