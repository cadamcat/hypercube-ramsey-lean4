import HypercubeRamsey.S18.Nodes_q_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4

open Classical Filter
open scoped BigOperators

theorem terminalScaleEventually
    (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT),
      8 ≤ T.S.n k ∧ 1 ≤ (D.encoding.Ts : ℝ) ∧ (D.geom.r : ℝ) ≤ D.encoding.Ts := by
  let R : ℝ := max 1 (2 * κ.A0 / Real.log 2)
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop
    (max 8 ⌈Real.exp R⌉₊)] with k hn
  intro PT hPT D
  have hn8 : 8 ≤ T.S.n k := le_trans (le_max_left _ _) hn
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hn1 : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hn8r : 8 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn8
  have hlog : R ≤ Real.log (T.S.n k) := by
    apply (Real.le_log_iff_exp_le hnpos).2
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (le_max_right _ _) hn))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hlog1 : 1 ≤ Real.log (T.S.n k) := hR1.trans hlog
  have hTs : Real.log (T.S.n k) ^ 2 ≤ (D.encoding.Ts : ℝ) := by
    rw [D.encoding.Ts_eq]
    exact Nat.le_ceil _
  have hTs1 : 1 ≤ (D.encoding.Ts : ℝ) := by nlinarith
  have hr : (D.geom.r : ℝ) ≤ (D.encoding.Ts : ℝ) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hR : 2 * κ.A0 / Real.log 2 ≤ R := le_max_right _ _
    have hRmul : 2 * κ.A0 ≤ R * Real.log 2 := (div_le_iff₀ hlog2).1 hR
    have hupper := D.l16_valid.r_upper
    have hmul := mul_le_mul_of_nonneg_right hRmul (by linarith : 0 ≤ Real.log (T.S.n k))
    have hbound : (D.geom.r : ℝ) ≤ R * Real.log (T.S.n k) := by
      apply (mul_le_mul_iff_of_pos_right hlog2).1
      nlinarith [hupper, hmul]
    have hsecond := mul_le_mul_of_nonneg_right hlog (by linarith : 0 ≤ Real.log (T.S.n k))
    nlinarith
  exact ⟨hn8, hTs1, hr⟩

theorem terminalPositiveEventually
    {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), S18.TerminalRiskBound D δ →
      ∀ L : S18.LeafCoupling D δ,
        0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x := by
  filter_upwards [terminalScaleEventually κ T] with k hscale
  intro PT hPT D hRisk L
  obtain ⟨hn8, hTs1, hr⟩ := hscale D
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hn1 : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hn8r : 8 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn8
  have hP : (100 * (κ.Ac + 10) : ℕ) ≤ κ.P := hκ.P_big.2
  have hPr : 100 * ((κ.Ac : ℝ) + 10) ≤ (κ.P : ℝ) := by exact_mod_cast hP
  have hexp : 20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
      (κ.P : ℝ) * D.encoding.Ts / 3 ≤ -1 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_right hPr (Nat.cast_nonneg D.encoding.Ts)
    have hAc : 0 ≤ (κ.Ac : ℝ) := Nat.cast_nonneg _
    have hAcTs : 0 ≤ (κ.Ac : ℝ) * D.encoding.Ts := mul_nonneg hAc (Nat.cast_nonneg _)
    nlinarith
  have hleafexp : -((κ.P : ℝ) * D.encoding.Ts / 3) ≤ -1 := by
    have hmul := mul_le_mul_of_nonneg_right hPr (Nat.cast_nonneg D.encoding.Ts)
    have hAcTs : 0 ≤ (κ.Ac : ℝ) * D.encoding.Ts := by positivity
    nlinarith
  have hleaf : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤
      (T.S.n k : ℝ)⁻¹ := by
    intro i
    calc
      D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) :=
        Lane_q_s18_n4.leafProbabilityBound D δ hRisk L i
      _ ≤ Real.rpow (T.S.n k : ℝ) (-1) :=
        Real.rpow_le_rpow_of_exponent_le hn1 hleafexp
      _ = (T.S.n k : ℝ)⁻¹ := Real.rpow_neg_one _
  have hinv : (T.S.n k : ℝ)⁻¹ ≤ 1 / 8 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hn8r
  apply Lane_q_s18_n4.terminalSetPositiveOfLeafBounds D δ L
  · intro i
    exact le_trans (hleaf i) (by linarith)
  · intro i
    calc
      (∑ j, if L.adjacent i j then 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤
          2 * Real.rpow (T.S.n k : ℝ)
            (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
              (κ.P : ℝ) * D.encoding.Ts / 3) := L.touching_charge i
      _ ≤ 2 * Real.rpow (T.S.n k : ℝ) (-1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp) (by norm_num)
      _ ≤ 1 / 2 := by
        have hpow : Real.rpow (T.S.n k : ℝ) (-1) = (T.S.n k : ℝ)⁻¹ := Real.rpow_neg_one _
        rw [hpow]
        linarith

end HypercubeRamsey.Lane_sol_s18_n4
