import HypercubeRamsey.S12.HomogeneousPeeling

/-!
Lane-local interfaces for the S15 copy of the Section 12 finite-law vocabulary.
-/

namespace HypercubeRamsey.Lane_q_s15_needs2

open Filter

/-- The fixed degree-window radius eventually falls below half the reference degree. -/
theorem eventually_degree_radius_lt_half (T : Stage) (C0 : ℝ) :
    ∀ᶠ k in atTop, C0 * bstar T k < 1 / 2 := by
  have hn : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  have hpow : Tendsto (fun k : ℕ => (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn
    simpa [Function.comp_def,
      show (-1 + (0.04 : ℝ)) = -(0.96 : ℝ) by norm_num] using h
  have hlim : Tendsto (fun k => C0 * bstar T k) atTop (nhds 0) := by
    simpa [bstar] using (tendsto_const_nhds.mul hpow)
  filter_upwards [Metric.tendsto_nhds.1 hlim (1 / 2) (by norm_num)] with k hk
  have hk' : |C0 * bstar T k| < 1 / 2 := by
    simpa [Real.dist_eq] using hk
  exact (abs_lt.mp hk').2

end HypercubeRamsey.Lane_q_s15_needs2
