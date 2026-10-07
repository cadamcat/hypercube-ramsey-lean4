import HypercubeRamsey.S18.Ancestors_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators

theorem eventually_query_size (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, ∀ roots : Finset (Pos T k), roots.card ≤ T.S.n k →
        ∀ m, m ≤ D.geom.r + 1 →
          ((ancestors roots m).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) ∧
          ((rowCells D (ancestors roots m)).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
  let C : ℝ := 2 * κ.A0 / Real.log 2
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlog := (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop (max 1 (3 * C + 7))
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2, hlog] with k hn hl
  intro PT hPT D roots hroots m hm
  have hnPos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hl1 : 1 ≤ Real.log (T.S.n k : ℝ) := (le_max_left _ _).trans hl
  have hlC : 3 * C + 7 ≤ Real.log (T.S.n k : ℝ) := (le_max_right _ _).trans hl
  have hr : (D.geom.r : ℝ) ≤ C * Real.log (T.S.n k : ℝ) := by
    dsimp [C]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr D.l16_valid.r_upper
  have hmR : (m : ℝ) ≤ D.geom.r + 1 := by exact_mod_cast hm
  have hexp : ((3 * m + 4 : ℕ) : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hlC (show 0 ≤ Real.log (T.S.n k : ℝ) from by linarith)
    push_cast
    nlinarith
  have hpower : (T.S.n k : ℝ) ^ (3 * m + 4) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
    have he : (T.S.n k : ℝ) ^ (3 * m + 4) =
        Real.exp ((3 * m + 4 : ℕ) * Real.log (T.S.n k : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hnPos]
    rw [he]
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_right hexp (show 0 ≤ Real.log (T.S.n k : ℝ) from by linarith)
    nlinarith
  constructor
  · have h : ((ancestors roots m).card : ℝ) ≤ (T.S.n k : ℝ) ^ (3 * m + 4) := by
      exact_mod_cast ancestors_rows_card roots hroots hn m
    exact h.trans hpower
  · have h : ((rowCells D (ancestors roots m)).card : ℝ) ≤ (T.S.n k : ℝ) ^ (3 * m + 4) := by
      exact_mod_cast ancestors_query_card D roots hroots hn m
    exact h.trans hpower

end HypercubeRamsey.S18.Lane_sol_s18_n5
