import HypercubeRamsey.S15.DirectNodes_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem small_bin_atom_exponential (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hs : PT.tiling.mode = .highSmall,
      ∀ W : ClusterHistory PT hPT (Or.inl hs), ∀ g : ClusterGroupIndex PT, ∀ D : clusterBinType g,
        (clusterSolver PT hPT (Or.inl hs) g.1.1).q g.2 (historyOnSlice W g.1) D ≤
          4 * Real.exp (-c * (T.S.n k : ℝ)) := by
  let c : ℝ := Real.log 2 / 2
  let C : ℝ := 9 + κ.a
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hι : κ.ι ≤ 1 / 2 := by linarith [hκ.ι_rng.2]
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hscale := hn.eventually (Lane_sol_consts_adm.eventually_power_bound (1 / 2) 1 C c (by norm_num) hc)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hscale, T.S.eventually_large 1 1] with k hscale hhost
  intro PT hPT hs W g D
  let i := g.1.1
  let n : ℝ := T.S.n k
  let N : ℝ := T.S.N k
  let M : ℝ := (PT.tiling.P i).M
  let Kt : ℝ := (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hhost.1
  have hnpos : 0 < n := by linarith only [hn1]
  have hNpos : 0 < N := by dsimp [N]; exact_mod_cast T.S.N_pos k
  have hMpos : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hNlower : (2 : ℝ) ^ (T.S.n k) ≤ N := by
    simpa only [one_mul] using hhost.2.1
  have hheight : ((PT.tiling.P i).h : ℝ) ≤ n ^ κ.ι := by
    apply le_trans _ (hPT.tiling_valid.allocation_bounds i).1.le
    exact_mod_cast Nat.le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ
  have hKt : Kt ≤ 4 * n ^ κ.ι := by
    have h := Lane_sol_s15_cross.sampler_scale_product hκ (clusterHeight_pos PT hPT (Or.inl hs) i)
    have h' : Kt ≤ 4 * (PT.tiling.P i).h := by simpa [Kt, Tiling.kScale, Tiling.tScale] using h
    exact h'.trans (mul_le_mul_of_nonneg_left hheight (by norm_num))
  have hWidth : Real.log (N / M) ≤ κ.a * n ^ κ.ι :=
    Lane_sol_s15_cross.cluster_log_width hκ PT hPT (Or.inl hs) hn1 i
  have hd : ((PT.tiling.P i).d : ℝ) ≤ Real.exp (Real.sqrt (Real.log n)) := by
    obtain ⟨_, _, _, hd, _, _, _, _, _, _, _, _⟩ :=
      hPT.tiling_valid.cluster_data (Or.inr (Or.inl hs)) i
    have hnat : (PT.tiling.P i).d ≤ ⌊Real.exp (Real.sqrt (Real.log n))⌋₊ := by
      rw [hd hs]
      exact Nat.min_le_right _ _
    exact (by exact_mod_cast hnat : ((PT.tiling.P i).d : ℝ) ≤ ⌊Real.exp (Real.sqrt (Real.log n))⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hpow : n ^ κ.ι ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hι
  have hlog : Real.sqrt (Real.log n) ≤ Real.sqrt n := Real.sqrt_le_sqrt (Real.log_le_self hnpos.le)
  have hExpo : 2 * Kt + Real.sqrt (Real.log n) + Real.log (N / M) ≤ C * Real.sqrt n := by
    have hm := mul_le_mul_of_nonneg_left hpow ha.le
    nlinarith only [hKt, hWidth, hlog, hpow, hm]
  have hscale' : C * Real.sqrt n ≤ c * n := by
    change C * (T.S.n k : ℝ) ^ (1 / 2 : ℝ) ≤ c * (T.S.n k : ℝ) ^ (1 : ℝ) at hscale
    simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using hscale
  have hExpN : Real.exp (n * Real.log 2) = (2 : ℝ) ^ (T.S.n k) := by
    dsimp [n]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hInvN : 1 / N ≤ Real.exp (-n * Real.log 2) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (n * Real.log 2)) (hExpN ▸ hNlower)
    simpa only [show -n * Real.log 2 = -(n * Real.log 2) by ring, Real.exp_neg, one_div] using h
  have hq := (clusterSolver PT hPT (Or.inl hs) i).q_cap g.2 (historyOnSlice W g.1) D
  calc
    _ ≤ 4 * Real.exp (2 * Kt) * (PT.tiling.P i).d / M := by
      simpa only [Kt, M, mul_assoc] using hq
    _ ≤ 4 * Real.exp (2 * Kt) * Real.exp (Real.sqrt (Real.log n)) / M :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) hMpos.le
    _ = (4 / N) * Real.exp (2 * Kt + Real.sqrt (Real.log n) + Real.log (N / M)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hNpos hMpos)]
      field_simp
    _ ≤ (4 / N) * Real.exp (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExpo) (by positivity)
    _ = (4 * Real.exp (C * Real.sqrt n)) * (1 / N) := by ring
    _ ≤ (4 * Real.exp (C * Real.sqrt n)) * Real.exp (-n * Real.log 2) :=
      mul_le_mul_of_nonneg_left hInvN (by positivity)
    _ = 4 * Real.exp (C * Real.sqrt n - n * Real.log 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1 <;> ring
    _ ≤ 4 * Real.exp (-c * n) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      dsimp [c] at *
      linarith only [hscale']

end HypercubeRamsey.Lane_sol_s15_c2
