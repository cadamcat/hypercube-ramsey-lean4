import HypercubeRamsey.S15.ClusterBinScales_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelGeometry_sol_s15_c2

namespace HypercubeRamsey.S15.Lane_q_s15_clock_atoms

open HypercubeRamsey HypercubeRamsey.S15 Classical Filter

set_option maxHeartbeats 400000 in
theorem highLarge_label_atoms (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (A' : ℝ) (hA' : 0 < A') :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highLarge →
    ∀ W : ClusterHistory PT hPT hm, ∀ B : ClusterBinAssignment PT,
      0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      ∀ b : OddPosition T k, ∀ y : Fin (T.S.N k),
        (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w y ≤
          (T.S.n k : ℝ) ^ (-A') := by
  let logn : ℕ → ℝ := fun k => Real.log (T.S.n k : ℝ)
  have hn : Filter.Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have hlog : Filter.Tendsto logn atTop atTop := by
    exact Real.tendsto_log_atTop.comp hn
  have hloglarge : ∀ᶠ k : ℕ in atTop, 48 ≤ logn k ∧ 8 * (A' + 1) ≤ logn k := by
    filter_upwards [hlog.eventually_ge_atTop 48,
      hlog.eventually_ge_atTop (8 * (A' + 1))] with k h48 hA
    exact ⟨h48, hA⟩
  filter_upwards [hloglarge] with k hk
  intro PT hPT hm hlarge W B hB b y
  let n : ℝ := T.S.n k
  let g := clusterGroupIndexAt PT hPT hm b
  let i := g.1.1
  let q : ℝ := (PT.tiling.P i).q
  let h : ℝ := (PT.tiling.P i).h
  have hnpos : 0 < n := by
    dsimp [n, logn] at hk
    by_contra hn'
    have hn0 : (T.S.n k : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn') (Nat.cast_nonneg _)
    have hbad : (48 : ℝ) ≤ 0 := by simpa [hn0] using hk.1
    norm_num at hbad
  have hnR : 0 < (T.S.n k : ℝ) := by simpa [n] using hnpos
  have hq1 : 1 ≤ q := by
    have hqLarge :
        (Real.log (T.S.n k : ℝ)) ^ 2 < q := by
      have hd := hPT.tiling_valid.cluster_data (Or.inr (Or.inr hlarge)) i
      rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, hlargeIff⟩
      simpa [q, n] using hlargeIff.mp hlarge
    dsimp [n, logn] at hk
    nlinarith
  have hdata := hPT.tiling_valid.cluster_data (Or.inr (Or.inr hlarge)) i
  rcases hdata with
    ⟨_, _, _, _, hdbinField, _, _, _, hheightUpper, _, _, hlargeIff⟩
  have hdbin : (PT.tiling.P i).d = ⌊Real.exp (q / 2)⌋₊ :=
    hdbinField (Or.inr hlarge)
  have hqLarge : (Real.log n) ^ 2 < q := by
    simpa [q, n] using hlargeIff.mp hlarge
  have hheight : h < 2 * Real.rpow q (κ.Mhi : ℝ) := by
    simpa [h, hlarge] using hheightUpper
  have hq2304 : 2304 ≤ q := by
    dsimp [n, logn] at hk
    nlinarith [hqLarge, hk.1]
  have hMhi1 : 1 ≤ (κ.Mhi : ℝ) := by
    have hCbRatio : 0 < 100 * κ.aC / κ.aB := by
      positivity [hκ.aC_rng.1, hκ.aB_rng.1]
    have hCb : 100 < κ.Cb := by linarith [hκ.Cb_big]
    have hMlo : 100 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big]
    have hden : 1 < 20 * (κ.Mlo : ℝ) := by nlinarith
    have hcq1 : κ.cq < 1 := by
      exact hκ.cq_rng.2.trans ((div_lt_one (by positivity)).2 hden)
    have hmhi := hκ.Mhi_big.2
    have hMhi5 : 5 < (κ.Mhi : ℝ) := by
      by_contra h
      have hle : (κ.Mhi : ℝ) ≤ 5 := le_of_not_gt h
      have hmul := mul_le_mul_of_nonneg_right hle hκ.cq_rng.1.le
      nlinarith [hmhi, hcq1]
    linarith
  have hω4 : 4 * κ.ω ≤ 1 := by
    have hω := hκ.ω_rng.2
    have haC : κ.aC < 1 := by
      have hmin := min_le_right κ.η0 (1 : ℝ)
      linarith [hκ.aC_rng.2]
    have hmul := mul_le_mul_of_nonneg_left hMhi1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hκ.ω_rng.1.le)
    nlinarith
  let γ : ℝ := 4 * κ.ω
  let δ : ℝ := γ * (κ.Mhi : ℝ)
  have hγpos : 0 < γ := by dsimp [γ]; positivity [hκ.ω_rng.1]
  have hγle : γ ≤ 1 := by exact hω4
  have hδpos : 0 < δ := by dsimp [δ, γ]; positivity [hκ.ω_rng.1, hMhi1]
  have hδhalf : δ ≤ 1 / 2 := by
    have hω := hκ.ω_rng.2
    have haC : κ.aC < 1 / 1000000 := by
      calc
        κ.aC < min κ.η0 1 / 10 ^ 6 := hκ.aC_rng.2
        _ ≤ 1 / 10 ^ 6 :=
          div_le_div_of_nonneg_right (min_le_right κ.η0 (1 : ℝ)) (by positivity)
        _ = 1 / 1000000 := by norm_num
    dsimp [δ, γ]
    nlinarith
  have hH1 : 1 ≤ h := by
    have hh := clusterHeight_pos PT hPT hm i
    dsimp [h]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hh.ne')
  have hkScale :
      (PT.tiling.kScale i : ℝ) ≤ 2 * h ^ (3 * κ.ω) := by
    have hpow : (1 : ℝ) ≤ h ^ (3 * κ.ω) :=
      Real.one_le_rpow hH1 (by nlinarith [hκ.ω_rng.1])
    simpa [Tiling.kScale, sliceK, h] using Nat.ceil_le_two_mul
      ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hpow)
  have htScale :
      (PT.tiling.tScale i : ℝ) ≤ 2 * h ^ κ.ω := by
    have hpow : (1 : ℝ) ≤ h ^ κ.ω :=
      Real.one_le_rpow hH1 hκ.ω_rng.1.le
    simpa [Tiling.tScale, sliceT, h] using Nat.ceil_le_two_mul
      ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hpow)
  have hscale :
      (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 8 * Real.sqrt q := by
    have hht : 0 < h := by linarith
    have hqpos : 0 < q := by linarith
    have hpowHeight :
        h ^ γ ≤ (2 * Real.rpow q (κ.Mhi : ℝ)) ^ γ :=
      Real.rpow_le_rpow (by positivity) hheight.le hγpos.le
    have hpowId :
        (2 * Real.rpow q (κ.Mhi : ℝ)) ^ γ =
          Real.rpow (2 : ℝ) γ * Real.rpow q δ := by
      have hmul :
          (2 * Real.rpow q (κ.Mhi : ℝ)) ^ γ =
          Real.rpow (2 : ℝ) γ * (Real.rpow q (κ.Mhi : ℝ)) ^ γ :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hqpos.le _)
      rw [hmul]
      change Real.rpow (2 : ℝ) γ * (Real.rpow q (κ.Mhi : ℝ)) ^ γ =
        Real.rpow (2 : ℝ) γ * Real.rpow q δ
      have hcomp :
          (Real.rpow q (κ.Mhi : ℝ)) ^ γ =
            Real.rpow q ((κ.Mhi : ℝ) * γ) :=
        (Real.rpow_mul hqpos.le (κ.Mhi : ℝ) γ).symm
      calc
        _ = Real.rpow (2 : ℝ) γ * Real.rpow q ((κ.Mhi : ℝ) * γ) := by
          rw [hcomp]
        _ = _ := by
          have hexp : (κ.Mhi : ℝ) * γ = δ := by
            dsimp [δ]
            ring
          exact congrArg
            (fun e : ℝ => Real.rpow (2 : ℝ) γ * Real.rpow q e) hexp
    have htwo : Real.rpow (2 : ℝ) γ ≤ 2 := by
      calc
        Real.rpow (2 : ℝ) γ ≤ Real.rpow (2 : ℝ) 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hγle
        _ = 2 := Real.rpow_one (2 : ℝ)
    have hqpow : Real.rpow q δ ≤ Real.sqrt q := by
      rw [Real.sqrt_eq_rpow q]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hδhalf
    have hqpow0 : 0 ≤ Real.rpow q δ := Real.rpow_nonneg (by positivity) _
    calc
      (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤
          (2 * h ^ (3 * κ.ω)) * (2 * h ^ κ.ω) :=
        mul_le_mul hkScale htScale (by positivity) (by positivity)
      _ = 4 * h ^ γ := by
        rw [show γ = 3 * κ.ω + κ.ω by dsimp [γ]; ring,
          Real.rpow_add hht]
        ring
      _ ≤ 4 * (2 * Real.rpow q (κ.Mhi : ℝ)) ^ γ :=
        mul_le_mul_of_nonneg_left hpowHeight (by norm_num)
      _ = 4 * (Real.rpow (2 : ℝ) γ * Real.rpow q δ) := by rw [hpowId]
      _ ≤ 4 * (2 * Real.sqrt q) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul htwo hqpow hqpow0 (by norm_num)
      _ = 8 * Real.sqrt q := by ring
  have hsqrt : Real.sqrt q ≤ q / 48 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (show 0 ≤ q by linarith)]
  have hpenalty : (3 / 2 : ℝ) *
      ((PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) ≤ q / 4 := by
    calc
      _ ≤ 12 * Real.sqrt q := by nlinarith [hscale]
      _ ≤ 12 * (q / 48) := by gcongr
      _ = q / 4 := by ring
  have hx : 2 ≤ Real.exp (q / 2) := by
    have harg : 1 ≤ q / 2 := by linarith
    calc
      2 ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h
        exact h
      _ ≤ Real.exp (q / 2) := Real.exp_le_exp.mpr harg
  have hfloor : Real.exp (q / 2) - 1 < ((PT.tiling.P i).d : ℝ) := by
    rw [hdbin]
    exact Nat.sub_one_lt_floor _
  have hdfloor :
      Real.exp (q / 2) / 2 ≤ ((PT.tiling.P i).d : ℝ) := by
    have hhalf : Real.exp (q / 2) / 2 ≤ Real.exp (q / 2) - 1 := by
      linarith [hx]
    exact (hhalf.trans_lt hfloor).le
  have hweightB :
      (clusterIndependentBinKernel PT hPT hm W).w B =
        ∏ g : ClusterGroupIndex PT,
          (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
    unfold clusterIndependentBinKernel
    rfl
  have hprod :
      (∏ g : ClusterGroupIndex PT,
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g)) ≠ 0 := by
    exact hweightB ▸ ne_of_gt hB
  have hqbin :
      0 < (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
    have hne := Finset.prod_ne_zero_iff.mp hprod g (Finset.mem_univ g)
    exact lt_of_le_of_ne
      ((clusterSolver PT hPT hm g.1.1).q_nonneg g.2 (historyOnSlice W g.1) (B g))
      (Ne.symm hne)
  have hUatom :=
    (clusterSolver PT hPT hm g.1.1).U_atom_cap g.2
      (historyOnSlice W g.1) (B g) y hqbin
  have hpenaltyGbase : (3 / 2 : ℝ) *
      ((PT.tiling.kScale g.1.1 : ℝ) * PT.tiling.tScale g.1.1) ≤ q / 4 := by
    simpa [i] using hpenalty
  have hpenaltyG : 1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
      PT.tiling.tScale g.1.1 ≤ q / 4 := by
    calc
      _ = (3 / 2 : ℝ) *
          ((PT.tiling.kScale g.1.1 : ℝ) * PT.tiling.tScale g.1.1) := by ring
      _ ≤ q / 4 := hpenaltyGbase
  have hdfloorG : Real.exp (q / 2) / 2 ≤ ((PT.tiling.P g.1.1).d : ℝ) := by
    simpa [i] using hdfloor
  change (clusterSolver PT hPT hm g.1.1).U g.2
      (historyOnSlice W g.1) (B g) y ≤ (T.S.n k : ℝ) ^ (-A')
  calc
    _ ≤ 2 * Real.exp (1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
        PT.tiling.tScale g.1.1) / (PT.tiling.P g.1.1).d := hUatom
    _ ≤ 4 * Real.exp (-q / 4) := by
      have hrecip :
          ((PT.tiling.P g.1.1).d : ℝ)⁻¹ ≤ 2 * Real.exp (-q / 2) := by
        calc
          _ ≤ (Real.exp (q / 2) / 2)⁻¹ := by
            simpa [one_div] using
              (one_div_le_one_div_of_le (by positivity) hdfloorG)
          _ = 2 * (Real.exp (q / 2))⁻¹ := by
            field_simp [ne_of_gt (Real.exp_pos (q / 2))]
          _ = 2 * Real.exp (-q / 2) := by
            rw [show -q / 2 = -(q / 2) by ring, Real.exp_neg]
      rw [div_eq_mul_inv]
      calc
        _ ≤ (2 * Real.exp (1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
            PT.tiling.tScale g.1.1)) *
              (2 * Real.exp (-q / 2)) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = 4 * Real.exp (1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
            PT.tiling.tScale g.1.1 - q / 2) := by
          calc
            _ = (2 * 2) * (Real.exp (1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
                PT.tiling.tScale g.1.1) *
                  Real.exp (-q / 2)) := by ring
            _ = _ := by
              rw [← Real.exp_add]
              rw [show
                (1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
                    PT.tiling.tScale g.1.1) + (-q / 2) =
                  1.5 * (PT.tiling.kScale g.1.1 : ℝ) *
                    PT.tiling.tScale g.1.1 - q / 2 by ring]
              ring
        _ ≤ 4 * Real.exp (-q / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          linarith [hpenaltyG]
    _ ≤ (T.S.n k : ℝ) ^ (-A') := by
      have ht : A' * Real.log n + Real.log 4 ≤ q / 4 := by
        dsimp [n, logn] at hk
        have hprodT :
            8 * (A' + 1) * Real.log (T.S.n k : ℝ) ≤
              (Real.log (T.S.n k : ℝ)) ^ 2 := by
          calc
            _ ≤ Real.log (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) :=
              mul_le_mul_of_nonneg_right hk.2 (by linarith [hk.1])
            _ = _ := by ring
        have hlog4 : Real.log (4 : ℝ) ≤ 4 :=
          Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)
        have hAprod :
            0 ≤ A' * Real.log (T.S.n k : ℝ) :=
          mul_nonneg hA'.le (by linarith [hk.1])
        nlinarith [hqLarge, hAprod]
      have hExp : 4 * Real.exp (-q / 4) =
          Real.exp (Real.log 4 - q / 4) := by
        calc
          _ = Real.exp (Real.log 4) * Real.exp (-q / 4) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          _ = Real.exp (Real.log 4 + (-q / 4)) :=
            (Real.exp_add _ _).symm
          _ = _ := by congr 1 <;> ring
      rw [hExp, Real.rpow_def_of_pos hnR]
      apply Real.exp_le_exp.mpr
      linarith

end HypercubeRamsey.S15.Lane_q_s15_clock_atoms
