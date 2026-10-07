import HypercubeRamsey.S18.Defs
import HypercubeRamsey.S18.Nodes_q_s18_n3
import HypercubeRamsey.S18.Nodes_sol_fix_surv
import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.S18.Nodes_sol_s18_n1_sketch
import HypercubeRamsey.S18.Nodes_q_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl
import HypercubeRamsey.S18.Nodes_sol_s18_dl_base
import HypercubeRamsey.S18.Nodes_sol_split_d18l
import HypercubeRamsey.S18.Nodes_q_s18_n4
import HypercubeRamsey.S18.Nodes_q_s18_n5
import HypercubeRamsey.S18.Nodes_q_s18_n1
import HypercubeRamsey.S18.Nodes_sol_s18_n5
import HypercubeRamsey.S18.PoolBudget_sol_s18_n5
import HypercubeRamsey.S18.Isolates_sol_s18_n5
import HypercubeRamsey.S18.Nodes_sol_s18_5d
import HypercubeRamsey.S18.Completion_sol_s18_n5
import HypercubeRamsey.S18.Locality_sol_s18_n5
import HypercubeRamsey.S18.Backward_sol_s18_n5
import HypercubeRamsey.S18.Nodes_sol_s18_5b
import HypercubeRamsey.S18.Probability_sol_s18_n5
import HypercubeRamsey.S18.ColumnMoment_sol_s18_n5
import HypercubeRamsey.S18.Nodes_sol_s18_n4
import HypercubeRamsey.S18.Run_sol_s18_n4
import HypercubeRamsey.S18.Risk_sol_s18_n4
import HypercubeRamsey.S18.PrefixObligations_sol_s18_n4
import HypercubeRamsey.S18.Terminal_sol_s18_n4
import HypercubeRamsey.S18.Sampler_sol_s18_n4
import HypercubeRamsey.S18.Leaf_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_3e
import HypercubeRamsey.S18.Swap_sol_s18_n4
import HypercubeRamsey.S18.Locality_sol_s18_n4
import HypercubeRamsey.S18.Cost_sol_s18_n4
import HypercubeRamsey.S18.Test_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_3f
import HypercubeRamsey.S18.Current_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_4b
import HypercubeRamsey.S18.Nodes_q_s18_n7
import HypercubeRamsey.S18.Nodes_q_s18_n6
import HypercubeRamsey.S18.Nodes_sol_s18_6b
import HypercubeRamsey.S18.Nodes_q_s18_n6_g
import HypercubeRamsey.S18.Nodes_sol_s18_5e
import HypercubeRamsey.S18.Nodes_q_s18_n2
import HypercubeRamsey.S18.Nodes_q_s18_n3
import HypercubeRamsey.S18.Deletion_sol_s18_1b
import HypercubeRamsey.S18.Nodes_sol_s18_1c

/-! Repaired Section 18 skeleton. Leaf estimates remain proof-lane work;
all assemblies below use their stated outputs without new placeholders. -/
namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators

/-- D18.L, §§16–17 and 18:43–87. Construct actual initial data, not arbitrary
lists. The selected discrepancy budgets are forwarded from C12.K. The input
geometry includes the prescribed cell slot count and the same physical
calibration/source links, positive typical mass and internal probability
priors in `L16QuantitativeValidity.physical`. The output calibration uses a
50ρh consultation-centre margin. Equation (24)'s palette-row constant is
selected before the eventual index and retained alongside `Spec`.
The general calibration and upstream
construction gaps recorded in `Needs` remain producer obligations. -/
theorem D18_L {κ : CConsts} (hκ : κ.Admissible) (hThresholds : LateThresholds κ) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∃ Krow : ℝ, 0 < Krow ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, PT.tiling.mode.isLow → ProfileCornerMass PT → LargeIndex κ T k →
      (∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F) →
      Nonempty {D : LateData hPT // D.Spec ∧ PaletteRowInput D Krow} := by
  have hSources : Lane_sol_split_d18l.Sources κ T := ⟨hInit, hDeep, hDisc, hDiscι⟩
  obtain ⟨Krow, hKrow, hRows⟩ :=
    Lane_sol_split_d18l.D18_L_palette_row hκ hThresholds T hSources
  refine ⟨Krow, hKrow, ?_⟩
  filter_upwards [
    hRows,
    Lane_sol_split_d18l.D18_L_inputs hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_fresh_internal hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_prior_mean hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_cell_query_calibration hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_upstream_bad hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_upstream_bad_pinned hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_fresh_singleton hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_palette_counts hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_initial_cap hκ hThresholds T hSources,
    Lane_sol_split_d18l.D18_L_initial_success hκ hThresholds T hSources]
    with k hRows hInputs hInternal hMean hCalibration hBad hPinned hSingleton hCounts hCap hSuccess
  intro PT hPT hLow hMass hLarge hOld
  obtain ⟨X⟩ := hInputs PT hPT hLow hMass hLarge hOld
  let D := Lane_sol_split_d18l.rawData hκ X
  refine ⟨⟨D, {
    corner_mass := hMass
    fresh_internal := hInternal PT hPT X hMass hLarge
    thresholds := hThresholds
    calibration := ⟨hMean PT hPT X hMass hLarge,
      Lane_sol_split_d18l.D18_L_separated_calibration D
        (hCalibration PT hPT X hMass hLarge)
        (Lane_sol_split_d18l.D18_L_query_factorization hκ X)⟩
    upstream_bad := hBad PT hPT X hMass hLarge
    upstream_bad_pinned := hPinned PT hPT X hMass hLarge
    typical_positive := Lane_sol_split_d18l.D18_L_typical_positive hκ X
    fresh_singleton := hSingleton PT hPT X hMass hLarge
    scope_eq := Lane_sol_split_d18l.D18_L_scope_eq hκ X
    palette_counts := hCounts PT hPT X hMass hLarge
    palette_separation := Lane_sol_split_d18l.D18_L_palette_separation hκ X
    events_eq := Lane_sol_split_d18l.D18_L_events_eq hκ X
    initial_cap := hCap PT hPT X hMass hLarge
    initial_success := hSuccess PT hPT X hMass hLarge
    prior_local := Lane_sol_split_d18l.D18_L_prior_local D },
    hRows PT hPT X hMass hLarge⟩⟩

/-- L18.0a, 18:78–87. Constants precede all stages; epsilon precedes its
own eventual quantifier. Only L16-valid geometries are quantified. -/
theorem L18_0a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ Kβ : ℝ, 0 < Kβ ∧
      (∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow →
        ∀ G : LowGeom PT, ∀ F : FreshCell G, L16QuantitativeValidity G F → ScheduleAt κ T k PT G Kβ) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k,
        PT.Valid → PT.tiling.mode.isLow → ∀ G : LowGeom PT, ∀ F : FreshCell G,
          L16QuantitativeValidity G F → SmallErrors κ T k PT G ε) := by
  have hβ : 0 < κ.β := hκ.β_rng.1
  have hR : 0 ≤ κ.R := by rw [hκ.R_eq]; positivity
  have hKB : 0 ≤ κ.KB := by nlinarith [hκ.KB_big]
  have hA0 : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hβsum : κ.β * (1 + κ.KB + 2 * κ.A0) ≤ 0.02 := by
    have hden : 0 < 1 + κ.KB + 2 * κ.A0 := by positivity
    exact (le_div_iff₀ hden).1 hκ.β_rng.2.1
  let q : ℝ := Real.rpow 2 (-κ.β)
  have hq0 : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_one_iff.2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_neg_of_pos_of_neg hlog2 (by linarith)
  let Kβ : ℝ := 1 / (1 - q)
  have hKβ : 0 < Kβ := by
    dsimp [Kβ]
    positivity
  have hgeom (r : ℕ) : (∑ j : Fin r, q ^ (r - j.val)) ≤ Kβ := by
    simpa [Kβ] using
      HypercubeRamsey.Lane_q_s18_n1.finite_reverse_geometric_sum_le hq0 hq1 r
  have hterm (m : ℕ) : Real.rpow 2 (-κ.β * (m : ℝ)) = q ^ m := by
    calc
      Real.rpow 2 (-κ.β * (m : ℝ)) =
          Real.rpow (Real.rpow 2 (-κ.β)) (m : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-κ.β) (m : ℝ)
      _ = q ^ m := by simp [q, Real.rpow_natCast]
  have hsumError {k : ℕ} {PT : ProfiledTiling κ T k}
      (G : LowGeom PT) (i : Fin PT.tiling.m) :
      (∑ j : Fin G.r, lateError κ T k PT i (G.r - j.val)) ≤
        Kβ * Real.rpow (densityScale T k) (-κ.β) *
          Real.exp (-κ.β * PT.tiling.gain i) := by
    let A := Real.rpow (densityScale T k) (-κ.β) *
      Real.exp (-κ.β * PT.tiling.gain i)
    have hdpos : 0 < densityScale T k := by
      unfold densityScale
      exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    calc
      (∑ j : Fin G.r, lateError κ T k PT i (G.r - j.val)) =
          A * ∑ j : Fin G.r, q ^ (G.r - j.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [A, lateError]
        rw [hterm]
      _ ≤ A * Kβ := mul_le_mul_of_nonneg_left (hgeom G.r) hA
      _ = Kβ * Real.rpow (densityScale T k) (-κ.β) *
            Real.exp (-κ.β * PT.tiling.gain i) := by
        dsimp [A]
        ring
  have hsmallIndex : ∀ᶠ k in atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 2
  refine ⟨Kβ, hKβ, ?_, ?_⟩
  · filter_upwards [hsmallIndex] with k hn
    intro PT hPT hLow G F hL16 i
    refine ⟨?_, ?_⟩
    · intro j
      let n : ℝ := T.S.n k
      let d : ℝ := densityScale T k
      have hnreal : 1 ≤ n := by
        dsimp [n]
        exact_mod_cast (show 1 ≤ T.S.n k by omega)
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hnreal
      have hNpos : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
      have hdpos : 0 < d := by
        dsimp [d, densityScale]
        exact div_pos hNpos (by positivity)
      have hNle : (T.S.N k : ℝ) ≤ n * (2 : ℝ) ^ T.S.n k := by
        have hNle' : (T.S.N k : ℝ) ≤ ((T.S.n k * 2 ^ T.S.n k : ℕ) : ℝ) := by
          exact_mod_cast T.S.N_le k
        simpa [n] using hNle'
      have hdle : d ≤ n := by
        dsimp [d, densityScale]
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T.S.n k)).2 hNle
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnreal
      have hlogd : Real.log d ≤ Real.log n := Real.log_le_log hdpos hdle
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hremaining : ((G.r - j.val : ℕ) : ℝ) * Real.log 2 ≤
          2 * κ.A0 * Real.log n := by
        have hsub : ((G.r - j.val : ℕ) : ℝ) ≤ (G.r : ℝ) := by
          exact_mod_cast Nat.sub_le G.r j.val
        calc
          ((G.r - j.val : ℕ) : ℝ) * Real.log 2 ≤ (G.r : ℝ) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hsub hlog2
          _ ≤ 2 * κ.A0 * Real.log n := by simpa [n] using hL16.r_upper
      have hgain := hL16.gain_upper i
      have htotal : Real.log d + PT.tiling.gain i +
          ((G.r - j.val : ℕ) : ℝ) * Real.log 2 ≤
          (1 + κ.KB + 2 * κ.A0) * Real.log n := by
        calc
          _ ≤ Real.log n + κ.KB * Real.log n + 2 * κ.A0 * Real.log n := by
            linarith
          _ = (1 + κ.KB + 2 * κ.A0) * Real.log n := by ring
      have hscaled : (-κ.β) * ((1 + κ.KB + 2 * κ.A0) * Real.log n) ≤
          (-κ.β) * (Real.log d + PT.tiling.gain i +
            ((G.r - j.val : ℕ) : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonpos_left htotal (by linarith)
      have hcoef : κ.β * (1 + κ.KB + 2 * κ.A0) * Real.log n ≤
          0.02 * Real.log n :=
        mul_le_mul_of_nonneg_right hβsum hlogn
      have hpoworder : (-0.02) * Real.log n ≤
          (-κ.β) * ((1 + κ.KB + 2 * κ.A0) * Real.log n) := by
        nlinarith [hcoef]
      calc
        Real.rpow n (-0.02) = Real.exp (Real.log n * (-0.02)) :=
          Real.rpow_def_of_pos hnpos (-0.02)
        _ = Real.exp ((-0.02) * Real.log n) := by congr 1 <;> ring
        _ ≤ Real.exp ((-κ.β) * ((1 + κ.KB + 2 * κ.A0) * Real.log n)) :=
          Real.exp_le_exp.mpr hpoworder
        _ ≤ Real.exp ((-κ.β) * (Real.log d + PT.tiling.gain i +
              ((G.r - j.val : ℕ) : ℝ) * Real.log 2)) :=
          Real.exp_le_exp.mpr hscaled
        _ = lateError κ T k PT i (G.r - j.val) := by
          symm
          have hDexp : Real.rpow (densityScale T k) (-κ.β) =
              Real.exp (Real.log (densityScale T k) * (-κ.β)) :=
            Real.rpow_def_of_pos (by simpa [d] using hdpos) _
          have h2exp : Real.rpow 2 (-κ.β * ((G.r - j.val : ℕ) : ℝ)) =
              Real.exp (Real.log 2 * (-κ.β * ((G.r - j.val : ℕ) : ℝ))) :=
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
          rw [lateError, hDexp, h2exp]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    · exact hsumError G i
  · intro ε hε
    let c : ℝ := κ.β * κ.a / 10 ^ 6
    let C : ℝ := 1 + c⁻¹
    have ha : 0 < κ.a := by
      rw [hκ.a_eq]
      exact div_pos hκ.θ_rng.1 (by norm_num)
    have hc : 0 < c := by dsimp [c]; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    have hC1 : 1 ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
    have hscale_tendsto : Tendsto (fun k => densityScale T k) atTop atTop := by
      simpa [densityScale] using T.S.ratio_tendsto
    have hpow_tendsto : Tendsto
        (fun k => Real.rpow (densityScale T k) (-κ.β)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hβ).comp hscale_tendsto
    have hsmall : ∀ᶠ k in atTop,
        (Kβ * C) * Real.rpow (densityScale T k) (-κ.β) < ε := by
      have hlim := hpow_tendsto.const_mul (Kβ * C)
      have hmem : Set.Iio ε ∈ nhds ((Kβ * C) * 0) := by
        simpa using (Iio_mem_nhds (a := ε) (b := 0) hε)
      have hevent := hlim.eventually hmem
      simpa [mul_assoc] using hevent
    filter_upwards [hsmall] with k hk
    intro PT hPT hLow G F hL16 i
    have hheight :
        (max 1 (PT.tiling.P i).h : ℝ) *
          Real.exp (-κ.β * PT.tiling.gain i) ≤ C := by
      cases hm : PT.tiling.mode with
      | bounded =>
          have hh := (hPT.tiling_valid.bounded_data hm).2 i
          rw [hh.2.1]
          simpa [Tiling.gain, hm] using hC1
      | lowDirect =>
          obtain ⟨_, _, _, _, hh, _, _⟩ :=
            hPT.tiling_valid.direct_data (Or.inl hm) i
          rw [hh]
          have hg : 0 ≤ PT.tiling.gain i := by
            rw [Tiling.gain, hm]
            positivity
          have he : Real.exp (-κ.β * PT.tiling.gain i) ≤ 1 := by
            apply Real.exp_le_one_iff.2
            nlinarith
          simpa using le_trans he hC1
      | lowCluster =>
          have hx : 0 ≤ ((PT.tiling.P i).h : ℝ) := by positivity
          have hmax : (max 1 (PT.tiling.P i).h : ℝ) ≤
              1 + (PT.tiling.P i).h := by
            apply max_le <;> linarith
          have hg : PT.tiling.gain i =
              κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
            simp [Tiling.gain, hm]
          have hexp : Real.exp (-c * (PT.tiling.P i).h) ≤ 1 := by
            apply Real.exp_le_one_iff.2
            have hcx : 0 ≤ c * (PT.tiling.P i).h := mul_nonneg hc.le hx
            nlinarith [hcx]
          have hlinear : c * (PT.tiling.P i).h ≤
              Real.exp (c * (PT.tiling.P i).h) := by
            have := Real.add_one_le_exp (c * (PT.tiling.P i).h)
            linarith
          have hdiv : (PT.tiling.P i).h ≤
              Real.exp (c * (PT.tiling.P i).h) / c := by
            apply (le_div_iff₀ hc).2
            nlinarith [hlinear]
          have htail : (PT.tiling.P i).h *
              Real.exp (-c * (PT.tiling.P i).h) ≤ c⁻¹ := by
            calc
              (PT.tiling.P i).h * Real.exp (-c * (PT.tiling.P i).h) ≤
                  (Real.exp (c * (PT.tiling.P i).h) / c) *
                    Real.exp (-c * (PT.tiling.P i).h) :=
                mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)
              _ = c⁻¹ * (Real.exp (c * (PT.tiling.P i).h) *
                    Real.exp (-c * (PT.tiling.P i).h)) := by ring
              _ = c⁻¹ := by rw [← Real.exp_add]; simp
          have hsame : Real.exp (-κ.β * PT.tiling.gain i) =
              Real.exp (-c * (PT.tiling.P i).h) := by
            rw [hg]
            congr 1
            dsimp [c]
            ring
          rw [hsame]
          calc
            (max 1 (PT.tiling.P i).h : ℝ) *
                Real.exp (-c * (PT.tiling.P i).h) ≤
                (1 + (PT.tiling.P i).h) * Real.exp (-c * (PT.tiling.P i).h) :=
              mul_le_mul_of_nonneg_right hmax (Real.exp_nonneg _)
            _ = Real.exp (-c * (PT.tiling.P i).h) +
                  (PT.tiling.P i).h * Real.exp (-c * (PT.tiling.P i).h) := by ring
            _ ≤ 1 + c⁻¹ := add_le_add hexp htail
            _ = C := by rfl
      | highSmall => simp [Mode.isLow, hm] at hLow
      | highLarge => simp [Mode.isLow, hm] at hLow
      | highDirect => simp [Mode.isLow, hm] at hLow
    have hsum := hsumError G i
    have hscale_pos : 0 < densityScale T k := by
      unfold densityScale
      exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
    have hbase : 0 ≤ Kβ * Real.rpow (densityScale T k) (-κ.β) := by
      exact mul_nonneg hKβ.le (Real.rpow_pos_of_pos hscale_pos _).le
    calc
      (max 1 (PT.tiling.P i).h : ℝ) *
          (∑ j : Fin G.r, lateError κ T k PT i (G.r - j.val)) ≤
          (max 1 (PT.tiling.P i).h : ℝ) *
            (Kβ * Real.rpow (densityScale T k) (-κ.β) *
              Real.exp (-κ.β * PT.tiling.gain i)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (Kβ * Real.rpow (densityScale T k) (-κ.β)) *
            ((max 1 (PT.tiling.P i).h : ℝ) *
              Real.exp (-κ.β * PT.tiling.gain i)) := by ring
      _ ≤ (Kβ * Real.rpow (densityScale T k) (-κ.β)) * C :=
        mul_le_mul_of_nonneg_left hheight hbase
      _ = (Kβ * C) * Real.rpow (densityScale T k) (-κ.β) := by ring
      _ ≤ ε := le_of_lt hk

/-- P18.4a / D18.T, 18:89–113, 810–825. Choose profiles by separation on
baseline *label* marginals, and construct their exact reference kernels. This
choice occurs before terminal conditioning. -/
theorem P18_4a {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) (hD : D.Spec) :
    ∃ K : LateKernels D.encoding.base,
      (D.withKernels K).Spec ∧ TransitionData (D.withKernels K) ∧ MaskBalance (D.withKernels K) := by
  exact Lane_sol_s18_n1.balanced_kernels D hD

/-- L18.0b, eq. (25). Finite smallness replaces impossible fixed-index
vanishing; the cap is on probability atoms, with no factor N. -/
theorem L18_0b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D →
      SmallErrors κ T k PT D.geom (Real.log 2 / 1000) → CurrentListCapFacts D := by
  filter_upwards [] with k
  intro PT hPT D hD hT hsmall
  exact Lane_sol_s18_n1_caps.gated_current_cap D hD hsmall

/-- L18.1a, 18:171–194. Exponent .04 leaves slack below the derived .09. -/
theorem L18_1a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → CurrentListCapFacts D →
      ∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  obtain ⟨Kβ,hKβ,hSchedule,hErrors⟩ := L18_0a hκ T
  obtain ⟨K16,hQuant⟩ := low_mode_quantitative_inputs hκ T
  have hlog : 0 < Real.log 2 / 1000 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hSchedule,hErrors _ hlog,hQuant,
    Lane_sol_s18_n1_sketch.numerical_cutoffs hκ T K16] with k hSched hSmall hQ hNum
  intro PT hPT D hD hT hC j b h hg
  obtain ⟨Q,hgain⟩ := hQ PT hPT D.low_mode
  have hs := hSmall PT hPT D.low_mode D.geom D.fresh D.l16_valid
  have hlower := hSched PT hPT D.low_mode D.geom D.fresh D.l16_valid
  exact Lane_sol_s18_n1_sketch.row_estimate hκ D hT hs hC Q hNum.1 hNum.2.1 hNum.2.2
    (fun i j => (hlower i).1 j) j b h hg

/-- L18.1b, 18:195–223. Actual broad prefixes, same-side-data deletions,
and both single and pair versions of eq. (27); K27 is uniform. -/
theorem L18_1b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ K27 : ℝ, 0 < K27 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → SmallErrors κ T k PT D.geom (Real.log 2 / 1000) →
        BroadDeletionFacts D K27 := by
  obtain ⟨Kβ, _, hSchedule, hSmall⟩ := L18_0a hκ T
  let ε : ℝ := min (1 / 1000) (κ.α / 300000)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hκ.α_rng.1 (by norm_num))
  refine ⟨1100, by norm_num, ?_⟩
  filter_upwards [hSchedule, hSmall ε hε, T.S.n_tendsto.eventually_ge_atTop 1] with k hS hE hn
  intro PT hPT D _ _ _
  have hsmall := hE PT hPT D.low_mode D.geom D.fresh D.l16_valid
  have hlower := hS PT hPT D.low_mode D.geom D.fresh D.l16_valid
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hn0 : 0 < (T.S.n k : ℝ) := by linarith
  have hm : 0 < sketchLength T k := by
    unfold sketchLength
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn0 _)
  have hB : ∀ v j, bstar T k ≤ D.error v j ^ 4 := by
    intro v j
    have he := (hlower (D.geom.patchOf v)).1 j
    change Real.rpow (T.S.n k : ℝ) (-0.02) ≤ D.error v j at he
    calc
      bstar T k ≤ (Real.rpow (T.S.n k : ℝ) (-0.02)) ^ 4 := by
        unfold bstar
        rw [Real.rpow_eq_pow, ← Real.rpow_mul_natCast hn0.le (-0.02) 4]
        apply Real.rpow_le_rpow_of_exponent_le hnR
        norm_num
      _ ≤ D.error v j ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) he 4
  exact HypercubeRamsey.Lane_sol_s18_1b.broadDeletion_of_small D hn hm hB ε hε
    ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _) hsmall

/-- L18.1c, 18:225–226. Bounds an intersection, not a success-conditioned law. -/
theorem L18_1c {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 : ℝ) (hK : 0 < K27) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → BroadDeletionFacts D K27 →
      ∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr
        (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  obtain ⟨Kβ, hKβ, hSchedule, hSmall⟩ := L18_0a hκ T
  have hε : 0 < Real.log 2 / 1000 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hn : ∀ᶠ k in atTop, 0 < (T.S.n k : ℝ) := by
    filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1] with k hk
    exact_mod_cast (show 0 < T.S.n k by omega)
  filter_upwards [hSchedule, hSmall (Real.log 2 / 1000) hε,
    Lane_sol_s18_1c.numerical_cutoff T, hn] with k hSchedule hSmall hCutoff hn
  intro PT hPT D hD hT hB j b h hg
  have hS := hSchedule PT hPT D.low_mode D.geom D.fresh D.l16_valid
  have hE := hSmall PT hPT D.low_mode D.geom D.fresh D.l16_valid
  exact (Lane_sol_s18_1c.trueHit_tail D hT K27 hB hE hn
    (fun i => (hS i).1) j b h hg).trans hCutoff

theorem L18_1 {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ K27 : ℝ, 0 < K27 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → SmallErrors κ T k PT D.geom (Real.log 2 / 1000) →
        LocalTransitionFacts D K27 := by
  obtain ⟨K, hK, hb⟩ := L18_1b hκ T
  have ha := L18_1a hκ T
  have hc := L18_1c hκ T K hK
  have hcap := L18_0b hκ T
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcap, ha, hb, hc] with k hcap ha hb hc
  intro PT hPT D hD hR hsmall
  have hC := hcap PT hPT D hD hR hsmall
  have hB := hb PT hPT D hD hR hsmall
  exact ⟨hC, hB, ha PT hPT D hD hR hC, hc PT hPT D hD hR hB⟩

/-- L18.2b/c/f, 18:290–415. Actual predecessor/erased-word/block geometry. -/
theorem L18_2b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D, TransferGeometry X := by
  have hcount := Lane_q_s18_n2.critical_count_field hκ T
  have hnReal : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnReal
  have hlogLarge : ∀ᶠ k in atTop, 4 ≤ Real.log (T.S.n k : ℝ) :=
    hlogT.eventually_ge_atTop 4
  have hA0 : 0 ≤ κ.A0 := by
    have hR : 0 ≤ (κ.R : ℝ) := Nat.cast_nonneg _
    exact le_trans (by positivity) hκ.A0_big
  have hlogMargin : ∀ᶠ k in atTop, 8 * κ.A0 + 10 ≤ Real.log (T.S.n k : ℝ) :=
    hlogT.eventually_ge_atTop (8 * κ.A0 + 10)
  have hmargin : ∀ᶠ k in atTop, (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3 := by
    filter_upwards [hlogLarge] with k hk
    have hpow : (4 : ℝ) ^ 3 ≤ Real.log (T.S.n k : ℝ) ^ 3 := by gcongr
    norm_num at hpow
    linarith
  filter_upwards [hcount, hmargin, hlogMargin] with k hcount hmargin hlogMargin
  intro PT hPT D hD X
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hrBound : (D.geom.r : ℝ) ≤ 4 * κ.A0 * Real.log (T.S.n k : ℝ) := by
    have hrnonneg : 0 ≤ (D.geom.r : ℝ) := Nat.cast_nonneg _
    nlinarith [D.l16_valid.r_upper]
  have hcoef : 8 * κ.A0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hlogLargeEnough : 2 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hmarginReal :
      2 * (D.geom.r : ℝ) + 4 ≤ Real.log (T.S.n k : ℝ) ^ 3 := by
    have hprod : 8 * κ.A0 * Real.log (T.S.n k : ℝ) ≤
        Real.log (T.S.n k : ℝ) ^ 2 := by
      calc
        8 * κ.A0 * Real.log (T.S.n k : ℝ) ≤
            Real.log (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (by linarith)
        _ = Real.log (T.S.n k : ℝ) ^ 2 := by ring
    have hfour : (4 : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 2 := by nlinarith
    have hsum : 8 * κ.A0 * Real.log (T.S.n k : ℝ) + 4 ≤
        2 * Real.log (T.S.n k : ℝ) ^ 2 := by linarith
    have hcube : 2 * Real.log (T.S.n k : ℝ) ^ 2 ≤
        Real.log (T.S.n k : ℝ) ^ 3 := by nlinarith
    have hr : 2 * (D.geom.r : ℝ) + 4 ≤
        8 * κ.A0 * Real.log (T.S.n k : ℝ) + 4 := by nlinarith [hrBound]
    exact hr.trans (hsum.trans hcube)
  have hmarginNat : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3 := by
    exact_mod_cast hmarginReal
  refine {
    critical_count := hcount PT hPT D hD X
    distinct_cells := ?_
    predecessor_radius := ?_
    erased_internal := Lane_q_s18_n2.erased_internal_field D X
    block_size := ?_
    one_block := by
      intro w hw
      exact Lane_q_s18_n2.one_block_field (D := D) (X := X) hmarginNat w hw }
  · intro a ha b hb hcell
    exact Lane_q_s18_n2.bulkCoord_eq_of_cellEq (D := D) (X := X) hmargin
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hcell
  · intro b hb
    exact Lane_q_s18_n2.predecessor_radius (D := D) (X := X) b hb
  · intro a
    exact Lane_q_s18_n2.block_size (D := D) (X := X) a

/-- L18.2d/e/g, 18:338–453. Perform path deletion and integrate erased
sketches before fixing independent seeds; construct a total local protocol. -/
theorem L18_2g {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 : ℝ) (hK : 0 < K27) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → LocalTransitionFacts D K27 →
      ∀ X : CriticalTransferData D, TransferGeometry X → Nonempty (TransferProtocol X) := by
  sorry

/-- L18.2h, 18:455–470. Complete reply-range cardinality, not an event tail. -/
theorem L18_2h {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
      ∀ P : TransferProtocol X, ReplyRangeBound P := by
  classical
  have hnReal : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnReal
  have hlogEventually : ∀ᶠ k in atTop, 2 ≤ Real.log (T.S.n k : ℝ) :=
    hlogT.eventually_ge_atTop 2
  have hratioN : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) ^ 28 / Real.rpow (n : ℝ) (3 / 20 : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (((isLittleO_log_rpow_rpow_atTop (28 : ℝ)
        (by norm_num : (0 : ℝ) < 3 / 20)).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop)
  have hsmallEventually : ∀ᶠ k in atTop,
      Real.log (T.S.n k : ℝ) ^ 28 /
        Real.rpow (T.S.n k : ℝ) (3 / 20 : ℝ) < 1 / 1000 :=
    hratioN.comp T.S.n_tendsto |>.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 1000))
  have hNEventually : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hlogEventually, hsmallEventually, hNEventually] with k hL hsmall hN
  intro PT hPT D hD X P
  have hn : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hN
  have hlogCube : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3 := by
    have hcube : (2 : ℝ) ^ 3 ≤ Real.log (T.S.n k : ℝ) ^ 3 := by gcongr
    norm_num at hcube
    linarith
  have hnum := Lane_q_s18_n2.protocol_code_exponential_bound P hn hL hsmall
  intro seed a fixed
  have hcount := Lane_q_s18_n2.replyRange_card_le_codeCard P seed a fixed hlogCube
  have hcountR :
      ((((Finset.univ : Finset (CriticalTransferData.Raw X)).filter
        (fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C)).image
        (fun s => P.replies seed s P.steps)).card : ℝ) ≤
        ((⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1 : ℕ) : ℝ) *
          ((Fintype.card (Fin P.steps × P.Reply) + 1 : ℕ) : ℝ) ^
            ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by
    exact_mod_cast hcount
  have hcode :
      ((⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1 : ℕ) : ℝ) *
          ((Fintype.card (Fin P.steps × P.Reply) + 1 : ℕ) : ℝ) ^
            ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ ≤
        Real.exp (Real.rpow (T.S.n k : ℝ) (2 / 5 : ℝ)) := by
    simpa using hnum
  change (((Finset.univ : Finset X.Raw).filter
      (fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C)).image
      (fun s => P.replies seed s P.steps)).card ≤
        Real.exp (Real.rpow (T.S.n k : ℝ) 0.4)
  exact hcountR.trans (by simpa only [show (2 / 5 : ℝ) = 0.4 by norm_num] using hcode)

/-- L18.2a/i and 18:472–490, 630–645. Positive whole-cell survival and
both surviving-witness second moments. -/
theorem L18_2i {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        TransferGeometry X → SurvivalFacts X := by
  classical
  filter_upwards [Lane_q_s18_n3.critical_cell_hit_bound_eventually hκ T,
    Lane_sol_fix_surv.survival_moments_eventually hκ T] with k hcell hmoments
  intro PT hPT D hD X hgeom
  exact ⟨hcell PT hPT D hD X hgeom, hmoments PT hPT D hD X hgeom⟩

/-- L18.2j, 18:500–524. Cylinder identity for the actual adaptive recurrence. -/
theorem L18_2j {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) : CylinderFacts P := by
  exact Lane_q_s18_n3.protocol_cylinder_facts P

/-- L18.2k/l, 18:526–615. The independent-witness likelihood process and
stopped moment/exception estimates are explicit. Choose cstop before stages. -/
theorem L18_2l {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∃ cstop : ℝ, 0 < cstop ∧ cstop < κ.xs / 4 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → ∀ X : CriticalTransferData D, TransferGeometry X → SurvivalFacts X →
        ∀ P : TransferProtocol X, ReplyRangeBound P → CylinderFacts P → StopFacts P cstop := by
  refine ⟨κ.xs / 8, ?_, ?_, ?_⟩
  · exact div_pos hκ.xs_rng.1 (by norm_num)
  · nlinarith [hκ.xs_rng.1]
  · sorry

/-- L18.2m, 18:617–628. An integrated tilted deviation estimate, not the
final unconditioned prefix-failure estimate. -/
theorem L18_2m {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) (cstop : ℝ) (hc : 0 < cstop) (hcx : cstop < κ.xs / 4) :
    ∃ ctilt : ℝ, 0 < ctilt ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → ∀ X : CriticalTransferData D, ∀ P : TransferProtocol X,
          StopFacts P cstop → TiltedDeviationBound P ctilt := by
  refine ⟨cstop, hc, ?_⟩
  sorry

/-- 18:630–657. Undo survival, use its second moment and restore deletion
costs. The exponent is chosen after the tilted bound, uniformly in X. -/
theorem L18_2_finish {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (ctilt : ℝ) (hc : 0 < ctilt) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → SmallErrors κ T k PT D.geom (Real.log 2 / 1000) →
        ∀ X : CriticalTransferData D, TransferGeometry X → SurvivalFacts X →
          ∀ P : TransferProtocol X, TiltedDeviationBound P ctilt →
            X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
              Real.exp (-Real.rpow (T.S.n k : ℝ) c1) := by
  exact Lane_q_s18_n3.finish_from_survival_tilt hκ T ctilt hc

theorem L18_2 {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) (K27 : ℝ) (hK : 0 < K27) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → LocalTransitionFacts D K27 →
        SmallErrors κ T k PT D.geom (Real.log 2 / 1000) → TransferBound D c1 := by
  obtain ⟨cs, hcs, hcsx, hl⟩ := L18_2l hκ T hDisc
  obtain ⟨ct, hct, hm⟩ := L18_2m hκ T hDisc cs hcs hcsx
  obtain ⟨c1, hc1, hfinish⟩ := L18_2_finish hκ T ct hct
  refine ⟨c1, hc1, ?_⟩
  filter_upwards [L18_2b hκ T, L18_2g hκ T K27 hK, L18_2h hκ T, L18_2i hκ T,
    hl, hm, hfinish] with k hb hg hh hi hl hm hfinish
  intro PT hPT D hD hR hLocal hsmall X
  have geom := hb PT hPT D hD X
  obtain ⟨P⟩ := hg PT hPT D hD hR hLocal X geom
  have range := hh PT hPT D hD X P
  have surv := hi PT hPT D hD X geom
  have cyl := L18_2j P
  have stopped := hl PT hPT D hD X geom surv P range cyl
  have tilt := hm PT hPT D hD X P stopped
  exact hfinish PT hPT D hD hsmall X geom surv P tilt

/-- P18.3a–d, 18:678–751. Per-requirement bounds under every global slot
pin; replay is a total function with explicit agreement. `D.l16_valid.slot_eq`
controls the slot inputs read by each touched cell, including under the pin. -/
theorem P18_3a {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c1 δ : ℝ) (hK : 0 < K27) (hc1 : 0 < c1)
    (hδ : 0 < δ) (hδsmall : δ < min 0.04 c1) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → LocalTransitionFacts D K27 →
        TransferBound D c1 → ReplayFacts D → TerminalRiskBound D δ := by
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2,
    Lane_sol_s18_n4.finalListTapeBound hκ T,
    Lane_sol_s18_n4.validPrefixPinnedBound hκ T K27 c1 δ hK hc1
      (hδsmall.trans_le (min_le_right _ _))] with k hk hfinal hprefix
  intro PT hPT D hD hTransition hLocal hTransfer hReplay
  intro pin f
  cases f with
  | inl pair =>
      cases pair with
      | inl C =>
          have hevent : terminalFailure D δ (.inl (.inl C)) = D.upstreamBad (.inl C) := by
            funext x
            rfl
          rw [hevent]
          exact Lane_q_s18_n4.upstreamBadPinnedBound D hD pin (.inl C) (by omega)
      | inr v =>
          have hevent : terminalFailure D δ (.inl (.inr v)) = D.upstreamBad (.inr v) := by
            funext x
            simp [terminalFailure, LateData.poolListOK, LateData.freshConfigLaw,
              LateData.upstreamBad]
          rw [hevent]
          exact Lane_q_s18_n4.upstreamBadPinnedBound D hD pin (.inr v) (by omega)
  | inr pair =>
      cases pair with
      | inl v =>
          exact Lane_sol_s18_n4.finalListPinnedBound D v (by omega)
            (hfinal D hD (Lane_sol_s18_n4.eventDegreeBound D hD hk) v) pin
      | inr F =>
          by_cases hkind : F.1.val = 1
          · by_cases hvalid : D.prefixValid F.2
            · exact hprefix D hD hTransition hLocal hTransfer hReplay F hkind hvalid pin
            · exact Lane_sol_s18_n4.invalidPrefixTerminalPinnedBound D δ F hkind hvalid pin
          · exact Lane_sol_s18_n4.nonPrefixTerminalPinnedBound D K27 δ hLocal (by omega)
              (hδsmall.le.trans (min_le_left _ _)) F hkind pin

/-- P18.3c, 18:715–737. Forced replay advances overlapping scopes once. -/
theorem P18_3c {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) : ReplayFacts D :=
  Lane_q_s18_n4.replay_facts D

/-- P18.3e, 18:752–788. Leaves of the actual bad requirements, exact
slot/image/tape dependency, conditional pushforward and touching charges.
The prescribed `D.l16_valid.slot_eq` bounds leaf slot domains as well as cells. -/
theorem P18_3e {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → TerminalRiskBound D δ →
        Nonempty (LeafCoupling D δ) := by
  have hnR := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  filter_upwards [Lane_sol_s18_n4.terminalScaleEventually κ T,
    hnR.eventually_ge_atTop κ.Kcell] with k hscale hK
  intro PT hPT D hD hR hRisk
  obtain ⟨hn8, hTs, hr⟩ := hscale D
  have hn : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  suffices hinputs : Nonempty (Lane_sol_s18_3e.CanonicalLeafInputs D δ) by
    obtain ⟨X⟩ := hinputs
    exact ⟨Lane_sol_s18_3e.leafCouplingOfInputs D δ hRisk X
      (Lane_sol_s18_3e.late_probability_local D hD hR) hn⟩
  exact Lane_sol_s18_3e.canonicalLeafInputs_of_bounds hκ D hD hR δ
    (by omega) (by exact_mod_cast hTs) (by exact_mod_cast hr) hK

/-- P18.3f, 18:773–798. Positive *canonical* terminal event and a uniform
vanishing cost for every stated local nonnegative test. The slot-count
contract in `D.l16_valid` is retained for the local pool comparison. -/
theorem P18_3f {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → TerminalRiskBound D δ → LeafCoupling D δ →
          Nonempty (TerminalCertificate D δ (ε k)) := by
  refine ⟨fun k => (T.S.n k : ℝ)⁻¹, fun k => inv_nonneg.mpr (Nat.cast_nonneg _),
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp T.S.n_tendsto, ?_⟩
  filter_upwards [Lane_sol_s18_3f.terminalCertificateEventually_of_nonneighbor hκ T δ]
    with k hcertificate
  intro PT hPT D hD hRisk leaves
  apply hcertificate PT hPT D hD hRisk leaves
  intro seed hseed
  -- The remaining obligation is the coordinate-fiber nonneighbor inequality.
  sorry

theorem P18_3 {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c1 δ : ℝ) (hK : 0 < K27) (hc1 : 0 < c1)
    (hδ : 0 < δ) (hδsmall : δ < min 0.04 c1) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → TransitionData D → LocalTransitionFacts D K27 →
          TransferBound D c1 → Nonempty (TerminalCertificate D δ (ε k)) := by
  obtain ⟨ε, hε, hlim, hf⟩ := P18_3f hκ T δ hδ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [P18_3a hκ T K27 c1 δ hK hc1 hδ hδsmall, P18_3e hκ T δ hδ, hf] with k ha he hf
  intro PT hPT D hD hR hLocal hTransfer
  have risk := ha PT hPT D hD hR hLocal hTransfer (P18_3c D)
  obtain ⟨leaves⟩ := he PT hPT D hD hR risk
  exact hf PT hPT D hD risk leaves

/-- P18.4b, 18:827–861. The entering predicate is the exact incoming-risk
and column condition. Current bads and future alarms are defined events. -/
theorem P18_4b {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c1 δ : ℝ) (hK : 0 < K27) (hc1 : 0 < c1)
    (hδ : 0 < δ) (hδsmall : δ < min 0.04 c1) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → LocalTransitionFacts D K27 →
        TransferBound D c1 → ∀ ε, TerminalCertificate D δ ε →
          Nonempty (ClassSamplerData D δ) := by
  filter_upwards [Lane_sol_s18_4b.classSamplerEventually hκ T δ hδ] with k hsampler
  intro PT hPT D hD hTransition hLocal hTransfer ε C
  exact hsampler D hD hTransition

/-- P18.4c/d, 18:863–909. Bound stops at reached histories and establish
all actual completion conclusions; no existential full=True shortcut.
The reached-column moment comparison retains `D.l16_valid.slot_eq`. -/
theorem P18_4c {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c1 δ : ℝ) (hK : 0 < K27) (hc1 : 0 < c1)
    (hδ : 0 < δ) (hδsmall : δ < min 0.04 c1)
    (εterm : ℕ → ℝ) (hterm : Tendsto εterm atTop (nhds 0)) :
    ∃ εrun : ℕ → ℝ, (∀ k, 0 ≤ εrun k) ∧ Tendsto εrun atTop (nhds 0) ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → TransitionData D → MaskBalance D → LocalTransitionFacts D K27 →
          TransferBound D c1 → ∀ C : TerminalCertificate D δ (εterm k),
            ∀ A : ClassSamplerData D δ, FullRunProbability D C A (εrun k) := by
  refine ⟨Lane_sol_s18_n5.runError T, Lane_sol_s18_n5.runError_nonneg T,
    Lane_sol_s18_n5.runError_tendsto T, ?_⟩
  have hθ : 0 < κ.θ0 := by rw [hκ.clock.2.1]; norm_num
  have hmoments : ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → MaskBalance D → LocalTransitionFacts D K27 →
        TransferBound D c1 → ∀ C : TerminalCertificate D δ (εterm k),
          ∀ A : ClassSamplerData D δ, ∀ j : Fin D.geom.r, ∀ y : Fin (T.S.N k),
            (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
              (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
                (fun z => if Lane_sol_s18_n5.reached D δ j z.2 then
                  D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ T.S.n k else 0) ≤
                    (2 : ℝ) ^ D.geom.r *
                      (12 * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) ^ T.S.n k := by
    filter_upwards [Lane_sol_s18_n5.actual_column_moment_eventually hκ T εterm hterm] with k hk
    intro PT hPT D hD hT hBalance _hLocal _hTransfer C A j y
    exact hk D hD hT hBalance δ C A j y
  filter_upwards [hmoments, T.S.n_tendsto.eventually_ge_atTop 1,
    T.S.ratio_tendsto.eventually_ge_atTop (576 * 12 / κ.θ0)] with k hk hn hscale
  intro PT hPT D hD hT hBalance hLocal hTransfer C A
  exact Lane_sol_s18_n5.fullRunProbability_of_column_moments D hD hT C A hLocal.2.1
    hθ (by norm_num) hn hscale (hk PT hPT D hD hT hBalance hLocal hTransfer C A)

theorem P18_4 {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c1 δ : ℝ) (hK : 0 < K27) (hc1 : 0 < c1)
    (hδ : 0 < δ) (hδsmall : δ < min 0.04 c1)
    (εterm : ℕ → ℝ) (hterm : Tendsto εterm atTop (nhds 0)) :
    ∃ εrun : ℕ → ℝ, (∀ k, 0 ≤ εrun k) ∧ Tendsto εrun atTop (nhds 0) ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → TransitionData D → MaskBalance D → LocalTransitionFacts D K27 →
          TransferBound D c1 → ∀ C : TerminalCertificate D δ (εterm k),
            Nonempty (CompletionCertificate D C (εrun k)) := by
  obtain ⟨εrun, hε, hlim, hc⟩ := P18_4c hκ T K27 c1 δ hK hc1 hδ hδsmall εterm hterm
  refine ⟨εrun, hε, hlim, ?_⟩
  filter_upwards [P18_4b hκ T K27 c1 δ hK hc1 hδ hδsmall, hc] with k hb hc
  intro PT hPT D hD hR hBalance hLocal hTransfer C
  obtain ⟨A⟩ := hb PT hPT D hD hR hLocal hTransfer (εterm k) C
  exact ⟨⟨A, hc PT hPT D hD hR hBalance hLocal hTransfer C A⟩⟩

/-- D18.I, 18:962–985. The caller fixes a palette and tested tuple. -/
def D18_I {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) (p : PaletteIndex D)
    (S : Finset (Pos T k)) (hS : S ⊆ D.paletteRows p) (hn : S.card ≤ T.S.n k) : InitialPairData D :=
  ⟨p, S, hS, hn⟩

/-- P18.5a, 18:914–945. Full-run pair-law support, all-neighbor hits,
palette counts and computed overlap statistics. -/
theorem P18_5a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → PairInitialFacts D δ K := by
  have hP : 0 < κ.P := by
    rcases hκ.P_big with ⟨_, hP⟩
    omega
  have hR : 0 < κ.R := by
    rw [hκ.R_eq]
    positivity
  have hR' : 0 < (κ.R : ℝ) := by exact_mod_cast hR
  have hK : 0 < κ.KB := by
    have hKB := hκ.KB_big
    nlinarith
  refine ⟨κ.KB, hK, ?_⟩
  have hn : ∀ᶠ k in atTop, 2 ≤ T.S.n k := T.S.n_tendsto.eventually_ge_atTop 2
  obtain ⟨Kβ, hKβ, hSchedule, hsmall⟩ := L18_0a hκ T
  obtain ⟨K16, hquant⟩ := low_mode_quantitative_inputs hκ T
  have hlog : 0 < Real.log 2 / 1000 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hscale : ∀ᶠ k in atTop, 8 * κ.KB < densityScale T k :=
    T.S.ratio_tendsto.eventually_gt_atTop (8 * κ.KB)
  have hconflictScale : ∀ᶠ k in atTop, 48 * κ.KB * K16 * κ.Kbd ≤ densityScale T k :=
    T.S.ratio_tendsto.eventually_ge_atTop (48 * κ.KB * K16 * κ.Kbd)
  filter_upwards [hn, hsmall (Real.log 2 / 1000) hlog,
    hsmall (1 / 1000) (by norm_num), L18_0b hκ T, hscale, hquant, hconflictScale]
    with k hk hsmall₀ hsmall₁ hcap hkScale hquant hkConflictScale
  intro PT hPT D hD hTransition
  obtain ⟨Q, _hGain⟩ := hquant PT hPT D.low_mode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa [Lane_q_s18_n5.paletteRows_eq_counted, LateData.paletteScale, densityScale,
      div_eq_mul_inv, mul_assoc]
      using (hD.palette_counts p.1 p.2).1
  · intro p
    simpa [Lane_q_s18_n5.paletteRows_eq_counted, LateData.paletteScale, densityScale]
      using (hD.palette_counts p.1 p.2).2
  · intro v
    exact Lane_q_s18_n5.geometricAdj_degree_bound hκ D hk v
  · intro S
    exact Lane_q_s18_n5.nonisolates_le_twice_rank D S
  · intro x h hfull v heven
    have hC := hcap PT hPT D hD hTransition
      (hsmall₀ PT hPT D.low_mode D.geom D.fresh D.l16_valid)
    have hmass : 0 < ∑ y, Lane_sol_s18_n5.finalWeight D h v y :=
      Lane_sol_s18_n5.full_finalWeight_pos D δ x h hfull v heven
        (fun j hj => Lane_sol_s18_n5.currentCap_lt_one hκ D hC hkScale δ x h hfull v j hj)
        (fun j => lt_of_le_of_lt (Lane_sol_s18_n5.smallErrors_error_le D (1 / 1000)
          (hsmall₁ PT hPT D.low_mode D.geom D.fresh D.l16_valid) v j) (by norm_num))
    have hZ : (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
          if D.nonconflict v p.1 p.2 then
            (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0 := by
      exact Lane_sol_s18_n5.final_nonconflict_mass hκ D hD Q hC hkConflictScale δ x h hfull
        v heven hmass (fun j => le_trans (Lane_sol_s18_n5.smallErrors_error_le D (1 / 1000)
          (hsmall₁ PT hPT D.low_mode D.geom D.fresh D.l16_valid) v j) (by norm_num))
    exact ⟨hZ, Lane_sol_s18_n5.pairLaw_support hκ D h v
      (hfull.2.2.2.2.1 v heven) hmass hZ⟩

/-- P18.5b, 18:993–1025. A nonnegative integral comparison retaining the
reach and side-data gates, with uniform constants before all stage indices. -/
theorem P18_5b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 δ : ℝ)
    (hK : 0 < K27) (hδ : 0 < δ) :
    ∃ KL Cp Cs : ℝ, 1 ≤ KL ∧ 0 < Cp ∧ 0 < Cs ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → LocalTransitionFacts D K27 →
        ∀ εterm εrun, ∀ C : TerminalCertificate D δ εterm, ∀ H : CompletionCertificate D C εrun,
          ∀ A : InitialPairData D, ∀ assignment,
            endpointProbability D C H A assignment ≤
              Real.exp (Cs * D.geom.r + Cp * A.rows.card * D.rank A.rows) * KL ^ A.rows.card *
                A.termTest C assignment := by
  have hKL : 1 ≤ 32 * Real.exp (24 + K27) := by
    have he : 1 ≤ Real.exp (24 + K27) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (24 + K27) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  refine ⟨32 * Real.exp (24 + K27), 8, 1, hKL, by norm_num, by norm_num, ?_⟩
  obtain ⟨Kpair, hKpair, hPairs⟩ := P18_5a hκ T δ hδ
  obtain ⟨Kβ, hKβ, hSchedule, hsmall⟩ := L18_0a hκ T
  have hscale : ∀ᶠ k in atTop, 8 * κ.KB < densityScale T k :=
    T.S.ratio_tendsto.eventually_gt_atTop (8 * κ.KB)
  filter_upwards [hPairs, hsmall (1 / 1000) (by norm_num), hscale,
    Lane_sol_s18_5b.eventually_query_size T] with k hPair hSmall hScale hQuery
  intro PT hPT D hD hTransition hLocal εterm εrun C H A assignment
  have hs := hSmall PT hPT D.low_mode D.geom D.fresh D.l16_valid
  have hs₁ : SmallErrors κ T k PT D.geom 1 :=
    fun i => (hs i).trans (by norm_num)
  have herr (v : Pos T k) (j : Fin D.geom.r) : D.error v j ≤ 1 / 1000 :=
    Lane_sol_s18_n5.smallErrors_error_le D (1 / 1000) hs v j
  have hPairFacts := hPair PT hPT D hD hTransition
  have hm (x : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
      (hf : D.full δ x h) (v : Pos T k) (hv : v ∈ A.rows) :
      0 < ∑ y, Lane_sol_s18_n5.finalWeight D h v y := by
    have heven : IsEvenRole v := (Finset.mem_filter.mp (A.rows_subset hv)).2.1
    exact Lane_sol_s18_n5.full_finalWeight_pos D δ x h hf v heven
      (fun j hj => Lane_sol_s18_n5.currentCap_lt_one hκ D hLocal.1 hScale δ x h hf v j hj)
      (fun j => lt_of_le_of_lt (herr v j) (by norm_num))
  have hZ (x : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
      (hf : D.full δ x h) (v : Pos T k) (hv : v ∈ A.rows) :
      (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
        if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0 :=
    (hPairFacts.2.2.2.2 x h hf v (Finset.mem_filter.mp (A.rows_subset hv)).2.1).1
  have hcard : (A.rows.card : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast A.small
  simpa only [one_mul] using Lane_sol_s18_5b.endpoint_comparison D hTransition hK.le hLocal.2.1 hs₁ C H A assignment
    (hcard.trans hQuery) (fun v hv j => (herr v j).trans (by norm_num)) hm hZ

/-- P18.5c, 18:1027–1056. Terminal → fixed-pool resampling → iid pools;
the stronger pool gate remains through the fixed-pool comparison. The last
comparison uses the prescribed `D.l16_valid.slot_eq` and the consulted tuple
scope; it is not an unrestricted comparison on arbitrary numbers of slots. -/
theorem P18_5c {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ δ εterm, ∀ C : TerminalCertificate D δ εterm,
        ∀ A : InitialPairData D, ∀ assignment,
          A.termTest C assignment ≤ (1 + εterm) * A.permTest assignment ∧
          A.permTest assignment ≤ 2 * A.permFreshTest assignment ∧
          A.permFreshTest assignment ≤ 2 * A.iidFreshTest assignment := by
  filter_upwards [Lane_sol_s18_n5.eventually_scope_size T,
    Lane_sol_s18_n5.perm_resampling_comparison hκ T,
    Lane_sol_s18_n5.perm_iid_fresh_comparison hκ T] with k hscope hresampling hiid
  intro PT hPT D hD δ εterm C A assignment
  refine ⟨Lane_sol_s18_n5.terminal_comparison D hD A C assignment (hscope D A),
    hresampling PT hPT D hD A assignment, ?_⟩
  exact hiid PT hPT D hD A assignment

/-- P18.5d, 18:1058–1090. Bounds the explicitly defined isolate kernel,
using equation (24) with `Krow` fixed before the eventual index. -/
theorem P18_5d {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (Krow : ℝ) (hKrow : 0 < Krow) :
    ∃ KI : ℝ, 1 ≤ KI ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → PaletteRowInput D Krow → IsolateKernelFacts D KI := by
  exact Lane_sol_s18_5d.isolate_facts hκ T Krow hKrow

/-- P18.5e, 18:1092–1124. Remove state gates before bin comparisons and
retain geometrically fixed bulk pair-hit queries. -/
theorem P18_5e {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ CQ : ℝ, 0 < CQ ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ A : InitialPairData D, ∃ Q : PairQueries D A,
        ∀ assignment, (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
          A.iidFreshTest assignment ≤
            Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
              CQ * A.rows.card * D.rank A.rows) * (4 : ℝ) ^ Q.count * Q.integral assignment *
                (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                ∏ v ∈ A.rows \ D.nonisolates A.rows,
                  isolatedWeight D v (assignment v).1 (assignment v).2 := by
  exact HypercubeRamsey.Lane_sol_s18_5e.pair_query_reduction hκ T

/-- P18.5f/g, 18:1126–1212. Calibrated label and group-bin comparisons,
reverse repeat summation and iid containment yield the actual query integral.
This includes k=0, for which the right side is one. -/
theorem P18_5f {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ A : InitialPairData D, ∀ Q : PairQueries D A,
        PairQueryBound D A Q := by
  have hξ : κ.ξ ≤ 1 / 1600 := by
    have hu : 0 ≤ (κ.u : ℝ) := by positivity
    have hexp : -(10 * (κ.u : ℝ) + 100) ≤ -4 := by nlinarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hrpow4 : Real.rpow (2 : ℝ) (-4 : ℝ) = 1 / 16 := by
      norm_num [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hα : κ.α ≤ 1 / 100 := by
      calc
        κ.α ≤ (0.01 : ℝ) := hκ.α_rng.2.le
        _ = 1 / 100 := by norm_num
    have hξbound : κ.ξ < 1 / 1600 := by
      calc
        κ.ξ < κ.α * Real.rpow (2 : ℝ) (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
        _ ≤ (1 / 100) * Real.rpow (2 : ℝ) (-(10 * (κ.u : ℝ) + 100)) :=
          mul_le_mul_of_nonneg_right hα (Real.rpow_nonneg (by norm_num) _)
        _ ≤ (1 / 100) * Real.rpow (2 : ℝ) (-4 : ℝ) :=
          mul_le_mul_of_nonneg_left hrpow (by norm_num)
        _ = 1 / 1600 := by rw [hrpow4]; norm_num
    exact hξbound.le
  have hNums := HypercubeRamsey.Lane_q_s18_n6.eventually_endpoint_numeric_bounds hκ T
  filter_upwards [hNums] with k hNums
  rcases hNums with ⟨hkB, hkD, hkL, hkErr, hklog, hkN⟩
  intro PT hPT D hD A Q
  have hOwn : ∀ i x, x ∈ PT.envelope i →
      deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤ 1 / 2 + 1 / 10000 := by
    intro i x hx
    have hdeg := hPT.envelope_degree i x hx
    cases hm : PT.tiling.mode with
    | bounded =>
      simp [OwnDegOK, hm] at hdeg
      have habs := abs_le.mp hdeg
      linarith [hkB]
    | lowDirect =>
      simp [OwnDegOK, hm] at hdeg
      norm_num at hdeg
      have hscale := hPT.tiling_valid.direct_scale_bound (Or.inl hm) i
      have hnpos : 0 < (T.S.n k : ℝ) := by linarith [hkN]
      have hG : ((PT.tiling.P i).g : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := hscale
      have hdiv : (T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ) =
          (T.S.n k : ℝ) ^ (κ.ι / 2 - 1) := by
        have h := Real.rpow_sub hnpos (κ.ι / 2) 1
        rw [Real.rpow_one] at h
        exact h.symm
      have hown : deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
          1 / 2 + 4 * ((PT.tiling.P i).g : ℝ) / (T.S.n k : ℝ) := hdeg.2
      have hgdiv : ((PT.tiling.P i).g : ℝ) / (T.S.n k : ℝ) ≤
          (T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ) :=
        div_le_div_of_nonneg_right hG hnpos.le
      have hG4 : 4 * ((PT.tiling.P i).g : ℝ) ≤ 4 * (T.S.n k : ℝ) ^ (κ.ι / 2) :=
        mul_le_mul_of_nonneg_left hG (by norm_num)
      have herrDirect : 4 * ((PT.tiling.P i).g : ℝ) / (T.S.n k : ℝ) ≤
          4 * (T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ) :=
        div_le_div_of_nonneg_right hG4 hnpos.le
      calc
        deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
            1 / 2 + 4 * ((PT.tiling.P i).g : ℝ) / (T.S.n k : ℝ) := hown
        _ ≤ 1 / 2 + 4 * (T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ) :=
            by linarith [herrDirect]
        _ = 1 / 2 + 4 * (T.S.n k : ℝ) ^ (κ.ι / 2 - 1) := by
              have hcancel : 4 * (T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ) =
                  4 * ((T.S.n k : ℝ) ^ (κ.ι / 2) / (T.S.n k : ℝ)) := by
                field_simp [ne_of_gt hnpos]
              rw [hcancel, hdiv]
        _ ≤ 1 / 2 + 1 / 10000 := by linarith [hkD]
    | lowCluster =>
      simp [OwnDegOK, hm] at hdeg
      norm_num at hdeg
      norm_num at hdeg
      rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
        ⟨_hthreshold, _hg, _hmass, _hsmall, _hlarge, _hcodegree, _hh, _hlo, _hup,
          hlow, _hsmallMode, _hlargeMode⟩
      have hqNat : 1 ≤ (PT.tiling.P i).q := by
        rw [(hPT.tiling_valid.measured_scales i).2]
        dsimp [qScale]
        exact Nat.one_le_pow _ _ (by omega)
      have hq : (1 : ℝ) ≤ (PT.tiling.P i).q := by exact_mod_cast hqNat
      have hqBound : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := hlow.mp hm
      have hCb : 0 < κ.Cb := by
        have hdiv : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
        have hEq : 100 * (κ.aC / κ.aB) = 100 * κ.aC / κ.aB := by
          field_simp [ne_of_gt hκ.aB_rng.1]
          <;> ring
        have hlower : 0 < 100 * κ.aC / κ.aB + 100 := by
          rw [← hEq]
          nlinarith
        exact lt_trans hlower hκ.Cb_big
      have hMlo : (κ.Cb + 100 : ℝ) < κ.Mlo := hκ.Mlo_big
      have hcqCb : 0 < κ.cq * κ.Cb := mul_pos hκ.cq_rng.1 hCb
      have hcqCbLt : κ.cq * κ.Cb < 1 := by
        have hmul := mul_lt_mul_of_pos_right hκ.cq_rng.2 hCb
        have hMloPos : 0 < (κ.Mlo : ℝ) := by linarith [hMlo, hCb]
        have hden : 0 < 20 * (κ.Mlo : ℝ) := mul_pos (by norm_num) hMloPos
        have hfrac : (1 / (20 * (κ.Mlo : ℝ))) * κ.Cb =
            κ.Cb / (20 * (κ.Mlo : ℝ)) := by field_simp
        rw [hfrac] at hmul
        have hratio : κ.Cb / (20 * (κ.Mlo : ℝ)) < 1 := by
          apply (div_lt_one hden).2
          nlinarith [hMlo]
        exact lt_trans hmul hratio
      have hqPower :
          Real.rpow (PT.tiling.P i).q κ.Cb ≤ Real.log (T.S.n k : ℝ) := by
        have hbase : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith [hklog]
        have hbasePow := Real.rpow_le_rpow (Nat.cast_nonneg _) hqBound hCb.le
        have hcomp :
            (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) ^ κ.Cb =
              Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) := by
          exact (Real.rpow_mul hbase κ.cq κ.Cb).symm
        calc
          Real.rpow (PT.tiling.P i).q κ.Cb ≤
              (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) ^ κ.Cb := hbasePow
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) := hcomp
          _ ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 1 :=
              Real.rpow_le_rpow_of_exponent_le hklog hcqCbLt.le
          _ = Real.log (T.S.n k : ℝ) := Real.rpow_one _
      have hnpos : 0 < (T.S.n k : ℝ) := by linarith [hkN]
      have hdiv := div_le_div_of_nonneg_right hqPower hnpos.le
      have hown : deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
          1 / 2 + 10 * Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ) := by
        have habs := (abs_le.mp hdeg).2
        have hle : deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
            10 * Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ) + 1 / 2 :=
          (sub_le_iff_le_add).mp habs
        simpa only [add_comm] using hle
      have hdiv10 :
          10 * Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ) =
            10 * (Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ)) := by
        field_simp [ne_of_gt hnpos]
        <;> ring
      calc
        deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
            1 / 2 + 10 * Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ) := hown
        _ = 1 / 2 + 10 * (Real.rpow (PT.tiling.P i).q κ.Cb / (T.S.n k : ℝ)) := by rw [hdiv10]
        _ ≤ 1 / 2 + 10 * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) :=
              by
                have hmul := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 10 by norm_num)
                simpa [add_comm] using add_le_add_left hmul (1 / 2 : ℝ)
        _ = 1 / 2 + 10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by ring
        _ ≤ 1 / 2 + 1 / 10000 := by linarith [hkL]
    | highSmall =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
    | highDirect =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
    | highLarge =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
  have hTV : ∀ i, PT.tvError i ≤ 1 / 100000 := by
    intro i
    cases hm : PT.tiling.mode with
    | bounded =>
      have hraw := hPT.raw_direct (by simp [Mode.isCluster, hm]) i
      have hEq := hPT.tv_error_eq i
      rw [hraw] at hEq
      simp at hEq
      linarith
    | lowDirect =>
      have hraw := hPT.raw_direct (by simp [Mode.isCluster, hm]) i
      have hEq := hPT.tv_error_eq i
      rw [hraw] at hEq
      simp at hEq
      linarith
    | lowCluster =>
      rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
        ⟨hthreshold, hg, _hmass, _hsmall, _hlarge, _hcodegree, _hh, hHlower, hHupper,
          _hlow, _hsmallMode, _hlargeMode⟩
      have hqNat : 1 ≤ (PT.tiling.P i).q := by
        rw [(hPT.tiling_valid.measured_scales i).2]
        dsimp [qScale]
        exact Nat.one_le_pow _ _ (by omega)
      have hq0 : κ.Q0 ≤ (PT.tiling.P i).q := by
        have hM1 : 0 < κ.M1 := by linarith [hκ.M1_big.1]
        have hmax : ((max (PT.tiling.P i).g (PT.tiling.P i).q : ℕ) : ℝ) ≤
            κ.M1 * (PT.tiling.P i).q := by
          rw [Nat.cast_max]
          apply max_le
          · exact hg
          · have hM1le : 1 ≤ κ.M1 := by linarith [hκ.M1_big.1]
            have hqnonneg : (0 : ℝ) ≤ (PT.tiling.P i).q := by positivity
            nlinarith [hM1le, hqnonneg]
        have hprod : κ.M1 * κ.Q0 ≤ κ.M1 * (PT.tiling.P i).q :=
          le_trans hthreshold hmax
        have hdiv := div_le_div_of_nonneg_right hprod hM1.le
        field_simp [ne_of_gt hM1] at hdiv
        exact hdiv
      have hQC := hκ.Q0_large ((PT.tiling.P i).q : ℝ) hq0
      rcases hQC with ⟨_, _, _, _, _, _, _, _, htail⟩
      have hlow : Real.rpow (PT.tiling.P i).q κ.Mlo ≤ (PT.tiling.P i).h := by simpa [hm] using hHlower
      have hMloMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
        have h := hκ.Mhi_big.1
        have hq : 0 < κ.cq := hκ.cq_rng.1
        have hfrac : 0 < 10 / κ.cq := by positivity
        exact le_trans (le_of_lt (lt_add_of_pos_right _ hfrac)) h
      have hqpow : Real.rpow (PT.tiling.P i).q κ.Mlo ≤
          Real.rpow (PT.tiling.P i).q κ.Mhi :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hqNat) hMloMhi
      have hup : (PT.tiling.P i).h <
          2 * Real.rpow (PT.tiling.P i).q κ.Mhi := by
        have hu : (PT.tiling.P i).h <
            2 * Real.rpow (PT.tiling.P i).q κ.Mlo := by simpa [hm] using hHupper
        exact lt_of_lt_of_le hu (by nlinarith [hqpow])
      rcases htail (PT.tiling.P i).h hlow hup with
        ⟨_, _, _, _, _, _, htv, _, _, _, _⟩
      have hTVraw := hPT.low_profile_tv hm i
      have hRpow10 : Real.rpow (10 : ℝ) (-5 : ℝ) = 1 / 100000 := by
        norm_num
      calc
        PT.tvError i ≤ Real.exp (-Real.rpow ((PT.tiling.P i).h : ℝ) (1 + κ.c14)) +
            2 * (PT.tiling.P i).h ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) := hTVraw
        _ ≤ 1 / 100000 := by
          rw [hRpow10] at htv
          exact htv
    | highSmall =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
    | highDirect =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
    | highLarge =>
      have : False := by simpa [Mode.isLow, hm] using D.low_mode
      exact False.elim this
  have hCountSub (A : InitialPairData D) :
      (D.nonisolates A.rows).card ≤ A.rows.card := by
    apply Finset.card_le_card
    intro v hv
    change v ∈ A.rows.filter (fun u => ∃ w ∈ A.rows, D.geometricAdj u w) at hv
    exact (Finset.mem_filter.mp hv).1
  have hCount : Q.count ≤ T.S.n k ^ 2 := by
    calc
      Q.count ≤ (D.nonisolates A.rows).card * T.S.n k := Q.count_bound
      _ ≤ A.rows.card * T.S.n k := Nat.mul_le_mul_right _ (hCountSub A)
      _ ≤ T.S.n k * T.S.n k := Nat.mul_le_mul_right _ A.small
      _ = T.S.n k ^ 2 := by rw [pow_two]
  have hRow (q : Fin Q.count) : Q.row q ∈ A.rows := by
    have h := Q.row_mem q
    change Q.row q ∈ A.rows.filter (fun u => ∃ w ∈ A.rows, D.geometricAdj u w) at h
    exact (Finset.mem_filter.mp h).1
  have hOdd : ∀ q, ¬ IsEvenRole (flipPos (Q.row q) (Q.coordinate q)) ∧
      D.geom.classOf (flipPos (Q.row q) (Q.coordinate q)) = none := by
    intro q
    have heven : IsEvenRole (Q.row q) := by
      have hm : Q.row q ∈ D.paletteRows A.paletteIndex := A.rows_subset (hRow q)
      exact (Finset.mem_filter.mp hm).2.1
    have hEarly : Q.coordinate q ∈ D.externalEarly (Q.row q) := Q.early q
    unfold LateData.externalEarly at hEarly
    rcases Finset.mem_filter.mp hEarly with ⟨_, ⟨_, hclass⟩⟩
    constructor
    · rw [HypercubeRamsey.S15.evenRole_flipPos]
      simp [heven]
    · exact hclass
  have hPalettePatch (q : Fin Q.count) :
      D.geom.patchOf (Q.row q) = A.paletteIndex.1 := by
    have hm : Q.row q ∈ D.paletteRows A.paletteIndex := A.rows_subset (hRow q)
    have hrole := (Finset.mem_filter.mp hm).2.2
    exact congrArg Sigma.fst hrole
  have hPatchFlip (q : Fin Q.count) :
      D.geom.patchOf (flipPos (Q.row q) (Q.coordinate q)) = D.geom.patchOf (Q.row q) := by
    have hbulk : Q.coordinate q ∈ PT.tiling.bulkCoords (D.geom.patchOf (Q.row q)) := Q.bulk q
    have hcoord : (PT.tiling.P (D.geom.patchOf (Q.row q))).ℓ ≤ (Q.coordinate q).val :=
      (Finset.mem_filter.mp hbulk).2.1
    have hrowLeaf := D.geom.patchOf_leaf (Q.row q)
    have hrowPrefix : ∀ j, j.val < (PT.tiling.P (D.geom.patchOf (Q.row q))).ℓ →
        (Q.row q) j = PT.tiling.w (D.geom.patchOf (Q.row q)) j := by
      simpa [Tiling.leaf, prefixLeaf] using hrowLeaf
    have hflipLeaf : flipPos (Q.row q) (Q.coordinate q) ∈
        PT.tiling.leaf (D.geom.patchOf (Q.row q)) := by
      change ∀ j, j.val < (PT.tiling.P (D.geom.patchOf (Q.row q))).ℓ →
        flipPos (Q.row q) (Q.coordinate q) j = PT.tiling.w (D.geom.patchOf (Q.row q)) j
      intro j hj
      have hne : j ≠ Q.coordinate q := by
        intro heq
        subst j
        omega
      simpa [flipPos, hne] using hrowPrefix j hj
    obtain ⟨i, hi, hUnique⟩ :=
      hPT.tiling_valid.prefix_complete (flipPos (Q.row q) (Q.coordinate q))
    have hrowEq : D.geom.patchOf (Q.row q) = i := hUnique _ hflipLeaf
    have hflipEq : D.geom.patchOf (flipPos (Q.row q) (Q.coordinate q)) = i :=
      hUnique _ (D.geom.patchOf_leaf _)
    exact hflipEq.trans hrowEq.symm
  have hErr : Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)) ≤ 1 / 25000 := by
    have h := hkErr.le
    have hExp : -((κ.Ac : ℝ) - 3) = -197 := by norm_num [hκ.Ac_eq]
    rw [hExp]
    exact h
  have hPairHit : ∀ (assignment : PairAssignment T k) q,
      (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
      (∑ y, (PT.πraw (D.geom.patchOf (flipPos (Q.row q) (Q.coordinate q)))).w y *
        (if Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).1 y ∧
            Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).2 y then (1 : ℝ) else 0)) ≤
        1 / 4 + 1 / 2500 := by
    intro assignment q hValid
    have hrow := hRow q
    rcases hValid (Q.row q) hrow with ⟨_, _, hxenv, hzenv, hnc⟩
    have hraw := HypercubeRamsey.Lane_q_s18_n6.rawPairHit_le_of_profile_bounds
      D (Q.row q) (assignment (Q.row q)).1 (assignment (Q.row q)).2
      ⟨hxenv, hzenv, hnc⟩
      (hOwn (D.geom.patchOf (Q.row q)) (assignment (Q.row q)).1 hxenv)
      (hOwn (D.geom.patchOf (Q.row q)) (assignment (Q.row q)).2 hzenv)
      (hTV (D.geom.patchOf (Q.row q))) hξ
    rw [hPatchFlip q]
    exact hraw
  have hSep : ∀ q q', q ≠ q' →
      D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q)) =
        D.geom.cellOf (flipPos (Q.row q') (Q.coordinate q')) →
      (hammingDist (flipPos (Q.row q) (Q.coordinate q))
        (flipPos (Q.row q') (Q.coordinate q')) : ℝ) >
          50 * κ.ρ * (PT.tiling.P
            (D.geom.patchOf (flipPos (Q.row q) (Q.coordinate q)))).h := by
    intro q q' hne hcell
    rw [hPatchFlip q, hPalettePatch q]
    exact Q.separated q q' hne hcell
  exact HypercubeRamsey.Lane_q_s18_n6.pairQueryBound_from_calibration
    hκ D hD A Q hCount hOdd Q.distinct_roles hSep hPairHit hErr

/-- P18.5g, 18:1212–1220. Assemble the numerical comparisons into the
all-tuples endpoint certificate. Constants remain uniform. -/
theorem P18_5g {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (Kpair KL KI Cp Cs CQ : ℝ) (hKpair : 0 < Kpair) (hKL : 1 ≤ KL) (hKI : 1 ≤ KI)
    (hCp : 0 < Cp) (hCs : 0 < Cs) (hCQ : 0 < CQ) :
    ∃ K Cprime Cstage : ℝ, 0 < K ∧ 0 < Cprime ∧ 0 < Cstage ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → ∀ δ εterm εrun, εterm ≤ 1 →
        ∀ C : TerminalCertificate D δ εterm, ∀ H : CompletionCertificate D C εrun,
        PairInitialFacts D δ Kpair → IsolateKernelFacts D KI →
        (∀ A : InitialPairData D, ∀ assignment, endpointProbability D C H A assignment ≤
          Real.exp (Cs * D.geom.r + Cp * A.rows.card * D.rank A.rows) * KL ^ A.rows.card *
            A.termTest C assignment) →
        (∀ A : InitialPairData D, ∀ assignment,
          A.termTest C assignment ≤ (1 + εterm) * A.permTest assignment ∧
          A.permTest assignment ≤ 2 * A.permFreshTest assignment ∧
          A.permFreshTest assignment ≤ 2 * A.iidFreshTest assignment) →
        (∀ A : InitialPairData D, ∃ Q : PairQueries D A, PairQueryBound D A Q ∧
          ∀ assignment, (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
            A.iidFreshTest assignment ≤
              Real.exp (0.005 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
                CQ * A.rows.card * D.rank A.rows) * (4 : ℝ) ^ Q.count * Q.integral assignment *
                  (D.paletteScale A.paletteIndex)⁻¹ ^ (2 * (D.nonisolates A.rows).card) *
                  ∏ v ∈ A.rows \ D.nonisolates A.rows,
                    isolatedWeight D v (assignment v).1 (assignment v).2) →
          EndpointCertificate D C H K Cprime Cstage := by
  refine ⟨Kpair + KL + KI + 2, Cp + CQ, Cs + 10, by positivity, by positivity,
    by positivity, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro k PT hPT D hD δ εterm εrun hε C H hPair hIso hEndpoint hCompare hQueries
  have hK : 0 < Kpair + KL + KI + 2 := by positivity
  have hCp' : 0 < Cp + CQ := by positivity
  have hCs' : 0 < Cs + 10 := by positivity
  have hCore := HypercubeRamsey.Lane_q_s18_n6.endpointCertificate_of_comparisons
    hκ D δ εterm εrun C H hε Kpair KL KI Cp Cs CQ hKpair hKL hKI hCp hCs hCQ
    hPair hIso hEndpoint hCompare hQueries
  simpa using hCore

theorem P18_5 {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 δ Krow : ℝ)
    (hK : 0 < K27) (hδ : 0 < δ) (hKrow : 0 < Krow) :
    ∃ K Cprime Cstage : ℝ, 0 < K ∧ 0 < Cprime ∧ 0 < Cstage ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → PaletteRowInput D Krow → TransitionData D → LocalTransitionFacts D K27 →
        ∀ εterm εrun, εterm ≤ 1 → ∀ C : TerminalCertificate D δ εterm,
          ∀ H : CompletionCertificate D C εrun, EndpointCertificate D C H K Cprime Cstage := by
  obtain ⟨KP, hKP, ha⟩ := P18_5a hκ T δ hδ
  obtain ⟨KL, Cp, Cs, hKL, hCp, hCs, hb⟩ := P18_5b hκ T K27 δ hK hδ
  obtain ⟨KI, hKI, hd⟩ := P18_5d hκ T Krow hKrow
  obtain ⟨CQ, hCQ, he⟩ := P18_5e hκ T
  obtain ⟨K, Cprime, Cstage, hK, hCp', hCs', hg⟩ :=
    P18_5g hκ T KP KL KI Cp Cs CQ hKP hKL hKI hCp hCs hCQ
  refine ⟨K, Cprime, Cstage, hK, hCp', hCs', ?_⟩
  filter_upwards [ha, hb, P18_5c hκ T, hd, he, P18_5f hκ T, hg] with k ha hb hc hd he hf hg
  intro PT hPT D hD hRows hR hLocal εterm εrun hε C H
  apply hg PT hPT D hD δ εterm εrun hε C H (ha PT hPT D hD hR) (hd PT hPT D hD hRows)
    (hb PT hPT D hD hR hLocal εterm εrun C H) (hc PT hPT D hD δ εterm C)
  intro A
  let A' := D18_I D A.paletteIndex A.rows A.rows_subset A.small
  obtain ⟨Q, hQ⟩ := he PT hPT D hD A'
  exact ⟨Q, hf PT hPT D hD A' Q, hQ⟩

/-- L18.6a, 18:1233–1242. Average the actual overlap correction over all
p-sets. η is chosen after Cprime and before the stages. -/
theorem L18_6a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K Cprime : ℝ)
    (hK : 0 < K) (hCp : 0 < Cprime) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 0.02 + Cprime * η < Real.log 2 / 2 ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → ∀ δ, PairInitialFacts D δ K →
          ∀ palette : PaletteIndex D, ∀ p : ℕ, (p : ℝ) ≤ η * T.S.n k →
            (∑ S ∈ (D.paletteRows palette).powersetCard p,
              Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cprime * p * D.rank S)) /
              ((D.paletteRows palette).powersetCard p).card ≤ 2 := by
  have hlogInv : Real.log (1 / 2 : ℝ) < -1 / 2 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hlogTwo : 1 / 2 < Real.log 2 := by
    have h := hlogInv
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hgap : 0 < Real.log 2 / 2 - 0.02 := by nlinarith [hlogTwo]
  let η : ℝ := min (1 / 2) ((Real.log 2 / 2 - 0.02) / (2 * Cprime))
  have hη : 0 < η := by
    apply lt_min
    · norm_num
    · exact div_pos hgap (by positivity)
  have hη1 : η < 1 := by
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hslack : 0.02 + Cprime * η < Real.log 2 / 2 := by
    have hη' : η ≤ (Real.log 2 / 2 - 0.02) / (2 * Cprime) := min_le_right _ _
    have hmul : Cprime * η ≤ (Real.log 2 / 2 - 0.02) / 2 := by
      have hmul' := mul_le_mul_of_nonneg_left hη' hCp.le
      have hden : 2 * Cprime ≠ 0 := ne_of_gt (by positivity)
      field_simp at hmul'
      nlinarith
    dsimp [η] at hη1
    linarith
  let a : ℝ := 0.02 + Cprime * η
  have hRateEvent := HypercubeRamsey.Lane_q_s18_n6.eventually_overlapRate_le_half
    hκ T η a hη1 (by dsimp [a]; exact hslack)
  refine ⟨η, hη, hη1, hslack, ?_⟩
  filter_upwards [hRateEvent] with k hRate
  intro PT hPT D hD δ hPair palette p hp
  let U : Finset (Pos T k) := D.paletteRows palette
  let Δ : ℕ := ⌈(T.S.n k : ℝ) ^ ((κ.Ac : ℝ) + 5)⌉₊
  have hExponentBound (S : Finset (Pos T k)) :
      0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cprime * p * D.rank S ≤
        (0.02 + Cprime * η) * (T.S.n k : ℝ) * D.rank S :=
    HypercubeRamsey.Lane_q_s18_n6.overlapMoment_exponent_bound
      D δ K Cprime η hPair hCp.le p hp S
  by_cases hpU : p ≤ U.card
  · have hRateLocal :
        Real.exp (a * (T.S.n k : ℝ)) * (p : ℝ) ^ 2 * Δ /
          ((U.card : ℝ) - p + 1) ≤ 1 / 2 := by
      simpa [a, U, Δ, Real.rpow_natCast, Nat.cast_add] using
        hRate U (hPair.2.1 palette) p hp
    have hdeg : ∀ v, (Finset.univ.filter fun w => D.geometricAdj v w).card ≤ Δ := by
      intro v
      have hdegReal := hPair.2.2.1 v
      have hceil : (T.S.n k : ℝ) ^ (κ.Ac + 5) ≤ (Δ : ℝ) := by
        calc
          (T.S.n k : ℝ) ^ (κ.Ac + 5) =
              (T.S.n k : ℝ) ^ ((κ.Ac + 5 : ℕ) : ℝ) := by rw [← Real.rpow_natCast]
          _ = (T.S.n k : ℝ) ^ ((κ.Ac : ℝ) + 5) := by congr 1 <;> norm_num
          _ ≤ (Δ : ℝ) := by dsimp [Δ]; exact Nat.le_ceil _
      exact_mod_cast hdegReal.trans hceil
    have hMoment := HypercubeRamsey.Lane_q_s18_n6.overlapRank_exp_moment_le_two
      D U p Δ (a * (T.S.n k : ℝ)) hpU hdeg (by simpa [a, U, Δ] using hRateLocal)
    have hSum :
        (∑ S ∈ U.powersetCard p,
          Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card +
            Cprime * p * D.rank S)) ≤
        (∑ S ∈ U.powersetCard p,
          Real.exp (a * (T.S.n k : ℝ) * D.rank S)) := by
      apply Finset.sum_le_sum
      intro S hS
      exact Real.exp_le_exp.mpr (by
        have h := hExponentBound S
        dsimp [a]
        nlinarith [h])
    have hdenPos : 0 < ((U.powersetCard p).card : ℝ) := by
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_pos hpU
    change
      (∑ S ∈ U.powersetCard p,
        Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card +
          Cprime * p * D.rank S)) / ((U.powersetCard p).card : ℝ) ≤ 2
    calc
      _ ≤ (∑ S ∈ U.powersetCard p,
          Real.exp (a * (T.S.n k : ℝ) * D.rank S)) / ((U.powersetCard p).card : ℝ) :=
        div_le_div_of_nonneg_right hSum hdenPos.le
      _ ≤ 2 := hMoment
  · have hEmpty : U.powersetCard p = ∅ := by
      apply Finset.powersetCard_eq_empty.mpr
      omega
    have hlt : U.card < p := Nat.lt_of_not_ge hpU
    dsimp [U] at hEmpty ⊢
    rw [hEmpty]
    simp [Nat.choose_eq_zero_of_lt hlt]

noncomputable def HallBudget {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) (η K Cs : ℝ) : ℝ :=
  Real.exp (Cs * D.geom.r) * ∑ p : PaletteIndex D,
    (D.paletteScale p * (K / densityScale T k) ^ ⌊η * (T.S.n k : ℝ)⌋₊ +
    (D.paletteScale p)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
      ∑ q ∈ Finset.range ⌊η * (T.S.n k : ℝ)⌋₊,
        if 3 ≤ q then (q : ℝ) ^ 4 * (K / densityScale T k) ^ q else 0)

/-- L18.6b, 18:1244–1287. Tree diagrams and two extra mergers on retained
distinct-endpoint support bound actual connected obstruction probabilities. -/
theorem L18_6b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K Cp Cs η : ℝ)
    (hK : 0 < K) (hCp : 0 < Cp) (hCs : 0 < Cs) (hη : 0 < η) (hη1 : η < 1) :
    ∃ KH : ℝ, 0 < KH ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ δ εterm εrun,
      ∀ C : TerminalCertificate D δ εterm, ∀ H : CompletionCertificate D C εrun,
      EndpointCertificate D C H K Cp Cs →
      (∀ palette : PaletteIndex D, ∀ p : ℕ, (p : ℝ) ≤ η * T.S.n k →
        (∑ S ∈ (D.paletteRows palette).powersetCard p,
          Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cp * p * D.rank S)) /
          ((D.paletteRows palette).powersetCard p).card ≤ 2) →
        (pairExperiment D C H).pr (fun out => D.full δ out.1.1 out.1.2 ∧
          HallObstruction D ⌊η * (T.S.n k : ℝ)⌋₊ out.2) ≤ HallBudget D η KH (Cs + 10) := by
  let B : ℝ := 4096 * (K + 1) ^ 2
  let KH : ℝ := B * K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hKH : 0 < KH := by dsimp [KH, B]; positivity
  have hthreshold : ∀ᶠ k : ℕ in atTop, 3 ≤ ⌊η * (T.S.n k : ℝ)⌋₊ := by
    have hlarge := T.S.n_tendsto.eventually_ge_atTop ⌈3 / η⌉₊
    filter_upwards [hlarge] with k hk
    have hcast : (⌈3 / η⌉₊ : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hk
    have hceil : 3 / η ≤ (⌈3 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (3 : ℝ) ≤ η * (T.S.n k : ℝ) := by
      have h := (div_le_iff₀ hη).mp (hceil.trans hcast)
      nlinarith
    exact Nat.le_floor h3
  have hChord := Lane_sol_s18_6b.eventually_chordRate_le_one hκ T K hK
  refine ⟨KH, hKH, ?_⟩
  filter_upwards [hthreshold, hChord] with k ht0 hChord
  intro PT hPT D hD δ εterm εrun C H hEndpoint hAverage
  have hPairFacts : PairInitialFacts D δ K := hEndpoint.pair_facts
  simpa only [HallBudget, KH] using
    (Lane_sol_s18_6b.obstruction_le_of_tuple_diagrams D C H K Cp Cs η B
      hK hη hB hPairFacts hAverage ht0 (by
        intro palette S hsub hthree hsmall
        have hfloor : (⌊η * (T.S.n k : ℝ)⌋₊ : ℝ) ≤ (T.S.n k : ℝ) := by
          have h := Nat.floor_le (mul_nonneg hη.le (Nat.cast_nonneg (T.S.n k)))
          have hmul : η * (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hη1.le
              (show (0 : ℝ) ≤ (T.S.n k : ℝ) from Nat.cast_nonneg _)
          exact h.trans hmul
        have hSn : S.card ≤ T.S.n k := by
          have hcast : (S.card : ℝ) ≤ (⌊η * (T.S.n k : ℝ)⌋₊ : ℝ) := by
            exact_mod_cast hsmall
          exact_mod_cast hcast.trans hfloor
        let A : InitialPairData D := ⟨palette, S, hsub, hSn⟩
        obtain ⟨ker, hnonneg, hsymm, hrow, hentry, hjoint⟩ := hEndpoint.joint A
        have hrate := hChord PT hPT D δ hPairFacts palette S.card hSn
        let F : ℝ := Real.exp (Cs * D.geom.r) * K ^ S.card *
          Lane_sol_s18_6b.correction D Cp S
        have hjoint' : ∀ assignment, endpointProbability D C H A assignment ≤
            F * ∏ v ∈ A.rows, ker v (assignment v).1 (assignment v).2 := by
          intro assignment
          exact hjoint assignment
        have hfalse := Lane_sol_s18_6b.connectedPr_le_kernelSum D C H hPairFacts A false ker F hjoint'
        have htrue := Lane_sol_s18_6b.connectedPr_le_kernelSum D C H hPairFacts A true ker F hjoint'
        have hcount :
            K ^ S.card * Lane_sol_s18_6b.kernelSum D palette S false ker ≤
              D.paletteScale palette * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card ∧
            K ^ S.card * Lane_sol_s18_6b.kernelSum D palette S true ker ≤
              (D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
                (S.card : ℝ) ^ 4 * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card := by
          -- The finite assignment-to-diagram injection and weighted count remain.
          -- Distinct endpoints and palette support are retained in kernelSum.
          sorry
        have hfactor : 0 ≤ Real.exp (Cs * D.geom.r) * Lane_sol_s18_6b.correction D Cp S :=
          mul_nonneg (Real.exp_pos _).le (Lane_sol_s18_6b.correction_nonneg D Cp S)
        constructor
        · calc
            _ ≤ F * Lane_sol_s18_6b.kernelSum D palette S false ker := hfalse
            _ = (Real.exp (Cs * D.geom.r) * Lane_sol_s18_6b.correction D Cp S) *
                (K ^ S.card * Lane_sol_s18_6b.kernelSum D palette S false ker) := by dsimp [F]; ring
            _ ≤ (Real.exp (Cs * D.geom.r) * Lane_sol_s18_6b.correction D Cp S) *
                (D.paletteScale palette * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card) :=
              mul_le_mul_of_nonneg_left hcount.1 hfactor
            _ = _ := by ring
        · calc
            _ ≤ F * Lane_sol_s18_6b.kernelSum D palette S true ker := htrue
            _ = (Real.exp (Cs * D.geom.r) * Lane_sol_s18_6b.correction D Cp S) *
                (K ^ S.card * Lane_sol_s18_6b.kernelSum D palette S true ker) := by dsimp [F]; ring
            _ ≤ (Real.exp (Cs * D.geom.r) * Lane_sol_s18_6b.correction D Cp S) *
                ((D.paletteScale palette)⁻¹ * Real.exp (0.02 * (T.S.n k : ℝ)) *
                  (S.card : ℝ) ^ 4 * (S.card.factorial : ℝ) * (B / D.paletteScale palette) ^ S.card) :=
              mul_le_mul_of_nonneg_left hcount.2 hfactor
            _ = _ := by ring))

set_option maxHeartbeats 400000

/-- L18.6c, 18:1289–1299. Sum all palettes/patches; C_n→∞ supplies the
negative linear exponent. The output spends a quarter of total mass. -/
theorem L18_6c {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (η K Cs Kpair : ℝ)
    (hη : 0 < η) (hK : 0 < K) (hCs : 0 < Cs) (hKP : 0 < Kpair) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ δ, PairInitialFacts D δ Kpair → HallBudget D η K Cs < 1 / 4 := by
  let B : ℝ := 4 * Cs * κ.A0
  have hnT : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hpoly1 : Tendsto (fun x : ℝ => x ^ (B + 1) * Real.exp (-x)) atTop (nhds 0) := by
    simpa [mul_comm] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B + 1) 1 one_pos)
  have hsmall1 : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (B + 1) * Real.exp (-(T.S.n k : ℝ)) < 1 / 8 := by
    exact (hpoly1.comp hnT).eventually (Iio_mem_nhds (by norm_num))
  have hpoly2 : Tendsto
      (fun x : ℝ => (Kpair * η ^ 5) * x ^ (B + 5) * Real.exp (-(1 / 3 : ℝ) * x))
      atTop (nhds 0) := by
    have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (B + 5) (1 / 3 : ℝ) (by norm_num)
    have hconst : Tendsto (fun _ : ℝ => Kpair * η ^ 5) atTop
        (nhds (Kpair * η ^ 5)) := tendsto_const_nhds
    simpa [mul_assoc] using hconst.mul hdecay
  have hsmall2 : ∀ᶠ k in atTop,
      (Kpair * η ^ 5) * (T.S.n k : ℝ) ^ (B + 5) *
        Real.exp (-(1 / 3 : ℝ) * (T.S.n k : ℝ)) < 1 / 8 := by
    exact (hpoly2.comp hnT).eventually (Iio_mem_nhds (by norm_num))
  have hdensity : Tendsto (fun k : ℕ => densityScale T k) atTop atTop := by
    simpa [densityScale] using T.S.ratio_tendsto
  have hlargeDensity : ∀ᶠ k in atTop,
      max 1 (K * Real.exp (4 / η)) ≤ densityScale T k :=
    hdensity.eventually_ge_atTop _
  have hlargeN : ∀ᶠ k in atTop,
      max (256 : ℝ) (2 / η) ≤ (T.S.n k : ℝ) := hnT.eventually_ge_atTop _
  filter_upwards [hsmall1, hsmall2, hlargeDensity, hlargeN] with k hsmall1 hsmall2 hlargeDensity hlargeN
  intro PT hPT D hD δ hPair
  let n : ℝ := (T.S.n k : ℝ)
  let t : ℕ := ⌊η * n⌋₊
  let u : ℝ := η * n
  let a : ℝ := K / densityScale T k
  have hncast : (T.S.n k : ℝ) = n := rfl
  have hnlarge : 256 ≤ n := (le_max_left _ _).trans hlargeN
  have hneta : 2 / η ≤ n := (le_max_right _ _).trans hlargeN
  have hnpos : 0 < n := by linarith
  have hdensity1 : 1 ≤ densityScale T k := (le_max_left _ _).trans hlargeDensity
  have hKdensity : K * Real.exp (4 / η) ≤ densityScale T k :=
    (le_max_right _ _).trans hlargeDensity
  have hsmall1' : n ^ (B + 1) * Real.exp (-n) < 1 / 8 := by simpa [n] using hsmall1
  have hsmall2' : (Kpair * η ^ 5) * n ^ (B + 5) *
      Real.exp (-(1 / 3 : ℝ) * n) < 1 / 8 := by simpa [n] using hsmall2
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hgeom : (D.geom.r : ℝ) ≤ 4 * κ.A0 * Real.log n := by
    have hhalf := mul_le_mul_of_nonneg_left hlog2lo (Nat.cast_nonneg D.geom.r)
    nlinarith [D.l16_valid.r_upper, hhalf]
  have houter : Real.exp (Cs * D.geom.r) ≤ n ^ B := by
    have h := mul_le_mul_of_nonneg_left hgeom hCs.le
    calc
      Real.exp (Cs * D.geom.r) ≤ Real.exp (B * Real.log n) := by
        apply Real.exp_le_exp.mpr
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using h
      _ = n ^ B := by rw [Real.rpow_def_of_pos hnpos]; congr 1 <;> ring
  have hNle : (T.S.N k : ℝ) ≤ n * (2 : ℝ) ^ (T.S.n k) := by
    rw [← hncast]
    exact_mod_cast T.S.N_le k
  have hpow2 : (2 : ℝ) ^ (T.S.n k) ≤ Real.exp n := by
    calc
      (2 : ℝ) ^ (T.S.n k) = (Real.exp (Real.log 2)) ^ (T.S.n k) := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((T.S.n k : ℝ) * Real.log 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp n := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hlog2hi (Nat.cast_nonneg (T.S.n k))
        calc
          (T.S.n k : ℝ) * Real.log 2 ≤ (T.S.n k : ℝ) * 1 := hmul
          _ = n := by simp [hncast]
  have hNexp : (T.S.N k : ℝ) ≤ n * Real.exp n :=
    hNle.trans (mul_le_mul_of_nonneg_left hpow2 (by linarith))
  have hneta2 : 2 ≤ u := by
    dsimp [u]
    have hmul := (div_le_iff₀ hη).1 hneta
    simpa [mul_comm] using hmul
  have htUpper : (t : ℝ) ≤ u := by
    dsimp [t, u]
    exact Nat.floor_le (by positivity)
  have htLower : u / 2 ≤ (t : ℝ) := by
    have hfloor : u < (t : ℝ) + 1 := by
      simpa [t, u] using Nat.lt_floor_add_one (η * n)
    nlinarith [hneta2]
  have hdensityPos : 0 < densityScale T k := lt_of_lt_of_le (by norm_num) hdensity1
  have hExpCancel : Real.exp (-4 / η) * Real.exp (4 / η) = 1 := by
    rw [← Real.exp_add]
    have : -4 / η + 4 / η = 0 := by ring
    rw [this, Real.exp_zero]
  have hKle : K ≤ Real.exp (-4 / η) * densityScale T k := by
    calc
      K = K * (Real.exp (-4 / η) * Real.exp (4 / η)) := by rw [hExpCancel]; ring
      _ = Real.exp (-4 / η) * (K * Real.exp (4 / η)) := by ring
      _ ≤ Real.exp (-4 / η) * densityScale T k :=
        mul_le_mul_of_nonneg_left hKdensity (Real.exp_nonneg _)
  have hbase : a ≤ Real.exp (-4 / η) := by
    dsimp [a]
    exact (div_le_iff₀ hdensityPos).2 hKle
  have hbase0 : 0 ≤ a := by positivity
  have hquotPos : 0 < (4 : ℝ) / η := div_pos (by norm_num) hη
  have hbase1 : Real.exp (-4 / η) < 1 :=
    Real.exp_lt_one_iff.mpr (by rw [neg_div]; exact neg_lt_zero.mpr hquotPos)
  have ha1 : a ≤ 1 := hbase.trans hbase1.le
  have hpowBase : a ^ t ≤ Real.exp (-2 * n) := by
    calc
      a ^ t ≤ (Real.exp (-4 / η)) ^ t := by gcongr
      _ = Real.exp ((t : ℝ) * (-4 / η)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-2 * n) := by
        apply Real.exp_le_exp.mpr
        have hcoeff : (-4 / η) * (u / 2) = -2 * n := by
          dsimp [u]
          field_simp
          ring
        have hcoeffneg : -4 / η ≤ 0 := by
          rw [neg_div]
          exact neg_nonpos.mpr hquotPos.le
        have hmul := mul_le_mul_of_nonpos_left htLower hcoeffneg
        calc
          (t : ℝ) * (-4 / η) = (-4 / η) * (t : ℝ) := by ring
          _ ≤ (-4 / η) * (u / 2) := hmul
          _ = -2 * n := hcoeff
  have hsumA :
      (∑ p : PaletteIndex D, D.paletteScale p * a ^ t) ≤
        (T.S.N k : ℝ) * a ^ t := by
    calc
      _ = (∑ p : PaletteIndex D, D.paletteScale p) * a ^ t := by
        rw [← Finset.sum_mul]
      _ ≤ (T.S.N k : ℝ) * a ^ t :=
        mul_le_mul_of_nonneg_right (Lane_q_s18_n7.paletteScale_sum_le_host D)
          (pow_nonneg hbase0 _)
  have hfirst : Real.exp (Cs * D.geom.r) *
      (∑ p : PaletteIndex D, D.paletteScale p * a ^ t) ≤
      n ^ (B + 1) * Real.exp (-n) := by
    calc
      _ ≤ Real.exp (Cs * D.geom.r) * ((T.S.N k : ℝ) * a ^ t) :=
        mul_le_mul_of_nonneg_left hsumA (Real.exp_nonneg _)
      _ ≤ n ^ B * (n * Real.exp n * Real.exp (-2 * n)) := by
        gcongr
      _ = n ^ (B + 1) * Real.exp (-n) := by
        have hexp : Real.exp n * Real.exp (-2 * n) = Real.exp (-n) := by
          calc
            _ = Real.exp (n + (-2 * n)) := (Real.exp_add n (-2 * n)).symm
            _ = Real.exp (-n) := by congr 1 <;> ring
        calc
          n ^ B * (n * Real.exp n * Real.exp (-2 * n)) =
              n ^ B * n * (Real.exp n * Real.exp (-2 * n)) := by ring
          _ = n ^ B * n * Real.exp (-n) := by rw [hexp]
          _ = n ^ (B + 1) * Real.exp (-n) := by
            calc
              n ^ B * n * Real.exp (-n) = (n ^ B * n) * Real.exp (-n) := by ring
              _ = n ^ (B + 1) * Real.exp (-n) := by
                rw [show n ^ B * n = n ^ (B + 1) by
                  simpa [Real.rpow_one] using (Real.rpow_add hnpos B 1).symm]
  have hLpos : 0 < (2 : ℝ) ^ (n - Real.sqrt n) := Real.rpow_pos_of_pos (by norm_num) _
  have hsqrt : Real.sqrt n ≤ n / 16 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hprod := mul_nonneg (by linarith : 0 ≤ n) (by linarith : 0 ≤ n - 256)
      nlinarith [hprod]
  have hcoeff : -n + 2 * Real.sqrt n ≤ -7 * n / 8 := by nlinarith [hsqrt]
  have hpowRatioEq :
      (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 =
        (2 : ℝ) ^ (-n + 2 * Real.sqrt n) := by
    have h2 : 0 < (2 : ℝ) := by norm_num
    rw [Real.rpow_def_of_pos h2, Real.rpow_def_of_pos h2]
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    rw [Real.rpow_def_of_pos h2]
    congr 1 <;> ring
  have hpowRatio :
      (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 ≤ Real.exp (-7 * n / 16) := by
    rw [hpowRatioEq, Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    have hcoeffneg : -n + 2 * Real.sqrt n ≤ 0 := by linarith [hcoeff, hnlarge]
    have hmul := mul_le_mul_of_nonpos_left hlog2lo hcoeffneg
    apply Real.exp_le_exp.mpr
    nlinarith [hmul, hcoeff]
  have hinner :
      (∑ q ∈ Finset.range t,
        if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0) ≤ u ^ 5 := by
    have hterm : ∀ q ∈ Finset.range t,
        (if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0) ≤ u ^ 4 := by
      intro q hq
      have hqle : (q : ℝ) ≤ u := by
        have hqt : q < t := Finset.mem_range.mp hq
        have hqtcast : (q : ℝ) ≤ (t : ℝ) := by exact_mod_cast hqt.le
        exact hqtcast.trans htUpper
      by_cases hq3 : 3 ≤ q
      · simp only [if_pos hq3]
        have hqp : (q : ℝ) ^ 4 ≤ u ^ 4 := by gcongr
        have hap : a ^ q ≤ 1 := by
          calc
            a ^ q ≤ (1 : ℝ) ^ q := by gcongr
            _ = 1 := by simp
        calc
          (q : ℝ) ^ 4 * a ^ q ≤ u ^ 4 * 1 :=
            mul_le_mul hqp hap (by positivity) (by positivity)
          _ = u ^ 4 := by ring
      · simp [hq3]
        positivity
    calc
      _ ≤ ∑ q ∈ Finset.range t, u ^ 4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact hterm q hq
      _ = (t : ℝ) * u ^ 4 := by simp
      _ ≤ u ^ 5 := by
        have hu : 0 ≤ u := by positivity
        calc
          (t : ℝ) * u ^ 4 ≤ u * u ^ 4 := by gcongr
          _ = u ^ 5 := by rw [pow_succ]; ring
  have hInv := Lane_q_s18_n7.paletteScale_inv_sum_le (D := D) hKP hPair hdensity1
  have hLsq : 0 < ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 := sq_pos_of_pos hLpos
  have hInv' :
      (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) ≤
        Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 := by
    calc
      _ ≤ Kpair * (2 : ℝ) ^ n /
          (densityScale T k * ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) := hInv
      _ ≤ Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos (lt_of_lt_of_le (by norm_num) hdensity1) hLsq) hLsq]
        have htop : 0 ≤ Kpair * (2 : ℝ) ^ n := by positivity
        have hden : ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 ≤
            densityScale T k * ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 :=
          by simpa using mul_le_mul_of_nonneg_right hdensity1 hLsq.le
        exact mul_le_mul_of_nonneg_left hden htop
  have hsumB :
      (∑ p : PaletteIndex D,
        (D.paletteScale p)⁻¹ * Real.exp (0.02 * n) *
          (∑ q ∈ Finset.range t,
            if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0)) ≤
        (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) * Real.exp (0.02 * n) * u ^ 5 := by
    calc
      _ = (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
          (Real.exp (0.02 * n) *
            (∑ q ∈ Finset.range t,
              if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0)) := by
        calc
          _ = ∑ p : PaletteIndex D, (D.paletteScale p)⁻¹ *
              (Real.exp (0.02 * n) *
                (∑ q ∈ Finset.range t,
                  if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0)) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ = _ := by rw [← Finset.sum_mul]
      _ ≤ (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
          (Real.exp (0.02 * n) * u ^ 5) := by
        have hnonneg : 0 ≤ ∑ p : PaletteIndex D, (D.paletteScale p)⁻¹ :=
          Finset.sum_nonneg fun p hp => inv_nonneg.mpr (by
            unfold LateData.paletteScale
            positivity)
        have hexp : 0 ≤ Real.exp (0.02 * n) := Real.exp_nonneg _
        have hprod := mul_le_mul_of_nonneg_left hinner hexp
        exact mul_le_mul_of_nonneg_left hprod hnonneg
      _ = _ := by ring
  have hsecond : Real.exp (Cs * D.geom.r) *
      (∑ p : PaletteIndex D,
        (D.paletteScale p)⁻¹ * Real.exp (0.02 * n) *
          (∑ q ∈ Finset.range t,
            if 3 ≤ q then (q : ℝ) ^ 4 * a ^ q else 0)) ≤
      (Kpair * η ^ 5) * n ^ (B + 5) * Real.exp (-(1 / 3 : ℝ) * n) := by
    have hinv0 : 0 ≤ ∑ p : PaletteIndex D, (D.paletteScale p)⁻¹ :=
      Finset.sum_nonneg fun p hp => inv_nonneg.mpr (by
        unfold LateData.paletteScale
        positivity)
    have htail0 : 0 ≤ Real.exp (0.02 * n) * u ^ 5 :=
      mul_nonneg (Real.exp_nonneg _) (pow_nonneg (by positivity) _)
    have hmiddle0 : 0 ≤ (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
        Real.exp (0.02 * n) * u ^ 5 := by positivity
    have hinvStep : (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
        Real.exp (0.02 * n) * u ^ 5 ≤
        (Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
          Real.exp (0.02 * n) * u ^ 5 := by
      calc
        _ = (∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
            (Real.exp (0.02 * n) * u ^ 5) := by ring
        _ ≤ (Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
            (Real.exp (0.02 * n) * u ^ 5) :=
          mul_le_mul_of_nonneg_right hInv' htail0
        _ = _ := by ring
    have hscaleStep : Real.exp (Cs * D.geom.r) *
        ((∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
          Real.exp (0.02 * n) * u ^ 5) ≤
        n ^ B * ((∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
          Real.exp (0.02 * n) * u ^ 5) :=
      mul_le_mul_of_nonneg_right houter hmiddle0
    have hinvStep' : n ^ B *
        ((∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) *
          Real.exp (0.02 * n) * u ^ 5) ≤
        n ^ B * ((Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
          Real.exp (0.02 * n) * u ^ 5) :=
      mul_le_mul_of_nonneg_left hinvStep (by positivity)
    calc
      _ ≤ Real.exp (Cs * D.geom.r) *
          ((∑ p : PaletteIndex D, (D.paletteScale p)⁻¹) * Real.exp (0.02 * n) * u ^ 5) :=
        mul_le_mul_of_nonneg_left hsumB (Real.exp_nonneg _)
      _ ≤ n ^ B *
          ((Kpair * (2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
            Real.exp (0.02 * n) * u ^ 5) := hscaleStep.trans hinvStep'
      _ ≤ (Kpair * η ^ 5) * n ^ (B + 5) * Real.exp (-(1 / 3 : ℝ) * n) := by
        have hsmallExp : (2 : ℝ) ^ n /
            ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 * Real.exp (0.02 * n) ≤
            Real.exp (-(1 / 3 : ℝ) * n) := by
          calc
            _ ≤ Real.exp (-7 * n / 16) * Real.exp (0.02 * n) :=
              mul_le_mul_of_nonneg_right hpowRatio (Real.exp_nonneg _)
            _ = Real.exp (-7 * n / 16 + 0.02 * n) :=
              (Real.exp_add (-7 * n / 16) (0.02 * n)).symm
            _ ≤ Real.exp (-(1 / 3 : ℝ) * n) := by
              apply Real.exp_le_exp.mpr
              have hcoeff : -7 / 16 + (0.02 : ℝ) ≤ -(1 / 3 : ℝ) := by norm_num
              calc
                -7 * n / 16 + 0.02 * n = (-7 / 16 + (0.02 : ℝ)) * n := by ring
                _ ≤ (-(1 / 3 : ℝ)) * n := mul_le_mul_of_nonneg_right hcoeff (by linarith)
        have hu5 : u ^ (5 : ℕ) = η ^ (5 : ℕ) * n ^ (5 : ℕ) := by simp [u, mul_pow]
        have hnPow : n ^ B * n ^ (5 : ℕ) = n ^ (B + 5) := by
          calc
            n ^ B * n ^ (5 : ℕ) = n ^ B * n ^ (5 : ℝ) :=
              congrArg (fun z : ℝ => n ^ B * z) (Real.rpow_natCast n 5).symm
            _ = n ^ (B + 5) := (Real.rpow_add hnpos B (5 : ℝ)).symm
        have hfactor : n ^ B *
            ((Kpair * (2 : ℝ) ^ n /
                ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
              Real.exp (0.02 * n) * u ^ 5) =
            (Kpair * η ^ 5 * n ^ (B + 5)) *
              ((2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 *
                Real.exp (0.02 * n)) := by
          rw [hu5]
          calc
            n ^ B * ((Kpair * (2 : ℝ) ^ n /
                ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
                Real.exp (0.02 * n) * (η ^ (5 : ℕ) * n ^ (5 : ℕ))) =
                (Kpair * η ^ 5) * (n ^ B * n ^ (5 : ℕ)) *
                  ((2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 *
                    Real.exp (0.02 * n)) := by ring
            _ = _ :=
              congrArg (fun z : ℝ => (Kpair * η ^ 5) * z *
                ((2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 *
                  Real.exp (0.02 * n))) hnPow
        have hcoef0 : 0 ≤ Kpair * η ^ 5 * n ^ (B + 5) := by positivity
        calc
          n ^ B * ((Kpair * (2 : ℝ) ^ n /
                ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2) *
              Real.exp (0.02 * n) * u ^ 5) =
              (Kpair * η ^ 5 * n ^ (B + 5)) *
                ((2 : ℝ) ^ n / ((2 : ℝ) ^ (n - Real.sqrt n)) ^ 2 *
                  Real.exp (0.02 * n)) := hfactor
          _ ≤ (Kpair * η ^ 5 * n ^ (B + 5)) *
                Real.exp (-(1 / 3 : ℝ) * n) :=
              mul_le_mul_of_nonneg_left hsmallExp hcoef0
  have hbudget : HallBudget D η K Cs ≤
      n ^ (B + 1) * Real.exp (-n) +
        (Kpair * η ^ 5) * n ^ (B + 5) * Real.exp (-(1 / 3 : ℝ) * n) := by
    unfold HallBudget
    rw [Finset.sum_add_distrib, mul_add]
    exact add_le_add hfirst hsecond
  have hs1 : n ^ (B + 1) * Real.exp (-n) < 1 / 8 := hsmall1'
  have hs2 : (Kpair * η ^ 5) * n ^ (B + 5) *
      Real.exp (-(1 / 3 : ℝ) * n) < 1 / 8 := hsmall2'
  linarith

/-- L18.6d, 18:1301–1306. Full mass≥3/4 minus actual obstruction mass<1/4
leaves positive success and per-palette representatives. -/
theorem L18_6d {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    (D : LateData hPT) {δ εterm εrun : ℝ} (C : TerminalCertificate D δ εterm)
    (H : CompletionCertificate D C εrun) (K : ℝ) (hPair : PairInitialFacts D δ K)
    (t₀ : ℕ) (ht : 3 ≤ t₀) (hfull : εrun ≤ 1 / 4)
    (hbad : (pairExperiment D C H).pr (fun out => D.full δ out.1.1 out.1.2 ∧ HallObstruction D t₀ out.2) < 1 / 4) :
    Nonempty (HallCertificate D δ) := by
  classical
  let P := pairExperiment D C H
  let fullEvent : ((D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r)) ×
      PairAssignment T k) → Prop := fun out => D.full δ out.1.1 out.1.2
  let badEvent : ((D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r)) ×
      PairAssignment T k) → Prop := fun out => HallObstruction D t₀ out.2
  let Base := FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
    (fun x => D.encoding.base.runFull H.samplers.act (D.encoding.initialState x))
  have hfullP : 1 - εrun ≤ P.pr fullEvent := by
    change 1 - εrun ≤ (FinLaw.bind Base (fun z => D.pairSampler z.2)).pr
      (fun out => D.full δ out.1.1 out.1.2)
    have hbaseFull : 1 - εrun ≤ Base.pr (fun z => D.full δ z.1 z.2) := by
      simpa [Base, FullRunProbability] using H.fullRun
    rw [Lane_q_s18_n7.finLaw_pr_bind_fst Base (fun z => D.pairSampler z.2)
      (fun z => D.full δ z.1 z.2)]
    exact hbaseFull
  have hfull34 : (3 : ℝ) / 4 ≤ P.pr fullEvent := by linarith
  have hgoodPos : 0 < P.pr (fun out => fullEvent out ∧ ¬ badEvent out) := by
    rw [Lane_q_s18_n7.finLaw_pr_split P fullEvent badEvent] at hfull34
    have hbad' : P.pr (fun out => fullEvent out ∧ badEvent out) < 1 / 4 := by
      simpa [P, fullEvent, badEvent] using hbad
    linarith
  obtain ⟨out, hout, houtw⟩ :=
    Lane_q_s18_n7.exists_weight_pos_of_pr_pos P
      (fun out => fullEvent out ∧ ¬ badEvent out) hgoodPos
  have houtFull : D.full δ out.1.1 out.1.2 := hout.1
  have houtNoObstruction : ¬ HallObstruction D t₀ out.2 := hout.2
  have hProd : Base.w out.1 * (D.pairSampler out.1.2).w out.2 > 0 := by
    simpa [P, Base, pairExperiment, LateEncoding.experiment, FinLaw.bind] using houtw
  have hsamplerNonneg : 0 ≤ (D.pairSampler out.1.2).w out.2 :=
    (D.pairSampler out.1.2).nonneg _
  have hsamplerPos : 0 < (D.pairSampler out.1.2).w out.2 := by
    by_contra h
    have hle : (D.pairSampler out.1.2).w out.2 ≤ 0 := le_of_not_gt h
    have hz : (D.pairSampler out.1.2).w out.2 = 0 := le_antisymm hle hsamplerNonneg
    rw [hz, mul_zero] at hProd
    linarith
  have hpairsPos : ∀ v : Pos T k, 0 < (D.pairLaw out.1.2 v).w (out.2 v) := by
    have hprod : 0 < ∏ v : Pos T k, (D.pairLaw out.1.2 v).w (out.2 v) := by
      simpa [LateData.pairSampler, FinLaw.pi] using hsamplerPos
    have hprodNe : ∏ v : Pos T k, (D.pairLaw out.1.2 v).w (out.2 v) ≠ 0 := ne_of_gt hprod
    intro v
    have hvne : (D.pairLaw out.1.2 v).w (out.2 v) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprodNe) v (Finset.mem_univ _)
    exact lt_of_le_of_ne ((D.pairLaw out.1.2 v).nonneg _) (Ne.symm hvne)
  have pairSupported (v : Pos T k) (hv : IsEvenRole v) :
      0 < (D.pairLaw out.1.2 v).w (out.2 v) := hpairsPos v
  have pairDistinct (v : Pos T k) (hv : IsEvenRole v) : (out.2 v).1 ≠ (out.2 v).2 := by
    exact ((hPair.2.2.2.2 out.1.1 out.1.2 houtFull v hv).2 (out.2 v)
      (pairSupported v hv)).1
  have rowEvent : ∀ p : PaletteIndex D, ∀ v ∈ D.paletteRows p, IsEvenRole v := by
    intro p v hv
    exact (Finset.mem_filter.mp hv).2.1
  let endpoints : Pos T k → Finset (Fin (T.S.N k)) := fun v =>
    insert (out.2 v).1 { (out.2 v).2 }
  let G : SimpleGraph (Pos T k) := {
    Adj v w := v ≠ w ∧ ((out.2 v).1 = (out.2 w).1 ∨ (out.2 v).1 = (out.2 w).2 ∨
      (out.2 v).2 = (out.2 w).1 ∨ (out.2 v).2 = (out.2 w).2)
    symm := by
      constructor
      intro v w h
      refine ⟨h.1.symm, ?_⟩
      rcases h.2 with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inr h.symm))
    loopless := by
      constructor
      intro v h
      exact h.1 rfl
  }
  have hGraphEq (S : Finset (Pos T k)) : endpointGraph S out.2 = G.induce (S : Set (Pos T k)) := by
    ext v w
    simp [endpointGraph, G]
  have endpointLeft (v : Pos T k) : (out.2 v).1 ∈ endpoints v := by
    change (out.2 v).1 ∈ insert (out.2 v).1 {(out.2 v).2}
    exact Finset.mem_insert_self _ _
  have endpointRight (v : Pos T k) : (out.2 v).2 ∈ endpoints v := by
    change (out.2 v).2 ∈ insert (out.2 v).1 {(out.2 v).2}
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have endpointChoice (v : Pos T k) {x : Fin (T.S.N k)} (hx : x ∈ endpoints v) :
      x = (out.2 v).1 ∨ x = (out.2 v).2 := by
    change x ∈ insert (out.2 v).1 {(out.2 v).2} at hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hOverlap : ∀ v w : Pos T k, G.Adj v w ↔
      v ≠ w ∧ (endpoints v ∩ endpoints w).Nonempty := by
    intro v w
    constructor
    · rintro ⟨hne, hshare⟩
      refine ⟨hne, ?_⟩
      rcases hshare with h | h | h | h
      · exact ⟨(out.2 v).1, Finset.mem_inter.mpr
          ⟨endpointLeft v, by rw [h]; exact endpointLeft w⟩⟩
      · exact ⟨(out.2 v).1, Finset.mem_inter.mpr
          ⟨endpointLeft v, by rw [h]; exact endpointRight w⟩⟩
      · exact ⟨(out.2 v).2, Finset.mem_inter.mpr
          ⟨endpointRight v, by rw [h]; exact endpointLeft w⟩⟩
      · exact ⟨(out.2 v).2, Finset.mem_inter.mpr
          ⟨endpointRight v, by rw [h]; exact endpointRight w⟩⟩
    · rintro ⟨hne, ⟨x, hxInter⟩⟩
      have hxv := (Finset.mem_inter.mp hxInter).1
      have hxw := (Finset.mem_inter.mp hxInter).2
      have hxv' := endpointChoice v hxv
      have hxw' := endpointChoice w hxw
      rcases hxv' with hxv | hxv <;> rcases hxw' with hxw | hxw
      · exact ⟨hne, Or.inl (hxv.symm.trans hxw)⟩
      · exact ⟨hne, Or.inr (Or.inl (hxv.symm.trans hxw))⟩
      · exact ⟨hne, Or.inr (Or.inr (Or.inl (hxv.symm.trans hxw)))⟩
      · exact ⟨hne, Or.inr (Or.inr (Or.inr (hxv.symm.trans hxw)))⟩
  have hGraphEq' (S : Finset (Pos T k)) :
      (endpointGraph S out.2).Connected ↔ (G.induce (S : Set (Pos T k))).Connected := by
    rw [hGraphEq S]
  let Rows : PaletteIndex D → Type := fun p => {v : Pos T k // v ∈ D.paletteRows p}
  have hForPalette : ∀ p : PaletteIndex D,
      ∃ m : Rows p → Fin (T.S.N k),
        Function.Injective m ∧ ∀ v, m v ∈ endpoints v.1 := by
    intro p
    let R := D.paletteRows p
    have hTwo : ∀ v ∈ R, 2 ≤ (endpoints v).card := by
      intro v hv
      have heven := rowEvent p v hv
      have hd := pairDistinct v heven
      simp [endpoints, hd]
    have hLarge : ∀ S : Finset (Pos T k), S ⊆ R → S.card = t₀ →
        (G.induce (S : Set (Pos T k))).Connected → False := by
      intro S hS hScard hSconn
      apply houtNoObstruction
      exact ⟨p, S, hS, (hGraphEq' S).2 hSconn, Or.inl hScard⟩
    have hSmall : ∀ S : Finset (Pos T k), S ⊆ R → 3 ≤ S.card → S.card < t₀ →
        (G.induce (S : Set (Pos T k))).Connected → ¬ (S.biUnion endpoints).card < S.card := by
      intro S hS h3 hlt hSconn hdef
      apply houtNoObstruction
      have hdef' : (endpointVertices S out.2).card < S.card := by
        simpa [endpointVertices, endpoints] using hdef
      exact ⟨p, S, hS, (hGraphEq' S).2 hSconn, Or.inr ⟨h3, hlt, hdef'⟩⟩
    have hHall := Lane_q_s18_n7.hall_condition_of_no_connected_obstruction
      G R endpoints t₀ ht hOverlap hTwo hLarge hSmall
    let I := Rows p
    have hHallI : ∀ S : Finset I, S.card ≤ (S.biUnion (fun v => endpoints v.1)).card := by
      intro S
      let Spos := S.image Subtype.val
      have hSsub : Spos ⊆ R := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
        exact x.2
      have hScard : Spos.card = S.card := by
        dsimp [Spos]
        exact Finset.card_image_of_injective S Subtype.val_injective
      have hUnion : S.biUnion (fun v => endpoints v.1) = Spos.biUnion endpoints := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
          exact Finset.mem_biUnion.mpr
            ⟨v.1, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
          rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
          exact Finset.mem_biUnion.mpr ⟨w, hw, hxv⟩
      calc
        S.card = Spos.card := hScard.symm
        _ ≤ (Spos.biUnion endpoints).card := hHall Spos hSsub
        _ = (S.biUnion (fun v => endpoints v.1)).card := by rw [hUnion]
    obtain ⟨m, hmInj, hmMem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun v : I => endpoints v.1)).mp hHallI
    exact ⟨m, hmInj, hmMem⟩
  let pick : ∀ p : PaletteIndex D, Rows p → Fin (T.S.N k) :=
    fun p => Classical.choose (hForPalette p)
  have pickSpec (p : PaletteIndex D) : Function.Injective (pick p) ∧
      ∀ v, pick p v ∈ endpoints v.1 := Classical.choose_spec (hForPalette p)
  have rowMem (v : {v : Pos T k // IsEvenRole v}) :
      v.1 ∈ D.paletteRows (D.rolePalette v.1) := by
    simp [LateData.paletteRows, LateData.rolePalette, v.2]
  let matching : {v : Pos T k // IsEvenRole v} → Fin (T.S.N k) := fun v =>
    pick (D.rolePalette v.1) ⟨v.1, rowMem v⟩
  have chosen (v : {v : Pos T k // IsEvenRole v}) :
      matching v = (out.2 v.1).1 ∨ matching v = (out.2 v.1).2 := by
    have hmem := (pickSpec (D.rolePalette v.1)).2 ⟨v.1, rowMem v⟩
    have hmem' : matching v ∈
        (insert (out.2 v.1).1 ({(out.2 v.1).2} : Finset (Fin (T.S.N k)))) := by
      simpa [matching, endpoints] using hmem
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem'
  have paletteInjective {v w : {v : Pos T k // IsEvenRole v}}
      (hp : D.rolePalette v.1 = D.rolePalette w.1) (hm : matching v = matching w) : v = w := by
    let p := D.rolePalette v.1
    let q := D.rolePalette w.1
    let rowV : Rows p := ⟨v.1, by simpa [p] using rowMem v⟩
    let rowW : Rows q := ⟨w.1, by simpa [q] using rowMem w⟩
    let rowVq : Rows q := Eq.mp (congrArg Rows hp) rowV
    have hm' : pick p rowV = pick q rowW := by
      simpa [matching, p, q, Rows, rowV, rowW] using hm
    have htransport := Lane_q_s18_n7.depFun_app_eq pick hp rowV
    have hrows : rowVq = rowW := (pickSpec q).1 (htransport.symm.trans hm')
    have hvalTransport : rowV.1 = rowVq.1 := by
      have h := Lane_q_s18_n7.depFun_app_eq
        (fun (q : PaletteIndex D) (x : Rows q) => x.1) hp rowV
      exact h
    have hpos : v.1 = w.1 := by
      calc
        v.1 = rowV.1 := rfl
        _ = rowVq.1 := hvalTransport
        _ = rowW.1 := congrArg Subtype.val hrows
        _ = w.1 := rfl
    exact Subtype.ext hpos
  refine ⟨{
    input := out.1.1
    history := out.1.2
    pairs := out.2
    full := houtFull
    pair_supported := pairSupported
    matching := matching
    chosen := chosen
    palette_injective := by
      intro v w hp hm
      exact paletteInjective hp hm
  }⟩

theorem L18_6 {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K Cp Cs : ℝ)
    (hK : 0 < K) (hCp : 0 < Cp) (hCs : 0 < Cs) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ δ εterm εrun, εrun ≤ 1 / 4 →
        ∀ C : TerminalCertificate D δ εterm, ∀ H : CompletionCertificate D C εrun,
          EndpointCertificate D C H K Cp Cs → Nonempty (HallCertificate D δ) := by
  obtain ⟨η, hη, hη1, _hslack, ha⟩ := L18_6a hκ T K Cp hK hCp
  obtain ⟨KH, hKH, hb⟩ := L18_6b hκ T K Cp Cs η hK hCp hCs hη hη1
  have hc := L18_6c hκ T η KH (Cs + 10) K hη hKH (by linarith) hK
  have hn : ∀ᶠ k in atTop, (3 : ℝ) / η + 1 ≤ (T.S.n k : ℝ) := by
    exact T.S.n_tendsto.eventually (eventually_atTop.2 ⟨⌈(3 : ℝ) / η + 1⌉₊, fun n hn =>
      le_trans (Nat.le_ceil _) (by exact_mod_cast hn)⟩)
  filter_upwards [ha, hb, hc, hn] with k ha hb hc hn
  intro PT hPT D hD δ εterm εrun hfull C H E
  have hbad := lt_of_le_of_lt (hb PT hPT D hD δ εterm εrun C H E
    (ha PT hPT D hD δ E.pair_facts)) (hc PT hPT D hD δ E.pair_facts)
  have ht : 3 ≤ ⌊η * (T.S.n k : ℝ)⌋₊ := by
    apply Nat.le_floor
    have hdiv : (3 : ℝ) / η ≤ (T.S.n k : ℝ) := by linarith
    have hmul := (div_le_iff₀ hη).mp hdiv
    norm_num at hmul ⊢
    nlinarith
  exact L18_6d D C H K E.pair_facts _ ht hfull hbad

/-- 18:1306–1310. Combine palette matchings using host disjointness, then
supply the actual odd labels and every edge from the final pair support. -/
theorem C18_Fcube {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) (δ K : ℝ) (hPair : PairInitialFacts D δ K)
    (H : HallCertificate D δ) : CubeIn T k PT.tiling.c := by
  have support (v : {v : Pos T k // IsEvenRole v}) :=
    (hPair.2.2.2.2 H.input H.history H.full v.1 v.2).2 (H.pairs v.1) (H.pair_supported v.1 v.2)
  have mem (v : {v : Pos T k // IsEvenRole v}) : H.matching v ∈ D.palette v.1 := by
    rcases H.chosen v with hv | hv
    · rw [hv]; exact (support v).2.1
    · rw [hv]; exact (support v).2.2.1
  have inj : Function.Injective H.matching := by
    intro v w hvw
    by_cases hp : D.rolePalette v.1 = D.rolePalette w.1
    · exact H.palette_injective v w hp hvw
    · have hd := D.palettes_global_disjoint (D.rolePalette v.1) (D.rolePalette w.1) hp
      have hm : H.matching v ∈ D.palette w.1 := by rw [hvw]; exact mem w
      exact False.elim ((Finset.disjoint_left.mp hd) (mem v) hm)
  apply cube_copy_of_parts H.matching (D.oddAt H.history) inj H.full.2.2.2.2.2.1
  intro v b hab
  have hedges := (support v).2.2.2 b hab
  rcases H.chosen v with hv | hv
  · rw [hv]; exact hedges.1
  · rw [hv]; exact hedges.2

/-- Internal low-mode assembly. The specific budgets chosen by C12.K are
needed to bound the adaptive broad laws, in addition to the full regime. -/
theorem C18_Flow {κ : CConsts} (hκ : κ.Admissible) (hThresholds : LateThresholds κ)
    (hConstants : ProducerConstants κ) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow → ProfileCornerMass PT → S16.Lane_sol_fix2_s16.SolverLabelsUniform PT → CubeIn T k PT.tiling.c := by
  obtain ⟨Kβ, _hKβ, hsched, hsmall⟩ := L18_0a hκ T
  obtain ⟨K27, hK27, hlocal⟩ := L18_1 hκ T
  obtain ⟨c1, hc1, htransfer⟩ := L18_2 hκ T hDisc K27 hK27
  let δ := min 0.04 c1 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ < min 0.04 c1 := by dsimp [δ]; have := lt_min (by norm_num : (0 : ℝ) < 0.04) hc1; linarith
  obtain ⟨εterm, hεterm, htermlim, hterminal⟩ := P18_3 hκ T K27 c1 δ hK27 hc1 hδ hδsmall
  obtain ⟨εrun, hεrun, hrunlim, hcompletion⟩ := P18_4 hκ T K27 c1 δ hK27 hc1 hδ hδsmall εterm htermlim
  obtain ⟨Krow, hKrow, hdata⟩ := D18_L hκ hThresholds T hInit hDeep hDisc hDiscι
  obtain ⟨K, Cp, Cs, hK, hCp, hCs, hendpoint⟩ := P18_5 hκ T K27 δ Krow hK27 hδ hKrow
  have hTermSmall : ∀ᶠ k in atTop, εterm k ≤ 1 := htermlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hRunSmall : ∀ᶠ k in atTop, εrun k ≤ 1 / 4 := hrunlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hSmall := hsmall (Real.log 2 / 1000) (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  filter_upwards [l16_quantitative_validity hκ hConstants T hInit hDeep hDisc, hdata,
    hsched, hSmall, hlocal, htransfer, hterminal, hcompletion, hendpoint, eventually_largeIndex κ T,
    L18_6 hκ T K Cp Cs hK hCp hCs, hTermSmall, hRunSmall] with
    k h16 hdata _hsched hSmall hLocal hTransfer hTerminal hCompletion hEndpoint hLarge hHall hTermSmall hRunSmall
  intro PT hPT hLow hCorners hUniform
  obtain ⟨⟨D0, hD0, hRows0⟩⟩ := hdata PT hPT hLow hCorners hLarge (h16 PT hPT hLow hCorners hUniform)
  obtain ⟨kernels, hD, hR, hBalance⟩ := P18_4a D0 hD0
  let D := D0.withKernels kernels
  have hRows : PaletteRowInput D Krow :=
    (Lane_sol_bridge_5d.paletteRowInput_withKernels D0 kernels Krow).2 hRows0
  have small := hSmall PT hPT hLow D.geom D.fresh D.l16_valid
  have localFacts := hLocal PT hPT D hD hR small
  have transfer := hTransfer PT hPT D hD hR localFacts small
  obtain ⟨C⟩ := hTerminal PT hPT D hD hR localFacts transfer
  obtain ⟨H⟩ := hCompletion PT hPT D hD hR hBalance localFacts transfer C
  have E := hEndpoint PT hPT D hD hRows hR localFacts (εterm k) (εrun k) hTermSmall C H
  obtain ⟨Hall⟩ := hHall PT hPT D hD δ (εterm k) (εrun k) hRunSmall C H E
  exact C18_Fcube D δ K E.pair_facts Hall

end HypercubeRamsey.S18
