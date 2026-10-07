import HypercubeRamsey.S18.Defs
import HypercubeRamsey.S18.Nodes_q_s18_dl
import HypercubeRamsey.S18.Nodes_q_s18_n4
import HypercubeRamsey.S18.Nodes_q_s18_n5
import HypercubeRamsey.S18.Nodes_q_s18_n1

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
50ρh consultation-centre margin. The general calibration and upstream
construction gaps recorded in `Needs` remain producer obligations. -/
theorem D18_L {κ : CConsts} (hκ : κ.Admissible) (hThresholds : LateThresholds κ) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, PT.tiling.mode.isLow → ProfileCornerMass PT → LargeIndex κ T k →
      (∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F) →
      Nonempty {D : LateData hPT // D.Spec} := by
  sorry

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
  sorry

/-- L18.0b, eq. (25). Finite smallness replaces impossible fixed-index
vanishing; the cap is on probability atoms, with no factor N. -/
theorem L18_0b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D →
      SmallErrors κ T k PT D.geom (Real.log 2 / 1000) → CurrentListCapFacts D := by
  sorry

/-- L18.1a, 18:171–194. Exponent .04 leaves slack below the derived .09. -/
theorem L18_1a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → CurrentListCapFacts D →
      ∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  sorry

/-- L18.1b, 18:195–223. Actual broad prefixes, same-side-data deletions,
and both single and pair versions of eq. (27); K27 is uniform. -/
theorem L18_1b {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ K27 : ℝ, 0 < K27 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → SmallErrors κ T k PT D.geom (Real.log 2 / 1000) →
        BroadDeletionFacts D K27 := by
  sorry

/-- L18.1c, 18:225–226. Bounds an intersection, not a success-conditioned law. -/
theorem L18_1c {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 : ℝ) (hK : 0 < K27) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TransitionData D → BroadDeletionFacts D K27 →
      ∀ j b h, D.gate j b.1 h → (D.encoding.kernels.refK j b h).pr
        (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  sorry

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
  sorry

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
  sorry

/-- L18.2a/i and 18:472–490, 630–645. Positive whole-cell survival and
both surviving-witness second moments. -/
theorem L18_2i {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        TransferGeometry X → SurvivalFacts X := by
  sorry

/-- L18.2j, 18:500–524. Cylinder identity for the actual adaptive recurrence. -/
theorem L18_2j {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) : CylinderFacts P := by
  sorry

/-- L18.2k/l, 18:526–615. The independent-witness likelihood process and
stopped moment/exception estimates are explicit. Choose cstop before stages. -/
theorem L18_2l {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∃ cstop : ℝ, 0 < cstop ∧ cstop < κ.xs / 4 ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → ∀ X : CriticalTransferData D, TransferGeometry X → SurvivalFacts X →
        ∀ P : TransferProtocol X, ReplyRangeBound P → CylinderFacts P → StopFacts P cstop := by
  sorry

/-- L18.2m, 18:617–628. An integrated tilted deviation estimate, not the
final unconditioned prefix-failure estimate. -/
theorem L18_2m {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) (cstop : ℝ) (hc : 0 < cstop) (hcx : cstop < κ.xs / 4) :
    ∃ ctilt : ℝ, 0 < ctilt ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → ∀ X : CriticalTransferData D, ∀ P : TransferProtocol X,
          StopFacts P cstop → TiltedDeviationBound P ctilt := by
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
  sorry

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
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1] with k hk
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
          exact Lane_q_s18_n4.upstreamBadPinnedBound D hD pin (.inl C) hk
      | inr v =>
          have hevent : terminalFailure D δ (.inl (.inr v)) = D.upstreamBad (.inr v) := by
            funext x
            simp [terminalFailure, LateData.poolListOK, LateData.freshConfigLaw,
              LateData.upstreamBad]
          rw [hevent]
          exact Lane_q_s18_n4.upstreamBadPinnedBound D hD pin (.inr v) hk
  | inr pair =>
      cases pair with
      | inl v => sorry
      | inr F => sorry

/-- P18.3c, 18:715–737. Forced replay advances overlapping scopes once. -/
theorem P18_3c {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) : ReplayFacts D :=
  Lane_q_s18_n4.replay_facts D

/-- P18.3e, 18:752–788. Leaves of the actual bad requirements, exact
slot/image/tape dependency, conditional pushforward and touching charges.
The prescribed `D.l16_valid.slot_eq` bounds leaf slot domains as well as cells. -/
theorem P18_3e {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → TerminalRiskBound D δ → Nonempty (LeafCoupling D δ) := by
  sorry

/-- P18.3f, 18:773–798. Positive *canonical* terminal event and a uniform
vanishing cost for every stated local nonnegative test. The slot-count
contract in `D.l16_valid` is retained for the local pool comparison. -/
theorem P18_3f {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
        ∀ D : LateData hPT, D.Spec → TerminalRiskBound D δ → LeafCoupling D δ →
          Nonempty (TerminalCertificate D δ (ε k)) := by
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
  obtain ⟨leaves⟩ := he PT hPT D hD risk
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
  sorry

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
  sorry

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
  apply Filter.Eventually.of_forall
  intro k PT hPT D hD hTransition
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa [Lane_q_s18_n5.paletteRows_eq_counted, LateData.paletteScale, densityScale,
      div_eq_mul_inv, mul_assoc]
      using (hD.palette_counts p.1 p.2).1
  · intro p
    simpa [Lane_q_s18_n5.paletteRows_eq_counted, LateData.paletteScale, densityScale]
      using (hD.palette_counts p.1 p.2).2
  · intro v
    sorry
  · intro S
    sorry
  · intro x h hfull v heven
    sorry

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
  sorry

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
  sorry

/-- P18.5d, 18:1058–1090. Bounds the explicitly defined isolate kernel. -/
theorem P18_5d {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ KI : ℝ, 1 ≤ KI ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → IsolateKernelFacts D KI := by
  refine ⟨1, by norm_num, ?_⟩
  apply Filter.Eventually.of_forall
  intro k PT hPT D hD v hv x z
  exact ⟨Lane_q_s18_n5.isolatedWeight_nonneg D v x z,
    Lane_q_s18_n5.isolatedWeight_symm D v x z, by
      sorry, by
      sorry⟩

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
  sorry

/-- P18.5f/g, 18:1126–1212. Calibrated label and group-bin comparisons,
reverse repeat summation and iid containment yield the actual query integral.
This includes k=0, for which the right side is one. -/
theorem P18_5f {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ A : InitialPairData D, ∀ Q : PairQueries D A,
        PairQueryBound D A Q := by
  sorry

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
  sorry

theorem P18_5 {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (K27 δ : ℝ)
    (hK : 0 < K27) (hδ : 0 < δ) :
    ∃ K Cprime Cstage : ℝ, 0 < K ∧ 0 < Cprime ∧ 0 < Cstage ∧ ∀ᶠ k in atTop,
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
        D.Spec → TransitionData D → LocalTransitionFacts D K27 →
        ∀ εterm εrun, εterm ≤ 1 → ∀ C : TerminalCertificate D δ εterm,
          ∀ H : CompletionCertificate D C εrun, EndpointCertificate D C H K Cprime Cstage := by
  obtain ⟨KP, hKP, ha⟩ := P18_5a hκ T δ hδ
  obtain ⟨KL, Cp, Cs, hKL, hCp, hCs, hb⟩ := P18_5b hκ T K27 δ hK hδ
  obtain ⟨KI, hKI, hd⟩ := P18_5d hκ T
  obtain ⟨CQ, hCQ, he⟩ := P18_5e hκ T
  obtain ⟨K, Cprime, Cstage, hK, hCp', hCs', hg⟩ :=
    P18_5g hκ T KP KL KI Cp Cs CQ hKP hKL hKI hCp hCs hCQ
  refine ⟨K, Cprime, Cstage, hK, hCp', hCs', ?_⟩
  filter_upwards [ha, hb, P18_5c hκ T, hd, he, P18_5f hκ T, hg] with k ha hb hc hd he hf hg
  intro PT hPT D hD hR hLocal εterm εrun hε C H
  apply hg PT hPT D hD δ εterm εrun hε C H (ha PT hPT D hD hR) (hd PT hPT D hD)
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
  sorry

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
  sorry

/-- L18.6c, 18:1289–1299. Sum all palettes/patches; C_n→∞ supplies the
negative linear exponent. The output spends a quarter of total mass. -/
theorem L18_6c {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (η K Cs Kpair : ℝ)
    (hη : 0 < η) (hK : 0 < K) (hCs : 0 < Cs) (hKP : 0 < Kpair) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ δ, PairInitialFacts D δ Kpair → HallBudget D η K Cs < 1 / 4 := by
  sorry

/-- L18.6d, 18:1301–1306. Full mass≥3/4 minus actual obstruction mass<1/4
leaves positive success and per-palette representatives. -/
theorem L18_6d {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    (D : LateData hPT) {δ εterm εrun : ℝ} (C : TerminalCertificate D δ εterm)
    (H : CompletionCertificate D C εrun) (K : ℝ) (hPair : PairInitialFacts D δ K)
    (t₀ : ℕ) (ht : 3 ≤ t₀) (hfull : εrun ≤ 1 / 4)
    (hbad : (pairExperiment D C H).pr (fun out => D.full δ out.1.1 out.1.2 ∧ HallObstruction D t₀ out.2) < 1 / 4) :
    Nonempty (HallCertificate D δ) := by
  sorry

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
  obtain ⟨K, Cp, Cs, hK, hCp, hCs, hendpoint⟩ := P18_5 hκ T K27 δ hK27 hδ
  have hTermSmall : ∀ᶠ k in atTop, εterm k ≤ 1 := htermlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hRunSmall : ∀ᶠ k in atTop, εrun k ≤ 1 / 4 := hrunlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hSmall := hsmall (Real.log 2 / 1000) (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  filter_upwards [l16_quantitative_validity hκ hConstants T hInit hDeep hDisc, D18_L hκ hThresholds T hInit hDeep hDisc hDiscι,
    hsched, hSmall, hlocal, htransfer, hterminal, hcompletion, hendpoint, eventually_largeIndex κ T,
    L18_6 hκ T K Cp Cs hK hCp hCs, hTermSmall, hRunSmall] with
    k h16 hdata _hsched hSmall hLocal hTransfer hTerminal hCompletion hEndpoint hLarge hHall hTermSmall hRunSmall
  intro PT hPT hLow hCorners hUniform
  obtain ⟨⟨D0, hD0⟩⟩ := hdata PT hPT hLow hCorners hLarge (h16 PT hPT hLow hCorners hUniform)
  obtain ⟨kernels, hD, hR, hBalance⟩ := P18_4a D0 hD0
  let D := D0.withKernels kernels
  have small := hSmall PT hPT hLow D.geom D.fresh D.l16_valid
  have localFacts := hLocal PT hPT D hD hR small
  have transfer := hTransfer PT hPT D hD hR localFacts small
  obtain ⟨C⟩ := hTerminal PT hPT D hD hR localFacts transfer
  obtain ⟨H⟩ := hCompletion PT hPT D hD hR hBalance localFacts transfer C
  have E := hEndpoint PT hPT D hD hR localFacts (εterm k) (εrun k) hTermSmall C H
  obtain ⟨Hall⟩ := hHall PT hPT D hD δ (εterm k) (εrun k) hRunSmall C H E
  exact C18_Fcube D δ K E.pair_facts Hall

end HypercubeRamsey.S18
