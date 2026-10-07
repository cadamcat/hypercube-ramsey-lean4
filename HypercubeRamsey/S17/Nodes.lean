import HypercubeRamsey.S17.Needs
import HypercubeRamsey.S17.Nodes_q_s17_pool
import HypercubeRamsey.S17.Nodes_sol_s17_pool
import HypercubeRamsey.S17.Nodes_q_s17_res1
import HypercubeRamsey.S17.Nodes_sol_s17_pool_experiment
import HypercubeRamsey.S17.Nodes_sol_s17_pool_mass
import HypercubeRamsey.S17.Nodes_sol_s17_compat

set_option maxHeartbeats 1000000

/-!
# Section 17 estimate and finite-resampling nodes

All analytic thresholds are chosen before the universally quantified local
data. Proof nodes remain placeholders in this repair lane; public exports
assemble their components without their own placeholders.
-/

namespace HypercubeRamsey

open Classical Filter
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

/-- Source witnesses use the exponents actually selected in `κ`. -/
def S17SourceFacts (κ : CConsts) (T : Stage) : Prop :=
  InitDisc T κ.η0 ∧ DeepDisc T κ.xs κ.α 0.04 ∧
    DeepDisc T κ.xι κ.αι (κ.ι / 2)

namespace ListGateContext

variable (D : ListGateContext κ T k PT)

/-- Validity conditions on a fixed pinned-list prior and its prescribed labels. -/
def PinnedPriorInput (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)) : Prop :=
  IsEvenRole v ∧ D.ValidInitialPrior v σ ∧
    pins ⊆ D.externalEarly v ∧ pins.card ≤ pinBudget κ ∧
    (D.pinnedPriorMass v σ pins fixed ≥
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)))

/-- Fixed-index form of L17.1, used as the input to the repeated-trial
argument in L17.2b. -/
def PinnedListEstimateAt (hN : 0 < T.S.N k) : Prop :=
  ∀ (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)),
    D.PinnedPriorInput v σ pins fixed →
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateBad v σ (D.labelsOfPinnedSample v hN ys)) ≤
      Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))

/-- Fixed-index form of the uniform pool estimate (eq:source-23). -/
def UniformPoolEstimateAt (v : Pos T k)
    (μ : FinLaw (ListGateContext.PoolAssignment D)) : Prop :=
  μ.pr (D.poolException v) ≤ Real.rpow (T.S.n k : ℝ)
    (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ) / 2))

end ListGateContext

/-- L17.1a: retained-mass failure, uniformly after one common index. -/
theorem independentPinnedMassFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
        (fixed : Pos T k → Fin (T.S.N k)),
        D.PinnedPriorInput v σ pins fixed →
        (D.pinnedLabelLaw v pins fixed).pr
          (fun ys => D.gateMassFailure v σ
            (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  sorry

/-- L17.1b: cleaned omitted-support failure, including bulk incidences. -/
theorem independentPinnedSupportFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
        (fixed : Pos T k → Fin (T.S.N k)),
        D.PinnedPriorInput v σ pins fixed →
        (D.pinnedLabelLaw v pins fixed).pr
          (fun ys => D.gateSupportFailure v
            (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  classical
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  have hPnat : 4 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hRnat : 0 < κ.R := by
    rw [hκ.R_eq]
    exact Nat.pow_pos (by omega)
  have hRpos : 0 < (κ.R : ℝ) := by exact_mod_cast hRnat
  have hA0 : 0 < κ.A0 := by
    have h := hκ.A0_big
    nlinarith
  let pinB : ℝ := (ListGateContext.pinBudget κ : ℝ)
  let Cbulk : ℝ := 2 + 2 * κ.A0 + K + pinB
  let Csmall : ℝ := 4 * Cbulk
  let Y0 : ℝ := Cbulk + 3 + 2 * K + 2 * (κ.R : ℝ)
  have hpinB : 0 ≤ pinB := by dsimp [pinB]; positivity
  have hCbulk : 1 ≤ Cbulk := by dsimp [Cbulk]; nlinarith [hA0, hK, hpinB]
  have hCbulkPos : 0 ≤ Cbulk := le_trans (by norm_num) hCbulk
  have hCbulkK : K ≤ Cbulk := by dsimp [Cbulk, pinB]; linarith
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hYpos : 1 ≤ Y0 := by dsimp [Y0]; nlinarith [hCbulk, hK, hRpos]
  have hlogSmall := Lane_q_s17_pool.eventually_log4_small T Csmall hCsmall
  have hlogT := Real.tendsto_log_atTop.comp hnT
  have hYevent := hlogT.eventually_ge_atTop Y0
  filter_upwards [hlogSmall, hYevent,
    T.S.n_tendsto.eventually_ge_atTop (2 : ℕ)] with k hsmall hY hk
  intro PT D hQuant v σ pins fixed hInput
  let n : ℕ := T.S.n k
  let nR : ℝ := T.S.n k
  let y : ℝ := Real.log nR
  have hnR : 0 < nR := by dsimp [nR]; exact_mod_cast (by omega : 0 < T.S.n k)
  have hy1 : 1 ≤ y := by
    have hY0 : 1 ≤ Y0 := hYpos
    exact hY0.trans (by simpa [y, nR] using hY)
  have hsmall' : Csmall * y ^ 4 ≤ nR / 4 := by
    simpa [y, nR] using hsmall
  have hY' : Cbulk + 3 + 2 * K + 2 * (κ.R : ℝ) ≤ y := by
    simpa [Y0, Cbulk, pinB, y] using hY
  rcases hInput with ⟨_, _, _, hpinCard, _⟩
  obtain ⟨B0, hB0ext, hB0patch, hB0lower, hB0upper, _hB0cross⟩ :=
    Lane_q_s17_pool.lowGeom_bulk_early_candidates D D.tiling_valid
      hQuant.geometry.ids_injective v
  have hExtCard := Lane_q_s17_pool.externalEarly_card_le D v
  let i := D.G.patchOf v
  let h := (PT.tiling.P i).h
  let ell := (PT.tiling.P i).ℓ
  let d : ℕ := ⌊y ^ 4⌋₊
  have hdReal : (d : ℝ) ≤ y ^ 4 := by
    dsimp [d]
    exact Nat.floor_le (by positivity)
  have hy2 : y ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hySq : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hy4sq : y ^ 2 ≤ y ^ 4 := by nlinarith [sq_nonneg (y ^ 2 - 1), hySq]
  have hy4 : y ≤ y ^ 4 := hy2.trans hy4sq
  have hhPow : Real.rpow y (1 / 10 : ℝ) ≤ y ^ 4 := by
    calc
      Real.rpow y (1 / 10 : ℝ) ≤ Real.rpow y 4 :=
        Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
      _ = y ^ 4 := by exact Real.rpow_natCast y 4
  have hhReal : (h : ℝ) ≤ y ^ 4 := by
    have hh := hQuant.geometry.height_bound i
    dsimp [h, y, nR] at hh ⊢
    exact hh.trans hhPow
  have hsqrt : Real.sqrt y ≤ y := by
    apply (Real.sqrt_le_left (by positivity)).2
    exact hy2
  have hellReal : (ell : ℝ) ≤ K * y ^ 4 := by
    have hell := hQuant.geometry.prefix_bound i
    dsimp [ell, y, nR] at hell ⊢
    calc
      (PT.tiling.P i).ℓ ≤ K * Real.sqrt (Real.log (T.S.n k : ℝ)) := hell
      _ ≤ K * y := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hK)
      _ ≤ K * y ^ 4 := mul_le_mul_of_nonneg_left hy4 (le_of_lt hK)
  have hrReal : (D.G.r : ℝ) ≤ 2 * κ.A0 * y ^ 4 := by
    have hr := hQuant.geometry.class_scale.2.le
    dsimp [y, nR] at hr ⊢
    calc
      (D.G.r : ℝ) ≤ 2 * κ.A0 * y := hr
      _ ≤ 2 * κ.A0 * y ^ 4 := mul_le_mul_of_nonneg_left hy4 (by positivity)
  have hy4one : 1 ≤ y ^ 4 := le_trans hy1 hy4
  have hpinReal : (ListGateContext.pinBudget κ : ℝ) ≤ pinB * y ^ 4 := by
    dsimp [pinB]
    have hpb : 0 ≤ (ListGateContext.pinBudget κ : ℝ) := by positivity
    simpa using mul_le_mul_of_nonneg_left hy4one hpb
  let loss : ℕ := h + ell + D.G.r + ListGateContext.pinBudget κ + d
  have hLossReal : (loss : ℝ) ≤ Cbulk * y ^ 4 := by
    dsimp [loss, Cbulk, pinB]
    push_cast
    nlinarith [hhReal, hellReal, hrReal, hpinReal, hdReal]
  have hCsmallBound : Cbulk * y ^ 4 ≤ nR / 16 := by
    dsimp [Csmall] at hsmall'
    nlinarith [hsmall']
  have hLossBound : (loss : ℝ) ≤ nR / 16 := hLossReal.trans hCsmallBound
  have hLossBoundN : (loss : ℝ) ≤ nR := by linarith
  have hLossNat : loss ≤ n := by
    have hLossBoundNat : (loss : ℝ) ≤ (n : ℝ) := by simpa [nR, n] using hLossBoundN
    exact_mod_cast hLossBoundNat
  have hbaseSum : h + ell + D.G.r + d ≤ n := by
    have hle : h + ell + D.G.r + d ≤ loss := by dsimp [loss]; omega
    omega
  have hB0size : d ≤ B0.card := by
    have hlow : n - (h + ell + D.G.r) ≤ B0.card := by
      simpa [n, h, ell, i, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB0lower
    omega
  have hExtD : d ≤ (D.externalEarly v).card :=
    le_trans hB0size (Finset.card_le_card hB0ext)
  let Family : Finset (Finset (Pos T k)) := (D.externalEarly v).powersetCard d
  have hFamilyCard : Family.card ≤ n ^ d := by
    dsimp [Family]
    rw [Finset.card_powersetCard]
    calc
      Nat.choose (D.externalEarly v).card d ≤ (D.externalEarly v).card ^ d :=
        Nat.choose_le_pow _ _
      _ ≤ n ^ d := by gcongr
  let a : ℝ := 1 / 2 + K * y / nR
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have hKy : K * y ≤ Cbulk * y ^ 4 := by
      calc
        K * y ≤ K * y ^ 4 := mul_le_mul_of_nonneg_left hy4 (le_of_lt hK)
        _ ≤ Cbulk * y ^ 4 := mul_le_mul_of_nonneg_right hCbulkK (by positivity)
    have hDiv : K * y / nR ≤ 1 / 4 := (div_le_iff₀ hnR).2 (by linarith [hKy, hCsmallBound])
    linarith
  have hdegree : ∀ x ∈ PT.envelope i,
      deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤ a := by
    intro x hx
    have hDrift := hQuant.geometry.degree_drift i x hx
    have hAbs : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ K * y / nR := by
      apply (le_div_iff₀ hnR).2
      dsimp [y, nR] at hDrift ⊢
      nlinarith [hDrift]
    dsimp [a]
    have := le_abs_self (deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2)
    linarith
  let μ : FinLaw (({w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k))) :=
    D.pinnedLabelLaw v pins fixed
  let threshold : ℝ := Real.exp (y ^ 8)
  let rho : ℝ := ((T.S.N k : ℝ) * a ^ (n - loss)) / threshold
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  have hFamilyBound : ∀ J' ∈ Family,
      μ.pr (fun ys => threshold <
        (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card) ≤ rho := by
    intro J' hJ'
    have hJprops := Finset.mem_powersetCard.mp hJ'
    have hJext : J' ⊆ D.externalEarly v := hJprops.1
    have hJcard : J'.card = d := hJprops.2
    let B : Finset (Pos T k) := B0 \ (pins ∪ J')
    have hBext : B ⊆ D.externalEarly v := by
      intro w hw
      exact hB0ext (Finset.mem_sdiff.mp hw).1
    have hBpatch : ∀ w ∈ B, D.G.patchOf w = D.G.patchOf v := by
      intro w hw
      exact hB0patch w (Finset.mem_sdiff.mp hw).1
    have hBavoid : ∀ w ∈ B, w ∉ pins ∧ w ∉ J' := by
      intro w hw
      have hnots := (Finset.mem_sdiff.mp hw).2
      constructor
      · intro hp
        exact hnots (Finset.mem_union_left _ hp)
      · intro hj
        exact hnots (Finset.mem_union_right _ hj)
    have hInter : (B0 ∩ (pins ∪ J')).card ≤ ListGateContext.pinBudget κ + d := by
      calc
        (B0 ∩ (pins ∪ J')).card ≤ (pins ∪ J').card :=
          Finset.card_le_card Finset.inter_subset_right
        _ ≤ pins.card + J'.card := Finset.card_union_le pins J'
        _ ≤ ListGateContext.pinBudget κ + d := by omega
    have hBcard : B.card = B0.card - (B0 ∩ (pins ∪ J')).card := by
      dsimp [B]
      rw [Finset.card_sdiff]
      rw [Finset.inter_comm]
    have hBsize : n - loss ≤ B.card := by
      rw [hBcard]
      have hlow : n - (h + ell + D.G.r) ≤ B0.card := by
        simpa [n, h, ell, i, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB0lower
      omega
    let f : ({w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) → ℝ := fun ys =>
      (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card
    have hf : ∀ ys, 0 ≤ f ys := by
      intro ys
      dsimp [f]
      exact_mod_cast (Nat.zero_le _)
    have hE : μ.E f ≤ (T.S.N k : ℝ) * a ^ B.card := by
      change (D.pinnedLabelLaw v pins fixed).E
        (fun ys => (D.omittedList v J'
          (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card) ≤ _
      exact Lane_q_s17_pool.pinned_support_expected_card_bound D v (T.S.N_pos k)
        pins J' B fixed hBext hBpatch hBavoid a (by positivity) hdegree
    have hpow : a ^ B.card ≤ a ^ (n - loss) :=
      pow_right_anti₀ ha0 ha1 hBsize
    have hEm : μ.E f ≤ (T.S.N k : ℝ) * a ^ (n - loss) := by
      calc
        μ.E f ≤ (T.S.N k : ℝ) * a ^ B.card := hE
        _ ≤ (T.S.N k : ℝ) * a ^ (n - loss) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    have hsubset : ∀ ys,
        threshold < (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card →
        threshold ≤ f ys := by intro ys h; simpa [f] using le_of_lt h
    have hmark : μ.pr (fun ys => threshold ≤ f ys) ≤ μ.E f / threshold := by
      exact Lane_q_s17_pool.pr_markov μ f threshold hf hthreshold
    calc
      μ.pr (fun ys => threshold <
          (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card) ≤
          μ.pr (fun ys => threshold ≤ f ys) := Lane_q_s17_pool.pr_mono μ hsubset
      _ ≤ μ.E f / threshold := hmark
      _ ≤ (T.S.N k : ℝ) * a ^ (n - loss) / threshold :=
        div_le_div_of_nonneg_right hEm hthreshold.le
      _ = rho := rfl
  have hcover : ∀ ys,
      D.gateSupportFailure v (D.labelsOfPinnedSample v (T.S.N_pos k) ys) →
      ∃ J' ∈ Family, threshold <
        (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card := by
    intro ys hbad
    rcases hbad with ⟨J, hJext, hJsize, hJlarge⟩
    have hJreal : (J.card : ℝ) ≤ y ^ 4 := by
      have hJsize' : (J.card : ℝ) ≤ Real.rpow y (4 : ℝ) := by
        change (J.card : ℝ) ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (4 : ℝ)
        exact hJsize
      exact hJsize'.trans (le_of_eq (Real.rpow_natCast y 4))
    have hJnat : J.card ≤ d := Nat.le_floor hJreal
    obtain ⟨J', hJJ', hJ'ext, hJ'card⟩ :=
      Finset.exists_subsuperset_card_eq hJext hJnat hExtD
    have hJmem : J' ∈ Family := by
      change J' ∈ (D.externalEarly v).powersetCard d
      exact Finset.mem_powersetCard.mpr ⟨hJ'ext, hJ'card⟩
    have hList : D.omittedList v J (D.labelsOfPinnedSample v (T.S.N_pos k) ys) ⊆
        D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys) := by
      intro z hz
      unfold ListGateContext.omittedList at hz ⊢
      rcases Finset.mem_filter.mp hz with ⟨_, ⟨hzenv, hhits⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hzenv, ?_⟩
      intro w hw
      have hw0 := Finset.mem_sdiff.mp hw
      have hwOld : w ∈ D.externalEarly v \ J := by
        refine Finset.mem_sdiff.mpr ⟨hw0.1, ?_⟩
        intro hJw
        exact hw0.2 (hJJ' hJw)
      exact hhits w hwOld
    have hcard : (D.omittedList v J (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card ≤
        (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card :=
      Finset.card_mono hList
    refine ⟨J', hJmem, ?_⟩
    have hJlarge' : Real.exp (y ^ 8) <
        (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card := by
      have hpow8 : Real.rpow y (8 : ℝ) = y ^ 8 := Real.rpow_natCast y 8
      have hJlarge'' : Real.exp (Real.rpow y (8 : ℝ)) <
          (D.omittedList v J (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card := by
        change Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) (8 : ℝ)) <
          (D.omittedList v J (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card
        exact hJlarge
      rw [hpow8] at hJlarge''
      exact lt_of_lt_of_le hJlarge''
        (by exact_mod_cast hcard)
    simpa [threshold] using hJlarge'
  have hUnion := Lane_q_s17_pool.support_failure_from_union_bound μ Family
    (fun J' ys => threshold <
      (D.omittedList v J' (D.labelsOfPinnedSample v (T.S.N_pos k) ys)).card)
    (fun ys => D.gateSupportFailure v (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
    hcover rho hFamilyBound
  have hFamilyNat : Family.card ≤ n ^ d := by
    dsimp [Family]
    rw [Finset.card_powersetCard]
    calc
      Nat.choose (D.externalEarly v).card d ≤ (D.externalEarly v).card ^ d :=
        Nat.choose_le_pow _ _
      _ ≤ n ^ d := by gcongr
  have hFamilyReal : (Family.card : ℝ) ≤ (n : ℝ) ^ d := by exact_mod_cast hFamilyNat
  have hRnonneg : 0 ≤ rho := by dsimp [rho, threshold, a]; positivity
  have hNumeric := Lane_q_s17_pool.support_union_numerical_bound
    (n := n) (N := T.S.N k) (m := n - loss) (d := d) (loss := loss)
    (K := K) (C := Cbulk) (R := (κ.R : ℝ)) (y := y)
    (by exact_mod_cast (by omega : 0 < n)) hy1 (by rfl)
    (le_of_lt hK) hCbulkPos hCbulkK (by nlinarith [hsmall'])
    (T.S.N_le k) (Nat.sub_le _ _) (by omega) hLossReal hdReal
    hRpos.le hY'
  calc
    μ.pr (fun ys => D.gateSupportFailure v
      (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
        (Family.card : ℝ) * rho := hUnion
    _ ≤ (n : ℝ) ^ d * rho :=
      mul_le_mul_of_nonneg_right hFamilyReal hRnonneg
    _ = ((n : ℝ) ^ d * (T.S.N k : ℝ) * a ^ (n - loss)) /
        Real.exp (y ^ 8) := by simp [rho, threshold, n, a]; ring
    _ ≤ (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
      simpa [a, n, neg_mul] using hNumeric

/-- L17.1 export: eventual independent pinned-label estimate. -/
theorem independentPinnedList
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      D.PinnedListEstimateAt (T.S.N_pos k) := by
  filter_upwards [independentPinnedMassFailure κ hκ T hSource K hK,
    independentPinnedSupportFailure κ hκ T hSource K hK] with k hm hs
  intro PT D hQuant v σ pins fixed hInput
  have hu := FinLaw.pr_or_le (D.pinnedLabelLaw v pins fixed)
    (fun ys => D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
    (fun ys => D.gateSupportFailure v (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
  change (D.pinnedLabelLaw v pins fixed).pr
    (fun ys => D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys) ∨
      D.gateSupportFailure v (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) +
        (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) :=
      hu.trans (add_le_add (hm PT D hQuant v σ pins fixed hInput)
        (hs PT D hQuant v σ pins fixed hInput))
    _ = _ := by ring

/-- L17.2a: compatibility at an even star; raw or one-pin pool law. -/
theorem poolCompatibilityFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (v : Pos T k), IsEvenRole v →
        ∀ μ : FinLaw D.PoolAssignment,
          D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ →
          μ.pr (D.compatibilityFailure v) ≤ Real.rpow (T.S.n k : ℝ)
            (-((κ.R : ℝ) * initialResamplingRounds T k)) := by
  sorry

/-- The L17.2b trial moment at fixed pools. -/
noncomputable def poolTrialMoment
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (μ : FinLaw (ListGateContext.PoolAssignment D)) : ℝ :=
  μ.E fun pools =>
    if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ initialResamplingRounds T k
    else 0

/-- L17.2b: repeated-trial moment using actual slots, permissions, and fresh priors. -/
theorem uniformPoolTrialsMoment
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      D.PinnedListEstimateAt (T.S.N_pos k) →
      ∀ (v : Pos T k) (μ : FinLaw D.PoolAssignment),
        D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ →
        poolTrialMoment D v μ ≤ 2 * Real.rpow (T.S.n k : ℝ)
          (-((κ.R : ℝ) * initialResamplingRounds T k)) := by
  sorry

/-- L17.2c: Markov assembly; odd roles have identically false list events. -/
theorem uniformPoolMarkov
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (v : Pos T k) (μ : FinLaw D.PoolAssignment),
        D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ →
        (IsEvenRole v → μ.pr (D.compatibilityFailure v) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k))) →
        poolTrialMoment D v μ ≤ 2 * Real.rpow (T.S.n k : ℝ)
          (-((κ.R : ℝ) * initialResamplingRounds T k)) →
        μ.pr (fun pools => ¬ D.LocalPoolsTypical v pools) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k)) →
        D.UniformPoolEstimateAt v μ := by
  classical
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2] with k hk
  intro PT D hQuant v μ hμ hCompat hMoment hTypical
  let n : ℝ := T.S.n k
  let m : ℕ := initialResamplingRounds T k
  let R : ℝ := κ.R
  let P : ℝ := κ.P
  have hn : 2 ≤ n := by
    dsimp [n]
    exact_mod_cast hk
  have hn1 : (1 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hmpos : 0 < m := by
    dsimp [m, initialResamplingRounds]
    apply Nat.ceil_pos.mpr
    exact sq_pos_of_pos hlog
  have hmNat : 1 ≤ m := Nat.succ_le_of_lt hmpos
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hPnat : 4 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hPreal : (4 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast hPnat
  have hRpow : R = P ^ 2 := by
    dsimp [R, P]
    exact_mod_cast hκ.R_eq
  have hRhalf : 3 ≤ R / 2 := by
    rw [hRpow]
    nlinarith [sq_nonneg (P - 4)]
  have hRgap : 3 ≤ R / 2 - P := by
    rw [hRpow]
    nlinarith [sq_nonneg (P - 4)]
  have hmR : 3 ≤ R * (m : ℝ) / 2 := by
    calc
      3 ≤ R / 2 := hRhalf
      _ = (R / 2) * 1 := by ring
      _ ≤ (R / 2) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm (by linarith [hRhalf])
      _ = R * (m : ℝ) / 2 := by ring
  have hmGap : 3 ≤ (R / 2 - P) * (m : ℝ) := by
    calc
      3 ≤ R / 2 - P := hRgap
      _ = (R / 2 - P) * 1 := by ring
      _ ≤ (R / 2 - P) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm (by linarith [hRgap])
  have hnumeric := Lane_q_s17_pool.pool_tail_numeric hn hmR hmGap
  have hqnonneg : 0 ≤ Real.rpow n (-(R * (m : ℝ))) :=
    Real.rpow_nonneg (by linarith [hn]) _
  have htyp := hTypical
  change μ.pr (fun pools => ¬ (D.LocalPoolsTypical v pools ∧
      D.freshEventProbability v pools ≤ Real.rpow n (-P))) ≤
    Real.rpow n (-(R * (m : ℝ) / 2))
  by_cases heven : IsEvenRole v
  · let q : ℝ := Real.rpow n (-(R * (m : ℝ)))
    let b : ℝ := Real.rpow n (-P)
    let good : D.PoolAssignment → Prop := fun pools =>
      D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools
    let f : D.PoolAssignment → ℝ := fun pools =>
      if good pools then (D.freshEventProbability v pools) ^ m else 0
    let atypical : D.PoolAssignment → Prop := fun pools =>
      ¬ D.LocalPoolsTypical v pools
    let incompatible : D.PoolAssignment → Prop := fun pools =>
      D.compatibilityFailure v pools
    let large : D.PoolAssignment → Prop := fun pools =>
      good pools ∧ b < D.freshEventProbability v pools
    have hb : 0 < b := by
      dsimp [b]
      exact Real.rpow_pos_of_pos (by linarith [hn]) _
    have hbpow : 0 < b ^ m := by positivity
    have hprob_nonneg (pools : D.PoolAssignment) :
        0 ≤ D.freshEventProbability v pools := by
      unfold ListGateContext.freshEventProbability FinLaw.pr
      apply Finset.sum_nonneg
      intro pools' hpools'
      by_cases hevent : D.event v pools'
      · simpa [hevent] using (D.freshConfigLaw pools).nonneg pools'
      · simp [hevent]
    have hfnonneg : ∀ pools, 0 ≤ f pools := by
      intro pools
      dsimp [f]
      split_ifs
      · exact pow_nonneg (hprob_nonneg pools) _
      · exact le_rfl
    have hfexpect : μ.E f = poolTrialMoment D v μ := by
      rfl
    have hfbound : μ.E f ≤ 2 * q := by
      rw [hfexpect]
      simpa [q, R, m, n] using hMoment
    have hlarge_subset : ∀ pools, large pools → b ^ m ≤ f pools := by
      intro pools hpools
      rcases hpools with ⟨hgood, hlarge⟩
      rcases hgood with ⟨htyp, hcompatible⟩
      dsimp [f, good]
      rw [if_pos ⟨htyp, hcompatible⟩]
      have hpow : b ^ m ≤ (D.freshEventProbability v pools) ^ m := by
        induction m with
        | zero => simp
        | succ m ih =>
            rw [pow_succ, pow_succ]
            exact mul_le_mul ih (le_of_lt hlarge)
              (le_of_lt hb) (pow_nonneg (hprob_nonneg pools) _)
      exact hpow
    have hlargeMarkov : μ.pr large ≤ μ.E f / (b ^ m) := by
      calc
        μ.pr large ≤ μ.pr (fun pools => b ^ m ≤ f pools) :=
          Lane_q_s17_pool.pr_mono μ hlarge_subset
        _ ≤ μ.E f / (b ^ m) :=
          Lane_q_s17_pool.pr_markov μ f (b ^ m) hfnonneg hbpow
    have hquot : q / (b ^ m) = Real.rpow n (-((R - P) * (m : ℝ))) := by
      dsimp [q, b]
      exact Lane_q_s17_pool.rpow_quotient (by linarith [hn])
    have hlargeBound : μ.pr large ≤
        2 * Real.rpow n (-((R - P) * (m : ℝ))) := by
      calc
        μ.pr large ≤ μ.E f / (b ^ m) := hlargeMarkov
        _ ≤ (2 * q) / (b ^ m) :=
          div_le_div_of_nonneg_right hfbound (le_of_lt hbpow)
        _ = 2 * (q / (b ^ m)) := by ring
        _ = 2 * Real.rpow n (-((R - P) * (m : ℝ))) := by rw [hquot]
    have hcover : ∀ pools,
        ¬ (D.LocalPoolsTypical v pools ∧
          D.freshEventProbability v pools ≤ b) →
        (¬ D.LocalPoolsTypical v pools ∨
          (D.compatibilityFailure v pools ∨ large pools)) := by
      intro pools hbad
      by_cases htyp : D.LocalPoolsTypical v pools
      · by_cases hcompatible : D.compatiblePool v pools
        · right
          right
          refine ⟨⟨htyp, hcompatible⟩, ?_⟩
          exact lt_of_not_ge (fun hle => hbad ⟨htyp, hle⟩)
        · right
          left
          exact ⟨htyp, hcompatible⟩
      · exact Or.inl htyp
    have hdecomp : μ.pr (fun pools =>
        ¬ (D.LocalPoolsTypical v pools ∧
          D.freshEventProbability v pools ≤ b)) ≤
        μ.pr atypical + (μ.pr incompatible + μ.pr large) := by
      calc
        _ ≤ μ.pr (fun pools => atypical pools ∨
            (incompatible pools ∨ large pools)) :=
          Lane_q_s17_pool.pr_mono μ hcover
        _ ≤ μ.pr atypical + μ.pr (fun pools => incompatible pools ∨ large pools) :=
          FinLaw.pr_or_le μ atypical (fun pools => incompatible pools ∨ large pools)
        _ ≤ μ.pr atypical + (μ.pr incompatible + μ.pr large) :=
          by
            gcongr
            exact FinLaw.pr_or_le μ incompatible large
    have hatypBound : μ.pr atypical ≤ q := by
      simpa [atypical, q, R, m, n] using htyp
    have hincBound : μ.pr incompatible ≤ q := by
      simpa [incompatible, q, R, m, n] using hCompat heven
    calc
      μ.pr (fun pools =>
          ¬ (D.LocalPoolsTypical v pools ∧
            D.freshEventProbability v pools ≤ b)) ≤
          μ.pr atypical + (μ.pr incompatible + μ.pr large) := hdecomp
      _ ≤ q + (q + 2 * Real.rpow n (-((R - P) * (m : ℝ)))) :=
          add_le_add hatypBound (add_le_add hincBound hlargeBound)
      _ = 2 * q + 2 * Real.rpow n (-((R - P) * (m : ℝ))) := by ring
      _ ≤ Real.rpow n (-(R * (m : ℝ) / 2)) := by
        simpa [q, R] using hnumeric
  · have hprobzero (pools : D.PoolAssignment) :
        D.freshEventProbability v pools = 0 := by
      unfold ListGateContext.freshEventProbability FinLaw.pr
      apply Finset.sum_eq_zero
      intro pools' hpools'
      simp [ListGateContext.event, heven]
    have hexception :
        (fun pools => ¬ (D.LocalPoolsTypical v pools ∧
          D.freshEventProbability v pools ≤ Real.rpow n (-P))) =
        (fun pools => ¬ D.LocalPoolsTypical v pools) := by
      funext pools
      have hthreshold : 0 ≤ Real.rpow n (-P) := Real.rpow_nonneg (by linarith [hn]) _
      apply propext
      rw [hprobzero pools]
      constructor
      · intro h htyp
        exact h ⟨htyp, hthreshold⟩
      · intro h hsuccess
        exact h hsuccess.1
    rw [hexception]
    have hnumeric' : Real.rpow n (-(R * (m : ℝ))) ≤
        Real.rpow n (-(R * (m : ℝ) / 2)) := by
      have hrest : 0 ≤ 2 * Real.rpow n (-((R - P) * (m : ℝ))) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [hn]) _)
      linarith [hnumeric, hqnonneg, hrest]
    simpa [R, m, n] using le_trans htyp hnumeric'

/-- L17.2 export: uniform raw/pinned pool estimate; consumes the L17.1 producer. -/
theorem uniformPoolListEstimate
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (v : Pos T k) (μ : FinLaw D.PoolAssignment),
        D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ →
        D.UniformPoolEstimateAt v μ := by
  filter_upwards [independentPinnedList κ hκ T hSource K hK,
    poolCompatibilityFailure κ hκ T hSource K hK,
    uniformPoolTrialsMoment κ hκ T hSource K hK,
    uniformPoolMarkov κ hκ T hSource K hK] with k hl hc ht hm
  intro PT D hQuant v μ hμ
  apply hm PT D hQuant v μ hμ
  · intro heven
    exact hc PT D hQuant v heven μ hμ
  · exact ht PT D hQuant (hl PT D hQuant) v μ hμ
  · rcases hμ with hraw | ⟨pin, hpin, hpinned⟩
    · simpa [hraw] using hQuant.pool_typical_tail v
    · simpa [hpinned] using hQuant.pool_typical_tail_pinned v pin hpin

/-- Internal Hamming weight of a binary word. -/
noncomputable def internalWeight {h : ℕ} (z : Fin h → ZMod 2) : ℕ :=
  (Finset.univ.filter fun j => z j ≠ 0).card

/-- Convenient fully-qualified names for the Section 17 linear palette data. -/
abbrev S17PaletteCode (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k) :=
  ListGateContext.PaletteCode i hle

abbrev S17PaletteAssignment {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k}
    (ψ : S17PaletteCode i hle) := ListGateContext.PaletteAssignment ψ

def s17Chi {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k}
    (ψ : S17PaletteCode i hle) : ℕ := ListGateContext.PaletteCode.chi ψ

noncomputable def s17Palette {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k} (ψ : S17PaletteCode i hle)
    (colours : S17PaletteAssignment ψ) (v : Pos T k) : Finset (Fin (T.S.N k)) :=
  ListGateContext.PaletteCode.palette ψ colours v

/-- L17.3(i): the linear code is onto, has no short nonzero kernel word,
and gives equal colour-class sizes on the even roles of the patch. -/
def PaletteCodeSpec
    (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle) : Prop :=
  Function.Surjective ψ.map ∧
  (∀ z, ψ.map z = 0 → z ≠ 0 →
    (internalWeight z : ℝ) ≤ 500 * κ.ρ * (PT.tiling.P i).h → False) ∧
  (∀ c₁ c₂ : Fin ψ.dimension → ZMod 2,
    (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₁).card =
    (Finset.univ.filter fun v : Pos T k =>
      v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₂).card) ∧
  (s17Chi ψ : ℝ) ≤ Real.exp (PT.tiling.gain i)

/-- L17.3(ii): simultaneous palette size, list-row retention, and prior-mass
bounds for all valid local histories and priors. -/
def PaletteRetentionSpec
    (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle)
    (colours : S17PaletteAssignment ψ) : Prop :=
  (∀ c : Fin ψ.dimension → ZMod 2,
    ((Finset.univ.filter fun x : Fin (T.S.N k) =>
      x ∈ (PT.tiling.P i).X ∧ colours x = c).card : ℝ) ≤
      2 * (PT.tiling.P i).M / (s17Chi ψ : ℝ)) ∧
  (∀ (pools : ∀ C : D.G.Cell, D.F.Pool C) (s : Config D.F)
      (v : Pos T k),
    (∀ C ∈ D.scopeCells v, D.F.typical C (pools C)) →
    (∀ C ∈ D.scopeCells v, D.stateValid C (pools C) (s C)) →
    v ∈ PT.tiling.leaf i → IsEvenRole v →
    (1 / 2 : ℝ) ≤ D.rowMass v (D.prior s v) (D.label s) →
      1 / (4 * (s17Chi ψ : ℝ)) ≤
      ∑ x ∈ s17Palette ψ colours v, D.row v (D.prior s v) (D.label s) x) ∧
  (∀ v : Pos T k, v ∈ PT.tiling.leaf i → IsEvenRole v →
    ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
    ∀ c : Fin ψ.dimension → ZMod 2,
    ∑ x ∈ (Finset.univ.filter fun x => x ∈ (PT.tiling.P i).X ∧ colours x = c),
      σ x ≤ 2 / (s17Chi ψ : ℝ))

/-- The normalized pair factor `R_j(x,z)` in eq:source-24. -/
noncomputable def externalPairFactor
    (j : Fin PT.tiling.m)
    (x z : Fin (T.S.N k)) : ℝ :=
  (∑ y, (PT.π j).w y * hit (T.S.E k) PT.tiling.c x y *
    hit (T.S.E k) PT.tiling.c z y) /
    (deg (T.S.E k) PT.tiling.c (PT.π j).w x *
      deg (T.S.E k) PT.tiling.c (PT.π j).w z)

/-- L17.3(iii), eq:source-24: the low-correlation row tail on each assigned
palette. -/
def PalettePairRowBound
    (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle)
    (colours : S17PaletteAssignment ψ) (Kpair : ℝ) : Prop :=
  ∀ v : Pos T k, v ∈ PT.tiling.leaf i → IsEvenRole v →
    ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
      ∀ x ∈ PT.envelope i,
        ∑ z ∈ s17Palette ψ colours v,
          (if |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
            σ z * ∏ w ∈ D.externalEarly v,
              externalPairFactor (D.G.patchOf w) x z
           else 0) ≤ Kpair / (s17Chi ψ : ℝ)

/-- L17.3(iv): the unconditioned uniform pair moment on the patch support. -/
def PalettePairMomentBound
    (i : Fin PT.tiling.m)
    (hX : (PT.tiling.P i).X.Nonempty) (Kmoment : ℝ) : Prop :=
  ∀ d : ℕ, d ≤ T.S.n k →
    (FinLaw.pi fun _ : Fin 2 => FinLaw.uniform (PT.tiling.P i).X hX).E
      (fun ω => if ω 0 ∈ PT.envelope i ∧ ω 1 ∈ PT.envelope i ∧
        |corr (T.S.E k) PT.tiling.c (PT.π i).w (ω 0) (ω 1)| ≤ κ.ξ then
        (4 * (∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c (ω 0) y *
          hit (T.S.E k) PT.tiling.c (ω 1) y)) ^ (2 * d)
       else 0) ≤ Real.exp (Kmoment * Real.log (T.S.n k : ℝ))

/-- Late-neighbour count at an even star, including the internal dummy. -/
noncomputable def initialLateCount (D : ListGateContext κ T k PT) (v : Pos T k) : ℕ :=
  (Finset.univ.filter fun j : Fin (T.S.n k) =>
    (D.G.classOf (flipPos v j)).isSome).card

/-- Deterministic atom estimate used in palette concentration. `Katom` is
fixed before all local data; `2^n/N` is the inverse host ratio. -/
def InitialAtomBound (D : ListGateContext κ T k PT) (Katom : ℝ) : Prop :=
  ∀ (v : Pos T k) (pools : D.PoolAssignment) (s : Config D.F),
    IsEvenRole v → D.LocalPoolsTypical v pools →
    (∀ C ∈ D.scopeCells v, D.stateValid C (pools C) (s C)) →
    ∀ x, D.row v (D.prior s v) (D.label s) x ≤
      Katom * (2 : ℝ) ^ T.S.n k / T.S.N k *
        Real.exp (-200 * PT.tiling.gain (D.G.patchOf v)) *
          Real.rpow 2 (-(initialLateCount D v : ℝ))

/-- L17.1 deterministic cap/degree calculation, consumed by palette retention.
The fixed constant is existential before the index, tiling, and sampler. -/
theorem initialRowAtomBound
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∃ Katom : ℝ, 0 < Katom ∧ ∀ᶠ k in atTop,
      ∀ (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT),
        D.L16QuantitativeValidity K → InitialAtomBound D Katom := by
  sorry

/-- L17.3(i): binary separating code; a free outer bit supplies equal even classes. -/
theorem lowModePaletteCode
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      ∀ (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k),
        (∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
          j.val < T.S.n k - (PT.tiling.P i).h) →
        ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ := by
  sorry

/-- L17.3(ii): one label colouring for every fixed valid-history readout. -/
theorem lowModePaletteRetention
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K)
    (Katom : ℝ) (hAtomPos : 0 < Katom) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hQuant : D.L16QuantitativeValidity K),
      InitialAtomBound D Katom →
      ∀ (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
        (ψ : S17PaletteCode i hle), PaletteCodeSpec i hle ψ →
        ∃ colours : S17PaletteAssignment ψ, PaletteRetentionSpec D i hle ψ colours := by
  sorry

/-- L17.3(iii): pair-tail bound. The paper's unspecified fixed constant
is existential before the index; it is not the low-mode cutoff `κ.KB`. -/
theorem lowModePalettePairRow
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∃ Kpair : ℝ, 0 < Kpair ∧ ∀ᶠ k in atTop,
      ∀ (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
        (hQuant : D.L16QuantitativeValidity K)
        (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
        (ψ : S17PaletteCode i hle), PaletteCodeSpec i hle ψ →
        ∀ colours : S17PaletteAssignment ψ,
          PaletteRetentionSpec D i hle ψ colours →
          PalettePairRowBound D i hle ψ colours Kpair := by
  sorry

/-- L17.3(iv): unconditioned uniform-pair integral with cleaned-envelope
indicator and a fixed moment constant chosen before the index. -/
theorem lowModePalettePairMoment
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∃ Kmoment : ℝ, 0 < Kmoment ∧ ∀ᶠ k in atTop,
      ∀ (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
        (hQuant : D.L16QuantitativeValidity K)
        (i : Fin PT.tiling.m) (hX : (PT.tiling.P i).X.Nonempty),
        PalettePairMomentBound i hX Kmoment := by
  sorry

/-- L17.3 export: constants are fixed for all patches and histories after
the common eventual index. All code/atom/retention/pair nodes are consumed. -/
theorem lowModePalettes
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∃ Kpair Kmoment : ℝ, 0 < Kpair ∧ 0 < Kmoment ∧ ∀ᶠ k in atTop,
      ∀ (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
        (hQuant : D.L16QuantitativeValidity K)
        (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k),
        (∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
          j.val < T.S.n k - (PT.tiling.P i).h) →
        ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ ∧
          ∃ colours : S17PaletteAssignment ψ,
            PaletteRetentionSpec D i hle ψ colours ∧
            PalettePairRowBound D i hle ψ colours Kpair ∧
              PalettePairMomentBound i (D.patchXNonempty i) Kmoment := by
  obtain ⟨Katom, hAtomPos, hAtom⟩ := initialRowAtomBound κ hκ T hSource K hK
  obtain ⟨Kpair, hPairPos, hPair⟩ := lowModePalettePairRow κ hκ T hSource K hK
  obtain ⟨Kmoment, hMomentPos, hMoment⟩ := lowModePalettePairMoment κ hκ T hSource K hK
  refine ⟨Kpair, Kmoment, hPairPos, hMomentPos, ?_⟩
  filter_upwards [hAtom, lowModePaletteCode κ hκ T hSource K hK,
    lowModePaletteRetention κ hκ T hSource K hK Katom hAtomPos,
    hPair, hMoment] with k ha hc hr hp hm
  intro PT D hQuant i hle hfree
  obtain ⟨ψ, hCode⟩ := hc PT D hQuant i hle hfree
  obtain ⟨colours, hRetention⟩ := hr PT D hQuant (ha PT D hQuant) i hle ψ hCode
  exact ⟨ψ, hCode, colours, hRetention,
    hp PT D hQuant i hle ψ hCode colours hRetention,
    hm PT D hQuant i (D.patchXNonempty i)⟩

/-- Sites executing in a specified round. -/
noncomputable def activeAtRound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : Tapes D.F Ts) (r : Fin Ts) : Finset (Pos T k) :=
  LE.active order events (LE.runRounds r.val order events pools tapes.extend).1

/-- One possible execution occurrence in a `Ts`-round process. -/
abbrev ExecutionOccurrence (T : Stage) (k Ts : ℕ) := Pos T k × Fin Ts

/-- An occurrence is executed when its event belongs to that round's selected
set. -/
def occurrenceExecuted
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (o : ExecutionOccurrence T k Ts) : Prop :=
  o.1 ∈ activeAtRound LE Ts order events pools tapes o.2

/-- Backward dependence between execution occurrences: the earlier event is
adjacent in the scope graph to a later one. -/
def backwardOccurrenceEdge
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (later earlier : ExecutionOccurrence T k Ts) : Prop :=
  occurrenceExecuted LE Ts order events pools tapes later ∧
    occurrenceExecuted LE Ts order events pools tapes earlier ∧
    earlier.2.val < later.2.val ∧ ¬ Disjoint (LE.scope later.1) (LE.scope earlier.1)

/-- Executed occurrences in the target cells' backward closure. -/
noncomputable def backwardClosure
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (targets : Finset D.G.Cell) : Finset (ExecutionOccurrence T k Ts) :=
  Finset.univ.filter fun o =>
    occurrenceExecuted LE Ts order events pools tapes o ∧
      ∃ seed, occurrenceExecuted LE Ts order events pools tapes seed ∧
        (∃ C, C ∈ targets ∧ C ∈ LE.scope seed.1) ∧
        Relation.ReflTransGen
          (backwardOccurrenceEdge LE order events pools tapes) seed o

/-- A plane tree in preorder: depths and parents. The interval condition
makes every subtree an interval; each parent is determined by the depths.
This excludes the factorial choice of arbitrary earlier parents. -/
abbrev PlaneTreeCode (m : ℕ) := (Fin m → Fin m) × (Fin m → Fin m)

def PlaneTreeSpec {m : ℕ} (Q : PlaneTreeCode m) : Prop :=
  (∀ j : Fin m, j.val = 0 → (Q.1 j).val = 0 ∧ (Q.2 j).val = 0) ∧
  (∀ j : Fin m, 0 < j.val →
    (Q.2 j).val < j.val ∧ (Q.1 j).val = (Q.1 (Q.2 j)).val + 1 ∧
    ∀ i : Fin m, (Q.2 j).val < i.val → i.val < j.val →
      (Q.1 j).val ≤ (Q.1 i).val)

/-- `some r` is a real execution; `none` is an added untouched site.
Traversal order is independent of chronological order. -/
abbrev WitnessItems (T : Stage) (k Ts m : ℕ) :=
  Fin m → Pos T k × Option (Fin Ts)

abbrev ComponentWitness (T : Stage) (k Ts m : ℕ) :=
  PlaneTreeCode m × WitnessItems T k Ts m

/-- An encoded component witness is a rooted plane-tree traversal. Its
anchor may be any site within distance one of the defining event. -/
def CandidateWitness
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (Ts : ℕ) (events : Finset (Pos T k)) (root : Pos T k) (m : ℕ)
    (W : ComponentWitness T k Ts m) : Prop :=
  PlaneTreeSpec W.1 ∧ Function.Injective W.2 ∧
  (∃ hm : 0 < m, (W.2 ⟨0, hm⟩).1 ∈ LE.graphBall {root} 1) ∧
  (∀ j, (W.2 j).1 ∈ events) ∧
  (∀ j, 0 < j.val →
    (W.2 j).1 ∈ LE.graphBall {(W.2 (W.1.2 j)).1} 3)

/-- Count all earlier-round executions touching a cell, regardless of their
position in the tree traversal. Untouched extra sites read entry zero. -/
noncomputable def witnessReadIndex
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (W : WitnessItems T k Ts m) (j : Fin m) (C : D.G.Cell) : ℕ :=
  match (W j).2 with
  | none => 0
  | some r => (Finset.univ.filter fun i : Fin m =>
      ∃ s : Fin Ts, (W i).2 = some s ∧ s.val < r.val ∧ C ∈ LE.scope (W i).1).card

noncomputable def witnessTestConfig
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (W : WitnessItems T k Ts m) (j : Fin m) : Config D.F :=
  fun C => tapes.extend C (witnessReadIndex LE Ts W j C) (pools C)

/-- Bounds are explicit: unequal indices must not be identified by the
finite tape's clamping operation. -/
def WitnessReadsDisjoint
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (W : WitnessItems T k Ts m) : Prop :=
  (∀ j C, C ∈ LE.scope (W j).1 → witnessReadIndex LE Ts W j C ≤ Ts) ∧
  (∀ i j, i ≠ j → ∀ C, C ∈ LE.scope (W i).1 → C ∈ LE.scope (W j).1 →
    witnessReadIndex LE Ts W i C ≠ witnessReadIndex LE Ts W j C)

def WitnessTestsPass
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (W : WitnessItems T k Ts m) : Prop :=
  ∀ j, LE.S (W j).1 (witnessTestConfig LE Ts pools tapes W j)

/-- Four per node for plane-tree shapes, polynomial choices along a radius
three edge, execution/untouched types, rounds, and the distance-one anchor. -/
def componentWitnessBase (d Ts : ℕ) : ℕ := 4 * (d + 1) ^ 4 * (Ts + 1)

/-- The auxiliary root at preorder index zero has no truth test. All other
nodes are distinct execution occurrences in the targets' backward closure. -/
abbrev TargetWitness (T : Stage) (k Ts m : ℕ) :=
  PlaneTreeCode (m + 1) × (Fin m → ExecutionOccurrence T k Ts)

/-- Embed a tested execution node into a plane tree with an auxiliary root. -/
def targetNode {m : ℕ} (j : Fin m) : Fin (m + 1) := ⟨j.val + 1, by omega⟩

/-- Target-rooted forest encoding. Children of the auxiliary root touch a
target; every other child meets its parent's scope, including repeated sites. -/
def CandidateTargetWitness
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (events : Finset (Pos T k)) (targets : Finset D.G.Cell) {m : ℕ}
    (W : TargetWitness T k Ts m) : Prop :=
  PlaneTreeSpec W.1 ∧ Function.Injective W.2 ∧
  (∀ j, (W.2 j).1 ∈ events) ∧
  (∀ j, ((W.1.2 (targetNode j)).val = 0 ∧
      ∃ C ∈ targets, C ∈ LE.scope (W.2 j).1) ∨
    ∃ i : Fin m, W.1.2 (targetNode j) = targetNode i ∧
      ¬ Disjoint (LE.scope (W.2 j).1) (LE.scope (W.2 i).1))

/-- Real execution occurrences as typed truth-test items. -/
def targetItems {T : Stage} {k Ts m : ℕ} (W : TargetWitness T k Ts m) :
    WitnessItems T k Ts m := fun j => ((W.2 j).1, some (W.2 j).2)

/-- Prescribed terminal entry: immediately after every listed touch. -/
noncomputable def targetTerminalIndex
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) {m : ℕ}
    (W : TargetWitness T k Ts m) (C : D.G.Cell) : ℕ :=
  (Finset.univ.filter fun j : Fin m => C ∈ LE.scope (W.2 j).1).card

noncomputable def targetTerminalState
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) {m : ℕ}
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (tapes : Tapes D.F Ts) (W : TargetWitness T k Ts m) :
    ∀ C : {C : D.G.Cell // C ∈ targets}, D.F.State C.1 :=
  fun C => tapes.extend C.1 (targetTerminalIndex LE W C.1) (pools C.1)

/-- Terminal entries lie within the finite tape and outside all truth tests. -/
def TargetTerminalSeparated
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (targets : Finset D.G.Cell) {m : ℕ} (W : TargetWitness T k Ts m) : Prop :=
  (∀ C ∈ targets, targetTerminalIndex LE W C ≤ Ts) ∧
  (∀ j C, C ∈ targets → C ∈ LE.scope (W.2 j).1 →
    witnessReadIndex LE Ts (targetItems W) j C < targetTerminalIndex LE W C)

/-- Exact closure coverage, test independence and final-entry identity.
The empty closure has `m=0`, no tests, and terminal entry zero. -/
def ActualTargetWitness
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (tapes : Tapes D.F Ts) {m : ℕ} (W : TargetWitness T k Ts m) : Prop :=
  CandidateTargetWitness LE events targets W ∧
  Finset.univ.image W.2 = backwardClosure LE order events pools tapes targets ∧
  WitnessReadsDisjoint LE Ts (targetItems W) ∧
  WitnessTestsPass LE Ts pools tapes (targetItems W) ∧
  TargetTerminalSeparated LE targets W ∧
  D.targetProjection targets (LE.resample Ts order events pools tapes.extend) =
    targetTerminalState LE pools targets tapes W

/-- Auxiliary-root incidences, graph steps, plane trees, and real rounds. -/
def targetWitnessBase (d Ts nTargets : ℕ) : ℕ :=
  4 * max 1 (nTargets * (d + 1)) * (d + 1) * max 1 Ts

/-- All three P17.4 outputs. -/
def FiniteResamplingConclusion
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
    (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (v : Pos T k) : Prop :=
  (tapeLaw D.F Ts).pr
    (fun tapes => LE.S v (LE.resample Ts order events pools tapes.extend)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) ∧
  (tapeLaw D.F Ts).pr
    (fun tapes => (backwardClosure LE order events pools tapes targets).card > Ts) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) ∧
  (∀ Ψ, (∀ s, 0 ≤ Ψ s) →
    (tapeLaw D.F Ts).E (fun tapes => Ψ
      (D.targetProjection targets (LE.resample Ts order events pools tapes.extend))) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
        (D.freshTargetLaw targets pools).E Ψ)

/-- D17.R-loc: bounded round influence, independent of analytic hypotheses. -/
theorem resampleLocality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    LE.CellLocalitySpec Ts order pools tapes ∧
      LE.EventTruthLocalitySpec Ts order pools tapes := by
  exact HypercubeRamsey.Lane_q_s17_res1.resampleLocality LE Ts order pools tapes

/-- P17.4a: extract the executions and only untouched extra sites from the
ever-true component; the root is not required to be an untouched test. -/
theorem finiteResamplingComponent
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (v : Pos T k) (hroot : v ∈ events)
    (hfinal : LE.S v (LE.resample Ts order events pools tapes.extend)) :
    ∃ m, Ts ≤ m ∧ 0 < m ∧ ∃ W : ComponentWitness T k Ts m,
      CandidateWitness LE Ts events v m W ∧ WitnessReadsDisjoint LE Ts W.2 ∧
        WitnessTestsPass LE Ts pools tapes W.2 := by
  classical
  by_cases hTs : Ts = 0
  · subst Ts
    let Q : PlaneTreeCode 1 := (fun _ => 0, fun _ => 0)
    let items : WitnessItems T k 0 1 := fun _ => (v, none)
    refine ⟨1, Nat.zero_le _, by norm_num, (Q, items), ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change PlaneTreeSpec Q
        constructor
        · intro j hj
          have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          simp [Q]
        · intro j hj
          omega
      · intro i j hij
        exact Subsingleton.elim _ _
      · refine ⟨by norm_num, ?_⟩
        have hzero : (items ⟨0, by norm_num⟩).1 = v := rfl
        rw [hzero]
        simp [ListEvent.graphBall]
      · intro j
        have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        exact hroot
      · intro j hj
        omega
    · constructor
      · intro j C hC
        simp [items, witnessReadIndex]
      · intro i j hij C hCi hCj
        exact (hij (Subsingleton.elim _ _)).elim
    · intro j
      have hj0 : j = (0 : Fin 1) := by omega
      subst j
      have hcfg0 : witnessTestConfig LE 0 pools tapes
          (fun _ : Fin 1 => (v, none)) 0 =
          LE.resample 0 order events pools tapes.extend := by
        funext C
        simp [witnessTestConfig, witnessReadIndex, Tapes.extend,
          ListEvent.resample, ListEvent.runRounds]
      rw [hcfg0]
      exact hfinal
  · sorry

/-- P17.4b: count plane-tree encodings, not arbitrary connected sequences. -/
theorem finiteResamplingWitnessCount
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts d : ℕ)
    (events : Finset (Pos T k)) (root : Pos T k)
    (hdegree : ∀ v, (Finset.univ.filter fun w => LE.Adjacent v w).card ≤ d) :
    ∀ m : ℕ, 0 < m →
      (Finset.univ.filter fun W : ComponentWitness T k Ts m =>
        CandidateWitness LE Ts events root m W).card ≤
        (componentWitnessBase d Ts) ^ m := by
  classical
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    let B := LE.graphBall {root} 1
    let WType := {W : ComponentWitness T k Ts 1 //
      CandidateWitness LE Ts events root 1 W}
    let Site := {x : Pos T k // x ∈ B}
    let encode (W : WType) : Site × Option (Fin Ts) :=
      let j : Fin 1 := ⟨0, by omega⟩
      ⟨⟨(W.1.2 j).1, by
          rcases W.2 with ⟨_, htail⟩
          rcases htail with ⟨_, htail⟩
          rcases htail with ⟨hanchor, _⟩
          rcases hanchor with ⟨hpos, hanchor⟩
          have hj : (⟨0, hpos⟩ : Fin 1) = j := Subsingleton.elim _ _
          rw [← hj]
          exact hanchor⟩,
        (W.1.2 j).2⟩
    have hencode : Function.Injective encode := by
      intro W W' h
      apply Subtype.ext
      have htree : W.1.1 = W'.1.1 := Subsingleton.elim _ _
      have hitem : W.1.2 (⟨0, by omega⟩ : Fin 1) =
          W'.1.2 (⟨0, by omega⟩ : Fin 1) := by
        have hsite : (W.1.2 (⟨0, by omega⟩ : Fin 1)).1 =
            (W'.1.2 (⟨0, by omega⟩ : Fin 1)).1 := by
          exact congrArg (fun z : Site × Option (Fin Ts) => z.1.1) h
        have hround := congrArg (fun z : Site × Option (Fin Ts) => z.2) h
        exact Prod.ext hsite hround
      exact Prod.ext htree (funext fun j => by
        have hj : j = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
        simpa [hj] using hitem)
    have hball : B.card ≤ d + 1 := by
      simpa [B, pow_one] using
        (HypercubeRamsey.Lane_q_s17_res1.graphBall_singleton_card_le_pow
          LE d hdegree root 1)
    have hcand : (Finset.univ.filter fun W : ComponentWitness T k Ts 1 =>
        CandidateWitness LE Ts events root 1 W).card = Fintype.card WType := by
      simp [WType, Fintype.card_subtype]
    have hSiteCard : Fintype.card Site = B.card := by
      simp [Site, Fintype.card_subtype]
    have hencodeCard : Fintype.card WType ≤
        Fintype.card (Site × Option (Fin Ts)) :=
      Fintype.card_le_of_injective encode hencode
    have hcoeff : d + 1 ≤ 4 * (d + 1) ^ 4 := by
      have hd : 1 ≤ d + 1 := by omega
      have hp : d + 1 ≤ (d + 1) ^ 4 := by
        calc
          d + 1 = (d + 1) * 1 := by omega
          _ ≤ (d + 1) * (d + 1) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow 3 (d + 1) hd)
          _ = (d + 1) ^ 4 := by rw [pow_succ]; ring
      nlinarith [hp, Nat.zero_le ((d + 1) ^ 4)]
    calc
      (Finset.univ.filter fun W : ComponentWitness T k Ts 1 =>
          CandidateWitness LE Ts events root 1 W).card = Fintype.card WType := hcand
      _ ≤ Fintype.card (Site × Option (Fin Ts)) := hencodeCard
      _ = B.card * (Ts + 1) := by simp [Fintype.card_prod, hSiteCard]
      _ ≤ (d + 1) * (Ts + 1) := Nat.mul_le_mul_right _ hball
      _ ≤ componentWitnessBase d Ts := by
        dsimp [componentWitnessBase]
        exact Nat.mul_le_mul_right (Ts + 1) hcoeff
      _ = componentWitnessBase d Ts ^ 1 := by simp
  · sorry

/-- P17.4c: independent entry tests for any supported typed item list.
Tree encoding is irrelevant to this probability estimate. -/
theorem finiteResamplingWitnessTests
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (hn : 2 ≤ T.S.n k) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (h23 : ∀ w ∈ events, (D.freshConfigLaw pools).pr (LE.S w) ≤
      Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) :
    ∀ m (W : WitnessItems T k Ts m), (∀ j, (W j).1 ∈ events) →
      WitnessReadsDisjoint LE Ts W →
      (tapeLaw D.F Ts).pr (fun tapes => WitnessTestsPass LE Ts pools tapes W) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
  classical
  intro m W hItems hReads
  let e := Lane_q_s17_res1.flattenTapesEquiv D.F Ts
  let Idx := Lane_q_s17_res1.TapeRoundIndex (G := D.G) Ts
  let key (j : Fin m) (C : D.G.Cell) : Idx :=
    ⟨C, ⟨min (witnessReadIndex LE Ts W j C) (Ts + 1), by omega⟩⟩
  let cfg (j : Fin m) (x : ∀ i : Idx, TapeEntry D.F i.1) : Config D.F :=
    fun C => x (key j C) (pools C)
  let test (j : Fin m) (x : ∀ i : Idx, TapeEntry D.F i.1) : Prop :=
    LE.S (W j).1 (witnessTestConfig LE Ts pools (e.symm x) W j)
  let support (j : Fin m) : Finset Idx := Finset.univ.filter fun i =>
    i.1 ∈ LE.scope (W j).1 ∧ i.2 = (key j i.1).2
  have hcfg (j : Fin m) (x : ∀ i : Idx, TapeEntry D.F i.1) :
      cfg j x = witnessTestConfig LE Ts pools (e.symm x) W j := by
    funext C
    simp [cfg, witnessTestConfig, Tapes.extend, e,
      Lane_q_s17_res1.flattenTapesEquiv, key]
  have hdep : ∀ j, FinProb.DependsOn
      (fun x => if test j x then (1 : ℝ) else 0) (support j) := by
    intro j x y hxy
    have hstates : ∀ C, C ∈ LE.scope (W j).1 →
        (witnessTestConfig LE Ts pools (e.symm x) W j) C =
          (witnessTestConfig LE Ts pools (e.symm y) W j) C := by
      intro C hC
      rw [← hcfg j x, ← hcfg j y]
      change x (key j C) (pools C) = y (key j C) (pools C)
      apply congrArg (fun a : TapeEntry D.F C => a (pools C))
      apply hxy
      simp [support, hC, key]
    have htruth := LE.scope_ok (W j).1
      (witnessTestConfig LE Ts pools (e.symm x) W j)
      (witnessTestConfig LE Ts pools (e.symm y) W j) hstates
    exact congrArg (fun p : Prop => if p then (1 : ℝ) else 0) (propext htruth)
  have hdisj : ∀ i j, i ≠ j → Disjoint (support i) (support j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    rcases Finset.mem_filter.mp hxi with ⟨_, ⟨hCi, hki⟩⟩
    rcases Finset.mem_filter.mp hxj with ⟨_, ⟨hCj, hkj⟩⟩
    have hiBound := hReads.1 i x.1 hCi
    have hjBound := hReads.1 j x.1 hCj
    have hiVal : (key i x.1).2.val = witnessReadIndex LE Ts W i x.1 := by
      simp [key, Nat.min_eq_left (by omega)]
      omega
    have hjVal : (key j x.1).2.val = witnessReadIndex LE Ts W j x.1 := by
      simp [key, Nat.min_eq_left (by omega)]
      omega
    have hval := congrArg Fin.val (hki.symm.trans hkj)
    rw [hiVal, hjVal] at hval
    exact (hReads.2 i j hij x.1 hCi hCj) hval
  have hmap (j : Fin m) :
      FinLaw.map (Lane_q_s17_res1.flatTapeLaw D.F Ts) (cfg j) =
        D.freshConfigLaw pools := by
    have hkey : Function.Injective (key j) := by
      intro C C' h
      exact congrArg Sigma.fst h
    have hprod := Lane_q_s17_res1.pi_map_injective
      (P := fun i : Idx => FinLaw.pi fun P : D.F.Pool i.1 => D.F.fresh i.1 P)
      (key j) hkey (fun C entry => entry (pools C))
    have hcoord (C : D.G.Cell) :
        FinLaw.map (FinLaw.pi (fun P : D.F.Pool C => D.F.fresh C P))
          (fun entry => entry (pools C)) = D.F.fresh C (pools C) :=
      Lane_q_s17_res1.pi_map_coordinate_law
        (fun P : D.F.Pool C => D.F.fresh C P) (pools C)
    have hcoords :
        (fun C : D.G.Cell =>
          FinLaw.map (FinLaw.pi (fun P : D.F.Pool C => D.F.fresh C P))
            (fun entry => entry (pools C))) =
        (fun C => D.F.fresh C (pools C)) := funext hcoord
    calc
      FinLaw.map (Lane_q_s17_res1.flatTapeLaw D.F Ts) (cfg j) =
          FinLaw.pi (fun C : D.G.Cell =>
            FinLaw.map (FinLaw.pi (fun P : D.F.Pool C => D.F.fresh C P))
              (fun entry => entry (pools C))) := by
        simpa [Lane_q_s17_res1.flatTapeLaw, cfg] using hprod
      _ = D.freshConfigLaw pools := by
        rw [hcoords]
        rfl
  have hsingle (j : Fin m) :
      (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr (test j) ≤
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
    have htest : test j = fun x => LE.S (W j).1 (cfg j x) := by
      funext x
      simp [test, hcfg]
    calc
      _ = (FinLaw.map (Lane_q_s17_res1.flatTapeLaw D.F Ts) (cfg j)).pr
          (LE.S (W j).1) := by
        rw [htest]
        exact (Lane_q_s17_res1.map_pr_law _ _ _).symm
      _ = (D.freshConfigLaw pools).pr (LE.S (W j).1) := by rw [hmap j]
      _ ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := h23 (W j).1 (hItems j)
  let flatTests (x : ∀ i : Idx, TapeEntry D.F i.1) : Prop :=
    WitnessTestsPass LE Ts pools (e.symm x) W
  have hfactor :
      (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr flatTests =
        ∏ j ∈ (Finset.univ : Finset (Fin m)),
          (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr (test j) := by
    simpa [Lane_q_s17_res1.flatTapeLaw, flatTests, WitnessTestsPass, test] using
      Lane_q_s17_res1.pi_pr_inter_disjoint
        (fun i : Idx => FinLaw.pi fun P : D.F.Pool i.1 => D.F.fresh i.1 P)
        Finset.univ test support hdep hdisj
  have hprob :
      (tapeLaw D.F Ts).pr
          (fun tapes => WitnessTestsPass LE Ts pools tapes W) =
        (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr flatTests := by
    calc
      _ = (FinLaw.map (tapeLaw D.F Ts) e).pr flatTests := by
        symm
        calc
          (FinLaw.map (tapeLaw D.F Ts) e).pr flatTests =
              (tapeLaw D.F Ts).pr (fun tapes => flatTests (e tapes)) :=
            Lane_q_s17_res1.map_pr_law _ _ _
          _ = (tapeLaw D.F Ts).pr
              (fun tapes => WitnessTestsPass LE Ts pools tapes W) := by
            congr 1
      _ = (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr flatTests := by
        rw [Lane_q_s17_res1.tapeLaw_flatten]
  calc
    (tapeLaw D.F Ts).pr (fun tapes => WitnessTestsPass LE Ts pools tapes W) =
        ∏ j ∈ (Finset.univ : Finset (Fin m)),
          (Lane_q_s17_res1.flatTapeLaw D.F Ts).pr (test j) := by
      rw [hprob, hfactor]
    _ ≤ ∏ j ∈ (Finset.univ : Finset (Fin m)),
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact Lane_q_s17_res1.finLaw_pr_nonneg
          (Lane_q_s17_res1.flatTapeLaw D.F Ts) (test j)
      · intro j hj
        exact hsingle j
    _ = (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by simp
    _ = Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
      calc
        _ = Real.rpow (T.S.n k : ℝ) ((-(κ.P : ℝ)) * (m : ℝ)) :=
          (Real.rpow_mul_natCast (by positivity) (-(κ.P : ℝ)) m).symm
        _ = Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
          congr 1
          push_cast
          ring

/-- P17.4d(i): target backward-closure extraction with exact terminal entries. -/
theorem finiteResamplingTargetWitness
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (tapes : Tapes D.F Ts) :
    ∃ m, ∃ W : TargetWitness T k Ts m,
      ActualTargetWitness LE order events pools targets tapes W := by
  classical
  by_cases hempty : backwardClosure LE order events pools tapes targets = ∅
  · have hno (r : Fin Ts) (C : D.G.Cell) (hC : C ∈ targets)
        (v : Pos T k) (hv : v ∈ activeAtRound LE Ts order events pools tapes r)
        (hCv : C ∈ LE.scope v) : False := by
      have ho : occurrenceExecuted LE Ts order events pools tapes (v, r) := by
        simpa [occurrenceExecuted, activeAtRound] using hv
      have hmem : (v, r) ∈ backwardClosure LE order events pools tapes targets := by
        unfold backwardClosure
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ho, (v, r), ho, ?_, Relation.ReflTransGen.refl⟩
        exact ⟨C, hC, hCv⟩
      rw [hempty] at hmem
      simp at hmem
    have hrun : ∀ n, n ≤ Ts → ∀ C : D.G.Cell, C ∈ targets →
        (LE.runRounds n order events pools tapes.extend).1 C =
          tapes.extend C 0 (pools C) := by
      intro n
      induction n with
      | zero =>
          intro hn C hC
          rfl
      | succ n ih =>
          intro hn C hC
          have hprev := ih (by omega) C hC
          let r : Fin Ts := ⟨n, by omega⟩
          have hnot : ¬ ∃ v ∈ LE.active order events
              (LE.runRounds n order events pools tapes.extend).1, C ∈ LE.scope v := by
            rintro ⟨v, hv, hCv⟩
            have hv' : v ∈ activeAtRound LE Ts order events pools tapes r := by
              simpa [activeAtRound, r] using hv
            exact hno r C hC v hv' hCv
          rw [show LE.runRounds (n + 1) order events pools tapes.extend =
            LE.round order events pools tapes.extend
              (LE.runRounds n order events pools tapes.extend).1
              (LE.runRounds n order events pools tapes.extend).2 by rfl]
          simp [ListEvent.round, hnot, hprev]
    let Q : PlaneTreeCode 1 := (fun _ => 0, fun _ => 0)
    let W : TargetWitness T k Ts 0 := (Q, Fin.elim0)
    have hTree : PlaneTreeSpec Q := by
      constructor
      · intro j hj
        have hj0 : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        simp [Q]
      · intro j hj
        omega
    have hCand : CandidateTargetWitness LE events targets W := by
      refine ⟨hTree, ?_, ?_, ?_⟩
      · intro i j hij
        exact Fin.elim0 i
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
    refine ⟨0, W, hCand, ?_, ?_, ?_, ?_, ?_⟩
    · simp [W, hempty]
    · constructor
      · intro j
        exact Fin.elim0 j
      · intro i j hij C hCi hCj
        exact Fin.elim0 i
    · intro j
      exact Fin.elim0 j
    · constructor
      · intro C hC
        simp [targetTerminalIndex, W]
      · intro j C hC hscope
        exact Fin.elim0 j
    · funext C
      change (LE.runRounds Ts order events pools tapes.extend).1 C.1 =
        tapes.extend C.1 (targetTerminalIndex LE W C.1) (pools C.1)
      have hfinal := hrun Ts le_rfl C.1 C.2
      simpa [targetTerminalIndex, W] using hfinal
  · sorry

/-- P17.4d(ii): the targets have their own auxiliary-root encoding count. -/
theorem finiteResamplingTargetCount
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (d : ℕ)
    (events : Finset (Pos T k)) (targets : Finset D.G.Cell)
    (hdegree : ∀ v, (Finset.univ.filter fun w => LE.Adjacent v w).card ≤ d) :
    ∀ m : ℕ,
      (Finset.univ.filter fun W : TargetWitness T k Ts m =>
        CandidateTargetWitness LE events targets W).card ≤
        (targetWitnessBase d Ts targets.card) ^ m := by
  sorry

/-- P17.4d(iii): factor prescribed fresh terminal entries from truth tests.
This is a multiplicative bound for arbitrary nonnegative target tests. -/
theorem finiteResamplingTerminalSeparation
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (hn : 2 ≤ T.S.n k) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (h23 : ∀ w ∈ events, (D.freshConfigLaw pools).pr (LE.S w) ≤
      Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)))
    (targets : Finset D.G.Cell) :
    ∀ m (W : TargetWitness T k Ts m), CandidateTargetWitness LE events targets W →
      WitnessReadsDisjoint LE Ts (targetItems W) → TargetTerminalSeparated LE targets W →
      ∀ Ψ : (∀ C : {C : D.G.Cell // C ∈ targets}, D.F.State C.1) → ℝ,
        (∀ s, 0 ≤ Ψ s) →
        (tapeLaw D.F Ts).E (fun tapes =>
          if WitnessTestsPass LE Ts pools tapes (targetItems W) then
            Ψ (targetTerminalState LE pools targets tapes W) else 0) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ := by
  sorry
/-- Inputs for the restricted process, all fixed before drawing tapes.
Degree control applies to every event, not just the defining root. -/
structure FiniteResamplingInput
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
    (events : Finset (Pos T k)) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (targets : Finset D.G.Cell) (v : Pos T k) : Prop where
  n_two : 2 ≤ T.S.n k
  root_mem : v ∈ events
  degree : ∀ w, (Finset.univ.filter fun z => LE.Adjacent w z).card ≤
    (T.S.n k) ^ (κ.Ac + 4)
  targets_count : targets.card ≤ (T.S.n k) ^ (10 * (κ.Ac + 10))
  pools_typical : ∀ C ∈ targets ∪ events.biUnion LE.scope, D.F.typical C (pools C)
  fresh_failure : ∀ w ∈ events, (D.freshConfigLaw pools).pr (LE.S w) ≤
    Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))

/-- Component-cover contract: intermediate encoded witnesses, not a tail. -/
def ComponentWitnessCover
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (v : Pos T k) : Prop :=
  ∀ tapes : Tapes D.F Ts,
    LE.S v (LE.resample Ts order events pools tapes.extend) →
      ∃ m, Ts ≤ m ∧ 0 < m ∧ ∃ W : ComponentWitness T k Ts m,
        CandidateWitness LE Ts events v m W ∧ WitnessReadsDisjoint LE Ts W.2 ∧
          WitnessTestsPass LE Ts pools tapes W.2

def ComponentWitnessCountBound
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (d : ℕ) (events : Finset (Pos T k)) (v : Pos T k) : Prop :=
  ∀ m : ℕ, 0 < m →
    (Finset.univ.filter fun W : ComponentWitness T k Ts m =>
      CandidateWitness LE Ts events v m W).card ≤ (componentWitnessBase d Ts) ^ m

def WitnessTestBound
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (events : Finset (Pos T k)) (pools : ∀ C : D.G.Cell, D.F.Pool C) : Prop :=
  ∀ m (W : WitnessItems T k Ts m), (∀ j, (W j).1 ∈ events) →
    WitnessReadsDisjoint LE Ts W →
    (tapeLaw D.F Ts).pr (fun tapes => WitnessTestsPass LE Ts pools tapes W) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m))

def TargetWitnessCover
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell) : Prop :=
  ∀ tapes : Tapes D.F Ts, ∃ m, ∃ W : TargetWitness T k Ts m,
    ActualTargetWitness LE order events pools targets tapes W

def TargetWitnessCountBound
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (d : ℕ) (events : Finset (Pos T k)) (targets : Finset D.G.Cell) : Prop :=
  ∀ m : ℕ,
    (Finset.univ.filter fun W : TargetWitness T k Ts m =>
      CandidateTargetWitness LE events targets W).card ≤
      (targetWitnessBase d Ts targets.card) ^ m

def TerminalTestBound
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (events : Finset (Pos T k)) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (targets : Finset D.G.Cell) : Prop :=
  ∀ m (W : TargetWitness T k Ts m), CandidateTargetWitness LE events targets W →
    WitnessReadsDisjoint LE Ts (targetItems W) → TargetTerminalSeparated LE targets W →
    ∀ Ψ : (∀ C : {C : D.G.Cell // C ∈ targets}, D.F.State C.1) → ℝ,
      (∀ s, 0 ≤ Ψ s) →
      (tapeLaw D.F Ts).E (fun tapes =>
        if WitnessTestsPass LE Ts pools tapes (targetItems W) then
          Ψ (targetTerminalState LE pools targets tapes W) else 0) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
          (D.freshTargetLaw targets pools).E Ψ

/-- P17.4(i): geometric sum for root failure. Admissibility and the horizon
are fixed before the index and event graph. -/
theorem finiteResamplingRootTail
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
      (order : Pos T k → ℕ) (events : Finset (Pos T k))
      (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell) (v : Pos T k),
      FiniteResamplingInput D LE events pools targets v →
      ComponentWitnessCover (Ts := initialResamplingRounds T k) LE order events pools v →
      ComponentWitnessCountBound (Ts := initialResamplingRounds T k) LE
        ((T.S.n k) ^ (κ.Ac + 4)) events v →
      WitnessTestBound (Ts := initialResamplingRounds T k) LE events pools →
      (tapeLaw D.F (initialResamplingRounds T k)).pr (fun tapes =>
        LE.S v (LE.resample (initialResamplingRounds T k) order events pools tapes.extend)) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * initialResamplingRounds T k / 2)) := by
  sorry

/-- P17.4(ii): geometric sum for the targets' own closure encodings. -/
theorem finiteResamplingClosureTail
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
      (order : Pos T k → ℕ) (events : Finset (Pos T k))
      (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell) (v : Pos T k),
      FiniteResamplingInput D LE events pools targets v →
      TargetWitnessCover (Ts := initialResamplingRounds T k) LE order events pools targets →
      TargetWitnessCountBound (Ts := initialResamplingRounds T k) LE
        ((T.S.n k) ^ (κ.Ac + 4)) events targets →
      WitnessTestBound (Ts := initialResamplingRounds T k) LE events pools →
      (tapeLaw D.F (initialResamplingRounds T k)).pr (fun tapes =>
        (backwardClosure LE order events pools tapes targets).card > initialResamplingRounds T k) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * initialResamplingRounds T k / 2)) := by
  sorry

/-- P17.4(iii): terminal-entry factorization followed by the target-closure
geometric sum. Root-failure witnesses are not used for target comparison. -/
theorem finiteResamplingTerminalComparison
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
      (order : Pos T k → ℕ) (events : Finset (Pos T k))
      (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell) (v : Pos T k),
      FiniteResamplingInput D LE events pools targets v →
      TargetWitnessCover (Ts := initialResamplingRounds T k) LE order events pools targets →
      TargetWitnessCountBound (Ts := initialResamplingRounds T k) LE
        ((T.S.n k) ^ (κ.Ac + 4)) events targets →
      TerminalTestBound (Ts := initialResamplingRounds T k) LE events pools targets →
      ∀ Ψ, (∀ s, 0 ≤ Ψ s) →
        (tapeLaw D.F (initialResamplingRounds T k)).E (fun tapes => Ψ
          (D.targetProjection targets
            (LE.resample (initialResamplingRounds T k) order events pools tapes.extend))) ≤
          (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
            (D.freshTargetLaw targets pools).E Ψ := by
  sorry

/-- P17.4 export: each of the three estimates consumes its own required
witness data. Constants precede the common eventual index. -/
theorem finiteResamplingComparison
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (order : Pos T k → ℕ)
      (events : Finset (Pos T k)) (pools : ∀ C : D.G.Cell, D.F.Pool C)
      (targets : Finset D.G.Cell) (v : Pos T k),
      FiniteResamplingInput D D.asListEvent events pools targets v →
      FiniteResamplingConclusion D D.asListEvent (initialResamplingRounds T k)
        order events pools targets v := by
  filter_upwards [finiteResamplingRootTail κ hκ T,
    finiteResamplingClosureTail κ hκ T,
    finiteResamplingTerminalComparison κ hκ T] with k hr hc ht
  intro PT D order events pools targets v hInput
  let Ts := initialResamplingRounds T k
  let LE := D.asListEvent
  have hCover : ComponentWitnessCover (Ts := Ts) LE order events pools v :=
    fun tapes hfinal => finiteResamplingComponent LE Ts order events pools tapes
      v hInput.root_mem hfinal
  have hCount : ComponentWitnessCountBound (Ts := Ts) LE
      ((T.S.n k) ^ (κ.Ac + 4)) events v :=
    finiteResamplingWitnessCount LE Ts ((T.S.n k) ^ (κ.Ac + 4)) events v hInput.degree
  have hTests : WitnessTestBound (Ts := Ts) LE events pools :=
    finiteResamplingWitnessTests LE Ts hInput.n_two events pools hInput.fresh_failure
  have hTargets : TargetWitnessCover (Ts := Ts) LE order events pools targets :=
    fun tapes => finiteResamplingTargetWitness LE order events pools targets tapes
  have hTargetCount : TargetWitnessCountBound (Ts := Ts) LE
      ((T.S.n k) ^ (κ.Ac + 4)) events targets :=
    finiteResamplingTargetCount LE ((T.S.n k) ^ (κ.Ac + 4)) events targets hInput.degree
  have hTerminal : TerminalTestBound (Ts := Ts) LE events pools targets :=
    finiteResamplingTerminalSeparation LE hInput.n_two events pools hInput.fresh_failure targets
  exact ⟨hr PT D LE order events pools targets v hInput hCover hCount hTests,
    hc PT D LE order events pools targets v hInput hTargets hTargetCount hTests,
    ht PT D LE order events pools targets v hInput hTargets hTargetCount hTerminal⟩

end HypercubeRamsey
