import HypercubeRamsey.S13.All
import HypercubeRamsey.S14.All
import HypercubeRamsey.S16.Producers

/-! Inputs constructed before the Section 18 assembly. The remaining leaves
are the fixed constant choice, the fine mesh, and the low-mode estimates;
none has a fresh law or a final cube as an input. -/

namespace HypercubeRamsey.S18

open Classical Filter
open scoped BigOperators
open S16 S16.Lane_sol_fix2_s16

/-- Fixed cluster-query threshold from 18:1118–1123, covering the actual
low-cluster height lower bound `Q0^Mlo`. -/
def LateThresholds (κ : CConsts) : Prop :=
  Real.exp (100 * κ.Kbd) + 100 * rowMeanConstant κ + κ.A0 ≤ κ.KB ∧
  ∀ h : ℕ, Real.rpow κ.Q0 κ.Mlo ≤ (h : ℝ) → 2 < 20 * κ.ρ * h

/-- Fixed Q0 inequalities used by both calibration stages (16:338–342,
400–427). The arguments are scalar scales, before any stage or profile. -/
def CalibrationConstants (κ : CConsts) : Prop :=
  ∀ q h : ℕ, κ.Q0 ≤ (q : ℝ) →
    Real.rpow (q : ℝ) κ.Mlo ≤ (h : ℝ) →
    (h : ℝ) < 2 * Real.rpow (q : ℝ) κ.Mlo →
    let d := ⌊Real.exp ((q : ℝ) / 2)⌋₊
    κ.d0 ≤ d ∧ (10 ^ 100 : ℕ) ≤ d ∧
      4 * Real.exp (1.5 * (sliceK κ h : ℝ) * sliceT κ h) ≤ Real.rpow (d : ℝ) 0.05 ∧
      2 * (h : ℝ) ^ 2 ≤ Real.rpow (d : ℝ) 0.01 ∧
      (h + 1 : ℝ) ≤ Real.rpow (d : ℝ) 0.025 ∧
      16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow (sliceEps κ h) (1 / 16 : ℝ) ≤
        Real.rpow (d : ℝ) (-20)

/-- The fixed outputs of L3.8 and the enlarged Q0 must accompany the
selected admissible constants; arbitrary positive c14/h0 are insufficient. -/
structure ProducerConstants (κ : CConsts) : Prop where
  height : Nonempty (S14.HeightConstantContract κ)
  calibration : CalibrationConstants κ

/-- Constant choice after C12.K: specialize L3.8 (14:68,155,167), decrease
c14, increase h0, then choose Q0 for every fixed-scale inequality (14:215;
16:26–28,338–342,400–427;18:1118–1123). Discrepancy widths are preserved.
This is a numerical/estimate-selection leaf, not a consequence of positivity. -/
theorem producer_constants_widening (κ₀ : CConsts) (hκ₀ : κ₀.Admissible) :
    ∃ κ : CConsts, κ.Admissible ∧ κ.η0 = κ₀.η0 ∧
      κ.xs = κ₀.xs ∧ κ.α = κ₀.α ∧ κ.xι = κ₀.xι ∧ κ.αι = κ₀.αι ∧ κ.ι = κ₀.ι ∧
      LateThresholds κ ∧ ProducerConstants κ := by
  sorry

/-- Symmetric law budgets transport across the orientation swap. -/
private theorem orient_two_budget {T : Stage} {k : ℕ} {s l e : ℝ}
    (h : TwoBudgetDisc T k s l e) (o : Bool) :
    TwoBudgetDisc (T.orient o) k s l e := by
  cases o with
  | false => exact h
  | true =>
    simp only [TwoBudgetDisc, Stage.orient, Stage.swap, BadSeq.swap]
    intro c μ ν hμ hν hw
    rw [dens_transpose]
    apply h c ν μ hν hμ
    rcases hw with hw | hw
    · exact Or.inr ⟨hw.2, hw.1⟩
    · exact Or.inl ⟨hw.2, hw.1⟩

theorem orient_init {T : Stage} {η : ℝ} (h : InitDisc T η) (o : Bool) :
    InitDisc (T.orient o) η := by
  filter_upwards [h] with k hk
  have hn : (T.orient o).S.n k = T.S.n k := by cases o <;> rfl
  simpa only [hn] using orient_two_budget hk o

theorem orient_deep_budget {T : Stage} {x α ε : ℝ}
    (h : DeepDisc T x α ε) (o : Bool) : DeepDisc (T.orient o) x α ε := by
  filter_upwards [h] with k hk
  have hn : (T.orient o).S.n k = T.S.n k := by cases o <;> rfl
  simpa only [hn] using orient_two_budget hk o

theorem orient_deep {T : Stage}
    (h : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) (o : Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc (T.orient o) x α ε := by
  intro ε hε
  obtain ⟨x, α, hx, hα, hd⟩ := h ε hε
  exact ⟨x, α, hx, hα, orient_deep_budget hd o⟩

/-- The scalar fixed-Q0 contract applies to an actual low-cluster patch. -/
theorem cell_calibration_of_constants {κ : CConsts} (hκ : κ.Admissible)
    (hc : CalibrationConstants κ) {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hlow : PT.tiling.mode.isLow) :
    CellCalibrationScale PT := by
  constructor
  intro hcluster i
  have hm : PT.tiling.mode = .lowCluster := by
    cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
  rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
    ⟨hthreshold, hgq, hmass, hsmall, hbin, hcodeg, hdyadic, hhl, hhu, hrest⟩
  have hq : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) := by
    have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
    have hmax : max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) ≤
        κ.M1 * (PT.tiling.P i).q := by
      apply max_le hgq
      nlinarith [(show (0 : ℝ) ≤ (PT.tiling.P i).q by positivity), hκ.M1_big.1]
    have hth : κ.M1 * κ.Q0 ≤
        max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) := by
      simpa only [Nat.cast_max] using hthreshold
    nlinarith [hth.trans hmax]
  have hbounds := hc (PT.tiling.P i).q (PT.tiling.P i).h hq
    (by simpa [hm] using hhl) (by simpa [hm] using hhu)
  have hdEq := hbin (Or.inl hm)
  simpa [hdEq] using hbounds

/-- L16.0 (16:15–34): geometry's input estimates, uniform over every
valid low profile. No syndrome/cell/sampler conclusion is assumed. -/
theorem low_mode_quantitative_inputs {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ K16 : ℝ, ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k,
      PT.Valid → PT.tiling.mode.isLow → ∃ Q : LowModeQuantFacts hκ (PT := PT) K16,
        ∀ i, PT.tiling.gain i ≤ κ.KB * Real.log (T.S.n k) := by
  sorry

end HypercubeRamsey.S18
