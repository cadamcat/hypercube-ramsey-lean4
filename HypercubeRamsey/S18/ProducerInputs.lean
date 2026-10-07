import HypercubeRamsey.S13.All
import HypercubeRamsey.S14.All
import HypercubeRamsey.S16.Producers
import HypercubeRamsey.S18.ProducerInputs_q_s18_bridge
import HypercubeRamsey.S18.ProducerInputs_sol_s18_widen

/-! Inputs constructed before the Section 18 assembly. The remaining leaves
are the fixed constant choice, the fine mesh, and the low-mode estimates;
none has a fresh law or a final cube as an input. -/

namespace HypercubeRamsey.S18

open Classical Filter
open scoped BigOperators
open S16 S16.Lane_sol_fix2_s16

/-- Fixed cluster-query threshold from 18:1118–1123. -/
def LateThresholds (κ : CConsts) : Prop :=
  Real.exp (100 * κ.Kbd) + 100 * rowMeanConstant κ + κ.A0 ≤ κ.KB ∧
  ∀ h : ℕ, Real.rpow (κ.M1 * κ.Q0) κ.Mlo ≤ (h : ℝ) → 2 < 20 * κ.ρ * h

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
  have ha : 0 < κ₀.a := by rw [hκ₀.a_eq]; exact div_pos hκ₀.θ_rng.1 (by norm_num)
  have haC : κ₀.aC < 1 := by
    have := hκ₀.aC_rng.2
    have := min_le_right κ₀.η0 1
    linarith
  have hCb : 0 < κ₀.Cb := by
    have h := hκ₀.Cb_big
    have hdiv : 0 < 100 * κ₀.aC / κ₀.aB :=
      div_pos (mul_pos (by norm_num) hκ₀.aC_rng.1) hκ₀.aB_rng.1
    linarith only [h, hdiv]
  have hM : 1 < (κ₀.Mlo : ℝ) := by linarith [hκ₀.Mlo_big]
  have hMhi : (κ₀.Mlo : ℝ) ≤ κ₀.Mhi := by
    have := div_pos (by norm_num : (0 : ℝ) < 10) hκ₀.cq_rng.1
    linarith [hκ₀.Mhi_big.1]
  have hωM : 4 * κ₀.ω * κ₀.Mlo < 1 := by
    have h1 := mul_le_mul_of_nonneg_left hMhi
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hκ₀.ω_rng.1.le)
    have h2 : 0 ≤ κ₀.ω * κ₀.Mhi := mul_nonneg hκ₀.ω_rng.1.le (by positivity)
    nlinarith [hκ₀.ω_rng.2]
  obtain ⟨c, h0, hc, hcc, hh0, hheight⟩ := Lane_sol_s18_widen.height_witness κ₀ hκ₀
  obtain ⟨qc, hqc⟩ := eventually_atTop.mp
    (Lane_sol_s18_widen.qcond_update_eventually κ₀ hκ₀ c hc h0 (by linarith))
  obtain ⟨qcal, hcal⟩ := eventually_atTop.mp
    (Lane_sol_s18_widen.calibration_eventually κ₀ hκ₀.ω_rng.1 ha hM hωM)
  obtain ⟨qlate, hlate⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < (κ₀.Mlo : ℝ) by linarith)).eventually_ge_atTop
      (1 / κ₀.ρ))
  let Q0 := max κ₀.Q0 (max qc (max qcal (max qlate 1)))
  have hQold : κ₀.Q0 ≤ Q0 := le_max_left _ _
  have hQqc : qc ≤ Q0 := by dsimp [Q0]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hQcal : qcal ≤ Q0 := by
    dsimp [Q0]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hQlate : qlate ≤ Q0 := by
    dsimp [Q0]
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hQone : 1 ≤ Q0 := by
    dsimp [Q0]
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨N, hN⟩ := exists_nat_gt (max (κ₀.Qbd : ℝ) (κ₀.M1 * Q0))
  let Qbd := 2 ^ N
  have hNQ : N ≤ Qbd := Nat.le_of_lt Nat.lt_two_pow_self
  have hNQR : (N : ℝ) ≤ Qbd := by exact_mod_cast hNQ
  have hQB : κ₀.Qbd ≤ Qbd := by
    exact_mod_cast ((le_max_left (κ₀.Qbd : ℝ) (κ₀.M1 * Q0)).trans (hN.le.trans hNQR))
  have hMQ : κ₀.M1 * Q0 < (Qbd : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le hNQR
  let Kbd := max κ₀.Kbd (Real.exp (Cstar κ₀.u κ₀.ξ * Qbd))
  let KB := max κ₀.KB (Real.exp (100 * Kbd) + 100 * rowMeanConstant κ₀ + κ₀.A0)
  have hKb : κ₀.Kbd ≤ Kbd := le_max_left _ _
  have hKB : κ₀.KB ≤ KB := le_max_left _ _
  have hKB0 : 0 ≤ KB := (le_trans (by positivity) hκ₀.KB_big).trans hKB
  have hA0 : 0 ≤ κ₀.A0 := le_trans (by positivity) hκ₀.A0_big
  have hden : 0 < 1 + KB + 2 * κ₀.A0 := by linarith
  let β := min κ₀.β (0.01 / (1 + KB + 2 * κ₀.A0))
  have hβ : 0 < β := lt_min hκ₀.β_rng.1 (div_pos (by norm_num) hden)
  let κ : CConsts := {κ₀ with c14 := c, h0 := h0, Q0 := Q0, Qbd := Qbd, Kbd := Kbd, KB := KB, β := β}
  have hκ : κ.Admissible := by
    refine {
      η0_pos := hκ₀.η0_pos, xs_rng := hκ₀.xs_rng, α_rng := hκ₀.α_rng,
      ι_rng := hκ₀.ι_rng, xι_pos := hκ₀.xι_pos, αι_pos := hκ₀.αι_pos,
      Ac_eq := hκ₀.Ac_eq, P_big := hκ₀.P_big, R_eq := hκ₀.R_eq,
      L_eq := hκ₀.L_eq, u_rng := hκ₀.u_rng, ξ_rng := hκ₀.ξ_rng,
      θ_rng := hκ₀.θ_rng, clock := hκ₀.clock, aC_rng := hκ₀.aC_rng,
      aB_rng := hκ₀.aB_rng, M1_big := hκ₀.M1_big, Cb_big := hκ₀.Cb_big,
      Mlo_big := hκ₀.Mlo_big, cq_rng := hκ₀.cq_rng, Mhi_big := hκ₀.Mhi_big,
      ω_rng := hκ₀.ω_rng, a_eq := hκ₀.a_eq, ρ_rng := hκ₀.ρ_rng,
      KB_big := hκ₀.KB_big.trans hKB, A0_big := hκ₀.A0_big,
      bucket := hκ₀.bucket, Kcell_big := hκ₀.Kcell_big,
      cperm_rng := hκ₀.cperm_rng, c5_pos := hκ₀.c5_pos, c5_le := hκ₀.c5_le,
      c14_pos := hc, cChernoff_pos := hκ₀.cChernoff_pos, h0_pos := hh0,
      d0_pos := hκ₀.d0_pos, nearProduct := hκ₀.nearProduct,
      Q0_large := ?_, bounded := ?_, β_rng := ?_ }
    · intro q hq
      exact hqc q (hQqc.trans hq)
    · refine ⟨⟨N, rfl⟩, hMQ, ?_, hκ₀.bounded.2.2.2.1.trans hKb, le_max_right _ _⟩
      have hqpow : (κ₀.Qbd : ℝ) ^ κ₀.aC ≤ (Qbd : ℝ) ^ κ₀.aC :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQB) hκ₀.aC_rng.1.le
      exact (Real.exp_le_exp.mpr (neg_le_neg hqpow)).trans hκ₀.bounded.2.2.1
    · refine ⟨hβ, ?_, ?_⟩
      · exact (min_le_right _ _).trans
          (div_le_div_of_nonneg_right (by norm_num : (0.01 : ℝ) ≤ 0.02) hden.le)
      · exact (min_le_left _ _).trans_lt hκ₀.β_rng.2.2
  have hcalibration : CalibrationConstants κ := by
    intro q h hq hl hh
    exact hcal (q : ℝ) (hQcal.trans hq) h hl hh
  have hheight' : Nonempty (S14.HeightConstantContract κ) :=
    Lane_sol_s18_widen.transfer_height (κ := {κ₀ with c14 := c, h0 := h0}) (κ' := κ)
      rfl rfl rfl rfl rfl rfl hheight
  have hlate' : LateThresholds κ := by
    refine ⟨le_max_right _ _, ?_⟩
    intro h hh
    have hscale := hlate Q0 hQlate
    have hbase : Q0 ≤ κ₀.M1 * Q0 := by
      nlinarith only [hQone, hκ₀.M1_big.1]
    have hp := Real.rpow_le_rpow (by linarith : 0 ≤ Q0) hbase (by linarith : 0 ≤ (κ₀.Mlo : ℝ))
    have hdim : 1 / κ₀.ρ ≤ (h : ℝ) := hscale.trans (hp.trans hh)
    have hρh : 1 ≤ (h : ℝ) * κ₀.ρ := (div_le_iff₀ hκ₀.ρ_rng.1).mp hdim
    change 2 < 20 * κ₀.ρ * h
    nlinarith only [hρh]
  exact ⟨κ, hκ, rfl, rfl, rfl, rfl, rfl, rfl, hlate', ⟨hheight', hcalibration⟩⟩

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
  have hP : 1 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    norm_num at h
    omega
  have hR : 1 ≤ κ.R := by
    rw [hκ.R_eq]
    exact Nat.one_le_pow 2 κ.P hP
  have hRreal : 1 ≤ (κ.R : ℝ) := by exact_mod_cast hR
  have hKBpos : 0 < κ.KB := by nlinarith [hκ.KB_big, hRreal]
  have hKBone : 1 ≤ κ.KB := by nlinarith [hκ.KB_big, hRreal]
  have hKbdone : 1 ≤ κ.Kbd := hκ.bounded.2.2.2.1
  let K16 : ℝ := κ.Kbd + 4 * κ.KB + 10
  have hK16pos : 0 < K16 := by dsimp [K16]; nlinarith [hKbdone, hKBpos]
  have hK16two : 2 ≤ K16 := by dsimp [K16]; nlinarith [hKbdone, hKBpos]
  have hK16one : 1 ≤ K16 := by dsimp [K16]; nlinarith [hKbdone, hKBpos]
  have hK16Kbd : κ.Kbd ≤ K16 := by dsimp [K16]; nlinarith [hKBpos]
  have hK16KB : 4 * κ.KB ≤ K16 := by dsimp [K16]; nlinarith [hKbdone]
  have hEvents := Lane_q_s18_bridge.eventually_low_input_scale_events
    hκ T K16 hKBpos hK16one
  refine ⟨K16, ?_⟩
  filter_upwards [hEvents] with k hEv
  intro PT hPT hlow
  let Q := Lane_q_s18_bridge.low_mode_quant_facts_of_events hκ hPT hlow hEv
      hK16pos hK16two hK16Kbd hK16KB
  refine ⟨Q, ?_⟩
  intro i
  have hL : 1 ≤ Real.log (T.S.n k : ℝ) := hEv.log_large
  have hLnonneg : 0 ≤ Real.log (T.S.n k : ℝ) := le_trans (by norm_num) hL
  have hLKB : Real.log (T.S.n k : ℝ) ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKBone hLnonneg
  rcases Lane_q_s18_bridge.low_mode_cases hlow with hb | hd | hc
  · have hprod : 0 ≤ κ.KB * Real.log (T.S.n k : ℝ) :=
      mul_nonneg hKBpos.le hLnonneg
    simpa [Tiling.gain, hb] using hprod
  · have hGain : (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
      rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
        ⟨_, _, _, _, _, _, hhigh⟩
      apply le_of_not_gt
      intro hlt
      exact (by simp [hd] : PT.tiling.mode ≠ .highDirect) (hhigh.mpr hlt)
    have hscaled : ((PT.tiling.P i).g : ℝ) / 1000 ≤ (PT.tiling.P i).g := by
      have hg : 0 ≤ ((PT.tiling.P i).g : ℝ) := Nat.cast_nonneg _
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)).2
      nlinarith
    simpa [Tiling.gain, hd] using hscaled.trans hGain
  · have hξlt : κ.ξ < 1 := by
      have hpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
      have hαpow : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ κ.α :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hκ.α_rng.1.le
      exact (lt_of_lt_of_le hκ.ξ_rng.2 hαpow).trans (by linarith [hκ.α_rng.2])
    have hθden : 0 < (3 : ℝ) * (4 : ℝ) ^ (κ.u + 3) := by positivity
    have hθmult : κ.θ * ((3 : ℝ) * (4 : ℝ) ^ (κ.u + 3)) < κ.ξ ^ 2 :=
      (lt_div_iff₀ hθden).mp hκ.θ_rng.2
    have hθsmall : κ.θ < κ.ξ ^ 2 := by
      have hpowNat : 1 ≤ 4 ^ (κ.u + 3) := Nat.one_le_pow (κ.u + 3) 4 (by decide)
      have hpowReal : 1 ≤ (4 : ℝ) ^ (κ.u + 3) := by exact_mod_cast hpowNat
      have hden : 1 ≤ (3 : ℝ) * (4 : ℝ) ^ (κ.u + 3) := by nlinarith
      have hthetaGrow : κ.θ ≤ κ.θ * ((3 : ℝ) * (4 : ℝ) ^ (κ.u + 3)) := by
        have h := mul_le_mul_of_nonneg_left hden hκ.θ_rng.1.le
        simpa only [mul_one] using h
      exact hthetaGrow.trans_lt hθmult
    have hξsq : κ.ξ ^ 2 < 1 := by nlinarith [hκ.ξ_rng.1, hξlt]
    have ha_lt : κ.a < 1 := by
      rw [hκ.a_eq]
      nlinarith [hθsmall, hξsq]
    have ha_nonneg : 0 ≤ κ.a / (10 ^ 6 : ℝ) := by
      rw [hκ.a_eq]
      exact div_nonneg (div_nonneg hκ.θ_rng.1.le (by norm_num)) (by norm_num)
    have ha_small : κ.a / (10 ^ 6 : ℝ) ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
      nlinarith [ha_lt]
    have hheight : (PT.tiling.P i).h ≤ Real.log (T.S.n k : ℝ) := by
      have hpow' : Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ) ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 10 : ℝ) ≤ 1)
      have hpow : Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ) ≤
          Real.log (T.S.n k : ℝ) := by
        calc
          Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ) ≤
              Real.rpow (Real.log (T.S.n k : ℝ)) (1 : ℝ) := hpow'
          _ = Real.log (T.S.n k : ℝ) := Real.rpow_one _
      exact (Q.height_bound i).trans hpow
    have hgain : κ.a * (PT.tiling.P i).h / (10 ^ 6 : ℝ) ≤
        Real.log (T.S.n k : ℝ) := by
      have hfactor : κ.a * (PT.tiling.P i).h / (10 ^ 6 : ℝ) =
          (κ.a / (10 ^ 6 : ℝ)) * (PT.tiling.P i).h := by ring
      rw [hfactor]
      calc
        (κ.a / (10 ^ 6 : ℝ)) * (PT.tiling.P i).h ≤
            (κ.a / (10 ^ 6 : ℝ)) * Real.log (T.S.n k : ℝ) :=
          mul_le_mul_of_nonneg_left hheight ha_nonneg
        _ ≤ 1 * Real.log (T.S.n k : ℝ) :=
          mul_le_mul_of_nonneg_right ha_small hLnonneg
        _ = Real.log (T.S.n k : ℝ) := by ring
    have hfinal : Real.log (T.S.n k : ℝ) ≤ κ.KB * Real.log (T.S.n k : ℝ) := hLKB
    simpa [Tiling.gain, hc] using hgain.trans hfinal

end HypercubeRamsey.S18
