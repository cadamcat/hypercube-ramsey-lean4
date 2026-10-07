import HypercubeRamsey.S05.Assembly
import HypercubeRamsey.S05.Needs

/-!
# L5.1f–j and L5.1l: posterior, avoidance, rarity, and load interfaces

These are finite contracts for the remaining probability stages.  The parameters are left general so that
Section 6 can reuse the row and avoidance nodes with its changed parent prior and selection rule.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- L5.1f: the odd-label reconstruction is the gated posterior estimate applied to the observed array record.
-/
theorem L5_1f_odd_reconstruction {Block Observation : Type*}
    [Fintype Block] [Fintype Observation]
    (M : BlockGate5 Block Observation) (ε s : ℝ) (hε : 0 < ε) :
    let m : Observation → ℝ := fun t => ∑ z, M.prior.w z * M.likelihood z t
    (∑ t, if m t < ε * M.reference.w t ∨ m t = 0 then m t else 0) ≤ ε ∧
    ((∀ z t, M.likelihood z t ≤ Real.exp s * M.reference.w t) →
      ∀ t, ¬ (m t < ε * M.reference.w t ∨ m t = 0) → ∀ z,
        M.prior.w z * M.likelihood z t / m t ≤ Real.exp s * ε⁻¹ * M.prior.w z) := by
  exact ⟨(L5_1d_gated_block M ε s hε).1,
    (L5_1d_gated_block M ε s hε).2.1⟩

/-- Positive log deletion cost for one high-row output relative to a smoothed deletion reference. -/
noncomputable def highDeletionCost5 {N s : ℕ} {Ref : Type*}
    (R : FinProb (Fin s × Fin N)) (Q : Ref → Fin s → Law N)
    (c : Ref) (h : Fin s) (y : Fin N) : ℝ :=
  max 0 (Real.log (R.w (h, y) / ((Q c h).w y / (s : ℝ))))

/-- Finite high-row data at a fixed observation history. -/
structure HighRowModel5 (Data Ref : Type*) [Fintype Data] [Fintype Ref]
    (s N : ℕ) where
  raw : FinProb Data
  good : Data → Prop
  errorExponent : ℝ
  failure_bound : raw.pr (fun d => ¬ good d) ≤ Real.exp (-errorExponent * s)
  source : Data → Fin s → Law N
  deleted : Data → Ref → Fin s → Law N
  length : Ref → ℕ
  capExponent : ℝ
  costBound : ℝ
  price_feasible : ∀ d, good d →
    ∀ price : Ref → ℝ, (∀ c, 0 ≤ price c) → (∑ c, price c = 1) →
      ∃ R : FinProb (Fin s × Fin N),
        (∀ h y, R.w (h, y) ≤ 2 * Real.exp capExponent / ((s : ℝ) * N)) ∧
        (∀ h y, R.w (h, y) ≠ 0 → (source d h).w y ≠ 0) ∧
        ∑ c, price c * (∑ h, ∑ y,
          R.w (h, y) * highDeletionCost5 R (deleted d) c h y) ≤
            ∑ c, price c * (costBound * length c)

/-- L5.1g: price feasibility over the compact high-row laws yields one law meeting every deletion cost at
once, with the atom cap and support on labels of positive reconstructed likelihood. -/
theorem L5_1g_common_high_law {Data Ref : Type*} [Fintype Data] [Fintype Ref]
    {s N : ℕ} (M : HighRowModel5 Data Ref s N) :
    M.raw.pr (fun d => ¬ M.good d) ≤ Real.exp (-M.errorExponent * s) ∧
    ∀ d, M.good d → ∃ R : FinProb (Fin s × Fin N),
      (∀ h y, R.w (h, y) ≤ 2 * Real.exp M.capExponent / ((s : ℝ) * N)) ∧
      (∀ h y, R.w (h, y) ≠ 0 → (M.source d h).w y ≠ 0) ∧
      (∀ c, ∑ h, ∑ y,
        R.w (h, y) * highDeletionCost5 R (M.deleted d) c h y ≤
          M.costBound * M.length c) := by
  sorry

/-- A stage-specific alarm and the raw experiment entering that stage. -/
structure AlarmStage5 (Ω : Type*) [Fintype Ω] where
  raw : FinProb Ω
  alarm : Ω → Prop
  charge : ℝ
  charge_nonneg : 0 ≤ charge
  alarm_mass : raw.pr alarm ≤ charge

/-- L5.1h1: parent restriction removes the stage-1 alarms at the charged cost. -/
theorem L5_1h1_parent {Ω : Type*} [Fintype Ω] (A : AlarmStage5 Ω)
    (hcharge : A.charge < 1) : ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A.alarm ω := by
  sorry

/-- L5.1h2: coarse-base restriction removes the stage-2 alarms at the charged cost. -/
theorem L5_1h2_coarse_base {Ω : Type*} [Fintype Ω] (A : AlarmStage5 Ω)
    (hcharge : A.charge < 1) : ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A.alarm ω := by
  sorry

/-- L5.1h3: high-key restriction removes the stage-3 alarms at the charged cost. -/
theorem L5_1h3_high_keys {Ω : Type*} [Fintype Ω] (A : AlarmStage5 Ω)
    (hcharge : A.charge < 1) : ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A.alarm ω := by
  sorry

/-- L5.1h4: separate optional-key pretrims retain the stage-4 good histories. -/
theorem L5_1h4_optional_pretrims {Ω : Type*} [Fintype Ω] (A : AlarmStage5 Ω)
    (hcharge : A.charge < 1) : ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A.alarm ω := by
  sorry

/-- L5.1h5: low-key restriction removes the stage-5 alarms at the charged cost. -/
theorem L5_1h5_low_keys {Ω : Type*} [Fintype Ω] (A : AlarmStage5 Ω)
    (hcharge : A.charge < 1) : ∃ Q : FinProb Ω, ∀ ω, Q.w ω ≠ 0 → ¬ A.alarm ω := by
  sorry

/-- A finite five-stage alarm family measured under one common raw law. The full Section 5 proof uses the
more refined entering-history kernels; this is the finite union contract used by the final positivity step. -/
structure FiveStageAvoidance5 (Ω : Type*) [Fintype Ω] where
  raw : FinProb Ω
  alarm : Fin 5 → Ω → Prop
  charge : Fin 5 → ℝ
  charge_nonneg : ∀ t, 0 ≤ charge t
  entering_mass : ∀ t, raw.pr (alarm t) ≤ charge t
  total_charge : ∑ t, charge t < 1

/-- L5.1h: all five history tests can be imposed while retaining positive raw mass. -/
theorem L5_1h_five_stage (Ω : Type*) [Fintype Ω] (A : FiveStageAvoidance5 Ω) :
    ∃ ω, (∀ t, ¬ A.alarm t ω) := by
  sorry

/-- L5.1i: a tuple whose coordinate law is dominated by `M` times a product reference has few entries in a
small label set. -/
theorem L5_1i_prior_heavy {N k : ℕ} (P Q : FinProb (Fin k → Fin N))
    (M q υ : ℝ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hυ : 0 ≤ υ)
    (hdom : P.DensityLE5 Q M)
    (hQ : ∀ S : Finset (Fin k),
      Q.pr (fun z => ∀ i ∈ S, (z i).val < (q * N)) ≤ q ^ S.card) :
    P.pr (fun z =>
      υ * k < (Finset.univ.filter (fun i => (z i).val < q * N)).card) ≤
        2 ^ k * M * q ^ (υ * k) := by
  sorry

/-- L5.1i's deterministic role-rarity bound for the low/high split. -/
theorem L5_1i_role_rarity (n : ℕ) (hlarge : 2 ≤ n)
    (lowMass highMass boundaryMass : ℝ)
    (hlow : 0 ≤ lowMass) (hhigh : highMass ≤ (n : ℝ) ^ (-(13 / 100 : ℝ)))
    (hboundary : boundaryMass ≤ (n : ℝ) ^ (-(5 / 100 : ℝ))) :
    boundaryMass + highMass ≤ (n : ℝ) ^ (-(5 / 100 : ℝ)) +
      (n : ℝ) ^ (-(13 / 100 : ℝ)) := by
  sorry

/-- L5.1j: marking-and-height uses the shared position-averaged forced-center contract.  Site geometry and
the short/long radii remain parameters in `MarkingHeightData5`; the underlying L3.8 estimate is requested in
`Needs.lean`. -/
theorem L5_1j_marking_height
    {Position Eligibility Centre : Type*}
    [Fintype Position] [Fintype Eligibility] [Fintype Centre]
    (positionLaw : FinProb Position)
    (legalEligibility : Position → Finset Eligibility)
    (forcedSelectionProbability : Position → Eligibility → Centre → ℝ)
    (lambda : ℝ)
    (hheight : PositionAveragedForcedCenterBound5 positionLaw legalEligibility
      forcedSelectionProbability lambda) :
    PositionAveragedForcedCenterBound5 positionLaw legalEligibility
      forcedSelectionProbability lambda := hheight

/-- L5.1l's deterministic conversion from bounded normalized average loads to odd column sums. -/
theorem L5_1l_odd_load_conversion {B : Type*} [Fintype B] {N : ℕ}
    (rows : B → Law N) (C theta : ℝ) (hN : 0 < N)
    (hmean : ∀ y, (Fintype.card B : ℝ)⁻¹ *
      ∑ b, (N : ℝ) * (rows b).w y ≤ C)
    (hratio : (Fintype.card B : ℝ) / N * C ≤ theta) :
    ∀ y, ∑ b, (rows b).w y ≤ theta := by
  sorry

/-- L5.1l: after its three history estimates, the normalized odd-row average controls every odd column sum.
This interface records the final deterministic conversion; the three scattered-moment estimates remain proof
nodes for the Section 5 construction. -/
theorem L5_1l {B : Type*} [Fintype B] {N : ℕ}
    (rows : B → Law N) (C theta : ℝ) (hN : 0 < N)
    (hmean : ∀ y, (Fintype.card B : ℝ)⁻¹ *
      ∑ b, (N : ℝ) * (rows b).w y ≤ C)
    (hratio : (Fintype.card B : ℝ) / N * C ≤ theta) :
    ∀ y, ∑ b, (rows b).w y ≤ theta := by
  exact L5_1l_odd_load_conversion rows C theta hN hmean hratio

end HypercubeRamsey
