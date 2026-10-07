import HypercubeRamsey.Tools.LinearCode
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.S17.Nodes_q_s17_pal
import HypercubeRamsey.S17.Needs

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
  sorry

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
  sorry

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

set_option maxHeartbeats 10000000 in
/-- L17.1 deterministic cap/degree calculation, consumed by palette retention.
The fixed constant is existential before the index, tiling, and sampler. -/
theorem initialRowAtomBound
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSource : S17SourceFacts κ T) (K : ℝ) (hK : 0 < K) :
    ∃ Katom : ℝ, 0 < Katom ∧ ∀ᶠ k in atTop,
      ∀ (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT),
        D.L16QuantitativeValidity K → InitialAtomBound D Katom := by
  let A : ℝ := 400 / (1 - κ.a)
  let Katom : ℝ := 2 * A * Real.exp (8 * κ.Kbd + 1)
  have ha : κ.a < 1 := Lane_q_s17_pal.a_lt_one κ hκ
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos (by norm_num) (by linarith)
  have hKatom : 0 < Katom := by positivity
  refine ⟨Katom, hKatom, ?_⟩
  let n₀ : ℕ := max (max 256 ⌈4 * κ.Kbd⌉₊) ⌈(80 * κ.A0) ^ 2⌉₊
  have hn : ∀ᶠ k in atTop, n₀ ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop n₀
  filter_upwards [hn] with k hk
  intro PT D hQuant
  have hPT : PT.Valid := D.tiling_valid
  have hTV : Tiling.Valid PT.tiling := hPT.tiling_valid
  have hLow := D.mode_low
  have hKbd : 1 ≤ κ.Kbd := hκ.bounded.2.2.2.1
  have hnKbd : 4 * κ.Kbd ≤ (T.S.n k : ℝ) := by
    have hceil : 4 * κ.Kbd ≤ (⌈4 * κ.Kbd⌉₊ : ℝ) := Nat.le_ceil _
    have hceilNat : ⌈4 * κ.Kbd⌉₊ ≤ n₀ :=
      le_trans (le_max_right 256 ⌈4 * κ.Kbd⌉₊)
        (le_max_left (max 256 ⌈4 * κ.Kbd⌉₊) ⌈(80 * κ.A0) ^ 2⌉₊)
    have hbound : (⌈4 * κ.Kbd⌉₊ : ℝ) ≤ (T.S.n k : ℝ) := by
      exact_mod_cast (le_trans hceilNat hk)
    exact le_trans hceil hbound
  have hnPos : 0 < (T.S.n k : ℝ) := by
    have hnNat : 0 < T.S.n k := by omega
    exact_mod_cast hnNat
  have hKbdNonneg : 0 ≤ κ.Kbd := by linarith
  have hKbdEps : 0 ≤ κ.Kbd / (T.S.n k : ℝ) ∧
      κ.Kbd / (T.S.n k : ℝ) ≤ 1 / 4 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnPos).2
      nlinarith
  cases hm : PT.tiling.mode with
  | bounded =>
      rcases hTV.bounded_data hm with ⟨_, hpatch⟩
      refine fun v pools s heven htyp hvalid x => ?_
      let i := D.G.patchOf v
      have hdata := hpatch i
      rcases hdata with ⟨hell, hh, _, hM, _⟩
      have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
      have hMpos : 0 < (PT.tiling.P i).M := by
        have hprod : 0 < (1 / 400 : ℝ) * (T.S.N k : ℝ) := by positivity
        have hMreal : 0 < ((PT.tiling.P i).M : ℝ) := lt_of_lt_of_le hprod hM
        exact_mod_cast hMreal
      have hnoncluster : ¬ PT.tiling.mode.isCluster := by
        simp [Mode.isCluster, hm]
      have haPos : 0 < 1 - κ.a := by linarith
      have hcell : D.G.cellOf v ∈ D.scopeCells v := by simp [ListGateContext.scopeCells]
      have hpoolTypical : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) :=
        htyp _ hcell
      have hstateValid : D.stateValid (D.G.cellOf v) (pools (D.G.cellOf v))
          (s (D.G.cellOf v)) := hvalid _ hcell
      have hclean : D.CleanInitialPrior v (D.prior s v) := by
        simpa [ListGateContext.prior] using
          hQuant.prior_shape v (pools (D.G.cellOf v)) (s (D.G.cellOf v))
            heven hpoolTypical hstateValid
      have hσcap := Lane_q_s17_pal.cleanInitialPrior_noncluster_cap D v
        (D.prior s v) hclean ha hMpos hnoncluster x
      have hcornerCap :
          1 / ((1 - κ.a) * (PT.tiling.P i).M) ≤ A / T.S.N k := by
        have hdenPos : 0 < (1 - κ.a) * (PT.tiling.P i).M := by positivity
        have hdenLower : (1 - κ.a) * (T.S.N k : ℝ) / 400 ≤
            (1 - κ.a) * (PT.tiling.P i).M := by
          have hmul := mul_le_mul_of_nonneg_left hM haPos.le
          nlinarith
        have hlowPos : 0 < (1 - κ.a) * (T.S.N k : ℝ) / 400 := by positivity
        have hinv := one_div_le_one_div_of_le hlowPos hdenLower
        calc
          _ ≤ 1 / ((1 - κ.a) * (T.S.N k : ℝ) / 400) := hinv
          _ = A / T.S.N k := by dsimp [A]; field_simp
      have hσ : D.prior s v x ≤
          A * (2 : ℝ) ^ 0 * Real.exp (-(0 : ℝ) * PT.tiling.gain i) /
            T.S.N k := by
        simpa using hσcap.trans hcornerCap
      by_cases hxzero : D.prior s v x = 0
      · have hrow : D.row v (D.prior s v) (D.label s) x = 0 := by
          simp [ListGateContext.row, hxzero]
        rw [hrow]
        have hbase : 0 ≤ Katom * (2 : ℝ) ^ T.S.n k / T.S.N k :=
          div_nonneg (mul_nonneg hKatom.le (by positivity)) hN.le
        have htail : 0 ≤ Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
          Real.rpow_nonneg (by norm_num) _
        exact mul_nonneg (mul_nonneg hbase (Real.exp_pos _).le) htail
      · have hxEnv : x ∈ PT.envelope i :=
          Lane_q_s17_pal.cleanInitialPrior_support_envelope hPT D v
            (D.prior s v) hclean x hxzero
        have hsame : ∀ w ∈ D.externalEarly v, D.G.patchOf w = i := by
          intro w hw
          rcases (Finset.mem_filter.mp hw).2 with ⟨_, j, hjnotI, rfl⟩
          apply Lane_q_s17_pal.patchOf_flip_eq_of_prefix D hPT v i
            (D.G.patchOf_leaf v) j
          simp [i, hell]
        have hdegLower : 1 / 2 - κ.Kbd / (T.S.n k : ℝ) ≤
            deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
          have hown := hPT.envelope_degree i x hxEnv
          have habs : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
              κ.Kbd / (T.S.n k : ℝ) := by
            simpa [OwnDegOK, hm] using hown
          have := (abs_le.mp habs).1
          linarith
        have hdegPos : 0 < deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
          have hbase : 0 < 1 / 2 - κ.Kbd / (T.S.n k : ℝ) := by
            linarith [hKbdEps.2]
          exact lt_of_lt_of_le hbase hdegLower
        let eps : Pos T k → ℝ := fun _ => 4 * (κ.Kbd / (T.S.n k : ℝ))
        have hFactor0 : ∀ w ∈ D.externalEarly v,
            0 ≤ D.hitRatio w x (D.label s w) := by
          intro w hw
          have hdegree : 0 ≤
              deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
            rw [hsame w hw]
            exact le_of_lt hdegPos
          exact Lane_q_s17_pal.hitRatio_nonneg D w x (D.label s w) hdegree
        have hFactor : ∀ w ∈ D.externalEarly v,
            D.hitRatio w x (D.label s w) ≤ 2 * Real.exp (eps w) := by
          intro w hw
          have hdegree : 1 / 2 - κ.Kbd / (T.S.n k : ℝ) ≤
              deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
            rw [hsame w hw]
            exact hdegLower
          have hRatio := Lane_q_s17_pal.hitRatio_le_of_degreeNearHalf D w x
            (D.label s w) (κ.Kbd / (T.S.n k : ℝ)) hKbdEps.1 hKbdEps.2 hdegree
          simpa [eps] using hRatio
        have hGeom := Lane_q_s17_pal.externalEarlyCoordCount D K hPT
          hQuant.geometry v heven
        have hcount : (D.externalEarly v).card + 0 + initialLateCount D v ≤
            T.S.n k + 1 := by
          have hh' : (PT.tiling.P (D.G.patchOf v)).h = 0 := hh
          rw [hh'] at hGeom
          simpa [initialLateCount] using hGeom
        have hcardNat : (D.externalEarly v).card ≤ T.S.n k + 1 := by omega
        have hcard : ((D.externalEarly v).card : ℝ) ≤ (T.S.n k : ℝ) + 1 := by
          exact_mod_cast hcardNat
        have hsumEq :
            (∑ w ∈ D.externalEarly v, eps w) =
              (D.externalEarly v).card * (4 * (κ.Kbd / (T.S.n k : ℝ))) := by
          simp [eps]
        have hsum : (∑ w ∈ D.externalEarly v, eps w) ≤ 8 * κ.Kbd := by
          rw [hsumEq]
          calc
            (D.externalEarly v).card * (4 * (κ.Kbd / (T.S.n k : ℝ))) ≤
            ((T.S.n k : ℝ) + 1) * (4 * (κ.Kbd / (T.S.n k : ℝ))) := by
                  gcongr
            _ ≤ 8 * κ.Kbd := by
              have heq : ((T.S.n k : ℝ) + 1) *
                  (4 * (κ.Kbd / (T.S.n k : ℝ))) =
                  (4 * κ.Kbd * ((T.S.n k : ℝ) + 1)) / (T.S.n k : ℝ) := by
                field_simp [ne_of_gt hnPos]
              rw [heq]
              apply (div_le_iff₀ hnPos).2
              nlinarith [hnPos, hKbdNonneg]
        have hσ0 : 0 ≤ D.prior s v x := hclean.1 x
        have hgain : PT.tiling.gain i = 0 := by simp [Tiling.gain, hm]
        have hscaled := Lane_q_s17_pal.row_le_scaled_of_factors D v
          (D.prior s v) (D.label s) x eps A 0 (PT.tiling.gain i) (8 * κ.Kbd)
          0 (initialLateCount D v) (by positivity) hσ0 hσ
          hFactor0 hFactor hsum hcount
        have hcoeff : 2 * A * Real.exp (8 * κ.Kbd) ≤ Katom := by
          dsimp [Katom]
          apply mul_le_mul_of_nonneg_left
          · exact Real.exp_le_exp.mpr (by linarith)
          · positivity
        calc
          _ ≤ 2 * A * (2 : ℝ) ^ T.S.n k / T.S.N k *
              Real.exp (8 * κ.Kbd - 0 * PT.tiling.gain i) *
                Real.rpow 2 (-(initialLateCount D v : ℝ)) := by
                  simpa [hgain] using hscaled
        _ ≤ Katom * (2 : ℝ) ^ T.S.n k / T.S.N k *
            Real.exp (-200 * PT.tiling.gain i) *
              Real.rpow 2 (-(initialLateCount D v : ℝ)) := by
                  rw [hgain]
                  simp only [mul_zero, Real.exp_zero]
                  have hcommon : 0 ≤
                      (2 : ℝ) ^ T.S.n k / T.S.N k *
                        Real.rpow 2 (-(initialLateCount D v : ℝ)) := by
                    have hpow : 0 ≤ (2 : ℝ) ^ T.S.n k := by positivity
                    have hdiv : 0 ≤ (2 : ℝ) ^ T.S.n k / T.S.N k :=
                      div_nonneg hpow hN.le
                    exact mul_nonneg hdiv
                      (Real.rpow_nonneg (by norm_num) _)
                  calc
                    _ = (2 * A * Real.exp (8 * κ.Kbd)) *
                        ((2 : ℝ) ^ T.S.n k / T.S.N k *
                          Real.rpow 2 (-(initialLateCount D v : ℝ))) := by ring
                    _ ≤ Katom *
                        ((2 : ℝ) ^ T.S.n k / T.S.N k *
                          Real.rpow 2 (-(initialLateCount D v : ℝ))) :=
                      mul_le_mul_of_nonneg_right hcoeff hcommon
                    _ = _ := by ring
  | lowDirect =>
      refine fun v pools s heven htyp hvalid x => ?_
      let i := D.G.patchOf v
      rcases hTV.direct_data (Or.inl hm) i with
        ⟨hscale, hgq, hM, hdirectDeg, hh, hd, hhi⟩
      have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
      have hPpos : 0 < κ.P := by
        have hp := hκ.P_big.2
        rw [hκ.Ac_eq] at hp
        nlinarith
      have hRpos : 0 < (κ.R : ℝ) := by rw [hκ.R_eq]; positivity
      have hA0pos : 0 < κ.A0 := by
        have hA0 := hκ.A0_big
        exact lt_of_lt_of_le (mul_pos (by norm_num) hRpos) hA0
      have hA0ceilNat : ⌈(80 * κ.A0) ^ 2⌉₊ ≤ n₀ :=
        le_max_right (max 256 ⌈4 * κ.Kbd⌉₊) ⌈(80 * κ.A0) ^ 2⌉₊
      have hA0square : (80 * κ.A0) ^ 2 ≤ (T.S.n k : ℝ) := by
        have hceil : (80 * κ.A0) ^ 2 ≤ (⌈(80 * κ.A0) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
        have hnceil : (⌈(80 * κ.A0) ^ 2⌉₊ : ℝ) ≤ (T.S.n k : ℝ) := by
          exact_mod_cast (le_trans hA0ceilNat hk)
        exact le_trans hceil hnceil
      have hsqrtN : 80 * κ.A0 ≤ Real.sqrt (T.S.n k : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [hA0square]
      have hlogBound := Lane_q_s17_pal.log_le_two_sqrt hnPos.le
      have hlogDiv : Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) ≤
          1 / (40 * κ.A0) := by
        have hsqrtPos : 0 < Real.sqrt (T.S.n k : ℝ) := Real.sqrt_pos.2 hnPos
        have hsqr : (Real.sqrt (T.S.n k : ℝ)) ^ 2 = T.S.n k := Real.sq_sqrt hnPos.le
        calc
          _ ≤ 2 * Real.sqrt (T.S.n k : ℝ) / (T.S.n k : ℝ) :=
            div_le_div_of_nonneg_right hlogBound hnPos.le
          _ = 2 / Real.sqrt (T.S.n k : ℝ) := by
            field_simp [ne_of_gt hnPos, ne_of_gt hsqrtPos]
            nlinarith [hsqr]
          _ ≤ 2 / (80 * κ.A0) := by
            apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
              (by positivity : 0 < 80 * κ.A0) hsqrtN
          _ = 1 / (40 * κ.A0) := by field_simp <;> ring
      have hMlower : 0 <
          (1 / 400 : ℝ) * (T.S.N k : ℝ) *
            Real.exp (-Real.rpow ((PT.tiling.P i).g : ℝ) κ.aB) := by positivity
      have hMpos : 0 < (PT.tiling.P i).M := by
        have hMreal : 0 < ((PT.tiling.P i).M : ℝ) := lt_of_lt_of_le hMlower hM
        exact_mod_cast hMreal
      have hnoncluster : ¬ PT.tiling.mode.isCluster := by simp [Mode.isCluster, hm]
      have haPos : 0 < 1 - κ.a := by linarith
      have hcell : D.G.cellOf v ∈ D.scopeCells v := by simp [ListGateContext.scopeCells]
      have hpoolTypical : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) :=
        htyp _ hcell
      have hstateValid : D.stateValid (D.G.cellOf v) (pools (D.G.cellOf v))
          (s (D.G.cellOf v)) := hvalid _ hcell
      have hclean : D.CleanInitialPrior v (D.prior s v) := by
        simpa [ListGateContext.prior] using
          hQuant.prior_shape v (pools (D.G.cellOf v)) (s (D.G.cellOf v))
            heven hpoolTypical hstateValid
      have hσcap := Lane_q_s17_pal.cleanInitialPrior_noncluster_cap D v
        (D.prior s v) hclean ha hMpos hnoncluster x
      have halloc := (hTV.allocation_bounds i).2
      simp [hm] at halloc
      rcases halloc with ⟨hEllBudget, hMassBudget⟩
      have hgain : PT.tiling.gain i = (PT.tiling.P i).g / 1000 := by
        simp [Tiling.gain, hm]
      have hratioPos : 0 < (T.S.N k : ℝ) / (PT.tiling.P i).M := by positivity
      have hratioExp : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤
          Real.exp (PT.tiling.gain i / (1000 * κ.u)) := by
        have h := Real.exp_le_exp.mpr hMassBudget
        rw [Real.exp_log hratioPos] at h
        exact h
      let C : ℝ := 1 / (1 - κ.a)
      let B : ℝ := -(1 / (1000 * κ.u))
      have hCpos : 0 < C := by dsimp [C]; positivity
      have hCleA : C ≤ A := by
        dsimp [C, A]
        exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 400) haPos.le
      have hMrec : 1 / (PT.tiling.P i).M =
          ((T.S.N k : ℝ) / (PT.tiling.P i).M) / T.S.N k := by
        field_simp [ne_of_gt hN, ne_of_gt hMpos]
      have hratioOverN :
          ((T.S.N k : ℝ) / (PT.tiling.P i).M) / T.S.N k ≤
            Real.exp (PT.tiling.gain i / (1000 * κ.u)) / T.S.N k :=
        div_le_div_of_nonneg_right hratioExp hN.le
      have hpriorCap : 1 / ((1 - κ.a) * (PT.tiling.P i).M) ≤
          A * Real.exp (PT.tiling.gain i / (1000 * κ.u)) / T.S.N k := by
        calc
          _ = C * (1 / (PT.tiling.P i).M) := by dsimp [C]; field_simp
          _ = C * (((T.S.N k : ℝ) / (PT.tiling.P i).M) / T.S.N k) := by rw [hMrec]
          _ ≤ A * (((T.S.N k : ℝ) / (PT.tiling.P i).M) / T.S.N k) :=
            mul_le_mul_of_nonneg_right hCleA (by positivity)
          _ ≤ A * (Real.exp (PT.tiling.gain i / (1000 * κ.u)) / T.S.N k) :=
            mul_le_mul_of_nonneg_left hratioOverN (by positivity)
          _ = _ := by ring
      have hσ : D.prior s v x ≤
          A * (2 : ℝ) ^ 0 * Real.exp (-B * PT.tiling.gain i) / T.S.N k := by
        have hexp : -B * PT.tiling.gain i = PT.tiling.gain i / (1000 * κ.u) := by
          dsimp [B]
          ring
        have hσcap' : D.prior s v x ≤
            A * Real.exp (PT.tiling.gain i / (1000 * κ.u)) / T.S.N k := by
          calc
            _ ≤ 1 / ((1 - κ.a) * (PT.tiling.P i).M) := hσcap
            _ ≤ _ := by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpriorCap
        simpa [hexp] using hσcap'
      let delta : ℝ := (PT.tiling.P i).g / (4 * (T.S.n k : ℝ))
      have hdeltaNonneg : 0 ≤ (PT.tiling.P i).g / (4 * (T.S.n k : ℝ)) := by positivity
      have hιle : κ.ι / 2 ≤ 1 := by
        have hι := hκ.ι_rng.2
        have hmin : min κ.xs (min κ.η0 0.01) ≤ κ.xs := min_le_left _ _
        have hxsSmall : κ.xs < 0.01 := hκ.xs_rng.2
        have hιSmall : κ.ι < κ.xs / 1000 := by
          calc
            κ.ι < min κ.xs (min κ.η0 0.01) / 1000 := hι
            _ ≤ κ.xs / 1000 := div_le_div_of_nonneg_right hmin (by norm_num)
        have hιlt : κ.ι < 1 := by
          calc
            κ.ι < κ.xs / 1000 := hιSmall
            _ < 1 := by nlinarith [hxsSmall]
        nlinarith
      have hgScale := hTV.direct_scale_bound (Or.inl hm) i
      have hgLeN : (PT.tiling.P i).g ≤ T.S.n k := by
        have hnOne : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast (show 1 ≤ T.S.n k by omega)
        have hpow := Real.rpow_le_rpow_of_exponent_le
          hnOne hιle
        have hpow' : (T.S.n k : ℝ) ^ (κ.ι / 2) ≤ (T.S.n k : ℝ) := by
          simpa [Real.rpow_one] using hpow
        have hgReal : ((PT.tiling.P i).g : ℝ) ≤ (T.S.n k : ℝ) :=
          le_trans hgScale hpow'
        exact_mod_cast hgReal
      have hdeltaLe : (PT.tiling.P i).g / (4 * (T.S.n k : ℝ)) ≤ 1 / 4 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (T.S.n k : ℝ))).2
        have hgLeNReal : ((PT.tiling.P i).g : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hgLeN
        nlinarith [hgLeNReal]
      have hdeltaHalf : delta ≤ 1 / 2 := by
        dsimp [delta]
        linarith [hdeltaLe]
      have hbstar := Lane_q_s17_pal.dimNegBstar_le_oneSixteenth (by omega : 256 ≤ T.S.n k)
      have hbstar' : bstar T k ≤ 1 / 16 := by simpa [bstar] using hbstar
      have hbstarNonneg : 0 ≤ bstar T k := by
        unfold bstar
        exact Real.rpow_nonneg (by positivity) _
      have hcrossErrNonneg : 0 ≤ 12 * bstar T k := mul_nonneg (by norm_num) hbstarNonneg
      have hcrossErrLe : 3 * bstar T k ≤ 1 / 4 := by nlinarith [hbstar']
      have huNat : 1 ≤ κ.u := by have hu := hκ.u_rng.2; omega
      have hu : 1 ≤ (κ.u : ℝ) := by exact_mod_cast huNat
      have hEllBudget' : ((PT.tiling.P i).ℓ : ℝ) ≤
          (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := by
        rw [hgain] at hEllBudget
        calc
          _ ≤ ((PT.tiling.P i).g / 1000) / (1000 * (κ.u : ℝ)) := hEllBudget
          _ = _ := by field_simp <;> ring
      have hEllBound : ((PT.tiling.P i).ℓ : ℝ) ≤
          ((PT.tiling.P i).g : ℝ) / 1000000 := by
        have hrecip : 1 / (1000000 * (κ.u : ℝ)) ≤ 1 / 1000000 :=
          one_div_le_one_div_of_le (by norm_num) (by nlinarith [hu])
        calc
          _ ≤ (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := hEllBudget'
          _ = (PT.tiling.P i).g * (1 / (1000000 * (κ.u : ℝ))) := by ring
          _ ≤ (PT.tiling.P i).g * (1 / 1000000) :=
            mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg _)
          _ = (PT.tiling.P i).g / 1000000 := by ring
      have hEllOverN : (PT.tiling.P i).ℓ / (T.S.n k : ℝ) ≤ 1 / 1000000 := by
        have hdiv := div_le_div_of_nonneg_right hEllBound hnPos.le
        calc
          _ ≤ ((PT.tiling.P i).g / 1000000) / (T.S.n k : ℝ) := hdiv
          _ = ((PT.tiling.P i).g / (T.S.n k : ℝ)) / 1000000 := by field_simp <;> ring
          _ ≤ 1 / 1000000 := by
            have hgLeNReal : ((PT.tiling.P i).g : ℝ) ≤ (T.S.n k : ℝ) := by
              exact_mod_cast hgLeN
            have hgdiv : (PT.tiling.P i).g / (T.S.n k : ℝ) ≤ 1 :=
              div_le_one_of_le₀ hgLeNReal hnPos.le
            exact div_le_div_of_nonneg_right hgdiv (by norm_num)
      by_cases hxzero : D.prior s v x = 0
      · have hrow : D.row v (D.prior s v) (D.label s) x = 0 := by
          simp [ListGateContext.row, hxzero]
        rw [hrow]
        have hbase : 0 ≤ Katom * (2 : ℝ) ^ T.S.n k / T.S.N k :=
          div_nonneg (mul_nonneg hKatom.le (by positivity)) hN.le
        have htail : 0 ≤ Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
          Real.rpow_nonneg (by norm_num) _
        exact mul_nonneg (mul_nonneg hbase (Real.exp_pos _).le) htail
      · have hxEnv : x ∈ PT.envelope i :=
          Lane_q_s17_pal.cleanInitialPrior_support_envelope hPT D v
            (D.prior s v) hclean x hxzero
        let eps : Pos T k → ℝ := fun w =>
          if D.G.patchOf w = i then -delta else 12 * bstar T k
        have hown : OwnDegOK PT.tiling i (PT.π i) x := hPT.envelope_degree i x hxEnv
        have hownData :
            1 / 2 + delta ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x ∧
            deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
              1 / 2 + 4 * (PT.tiling.P i).g / (T.S.n k : ℝ) := by
          simpa [OwnDegOK, hm, delta] using hown
        have hdegNonneg (w : Pos T k) :
            0 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
          unfold deg
          apply Finset.sum_nonneg
          intro y hy
          apply mul_nonneg
          · exact (PT.π (D.G.patchOf w)).nonneg y
          · by_cases hhit : Hits (T.S.E k) PT.tiling.c x y <;> simp [hit, hhit]
        have hFactor0 : ∀ w ∈ D.externalEarly v,
            0 ≤ D.hitRatio w x (D.label s w) := by
          intro w hw
          exact Lane_q_s17_pal.hitRatio_nonneg D w x (D.label s w) (hdegNonneg w)
        have hFactor : ∀ w ∈ D.externalEarly v,
            D.hitRatio w x (D.label s w) ≤ 2 * Real.exp (eps w) := by
          intro w hw
          by_cases hsame : D.G.patchOf w = i
          · have hdegree : 1 / 2 + delta ≤
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
              rw [hsame]
              exact hownData.1
            have hRatio := Lane_q_s17_pal.hitRatio_le_of_degreeAboveHalf D w x
              (D.label s w) delta hdeltaNonneg hdeltaHalf hdegree
            simpa [eps, hsame] using hRatio
          · have hother := hPT.envelope_other_degree i (D.G.patchOf w) hsame x hxEnv
            have hlower : 1 / 2 - 3 * bstar T k ≤
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
              have := (abs_le.mp hother).1
              linarith
            have hRatio := Lane_q_s17_pal.hitRatio_le_of_degreeNearHalf D w x
              (D.label s w) (3 * bstar T k)
              (mul_nonneg (by norm_num) hbstarNonneg) hcrossErrLe hlower
            have heps : 4 * (3 * bstar T k) = 12 * bstar T k := by ring
            simpa [eps, hsame, heps] using hRatio
        have hGeom := Lane_q_s17_pal.externalEarlyCoordCount D K hPT
          hQuant.geometry v heven
        have hcount : (D.externalEarly v).card + 0 + initialLateCount D v ≤
            T.S.n k + 1 := by
          have hh' : (PT.tiling.P (D.G.patchOf v)).h = 0 := hh
          rw [hh'] at hGeom
          simpa [initialLateCount] using hGeom
        let Same : Finset (Pos T k) := (D.externalEarly v).filter fun w =>
          D.G.patchOf w = i
        let Cross : Finset (Pos T k) := (D.externalEarly v).filter fun w =>
          D.G.patchOf w ≠ i
        have hSameNat := Lane_q_s17_pal.samePatchExternalEarly_card_lower D hPT v
        have hSameLower : T.S.n k - (PT.tiling.P i).ℓ -
            initialLateCount D v ≤ Same.card := by
          have hh' : (PT.tiling.P (D.G.patchOf v)).h = 0 := hh
          simpa [Same, initialLateCount, hh'] using hSameNat
        have hCrossUpper := Lane_q_s17_pal.externalEarly_crossPatch_card_le_prefix D hPT v
        have hCross : Cross.card ≤ (PT.tiling.P i).ℓ := by simpa [Cross] using hCrossUpper
        have hlateNat := Lane_q_s17_pal.lateNeighborCount_le_r D K hQuant.geometry v
        have hLateUpper : (initialLateCount D v : ℝ) ≤
            2 * κ.A0 * Real.log (T.S.n k : ℝ) := by
          have hLateCast : (initialLateCount D v : ℝ) ≤ D.G.r := by
            exact_mod_cast hlateNat
          exact le_of_lt (lt_of_le_of_lt hLateCast hQuant.geometry.class_scale.2)
        have hLateOverN : (initialLateCount D v : ℝ) / (T.S.n k : ℝ) ≤ 1 / 20 := by
          calc
            _ ≤ (2 * κ.A0 * Real.log (T.S.n k : ℝ)) / (T.S.n k : ℝ) :=
              div_le_div_of_nonneg_right hLateUpper hnPos.le
            _ = 2 * κ.A0 * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) := by ring
            _ ≤ 2 * κ.A0 * (1 / (40 * κ.A0)) :=
              mul_le_mul_of_nonneg_left hlogDiv (by positivity)
            _ = 1 / 20 := by field_simp <;> ring
        have hEllLateReal :
            (PT.tiling.P i).ℓ + (initialLateCount D v : ℝ) ≤ (T.S.n k : ℝ) := by
          have hsum : (PT.tiling.P i).ℓ / (T.S.n k : ℝ) +
              (initialLateCount D v : ℝ) / (T.S.n k : ℝ) ≤ 1 := by
            linarith [hEllOverN, hLateOverN]
          have heq : ((PT.tiling.P i).ℓ + (initialLateCount D v : ℝ)) /
              (T.S.n k : ℝ) = (PT.tiling.P i).ℓ / (T.S.n k : ℝ) +
                (initialLateCount D v : ℝ) / (T.S.n k : ℝ) := by
            field_simp [ne_of_gt hnPos] <;> ring
          have hdiv : ((PT.tiling.P i).ℓ + (initialLateCount D v : ℝ)) /
              (T.S.n k : ℝ) ≤ 1 := by rw [heq]; exact hsum
          simpa using (div_le_iff₀ hnPos).1 hdiv
        have hEllLateNat : (PT.tiling.P i).ℓ + initialLateCount D v ≤ T.S.n k := by
          exact_mod_cast hEllLateReal
        have hsumEq :
            (∑ w ∈ D.externalEarly v, eps w) =
              -delta * (Same.card : ℝ) + (12 * bstar T k) * (Cross.card : ℝ) := by
          have hSameSum : (∑ w ∈ Same, eps w) =
              -delta * (Same.card : ℝ) := by
            calc
              _ = ∑ w ∈ Same, -delta := by
                apply Finset.sum_congr rfl
                intro w hw
                simp [eps, Same, (Finset.mem_filter.mp hw).2]
              _ = _ := by simp [Finset.sum_const, nsmul_eq_mul] <;> ring
          have hCrossSum : (∑ w ∈ Cross, eps w) =
              (12 * bstar T k) * (Cross.card : ℝ) := by
            calc
              _ = ∑ w ∈ Cross, (12 * bstar T k) := by
                apply Finset.sum_congr rfl
                intro w hw
                simp [eps, Cross, (Finset.mem_filter.mp hw).2]
              _ = _ := by simp [Finset.sum_const, nsmul_eq_mul] <;> ring
          have hpartition : (∑ w ∈ D.externalEarly v, eps w) =
              (∑ w ∈ Same, eps w) + (∑ w ∈ Cross, eps w) := by
            rw [← Finset.sum_filter_add_sum_filter_not _
              (fun w => D.G.patchOf w = i)]
          rw [hpartition, hSameSum, hCrossSum]
        have hE : (∑ w ∈ D.externalEarly v, eps w) ≤
            -(9 / 40 : ℝ) * (PT.tiling.P i).g := by
          have hEllLeN : (PT.tiling.P i).ℓ ≤ T.S.n k := by omega
          have hLateLe : initialLateCount D v ≤ T.S.n k - (PT.tiling.P i).ℓ := by omega
          have hsub :
              ((T.S.n k - (PT.tiling.P i).ℓ - initialLateCount D v : ℕ) : ℝ) =
                (T.S.n k : ℝ) - (PT.tiling.P i).ℓ - initialLateCount D v := by
            rw [Nat.cast_sub hLateLe, Nat.cast_sub hEllLeN] <;>
              push_cast <;> ring
          have hSameCast :
              ((T.S.n k - (PT.tiling.P i).ℓ - initialLateCount D v : ℕ) : ℝ) ≤
                (Same.card : ℝ) := by exact_mod_cast hSameLower
          have hSameLowerReal : (T.S.n k : ℝ) - (PT.tiling.P i).ℓ -
              (initialLateCount D v : ℝ) ≤ (Same.card : ℝ) := by
            rw [← hsub]
            exact hSameCast
          have hCrossReal : (Cross.card : ℝ) ≤ (PT.tiling.P i).ℓ := by
            exact_mod_cast hCross
          have hnegPart : -delta * (Same.card : ℝ) ≤
              -delta * ((T.S.n k : ℝ) - (PT.tiling.P i).ℓ - initialLateCount D v) :=
            mul_le_mul_of_nonpos_left hSameLowerReal (by linarith [hdeltaNonneg])
          have hposPart : (12 * bstar T k) * (Cross.card : ℝ) ≤
              (12 * bstar T k) * (PT.tiling.P i).ℓ :=
            mul_le_mul_of_nonneg_left hCrossReal hcrossErrNonneg
          have hmainEq : -delta * ((T.S.n k : ℝ) - (PT.tiling.P i).ℓ -
              (initialLateCount D v : ℝ)) =
              -(PT.tiling.P i).g / 4 + delta *
                ((PT.tiling.P i).ℓ + (initialLateCount D v : ℝ)) := by
            dsimp [delta]
            field_simp [ne_of_gt hnPos] <;> ring
          have hErrEq : delta * ((PT.tiling.P i).ℓ +
              (initialLateCount D v : ℝ)) =
              ((PT.tiling.P i).g / 4) *
                ((PT.tiling.P i).ℓ / (T.S.n k : ℝ) +
                  (initialLateCount D v : ℝ) / (T.S.n k : ℝ)) := by
            dsimp [delta]
            field_simp [ne_of_gt hnPos] <;> ring
          have hGammaLe : 12 * bstar T k ≤ 3 / 4 := by nlinarith [hbstar']
          have hCrossError : (12 * bstar T k) * (PT.tiling.P i).ℓ ≤
              (PT.tiling.P i).g / 1000000 := by
            have hEllNonneg : 0 ≤ ((PT.tiling.P i).ℓ : ℝ) := Nat.cast_nonneg _
            have hgSmallNonneg : 0 ≤ ((PT.tiling.P i).g : ℝ) / 1000000 := by positivity
            have hmul := mul_le_mul hGammaLe hEllBound
              hEllNonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
            nlinarith [hmul, hGammaLe, hEllBound]
          have hratioErr : (PT.tiling.P i).ℓ / (T.S.n k : ℝ) +
              (initialLateCount D v : ℝ) / (T.S.n k : ℝ) ≤ 1 / 1000000 + 1 / 20 :=
            add_le_add hEllOverN hLateOverN
          rw [hsumEq]
          calc
            -delta * (Same.card : ℝ) + (12 * bstar T k) * (Cross.card : ℝ)
                ≤ -delta * ((T.S.n k : ℝ) - (PT.tiling.P i).ℓ - initialLateCount D v) +
                    (12 * bstar T k) * (PT.tiling.P i).ℓ := add_le_add hnegPart hposPart
            _ = -(PT.tiling.P i).g / 4 +
                  delta * ((PT.tiling.P i).ℓ + (initialLateCount D v : ℝ)) +
                    (12 * bstar T k) * (PT.tiling.P i).ℓ := by rw [hmainEq]
            _ ≤ -(PT.tiling.P i).g / 4 +
                  ((PT.tiling.P i).g / 4) *
                    (1 / 1000000 + 1 / 20) + (PT.tiling.P i).g / 1000000 := by
              rw [hErrEq]
              have hgOver4Nonneg : 0 ≤ ((PT.tiling.P i).g : ℝ) / 4 := by positivity
              have hErrorBound := add_le_add
                (mul_le_mul_of_nonneg_left hratioErr hgOver4Nonneg) hCrossError
              nlinarith [hErrorBound]
            _ ≤ -(9 / 40 : ℝ) * (PT.tiling.P i).g := by
              nlinarith [show 0 ≤ (PT.tiling.P i).g from Nat.cast_nonneg _]
        have hscaled := Lane_q_s17_pal.row_le_scaled_of_factors D v
          (D.prior s v) (D.label s) x eps A B (PT.tiling.gain i) (-(9 / 40 : ℝ) * (PT.tiling.P i).g)
          0 (initialLateCount D v) (by positivity) (hclean.1 x) (by
            have hEq : -B * PT.tiling.gain i = PT.tiling.gain i / (1000 * κ.u) := by
              dsimp [B]
              ring
            have hσcap' : D.prior s v x ≤
                A * Real.exp (PT.tiling.gain i / (1000 * κ.u)) / T.S.N k := by
              calc
                _ ≤ 1 / ((1 - κ.a) * (PT.tiling.P i).M) := hσcap
                _ ≤ _ := by
                  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpriorCap
            simpa [hEq] using hσcap')
          hFactor0 hFactor hE hcount
        have hExp :
            (-(9 / 40 : ℝ) * (PT.tiling.P i).g) - B * PT.tiling.gain i ≤
              -200 * PT.tiling.gain i := by
          have huOne : 1 ≤ (κ.u : ℝ) := by exact_mod_cast (by omega : 1 ≤ κ.u)
          have huPos : 0 < (κ.u : ℝ) := by positivity
          have hrecip : 1 / (1000000 * (κ.u : ℝ)) ≤ 1 / 1000000 :=
            one_div_le_one_div_of_le (by norm_num) (by nlinarith [huOne])
          have hgNonneg : 0 ≤ ((PT.tiling.P i).g : ℝ) := Nat.cast_nonneg _
          have htermSmall : (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) ≤
              (PT.tiling.P i).g / 40 := by
            calc
              _ = (PT.tiling.P i).g * (1 / (1000000 * (κ.u : ℝ))) := by ring
              _ ≤ (PT.tiling.P i).g * (1 / 1000000) :=
                mul_le_mul_of_nonneg_left hrecip hgNonneg
              _ = (PT.tiling.P i).g / 1000000 := by ring
              _ ≤ (PT.tiling.P i).g / 40 := by
                have hc : 1 / (1000000 : ℝ) ≤ 1 / 40 :=
                  one_div_le_one_div_of_le (by norm_num) (by norm_num)
                have h := mul_le_mul_of_nonneg_left hc hgNonneg
                simpa [div_eq_mul_inv] using h
          have hExpEq :
              (-(9 / 40 : ℝ) * (PT.tiling.P i).g) - B * PT.tiling.gain i =
                -(9 / 40 : ℝ) * (PT.tiling.P i).g +
                  (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := by
            rw [hgain]
            dsimp [B]
            field_simp [ne_of_gt huPos] <;> ring
          calc
            _ = -(9 / 40 : ℝ) * (PT.tiling.P i).g +
                (PT.tiling.P i).g / (1000000 * (κ.u : ℝ)) := hExpEq
            _ ≤ -(9 / 40 : ℝ) * (PT.tiling.P i).g +
                (PT.tiling.P i).g / 40 := by nlinarith [htermSmall]
            _ = -200 * PT.tiling.gain i := by rw [hgain]; ring
        have hcoeff : 2 * A ≤ Katom := by
          have hfactor : 1 ≤ Real.exp (8 * κ.Kbd + 1) :=
            Real.one_le_exp (by positivity)
          calc
            2 * A = (2 * A) * 1 := by ring
            _ ≤ (2 * A) * Real.exp (8 * κ.Kbd + 1) :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            _ = Katom := by rfl
        calc
          _ ≤ 2 * A * (2 : ℝ) ^ T.S.n k / T.S.N k *
              Real.exp ((-(9 / 40 : ℝ) * (PT.tiling.P i).g) - B * PT.tiling.gain i) *
                Real.rpow 2 (-(initialLateCount D v : ℝ)) := hscaled
          _ = ((2 * A) * ((2 : ℝ) ^ T.S.n k / T.S.N k) *
                Real.rpow 2 (-(initialLateCount D v : ℝ))) *
              Real.exp ((-(9 / 40 : ℝ) * (PT.tiling.P i).g) - B * PT.tiling.gain i) := by ring
          _ ≤ _ := by
            have hpowNonneg : 0 ≤ (2 : ℝ) ^ T.S.n k := by positivity
            have hdivNonneg : 0 ≤ (2 : ℝ) ^ T.S.n k / T.S.N k :=
              div_nonneg hpowNonneg hN.le
            have hrpowNonneg : 0 ≤ Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              Real.rpow_nonneg (by norm_num) _
            have hFactorNonneg : 0 ≤
                (2 * A) * ((2 : ℝ) ^ T.S.n k / T.S.N k) *
                  Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              mul_nonneg (mul_nonneg (by positivity) hdivNonneg) hrpowNonneg
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hFactorNonneg
          _ = (2 * A) *
              ((2 : ℝ) ^ T.S.n k / T.S.N k * Real.exp (-200 * PT.tiling.gain i) *
                Real.rpow 2 (-(initialLateCount D v : ℝ))) := by ring
          _ ≤ Katom *
              ((2 : ℝ) ^ T.S.n k / T.S.N k * Real.exp (-200 * PT.tiling.gain i) *
                Real.rpow 2 (-(initialLateCount D v : ℝ))) :=
            mul_le_mul_of_nonneg_right hcoeff
              (mul_nonneg (mul_nonneg (div_nonneg (by positivity) hN.le)
                (Real.exp_pos _).le) (Real.rpow_nonneg (by norm_num) _))
          _ = _ := by ring
  | lowCluster =>
      refine fun v pools s heven htyp hvalid x => ?_
      let i := D.G.patchOf v
      rcases hTV.cluster_data (Or.inl hm) i with
        ⟨hscale, hg, hM, hdsmall, hdh, hcodeg, hdyadic, hpowLow,
          hpowHigh, hmodeLow, hmodeSmall, hmodeLarge⟩
      have hM1pos : 0 < κ.M1 := by linarith [hκ.M1_big.1]
      have hqNonneg : 0 ≤ ((PT.tiling.P i).q : ℝ) := by positivity
      have hqM1 : (PT.tiling.P i).q ≤ κ.M1 * (PT.tiling.P i).q := by
        nlinarith [hκ.M1_big.1, hqNonneg]
      have hmax : ((max (PT.tiling.P i).g (PT.tiling.P i).q : ℕ) : ℝ) ≤
          κ.M1 * (PT.tiling.P i).q := by
        simpa [Nat.cast_max] using max_le hg hqM1
      have hq0 : κ.Q0 ≤ (PT.tiling.P i).q := by
        by_contra hnq
        have hqLt : (PT.tiling.P i).q < κ.Q0 := lt_of_not_ge hnq
        have hmul : κ.M1 * (PT.tiling.P i).q < κ.M1 * κ.Q0 :=
          mul_lt_mul_of_pos_left hqLt hM1pos
        linarith [hscale, hmax]
      have hQ := hκ.Q0_large (PT.tiling.P i).q hq0
      rcases hQ with ⟨_, _, _, _, _, _, _, hQ8, _⟩
      have hpowLow' : Real.rpow (PT.tiling.P i).q κ.Mlo ≤
          (PT.tiling.P i).h := by simpa [hm] using hpowLow
      have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have haLt : κ.a < 1 := Lane_q_s17_pal.a_lt_one κ hκ
      have hgain : PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
        simp [Tiling.gain, hm]
      have halloc := (hTV.allocation_bounds i).2
      simp [hm] at halloc
      rcases halloc with ⟨hEllBudget, _⟩
      have huNat : 1 ≤ κ.u := by have hu := hκ.u_rng.2; omega
      have hu : 1 ≤ (κ.u : ℝ) := by exact_mod_cast huNat
      have hQ8Bound : 40 * Real.rpow (PT.tiling.P i).q κ.Cb ≤
          PT.tiling.gain i / (100 * κ.u) := by
        have hcoef : 0 ≤ κ.a / 10 ^ 6 := by positivity
        have hmiddle :
          (κ.a / 10 ^ 6) * Real.rpow (PT.tiling.P i).q κ.Mlo ≤
              (κ.a / 10 ^ 6) * (PT.tiling.P i).h :=
          mul_le_mul_of_nonneg_left hpowLow' hcoef
        calc
          _ ≤ (κ.a / 10 ^ 6) * Real.rpow (PT.tiling.P i).q κ.Mlo /
                (100 * κ.u) := hQ8
          _ ≤ ((κ.a / 10 ^ 6) * (PT.tiling.P i).h) /
                (100 * κ.u) := div_le_div_of_nonneg_right hmiddle (by positivity)
          _ = PT.tiling.gain i / (100 * κ.u) := by rw [hgain]; ring
      have hHsup : (PT.tiling.P i).h ≤
          Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h := by
        exact Finset.le_sup (s := Finset.univ)
          (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
      have hglobal := hTV.prefix_internal_length
      change (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) +
          (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h) ≤ T.S.n k at hglobal
      have hSupLe : (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h) ≤
          T.S.n k := by
        calc
          _ ≤ (Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) +
              Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
            Nat.le_add_left _ _
          _ ≤ T.S.n k := hglobal
      have hHeightLeN : (PT.tiling.P i).h ≤ T.S.n k := le_trans hHsup hSupLe
      have hgainNonneg : 0 ≤ PT.tiling.gain i := by rw [hgain]; positivity
      have hgainUpper : PT.tiling.gain i ≤ (T.S.n k : ℝ) / 10 ^ 6 := by
        have hheightNonneg : 0 ≤ ((PT.tiling.P i).h : ℝ) := Nat.cast_nonneg _
        have hmul : κ.a * ((PT.tiling.P i).h : ℝ) ≤ ((PT.tiling.P i).h : ℝ) := by
          simpa using mul_le_mul_of_nonneg_right haLt.le hheightNonneg
        rw [hgain]
        calc
          _ ≤ ((PT.tiling.P i).h : ℝ) / 10 ^ 6 :=
            div_le_div_of_nonneg_right hmul (by positivity)
          _ ≤ (T.S.n k : ℝ) / 10 ^ 6 :=
            div_le_div_of_nonneg_right (by exact_mod_cast hHeightLeN) (by positivity)
      have hownNumer : 40 * Real.rpow (PT.tiling.P i).q κ.Cb ≤
          (T.S.n k : ℝ) / 10 ^ 8 := by
        calc
          _ ≤ PT.tiling.gain i / (100 * κ.u) := hQ8Bound
          _ ≤ ((T.S.n k : ℝ) / 10 ^ 6) / (100 * κ.u) :=
            div_le_div_of_nonneg_right hgainUpper (by positivity)
          _ = (T.S.n k : ℝ) / (10 ^ 8 * κ.u) := by field_simp; ring
          _ ≤ (T.S.n k : ℝ) / 10 ^ 8 := by
            have hrecip : 1 / (10 ^ 8 * (κ.u : ℝ)) ≤ 1 / 10 ^ 8 :=
              one_div_le_one_div_of_le (by norm_num) (by nlinarith [show (1 : ℝ) ≤ κ.u by exact_mod_cast (by omega : 1 ≤ κ.u)])
            have h := mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ (T.S.n k : ℝ))
            simpa [div_eq_mul_inv] using h
      have hownDelta : 10 * Real.rpow (PT.tiling.P i).q κ.Cb /
          (T.S.n k : ℝ) ≤ 1 / 4 := by
        have hquarter : 10 * Real.rpow (PT.tiling.P i).q κ.Cb ≤
            (T.S.n k : ℝ) / 4 := by
          calc
            _ = (40 * Real.rpow (PT.tiling.P i).q κ.Cb) / 4 := by ring
            _ ≤ ((T.S.n k : ℝ) / 10 ^ 8) / 4 :=
              div_le_div_of_nonneg_right hownNumer (by norm_num)
            _ ≤ (T.S.n k : ℝ) / 4 := by
              have hrecip : 1 / (10 ^ 8 : ℝ) ≤ 1 := by norm_num
              have hbig : (T.S.n k : ℝ) / 10 ^ 8 ≤ (T.S.n k : ℝ) := by
                calc
                  _ = (T.S.n k : ℝ) * (1 / (10 ^ 8 : ℝ)) := by ring
                  _ ≤ (T.S.n k : ℝ) * 1 := mul_le_mul_of_nonneg_left hrecip (by positivity)
                  _ = (T.S.n k : ℝ) := by ring
              exact div_le_div_of_nonneg_right hbig (by norm_num)
        exact (div_le_iff₀ hnPos).2 (by nlinarith [hquarter])
      have hbstar : bstar T k ≤ 1 / 16 := by
        have h := Lane_q_s17_pal.dimNegBstar_le_oneSixteenth (by omega : 256 ≤ T.S.n k)
        simpa [bstar] using h
      have hbstarNonneg : 0 ≤ bstar T k := by
        unfold bstar
        exact Real.rpow_nonneg (by positivity) _
      have hcrossErrNonneg : 0 ≤ 12 * bstar T k :=
        mul_nonneg (by norm_num) hbstarNonneg
      have hcrossErrLe : 3 * bstar T k ≤ 1 / 4 := by nlinarith [hbstar]
      have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
      have hMpos : 0 < (PT.tiling.P i).M := by
        have hlower : 0 < (1 / 400 : ℝ) * (T.S.N k : ℝ) *
            Real.exp (-Real.rpow ((PT.tiling.P i).q : ℝ) κ.aC) := by positivity
        exact_mod_cast (lt_of_lt_of_le hlower hM)
      have hcluster : PT.tiling.mode.isCluster := by simp [Mode.isCluster, hm]
      have hcell : D.G.cellOf v ∈ D.scopeCells v := by simp [ListGateContext.scopeCells]
      have hpoolTypical : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) :=
        htyp _ hcell
      have hstateValid : D.stateValid (D.G.cellOf v) (pools (D.G.cellOf v))
          (s (D.G.cellOf v)) := hvalid _ hcell
      have hclean : D.CleanInitialPrior v (D.prior s v) := by
        simpa [ListGateContext.prior] using
          hQuant.prior_shape v (pools (D.G.cellOf v)) (s (D.G.cellOf v))
            heven hpoolTypical hstateValid
      have hσcap := Lane_q_s17_pal.cleanInitialPrior_cluster_cap D v
        (D.prior s v) hclean hcluster x
      have hσ : D.prior s v x ≤
          (2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (-500 * PT.tiling.gain i) /
            T.S.N k := by
        apply (le_div_iff₀ hN).2
        simpa [mul_comm] using hσcap
      by_cases hxzero : D.prior s v x = 0
      · have hrow : D.row v (D.prior s v) (D.label s) x = 0 := by
          simp [ListGateContext.row, hxzero]
        rw [hrow]
        have hbase : 0 ≤ Katom * (2 : ℝ) ^ T.S.n k / T.S.N k :=
          div_nonneg (mul_nonneg hKatom.le (by positivity)) hN.le
        exact mul_nonneg (mul_nonneg hbase (Real.exp_pos _).le)
          (Real.rpow_nonneg (by norm_num) _)
      · have hxEnv : x ∈ PT.envelope i :=
          Lane_q_s17_pal.cleanInitialPrior_support_envelope hPT D v
            (D.prior s v) hclean x hxzero
        let ownErr : ℝ := 10 * Real.rpow (PT.tiling.P i).q κ.Cb /
          (T.S.n k : ℝ)
        let eps : Pos T k → ℝ := fun w =>
          if D.G.patchOf w = i then 4 * ownErr else 12 * bstar T k
        have hqcbNonneg : 0 ≤ Real.rpow (PT.tiling.P i).q κ.Cb :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hownErrNonneg : 0 ≤ ownErr := by
          dsimp [ownErr]
          exact div_nonneg (mul_nonneg (by norm_num) hqcbNonneg) hnPos.le
        have hown : OwnDegOK PT.tiling i (PT.π i) x := hPT.envelope_degree i x hxEnv
        have habs : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
            ownErr := by simpa [OwnDegOK, hm, ownErr] using hown
        have hdegNonneg (w : Pos T k) :
            0 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
          unfold deg
          apply Finset.sum_nonneg
          intro y hy
          apply mul_nonneg
          · exact (PT.π (D.G.patchOf w)).nonneg y
          · by_cases hhit : Hits (T.S.E k) PT.tiling.c x y <;> simp [hit, hhit]
        have hFactor0 : ∀ w ∈ D.externalEarly v,
            0 ≤ D.hitRatio w x (D.label s w) := by
          intro w hw
          exact Lane_q_s17_pal.hitRatio_nonneg D w x (D.label s w) (hdegNonneg w)
        have hFactor : ∀ w ∈ D.externalEarly v,
            D.hitRatio w x (D.label s w) ≤ 2 * Real.exp (eps w) := by
          intro w hw
          by_cases hsame : D.G.patchOf w = i
          · have hlow : 1 / 2 - ownErr ≤
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
              rw [hsame]
              have := (abs_le.mp habs).1
              linarith
            have hRatio := Lane_q_s17_pal.hitRatio_le_of_degreeNearHalf D w x
              (D.label s w) ownErr hownErrNonneg (by linarith [hownDelta]) hlow
            simpa [eps, hsame, ownErr] using hRatio
          · have hother := hPT.envelope_other_degree i (D.G.patchOf w) hsame x hxEnv
            have hlower : 1 / 2 - 3 * bstar T k ≤
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
              have := (abs_le.mp hother).1
              linarith
            have hRatio := Lane_q_s17_pal.hitRatio_le_of_degreeNearHalf D w x
              (D.label s w) (3 * bstar T k)
              (mul_nonneg (by norm_num) hbstarNonneg) hcrossErrLe hlower
            have heps : 4 * (3 * bstar T k) = 12 * bstar T k := by ring
            simpa [eps, hsame, heps] using hRatio
        have hGeom := Lane_q_s17_pal.externalEarlyCoordCount D K hPT
          hQuant.geometry v heven
        have hcount : (D.externalEarly v).card + (PT.tiling.P i).h +
            initialLateCount D v ≤ T.S.n k + 1 := by
          simpa [initialLateCount] using hGeom
        let Same : Finset (Pos T k) := (D.externalEarly v).filter fun w =>
          D.G.patchOf w = i
        let Cross : Finset (Pos T k) := (D.externalEarly v).filter fun w =>
          D.G.patchOf w ≠ i
        have hSameSum : (∑ w ∈ Same, eps w) =
            (4 * ownErr) * (Same.card : ℝ) := by
          calc
            _ = ∑ w ∈ Same, 4 * ownErr := by
              apply Finset.sum_congr rfl
              intro w hw
              simp [eps, Same, (Finset.mem_filter.mp hw).2]
            _ = _ := by simp [Finset.sum_const, nsmul_eq_mul] <;> ring
        have hCrossSum : (∑ w ∈ Cross, eps w) =
            (12 * bstar T k) * (Cross.card : ℝ) := by
          calc
            _ = ∑ w ∈ Cross, 12 * bstar T k := by
              apply Finset.sum_congr rfl
              intro w hw
              simp [eps, Cross, (Finset.mem_filter.mp hw).2]
            _ = _ := by simp [Finset.sum_const, nsmul_eq_mul] <;> ring
        have hpartition : (∑ w ∈ D.externalEarly v, eps w) =
            (∑ w ∈ Same, eps w) + (∑ w ∈ Cross, eps w) := by
          rw [← Finset.sum_filter_add_sum_filter_not _
            (fun w => D.G.patchOf w = i)]
        have hSameCard : (Same.card : ℝ) ≤ (D.externalEarly v).card := by
          exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
        have hCrossCard : (Cross.card : ℝ) ≤ (PT.tiling.P i).ℓ := by
          exact_mod_cast (Lane_q_s17_pal.externalEarly_crossPatch_card_le_prefix D hPT v)
        have hcardNat : (D.externalEarly v).card ≤ T.S.n k + 1 := by omega
        have hcard : ((D.externalEarly v).card : ℝ) ≤ (T.S.n k : ℝ) + 1 := by
          exact_mod_cast hcardNat
        have hnDim : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
        have hSameBound : (4 * ownErr) * (Same.card : ℝ) ≤
            80 * Real.rpow (PT.tiling.P i).q κ.Cb := by
          calc
            _ ≤ (4 * ownErr) * (D.externalEarly v).card :=
              mul_le_mul_of_nonneg_left hSameCard
                (mul_nonneg (by norm_num) hownErrNonneg)
            _ ≤ (4 * ownErr) * ((T.S.n k : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hcard
                (mul_nonneg (by norm_num) hownErrNonneg)
            _ = 40 * Real.rpow (PT.tiling.P i).q κ.Cb *
                ((T.S.n k : ℝ) + 1) / (T.S.n k : ℝ) := by dsimp [ownErr]; field_simp <;> ring
            _ ≤ 80 * Real.rpow (PT.tiling.P i).q κ.Cb := by
              have hdimRatio : ((T.S.n k : ℝ) + 1) / (T.S.n k : ℝ) ≤ 2 := by
                apply (div_le_iff₀ hnPos).2
                nlinarith
              have hqcb : 0 ≤ Real.rpow (PT.tiling.P i).q κ.Cb := hqcbNonneg
              calc
                _ = 40 * Real.rpow (PT.tiling.P i).q κ.Cb *
                    (((T.S.n k : ℝ) + 1) / (T.S.n k : ℝ)) := by ring
                _ ≤ 40 * Real.rpow (PT.tiling.P i).q κ.Cb * 2 :=
                  mul_le_mul_of_nonneg_left hdimRatio (by positivity)
                _ = 80 * Real.rpow (PT.tiling.P i).q κ.Cb := by ring
        have hQown : 80 * Real.rpow (PT.tiling.P i).q κ.Cb ≤ PT.tiling.gain i / 50 := by
          have hfirst : 80 * Real.rpow (PT.tiling.P i).q κ.Cb ≤
              2 * (PT.tiling.gain i / (100 * κ.u)) := by
            calc
              _ = 2 * (40 * Real.rpow (PT.tiling.P i).q κ.Cb) := by ring
              _ ≤ 2 * (PT.tiling.gain i / (100 * κ.u)) :=
                mul_le_mul_of_nonneg_left hQ8Bound (by norm_num)
          have hsecond : 2 * (PT.tiling.gain i / (100 * κ.u)) ≤
              PT.tiling.gain i / 50 := by
            have hrecip : 1 / (50 * (κ.u : ℝ)) ≤ 1 / 50 :=
              one_div_le_one_div_of_le (by norm_num) (by nlinarith [hu])
            calc
              _ = PT.tiling.gain i / (50 * (κ.u : ℝ)) := by field_simp <;> ring
              _ ≤ PT.tiling.gain i / 50 := by
                have hmul := mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ PT.tiling.gain i)
                simpa [div_eq_mul_inv] using hmul
          exact le_trans hfirst hsecond
        have hcrossBound : (12 * bstar T k) * (Cross.card : ℝ) ≤
            3 * PT.tiling.gain i / 4000 := by
          have hgammaLe : 12 * bstar T k ≤ 3 / 4 := by nlinarith [hbstar]
          have hcrossEll : (Cross.card : ℝ) ≤ (PT.tiling.P i).ℓ := hCrossCard
          have hEllNonneg : 0 ≤ ((PT.tiling.P i).ℓ : ℝ) := Nat.cast_nonneg _
          calc
            _ ≤ (12 * bstar T k) * (PT.tiling.P i).ℓ :=
              mul_le_mul_of_nonneg_left hcrossEll hcrossErrNonneg
            _ ≤ (3 / 4) * (PT.tiling.gain i / (1000 * κ.u)) := by
              exact mul_le_mul hgammaLe hEllBudget hEllNonneg
                (by norm_num : (0 : ℝ) ≤ 3 / 4)
            _ ≤ 3 * PT.tiling.gain i / 4000 := by
              have hrecip : 1 / (1000 * (κ.u : ℝ)) ≤ 1 / 1000 :=
                one_div_le_one_div_of_le (by norm_num) (by nlinarith [hu])
              have hmul := mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ PT.tiling.gain i)
              calc
                _ = (3 / 4) * (PT.tiling.gain i * (1 / (1000 * (κ.u : ℝ)))) := by ring
                _ ≤ (3 / 4) * (PT.tiling.gain i * (1 / 1000)) :=
                  mul_le_mul_of_nonneg_left hmul (by norm_num)
                _ = 3 * PT.tiling.gain i / 4000 := by ring
        have hE : (∑ w ∈ D.externalEarly v, eps w) ≤ PT.tiling.gain i := by
          rw [hpartition, hSameSum, hCrossSum]
          calc
            _ ≤ 80 * Real.rpow (PT.tiling.P i).q κ.Cb +
                12 * bstar T k * (Cross.card : ℝ) :=
              add_le_add hSameBound (le_of_eq rfl)
            _ ≤ PT.tiling.gain i / 50 + 3 * PT.tiling.gain i / 4000 :=
              add_le_add hQown hcrossBound
            _ ≤ PT.tiling.gain i := by nlinarith [hgainNonneg]
        have hscaled := Lane_q_s17_pal.row_le_scaled_of_factors D v
          (D.prior s v) (D.label s) x eps 1 500 (PT.tiling.gain i) (PT.tiling.gain i)
          (PT.tiling.P i).h (initialLateCount D v) (by norm_num) (hclean.1 x)
          (by simpa using hσ)
          hFactor0 hFactor hE hcount
        have hAone : 1 ≤ A := by
          dsimp [A]
          have haDenPos : 0 < 1 - κ.a := by linarith [ha]
          apply (le_div_iff₀ haDenPos).2
          nlinarith [ha]
        have hExpOne : 1 ≤ Real.exp (8 * κ.Kbd + 1) :=
          Real.one_le_exp (by positivity)
        have hcoeff : 2 ≤ Katom := by
          calc
            2 = 2 * 1 := by ring
            _ ≤ 2 * A := mul_le_mul_of_nonneg_left hAone (by norm_num)
            _ ≤ 2 * A * Real.exp (8 * κ.Kbd + 1) :=
              by
                simpa using mul_le_mul_of_nonneg_left hExpOne
                  (show 0 ≤ (2 : ℝ) * A from mul_nonneg (by norm_num) hApos.le)
            _ = Katom := by rfl
        have hExp : PT.tiling.gain i - 500 * PT.tiling.gain i ≤
            -200 * PT.tiling.gain i := by nlinarith [hgainNonneg]
        calc
          _ ≤ 2 * (2 : ℝ) ^ T.S.n k / T.S.N k *
              Real.exp (PT.tiling.gain i - 500 * PT.tiling.gain i) *
                Real.rpow 2 (-(initialLateCount D v : ℝ)) := by simpa using hscaled
          _ = (2 * ((2 : ℝ) ^ T.S.n k / T.S.N k) *
                Real.rpow 2 (-(initialLateCount D v : ℝ))) *
              Real.exp (PT.tiling.gain i - 500 * PT.tiling.gain i) := by ring
          _ ≤ _ := by
            have hpowNonneg : 0 ≤ (2 : ℝ) ^ T.S.n k := by positivity
            have hdivNonneg : 0 ≤ (2 : ℝ) ^ T.S.n k / T.S.N k :=
              div_nonneg hpowNonneg hN.le
            have hrpowNonneg : 0 ≤ Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              Real.rpow_nonneg (by norm_num) _
            have hFactorNonneg : 0 ≤
                2 * ((2 : ℝ) ^ T.S.n k / T.S.N k) *
                  Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              mul_nonneg (mul_nonneg (by norm_num) hdivNonneg) hrpowNonneg
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hFactorNonneg
          _ = 2 * ((2 : ℝ) ^ T.S.n k / T.S.N k *
                Real.exp (-200 * PT.tiling.gain i) *
                  Real.rpow 2 (-(initialLateCount D v : ℝ))) := by ring
          _ ≤ Katom * ((2 : ℝ) ^ T.S.n k / T.S.N k *
                Real.exp (-200 * PT.tiling.gain i) *
                  Real.rpow 2 (-(initialLateCount D v : ℝ))) := by
            have hdivNonneg : 0 ≤ (2 : ℝ) ^ T.S.n k / T.S.N k :=
              div_nonneg (by positivity) hN.le
            have hrpowNonneg : 0 ≤ Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              Real.rpow_nonneg (by norm_num) _
            have hcommon : 0 ≤ (2 : ℝ) ^ T.S.n k / T.S.N k *
                Real.exp (-200 * PT.tiling.gain i) *
                  Real.rpow 2 (-(initialLateCount D v : ℝ)) :=
              mul_nonneg (mul_nonneg hdivNonneg (Real.exp_pos _).le) hrpowNonneg
            exact mul_le_mul_of_nonneg_right hcoeff hcommon
          _ = _ := by ring
  | highDirect => simp [Mode.isLow, hm] at hLow
  | highSmall => simp [Mode.isLow, hm] at hLow
  | highLarge => simp [Mode.isLow, hm] at hLow

set_option maxHeartbeats 1000000 in
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
  filter_upwards [] with k
  intro PT D hQuant i hle hfree
  have hPT : PT.Valid := D.tiling_valid
  have hTV : Tiling.Valid PT.tiling := hPT.tiling_valid
  have hLow := D.mode_low
  have hzeroSpec (hh : (PT.tiling.P i).h = 0) (hgain : 0 ≤ PT.tiling.gain i) :
      ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ := by
    let ψ : S17PaletteCode i hle := ⟨0, 0⟩
    have hmap : Function.Surjective ψ.map := by
      intro c
      refine ⟨0, ?_⟩
      ext j
      exact Fin.elim0 j
    have hspec : PaletteCodeSpec i hle ψ := by
      refine ⟨hmap, ?_⟩
      refine ⟨?_, ?_⟩
      · intro z hzmap hz hweight
        have hz0 : z = 0 := by
          funext j
          exact Fin.elim0 (Fin.cast hh j)
        exact (hz hz0).elim
      · refine ⟨Lane_q_s17_pal.evenLeafPaletteCardEq i hle hPT hfree ψ hmap, ?_⟩
        change (s17Chi ψ : ℝ) ≤ Real.exp (PT.tiling.gain i)
        have hchi : s17Chi ψ = 1 := by simp [s17Chi, ψ, ListGateContext.PaletteCode.chi]
        rw [hchi]
        simpa using Real.one_le_exp hgain
    exact ⟨ψ, hspec⟩
  cases hm : PT.tiling.mode with
  | bounded =>
      rcases hTV.bounded_data hm with ⟨_, hpatch⟩
      rcases hpatch i with ⟨_, hh, _, _⟩
      exact hzeroSpec hh (by simp [Tiling.gain, hm])
  | lowDirect =>
      have hd := hTV.direct_data (Or.inl hm) i
      have hh : (PT.tiling.P i).h = 0 := hd.2.2.2.2.1
      have hgq := hd.2.1
      have hM1 : 4 ≤ κ.M1 := hκ.M1_big.1
      have hq : 0 ≤ ((PT.tiling.P i).q : ℝ) := by positivity
      have hM1q : 0 ≤ κ.M1 * (PT.tiling.P i).q := mul_nonneg (by linarith) hq
      have hg : 0 < ((PT.tiling.P i).g : ℝ) := lt_of_le_of_lt hM1q hgq
      have hgain : 0 ≤ PT.tiling.gain i := by
        simp [Tiling.gain, hm]
        positivity
      exact hzeroSpec hh hgain
  | lowCluster =>
      have hcl := hTV.cluster_data (Or.inl hm) i
      rcases hcl with ⟨hscale, hg, hmass, hdsmall, hdh, hcodeg,
        hdyadic, hpowLow, hpowHigh, hmodeLow, hmodeSmall, hmodeLarge⟩
      have hM1pos : 0 < κ.M1 := by linarith [hκ.M1_big.1]
      have hqNonneg : 0 ≤ ((PT.tiling.P i).q : ℝ) := by positivity
      have hqM1 : (PT.tiling.P i).q ≤ κ.M1 * (PT.tiling.P i).q := by
        nlinarith [hκ.M1_big.1, hqNonneg]
      have hmax : ((max (PT.tiling.P i).g (PT.tiling.P i).q : ℕ) : ℝ) ≤
          κ.M1 * (PT.tiling.P i).q := by
        simpa [Nat.cast_max] using max_le hg hqM1
      have hq0 : κ.Q0 ≤ (PT.tiling.P i).q := by
        by_contra hn
        have hlt : (PT.tiling.P i).q < κ.Q0 := lt_of_not_ge hn
        have hmul : κ.M1 * (PT.tiling.P i).q < κ.M1 * κ.Q0 :=
          mul_lt_mul_of_pos_left hlt hM1pos
        linarith [hscale, hmax]
      have hQ := hκ.Q0_large (PT.tiling.P i).q hq0
      have hqpowNonneg : 0 ≤ Real.rpow (PT.tiling.P i).q κ.aC :=
        Real.rpow_nonneg (by positivity) _
      have hqtail : 10 ≤ κ.a / 10 ^ 6 *
          Real.rpow (PT.tiling.P i).q κ.Mlo / (1000 * κ.u) := by
        have hq := hQ.2.1
        linarith [hqpowNonneg]
      have huNat : 0 < κ.u := by have hu := hκ.u_rng.2; omega
      have hu : 0 < (κ.u : ℝ) := by exact_mod_cast huNat
      have hprod : (10 ^ 10 : ℝ) * κ.u ≤ κ.a *
          Real.rpow (PT.tiling.P i).q κ.Mlo := by
        have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1000) hu)).mp hqtail
        nlinarith [hmul]
      have hhLower : Real.rpow (PT.tiling.P i).q κ.Mlo ≤
          (PT.tiling.P i).h := by simpa [hm] using hpowLow
      have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have hprodH : (10 ^ 10 : ℝ) * κ.u ≤ κ.a * (PT.tiling.P i).h :=
        le_trans hprod (mul_le_mul_of_nonneg_left hhLower haPos.le)
      have huOneNat : 1 ≤ κ.u := by omega
      have huOne : 1 ≤ (κ.u : ℝ) := by exact_mod_cast huOneNat
      have hgainEq : PT.tiling.gain i =
          κ.a * (PT.tiling.P i).h / 10 ^ 6 := by simp [Tiling.gain, hm]
      have hprodBig : (10 ^ 10 : ℝ) ≤ κ.a * (PT.tiling.P i).h := by
        have h := mul_le_mul_of_nonneg_left huOne (by norm_num : (0 : ℝ) ≤ 10 ^ 10)
        have h' : (10 ^ 10 : ℝ) ≤ 10 ^ 10 * κ.u := by simpa using h
        exact le_trans h' hprodH
      have hgainLower : 10000 ≤ PT.tiling.gain i := by
        rw [hgainEq]
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
        calc
          (10000 : ℝ) * 10 ^ 6 = 10 ^ 10 := by norm_num
          _ ≤ κ.a * (PT.tiling.P i).h := hprodBig
      have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have haLt : κ.a < 1 := by
        have huNeg : -(10 * (κ.u : ℝ) + 100) < 0 := by
          have huNonneg : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
          linarith
        have hrpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) huNeg
        have hxiLt : κ.ξ < 1 := by
          have hxi := hκ.ξ_rng.2
          have halpha := hκ.α_rng.2
          have hprodXi : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α :=
            by simpa using mul_lt_mul_of_pos_left hrpow hκ.α_rng.1
          linarith
        have hfour : 1 ≤ (4 : ℝ) ^ (κ.u + 3) :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
        have hden : 1 < 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith [hfour]
        have hquot : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) < 1 := by
          have hxiPos : 0 ≤ κ.ξ := hκ.ξ_rng.1.le
          have hxiSq : κ.ξ ^ 2 < 1 := by nlinarith [hxiLt, hxiPos]
          apply (div_lt_iff₀ (by positivity)).2
          nlinarith [hxiSq, hden]
        have hθ : κ.θ < 1 := lt_trans hκ.θ_rng.2 hquot
        rw [hκ.a_eq]
        linarith
      have hlogHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        norm_num1 at this
        linarith
      let rhoCode : ℝ := 1000 * κ.ρ
      let m : ℕ := ⌈(PT.tiling.gain i) / (2 * Real.log 2)⌉₊
      let w : ℕ := ⌊500 * κ.ρ * (PT.tiling.P i).h⌋₊
      have hargNonneg : 0 ≤ PT.tiling.gain i / (2 * Real.log 2) := by positivity
      have hmle : m ≤ (PT.tiling.P i).h := by
        apply Nat.ceil_le.2
        rw [hgainEq]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 2)).2
        nlinarith [haLt, hlogHalf]
      have hceilLow : PT.tiling.gain i / (2 * Real.log 2) ≤ (m : ℝ) := by
        exact Nat.le_ceil _
      have hceilHigh : (m : ℝ) ≤ PT.tiling.gain i / (2 * Real.log 2) + 1 := by
        dsimp [m]
        calc
          _ ≤ (⌊PT.tiling.gain i / (2 * Real.log 2)⌋₊ : ℝ) + 1 := by
            exact_mod_cast Nat.ceil_le_floor_add_one _
          _ ≤ PT.tiling.gain i / (2 * Real.log 2) + 1 := by
            simpa [add_comm] using add_le_add_right (Nat.floor_le hargNonneg) 1
      have hmulLow : PT.tiling.gain i / 2 ≤ (m : ℝ) * Real.log 2 := by
        have h := mul_le_mul_of_nonneg_right hceilLow hlogpos.le
        have hd : PT.tiling.gain i / (2 * Real.log 2) * Real.log 2 =
            PT.tiling.gain i / 2 := by field_simp [ne_of_gt hlogpos]
        rw [hd] at h
        nlinarith
      have hmulHigh : (m : ℝ) * Real.log 2 ≤ PT.tiling.gain i := by
        have hUpper : (m : ℝ) * Real.log 2 ≤ PT.tiling.gain i / 2 + Real.log 2 := by
          calc
            _ ≤ (PT.tiling.gain i / (2 * Real.log 2) + 1) * Real.log 2 :=
              mul_le_mul_of_nonneg_right hceilHigh hlogpos.le
            _ = PT.tiling.gain i / 2 + Real.log 2 := by field_simp [ne_of_gt hlogpos]
        have hlogLt : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        have hLhalf : Real.log 2 ≤ PT.tiling.gain i / 2 := by linarith [hgainLower, hlogLt]
        exact le_trans hUpper (by linarith only [hLhalf])
      have hrho0 : 0 ≤ rhoCode := by
        dsimp [rhoCode]
        exact mul_nonneg (by norm_num) hκ.ρ_rng.1.le
      have hrhoHalf : rhoCode ≤ 1 / 2 := by
        have hrho : κ.ρ < 1 / 4000 := hκ.ρ_rng.2.1
        change 1000 * κ.ρ ≤ 1 / 2
        have hquarter : 1000 * κ.ρ < 1 / 4 := by
          calc
            1000 * κ.ρ < 1000 * (1 / 4000) :=
              mul_lt_mul_of_pos_left hrho (by norm_num)
            _ = 1 / 4 := by norm_num
        exact hquarter.le.trans (by norm_num)
      have hrhoQuarter : rhoCode < 1 / 4 := by
        dsimp [rhoCode]
        have hrho : κ.ρ < 1 / 4000 := hκ.ρ_rng.2.1
        calc
          1000 * κ.ρ < 1000 * (1 / 4000) :=
            mul_lt_mul_of_pos_left hrho (by norm_num)
          _ = 1 / 4 := by norm_num
      have hwReal : (w : ℝ) ≤ rhoCode * (PT.tiling.P i).h := by
        have hradiusNonneg : 0 ≤ 500 * κ.ρ * (PT.tiling.P i).h :=
          mul_nonneg (mul_nonneg (by norm_num) hκ.ρ_rng.1.le) (Nat.cast_nonneg _)
        have hfloor := Nat.floor_le hradiusNonneg
        have hcoef : 500 * κ.ρ ≤ rhoCode := by
          change 500 * κ.ρ ≤ 1000 * κ.ρ
          exact mul_le_mul_of_nonneg_right (by norm_num : (500 : ℝ) ≤ 1000)
            hκ.ρ_rng.1.le
        have hscale : 500 * κ.ρ * (PT.tiling.P i).h ≤ rhoCode * (PT.tiling.P i).h :=
          mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (PT.tiling.P i).h)
        calc
          (w : ℝ) ≤ 500 * κ.ρ * (PT.tiling.P i).h := hfloor
          _ ≤ rhoCode * (PT.tiling.P i).h := hscale
      have hw : w ≤ (PT.tiling.P i).h := by
        have hrhoOne : rhoCode ≤ 1 := hrhoQuarter.le.trans (by norm_num)
        have hmul : rhoCode * (PT.tiling.P i).h ≤ (PT.tiling.P i).h := by
          simpa using mul_le_mul_of_nonneg_right hrhoOne
            (Nat.cast_nonneg (PT.tiling.P i).h)
        have hw' : (w : ℝ) ≤ (PT.tiling.P i).h :=
          le_trans hwReal hmul
        exact_mod_cast hw'
      have hentropy : Real.binEntropy rhoCode < κ.a / 10 ^ 9 := by
        have hrhoPos : 0 < rhoCode := by
          dsimp [rhoCode]
          exact mul_pos (by norm_num) hκ.ρ_rng.1
        have hrhoNe : rhoCode ≠ 1 := ne_of_lt (lt_trans hrhoQuarter (by norm_num))
        have hcustom : binEntropy rhoCode < κ.a / 10 ^ 9 := by
          change binEntropy (1000 * κ.ρ) < κ.a / 10 ^ 9
          exact hκ.ρ_rng.2.2
        have heq := Lane_q_s17_pal.realBinEntropy_eq_custom rhoCode hrhoPos.ne' hrhoNe
        rw [heq]
        exact hcustom
      have hball := Lane_q_s17_pal.weightBall_entropyBound
        (PT.tiling.P i).h w rhoCode hrho0 hrhoHalf hwReal
      have hballCast :
          (∑ j ∈ Finset.range (w + 1), (Nat.choose (PT.tiling.P i).h j : ℝ)) <
            (2 : ℝ) ^ m := by
        have hcardReal :
            ((LinearCodePToolsCubeR.weightBall (PT.tiling.P i).h w).card : ℝ) =
              ∑ j ∈ Finset.range (w + 1), (Nat.choose (PT.tiling.P i).h j : ℝ) := by
          exact_mod_cast LinearCodePToolsCubeR.card_weightBall _ _
        have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
          calc
            (2 : ℝ) ^ m = (Real.exp (Real.log 2)) ^ m := by rw [Real.exp_log (by norm_num)]
            _ = Real.exp ((m : ℝ) * Real.log 2) := by rw [Real.exp_nat_mul]
        have hhalf : Real.binEntropy rhoCode * (PT.tiling.P i).h < PT.tiling.gain i / 1000 := by
          have hheightPos : 0 < (PT.tiling.P i).h := by
            by_contra hn
            have hle : (PT.tiling.P i).h ≤ 0 := le_of_not_gt hn
            have hzero : (PT.tiling.P i).h = 0 :=
              le_antisymm hle (Nat.cast_nonneg (PT.tiling.P i).h)
            have hcontra : (10 ^ 10 : ℝ) * κ.u ≤ 0 := by simpa [hzero] using hprodH
            have hpos : 0 < (10 ^ 10 : ℝ) * κ.u := by positivity
            linarith
          have hheightPosReal : 0 < ((PT.tiling.P i).h : ℝ) := by exact_mod_cast hheightPos
          have hEntMul := mul_lt_mul_of_pos_right hentropy hheightPosReal
          rw [hgainEq]
          have hscale : (κ.a / 10 ^ 9) * (PT.tiling.P i).h =
              (κ.a * (PT.tiling.P i).h / 10 ^ 6) / 1000 := by ring
          rw [← hscale]
          exact hEntMul
        have hpowArg : Real.binEntropy rhoCode * (PT.tiling.P i).h <
            (m : ℝ) * Real.log 2 := by
          have hhalfle : PT.tiling.gain i / 1000 ≤ PT.tiling.gain i / 2 := by
            nlinarith [hgainLower]
          exact lt_of_lt_of_le hhalf (le_trans hhalfle hmulLow)
        have hballLt :
            ((LinearCodePToolsCubeR.weightBall (PT.tiling.P i).h w).card : ℝ) <
              Real.exp ((m : ℝ) * Real.log 2) := by
          apply lt_of_le_of_lt hball
          exact Real.exp_strictMono hpowArg
        have hballPow :
            ((LinearCodePToolsCubeR.weightBall (PT.tiling.P i).h w).card : ℝ) < (2 : ℝ) ^ m := by
          rw [hpow]
          exact hballLt
        calc
          (∑ j ∈ Finset.range (w + 1), (Nat.choose (PT.tiling.P i).h j : ℝ)) =
              (LinearCodePToolsCubeR.weightBall (PT.tiling.P i).h w).card := hcardReal.symm
          _ < (2 : ℝ) ^ m := hballPow
      have hvol : (∑ j ∈ Finset.range (w + 1), Nat.choose (PT.tiling.P i).h j) <
          2 ^ m := by exact_mod_cast hballCast
      obtain ⟨L, hsurj, hker⟩ := xVarshamov (PT.tiling.P i).h m w hmle hw hvol
      let ψ : S17PaletteCode i hle := ⟨m, L⟩
      have hcolors : ∀ c₁ c₂ : Fin ψ.dimension → ZMod 2,
          (Finset.univ.filter fun v : Pos T k =>
            v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₁).card =
          (Finset.univ.filter fun v : Pos T k =>
            v ∈ PT.tiling.leaf i ∧ IsEvenRole v ∧ ψ.roleColour v = c₂).card :=
        Lane_q_s17_pal.evenLeafPaletteCardEq i hle hPT hfree ψ hsurj
      have hchi : (s17Chi ψ : ℝ) ≤ Real.exp (PT.tiling.gain i) := by
        have hchiEq : (s17Chi ψ : ℝ) = (2 : ℝ) ^ m := by
          simp [s17Chi, ψ, ListGateContext.PaletteCode.chi]
        rw [hchiEq]
        have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
          calc
            (2 : ℝ) ^ m = (Real.exp (Real.log 2)) ^ m := by rw [Real.exp_log (by norm_num)]
            _ = Real.exp ((m : ℝ) * Real.log 2) := by rw [Real.exp_nat_mul]
        rw [hpow]
        exact Real.exp_le_exp.mpr hmulHigh
      refine ⟨ψ, ?_⟩
      refine ⟨hsurj, ?_⟩
      refine ⟨?_, ?_⟩
      · intro z hzmap hzne hweight
        have hwtNat : internalWeight z ≤ w := by
          simpa [w] using Nat.le_floor hweight
        have hbinary : binaryWeight z = internalWeight z := by rfl
        have hker' := hker z hzmap hzne
        rw [hbinary] at hker'
        exact (Nat.not_lt_of_ge hwtNat) hker'
      · exact ⟨hcolors, hchi⟩
  | highDirect => simp [Mode.isLow, hm] at hLow
  | highSmall => simp [Mode.isLow, hm] at hLow
  | highLarge => simp [Mode.isLow, hm] at hLow

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
  classical
  let Kmoment : ℝ := 8 * K + 20
  have hKmoment : 0 < Kmoment := by dsimp [Kmoment]; positivity
  refine ⟨Kmoment, hKmoment, ?_⟩
  have hnTop : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hn2 : ∀ᶠ k in atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 2
  have hlog : ∀ᶠ k in atTop, 1 ≤ Real.log (T.S.n k : ℝ) := by
    exact (Real.tendsto_log_atTop.comp hnTop).eventually_ge_atTop 1
  have hpowTop : Tendsto
      (fun k : ℕ => (T.S.n k : ℝ) ^ (0.19 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).comp hnTop
  have hpoly : Tendsto
      (fun k : ℕ => (T.S.n k : ℝ) ^ (8 * K) *
        Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ)))) atTop (nhds 0) := by
    have hNested :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (8 * K / (0.19 : ℝ)) 1 one_pos).comp hpowTop
    have hNested' : Tendsto
        (fun k : ℕ => ((T.S.n k : ℝ) ^ (0.19 : ℝ)) ^
          (8 * K / (0.19 : ℝ)) *
            Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ)))) atTop (nhds 0) := by
      simpa only [Function.comp_def, one_mul, neg_one_mul] using hNested
    have hEq :
        (fun k : ℕ => ((T.S.n k : ℝ) ^ (0.19 : ℝ)) ^
          (8 * K / (0.19 : ℝ)) *
            Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ)))) =
        (fun k : ℕ => (T.S.n k : ℝ) ^ (8 * K) *
          Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ)))) := by
      funext k
      rw [← Real.rpow_mul (show 0 ≤ (T.S.n k : ℝ) by positivity)]
      congr 1
      field_simp
      <;> ring
    rw [← hEq]
    exact hNested'
  have hpolySmall : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (8 * K) *
        Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ))) ≤ 1 := by
    have hlt : ∀ᶠ k in atTop,
        (T.S.n k : ℝ) ^ (8 * K) *
          Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ))) < 1 :=
      hpoly.eventually (Iio_mem_nhds (by norm_num))
    exact hlt.mono fun _ h => h.le
  filter_upwards [hn2, hlog, hpolySmall] with k hn hlogn hpolyN
  intro PT D hQuant i hX
  unfold PalettePairMomentBound
  intro d hd
  let X := (PT.tiling.P i).X
  let Env := PT.envelope i
  let n : ℝ := T.S.n k
  let M : ℝ := (X.card : ℝ)
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast (by omega : 0 < T.S.n k)
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hlogpos : 0 ≤ Real.log n := by linarith
  have hMpos : 0 < M := by
    dsimp [M, X]
    exact_mod_cast Finset.card_pos.mpr hX
  have hPT : PT.Valid := D.tiling_valid
  have hEnvX : Env ⊆ X := by
    dsimp [Env, X]
    exact hPT.envelope_subset i
  have hdegree (x : Fin (T.S.N k)) (hx : x ∈ Env) :
      n * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
        K * Real.log n := by
    simpa [n] using hQuant.geometry.degree_drift i x hx
  have hrowTail (x : Fin (T.S.N k)) (hx : x ∈ Env) :
      (∑ z ∈ X.filter (fun z =>
        Real.rpow n (-1.02) <
          |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ∧
        |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ 2 * κ.ξ),
        Real.exp (100 * n *
          |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|)) ≤
        Real.exp (-Real.rpow n 0.19) * M := by
    simpa [n, X] using (hPT.envelope_row_tail i i x hx).2
  let joint (x z : Fin (T.S.N k)) : ℝ :=
    4 * ∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y *
      hit (T.S.E k) PT.tiling.c z y
  have hjoint_nonneg (x z : Fin (T.S.N k)) : 0 ≤ joint x z := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro y hy
    have hhitx : 0 ≤ hit (T.S.E k) PT.tiling.c x y := by
      unfold hit
      split_ifs <;> norm_num
    have hhitZ : 0 ≤ hit (T.S.E k) PT.tiling.c z y := by
      unfold hit
      split_ifs <;> norm_num
    exact mul_nonneg
      (mul_nonneg ((PT.π i).nonneg y) hhitx) hhitZ
  have hidentity (x z : Fin (T.S.N k)) :
      joint x z = 2 * deg (T.S.E k) PT.tiling.c (PT.π i).w x +
        2 * deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 +
        corr (T.S.E k) PT.tiling.c (PT.π i).w x z := by
    have hmass : (∑ y, (PT.π i).w y) = 1 := (PT.π i).sum_eq_one
    have hpoint (y : Fin (T.S.N k)) :
        4 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y *
            hit (T.S.E k) PT.tiling.c z y =
          2 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y +
            2 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c z y -
            (PT.π i).w y +
            (PT.π i).w y * fv (T.S.E k) PT.tiling.c x y *
              fv (T.S.E k) PT.tiling.c z y := by
      simp only [fv]
      ring
    dsimp [joint]
    calc
      4 * ∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y *
          hit (T.S.E k) PT.tiling.c z y =
        ∑ y, 4 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y *
          hit (T.S.E k) PT.tiling.c z y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = ∑ y, (2 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y +
          2 * (PT.π i).w y * hit (T.S.E k) PT.tiling.c z y -
          (PT.π i).w y +
          (PT.π i).w y * fv (T.S.E k) PT.tiling.c x y *
            fv (T.S.E k) PT.tiling.c z y) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint y
      _ = 2 * deg (T.S.E k) PT.tiling.c (PT.π i).w x +
          2 * deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 +
          corr (T.S.E k) PT.tiling.c (PT.π i).w x z := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp [deg, corr, hmass, Finset.mul_sum]
        <;> ring
  let high (x z : Fin (T.S.N k)) : Prop :=
    Real.rpow n (-1.02) <
      |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ∧
    |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ 2 * κ.ξ
  let value (x z : Fin (T.S.N k)) : ℝ :=
    if x ∈ Env ∧ z ∈ Env ∧
        |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
      joint x z ^ (2 * d) else 0
  let small : ℝ := Real.exp (8 * K * Real.log n + 2)
  let pref : ℝ := Real.exp (8 * K * Real.log n)
  have hpref : pref = n ^ (8 * K) := by
    dsimp [pref]
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have htailFactor : pref * Real.exp (-Real.rpow n 0.19) ≤ 1 := by
    rw [hpref]
    simpa [n] using hpolyN
  have hvalueBound (x z : Fin (T.S.N k)) :
      value x z ≤ small + if high x z then
        Real.exp (8 * K * Real.log n + 100 * n *
          |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0 := by
    by_cases hgood : x ∈ Env ∧ z ∈ Env ∧
        |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ
    · rcases hgood with ⟨hx, hz, hcorr⟩
      have hdx := hdegree x hx
      have hdz := hdegree z hz
      have hdx' : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
          K * Real.log n / n := by
        apply (le_div_iff₀ hnpos).2
        nlinarith [hdx]
      have hdz' : |deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 / 2| ≤
          K * Real.log n / n := by
        apply (le_div_iff₀ hnpos).2
        nlinarith [hdz]
      let corrAbs := |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|
      let t := 2 * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| +
        2 * |deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 / 2| + corrAbs
      have ht0 : 0 ≤ t := by dsimp [t, corrAbs]; positivity
      have hqle : joint x z ≤ 1 + t := by
        rw [hidentity]
        dsimp [t, corrAbs]
        have hxabs := le_abs_self
          (deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2)
        have hzabs := le_abs_self
          (deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 / 2)
        have hcabs := le_abs_self (corr (T.S.E k) PT.tiling.c (PT.π i).w x z)
        nlinarith
      have hqexp : joint x z ≤ Real.exp t :=
        hqle.trans (by simpa [add_comm] using Real.add_one_le_exp t)
      have htbound : t ≤ 4 * K * Real.log n / n + corrAbs := by
        dsimp [t]
        calc
          2 * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| +
              2 * |deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 / 2| + corrAbs ≤
            2 * (K * Real.log n / n) + 2 * (K * Real.log n / n) + corrAbs := by
              gcongr
          _ = 4 * K * Real.log n / n + corrAbs := by ring
      have htPow : (2 * d : ℝ) * t ≤
          8 * K * Real.log n + 2 * n * corrAbs := by
        have hdReal : (2 * d : ℝ) ≤ 2 * n := by
          dsimp [n]
          exact_mod_cast Nat.mul_le_mul_left 2 hd
        calc
          (2 * d : ℝ) * t ≤ 2 * n * t :=
            mul_le_mul_of_nonneg_right hdReal ht0
          _ ≤ 2 * n * (4 * K * Real.log n / n + corrAbs) := by
            gcongr
          _ = 8 * K * Real.log n + 2 * n * corrAbs := by
            field_simp [ne_of_gt hnpos]
            <;> ring
      have hqpow : joint x z ^ (2 * d) ≤
          Real.exp (8 * K * Real.log n + 2 * n * corrAbs) := by
        calc
          joint x z ^ (2 * d) ≤ Real.exp t ^ (2 * d) :=
            pow_le_pow_left₀ (hjoint_nonneg x z) hqexp _
          _ = Real.exp ((2 * d : ℝ) * t) := by
            rw [← Real.exp_nat_mul]
            congr 1
            norm_num
          _ ≤ Real.exp (8 * K * Real.log n + 2 * n * corrAbs) :=
            Real.exp_le_exp.mpr htPow
      by_cases hsmall : corrAbs ≤ Real.rpow n (-1.02)
      · have hexpCompare : Real.rpow n (-1.02) ≤ Real.rpow n (-1) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        have hInv : n * Real.rpow n (-1) = 1 := by
          change n * n ^ (-1 : ℝ) = 1
          rw [Real.rpow_neg_one]
          exact mul_inv_cancel₀ hnpos.ne'
        have hna : n * corrAbs ≤ 1 := by
          calc
            n * corrAbs ≤ n * Real.rpow n (-1.02) :=
              mul_le_mul_of_nonneg_left hsmall hnpos.le
            _ ≤ n * Real.rpow n (-1) :=
              mul_le_mul_of_nonneg_left hexpCompare hnpos.le
            _ = 1 := hInv
        have hvalue : value x z = joint x z ^ (2 * d) := by
          simp [value, hx, hz, hcorr]
        have hhighFalse : ¬ high x z := by
          intro hh
          exact (not_lt_of_ge hsmall) hh.1
        calc
          value x z = joint x z ^ (2 * d) := hvalue
          _ ≤ Real.exp (8 * K * Real.log n + 2 * n * corrAbs) := hqpow
          _ ≤ small := by
            have he : Real.exp (8 * K * Real.log n + 2 * n * corrAbs) ≤
                Real.exp (8 * K * Real.log n + 2) :=
              Real.exp_le_exp.mpr (by nlinarith [hna])
            simpa [small] using he
          _ = small + if high x z then
              Real.exp (8 * K * Real.log n + 100 * n * corrAbs) else 0 := by
            simp [hhighFalse]
      · have hhigh : high x z := by
          refine ⟨lt_of_not_ge hsmall, ?_⟩
          exact le_trans hcorr (by linarith [hκ.ξ_rng.1])
        have hvalue : value x z = joint x z ^ (2 * d) := by
          simp [value, hx, hz, hcorr]
        have habsnonneg : 0 ≤ corrAbs := by positivity
        have hlarge : joint x z ^ (2 * d) ≤
            Real.exp (8 * K * Real.log n + 100 * n * corrAbs) := by
          exact hqpow.trans (Real.exp_le_exp.mpr (by nlinarith))
        calc
          value x z = joint x z ^ (2 * d) := hvalue
          _ ≤ Real.exp (8 * K * Real.log n + 100 * n * corrAbs) := hlarge
          _ ≤ small + Real.exp (8 * K * Real.log n + 100 * n * corrAbs) := by
            dsimp [small]
            nlinarith [Real.exp_nonneg (8 * K * Real.log n + 2)]
          _ = small + if high x z then
              Real.exp (8 * K * Real.log n + 100 * n *
                |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0 := by
            simp [hhigh, corrAbs]
    · simp [value, hgood]
      positivity
  have hbigSum (x : Fin (T.S.N k)) :
      (∑ z ∈ X, if high x z then
          Real.exp (8 * K * Real.log n + 100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) =
        pref * (∑ z ∈ X.filter (high x),
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|)) := by
    calc
      _ = ∑ z ∈ X, if high x z then pref *
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hh : high x z <;> simp [hh, pref, Real.exp_add]
      _ = ∑ z ∈ X, pref * (if high x z then
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hh : high x z <;> simp [hh]
      _ = pref * ∑ z ∈ X, if high x z then
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0 := by
        rw [← Finset.mul_sum]
      _ = pref * (∑ z ∈ X.filter (high x),
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|)) := by
        rw [← Finset.sum_filter]
  have hinner (x : Fin (T.S.N k)) :
      (∑ z ∈ X, value x z) ≤ M * (small + 1) := by
    by_cases hx : x ∈ Env
    · have hrow := hrowTail x hx
      have hrow' : (∑ z ∈ X.filter (high x),
          Real.exp (100 * n *
            |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|)) ≤
          Real.exp (-Real.rpow n 0.19) * M := by
        simpa [high, n, X] using hrow
      have hsum : (∑ z ∈ X, value x z) ≤
          ∑ z ∈ X, (small + if high x z then
            Real.exp (8 * K * Real.log n + 100 * n *
              |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        exact hvalueBound x z
      calc
        _ ≤ ∑ z ∈ X, (small + if high x z then
            Real.exp (8 * K * Real.log n + 100 * n *
              |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) := hsum
        _ = M * small +
            ∑ z ∈ X, if high x z then
              Real.exp (8 * K * Real.log n + 100 * n *
                |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0 := by
          simp [M, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ = M * small + pref *
            (∑ z ∈ X.filter (high x),
              Real.exp (100 * n *
                |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|)) := by
          rw [hbigSum]
        _ ≤ M * small + pref * (Real.exp (-Real.rpow n 0.19) * M) := by
          apply add_le_add
          · exact le_rfl
          · exact mul_le_mul_of_nonneg_left hrow' (by dsimp [pref]; positivity)
        _ = M * (small + pref * Real.exp (-Real.rpow n 0.19)) := by ring
        _ ≤ M * (small + 1) := by
          gcongr <;> exact htailFactor
    · have hzero : (∑ z ∈ X, value x z) = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        simp [value, hx]
      rw [hzero]
      positivity
  have hdouble :
      (∑ x ∈ X, ∑ z ∈ X, value x z) ≤ M ^ 2 * (small + 1) := by
    calc
      _ ≤ ∑ x ∈ X, M * (small + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hinner x
      _ = M ^ 2 * (small + 1) := by
        simp [M, Finset.sum_const, nsmul_eq_mul]
        ring
  have hmomentNumerator :
      (∑ x ∈ X, ∑ z ∈ X, value x z) / M ^ 2 ≤ small + 1 := by
    apply (div_le_iff₀ (by positivity : 0 < M ^ 2)).2
    nlinarith [hdouble]
  have hsmallFinal : small + 1 ≤ Real.exp (Kmoment * Real.log n) := by
    dsimp [small, Kmoment]
    have hloglarge : 2 ≤ 10 * Real.log n := by nlinarith [hlogn]
    have hAddExp (t : ℝ) : 1 + t ≤ Real.exp t := by
      linarith [Real.add_one_le_exp t]
    have hsmallLe : Real.exp (8 * K * Real.log n + 2) ≤
        Real.exp (8 * K * Real.log n + 10 * Real.log n) :=
      Real.exp_le_exp.mpr (by linarith [hloglarge])
    have hunitLe : 1 ≤ Real.exp (8 * K * Real.log n + 10 * Real.log n) := by
      have hKlog : 0 ≤ 8 * K * Real.log n := by positivity
      calc
        1 ≤ 1 + (8 * K * Real.log n + 10 * Real.log n) := by
          nlinarith [hKlog, hlogn]
        _ ≤ Real.exp (8 * K * Real.log n + 10 * Real.log n) :=
          hAddExp (8 * K * Real.log n + 10 * Real.log n)
    have htwo : 2 ≤ Real.exp (10 * Real.log n) := by
      calc
        2 ≤ 1 + 10 * Real.log n := by nlinarith [hlogn]
        _ ≤ Real.exp (10 * Real.log n) := hAddExp (10 * Real.log n)
    calc
      Real.exp (8 * K * Real.log n + 2) + 1 ≤
          Real.exp (8 * K * Real.log n + 10 * Real.log n) +
            Real.exp (8 * K * Real.log n + 10 * Real.log n) :=
        add_le_add hsmallLe hunitLe
      _ = 2 * Real.exp (8 * K * Real.log n + 10 * Real.log n) := by ring
      _ ≤ Real.exp ((8 * K + 20) * Real.log n) := by
        calc
          2 * Real.exp (8 * K * Real.log n + 10 * Real.log n) ≤
              Real.exp (10 * Real.log n) *
                Real.exp (8 * K * Real.log n + 10 * Real.log n) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = Real.exp ((8 * K + 20) * Real.log n) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ = Real.exp (Kmoment * Real.log n) := by rfl
  have hmomentSum :
      (∑ x ∈ X, ∑ z ∈ X, value x z) / (X.card : ℝ) ^ 2 ≤
        Real.exp (Kmoment * Real.log n) := by
    have hden : M ^ 2 = (X.card : ℝ) ^ 2 := by rfl
    rw [← hden]
    exact hmomentNumerator.trans hsmallFinal
  rw [Lane_q_s17_pal.uniform_pair_expect
    (N := T.S.N k) (X := (PT.tiling.P i).X) (hX := hX)
    (g := fun x z => if x ∈ PT.envelope i ∧ z ∈ PT.envelope i ∧
      |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
        (4 * ∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y *
          hit (T.S.E k) PT.tiling.c z y) ^ (2 * d) else 0)]
  simpa [value, joint, n, X, Env] using hmomentSum

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- P17.4d(i): target backward-closure extraction with exact terminal entries. -/
theorem finiteResamplingTargetWitness
    {κ : CConsts} {T : Stage} {k Ts : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (tapes : Tapes D.F Ts) :
    ∃ m, ∃ W : TargetWitness T k Ts m,
      ActualTargetWitness LE order events pools targets tapes W := by
  sorry

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
