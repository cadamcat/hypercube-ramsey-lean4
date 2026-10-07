import HypercubeRamsey.S17.Needs
import HypercubeRamsey.S17.Nodes_q_s17_res2

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
  classical
  intro m
  by_cases hm : m = 0
  · subst m
    haveI : Subsingleton (TargetWitness T k Ts 0) := by
      constructor
      intro W W'
      apply Prod.ext
      · apply Prod.ext
        · funext i
          apply Fin.ext
          omega
        · funext i
          apply Fin.ext
          omega
      · funext i
        exact Fin.elim0 i
    have hcard :
        (Finset.univ.filter fun W : TargetWitness T k Ts 0 =>
          CandidateTargetWitness LE events targets W).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro W hW W' hW'
      exact Subsingleton.elim W W'
    simpa [targetWitnessBase] using hcard
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let depthSeq (Q : PlaneTreeCode (m + 1)) (i : Fin (m + 1)) : ℕ :=
      if hi : i.val < m then
        (Q.1 (targetNode ⟨i.val, hi⟩)).val - 1 else 0
    have hDepthEnd (Q : PlaneTreeCode (m + 1)) : depthSeq Q (Fin.last m) = 0 := by
      simp [depthSeq]
    have hDepthCast (Q : PlaneTreeCode (m + 1)) (j : Fin m) :
        depthSeq Q j.castSucc = (Q.1 (targetNode j)).val - 1 := by
      change (if h : j.val < m then
        (Q.1 (targetNode ⟨j.val, h⟩)).val - 1 else 0) = _
      split_ifs with h
      · rfl
      · exact (h j.isLt).elim
    have hDepthSucc (Q : PlaneTreeCode (m + 1)) (j : Fin m)
        (hj : j.val + 1 < m) :
        depthSeq Q j.succ =
          (Q.1 (targetNode ⟨j.val + 1, hj⟩)).val - 1 := by
      change (if h : j.val + 1 < m then
        (Q.1 (targetNode ⟨j.val + 1, h⟩)).val - 1 else 0) = _
      split_ifs with h
      · rfl
    have hDepthZero (Q : PlaneTreeCode (m + 1)) (hQ : PlaneTreeSpec Q) :
        depthSeq Q 0 = 0 := by
      have hzeroLt : (0 : ℕ) < m := hmpos
      have hroot : (Q.1 (0 : Fin (m + 1))).val = 0 := (hQ.1 0 rfl).1
      let j : Fin m := ⟨0, hzeroLt⟩
      have hjPos : 0 < (targetNode j).val := by simp [targetNode]
      obtain ⟨hp, hdepth, _⟩ := hQ.2 (targetNode j) hjPos
      have hnodeVal : (targetNode j).val = 1 := by simp [targetNode, j]
      have hpval : (Q.2 (targetNode j)).val = 0 := by
        have hlt : (Q.2 (targetNode j)).val < 1 := by
          calc
            (Q.2 (targetNode j)).val < (targetNode j).val := hp
            _ = 1 := hnodeVal
        exact Nat.lt_one_iff.mp hlt
      have hparentEq : Q.2 (targetNode j) = 0 := Fin.ext hpval
      have hparentDepth : (Q.1 (Q.2 (targetNode j))).val = 0 := by
        rw [hparentEq]
        exact hroot
      have hraw : (Q.1 (targetNode j)).val = 1 := by
        rw [hparentDepth] at hdepth
        exact hdepth
      have hindex : (0 : Fin (m + 1)) = j.castSucc := by
        apply Fin.ext
        simp [j]
      rw [hindex]
      rw [hDepthCast Q j, hraw]
    have hDepthStep (Q : PlaneTreeCode (m + 1)) (hQ : PlaneTreeSpec Q)
        (j : Fin m) :
        depthSeq Q j.succ ≤ depthSeq Q j.castSucc + 1 := by
      by_cases hlast : j.val + 1 = m
      · have hnext : ¬ (j.val + 1 < m) := by omega
        have hnextDepth : depthSeq Q j.succ = 0 := by
          change (if h : j.val + 1 < m then
          (Q.1 (targetNode ⟨j.val + 1, h⟩)).val - 1 else 0) = 0
          split_ifs with h
          · omega
        rw [hDepthCast Q j, hnextDepth]
        omega
      · have hnextlt : j.val + 1 < m := by omega
        let cur : Fin (m + 1) := targetNode j
        let nxt : Fin (m + 1) := targetNode ⟨j.val + 1, hnextlt⟩
        have hcurval : cur.val = j.val + 1 := by simp [cur, targetNode]
        have hnxtval : nxt.val = j.val + 2 := by simp [nxt, targetNode]
        have hnxtpos : 0 < nxt.val := by omega
        obtain ⟨hparent, hdepth, hinterval⟩ := hQ.2 nxt hnxtpos
        by_cases hsame : Q.2 nxt = cur
        · have hraw : (Q.1 nxt).val = (Q.1 cur).val + 1 := by
            have hparentDepth : (Q.1 (Q.2 nxt)).val = (Q.1 cur).val :=
              congrArg (fun x => (Q.1 x).val) hsame
            rw [hparentDepth] at hdepth
            exact hdepth
          have hcurDepth : depthSeq Q j.castSucc = (Q.1 cur).val - 1 := by
            simpa [cur] using hDepthCast Q j
          have hnextDepth : depthSeq Q j.succ = (Q.1 nxt).val - 1 := by
            simpa [nxt] using hDepthSucc Q j hnextlt
          rw [hcurDepth, hnextDepth]
          omega
        · have hparentCur : (Q.2 nxt).val < cur.val := by
            have hne : (Q.2 nxt).val ≠ cur.val := by
              intro heq
              exact hsame (Fin.ext heq)
            omega
          have hcurLtNxt : cur.val < nxt.val := by omega
          have hraw : (Q.1 nxt).val ≤ (Q.1 cur).val :=
            hinterval cur hparentCur hcurLtNxt
          have hcurDepth : depthSeq Q j.castSucc = (Q.1 cur).val - 1 := by
            simpa [cur] using hDepthCast Q j
          have hnextDepth : depthSeq Q j.succ = (Q.1 nxt).val - 1 := by
            simpa [nxt] using hDepthSucc Q j hnextlt
          rw [hcurDepth, hnextDepth]
          omega
    let treeBlock (Q : PlaneTreeCode (m + 1)) (j : Fin m) : ℕ :=
      depthSeq Q j.castSucc + 2 - depthSeq Q j.succ
    have hBlockPos (Q : PlaneTreeCode (m + 1)) (hQ : PlaneTreeSpec Q)
        (j : Fin m) : 0 < treeBlock Q j := by
      have hstep := hDepthStep Q hQ j
      dsimp [treeBlock]
      omega
    have hBlockSum (Q : PlaneTreeCode (m + 1)) (hQ : PlaneTreeSpec Q) :
        (∑ j : Fin m, treeBlock Q j) = 2 * m := by
      let d : ℕ → ℕ := fun i =>
        if hi : i < m then depthSeq Q ⟨i, by omega⟩ else 0
      have hbound : ∀ i < m, d (i + 1) ≤ d i + 2 := by
        intro i hi
        let j : Fin m := ⟨i, hi⟩
        by_cases hi' : i + 1 < m
        · have hcur : d i = depthSeq Q j.castSucc := by simpa [d, j, hi]
          have hnext : d (i + 1) = depthSeq Q j.succ := by simpa [d, j, hi']
          rw [hcur, hnext]
          have hstep := hDepthStep Q hQ j
          omega
        · have hieq : i + 1 = m := by omega
          have hnext : d (i + 1) = 0 := by simp [d, hieq]
          rw [hnext]
          omega
      have hsum := Lane_q_s17_res2.sum_range_depth_gaps m d hbound
      have hzero : d 0 = 0 := by
        dsimp [d]
        simp [hmpos, hDepthZero Q hQ]
      have hend : d m = 0 := by simp [d]
      have hsum' : (∑ i ∈ Finset.range m, (d i + 2 - d (i + 1))) = 2 * m := by
        rw [hzero, hend] at hsum
        simpa using hsum
      let treeBlockNat : ℕ → ℕ := fun i =>
        if hi : i < m then treeBlock Q ⟨i, hi⟩ else 0
      have hFinSum : (∑ j : Fin m, treeBlock Q j) =
          ∑ i ∈ Finset.range m, treeBlockNat i := by
        simpa [treeBlockNat] using (Fin.sum_univ_eq_sum_range treeBlockNat m)
      calc
        (∑ j : Fin m, treeBlock Q j) =
            ∑ i ∈ Finset.range m, treeBlockNat i := hFinSum
        _ = ∑ i ∈ Finset.range m, (d i + 2 - d (i + 1)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hiNat : i < m := Finset.mem_range.mp hi
              let j : Fin m := ⟨i, hiNat⟩
              have hcur : d i = depthSeq Q j.castSucc := by simpa [d, j, hiNat]
              have hdnext : d (i + 1) = depthSeq Q j.succ := by
                by_cases hnext : i + 1 < m
                · simpa [d, j, hnext]
                · have hieq : i + 1 = m := by omega
                  have hlastIndex : j.succ = Fin.last m := by
                    apply Fin.ext
                    simp [j, hieq]
                  have hsentinel : depthSeq Q j.succ = 0 := by
                    rw [hlastIndex]
                    exact hDepthEnd Q
                  simpa [d, hieq, hsentinel]
              rw [hcur, hdnext]
              simpa [treeBlockNat, treeBlock, j, hiNat]
        _ = 2 * m := hsum'
    let Shape := {Q : PlaneTreeCode (m + 1) // PlaneTreeSpec Q}
    let shapeEncoding (Q : Shape) : Composition (2 * m) := {
      blocks := List.ofFn (treeBlock Q.1)
      blocks_pos := by
        intro b hb
        rcases (List.mem_ofFn' (treeBlock Q.1) b).mp hb with ⟨j, hj⟩
        rw [← hj]
        exact hBlockPos Q.1 Q.2 j
      blocks_sum := by
        simpa [List.sum_ofFn] using hBlockSum Q.1 Q.2 }
    have hShapeBound : Fintype.card Shape ≤ 4 ^ m := by
      have hCard : Fintype.card Shape ≤ Fintype.card (Composition (2 * m)) :=
        Fintype.card_le_of_injective shapeEncoding (by
          intro Q R h
          apply Subtype.ext
          have hlist : List.ofFn (treeBlock Q.1) = List.ofFn (treeBlock R.1) :=
            congrArg Composition.blocks h
          have hblocks : treeBlock Q.1 = treeBlock R.1 := List.ofFn_inj.mp hlist
          have hdepth : depthSeq Q.1 = depthSeq R.1 :=
            Lane_q_s17_res2.fin_depth_eq_of_step (depthSeq Q.1) (depthSeq R.1)
              ((hDepthEnd Q.1).trans (hDepthEnd R.1).symm)
              (by
                intro j
                constructor
                · have hstep := hDepthStep Q.1 Q.2 j
                  omega
                · have hstep := hDepthStep R.1 R.2 j
                  omega)
              (by intro j; exact congrFun hblocks j)
          have hdepthCode : Q.1.1 = R.1.1 := by
            funext i
            by_cases hi0 : i.val = 0
            · have hq0 := (Q.2.1 i hi0).1
              have hr0 := (R.2.1 i hi0).1
              apply Fin.ext
              omega
            · let j : Fin m := ⟨i.val - 1, by omega⟩
              have hidx : targetNode j = i := by
                apply Fin.ext
                simp [targetNode, j]
                omega
              have hjlt : j.val < m := by omega
              have hrel := congrFun hdepth j.castSucc
              have hposQ : 0 < (Q.1.1 i).val := by
                rcases Q.2.2 i (by omega) with ⟨_, hdep, _⟩
                omega
              have hposR : 0 < (R.1.1 i).val := by
                rcases R.2.2 i (by omega) with ⟨_, hdep, _⟩
                omega
              have hraw : (Q.1.1 i).val - 1 = (R.1.1 i).val - 1 := by
                simpa [depthSeq, hidx, j, hjlt] using hrel
              apply Fin.ext
              omega
          have hparentCode : Q.1.2 = R.1.2 := by
            funext i
            apply Fin.ext
            by_cases hi0 : i.val = 0
            · have hq0 := (Q.2.1 i hi0).2
              have hr0 := (R.2.1 i hi0).2
              omega
            · have hiPos : 0 < i.val := by omega
              rcases Q.2.2 i hiPos with ⟨hpQ, hdQ, hIntQ⟩
              rcases R.2.2 i hiPos with ⟨hpR, hdR, hIntR⟩
              by_cases hlt : (Q.1.2 i).val < (R.1.2 i).val
              · have hInt := hIntQ (R.1.2 i) hlt hpR
                have hdEqChild : (Q.1.1 i).val = (R.1.1 i).val :=
                  congrArg Fin.val (congrFun hdepthCode i)
                have hdEqParent : (Q.1.1 (R.1.2 i)).val =
                    (R.1.1 (R.1.2 i)).val :=
                  congrArg Fin.val (congrFun hdepthCode (R.1.2 i))
                omega
              · by_cases hgt : (R.1.2 i).val < (Q.1.2 i).val
                · have hInt := hIntR (Q.1.2 i) hgt hpQ
                  have hdEqChild : (Q.1.1 i).val = (R.1.1 i).val :=
                    congrArg Fin.val (congrFun hdepthCode i)
                  have hdEqParent : (Q.1.1 (Q.1.2 i)).val =
                      (R.1.1 (Q.1.2 i)).val :=
                    congrArg Fin.val (congrFun hdepthCode (Q.1.2 i))
                  omega
                · omega
          exact Prod.ext hdepthCode hparentCode)
      calc
        Fintype.card Shape ≤ Fintype.card (Composition (2 * m)) := hCard
        _ = 2 ^ (2 * m - 1) := composition_card (2 * m)
        _ ≤ 2 ^ (2 * m) := pow_le_pow_right' (by norm_num : 1 ≤ 2) (Nat.sub_le _ _)
        _ = 4 ^ m := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
    have hIncidentCount (C : D.G.Cell) :
        (LE.incidentEvents C).card ≤ d + 1 := by
      classical
      let s := LE.incidentEvents C
      by_cases hs : s.Nonempty
      · obtain ⟨v, hv⟩ := hs
        have hsub : s.erase v ⊆ Finset.univ.filter (fun w => LE.Adjacent v w) := by
          intro w hw
          have hne : w ≠ v := (Finset.mem_erase.mp hw).1
          have hwC : C ∈ LE.scope w := (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).2
          have hvC : C ∈ LE.scope v := (Finset.mem_filter.mp hv).2
          have hnot : ¬ Disjoint (LE.scope v) (LE.scope w) := by
            intro hdis
            exact (Finset.disjoint_left.mp hdis) hvC hwC
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ⟨hne.symm, hnot⟩⟩
        have hcard := Finset.card_le_card hsub
        have hcardErase := Finset.card_erase_add_one hv
        have hdeg := hdegree v
        calc
          s.card = (s.erase v).card + 1 := hcardErase.symm
          _ ≤ d + 1 := Nat.add_le_add_right (hcard.trans hdeg) 1
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [s, hsEmpty]
    let rootPositions : Finset (Pos T k) :=
      targets.biUnion (fun C => LE.incidentEvents C)
    have hRootCard : rootPositions.card ≤ targets.card * (d + 1) := by
      dsimp [rootPositions]
      exact Finset.card_biUnion_le_card_mul targets (fun C => LE.incidentEvents C) (d + 1)
        (by intro C hC; exact hIncidentCount C)
    let closePositions (v : Pos T k) : Finset (Pos T k) :=
      insert v (Finset.univ.filter fun w => LE.Adjacent v w)
    have hCloseCard (v : Pos T k) : (closePositions v).card ≤ d + 1 := by
      dsimp [closePositions]
      exact (Finset.card_insert_le v _).trans (Nat.add_le_add_right (hdegree v) 1)
    let rootFactor := max 1 (targets.card * (d + 1))
    let roundFactor := max 1 Ts
    let B := rootFactor * (d + 1) * roundFactor
    have hDpos : 1 ≤ d + 1 := by omega
    have hRootBound : rootPositions.card ≤ rootFactor :=
      hRootCard.trans (Nat.le_max_right _ _)
    have hRoundBound : Ts ≤ roundFactor := Nat.le_max_right _ _
    have hFactorMul : rootFactor ≤ rootFactor * (d + 1) := by
      calc
        rootFactor = rootFactor * 1 := by omega
        _ ≤ rootFactor * (d + 1) := Nat.mul_le_mul_left _ hDpos
    have hDegreeMul : d + 1 ≤ rootFactor * (d + 1) := by
      calc
        d + 1 = 1 * (d + 1) := by omega
        _ ≤ rootFactor * (d + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_max_left _ _)
    let parentItem (Q : Shape) (j : Fin m) : Fin m :=
      ⟨(Q.1.2 (targetNode j)).val - 1, by
        have hpos : 0 < (targetNode j).val := by simp [targetNode]
        have hparent := (Q.2.2 (targetNode j) hpos).1
        simp [targetNode] at hparent
        omega⟩
    let allowedPositions (Q : Shape) (W : TargetWitness T k Ts m) (j : Fin m) :
        Finset (Pos T k) :=
      if hroot : (Q.1.2 (targetNode j)).val = 0 then rootPositions
      else closePositions ((W.2 (parentItem Q j)).1)
    let allowedOccurrences (Q : Shape) (W : TargetWitness T k Ts m) (j : Fin m) :
        Finset (ExecutionOccurrence T k Ts) :=
      allowedPositions Q W j ×ˢ Finset.univ
    have hAllowedPosCard (Q : Shape) (W : TargetWitness T k Ts m) (j : Fin m) :
        (allowedPositions Q W j).card ≤ rootFactor * (d + 1) := by
      dsimp [allowedPositions]
      split_ifs with hroot
      · exact hRootBound.trans hFactorMul
      · exact (hCloseCard _).trans hDegreeMul
    have hAllowedCard (Q : Shape) (W : TargetWitness T k Ts m) (j : Fin m) :
        (allowedOccurrences Q W j).card ≤ B := by
      dsimp only [allowedOccurrences]
      rw [Finset.card_product]
      simp only [Finset.card_univ, Fintype.card_fin]
      calc
        (allowedPositions Q W j).card * Ts ≤
            (rootFactor * (d + 1)) * roundFactor :=
          Nat.mul_le_mul (hAllowedPosCard Q W j) hRoundBound
        _ = B := by dsimp [B]
    let shapeOf (W : TargetWitness T k Ts m)
        (hW : CandidateTargetWitness LE events targets W) : Shape :=
      ⟨W.1, hW.1⟩
    have hItemAllowed (W : TargetWitness T k Ts m)
        (hW : CandidateTargetWitness LE events targets W) (j : Fin m) :
        W.2 j ∈ allowedOccurrences (shapeOf W hW) W j := by
      classical
      have hParent := hW.2.2.2 j
      rcases hParent with hRoot | ⟨i, hiParent, hNotDisjoint⟩
      · rcases hRoot.2 with ⟨C, hC, hScope⟩
        have hpos : (W.2 j).1 ∈ rootPositions := by
          dsimp [rootPositions]
          exact Finset.mem_biUnion.mpr ⟨C, hC,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hScope⟩⟩
        change (W.2 j) ∈ allowedPositions (shapeOf W hW) W j ×ˢ Finset.univ
        rw [Finset.mem_product]
        constructor
        · dsimp only [allowedPositions, shapeOf]
          split_ifs with h
          · exact hpos
          · exact False.elim (h hRoot.1)
        · exact Finset.mem_univ _
      · have hnotRoot :
        ¬ ((shapeOf W hW).1.2 (targetNode j)).val = 0 := by
          intro hz
          change (W.1.2 (targetNode j)).val = 0 at hz
          rw [hiParent] at hz
          simp [targetNode] at hz
        have hparentIndex : parentItem (shapeOf W hW) j = i := by
          apply Fin.ext
          have hi : (W.1.2 (targetNode j)).val = i.val + 1 := by
            simpa [targetNode] using congrArg Fin.val hiParent
          change (W.1.2 (targetNode j)).val - 1 = i.val
          omega
        have hpos : (W.2 j).1 ∈ closePositions ((W.2 i).1) := by
          dsimp [closePositions]
          by_cases heq : (W.2 j).1 = (W.2 i).1
          · simp [heq]
          · apply Finset.mem_insert_of_mem
            apply Finset.mem_filter.mpr
            have hReverse :
                ¬ Disjoint (LE.scope (W.2 i).1) (LE.scope (W.2 j).1) := by
              intro hdis
              exact hNotDisjoint hdis.symm
            exact ⟨Finset.mem_univ _, ⟨Ne.symm heq, hReverse⟩⟩
        change (W.2 j) ∈ allowedPositions (shapeOf W hW) W j ×ˢ Finset.univ
        rw [Finset.mem_product]
        constructor
        · dsimp only [allowedPositions, shapeOf]
          split_ifs with h
          · exact False.elim (hnotRoot h)
          · rw [hparentIndex]
            exact hpos
        · exact Finset.mem_univ _
    let rankOccurrence (S : Finset (ExecutionOccurrence T k Ts))
        (x : ExecutionOccurrence T k Ts) (hx : x ∈ S) (hS : S.card ≤ B) : Fin B :=
      Fin.castLE hS (Fin.cast (Fintype.card_coe S) (Fintype.equivFin S ⟨x, hx⟩))
    have hRankRecover (S S' : Finset (ExecutionOccurrence T k Ts))
        (x x' : ExecutionOccurrence T k Ts) (hx : x ∈ S) (hx' : x' ∈ S')
        (hS : S.card ≤ B) (hS' : S'.card ≤ B) (hSS' : S = S')
        (hr : rankOccurrence S x hx hS = rankOccurrence S' x' hx' hS') : x = x' := by
      subst S'
      have hfin : Fintype.equivFin S ⟨x, hx⟩ = Fintype.equivFin S ⟨x', hx'⟩ := by
        apply Fin.ext
        simpa [rankOccurrence] using congrArg Fin.val hr
      have hsub : (⟨x, hx⟩ : S) = ⟨x', hx'⟩ := (Fintype.equivFin S).injective hfin
      exact congrArg Subtype.val hsub
    have hAllowedEq (W W' : TargetWitness T k Ts m)
        (hW : CandidateTargetWitness LE events targets W)
        (hW' : CandidateTargetWitness LE events targets W')
        (hTree : W.1 = W'.1) (j : Fin m)
        (hPrefix : ∀ i : Fin m, i.val < j.val → W.2 i = W'.2 i) :
        allowedOccurrences (shapeOf W hW) W j =
          allowedOccurrences (shapeOf W' hW') W' j := by
      classical
      let Q := shapeOf W hW
      let R := shapeOf W' hW'
      have hQR : Q = R := by
        apply Subtype.ext
        exact hTree
      by_cases hroot : (Q.1.2 (targetNode j)).val = 0
      · have hroot' : (R.1.2 (targetNode j)).val = 0 := by
          rw [← hQR]
          exact hroot
        have hAllowedW : allowedPositions Q W j = rootPositions := by
          dsimp only [allowedPositions]
          split_ifs <;> rfl
        have hAllowedW' : allowedPositions R W' j = rootPositions := by
          dsimp only [allowedPositions]
          split_ifs <;> rfl
        change allowedPositions Q W j ×ˢ Finset.univ =
          allowedPositions R W' j ×ˢ Finset.univ
        rw [hAllowedW, hAllowedW']
      · have hroot' : ¬ (R.1.2 (targetNode j)).val = 0 := by
          intro h
          exact hroot (by rw [hQR]; exact h)
        have hSpec := hW.1
        have hSpec' := hW'.1
        have hParent := hW.2.2.2
        have hParent' := hW'.2.2.2
        have hParentExists : ∃ i : Fin m,
            W.1.2 (targetNode j) = targetNode i ∧
              ¬ Disjoint (LE.scope (W.2 j).1) (LE.scope (W.2 i).1) := by
          rcases hParent j with h | hp
          · exact False.elim (hroot h.1)
          · rcases hp with ⟨i, hi, hnd⟩
            exact ⟨i, hi, hnd⟩
        have hParentExists' : ∃ i : Fin m,
            W'.1.2 (targetNode j) = targetNode i ∧
              ¬ Disjoint (LE.scope (W'.2 j).1) (LE.scope (W'.2 i).1) := by
          rcases hParent' j with h | hp
          · exact False.elim (hroot' h.1)
          · rcases hp with ⟨i, hi, hnd⟩
            exact ⟨i, hi, hnd⟩
        rcases hParentExists with ⟨i, hiParent, hNotDisjoint⟩
        rcases hParentExists' with ⟨i', hiParent', hNotDisjoint'⟩
        have hchildPos : 0 < (targetNode j).val := by simp [targetNode]
        have htreeParent := (hSpec.2 (targetNode j) hchildPos).1
        have hiLt : i.val < j.val := by
          rw [hiParent] at htreeParent
          simp only [targetNode] at htreeParent
          omega
        have hparentIndex : parentItem Q j = i := by
          apply Fin.ext
          have hval : (W.1.2 (targetNode j)).val = i.val + 1 := by
            simpa [targetNode] using congrArg Fin.val hiParent
          change (W.1.2 (targetNode j)).val - 1 = i.val
          omega
        have hparentOccurrence : W.2 (parentItem Q j) =
            W'.2 (parentItem Q j) := by
          rw [hparentIndex]
          exact hPrefix i hiLt
        have hparentPos : (W.2 (parentItem Q j)).1 =
            (W'.2 (parentItem Q j)).1 := congrArg Prod.fst hparentOccurrence
        have hparentItemEq : parentItem Q j = parentItem R j := by rw [hQR]
        have hparentPosR : (W.2 (parentItem Q j)).1 =
            (W'.2 (parentItem R j)).1 := by
          rw [← hparentItemEq]
          exact hparentPos
        have hAllowedW : allowedPositions Q W j =
            closePositions ((W.2 (parentItem Q j)).1) := by
          dsimp only [allowedPositions]
          split_ifs <;> rfl
        have hAllowedW' : allowedPositions R W' j =
            closePositions ((W'.2 (parentItem R j)).1) := by
          dsimp only [allowedPositions]
          split_ifs <;> rfl
        have hCloseEq : closePositions ((W.2 (parentItem Q j)).1) =
            closePositions ((W'.2 (parentItem R j)).1) := congrArg closePositions hparentPosR
        change allowedPositions Q W j ×ˢ Finset.univ =
          allowedPositions R W' j ×ˢ Finset.univ
        rw [hAllowedW, hAllowedW', hCloseEq]
    let candidates : Finset (TargetWitness T k Ts m) :=
      Finset.univ.filter fun W => CandidateTargetWitness LE events targets W
    let Encoded := Shape × (Fin m → Fin B)
    let witnessShape (x : candidates) : Shape :=
      shapeOf x.1 ((Finset.mem_filter.mp x.2).2)
    let witnessRanks (x : candidates) : Fin m → Fin B := fun j =>
      rankOccurrence (allowedOccurrences (witnessShape x) x.1 j) (x.1.2 j)
        (hItemAllowed x.1 ((Finset.mem_filter.mp x.2).2) j)
        (hAllowedCard (witnessShape x) x.1 j)
    let encode (x : candidates) : Encoded := (witnessShape x, witnessRanks x)
    have hencodeInjective : Function.Injective encode := by
      intro x y hxy
      have hShape : witnessShape x = witnessShape y := congrArg Prod.fst hxy
      have hTree : x.1.1 = y.1.1 := congrArg Subtype.val hShape
      have hRanks : witnessRanks x = witnessRanks y := congrArg Prod.snd hxy
      have hPrefix : ∀ n, ∀ j : Fin m, j.val < n → x.1.2 j = y.1.2 j := by
        intro n
        induction n with
        | zero =>
            intro j hj
            omega
        | succ n ih =>
            intro j hj
            by_cases hjn : j.val < n
            · exact ih j hjn
            · have hjEq : j.val = n := by omega
              have hS : allowedOccurrences (witnessShape x) x.1 j =
                  allowedOccurrences (witnessShape y) y.1 j :=
                hAllowedEq x.1 y.1 ((Finset.mem_filter.mp x.2).2)
                  ((Finset.mem_filter.mp y.2).2) hTree j
                  (by intro i hi; exact ih i (by omega))
              have hrank : witnessRanks x j = witnessRanks y j :=
                congrFun hRanks j
              have hItem := hRankRecover (allowedOccurrences (witnessShape x) x.1 j)
                (allowedOccurrences (witnessShape y) y.1 j) (x.1.2 j) (y.1.2 j)
                (hItemAllowed x.1 ((Finset.mem_filter.mp x.2).2) j)
                (hItemAllowed y.1 ((Finset.mem_filter.mp y.2).2) j)
                (hAllowedCard (witnessShape x) x.1 j)
                (hAllowedCard (witnessShape y) y.1 j) hS hrank
              exact hItem
      apply Subtype.ext
      apply Prod.ext
      · exact hTree
      · funext j
        exact hPrefix m j j.isLt
    have hCodeCard : candidates.card ≤ Fintype.card Encoded := by
      calc
        candidates.card = Fintype.card candidates := (Fintype.card_coe candidates).symm
        _ ≤ Fintype.card Encoded := Fintype.card_le_of_injective encode hencodeInjective
    change candidates.card ≤ targetWitnessBase d Ts targets.card ^ m
    calc
      candidates.card ≤ Fintype.card Encoded := hCodeCard
      _ = Fintype.card Shape * B ^ m := by simp [Encoded, Fintype.card_fun]
      _ ≤ 4 ^ m * B ^ m := Nat.mul_le_mul_right _ hShapeBound
      _ = (4 * B) ^ m := by rw [← Nat.mul_pow]
      _ = targetWitnessBase d Ts targets.card ^ m := by
        congr 1
        simp [targetWitnessBase, B, rootFactor, roundFactor]
        ring

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
  classical
  intro m W hCandidate hReads hSeparated Ψ hΨ
  let I := Lane_q_s17_res2.TapeCoordinate D Ts
  let flatLaw := Lane_q_s17_res2.flatTapeLaw D Ts
  let readIndex (j : Fin m) (C : D.G.Cell) : Fin (Ts + 2) :=
    ⟨if C ∈ LE.scope (targetItems W j).1 then
        witnessReadIndex LE Ts (targetItems W) j C else 0, by
      split_ifs with hC
      · have hle := hReads.1 j C hC
        omega
      · omega⟩
  let terminalIndex (C : D.G.Cell) : Fin (Ts + 2) :=
    ⟨if C ∈ targets then targetTerminalIndex LE W C else 0, by
      split_ifs with hC
      · have hle := hSeparated.1 C hC
        omega
      · omega⟩
  let testSupport : Finset I := Finset.univ.biUnion fun j : Fin m =>
    (LE.scope (targetItems W j).1).image fun C => (⟨C, readIndex j C⟩ : I)
  let targetSupport : Finset I := targets.attach.image fun C =>
    (⟨C.1, terminalIndex C.1⟩ : I)
  let passes (x : Lane_q_s17_res2.FlatTapes D Ts) : Prop :=
    WitnessTestsPass LE Ts pools ((Lane_q_s17_res2.flattenTapes D Ts).symm x)
      (targetItems W)
  let indicator (x : Lane_q_s17_res2.FlatTapes D Ts) : ℝ :=
    if passes x then 1 else 0
  let terminalTest (x : Lane_q_s17_res2.FlatTapes D Ts) : ℝ :=
    Ψ (fun C : {C : D.G.Cell // C ∈ targets} =>
      x ⟨C.1, terminalIndex C.1⟩ (pools C.1))
  have hTestConfig (x : Lane_q_s17_res2.FlatTapes D Ts) (j : Fin m)
      (C : D.G.Cell) (hC : C ∈ LE.scope (targetItems W j).1) :
      witnessTestConfig LE Ts pools ((Lane_q_s17_res2.flattenTapes D Ts).symm x)
        (targetItems W) j C = x ⟨C, readIndex j C⟩ (pools C) := by
    have hle : witnessReadIndex LE Ts (targetItems W) j C ≤ Ts + 1 := by
      have := hReads.1 j C hC
      omega
    change x ⟨C, ⟨min (witnessReadIndex LE Ts (targetItems W) j C) (Ts + 1), by omega⟩⟩
      (pools C) = x ⟨C, readIndex j C⟩ (pools C)
    let tapeAtCell : Fin (Ts + 2) → TapeEntry D.F C := fun r => x ⟨C, r⟩
    change tapeAtCell ⟨min (witnessReadIndex LE Ts (targetItems W) j C) (Ts + 1), by omega⟩
        (pools C) = tapeAtCell (readIndex j C) (pools C)
    apply congrArg (fun r => tapeAtCell r (pools C))
    apply Fin.ext
    simp [readIndex, hC]
    omega
  have hTerminalConfig (x : Lane_q_s17_res2.FlatTapes D Ts)
      (C : {C : D.G.Cell // C ∈ targets}) :
      targetTerminalState LE pools targets
          ((Lane_q_s17_res2.flattenTapes D Ts).symm x) W C =
        x ⟨C.1, terminalIndex C.1⟩ (pools C.1) := by
    have hle : targetTerminalIndex LE W C.1 ≤ Ts + 1 := by
      have := hSeparated.1 C.1 C.2
      omega
    change x ⟨C.1, ⟨min (targetTerminalIndex LE W C.1) (Ts + 1), by omega⟩⟩
      (pools C.1) = x ⟨C.1, terminalIndex C.1⟩ (pools C.1)
    let tapeAtCell : Fin (Ts + 2) → TapeEntry D.F C.1 := fun r => x ⟨C.1, r⟩
    change tapeAtCell ⟨min (targetTerminalIndex LE W C.1) (Ts + 1), by omega⟩
        (pools C.1) = tapeAtCell (terminalIndex C.1) (pools C.1)
    apply congrArg (fun r => tapeAtCell r (pools C.1))
    apply Fin.ext
    simp [terminalIndex, C.2]
    omega
  have hDisjoint : Disjoint testSupport targetSupport := by
    apply Finset.disjoint_left.mpr
    intro q hqTest hqTarget
    rcases Finset.mem_biUnion.mp hqTest with ⟨j, hj, hjmem⟩
    rcases Finset.mem_image.mp hjmem with ⟨C, hCscope, hq₁⟩
    rcases Finset.mem_image.mp hqTarget with ⟨Ctar, hCtar, hq₂⟩
    have hcoord : (⟨C, readIndex j C⟩ : I) = ⟨Ctar.1, terminalIndex Ctar.1⟩ :=
      hq₁.trans hq₂.symm
    have hcell : C = Ctar.1 := congrArg Sigma.fst hcoord
    have hidx : (readIndex j C).val = (terminalIndex Ctar.1).val :=
      congrArg Fin.val (congrArg Sigma.snd hcoord)
    have hCtarget : C ∈ targets := by simpa [hcell] using Ctar.2
    have hsep := hSeparated.2 j C hCtarget hCscope
    rw [← hcell] at hidx
    simp [readIndex, hCscope, terminalIndex, hCtarget] at hidx
    omega
  have hDependsTest : FinProb.DependsOn indicator testSupport := by
    intro x y hxy
    have hPass : passes x ↔ passes y := by
      constructor
      · intro hpass j
        apply (LE.scope_ok (targetItems W j).1 _ _ ?_).mp (hpass j)
        intro C hC
        have hcoord : (⟨C, readIndex j C⟩ : I) ∈ testSupport := by
          apply Finset.mem_biUnion.mpr
          refine ⟨j, Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
        rw [hTestConfig x j C hC, hTestConfig y j C hC]
        exact congrArg (fun e => e (pools C)) (hxy _ hcoord)
      · intro hpass j
        apply (LE.scope_ok (targetItems W j).1 _ _ ?_).mpr (hpass j)
        intro C hC
        have hcoord : (⟨C, readIndex j C⟩ : I) ∈ testSupport := by
          apply Finset.mem_biUnion.mpr
          refine ⟨j, Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
        rw [hTestConfig x j C hC, hTestConfig y j C hC]
        exact congrArg (fun e => e (pools C)) (hxy _ hcoord)
    simp [indicator, hPass]
  have hDependsTerminal : FinProb.DependsOn terminalTest targetSupport := by
    intro x y hxy
    apply congrArg Ψ
    funext C
    have hcoord : (⟨C.1, terminalIndex C.1⟩ : I) ∈ targetSupport := by
      exact Finset.mem_image.mpr ⟨C, Finset.mem_attach _ _, rfl⟩
    exact congrArg (fun e => e (pools C.1)) (hxy _ hcoord)
  have hTestProbability :
      (tapeLaw D.F Ts).pr
        (fun tapes => WitnessTestsPass LE Ts pools tapes (targetItems W)) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) :=
    finiteResamplingWitnessTests LE Ts hn events pools h23 m (targetItems W)
      (by intro j; exact hCandidate.2.2.1 j) hReads
  have hIndicatorProbability : flatLaw.E indicator =
      (tapeLaw D.F Ts).pr
        (fun tapes => WitnessTestsPass LE Ts pools tapes (targetItems W)) := by
    rw [← Lane_q_s17_res2.tapeLaw_expect_flatten D Ts indicator]
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro tapes ht
    by_cases hpass : WitnessTestsPass LE Ts pools tapes (targetItems W)
    · simp [indicator, passes, hpass, Lane_q_s17_res2.flattenTapes]
    · simp [indicator, passes, hpass, Lane_q_s17_res2.flattenTapes]
  have hFactor : flatLaw.E (fun x => indicator x * terminalTest x) =
      flatLaw.E indicator * flatLaw.E terminalTest := by
    simpa [flatLaw, Lane_q_s17_res2.flatTapeLaw] using
      (Lane_q_s17_res2.pi_expect_mul_of_disjoint
        (fun i : I => FinLaw.pi fun P => D.F.fresh i.1 P)
        indicator terminalTest testSupport targetSupport
        hDependsTest hDependsTerminal hDisjoint)
  have hMainEq :
      (tapeLaw D.F Ts).E (fun tapes =>
        if WitnessTestsPass LE Ts pools tapes (targetItems W) then
          Ψ (targetTerminalState LE pools targets tapes W) else 0) =
        flatLaw.E (fun x => indicator x * terminalTest x) := by
    rw [← Lane_q_s17_res2.tapeLaw_expect_flatten D Ts
      (fun x => indicator x * terminalTest x)]
    congr 1
    funext tapes
    by_cases hpass : WitnessTestsPass LE Ts pools tapes (targetItems W)
    · have hstate :
        Ψ (targetTerminalState LE pools targets tapes W) =
          terminalTest (Lane_q_s17_res2.flattenTapes D Ts tapes) := by
        unfold terminalTest
        congr 1
        funext C
        simpa [Lane_q_s17_res2.flattenTapes] using
          hTerminalConfig (Lane_q_s17_res2.flattenTapes D Ts tapes) C
      simp [indicator, passes, Lane_q_s17_res2.flattenTapes, hpass, hstate]
    · simp [indicator, passes, Lane_q_s17_res2.flattenTapes, hpass]
  have hFresh : flatLaw.E terminalTest = (D.freshTargetLaw targets pools).E Ψ := by
    let targetType := {C : D.G.Cell // C ∈ targets}
    let coordinate (C : targetType) : I := ⟨C.1, terminalIndex C.1⟩
    have hCoordinateMem (C : targetType) : coordinate C ∈ targetSupport := by
      exact Finset.mem_image.mpr ⟨C, Finset.mem_attach _ _, rfl⟩
    let coordEquiv : {q : I // q ∈ targetSupport} ≃ targetType := {
      toFun := fun q => ⟨q.1.1, by
        rcases Finset.mem_image.mp q.2 with ⟨C, hC, hEq⟩
        have hcell : C.1 = q.1.1 := congrArg Sigma.fst hEq
        exact hcell.symm ▸ C.2⟩
      invFun := fun C => ⟨coordinate C, hCoordinateMem C⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rcases Finset.mem_image.mp q.2 with ⟨C, hC, hEq⟩
        have hcell : C.1 = q.1.1 := congrArg Sigma.fst hEq
        have hCeq : (⟨q.1.1, hcell.symm ▸ C.2⟩ : targetType) = C := by
          apply Subtype.ext
          exact hcell.symm
        exact (congrArg coordinate hCeq).trans hEq
      right_inv := by
        intro C
        apply Subtype.ext
        rfl }
    let stateEquiv :
        (∀ q : {q : I // q ∈ targetSupport}, D.F.State q.1.1) ≃
          (∀ C : targetType, D.F.State C.1) :=
      Equiv.piCongrLeft (fun C : targetType => D.F.State C.1) coordEquiv
    let poolLaws : ∀ i : I, FinLaw (TapeEntry D.F i.1) :=
      fun i => FinLaw.pi fun P => D.F.fresh i.1 P
    let poolDefault : ∀ i : I, TapeEntry D.F i.1 :=
      fun i P => Classical.choice
        (Lane_q_s17_res2.nonempty_of_finLaw (D.F.fresh i.1 P))
    let restrictedLaw : ∀ q : {q : I // q ∈ targetSupport},
        FinLaw (TapeEntry D.F q.1.1) := fun q => poolLaws q.1
    let terminalOnTarget (a : ∀ q : {q : I // q ∈ targetSupport},
        TapeEntry D.F q.1.1) : ℝ :=
      Ψ (fun C : targetType =>
        a ⟨coordinate C, hCoordinateMem C⟩ (pools C.1))
    have hRestrict : flatLaw.E terminalTest =
        (FinLaw.pi restrictedLaw).E terminalOnTarget := by
      calc
        flatLaw.E terminalTest =
            (FinLaw.pi restrictedLaw).E
              (fun a => terminalTest
                ((Equiv.piEquivPiSubtypeProd
                  (fun i : I => i ∈ targetSupport)
                  (fun i => TapeEntry D.F i.1)).symm
                    (a, fun i => poolDefault i.1))) := by
          exact Lane_q_s17_res2.pi_expect_depends poolLaws targetSupport
            terminalTest poolDefault hDependsTerminal
        _ = (FinLaw.pi restrictedLaw).E terminalOnTarget := by
          unfold FinLaw.E
          apply Finset.sum_congr rfl
          intro a ha
          change (FinLaw.pi restrictedLaw).w a *
              terminalTest
                ((Equiv.piEquivPiSubtypeProd
                  (fun i : I => i ∈ targetSupport)
                  (fun i => TapeEntry D.F i.1)).symm
                    (a, fun i => poolDefault i.1)) =
            (FinLaw.pi restrictedLaw).w a * terminalOnTarget a
          have hpoint : terminalTest
              ((Equiv.piEquivPiSubtypeProd
                (fun i : I => i ∈ targetSupport)
                (fun i => TapeEntry D.F i.1)).symm
                  (a, fun i => poolDefault i.1)) = terminalOnTarget a := by
            unfold terminalTest terminalOnTarget
            apply congrArg Ψ
            funext C
            simp [Equiv.piEquivPiSubtypeProd, coordinate, hCoordinateMem C]
          rw [hpoint]
    let evalPool (q : {q : I // q ∈ targetSupport})
        (tape : TapeEntry D.F q.1.1) : D.F.State q.1.1 :=
      tape (pools q.1.1)
    let targetTest (s : ∀ q : {q : I // q ∈ targetSupport},
        D.F.State q.1.1) : ℝ :=
      Ψ (fun C : targetType => s ⟨coordinate C, hCoordinateMem C⟩)
    have hMapExpect : (FinLaw.pi restrictedLaw).E terminalOnTarget =
        (FinLaw.pi (fun q => FinLaw.map (restrictedLaw q) (evalPool q))).E
          targetTest := by
      simpa [terminalOnTarget, targetTest, evalPool] using
        (Lane_q_s17_res2.pi_expect_map restrictedLaw evalPool targetTest)
    let freshOnTarget : ∀ q : {q : I // q ∈ targetSupport},
        FinLaw (D.F.State q.1.1) :=
      fun q => D.F.fresh q.1.1 (pools q.1.1)
    have hFreshProduct :
        FinLaw.pi (fun q => FinLaw.map (restrictedLaw q) (evalPool q)) =
          FinLaw.pi freshOnTarget := by
      apply Lane_q_s17_res2.law_ext
      intro s
      simp only [FinLaw.pi]
      apply Finset.prod_congr rfl
      intro q hq
      exact Lane_q_s17_res2.pi_eval_weight
        (fun P => D.F.fresh q.1.1 P) (pools q.1.1) (s q)
    have hTargetLaw : FinLaw.map (FinLaw.pi freshOnTarget) stateEquiv =
        D.freshTargetLaw targets pools := by
      apply Lane_q_s17_res2.law_ext
      intro y
      rw [Lane_q_s17_res2.map_equiv_weight (FinLaw.pi freshOnTarget) stateEquiv y]
      change (∏ q : {q : I // q ∈ targetSupport},
          (D.F.fresh q.1.1 (pools q.1.1)).w (stateEquiv.symm y q)) =
        ∏ C : targetType, (D.F.fresh C.1 (pools C.1)).w (y C)
      simpa [stateEquiv, coordEquiv, coordinate] using
        (Fintype.prod_equiv coordEquiv
          (fun q => (D.F.fresh q.1.1 (pools q.1.1)).w (y (coordEquiv q)))
          (fun C => (D.F.fresh C.1 (pools C.1)).w (y C)) (by intro q; rfl))
    calc
      flatLaw.E terminalTest = (FinLaw.pi restrictedLaw).E terminalOnTarget := hRestrict
      _ = (FinLaw.pi (fun q => FinLaw.map (restrictedLaw q) (evalPool q))).E
          targetTest := hMapExpect
      _ = (FinLaw.pi freshOnTarget).E targetTest := by rw [hFreshProduct]
      _ = (FinLaw.map (FinLaw.pi freshOnTarget) stateEquiv).E Ψ := by
        calc
          (FinLaw.pi freshOnTarget).E targetTest =
              (FinLaw.pi freshOnTarget).E (fun s => Ψ (stateEquiv s)) := by
            congr 1
          _ = (FinLaw.map (FinLaw.pi freshOnTarget) stateEquiv).E Ψ :=
            (Lane_q_s17_res2.map_E (FinLaw.pi freshOnTarget) stateEquiv Ψ).symm
      _ = (D.freshTargetLaw targets pools).E Ψ := by rw [hTargetLaw]
  calc
    (tapeLaw D.F Ts).E (fun tapes =>
        if WitnessTestsPass LE Ts pools tapes (targetItems W) then
          Ψ (targetTerminalState LE pools targets tapes W) else 0) =
      flatLaw.E (fun x => indicator x * terminalTest x) := hMainEq
    _ = flatLaw.E indicator * flatLaw.E terminalTest := hFactor
    _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
        (D.freshTargetLaw targets pools).E Ψ := by
      rw [hFresh]
      apply mul_le_mul_of_nonneg_right
        (hIndicatorProbability.symm ▸ hTestProbability)
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg ((D.freshTargetLaw targets pools).nonneg s) (hΨ s)
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
  classical
  apply Filter.Eventually.of_forall
  intro k PT D LE order events pools targets v hInput hCover hCount hTests
  have hnNat : 2 ≤ T.S.n k := hInput.n_two
  let Ts := initialResamplingRounds T k
  have hnR : 1 ≤ (T.S.n k : ℝ) := by
    exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 2) hnNat)
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := Real.log_nonneg hnR
  have hlogle : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) :=
    Real.log_le_self (by positivity)
  have hlogSq : (Real.log (T.S.n k : ℝ)) ^ 2 ≤ (T.S.n k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((T.S.n k : ℝ) - Real.log (T.S.n k : ℝ))]
  have hTs : Ts ≤ (T.S.n k) ^ 2 := by
    dsimp [Ts, initialResamplingRounds]
    exact Nat.ceil_le.mpr (by rw [Nat.cast_pow]; exact hlogSq)
  have hTspos : 1 ≤ Ts := by
    have hnRgt : 1 < (T.S.n k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hnNat)
    have hlogpos : 0 < Real.log (T.S.n k : ℝ) := Real.log_pos hnRgt
    have hceil : 0 < Ts := by
      dsimp [Ts, initialResamplingRounds]
      exact Nat.ceil_pos.mpr (sq_pos_of_pos hlogpos)
    omega
  let P := tapeLaw D.F Ts
  let M := Fintype.card (Pos T k × Option (Fin Ts))
  let Enc := Σ m : Fin (M + 1), ComponentWitness T k Ts m.val
  let base := componentWitnessBase ((T.S.n k) ^ (κ.Ac + 4)) Ts
  let good (a : Enc) : Prop :=
    Ts ≤ a.1.val ∧ 0 < a.1.val ∧
      CandidateWitness LE Ts events v a.1.val a.2 ∧
      WitnessReadsDisjoint LE Ts a.2.2
  let passes (a : Enc) (tapes : Tapes D.F Ts) : Prop :=
    WitnessTestsPass LE Ts pools tapes a.2.2
  have hLength (m : ℕ) (W : ComponentWitness T k Ts m)
      (hCand : CandidateWitness LE Ts events v m W) : m ≤ M := by
    have hcard := Fintype.card_le_of_injective W.2 hCand.2.1
    simpa [M] using hcard
  have hCoverFinite : ∀ tapes, LE.S v (LE.resample Ts order events pools tapes.extend) →
      ∃ a : Enc, good a ∧ passes a tapes := by
    intro tapes hfinal
    obtain ⟨m, hmTs, hmpos, W, hCand, hReads, hPass⟩ := hCover tapes hfinal
    have hmM := hLength m W hCand
    let a : Enc := ⟨⟨m, by omega⟩, W⟩
    exact ⟨a, ⟨hmTs, hmpos, hCand, hReads⟩, hPass⟩
  have hUnion := Lane_q_s17_res2.pr_iUnion_le_sum P (fun a tapes => good a ∧ passes a tapes)
  have hProb : P.pr (fun tapes => LE.S v (LE.resample Ts order events pools tapes.extend)) ≤
      ∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes) := by
    apply (Lane_q_s17_res2.pr_mono P ?_).trans hUnion
    intro tapes hfinal
    obtain ⟨a, ha, hp⟩ := hCoverFinite tapes hfinal
    exact ⟨a, ha, hp⟩
  let goodAt (m : ℕ) (W : ComponentWitness T k Ts m) : Prop :=
    Ts ≤ m ∧ 0 < m ∧ CandidateWitness LE Ts events v m W ∧
      WitnessReadsDisjoint LE Ts W.2
  let weightedTests (m : ℕ) : ℝ :=
    ∑ W : ComponentWitness T k Ts m,
      P.pr (fun tapes => goodAt m W ∧ WitnessTestsPass LE Ts pools tapes W.2)
  let tailTerm (m : ℕ) : ℝ :=
    if Ts ≤ m then (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) else 0
  have hGrouped :
      (∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes)) ≤
        ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
    calc
      (∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes)) =
          ∑ m : Fin (M + 1), weightedTests m.val := by
            rw [Fintype.sum_sigma]
      _ ≤ ∑ m : Fin (M + 1),
          if Ts ≤ m.val then
            (base : ℝ) ^ m.val * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m.val)) else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            by_cases hlen : Ts ≤ m.val
            · simp only [if_pos hlen]
              let sGood : Finset (ComponentWitness T k Ts m.val) :=
                Finset.univ.filter (goodAt m.val)
              have hEq : weightedTests m.val =
                  ∑ W ∈ sGood, P.pr
                    (fun tapes => WitnessTestsPass LE Ts pools tapes W.2) := by
                unfold weightedTests
                calc
                  _ = ∑ W, if goodAt m.val W then P.pr
                        (fun tapes => WitnessTestsPass LE Ts pools tapes W.2) else 0 := by
                    apply Finset.sum_congr rfl
                    intro W hW
                    by_cases hg : goodAt m.val W <;> simp [hg, FinLaw.pr]
                  _ = _ := by simp [sGood, Finset.sum_filter]
              rw [hEq]
              let sCand : Finset (ComponentWitness T k Ts m.val) := Finset.univ.filter
                (CandidateWitness LE Ts events v m.val)
              have hCard : sGood.card ≤ sCand.card := by
                apply Finset.card_le_card
                intro W hW
                rcases (Finset.mem_filter.mp hW).2 with ⟨hTs', hpos, hCand, hReads⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCand⟩
              have hmpos : 0 < m.val := by omega
              have hcount := hCount m.val hmpos
              have hcardReal : (sGood.card : ℝ) ≤ (base : ℝ) ^ m.val := by
                exact_mod_cast hCard.trans hcount
              have hsum :
                  (∑ W ∈ sGood, P.pr
                    (fun tapes => WitnessTestsPass LE Ts pools tapes W.2)) ≤
                  (sGood.card : ℝ) * Real.rpow (T.S.n k : ℝ)
                    (-((κ.P : ℝ) * m.val)) := by
                calc
                  _ ≤ ∑ W ∈ sGood, Real.rpow (T.S.n k : ℝ)
                        (-((κ.P : ℝ) * m.val)) := by
                    apply Finset.sum_le_sum
                    intro W hW
                    rcases (Finset.mem_filter.mp hW).2 with ⟨hTs', hpos, hCand, hReads⟩
                    rcases hCand with ⟨_, _, _, hEvents, _⟩
                    exact hTests m.val W.2 hEvents hReads
                  _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
              have hnRpow : 0 ≤ Real.rpow (T.S.n k : ℝ)
                  (-((κ.P : ℝ) * m.val)) := Real.rpow_nonneg (by positivity) _
              exact hsum.trans
                (mul_le_mul_of_nonneg_right hcardReal hnRpow)
            · have hzero : weightedTests m.val = 0 := by
                unfold weightedTests
                apply Finset.sum_eq_zero
                intro W hW
                have hnot : ¬ goodAt m.val W := by
                  intro hg
                  exact hlen hg.1
                simp [hnot, FinLaw.pr]
              simp [hlen, hzero]
      _ = ∑ m : Fin (M + 1), tailTerm m.val := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hlen : Ts ≤ m.val <;> simp [tailTerm, hlen]
      _ = ∑ m ∈ Finset.range (M + 1), tailTerm m := by
            exact Fin.sum_univ_eq_sum_range tailTerm (M + 1)
      _ = ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
            simp [tailTerm, Finset.sum_filter]
  have hP : 21000 ≤ κ.P := by
    calc
      21000 = 100 * (κ.Ac + 10) := by norm_num [hκ.Ac_eq]
      _ ≤ κ.P := hκ.P_big.2
  have hAc : κ.Ac + 4 = 204 := by simp [hκ.Ac_eq]
  have hd : (T.S.n k) ^ (κ.Ac + 4) + 1 ≤ 2 * (T.S.n k) ^ 204 := by
    rw [hAc]
    have hp : 0 < (T.S.n k) ^ 204 := pow_pos (by omega) 204
    have hp' : 1 ≤ (T.S.n k) ^ 204 := by omega
    omega
  have hbaseNat : base ≤ (T.S.n k) ^ 825 := by
    have hTsplus : Ts + 1 ≤ 2 * (T.S.n k) ^ 2 := by
      have hpPos : 0 < (T.S.n k) ^ 2 := pow_pos (by omega) 2
      have hp : 1 ≤ (T.S.n k) ^ 2 := by omega
      calc
        Ts + 1 ≤ (T.S.n k) ^ 2 + 1 := Nat.add_le_add_right hTs 1
        _ ≤ 2 * (T.S.n k) ^ 2 := by omega
    dsimp [base, componentWitnessBase]
    calc
      _ ≤ 4 * (2 * (T.S.n k) ^ 204) ^ 4 * (2 * (T.S.n k) ^ 2) := by gcongr
      _ = 4 * (16 * (T.S.n k ^ 204) ^ 4) * (2 * (T.S.n k) ^ 2) := by
        rw [Nat.mul_pow]
      _ = 4 * (16 * (T.S.n k) ^ (204 * 4)) * (2 * (T.S.n k) ^ 2) := by
        rw [← pow_mul]
      _ = 128 * ((T.S.n k) ^ (204 * 4) * (T.S.n k) ^ 2) := by ring
      _ = 128 * (T.S.n k) ^ (204 * 4 + 2) := by rw [← pow_add]
      _ = 128 * (T.S.n k) ^ 818 := by norm_num
      _ ≤ (T.S.n k) ^ 825 := by
        have hpow : 128 ≤ (T.S.n k) ^ 7 := by
          have h := Nat.pow_le_pow_left hInput.n_two 7
          norm_num at h ⊢
          exact h
        calc
          128 * (T.S.n k) ^ 818 ≤ (T.S.n k) ^ 7 * (T.S.n k) ^ 818 :=
            Nat.mul_le_mul_right _ hpow
          _ = (T.S.n k) ^ 825 := by rw [← pow_add]
  let q : ℝ := (base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))
  have hnPositive : 0 < (T.S.n k : ℝ) := by positivity
  have hterm (m : ℕ) :
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) = q ^ m := by
    have hpow := Real.rpow_mul_natCast (by positivity : 0 ≤ (T.S.n k : ℝ))
      (-(κ.P : ℝ)) m
    have hpow' : Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
        (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by
      have hExp : (-(κ.P : ℝ)) * (m : ℝ) = -((κ.P : ℝ) * (m : ℝ)) := by ring
      simpa [hExp] using hpow
    calc
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
          (base : ℝ) ^ m * (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [hpow']
      _ = ((base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [← mul_pow]
      _ = q ^ m := rfl
  have hqBound : q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := by
    have hBaseReal : (base : ℝ) ≤ Real.rpow (T.S.n k : ℝ) 825 := by
      have hcast : (base : ℝ) ≤ (T.S.n k : ℝ) ^ 825 := by exact_mod_cast hbaseNat
      calc
        (base : ℝ) ≤ (T.S.n k : ℝ) ^ (825 : ℕ) := hcast
        _ = Real.rpow (T.S.n k : ℝ) 825 := by
          exact (Real.rpow_natCast (T.S.n k : ℝ) 825).symm
    have hexp : (825 : ℝ) - κ.P ≤ -((κ.P : ℝ) + 2) / 2 := by
      have hp : 1652 ≤ κ.P := by omega
      have hpR : (1652 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) 825 *
          Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
            dsimp [q]
            exact mul_le_mul_of_nonneg_right hBaseReal
              (Real.rpow_nonneg (by positivity) _)
      _ = Real.rpow (T.S.n k : ℝ) (825 - κ.P) := by
        have hadd := Real.rpow_add hnPositive (825 : ℝ) (-(κ.P : ℝ))
        have hExp : (825 : ℝ) + -(κ.P : ℝ) = 825 - κ.P := by ring
        simpa [hExp] using hadd.symm
      _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hnR hexp
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqHalf : q ≤ 1 / 2 := by
    have hexp : -((κ.P : ℝ) + 2) / 2 ≤ -1 := by
      have hp : 2 ≤ κ.P := by omega
      have hpR : (2 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := hqBound
      _ ≤ Real.rpow (T.S.n k : ℝ) (-1) := Real.rpow_le_rpow_of_exponent_le hnR hexp
      _ = ((T.S.n k : ℝ)⁻¹) := by
        change (T.S.n k : ℝ) ^ (-1 : ℝ) = (T.S.n k : ℝ)⁻¹
        exact Real.rpow_neg_one (T.S.n k : ℝ)
      _ ≤ 1 / 2 := by
        have hn2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hInput.n_two
        calc
          (T.S.n k : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ hnPositive (by norm_num : (0 : ℝ) < 2)).mpr hn2
          _ = 1 / 2 := by norm_num
  have hGeo := Lane_q_s17_res2.sum_geometric_tail hq0 hqHalf Ts M
  have hqTs : 2 * q ^ Ts ≤ Real.rpow (T.S.n k : ℝ)
      (-((κ.P : ℝ) * Ts / 2)) := by
    have hqTs' : q ^ Ts ≤ Real.rpow (T.S.n k : ℝ)
        (-((κ.P : ℝ) * Ts / 2) - Ts) := by
      calc
        q ^ Ts ≤ (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2)) ^ Ts :=
          pow_le_pow_left₀ hq0 hqBound Ts
        _ = Real.rpow (T.S.n k : ℝ)
            ((-((κ.P : ℝ) + 2) / 2) * Ts) := by
              exact (Real.rpow_mul_natCast (by positivity)
                (-((κ.P : ℝ) + 2) / 2) Ts).symm
        _ = Real.rpow (T.S.n k : ℝ)
            (-((κ.P : ℝ) * Ts / 2) - Ts) := by
              congr 1
              ring
    have hhalf : Real.rpow (T.S.n k : ℝ) (-Ts) ≤ 1 / 2 := by
      have hpow : 2 ≤ (T.S.n k : ℝ) ^ Ts := by
        have hpown : 2 ≤ T.S.n k ^ Ts := by
          exact Nat.le_trans hInput.n_two
            (by
              have hpow := pow_le_pow_right' (by omega : 1 ≤ T.S.n k) hTspos
              simpa using hpow)
        exact_mod_cast hpown
      have hinv : Real.rpow (T.S.n k : ℝ) (-Ts) =
          ((T.S.n k : ℝ) ^ Ts)⁻¹ := by
        simpa using (Real.rpow_neg (by positivity : 0 ≤ (T.S.n k : ℝ)) (Ts : ℝ))
      rw [hinv]
      have hpowR : (2 : ℝ) ≤ (T.S.n k : ℝ) ^ Ts := by exact_mod_cast hpow
      calc
        ((T.S.n k : ℝ) ^ Ts)⁻¹ ≤ (2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (pow_pos hnPositive Ts) (by norm_num : (0 : ℝ) < 2)).mpr hpowR
        _ = 1 / 2 := by norm_num
    calc
      2 * q ^ Ts ≤ 2 * (Real.rpow (T.S.n k : ℝ)
          (-((κ.P : ℝ) * Ts / 2) - Ts)) := mul_le_mul_of_nonneg_left hqTs' (by norm_num)
      _ = 2 * (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) *
          Real.rpow (T.S.n k : ℝ) (-Ts)) := by
            have hadd := Real.rpow_add hnPositive
              (-((κ.P : ℝ) * Ts / 2)) (-Ts)
            have hmul : Real.rpow (T.S.n k : ℝ)
                (-((κ.P : ℝ) * Ts / 2) - Ts) =
              Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) *
                Real.rpow (T.S.n k : ℝ) (-Ts) := by
              simpa [sub_eq_add_neg] using hadd
            rw [hmul]
      _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) := by
          have hnonneg : 0 ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) :=
            Real.rpow_nonneg (by positivity) _
          nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg]
  calc
    P.pr (fun tapes => LE.S v (LE.resample Ts order events pools tapes.extend)) ≤
      ∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes) := hProb
    _ ≤ ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := hGrouped
    _ = ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m), q ^ m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm m
    _ ≤ 2 * q ^ Ts := hGeo
    _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) := hqTs

set_option maxHeartbeats 400000 in
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
  classical
  apply Filter.Eventually.of_forall
  intro k PT D LE order events pools targets v hInput hCover hCount hTests
  have hnNat : 2 ≤ T.S.n k := hInput.n_two
  let Ts := initialResamplingRounds T k
  have hnR : 1 ≤ (T.S.n k : ℝ) := by
    exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 2) hnNat)
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := Real.log_nonneg hnR
  have hlogle : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) :=
    Real.log_le_self (by positivity)
  have hlogSq : (Real.log (T.S.n k : ℝ)) ^ 2 ≤ (T.S.n k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((T.S.n k : ℝ) - Real.log (T.S.n k : ℝ))]
  have hTs : Ts ≤ (T.S.n k) ^ 2 := by
    dsimp [Ts, initialResamplingRounds]
    exact Nat.ceil_le.mpr (by rw [Nat.cast_pow]; exact hlogSq)
  have hTspos : 1 ≤ Ts := by
    have hnRgt : 1 < (T.S.n k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hnNat)
    have hlogpos : 0 < Real.log (T.S.n k : ℝ) := Real.log_pos hnRgt
    have hceil : 0 < Ts := by
      dsimp [Ts, initialResamplingRounds]
      exact Nat.ceil_pos.mpr (sq_pos_of_pos hlogpos)
    omega
  let P := tapeLaw D.F Ts
  let M := Fintype.card (Pos T k × Fin Ts)
  let Enc := Σ m : Fin (M + 1), TargetWitness T k Ts m.val
  let base := targetWitnessBase ((T.S.n k) ^ (κ.Ac + 4)) Ts targets.card
  let goodAt (m : ℕ) (W : TargetWitness T k Ts m) : Prop :=
    Ts ≤ m ∧ 0 < m ∧ CandidateTargetWitness LE events targets W ∧
      WitnessReadsDisjoint LE Ts (targetItems W)
  let good (a : Enc) : Prop := goodAt a.1.val a.2
  let passes (a : Enc) (tapes : Tapes D.F Ts) : Prop :=
    WitnessTestsPass LE Ts pools tapes (targetItems a.2)
  have hLength (m : ℕ) (W : TargetWitness T k Ts m)
      (hCand : CandidateTargetWitness LE events targets W) : m ≤ M := by
    have hcard := Fintype.card_le_of_injective W.2 hCand.2.1
    simpa [M] using hcard
  have hCoverFinite : ∀ tapes,
      (backwardClosure LE order events pools tapes targets).card > Ts →
      ∃ a : Enc, good a ∧ passes a tapes := by
    intro tapes hlarge
    obtain ⟨m, W, hActual⟩ := hCover tapes
    have hmCard : (backwardClosure LE order events pools tapes targets).card = m := by
      calc
        _ = (Finset.univ.image W.2).card := by rw [← hActual.2.1]
        _ = m := by rw [Finset.card_image_of_injective _ hActual.1.2.1]; simp
    have hmTs : Ts < m := by omega
    have hmM := hLength m W hActual.1
    let a : Enc := ⟨⟨m, by omega⟩, W⟩
    refine ⟨a, ?_, ?_⟩
    · exact ⟨hmTs.le, hmTs.pos, hActual.1, hActual.2.2.1⟩
    · exact hActual.2.2.2.1
  have hUnion := Lane_q_s17_res2.pr_iUnion_le_sum P
    (fun a tapes => good a ∧ passes a tapes)
  have hProb : P.pr (fun tapes =>
      (backwardClosure LE order events pools tapes targets).card > Ts) ≤
      ∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes) := by
    apply (Lane_q_s17_res2.pr_mono P ?_).trans hUnion
    intro tapes hlarge
    obtain ⟨a, ha, hp⟩ := hCoverFinite tapes hlarge
    exact ⟨a, ha, hp⟩
  let weightedTests (m : ℕ) : ℝ :=
    ∑ W : TargetWitness T k Ts m,
      P.pr (fun tapes => goodAt m W ∧
        WitnessTestsPass LE Ts pools tapes (targetItems W))
  let tailTerm (m : ℕ) : ℝ :=
    if Ts ≤ m then (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ)
      (-((κ.P : ℝ) * m)) else 0
  have hGrouped :
      (∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes)) ≤
        ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
    calc
      (∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes)) =
          ∑ m : Fin (M + 1), weightedTests m.val := by rw [Fintype.sum_sigma]
      _ ≤ ∑ m : Fin (M + 1),
          if Ts ≤ m.val then
            (base : ℝ) ^ m.val * Real.rpow (T.S.n k : ℝ)
              (-((κ.P : ℝ) * m.val)) else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            by_cases hlen : Ts ≤ m.val
            · simp only [if_pos hlen]
              let sGood : Finset (TargetWitness T k Ts m.val) :=
                Finset.univ.filter (goodAt m.val)
              have hEq : weightedTests m.val =
                  ∑ W ∈ sGood, P.pr
                    (fun tapes => WitnessTestsPass LE Ts pools tapes (targetItems W)) := by
                unfold weightedTests
                calc
                  _ = ∑ W, if goodAt m.val W then P.pr
                        (fun tapes => WitnessTestsPass LE Ts pools tapes (targetItems W)) else 0 := by
                    apply Finset.sum_congr rfl
                    intro W hW
                    by_cases hg : goodAt m.val W <;> simp [hg, FinLaw.pr]
                  _ = _ := by simp [sGood, Finset.sum_filter]
              rw [hEq]
              let sCand : Finset (TargetWitness T k Ts m.val) := Finset.univ.filter
                (CandidateTargetWitness LE events targets)
              have hCard : sGood.card ≤ sCand.card := by
                apply Finset.card_le_card
                intro W hW
                rcases (Finset.mem_filter.mp hW).2 with ⟨hTs', hpos, hCand, hReads⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCand⟩
              have hcardReal : (sGood.card : ℝ) ≤ (base : ℝ) ^ m.val := by
                have hcount := hCount m.val
                exact_mod_cast hCard.trans hcount
              have hsum :
                  (∑ W ∈ sGood, P.pr
                    (fun tapes => WitnessTestsPass LE Ts pools tapes (targetItems W))) ≤
                  (sGood.card : ℝ) * Real.rpow (T.S.n k : ℝ)
                    (-((κ.P : ℝ) * m.val)) := by
                calc
                  _ ≤ ∑ W ∈ sGood, Real.rpow (T.S.n k : ℝ)
                        (-((κ.P : ℝ) * m.val)) := by
                    apply Finset.sum_le_sum
                    intro W hW
                    rcases (Finset.mem_filter.mp hW).2 with ⟨hTs', hpos, hCand, hReads⟩
                    rcases hCand with ⟨_, _, hEvents, _⟩
                    exact hTests m.val (targetItems W) hEvents hReads
                  _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
              have hnRpow : 0 ≤ Real.rpow (T.S.n k : ℝ)
                  (-((κ.P : ℝ) * m.val)) := Real.rpow_nonneg (by positivity) _
              exact hsum.trans (mul_le_mul_of_nonneg_right hcardReal hnRpow)
            · have hzero : weightedTests m.val = 0 := by
                unfold weightedTests
                apply Finset.sum_eq_zero
                intro W hW
                have hnot : ¬ goodAt m.val W := by
                  intro hg
                  exact hlen hg.1
                simp [hnot, FinLaw.pr]
              simp [hlen, hzero]
      _ = ∑ m : Fin (M + 1), tailTerm m.val := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hlen : Ts ≤ m.val <;> simp [tailTerm, hlen]
      _ = ∑ m ∈ Finset.range (M + 1), tailTerm m := by
            exact Fin.sum_univ_eq_sum_range tailTerm (M + 1)
      _ = ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := by
            simp [tailTerm, Finset.sum_filter]
  have hP : 21000 ≤ κ.P := by
    calc
      21000 = 100 * (κ.Ac + 10) := by norm_num [hκ.Ac_eq]
      _ ≤ κ.P := hκ.P_big.2
  have hAc : κ.Ac + 4 = 204 := by simp [hκ.Ac_eq]
  have hDplus : (T.S.n k) ^ (κ.Ac + 4) + 1 ≤ 2 * (T.S.n k) ^ 204 := by
    rw [hAc]
    have hpow : 0 < (T.S.n k) ^ 204 := pow_pos (by omega) 204
    omega
  have hD204 : (T.S.n k) ^ 204 + 1 ≤ 2 * (T.S.n k) ^ 204 := by
    have hpow : 0 < (T.S.n k) ^ 204 := pow_pos (by omega) 204
    omega
  have hTargetCount : targets.card ≤ (T.S.n k) ^ 2100 := by
    simpa [hκ.Ac_eq] using hInput.targets_count
  have hTargetProduct : targets.card * ((T.S.n k) ^ 204 + 1) ≤
      2 * (T.S.n k) ^ 2304 := by
    calc
      _ ≤ (T.S.n k) ^ 2100 * ((T.S.n k) ^ 204 + 1) :=
        Nat.mul_le_mul_right _ hTargetCount
      _ ≤ (T.S.n k) ^ 2100 * (2 * (T.S.n k) ^ 204) :=
        Nat.mul_le_mul_left _ hD204
      _ = 2 * ((T.S.n k) ^ 2100 * (T.S.n k) ^ 204) := by ring
      _ = 2 * (T.S.n k) ^ 2304 := by
        rw [← pow_add]
  have hTargetFactor : max 1 (targets.card * ((T.S.n k) ^ 204 + 1)) ≤
      2 * (T.S.n k) ^ 2304 := by
    exact max_le_iff.mpr ⟨by
      have hp : 1 ≤ (T.S.n k) ^ 2304 := by
        have hp' : 0 < (T.S.n k) ^ 2304 := pow_pos (by omega) 2304
        omega
      omega, hTargetProduct⟩
  have hTsMax : max 1 Ts = Ts := max_eq_right hTspos
  have hBaseNat : base ≤ (T.S.n k) ^ 2514 := by
    dsimp [base, targetWitnessBase]
    rw [hAc, hTsMax]
    calc
      4 * max 1 (targets.card * ((T.S.n k) ^ 204 + 1)) *
          ((T.S.n k) ^ 204 + 1) * Ts ≤
        4 * (2 * (T.S.n k) ^ 2304) * (2 * (T.S.n k) ^ 204) *
          (T.S.n k) ^ 2 := by gcongr
      _ = 16 * ((T.S.n k) ^ 2304 * (T.S.n k) ^ 204 * (T.S.n k) ^ 2) := by ring
      _ = 16 * (T.S.n k) ^ 2510 := by rw [← pow_add, ← pow_add]
      _ ≤ (T.S.n k) ^ 2514 := by
        have hpow : 16 ≤ (T.S.n k) ^ 4 := by
          have h := Nat.pow_le_pow_left hInput.n_two 4
          norm_num at h ⊢
          exact h
        calc
          16 * (T.S.n k) ^ 2510 ≤ (T.S.n k) ^ 4 * (T.S.n k) ^ 2510 :=
            Nat.mul_le_mul_right _ hpow
          _ = (T.S.n k) ^ 2514 := by rw [← pow_add]
  let q : ℝ := (base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))
  have hnPositive : 0 < (T.S.n k : ℝ) := by positivity
  have hterm (m : ℕ) :
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) = q ^ m := by
    have hpow := Real.rpow_mul_natCast (by positivity : 0 ≤ (T.S.n k : ℝ))
      (-(κ.P : ℝ)) m
    have hpow' : Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
        (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by
      have hExp : (-(κ.P : ℝ)) * (m : ℝ) = -((κ.P : ℝ) * (m : ℝ)) := by ring
      simpa [hExp] using hpow
    calc
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
          (base : ℝ) ^ m * (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [hpow']
      _ = ((base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [← mul_pow]
      _ = q ^ m := rfl
  have hqBound : q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := by
    have hBaseReal : (base : ℝ) ≤ Real.rpow (T.S.n k : ℝ) 2514 := by
      have hcast : (base : ℝ) ≤ (T.S.n k : ℝ) ^ (2514 : ℕ) := by exact_mod_cast hBaseNat
      calc
        (base : ℝ) ≤ (T.S.n k : ℝ) ^ (2514 : ℕ) := hcast
        _ = Real.rpow (T.S.n k : ℝ) 2514 := (Real.rpow_natCast _ _).symm
    have hexp : (2514 : ℝ) - κ.P ≤ -((κ.P : ℝ) + 2) / 2 := by
      have hp : 5030 ≤ κ.P := by omega
      have hpR : (5030 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) 2514 *
          Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
            dsimp [q]
            exact mul_le_mul_of_nonneg_right hBaseReal
              (Real.rpow_nonneg (by positivity) _)
      _ = Real.rpow (T.S.n k : ℝ) (2514 - κ.P) := by
        have hadd := Real.rpow_add hnPositive (2514 : ℝ) (-(κ.P : ℝ))
        have hExp : (2514 : ℝ) + -(κ.P : ℝ) = 2514 - κ.P := by ring
        simpa [hExp] using hadd.symm
      _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hnR hexp
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqHalf : q ≤ 1 / 2 := by
    have hexp : -((κ.P : ℝ) + 2) / 2 ≤ -1 := by
      have hp : 2 ≤ κ.P := by omega
      have hpR : (2 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := hqBound
      _ ≤ Real.rpow (T.S.n k : ℝ) (-1) := Real.rpow_le_rpow_of_exponent_le hnR hexp
      _ = ((T.S.n k : ℝ)⁻¹) := by
        change (T.S.n k : ℝ) ^ (-1 : ℝ) = (T.S.n k : ℝ)⁻¹
        exact Real.rpow_neg_one (T.S.n k : ℝ)
      _ ≤ 1 / 2 := by
        have hn2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hInput.n_two
        calc
          (T.S.n k : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ hnPositive (by norm_num : (0 : ℝ) < 2)).mpr hn2
          _ = 1 / 2 := by norm_num
  have hGeo := Lane_q_s17_res2.sum_geometric_tail hq0 hqHalf Ts M
  have hqTs : 2 * q ^ Ts ≤ Real.rpow (T.S.n k : ℝ)
      (-((κ.P : ℝ) * Ts / 2)) := by
    have hqTs' : q ^ Ts ≤ Real.rpow (T.S.n k : ℝ)
        (-((κ.P : ℝ) * Ts / 2) - Ts) := by
      calc
        q ^ Ts ≤ (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2)) ^ Ts :=
          pow_le_pow_left₀ hq0 hqBound Ts
        _ = Real.rpow (T.S.n k : ℝ)
            ((-((κ.P : ℝ) + 2) / 2) * Ts) := by
              exact (Real.rpow_mul_natCast (by positivity)
                (-((κ.P : ℝ) + 2) / 2) Ts).symm
        _ = Real.rpow (T.S.n k : ℝ)
            (-((κ.P : ℝ) * Ts / 2) - Ts) := by
              congr 1
              ring
    have hhalf : Real.rpow (T.S.n k : ℝ) (-Ts) ≤ 1 / 2 := by
      have hpow : 2 ≤ (T.S.n k : ℝ) ^ Ts := by
        have hpown : 2 ≤ T.S.n k ^ Ts := by
          exact Nat.le_trans hInput.n_two
            (by
              have hpow := pow_le_pow_right' (by omega : 1 ≤ T.S.n k) hTspos
              simpa using hpow)
        exact_mod_cast hpown
      have hinv : Real.rpow (T.S.n k : ℝ) (-Ts) =
          ((T.S.n k : ℝ) ^ Ts)⁻¹ := by
        simpa using (Real.rpow_neg (by positivity : 0 ≤ (T.S.n k : ℝ)) (Ts : ℝ))
      rw [hinv]
      have hpowR : (2 : ℝ) ≤ (T.S.n k : ℝ) ^ Ts := by exact_mod_cast hpow
      calc
        ((T.S.n k : ℝ) ^ Ts)⁻¹ ≤ (2 : ℝ)⁻¹ :=
          (inv_le_inv₀ (pow_pos hnPositive Ts) (by norm_num : (0 : ℝ) < 2)).mpr hpowR
        _ = 1 / 2 := by norm_num
    calc
      2 * q ^ Ts ≤ 2 * (Real.rpow (T.S.n k : ℝ)
          (-((κ.P : ℝ) * Ts / 2) - Ts)) := mul_le_mul_of_nonneg_left hqTs' (by norm_num)
      _ = 2 * (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) *
          Real.rpow (T.S.n k : ℝ) (-Ts)) := by
            have hadd := Real.rpow_add hnPositive
              (-((κ.P : ℝ) * Ts / 2)) (-Ts)
            have hmul : Real.rpow (T.S.n k : ℝ)
                (-((κ.P : ℝ) * Ts / 2) - Ts) =
              Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) *
                Real.rpow (T.S.n k : ℝ) (-Ts) := by
              simpa [sub_eq_add_neg] using hadd
            rw [hmul]
      _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) := by
          have hnonneg : 0 ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) :=
            Real.rpow_nonneg (by positivity) _
          nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg]
  calc
    P.pr (fun tapes => (backwardClosure LE order events pools tapes targets).card > Ts) ≤
      ∑ a : Enc, P.pr (fun tapes => good a ∧ passes a tapes) := hProb
    _ ≤ ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) := hGrouped
    _ = ∑ m ∈ (Finset.range (M + 1)).filter (fun m => Ts ≤ m), q ^ m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm m
    _ ≤ 2 * q ^ Ts := hGeo
    _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * Ts / 2)) := hqTs

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
  classical
  apply Filter.Eventually.of_forall
  intro k PT D LE order events pools targets v hInput hCover hCount hTerminal Ψ hΨ
  have hnNat : 2 ≤ T.S.n k := hInput.n_two
  let Ts := initialResamplingRounds T k
  have hnR : 1 ≤ (T.S.n k : ℝ) := by
    exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 2) hnNat)
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := Real.log_nonneg hnR
  have hlogle : Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) :=
    Real.log_le_self (by positivity)
  have hlogSq : (Real.log (T.S.n k : ℝ)) ^ 2 ≤ (T.S.n k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((T.S.n k : ℝ) - Real.log (T.S.n k : ℝ))]
  have hTs : Ts ≤ (T.S.n k) ^ 2 := by
    dsimp [Ts, initialResamplingRounds]
    exact Nat.ceil_le.mpr (by rw [Nat.cast_pow]; exact hlogSq)
  have hTspos : 1 ≤ Ts := by
    have hnRgt : 1 < (T.S.n k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hnNat)
    have hlogpos : 0 < Real.log (T.S.n k : ℝ) := Real.log_pos hnRgt
    have hceil : 0 < Ts := by
      dsimp [Ts, initialResamplingRounds]
      exact Nat.ceil_pos.mpr (sq_pos_of_pos hlogpos)
    omega
  let P := tapeLaw D.F Ts
  let M := Fintype.card (Pos T k × Fin Ts)
  let Enc := Σ m : Fin (M + 1), TargetWitness T k Ts m.val
  let base := targetWitnessBase ((T.S.n k) ^ (κ.Ac + 4)) Ts targets.card
  let goodAt (m : ℕ) (W : TargetWitness T k Ts m) : Prop :=
    CandidateTargetWitness LE events targets W ∧
      WitnessReadsDisjoint LE Ts (targetItems W) ∧ TargetTerminalSeparated LE targets W
  let termAt (m : ℕ) (W : TargetWitness T k Ts m) (tapes : Tapes D.F Ts) : ℝ :=
    if goodAt m W ∧ WitnessTestsPass LE Ts pools tapes (targetItems W) then
      Ψ (targetTerminalState LE pools targets tapes W) else 0
  let weightedAt (m : ℕ) (W : TargetWitness T k Ts m) : ℝ := P.E (termAt m W)
  have hLength (m : ℕ) (W : TargetWitness T k Ts m)
      (hCand : CandidateTargetWitness LE events targets W) : m ≤ M := by
    have hcard := Fintype.card_le_of_injective W.2 hCand.2.1
    simpa [M] using hcard
  have hFreshNonneg : 0 ≤ (D.freshTargetLaw targets pools).E Ψ := by
    unfold FinLaw.E
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg ((D.freshTargetLaw targets pools).nonneg s) (hΨ s)
  have hTermNonneg (m : ℕ) (W : TargetWitness T k Ts m) (tapes : Tapes D.F Ts) :
      0 ≤ termAt m W tapes := by
    by_cases h : goodAt m W ∧ WitnessTestsPass LE Ts pools tapes (targetItems W)
    · simp [termAt, h, hΨ]
    · simp [termAt, h]
  have hPoint (tapes : Tapes D.F Ts) :
      Ψ (D.targetProjection targets
        (LE.resample Ts order events pools tapes.extend)) ≤
        ∑ a : Enc, termAt a.1.val a.2 tapes := by
    obtain ⟨m, W, hActual⟩ := hCover tapes
    have hmM : m ≤ M := hLength m W hActual.1
    let a : Enc := ⟨⟨m, by omega⟩, W⟩
    have hChosen : termAt m W tapes =
        Ψ (D.targetProjection targets
          (LE.resample Ts order events pools tapes.extend)) := by
      have hGood : goodAt m W := ⟨hActual.1, hActual.2.2.1, hActual.2.2.2.2.1⟩
      have hPass : WitnessTestsPass LE Ts pools tapes (targetItems W) := hActual.2.2.2.1
      have hFinal := hActual.2.2.2.2.2
      simp [termAt, hGood, hPass]
      exact congrArg Ψ hFinal.symm
    calc
      Ψ (D.targetProjection targets
          (LE.resample Ts order events pools tapes.extend)) = termAt m W tapes := hChosen.symm
      _ ≤ ∑ a : Enc, termAt a.1.val a.2 tapes :=
        Finset.single_le_sum (fun b hb => hTermNonneg b.1.val b.2 tapes)
          (Finset.mem_univ a)
  have hOutput := Lane_q_s17_res2.E_mono P hPoint
  have hInterchange : P.E (fun tapes => ∑ a : Enc, termAt a.1.val a.2 tapes) =
      ∑ a : Enc, weightedAt a.1.val a.2 := by
    unfold FinLaw.E weightedAt
    change
      (∑ tapes ∈ (Finset.univ : Finset (Tapes D.F Ts)),
        P.w tapes * ∑ a ∈ (Finset.univ : Finset Enc), termAt a.1.val a.2 tapes) =
        ∑ a ∈ (Finset.univ : Finset Enc),
          ∑ tapes ∈ (Finset.univ : Finset (Tapes D.F Ts)),
            P.w tapes * termAt a.1.val a.2 tapes
    calc
      _ = ∑ tapes ∈ (Finset.univ : Finset (Tapes D.F Ts)),
            ∑ a ∈ (Finset.univ : Finset Enc), P.w tapes * termAt a.1.val a.2 tapes := by
              apply Finset.sum_congr rfl
              intro tapes ht
              exact Finset.mul_sum _ _ _
      _ = _ := by rw [Finset.sum_comm]
  have hBoundAt (m : ℕ) :
      (∑ W : TargetWitness T k Ts m, weightedAt m W) ≤
        (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
          (D.freshTargetLaw targets pools).E Ψ := by
    let sGood : Finset (TargetWitness T k Ts m) := Finset.univ.filter (goodAt m)
    have hScalarNonneg :
        0 ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
          (D.freshTargetLaw targets pools).E Ψ :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) hFreshNonneg
    have hOne (W : TargetWitness T k Ts m) (hW : W ∈ sGood) :
        weightedAt m W ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
          (D.freshTargetLaw targets pools).E Ψ := by
      have hGood : goodAt m W := (Finset.mem_filter.mp hW).2
      unfold weightedAt
      calc
        P.E (termAt m W) = P.E (fun tapes =>
            if WitnessTestsPass LE Ts pools tapes (targetItems W) then
              Ψ (targetTerminalState LE pools targets tapes W) else 0) := by
                congr 1
                funext tapes
                simp [termAt, hGood]
        _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ :=
            hTerminal m W hGood.1 hGood.2.1 hGood.2.2 Ψ hΨ
    have hsum : (∑ W : TargetWitness T k Ts m, weightedAt m W) ≤
        (sGood.card : ℝ) *
          (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ) := by
      calc
        _ ≤ ∑ W : TargetWitness T k Ts m,
              if goodAt m W then
                Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
                  (D.freshTargetLaw targets pools).E Ψ else 0 := by
                apply Finset.sum_le_sum
                intro W hW
                by_cases hg : goodAt m W
                · have hW : W ∈ sGood := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
                  simpa [hg] using hOne W hW
                · simp [hg, weightedAt, termAt, FinLaw.E]
        _ = (sGood.card : ℝ) *
              (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
                (D.freshTargetLaw targets pools).E Ψ) := by
                  calc
                    (∑ W : TargetWitness T k Ts m,
                        if goodAt m W then
                          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
                            (D.freshTargetLaw targets pools).E Ψ else 0) =
                        ∑ W ∈ sGood,
                          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
                            (D.freshTargetLaw targets pools).E Ψ := by
                              change
                                (∑ W ∈ (Finset.univ : Finset (TargetWitness T k Ts m)),
                                  if goodAt m W then
                                    Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
                                      (D.freshTargetLaw targets pools).E Ψ else 0) = _
                              rw [← Finset.sum_filter]
                    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hCard : sGood.card ≤
        (Finset.univ.filter fun W : TargetWitness T k Ts m =>
          CandidateTargetWitness LE events targets W).card := by
      apply Finset.card_le_card
      intro W hW
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hW).2.1⟩
    have hcardReal : (sGood.card : ℝ) ≤ (base : ℝ) ^ m := by
      exact_mod_cast hCard.trans (hCount m)
    calc
      _ ≤ (base : ℝ) ^ m *
          (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ) :=
        hsum.trans (mul_le_mul_of_nonneg_right hcardReal hScalarNonneg)
      _ = _ := by ring
  have hGrouped :
      (∑ a : Enc, weightedAt a.1.val a.2) ≤
        ∑ m ∈ Finset.range (M + 1),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ := by
    calc
      (∑ a : Enc, weightedAt a.1.val a.2) =
          ∑ m : Fin (M + 1), ∑ W : TargetWitness T k Ts m.val, weightedAt m.val W := by
            rw [Fintype.sum_sigma]
      _ ≤ ∑ m : Fin (M + 1),
          (base : ℝ) ^ m.val * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m.val)) *
            (D.freshTargetLaw targets pools).E Ψ := by
            apply Finset.sum_le_sum
            intro m hm
            exact hBoundAt m.val
      _ = ∑ m ∈ Finset.range (M + 1),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ := by
            exact Fin.sum_univ_eq_sum_range
              (fun m => (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ)
                (-((κ.P : ℝ) * m)) * (D.freshTargetLaw targets pools).E Ψ) (M + 1)
  have hP : 21000 ≤ κ.P := by
    calc
      21000 = 100 * (κ.Ac + 10) := by norm_num [hκ.Ac_eq]
      _ ≤ κ.P := hκ.P_big.2
  have hAc : κ.Ac + 4 = 204 := by simp [hκ.Ac_eq]
  have hD204 : (T.S.n k) ^ 204 + 1 ≤ 2 * (T.S.n k) ^ 204 := by
    have hp : 0 < (T.S.n k) ^ 204 := pow_pos (by omega) 204
    omega
  have hTargetCount : targets.card ≤ (T.S.n k) ^ 2100 := by
    simpa [hκ.Ac_eq] using hInput.targets_count
  have hTargetProduct : targets.card * ((T.S.n k) ^ 204 + 1) ≤
      2 * (T.S.n k) ^ 2304 := by
    calc
      _ ≤ (T.S.n k) ^ 2100 * ((T.S.n k) ^ 204 + 1) :=
        Nat.mul_le_mul_right _ hTargetCount
      _ ≤ (T.S.n k) ^ 2100 * (2 * (T.S.n k) ^ 204) :=
        Nat.mul_le_mul_left _ hD204
      _ = 2 * ((T.S.n k) ^ 2100 * (T.S.n k) ^ 204) := by ring
      _ = 2 * (T.S.n k) ^ 2304 := by rw [← pow_add]
  have hTargetFactor : max 1 (targets.card * ((T.S.n k) ^ 204 + 1)) ≤
      2 * (T.S.n k) ^ 2304 := by
    exact max_le_iff.mpr ⟨by
      have hp : 1 ≤ (T.S.n k) ^ 2304 := by
        have hp' : 0 < (T.S.n k) ^ 2304 := pow_pos (by omega) 2304
        omega
      omega, hTargetProduct⟩
  have hTsMax : max 1 Ts = Ts := max_eq_right hTspos
  have hBaseNat : base ≤ (T.S.n k) ^ 2514 := by
    dsimp [base, targetWitnessBase]
    rw [hAc, hTsMax]
    calc
      4 * max 1 (targets.card * ((T.S.n k) ^ 204 + 1)) *
          ((T.S.n k) ^ 204 + 1) * Ts ≤
        4 * (2 * (T.S.n k) ^ 2304) * (2 * (T.S.n k) ^ 204) *
          (T.S.n k) ^ 2 := by gcongr
      _ = 16 * ((T.S.n k) ^ 2304 * (T.S.n k) ^ 204 * (T.S.n k) ^ 2) := by ring
      _ = 16 * (T.S.n k) ^ 2510 := by rw [← pow_add, ← pow_add]
      _ ≤ (T.S.n k) ^ 2514 := by
        have hpow : 16 ≤ (T.S.n k) ^ 4 := by
          have h := Nat.pow_le_pow_left hInput.n_two 4
          norm_num at h ⊢
          exact h
        calc
          16 * (T.S.n k) ^ 2510 ≤ (T.S.n k) ^ 4 * (T.S.n k) ^ 2510 :=
            Nat.mul_le_mul_right _ hpow
          _ = (T.S.n k) ^ 2514 := by rw [← pow_add]
  let q : ℝ := (base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))
  have hnPositive : 0 < (T.S.n k : ℝ) := by positivity
  have hBaseReal : (base : ℝ) ≤ Real.rpow (T.S.n k : ℝ) 2514 := by
    have hcast : (base : ℝ) ≤ (T.S.n k : ℝ) ^ (2514 : ℕ) := by exact_mod_cast hBaseNat
    calc
      (base : ℝ) ≤ (T.S.n k : ℝ) ^ (2514 : ℕ) := hcast
      _ = Real.rpow (T.S.n k : ℝ) 2514 := (Real.rpow_natCast _ _).symm
  have hqBound : q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := by
    have hexp : (2514 : ℝ) - κ.P ≤ -((κ.P : ℝ) + 2) / 2 := by
      have hp : 5030 ≤ κ.P := by omega
      have hpR : (5030 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) 2514 *
          Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
            dsimp [q]
            exact mul_le_mul_of_nonneg_right hBaseReal
              (Real.rpow_nonneg (by positivity) _)
      _ = Real.rpow (T.S.n k : ℝ) (2514 - κ.P) := by
        have hadd := Real.rpow_add hnPositive (2514 : ℝ) (-(κ.P : ℝ))
        have hExp : (2514 : ℝ) + -(κ.P : ℝ) = 2514 - κ.P := by ring
        simpa [hExp] using hadd.symm
      _ ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hnR hexp
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqHalf : q ≤ 1 / 2 := by
    have hexp : -((κ.P : ℝ) + 2) / 2 ≤ -1 := by
      have hp : 2 ≤ κ.P := by omega
      have hpR : (2 : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hp
      nlinarith
    calc
      q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) := hqBound
      _ ≤ Real.rpow (T.S.n k : ℝ) (-1) :=
        Real.rpow_le_rpow_of_exponent_le hnR hexp
      _ = ((T.S.n k : ℝ)⁻¹) := by
        change (T.S.n k : ℝ) ^ (-1 : ℝ) = (T.S.n k : ℝ)⁻¹
        exact Real.rpow_neg_one (T.S.n k : ℝ)
      _ ≤ 1 / 2 := by
        have hn2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hInput.n_two
        calc
          (T.S.n k : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ hnPositive (by norm_num : (0 : ℝ) < 2)).mpr hn2
          _ = 1 / 2 := by norm_num
  have hterm (m : ℕ) :
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) = q ^ m := by
    have hpow := Real.rpow_mul_natCast (by positivity : 0 ≤ (T.S.n k : ℝ))
      (-(κ.P : ℝ)) m
    have hpow' : Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
        (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by
      have hExp : (-(κ.P : ℝ)) * (m : ℝ) = -((κ.P : ℝ) * (m : ℝ)) := by ring
      simpa [hExp] using hpow
    calc
      (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) =
          (base : ℝ) ^ m * (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [hpow']
      _ = ((base : ℝ) * Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) ^ m := by rw [← mul_pow]
      _ = q ^ m := rfl
  have hhalf : Real.rpow (T.S.n k : ℝ) (-1) ≤ 1 / 2 := by
    calc
      Real.rpow (T.S.n k : ℝ) (-1) = (T.S.n k : ℝ)⁻¹ := by
        change (T.S.n k : ℝ) ^ (-1 : ℝ) = (T.S.n k : ℝ)⁻¹
        exact Real.rpow_neg_one (T.S.n k : ℝ)
      _ ≤ 1 / 2 := by
        have hn2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hInput.n_two
        calc
          (T.S.n k : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ hnPositive (by norm_num : (0 : ℝ) < 2)).mpr hn2
          _ = 1 / 2 := by norm_num
  have h2q : 2 * q ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) := by
    have hadd := Real.rpow_add hnPositive (-(κ.P : ℝ) / 2) (-1 : ℝ)
    have hfactor : Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) =
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) *
          Real.rpow (T.S.n k : ℝ) (-1) := by
      calc
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) =
            Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2 + (-1 : ℝ)) := by
              congr 1
              ring
        _ = _ := hadd
    calc
      2 * q ≤ 2 * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) + 2) / 2) :=
        mul_le_mul_of_nonneg_left hqBound (by norm_num)
      _ = 2 * (Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) *
          Real.rpow (T.S.n k : ℝ) (-1)) := by rw [hfactor]
      _ ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) := by
        have hnonneg : 0 ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) :=
          Real.rpow_nonneg (by positivity) _
        nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg]
  have hGeo := Lane_q_s17_res2.sum_geometric_tail hq0 hqHalf 1 M
  have hTotal : (∑ m ∈ Finset.range (M + 1), q ^ m) ≤ 1 + 2 * q := by
    have hSplit :
        (∑ m ∈ Finset.range (M + 1), q ^ m) =
          (∑ m ∈ (Finset.range (M + 1)).filter (fun m => 0 < m), q ^ m) +
          (∑ m ∈ (Finset.range (M + 1)).filter (fun m => ¬ 0 < m), q ^ m) := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.range (M + 1)) (fun m : ℕ => 0 < m)]
    have hpos : (∑ m ∈ (Finset.range (M + 1)).filter (fun m => 0 < m), q ^ m) ≤ 2 * q := by
      simpa [Nat.succ_le_iff] using hGeo
    have hzeroSubset : (Finset.range (M + 1)).filter (fun m => ¬ 0 < m) ⊆ {0} := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        at hm ⊢
      omega
    have hzero :
        (∑ m ∈ (Finset.range (M + 1)).filter (fun m => ¬ 0 < m), q ^ m) ≤ 1 := by
      calc
        _ ≤ ∑ m ∈ ({0} : Finset ℕ), q ^ m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hzeroSubset
          intro m hm hnot
          exact pow_nonneg hq0 m
        _ = 1 := by simp
    rw [hSplit]
    linarith
  have hOutput := Lane_q_s17_res2.E_mono P hPoint
  calc
    P.E (fun tapes => Ψ (D.targetProjection targets
        (LE.resample Ts order events pools tapes.extend))) ≤
      P.E (fun tapes => ∑ a : Enc, termAt a.1.val a.2 tapes) := hOutput
    _ = ∑ a : Enc, weightedAt a.1.val a.2 := hInterchange
    _ ≤ ∑ m ∈ Finset.range (M + 1),
          (base : ℝ) ^ m * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m)) *
            (D.freshTargetLaw targets pools).E Ψ := hGrouped
    _ = (∑ m ∈ Finset.range (M + 1), q ^ m) *
          (D.freshTargetLaw targets pools).E Ψ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro m hm
            rw [hterm m]
    _ ≤ (1 + 2 * q) * (D.freshTargetLaw targets pools).E Ψ :=
      mul_le_mul_of_nonneg_right hTotal hFreshNonneg
    _ ≤ (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
          (D.freshTargetLaw targets pools).E Ψ := by
            exact mul_le_mul_of_nonneg_right (by linarith) hFreshNonneg

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
