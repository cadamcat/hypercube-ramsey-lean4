import HypercubeRamsey.S17.Defs

/-!
# Section 17 proof nodes

The estimate nodes are intentionally separated along the proof dependencies
in PART-C.md: pinned list mass and support, pool compatibility and trials,
palette code and retention/pair bounds, then the four finite-resampling
witness and terminal-entry steps.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

/-- Large-index assumptions used to read the Section 12--16 asymptotic
contracts at one fixed stage index. -/
def S17Large (κ : CConsts) (T : Stage) (k : ℕ) : Prop :=
  2 ≤ T.S.n k ∧ κ.Q0 ≤ Real.log (T.S.n k : ℝ)

/-- The source facts from Sections 12 and 15 used in the pinned-list
estimate. -/
def S17SourceFacts (κ : CConsts) (T : Stage) : Prop :=
  InitDisc T κ.η0 ∧
    (∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)

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

/-- L17.1a: the initial row mass is below one half only with this small
probability. -/
theorem independentPinnedMassFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hN : 0 < T.S.N k)
    (hSource : S17SourceFacts κ T) (hQuant : D.L16QuantitativeValidity)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k))
    (hInput : D.PinnedPriorInput v σ pins fixed)
    (hPriorSubprob : ∑ x, σ x ≤ 1) :
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateMassFailure v σ (D.labelsOfPinnedSample v hN ys)) ≤
      (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  sorry

/-- L17.1b: the support left after every allowed omission is exponentially
large only with this small probability. -/
theorem independentPinnedSupportFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hN : 0 < T.S.N k)
    (hSource : S17SourceFacts κ T) (hQuant : D.L16QuantitativeValidity)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k))
    (hInput : D.PinnedPriorInput v σ pins fixed) :
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateSupportFailure v (D.labelsOfPinnedSample v hN ys)) ≤
      (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  sorry

/-- L17.1: the independent pinned-label list estimate, assembled from the
retained-mass and omitted-support bounds. -/
theorem independentPinnedList
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hN : 0 < T.S.N k)
    (hSource : S17SourceFacts κ T) (hQuant : D.L16QuantitativeValidity) :
    D.PinnedListEstimateAt hN := by
  intro v σ pins fixed hInput
  have hPriorSubprob := D.validInitialPriorSubprob v σ hInput.2.1
  have hm := independentPinnedMassFailure κ hκ T k PT D hLarge hN hSource hQuant
    v σ pins fixed hInput hPriorSubprob
  have hs := independentPinnedSupportFailure κ hκ T k PT D hLarge hN hSource hQuant
    v σ pins fixed hInput
  have hu := FinLaw.pr_or_le (D.pinnedLabelLaw v pins fixed)
    (fun ys => D.gateMassFailure v σ (D.labelsOfPinnedSample v hN ys))
    (fun ys => D.gateSupportFailure v (D.labelsOfPinnedSample v hN ys))
  change (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateMassFailure v σ (D.labelsOfPinnedSample v hN ys) ∨
        D.gateSupportFailure v (D.labelsOfPinnedSample v hN ys)) ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) +
        (1 / 2 : ℝ) * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
          exact hu.trans (add_le_add hm hs)
    _ = Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by ring

/-- L17.2a: compatibility failures on locally typical pools are rare enough
for the resampling horizon, also under one prescribed global slot pin. -/
theorem poolCompatibilityFailure
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (v : Pos T k) (μ : FinLaw (ListGateContext.PoolAssignment D))
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) :
    μ.pr (D.compatibilityFailure v) ≤
      Real.rpow (T.S.n k : ℝ)
        (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ))) := by
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

/-- L17.2b: overlap-rank summation bounds the repeated-trial moment. -/
theorem uniformPoolTrialsMoment
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hN : 0 < T.S.N k)
    (hSource : S17SourceFacts κ T) (hQuant : D.L16QuantitativeValidity)
    (hList : D.PinnedListEstimateAt hN) (v : Pos T k)
    (μ : FinLaw (ListGateContext.PoolAssignment D))
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) :
    poolTrialMoment D v μ ≤ 2 * Real.rpow (T.S.n k : ℝ)
      (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ))) := by
  sorry

/-- L17.2c: Markov's inequality turns the trial moment and auxiliary pool
bounds into the eq:source-23 exception estimate. -/
theorem uniformPoolMarkov
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (v : Pos T k) (μ : FinLaw (ListGateContext.PoolAssignment D))
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ)
    (hCompat : μ.pr (D.compatibilityFailure v) ≤
      Real.rpow (T.S.n k : ℝ)
        (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ))))
    (hMoment : poolTrialMoment D v μ ≤ 2 * Real.rpow (T.S.n k : ℝ)
      (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ))))
    (hTypical : μ.pr (fun pools => ¬ D.LocalPoolsTypical v pools) ≤
      Real.rpow (T.S.n k : ℝ)
        (-((κ.R : ℝ) * (initialResamplingRounds T k : ℝ)))) :
    D.UniformPoolEstimateAt v μ := by
  sorry

/-- L17.2: the uniform pool estimate, including the conditioned version for
one prescribed slot-to-bin pin. -/
theorem uniformPoolListEstimate
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hN : 0 < T.S.N k)
    (hSource : S17SourceFacts κ T) (hQuant : D.L16QuantitativeValidity)
    (hList : D.PinnedListEstimateAt hN) (v : Pos T k)
    (μ : FinLaw (ListGateContext.PoolAssignment D))
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) :
    D.UniformPoolEstimateAt v μ := by
  apply uniformPoolMarkov κ hκ T k PT D hLarge hQuant v μ hμ
  · exact poolCompatibilityFailure κ hκ T k PT D hLarge hQuant v μ hμ
  · exact uniformPoolTrialsMoment κ hκ T k PT D hLarge hN hSource hQuant hList v μ hμ
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
    (∀ C, D.F.typical C (pools C) → D.stateValid C (pools C) (s C)) →
    v ∈ PT.tiling.leaf i → IsEvenRole v →
    (1 / 2 : ℝ) ≤ D.rowMass v (D.prior s v) (D.label s) →
      1 / (4 * (s17Chi ψ : ℝ)) ≤
      ∑ x ∈ s17Palette ψ colours v, D.row v (D.prior s v) (D.label s) x) ∧
  (∀ v : Pos T k, v ∈ PT.tiling.leaf i → IsEvenRole v →
    ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
    ∑ x ∈ s17Palette ψ colours v, σ x ≤ 2 / (s17Chi ψ : ℝ))

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
    (colours : S17PaletteAssignment ψ) : Prop :=
  ∀ v : Pos T k, v ∈ PT.tiling.leaf i → IsEvenRole v →
    ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
      ∀ x ∈ (PT.tiling.P i).X,
        ∑ z ∈ s17Palette ψ colours v,
          (if |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
            σ z * ∏ w ∈ D.externalEarly v,
              externalPairFactor (D.G.patchOf w) x z
           else 0) ≤ κ.KB / (s17Chi ψ : ℝ)

/-- L17.3(iv): the unconditioned uniform pair moment on the patch support. -/
def PalettePairMomentBound
    (i : Fin PT.tiling.m)
    (hX : (PT.tiling.P i).X.Nonempty) : Prop :=
  ∀ d : ℕ, d ≤ T.S.n k →
    (FinLaw.pi fun _ : Fin 2 => FinLaw.uniform (PT.tiling.P i).X hX).E
      (fun ω => if |corr (T.S.E k) PT.tiling.c (PT.π i).w (ω 0) (ω 1)| ≤ κ.ξ then
        (4 * (∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c (ω 0) y *
          hit (T.S.E k) PT.tiling.c (ω 1) y)) ^ (2 * d)
       else 0) ≤ Real.exp (κ.KB * Real.log (T.S.n k : ℝ))

/-- L17.3(i): an X-Varshamov linear code separates internal words up to the
stated radius. -/
theorem lowModePaletteCode
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (_hfree : ∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
      j.val < T.S.n k - (PT.tiling.P i).h) :
    ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ := by
  sorry

/-- L17.3(ii): one colouring of the label support works for every valid
local history and internal prior. -/
theorem lowModePaletteRetention
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle) (hCode : PaletteCodeSpec i hle ψ) :
    ∃ colours : S17PaletteAssignment ψ, PaletteRetentionSpec D i hle ψ colours := by
  sorry

/-- L17.3(iii): all valid priors satisfy the palette pair-tail bound. -/
theorem lowModePalettePairRow
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (ψ : S17PaletteCode i hle) (hCode : PaletteCodeSpec i hle ψ)
    (colours : S17PaletteAssignment ψ)
    (hRetention : PaletteRetentionSpec D i hle ψ colours) :
    PalettePairRowBound D i hle ψ colours := by
  sorry

/-- L17.3(iv): the uniform pair integral has a polylogarithmic exponential
bound for every moment order through the ambient dimension. -/
theorem lowModePalettePairMoment
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (i : Fin PT.tiling.m) (hX : (PT.tiling.P i).X.Nonempty) :
    PalettePairMomentBound i hX := by
  sorry

/-- L17.3 export: code, fixed palette retention, row-pair estimate, and
unconditioned second moment assembled from their component nodes. -/
theorem lowModePalettes
    (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k) (hQuant : D.L16QuantitativeValidity)
    (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (hfree : ∃ j : Fin (T.S.n k), (PT.tiling.P i).ℓ ≤ j.val ∧
      j.val < T.S.n k - (PT.tiling.P i).h) :
    ∃ ψ : S17PaletteCode i hle, PaletteCodeSpec i hle ψ ∧
      ∃ colours : S17PaletteAssignment ψ,
        PaletteRetentionSpec D i hle ψ colours ∧
        PalettePairRowBound D i hle ψ colours ∧
          PalettePairMomentBound i (D.patchXNonempty i) := by
  obtain ⟨ψ, hCode⟩ := lowModePaletteCode κ hκ T k PT D hLarge hQuant i hle hfree
  obtain ⟨colours, hRetention⟩ :=
    lowModePaletteRetention κ hκ T k PT D hLarge hQuant i hle ψ hCode
  have hPair := lowModePalettePairRow κ hκ T k PT D hLarge hQuant i hle
    ψ hCode colours hRetention
  have hMoment := lowModePalettePairMoment κ hκ T k PT D hLarge hQuant i
    (D.patchXNonempty i)
  exact ⟨ψ, hCode, colours, hRetention, hPair, hMoment⟩

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
    earlier.2.val < later.2.val ∧ LE.Adjacent later.1 earlier.1

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

/-- Candidate witness list used in P17.4b. The final round index `Ts` is a
sentinel for an added ever-true site whose input is still at index zero. -/
def CandidateWitness
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (Ts : ℕ) (events : Finset (Pos T k)) (root : Pos T k) (m : ℕ)
    (W : Fin m → Pos T k × Fin (Ts + 1)) : Prop :=
  (∃ hm : 0 < m, W ⟨0, hm⟩ = (root, ⟨Ts, by omega⟩)) ∧
    (∀ j, (W j).1 ∈ events) ∧
    (∀ j, j.val = 0 ∨ ∃ i : Fin m, i.val < j.val ∧
      (W j).1 ∈ LE.graphBall { (W i).1 } 3)

/-- Number of earlier listed executions touching one cell before a witness
test. -/
noncomputable def witnessReadIndex
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (W : Fin m → Pos T k × Fin (Ts + 1)) (j : Fin m) (C : D.G.Cell) : ℕ :=
  (Finset.univ.filter fun i : Fin m =>
    i.val < j.val ∧ (W i).2.val < Ts ∧
      (W i).2.val < (W j).2.val ∧ C ∈ LE.scope (W i).1).card

/-- Configuration read by a candidate truth test. -/
noncomputable def witnessTestConfig
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : Tapes D.F Ts) (W : Fin m → Pos T k × Fin (Ts + 1))
    (j : Fin m) : Config D.F :=
  fun C => tapes.extend C (witnessReadIndex LE Ts W j C) (pools C)

/-- Pairwise disjoint tape entries read by the truth tests in one witness.
When two tests' event scopes overlap, their prescribed tape indices differ. -/
def WitnessReadsDisjoint
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (W : Fin m → Pos T k × Fin (Ts + 1)) : Prop :=
  ∀ i j, i ≠ j → ¬ Disjoint (LE.scope (W i).1) (LE.scope (W j).1) →
    ∀ C, C ∈ LE.scope (W i).1 → C ∈ LE.scope (W j).1 →
      witnessReadIndex LE Ts W i C ≠ witnessReadIndex LE Ts W j C

/-- All prescribed truth tests in a witness list pass. -/
def WitnessTestsPass
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ) {m : ℕ}
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : Tapes D.F Ts) (W : Fin m → Pos T k × Fin (Ts + 1)) : Prop :=
  ∀ j, LE.S (W j).1 (witnessTestConfig LE Ts pools tapes W j)

/-- Final target law comparison and rare-event bounds, P17.4(i)--(iii). -/
def FiniteResamplingConclusion
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
    (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (targets : Finset D.G.Cell)
    (v : Pos T k) : Prop :=
  (tapeLaw D.F Ts).pr
    (fun tapes => LE.S v (LE.resample Ts order events pools tapes.extend)) ≤
      Real.rpow (T.S.n k : ℝ)
        (-((κ.P : ℝ) * (Ts : ℝ) / 2)) ∧
  (tapeLaw D.F Ts).pr
    (fun tapes => (backwardClosure LE order events pools tapes targets).card > Ts) ≤
      Real.rpow (T.S.n k : ℝ)
        (-((κ.P : ℝ) * (Ts : ℝ) / 2)) ∧
  (∀ Ψ, (∀ s, 0 ≤ Ψ s) →
    (tapeLaw D.F Ts).E (fun tapes => Ψ
      (D.targetProjection targets (LE.resample Ts order events pools tapes.extend))) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
        (D.freshTargetLaw targets pools).E Ψ)

/-- D17.R-loc: bounded round influence gives locality of cell states and event
truth in restricted simulations. -/
theorem resampleLocality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    LE.CellLocalitySpec Ts order pools tapes ∧
      LE.EventTruthLocalitySpec Ts order pools tapes := by
  sorry

/-- P17.4a: if the defining event survives the fixed-priority process, its
ever-true component contains an executing site at every round start. -/
theorem finiteResamplingComponent
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C) (tapes : Tapes D.F Ts)
    (v : Pos T k) (_hroot : v ∈ events)
    (hfinal : LE.S v (LE.resample Ts order events pools tapes.extend)) :
    (∀ r : Fin Ts, ∃ u, u ∈ events ∧ LE.S u
      (LE.runRounds r.val order events pools tapes.extend).1 ∧
      u ∈ LE.active order events (LE.runRounds r.val order events pools tapes.extend).1 ∧
      Relation.ReflTransGen (fun a b => LE.Adjacent a b ∧
        (∃ t : Fin (Ts + 1), LE.S a (LE.runRounds t.val order events pools tapes.extend).1) ∧
        (∃ t : Fin (Ts + 1), LE.S b (LE.runRounds t.val order events pools tapes.extend).1)) v u) ∧
    (∃ m, Ts ≤ m ∧ ∃ W : Fin m → Pos T k × Fin (Ts + 1),
      CandidateWitness LE Ts events v m W ∧ WitnessReadsDisjoint LE Ts W ∧
        WitnessTestsPass LE Ts pools tapes W) := by
  sorry

/-- P17.4b: witness-list enumeration for a scope graph with the Section 17
polynomial degree bound. -/
theorem finiteResamplingWitnessCount
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (events : Finset (Pos T k)) (root : Pos T k)
    (hLarge : S17Large κ T k)
    (hdegree : ∀ v, (Finset.univ.filter fun w => LE.Adjacent v w).card ≤
      (T.S.n k) ^ (κ.Ac + 4)) :
    ∀ m : ℕ, 0 < m →
      (Finset.univ.filter fun W : Fin m → Pos T k × Fin (Ts + 1) =>
        CandidateWitness LE Ts events root m W).card ≤
        ((T.S.n k) ^ (3 * (κ.Ac + 4)) * (Ts + 1)) ^ m := by
  sorry

/-- P17.4c: the event tests in a witness list read disjoint tape entries, so
all `m` required truth tests cost at most `n^{-Pm}`. -/
theorem finiteResamplingWitnessTests
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (hLarge : S17Large κ T k)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (h23 : ∀ w ∈ events,
      (D.freshConfigLaw pools).pr (LE.S w) ≤
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))) :
    ∀ m (root : Pos T k) (W : Fin m → Pos T k × Fin (Ts + 1)),
      CandidateWitness LE Ts events root m W →
      WitnessReadsDisjoint LE Ts W →
      (tapeLaw D.F Ts).pr (fun tapes => WitnessTestsPass LE Ts pools tapes W) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * (m : ℝ))) := by
  sorry

/-- P17.4d: backward closure counting and separation of consumed truth-test
entries from terminal target entries. -/
theorem finiteResamplingTerminalComparison
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (LE : ListEvent D.F)
    (Ts : ℕ) (hLarge : S17Large κ T k)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (hPools : ∀ C, D.F.typical C (pools C))
    (h23 : ∀ w ∈ events,
      (D.freshConfigLaw pools).pr (LE.S w) ≤
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)))
    (targets : Finset D.G.Cell)
    (htarget : targets.card ≤ (T.S.n k) ^ (10 * (κ.Ac + 10)))
    (v : Pos T k) (hroot : v ∈ events)
    (hComponent : ∀ tapes : Tapes D.F Ts,
      LE.S v (LE.resample Ts order events pools tapes.extend) →
      ∃ m, Ts ≤ m ∧ ∃ W : Fin m → Pos T k × Fin (Ts + 1),
        CandidateWitness LE Ts events v m W ∧ WitnessReadsDisjoint LE Ts W ∧
          WitnessTestsPass LE Ts pools tapes W)
    (hCount : ∀ m : ℕ, 0 < m →
      (Finset.univ.filter fun W : Fin m → Pos T k × Fin (Ts + 1) =>
        CandidateWitness LE Ts events v m W).card ≤
        ((T.S.n k) ^ (3 * (κ.Ac + 4)) * (Ts + 1)) ^ m)
    (hTests : ∀ m (W : Fin m → Pos T k × Fin (Ts + 1)),
      CandidateWitness LE Ts events v m W → WitnessReadsDisjoint LE Ts W →
      (tapeLaw D.F Ts).pr (fun tapes => WitnessTestsPass LE Ts pools tapes W) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * (m : ℝ)))) :
    FiniteResamplingConclusion D LE Ts order events pools targets v := by
  sorry

/-- P17.4: finite resampling failure, backward-closure tail, and the
multiplicative terminal-state comparison. The export consumes all four
witness/count/test/terminal nodes. -/
theorem finiteResamplingComparison
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT)
    (hLarge : S17Large κ T k)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (hPools : ∀ C, D.F.typical C (pools C))
    (h23 : ∀ w ∈ events,
      D.freshEventProbability w pools ≤
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)))
    (targets : Finset D.G.Cell)
    (htarget : targets.card ≤ (T.S.n k) ^ (10 * (κ.Ac + 10)))
    (v : Pos T k) (hroot : v ∈ events)
    (hdegree : ∀ w,
      (Finset.univ.filter fun z => D.asListEvent.Adjacent w z).card ≤
      (T.S.n k) ^ (κ.Ac + 4)) :
    FiniteResamplingConclusion D D.asListEvent (initialResamplingRounds T k)
      order events pools targets v := by
  let Ts := initialResamplingRounds T k
  let LE := D.asListEvent
  have h23LE : ∀ w ∈ events,
      (D.freshConfigLaw pools).pr (LE.S w) ≤
        Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
    intro w hw
    change (D.freshConfigLaw pools).pr (D.event w) ≤ _
    exact h23 w hw
  have hComponent : ∀ tapes : Tapes D.F Ts,
      LE.S v (LE.resample Ts order events pools tapes.extend) →
        ∃ m, Ts ≤ m ∧ ∃ W : Fin m → Pos T k × Fin (Ts + 1),
          CandidateWitness LE Ts events v m W ∧ WitnessReadsDisjoint LE Ts W ∧
            WitnessTestsPass LE Ts pools tapes W := by
    intro tapes hfinal
    exact (finiteResamplingComponent LE Ts order events pools tapes v hroot hfinal).2
  have hCount := finiteResamplingWitnessCount LE Ts events v hLarge hdegree
  have hTests := finiteResamplingWitnessTests LE Ts hLarge order events pools h23LE
  have hTestsRoot := fun m W hW hDis => hTests m v W hW hDis
  exact finiteResamplingTerminalComparison D LE Ts hLarge order events pools hPools h23LE
    targets htarget v hroot hComponent hCount hTestsRoot

end HypercubeRamsey
