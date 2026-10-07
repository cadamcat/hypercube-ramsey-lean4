import HypercubeRamsey.S18.Defs
import HypercubeRamsey.S18.Nodes_q_s18_n6
import HypercubeRamsey.S18.Nodes_q_s18_n6_g

/-! Repaired Section 18 skeleton. Leaf estimates remain proof-lane work;
all assemblies below use their stated outputs without new placeholders. -/
namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators

/-- D18.L, §§16–17 and 18:43–87. Construct actual initial data, not arbitrary
lists. The selected discrepancy budgets are forwarded from C12.K. The input
geometry now includes the prescribed cell slot count; the output calibration
uses a 50ρh consultation-centre margin. The general calibration and upstream
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
  sorry

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
  sorry

/-- P18.3c, 18:715–737. Forced replay advances overlapping scopes once. -/
theorem P18_3c {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : LateData hPT) : ReplayFacts D := by
  sorry

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
  sorry

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
  refine ⟨η, hη, hη1, hslack, ?_⟩
  filter_upwards [] with k
  intro PT hPT D hD δ hPair palette p hp
  have hExponentBound (S : Finset (Pos T k)) :
      0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card + Cprime * p * D.rank S ≤
        (0.02 + Cprime * η) * (T.S.n k : ℝ) * D.rank S :=
    HypercubeRamsey.Lane_q_s18_n6.overlapMoment_exponent_bound
      D δ K Cprime η hPair hCp.le p hp S
  by_cases hp0 : p = 0
  · subst p
    rw [Finset.powersetCard_zero]
    simp [LateData.nonisolates, LateData.rank]
  · by_cases hp1 : p = 1
    · subst p
      let U : Finset (Pos T k) := D.paletteRows palette
      have hpow : 0 < (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hcardReal : 0 < (U.card : ℝ) := by
        dsimp [U]
        exact lt_of_lt_of_le hpow (hPair.2.1 palette)
      have hcard : 0 < U.card := by exact_mod_cast hcardReal
      have hnum :
          (∑ S ∈ U.powersetCard 1,
            Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card +
              Cprime * 1 * D.rank S)) = U.card := by
        rw [Finset.powersetCard_one, Finset.sum_map]
        change
          (∑ v ∈ U,
            Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates ({v} : Finset (Pos T k))).card +
              Cprime * 1 * D.rank {v})) = (U.card : ℝ)
        simp_rw [HypercubeRamsey.Lane_q_s18_n6.singleton_overlap_exponent_zero]
        simp
      have hden : (U.powersetCard 1).card = U.card := by simp
      dsimp [U] at hnum hden ⊢
      simp only [Nat.cast_one] at hnum hden ⊢
      rw [hnum, hden]
      have hcardNe : (U.card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
      rw [div_self hcardNe]
      norm_num
    · sorry

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
