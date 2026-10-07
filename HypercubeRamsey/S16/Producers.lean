import HypercubeRamsey.S16.Comparisons
import HypercubeRamsey.S16.Producers_q_s16_prod2

/-! Construction contracts connecting the conditional Section 16 estimates
to physical cells. These nodes are separate proof obligations: none assumes
an avoidance certificate, calibrated marginal, or fresh comparison bound. -/

namespace HypercubeRamsey.S16
namespace Lane_sol_fix2_s16

open Classical
open scoped BigOperators

abbrev EvenCellRole {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) :=
  {v : Pos T k // G.cellOf v = C ∧ IsEvenRole v}

/-- T14:75 and T16:415–417 use uniform-subset in-bin laws. D14.S currently
records only their support size, so this missing upstream input is explicit. -/
def SolverLabelsUniform {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop :=
  PT.tiling.mode.isCluster → ∀ i (S : SliceSolver κ PT.tiling i PT.mesh), PT.solver i = some S →
    ∀ g W D, 0 < S.q g W D → ∃ support : Finset (Fin (T.S.N k)),
      ∃ hs : support.Nonempty, ∀ y, S.U g W D y = (FinLaw.uniform support hs).w y

/-- Fixed Q0 room used in T16:338–342 and 400–427. Low scales need not
grow with n, so an eventual dimension cutoff cannot supply this input.
The current QCond records h ≤ d^.01, which alone does not bound h². -/
structure CellCalibrationScale {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop where
  room : PT.tiling.mode.isCluster → ∀ i,
    κ.d0 ≤ (PT.tiling.P i).d ∧
    (10 ^ 100 : ℕ) ≤ (PT.tiling.P i).d ∧
    4 * Real.exp (1.5 * (sliceK κ (PT.tiling.P i).h : ℝ) * sliceT κ (PT.tiling.P i).h) ≤
      Real.rpow ((PT.tiling.P i).d : ℝ) 0.05 ∧
    2 * ((PT.tiling.P i).h : ℝ) ^ 2 ≤ Real.rpow ((PT.tiling.P i).d : ℝ) 0.01 ∧
    ((PT.tiling.P i).h + 1 : ℝ) ≤ Real.rpow ((PT.tiling.P i).d : ℝ) 0.025 ∧
    16 * ((PT.tiling.P i).d : ℝ) ^ 2 * ((PT.tiling.P i).h + 1 : ℝ) ^ 2 *
      Real.rpow (sliceEps κ (PT.tiling.P i).h) (1 / 16 : ℝ) ≤
        Real.rpow ((PT.tiling.P i).d : ℝ) (-20)

/-- Raw data only. Slice laws are unrestricted; each slice is conditioned
separately. Pool restrictions and calibrated samplers are not fields. -/
structure CellRawData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) where
  Slice : G.Cell → Type
  [sliceFin : ∀ C, Fintype (Slice C)]
  [sliceDec : ∀ C, DecidableEq (Slice C)]
  Value : ∀ C, Slice C → Type
  [valueFin : ∀ C s, Fintype (Value C s)]
  [valueDec : ∀ C s, DecidableEq (Value C s)]
  sliceLaw : ∀ C s, FinLaw (Value C s)
  slicePass : ∀ C s, Finset (Value C s)
  slice_pos : ∀ C s, 0 < ∑ W ∈ slicePass C s, (sliceLaw C s).w W
  Group : G.Cell → Type
  [groupFin : ∀ C, Fintype (Group C)]
  [groupDec : ∀ C, DecidableEq (Group C)]
  groupOf : ∀ C, OddCellRole G C → Group C
  cellWords : ∀ C, (Slice C × IWord PT.tiling (G.cellPatch C)) ≃
    {v : Pos T k // G.cellOf v = C}
  axis : ∀ C, Fin (PT.tiling.P (G.cellPatch C)).h → Fin (T.S.n k)
  axis_injective : ∀ C, Function.Injective (axis C)
  axes_eq : ∀ C, Finset.univ.image (axis C) = PT.tiling.Icoord (G.cellPatch C)
  word_parity : PT.tiling.mode.isCluster → ∀ C s z,
    IsEvenRole (cellWords C (s, z)).1 ↔ IsEvenRole z
  word_flip : ∀ C s z j,
    (cellWords C (s, flipPos z j)).1 = flipPos (cellWords C (s, z)).1 (axis C j)
  word_outer : ∀ C s z z' j, j ∉ PT.tiling.Icoord (G.cellPatch C) →
    (cellWords C (s, z)).1 j = (cellWords C (s, z')).1 j
  qraw : ∀ C, (∀ s, Value C s) → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  pretrim : ∀ C, (∀ s, Value C s) → Group C → Finset (Bin PT.tiling (G.cellPatch C))
  qin : ∀ C, (∀ s, Value C s) → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qin_eq : ∀ C W g D, (∀ s, W s ∈ slicePass C s ∧ (sliceLaw C s).w (W s) ≠ 0) →
    (qin C W g).w D = (if D ∈ pretrim C W g then (qraw C W g).w D else 0) /
      (∑ D' ∈ pretrim C W g, (qraw C W g).w D')
  U : ∀ C, (∀ s, Value C s) → Group C → Bin PT.tiling (G.cellPatch C) →
    FinLaw (Fin (T.S.N k))
  U_support : ∀ C W g D y, (U C W g D).w y ≠ 0 → y ∈ D.1
  rawPrior : ∀ C, (∀ s, Value C s) → (OddCellRole G C → Fin (T.S.N k)) →
    Pos T k → Fin (T.S.N k) → ℝ
  prior_nonneg : ∀ C W ys v y, 0 ≤ rawPrior C W ys v y
  prior_subprob : ∀ C W ys v, ∑ y, rawPrior C W ys v y ≤ 1

namespace CellRawData
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
instance instSliceFintype (R : CellRawData G) : ∀ C, Fintype (R.Slice C) := R.sliceFin
instance instSliceDecidableEq (R : CellRawData G) : ∀ C, DecidableEq (R.Slice C) := R.sliceDec
instance instValueFintype (R : CellRawData G) : ∀ C s, Fintype (R.Value C s) := R.valueFin
instance instValueDecidableEq (R : CellRawData G) : ∀ C s, DecidableEq (R.Value C s) := R.valueDec
instance instGroupFintype (R : CellRawData G) : ∀ C, Fintype (R.Group C) := R.groupFin
instance instGroupDecidableEq (R : CellRawData G) : ∀ C, DecidableEq (R.Group C) := R.groupDec
abbrev Hist (R : CellRawData G) (C : G.Cell) := ∀ s, R.Value C s
noncomputable def rawHistory (R : CellRawData G) (C : G.Cell) := FinLaw.pi (R.sliceLaw C)
noncomputable def history (R : CellRawData G) (C : G.Cell) :=
  FinLaw.pi fun s => FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s)

noncomputable def wordLabel (R : CellRawData G) (C : G.Cell)
    (ys : OddCellRole G C → Fin (T.S.N k)) (s : R.Slice C)
    (fallback : Fin (T.S.N k)) (z : IWord PT.tiling (G.cellPatch C)) :=
  if hz : ¬ IsEvenRole (R.cellWords C (s, z)).1 then
    ys ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ else fallback

/-- Exact links to D14.S, including its raw posterior, and to the direct
cleaned prior. The equivalences prevent an arbitrary prior experiment. -/
def SourceValid (R : CellRawData G) : Prop :=
  (PT.tiling.mode = .lowCluster ∧ SolverLabelsUniform PT ∧ ∀ C,
    ∃ S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh,
      PT.solver (G.cellPatch C) = some S ∧
      ∃ records : ∀ s, R.Value C s ≃ (∀ r, S.Val r),
      ∃ groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C,
        (∀ s, R.sliceLaw C s = FinLaw.map (S.recLaw PT.parameter) (records s).symm) ∧
        (∀ s W, W ∈ R.slicePass C s ↔ S.AllGood (records s W)) ∧
        (∀ s z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
          R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
            groups (s, S.groupOf z)) ∧
        (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) ∧
        (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) ∧
        (∀ W s g D y, (R.U C W (groups (s, g)) D).w y = S.U g (records s (W s)) D y) ∧
        (∀ W s (w : EvenRole PT.tiling (G.cellPatch C)) ys fallback,
          R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
            S.σ w (records s (W s)) (nbrLabels w.1 (R.wordLabel C ys s fallback)))) ∨
  (¬ PT.tiling.mode.isCluster ∧ ∀ C,
    Function.Injective (R.groupOf C) ∧
    (∀ s, Nonempty (R.Value C s ≃ Unit)) ∧
    (∀ s, R.slicePass C s = Finset.univ) ∧
    (∀ W g D, (R.qraw C W g).w D = 1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ)) ∧
    (∀ W g, R.pretrim C W g = Finset.univ) ∧
    (∀ W g D y, (R.U C W g D).w y = if y ∈ D.1 then 1 else 0) ∧
    ∃ h : (PT.envelope (G.cellPatch C)).Nonempty,
      ∀ W ys v, G.cellOf v = C → IsEvenRole v →
        R.rawPrior C W ys v = (Law.unifCore (PT.envelope (G.cellPatch C)) h).w)

noncomputable def rawLaw (R : CellRawData G) (C : G.Cell) (W : R.Hist C) :=
  FinLaw.bind (FinLaw.pi (R.qraw C W)) fun a =>
    FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
noncomputable def baseExperiment (R : CellRawData G) (C : G.Cell) (v : Pos T k) :
    PriorExperiment (T.S.N k) where
  State := R.Hist C × ((R.Group C → Bin PT.tiling (G.cellPatch C)) ×
    (OddCellRole G C → Fin (T.S.N k)))
  law := FinLaw.bind (R.rawHistory C) (R.rawLaw C)
  prior := fun ω => R.rawPrior C ω.1 ω.2.2 v
end CellRawData

/-- T16:167–177,259–288. A physical-kernel producer, before any estimates. -/
theorem cell_raw_data_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q),
      SolverLabelsUniform PT → n₀ ≤ T.S.n k →
      ∃ R : CellRawData H.geom, R.SourceValid := by
  sorry

/-- The permission table uses unrestricted priors at the actual external
neighbor, including neighbors in other cells. No fresh prior is substituted. -/
structure CellPermissions {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G) where
  table : ∀ C, PermissionTable (R.Group C) (Bin PT.tiling (G.cellPatch C))
    (Fin (T.S.N k)) (OddCellRole G C × Fin (T.S.n k))
  n_eq : ∀ C, (table C).n = T.S.n k
  rate_eq : ∀ C, (table C).cperm = κ.cperm
  labels_eq : ∀ C D, (table C).labels D = D.1
  group_eq : ∀ C inc, (table C).groupOf inc = R.groupOf C inc.1
  bad_eq : ∀ C inc y, (table C).badMass inc y =
    if inc.2 ∉ PT.tiling.Icoord (G.cellPatch C) ∧ G.classOf inc.1.1 = none then
      (R.baseExperiment (G.cellOf (flipPos inc.1.1 inc.2)) (flipPos inc.1.1 inc.2)).expect
        (fun σ => if σ ≠ 0 ∧ |∑ x, σ x * hit (T.S.E k) PT.tiling.c x y - 1 / 2| >
          2 * bstar T k then 1 else 0)
    else 0

/-- S1 producer: retain the solver cap and its pretrim denominator, then
absorb their subexponential inflation at one uniform cutoff (T16:147–156). -/
theorem cell_permission_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage}, DeepDisc T κ.xs κ.α 0.04 →
      ∀ {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → n₀ ≤ T.S.n k →
      ∃ Perm : CellPermissions R, ∀ C W, (R.history C).w W ≠ 0 →
        PermissionLossHypotheses (Perm.table C) (R.qin C W) := by
  sorry

/-- A pool restriction of the actual incoming and permission kernels.
The fallback row handles zero denominators, as in T16:176. -/
structure CellRestrictedKernels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) where
  qbar : ∀ C, R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qtilde : ∀ C, CellPool G C → R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qbar_eq : ∀ C W g D, (R.history C).w W ≠ 0 →
    (qbar C W g).w D = (if D ∈ (Perm.table C).permitted g then (R.qin C W g).w D else 0) /
      (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D')
  qtilde_eq : ∀ C pool W g D, (R.history C).w W ≠ 0 →
    (∑ D' ∈ Finset.univ.image pool, (qbar C W g).w D') ≠ 0 →
    (qtilde C pool W g).w D =
      (if D ∈ Finset.univ.image pool then (qbar C W g).w D else 0) /
        (∑ D' ∈ Finset.univ.image pool, (qbar C W g).w D')

namespace CellRestrictedKernels
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
variable {R : CellRawData G} {Perm : CellPermissions R}
noncomputable def participants (_K : CellRestrictedKernels R Perm) (C : G.Cell)
    (v : EvenCellRole G C) : Finset (OddCellRole G C) :=
  Finset.univ.filter fun r => ∃ j ∈ PT.tiling.Icoord (G.cellPatch C), r.1 = flipPos v.1 j
noncomputable def labelLaw (_K : CellRestrictedKernels R Perm) (C : G.Cell) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :=
  FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
noncomputable def failure (K : CellRestrictedKernels R Perm) (C : G.Cell) (W : R.Hist C)
    (v : EvenCellRole G C) (a : R.Group C → Bin PT.tiling (G.cellPatch C)) : ℝ :=
  if PT.tiling.mode.isCluster then (K.labelLaw C W a).pr (fun ys => R.rawPrior C W ys v.1 = 0) else 0
noncomputable def binProblem (K : CellRestrictedKernels R Perm) (C : G.Cell)
    (pool : CellPool G C) (W : R.Hist C) :
    GroupBinProblem (R.Group C) (Bin PT.tiling (G.cellPatch C)) (EvenCellRole G C) (Fin (T.S.N k)) where
  target := K.qtilde C pool W
  participants := fun v => (K.participants C v).image (R.groupOf C)
  failureMass := K.failure C W
  contribution := fun g D y => ∑ r : OddCellRole G C,
    if R.groupOf C r = g then (R.U C W g D).w y else 0
  d := (PT.tiling.P (G.cellPatch C)).d
  ε := sliceEps κ (PT.tiling.P (G.cellPatch C)).h
end CellRestrictedKernels

/-- Diagnostic identities use sums over pool images, actual independent
role failures, their group-bin pins, and the actual label load. Probe maps
allow the finite check family to index groups, stars, and all positive pins. -/
structure CellDiagnosticLink {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell)
    {Check : Type} [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
      (R.Hist C) Check (T.S.n k) c0) where
  groupProbe : R.Group C → D.Group
  starProbe : EvenCellRole G C → D.Group
  pinProbe : EvenCellRole G C → R.Group C → Bin PT.tiling (G.cellPatch C) → D.Group
  epsilon_eq : D.ε = sliceEps κ (PT.tiling.P (G.cellPatch C)).h
  normalizer_eq : ∀ pool W g, (R.history C).w W ≠ 0 →
    D.poolNormalizer pool (groupProbe g) W = ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b
  failure_eq : ∀ pool W v, (R.history C).w W ≠ 0 →
    D.internalFailure pool (starProbe v) W = (K.binProblem C pool W).independentFailure v
  pinned_failure_eq : ∀ pool W v g b, (R.history C).w W ≠ 0 →
    D.pinnedInternalFailure pool (pinProbe v g b) W = (K.binProblem C pool W).pinnedFailure v g b
  history_eq : ∀ pool, D.historyLaw pool = R.history C
  Column : D.LoadColumn ≃ Fin (T.S.N k)
  load_eq : ∀ pool W y, D.loadValue pool W y =
    ∑ r : OddCellRole G C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w (Column y)
  threshold_eq : D.loadThreshold = κ.θstar

/-- S3 diagnostic producer. The exponent and cutoff precede every stage,
cell, history and pin; means and sensitivities are conclusions, not inputs.
T16:207–257 and 259–288 supply the two different concentration budgets. -/
theorem cell_pool_diagnostics_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ c0 : ℝ, c0 = 1 / 2 ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
        (R : CellRawData H.geom) (Perm : CellPermissions R),
        R.SourceValid → n₀ ≤ T.S.n k →
        (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
        ∃ K : CellRestrictedKernels R Perm, ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
          ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
            (R.Hist C) Check (T.S.n k) c0,
            Nonempty (CellDiagnosticLink K C D) ∧
            Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
  sorry

/-- S2 group producer at successful physical data. The capacity subset
certificates of T16:330–342 and the actual star tests produce hP.certificates. -/
theorem successful_group_bin_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
      (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
        (R.Hist C) Check (T.S.n k) c0),
      R.SourceValid → PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      CellDiagnosticLink K C D → ∀ pool W, D.typical pool → D.loadGate pool W →
      (R.history C).w W ≠ 0 → GroupBinHypotheses hκ (K.binProblem C pool W) := by
  sorry

/-- A role problem linked to the successful physical bins, not arbitrary
targets/tests. In direct modes its single block is the whole cell pool. -/
structure CellRoleProblem {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell)
    (pool : CellPool G C) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) where
  Block : Type
  [blockFin : Fintype Block]
  [blockDec : DecidableEq Block]
  problem : RoleLabelProblem (OddCellRole G C) (Fin (T.S.N k)) (EvenCellRole G C) Block
  regime_eq : problem.regime = if PT.tiling.mode.isCluster then .cluster else .direct
  scale_eq : problem.d = if PT.tiling.mode.isCluster then (PT.tiling.P (G.cellPatch C)).d else G.nslot C
  height_eq : problem.h = (PT.tiling.P (G.cellPatch C)).h
  targets_eq : ∀ r y, (problem.target r).w y =
    if PT.tiling.mode.isCluster then (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y else
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
  participants_eq : ∀ v, problem.participants v = K.participants C v
  tests_eq : ∀ v ys, problem.starBad v ys ↔ PT.tiling.mode.isCluster ∧ R.rawPrior C W ys v.1 = 0
  cluster_blocks : PT.tiling.mode.isCluster →
    ∃ bins : Block ≃ Bin PT.tiling (G.cellPatch C),
      (∀ b, problem.blockLabels b = (bins b).1) ∧
      ∀ r, bins (problem.blockOf r) = a (R.groupOf C r)
  direct_block : ¬ PT.tiling.mode.isCluster →
    ∃ _one : Block ≃ Unit, ∀ b, problem.blockLabels b = (Finset.univ.image pool).biUnion (fun D => D.1)

attribute [instance] CellRoleProblem.blockFin CellRoleProblem.blockDec

/-- S2 role producer. The two independent failure endpoints now belong to
the physical producer contract (T16:409–417); the certificate uses independent
whole-bin injection variables, not independent individual role labels. -/
theorem successful_role_label_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
      (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
        (R.Hist C) Check (T.S.n k) c0),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      CellDiagnosticLink K C D →
      ∀ pool W a, D.typical pool → D.loadGate pool W → (R.history C).w W ≠ 0 →
      (PT.tiling.mode.isCluster → (K.binProblem C pool W).safe a) →
      (PT.tiling.mode.isCluster → ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0) →
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem ∧
        (∀ v, L.problem.independentStarFailure v ≤
          Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ)) ∧
        (∀ v r y, L.problem.pinnedStarFailure v r y ≤
          2 * (PT.tiling.P (H.geom.cellPatch C)).d *
            Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ)) := by
  sorry

/-- Selected lookup kernels after applying the two unchanged calibration
exports. Direct modes omit the group calibration and use only P16.4. -/
structure CellCalibratedStages {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) where
  typical : ∀ C, CellPool G C → Prop
  gate : ∀ C, CellPool G C → Finset (R.Hist C)
  gate_pos : ∀ C pool, typical C pool → 0 < ∑ W ∈ gate C pool, (R.history C).w W
  binLaw : ∀ C, CellPool G C → R.Hist C → FinLaw (R.Group C → Bin PT.tiling (G.cellPatch C))
  bin_marginals : ∀ C pool W g b, typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 →
    (binLaw C pool W).pr (fun a => a g = b) = (K.qtilde C pool W g).w b
  bin_feasible : ∀ C pool W, typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 →
    PT.tiling.mode.isCluster → (K.binProblem C pool W).feasible (binLaw C pool W)
  labelLaw : ∀ C, CellPool G C → R.Hist C →
    (R.Group C → Bin PT.tiling (G.cellPatch C)) → FinLaw (OddCellRole G C → Fin (T.S.N k))
  label_marginals : ∀ C pool W a r y, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    (labelLaw C pool W a).pr (fun ys => ys r = y) =
      (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y
  label_injective : ∀ C pool W a ys, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    (labelLaw C pool W a).w ys ≠ 0 → Function.Injective ys
  cluster_label_feasible : ∀ C pool W a, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    PT.tiling.mode.isCluster → ∃ L : CellRoleProblem K C pool W a,
      L.problem.feasible (labelLaw C pool W a)
  /-- In direct modes P16.4 calibrates the whole label law first; bins are
  then its singleton-bin readout, and the conditional label stage is Dirac. -/
  direct_joint : ∀ C pool W (S : Finset (OddCellRole G C)) (ys : OddCellRole G C → Fin (T.S.N k)),
    typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 → ¬ PT.tiling.mode.isCluster →
    (S.card : ℝ) ≤ Real.rpow (G.nslot C : ℝ) 0.025 →
    (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr (fun ω => ∀ r ∈ S, ω.2 r = ys r) ≤
      Real.exp (Real.rpow (G.nslot C : ℝ) (-0.04) * S.card) *
        ∏ r ∈ S, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w (ys r))

/-- Keep every chosen diagnostic linked when assembling the lookup kernels. -/
structure CellDiagnostics {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (c0 : ℝ) where
  exponent_half : c0 = 1 / 2
  Check : G.Cell → Type
  [checkFin : ∀ C, Fintype (Check C)]
  diagnostic : ∀ C, CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
    (R.Hist C) (Check C) (T.S.n k) c0
  linked : ∀ C, CellDiagnosticLink K C (diagnostic C)
  concentration : ∀ C, PoolConcentrationHypotheses (diagnostic C)
  load : ∀ C, LoadGateHypotheses (diagnostic C)

attribute [instance] CellDiagnostics.checkFin

set_option maxHeartbeats 2000000 in
/-- This assembly consumes the hypotheses produced above and the two
calibration exports; it does not assume any calibrated law as an input. -/
theorem cell_calibrated_stages_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0), R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∃ S : CellCalibratedStages K,
        (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) ∧
        ∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool) := by
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  refine ⟨max nG nR, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds hSource hn hPerm
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left _ _).trans hn
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hLowCluster : PT.tiling.mode.isCluster → PT.tiling.mode = .lowCluster := by
    intro hcl
    cases hmode : PT.tiling.mode with
    | bounded =>
        rw [hmode] at hcl
        simp [Mode.isCluster] at hcl
    | lowDirect =>
        rw [hmode] at hcl
        simp [Mode.isCluster] at hcl
    | highDirect =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | lowCluster => rfl
    | highSmall =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highLarge =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
  have hGroupInput (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0) :
      GroupBinHypotheses hκ (K.binProblem C pool W) :=
    hG Q H hCalibration R Perm K C (Ds.diagnostic C) hSource (hLowCluster hcl)
      hnG hPerm (Ds.linked C) pool W htyp hload hw
  have hRoleInput (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0)
      (hsafe : PT.tiling.mode.isCluster → (K.binProblem C pool W).safe a)
      (hqpos : PT.tiling.mode.isCluster →
        ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0) :
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem := by
    obtain ⟨L, hL, _hIndependent, _hPinned⟩ :=
      hR Q H hCalibration R Perm K C (Ds.diagnostic C) hSource hnR hPerm
        (Ds.linked C) pool W a htyp hload hw hsafe hqpos
    exact ⟨L, hL⟩
  have hDirectD1 (hnot : ¬ PT.tiling.mode.isCluster) (i : Fin PT.tiling.m) :
      (PT.tiling.P i).d = 1 := by
    cases hmode : PT.tiling.mode with
    | bounded =>
        have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
        exact (hdata.2 i).2.2.1
    | lowDirect =>
        have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode) i
        exact hdata.2.2.2.2.2.1
    | lowCluster =>
        have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
        exact False.elim (hnot hc)
    | highDirect =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highSmall =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highLarge =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
  have hBinSingleton (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster)
      (D : Bin PT.tiling (H.geom.cellPatch C)) : D.1.card = 1 := by
    calc
      D.1.card = (PT.tiling.P (H.geom.cellPatch C)).d :=
        Q.profiled_valid.tiling_valid.bins_card (H.geom.cellPatch C) D.1 D.2
      _ = 1 := hDirectD1 hnot (H.geom.cellPatch C)
  let binLabel (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster)
      (D : Bin PT.tiling (H.geom.cellPatch C)) : Fin (T.S.N k) :=
    Classical.choose (Finset.card_eq_one.mp (hBinSingleton C hnot D))
  let defaultBin (C : H.geom.Cell) : Bin PT.tiling (H.geom.cellPatch C) :=
    Classical.choice (by
      have hYne : (PT.tiling.P (H.geom.cellPatch C)).Y ≠ ∅ :=
        (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2.ne_empty
      have hY : (PT.tiling.P (H.geom.cellPatch C)).Y ≠ ⊥ := by simpa using hYne
      obtain ⟨D, hD⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty hY
      exact ⟨⟨D, hD⟩⟩)
  let binOfLabel (C : H.geom.Cell) (pool : CellPool H.geom C)
      (y : Fin (T.S.N k)) : Bin PT.tiling (H.geom.cellPatch C) :=
    if hy : ∃ s : Fin (H.geom.nslot C), y ∈ (pool s).1 then
      pool (Classical.choose hy) else defaultBin C
  let groupBinReadout (C : H.geom.Cell) (pool : CellPool H.geom C)
      (ys : OddCellRole H.geom C → Fin (T.S.N k))
      (a0 : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :
      R.Group C → Bin PT.tiling (H.geom.cellPatch C) := fun g =>
    if hr : ∃ r, R.groupOf C r = g then
      binOfLabel C pool (ys (Classical.choose hr)) else a0 g
  have hDirectRoleData (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      ∃ L : CellRoleProblem K C pool W (fun _ => defaultBin C),
        RoleLabelHypotheses hκ L.problem ∧
        ∃ Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)),
          L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
    have hsafe : PT.tiling.mode.isCluster →
        (K.binProblem C pool W).safe (fun _ => defaultBin C) := fun hc => False.elim (hnot hc)
    have hqpos : PT.tiling.mode.isCluster →
        ∀ g, (K.qtilde C pool W g).w (defaultBin C) ≠ 0 := fun hc => False.elim (hnot hc)
    obtain ⟨L, hL⟩ := hRoleInput C pool W (fun _ => defaultBin C) htyp hload hw hsafe hqpos
    obtain ⟨Qlab, hFeasible, hMarg⟩ := calibrated_role_labels hκ L.problem hL
    exact ⟨L, hL, Qlab, hFeasible, hMarg⟩
  let directRoleLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) :=
    Classical.choose ((Classical.choose_spec (hDirectRoleData C pool W htyp hload hw hnot)).2)
  have hDirectGroupInj (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster) :
      Function.Injective (R.groupOf C) := by
    rcases hSource with ⟨hmode, _hUniform, _hData⟩ | ⟨_hnot, hData⟩
    · have hcl : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
      exact False.elim (hnot hcl)
    · exact (hData C).1
  have hDirectRoleSupport (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) (L : CellRoleProblem K C pool W a)
      (Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)))
      (hMarg : ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y)
      (hnot : ¬ PT.tiling.mode.isCluster) (ys : OddCellRole H.geom C → Fin (T.S.N k))
      (hys : Qlab.w ys ≠ 0) (r : OddCellRole H.geom C) :
      poolContainsLabel pool (ys r) := by
    have hweight : 0 < Qlab.w ys :=
      lt_of_le_of_ne (Qlab.nonneg ys) (Ne.symm hys)
    have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr Qlab (fun z => z r = ys r) ys rfl
    have htarget : (L.problem.target r).w (ys r) ≠ 0 := by
      have hpos : 0 < Qlab.pr (fun z => z r = ys r) := lt_of_lt_of_le hweight hAtom
      rw [hMarg r (ys r)] at hpos
      exact ne_of_gt hpos
    have hlabel : ys r ∈ L.problem.blockLabels (L.problem.blockOf r) :=
      L.problem.target_support r (ys r) htarget
    obtain ⟨one, hblock⟩ := L.direct_block hnot
    rw [hblock (L.problem.blockOf r)] at hlabel
    simpa [poolContainsLabel, Finset.mem_biUnion, Finset.mem_image] using hlabel
  have hDirectDecode (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a0 : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) (L : CellRoleProblem K C pool W a0)
      (aOther : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)))
      (hMarg : ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y)
      (hnot : ¬ PT.tiling.mode.isCluster)
      (ys : OddCellRole H.geom C → Fin (T.S.N k)) (hys : Qlab.w ys ≠ 0)
      (r : OddCellRole H.geom C) :
      binLabel C hnot (groupBinReadout C pool ys aOther (R.groupOf C r)) = ys r := by
    have hinj := hDirectGroupInj C hnot
    have hr : ∃ r' : OddCellRole H.geom C, R.groupOf C r' = R.groupOf C r := ⟨r, rfl⟩
    have hchosen : Classical.choose hr = r := by
      apply hinj
      exact Classical.choose_spec hr
    have hpool := hDirectRoleSupport C pool W a0 L Qlab hMarg hnot ys hys r
    rcases hpool with ⟨s, hs⟩
    have hfind : ∃ s : Fin (H.geom.nslot C), ys r ∈ (pool s).1 := ⟨s, hs⟩
    have hy : ys r ∈ (pool (Classical.choose hfind)).1 := Classical.choose_spec hfind
    have hcard := hBinSingleton C hnot (pool (Classical.choose hfind))
    have hsingle : (pool (Classical.choose hfind)).1 =
        {binLabel C hnot (pool (Classical.choose hfind))} :=
      Classical.choose_spec (Finset.card_eq_one.mp hcard)
    have hlabel : ys r = binLabel C hnot (pool (Classical.choose hfind)) := by
      rw [hsingle] at hy
      simpa using hy
    have hread : groupBinReadout C pool ys aOther (R.groupOf C r) = binOfLabel C pool (ys r) := by
      dsimp [groupBinReadout]
      rw [dif_pos hr, hchosen]
    have hread' : binOfLabel C pool (ys r) = pool (Classical.choose hfind) := by
      simp [binOfLabel, hfind]
    rw [hread, hread']
    exact hlabel.symm
  let directBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    FinLaw.map
      (FinLaw.bind (directRoleLaw C pool W htyp hload hw hnot)
        (fun _ => FinLaw.pi fun g => K.qtilde C pool W g))
      (fun ω => groupBinReadout C pool ω.1 ω.2)
  let directLabelLaw (C : H.geom.Cell) (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) := by
    letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
    exact FinLaw.dirac (fun r => binLabel C hnot (a (R.groupOf C r)))
  let calibratedBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    Classical.choose (calibrated_group_bins hκ (K.binProblem C pool W)
      (hGroupInput C pool W hcl htyp hload hw))
  let productBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    FinLaw.pi fun g => K.qtilde C pool W g
  have hDirectU (C : H.geom.Cell) (W : R.Hist C) (g : R.Group C)
      (D : Bin PT.tiling (H.geom.cellPatch C)) (y : Fin (T.S.N k))
      (hnot : ¬ PT.tiling.mode.isCluster) :
      (R.U C W g D).w y = if y ∈ D.1 then 1 else 0 := by
    rcases hSource with ⟨hmode, _hUniform, _hCells⟩ | ⟨_hnot, hCells⟩
    · have hcluster : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
      exact False.elim (hnot hcluster)
    · rcases hCells C with ⟨_hInjective, _hValues, _hPass, _hRaw, _hTrim, hU, _hPrior⟩
      exact hU W g D y
  have hBinUnique (C : H.geom.Cell) (D D' : Bin PT.tiling (H.geom.cellPatch C))
      (y : Fin (T.S.N k)) (hD : y ∈ D.1) (hD' : y ∈ D'.1) : D = D' := by
    by_contra hne
    have hdis := (PT.tiling.P (H.geom.cellPatch C)).bins.disjoint D.2 D'.2 (by
      intro hsets
      apply hne
      exact Subtype.ext hsets)
    exact False.elim ((Finset.disjoint_left.mp hdis) hD hD')
  have hDirectRowPoolSupport (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (L : CellRoleProblem K C pool W a) (r : OddCellRole H.geom C)
      (y : Fin (T.S.N k)) (hnot : ¬ PT.tiling.mode.isCluster)
      (hy : (L.problem.target r).w y ≠ 0) : poolContainsLabel pool y := by
    have hlabels := L.problem.target_support r y hy
    obtain ⟨one, hblock⟩ := L.direct_block hnot
    rw [hblock (L.problem.blockOf r)] at hlabels
    simpa [poolContainsLabel, Finset.mem_biUnion, Finset.mem_image] using hlabels
  have hDirectTargetMap (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (L : CellRoleProblem K C pool W a) (r : OddCellRole H.geom C)
      (hnot : ¬ PT.tiling.mode.isCluster) (D : Bin PT.tiling (H.geom.cellPatch C)) :
      (FinLaw.map (L.problem.target r) (binOfLabel C pool)).pr (fun B => B = D) =
        (K.qtilde C pool W (R.groupOf C r)).w D := by
    rw [Lane_q_s16_prod2.finLaw_map_pr]
    have hevent : ∀ y, (L.problem.target r).w y ≠ 0 →
        (binOfLabel C pool y = D ↔ y ∈ D.1) := by
      intro y hy
      have hp := hDirectRowPoolSupport C pool W a L r y hnot hy
      constructor
      · intro hEq
        have hmem : y ∈ (binOfLabel C pool y).1 := by
          unfold binOfLabel
          split_ifs with hs
          · exact Classical.choose_spec hs
          · exact False.elim (hs hp)
        rw [hEq] at hmem
        exact hmem
      · intro hyD
        obtain ⟨s, hs⟩ := hp
        let hslt : ∃ s : Fin (H.geom.nslot C), y ∈ (pool s).1 := ⟨s, hs⟩
        have hpoolMem : y ∈ (pool (Classical.choose hslt)).1 := Classical.choose_spec hslt
        have huniq := hBinUnique C D (pool (Classical.choose hslt)) y hyD hpoolMem
        have hread : binOfLabel C pool y = pool (Classical.choose hslt) := by
          simp [binOfLabel, hslt]
        exact hread.trans huniq.symm
    rw [Lane_q_s16_prod2.finLaw_pr_congr_of_supported (L.problem.target r)
      (fun y => binOfLabel C pool y = D) (fun y => y ∈ D.1) hevent]
    have htarget : ∀ y, (L.problem.target r).w y =
        ∑ B, (K.qtilde C pool W (R.groupOf C r)).w B * (R.U C W (R.groupOf C r) B).w y := by
      intro y
      simpa [hnot] using L.targets_eq r y
    have hmass : (L.problem.target r).pr (fun y => y ∈ D.1) =
        (K.qtilde C pool W (R.groupOf C r)).w D := by
      letI : DecidablePred (fun y : Fin (T.S.N k) => y ∈ D.1) :=
        fun y => Classical.propDecidable (y ∈ D.1)
      have hmassRaw : (∑ y, if y ∈ D.1 then (L.problem.target r).w y else 0) =
          (K.qtilde C pool W (R.groupOf C r)).w D := by
        calc
          (∑ y, if y ∈ D.1 then (L.problem.target r).w y else 0) =
              ∑ y, ∑ B, if y ∈ D.1 then
                (K.qtilde C pool W (R.groupOf C r)).w B *
                  (if y ∈ B.1 then 1 else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hmem : y ∈ D.1
            · simp only [if_pos hmem]
              rw [htarget y]
              apply Finset.sum_congr rfl
              intro B hB
              rw [hDirectU C W (R.groupOf C r) B y hnot]
            · simp [hmem]
          _ = ∑ B, ∑ y, if y ∈ D.1 then
                (K.qtilde C pool W (R.groupOf C r)).w B *
                  (if y ∈ B.1 then 1 else 0) else 0 := by
            rw [Finset.sum_comm]
          _ = (K.qtilde C pool W (R.groupOf C r)).w D := by
            calc
              (∑ B, ∑ y, if y ∈ D.1 then
                  (K.qtilde C pool W (R.groupOf C r)).w B *
                    (if y ∈ B.1 then 1 else 0) else 0) =
                  ∑ B, if B = D then (K.qtilde C pool W (R.groupOf C r)).w B else 0 := by
                apply Finset.sum_congr rfl
                intro B hB
                by_cases hBD : B = D
                · subst B
                  obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.mp (hBinSingleton C hnot D)
                  simp [hy₀]
                · have hdis : Disjoint B.1 D.1 :=
                    (PT.tiling.P (H.geom.cellPatch C)).bins.disjoint B.2 D.2 (by
                      intro hsets
                      apply hBD
                      exact Subtype.ext hsets)
                  simp only [if_neg hBD]
                  apply Finset.sum_eq_zero
                  intro y hy
                  by_cases hmemD : y ∈ D.1
                  · have hnotB : y ∉ B.1 := fun hmemB =>
                      (Finset.disjoint_left.mp hdis) hmemB hmemD
                    simp [hmemD, hnotB]
                  · simp [hmemD]
              _ = (K.qtilde C pool W (R.groupOf C r)).w D := by simp
      simpa only [FinLaw.pr] using hmassRaw
    exact hmass
  let binLaw : ∀ C (pool : CellPool H.geom C) (W : R.Hist C),
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) := fun C pool W =>
    if hcl : PT.tiling.mode.isCluster then
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            calibratedBinLaw C pool W hcl htyp hload hw
          else productBinLaw C pool W
        else productBinLaw C pool W
      else productBinLaw C pool W
    else
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            directBinLaw C pool W htyp hload hw hcl
          else productBinLaw C pool W
        else productBinLaw C pool W
      else productBinLaw C pool W
  have hBinMarg : ∀ C pool W g b, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 →
      (binLaw C pool W).pr (fun a => a g = b) = (K.qtilde C pool W g).w b := by
    intro C pool W g b htyp hgate hw
    by_cases hcl : PT.tiling.mode.isCluster
    · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      have hbin := Classical.choose_spec (calibrated_group_bins hκ (K.binProblem C pool W)
        (hGroupInput C pool W hcl htyp hload hw))
      simpa [binLaw, hcl, htyp, hload, hw, calibratedBinLaw,
        CellRestrictedKernels.binProblem] using hbin.2 g b
    · have hnot : ¬ PT.tiling.mode.isCluster := hcl
      have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hDirectRoleData C pool W htyp hload hw hnot
      let L := Classical.choose hData
      let hQexists := (Classical.choose_spec hData).2
      let Qlab := directRoleLaw C pool W htyp hload hw hnot
      have hQspec : L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
        dsimp [Qlab, directRoleLaw, L, hData]
        exact Classical.choose_spec hQexists
      let tailLaw := FinLaw.pi fun g => K.qtilde C pool W g
      let sourceLaw := FinLaw.bind Qlab (fun _ => tailLaw)
      let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
          (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
        groupBinReadout C pool ω.1 ω.2
      have hBinLaw : binLaw C pool W = FinLaw.map sourceLaw readout := by
        simp [binLaw, hnot, htyp, hload, hw, directBinLaw, sourceLaw, readout,
          tailLaw, productBinLaw, directRoleLaw, Qlab, hData]
      have hMapped : (binLaw C pool W).pr (fun a => a g = b) =
          sourceLaw.pr (fun ω => readout ω g = b) := by
        rw [hBinLaw]
        exact Lane_q_s16_prod2.finLaw_map_pr sourceLaw readout (fun a => a g = b)
      by_cases hr : ∃ r : OddCellRole H.geom C, R.groupOf C r = g
      · let r := Classical.choose hr
        have hrEq : R.groupOf C r = g := Classical.choose_spec hr
        have hchoose : Classical.choose hr = r := by
          apply hDirectGroupInj C hnot
          exact (Classical.choose_spec hr).trans hrEq.symm
        have hread (ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C))) :
            readout ω g = binOfLabel C pool (ω.1 r) := by
          dsimp [readout, groupBinReadout]
          rw [dif_pos hr, hchoose]
        have hsource : sourceLaw.pr (fun ω => readout ω g = b) =
            (K.qtilde C pool W g).w b := by
          calc
            sourceLaw.pr (fun ω => readout ω g = b) =
                sourceLaw.pr (fun ω => binOfLabel C pool (ω.1 r) = b) := by
              apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
              intro ω _
              rw [hread ω]
            _ = Qlab.pr (fun ys => binOfLabel C pool (ys r) = b) := by
              simpa [sourceLaw] using
                (Lane_q_s16_prod2.finLaw_bind_pr_fst Qlab (fun _ => tailLaw)
                  (fun ys => binOfLabel C pool (ys r) = b))
            _ = (FinLaw.map (L.problem.target r) (binOfLabel C pool)).pr
                (fun D => D = b) :=
              Lane_q_s16_prod2.finLaw_pr_map_coordinate Qlab
                (fun r => L.problem.target r) hQspec.2 r (binOfLabel C pool)
                (fun D => D = b)
            _ = (K.qtilde C pool W g).w b := by
              rw [hDirectTargetMap C pool W (fun _ => defaultBin C) L r hnot b]
              rw [hrEq]
        exact hMapped.trans hsource
      · have hread (ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C))) :
            readout ω g = ω.2 g := by
          dsimp [readout, groupBinReadout]
          rw [dif_neg hr]
        have hTailMarg : tailLaw.pr (fun a => a g = b) = (K.qtilde C pool W g).w b := by
          dsimp [tailLaw]
          exact Lane_q_s16_prod2.finLaw_pi_coordinate_mass
            (fun g => K.qtilde C pool W g) g b
        have hsource : sourceLaw.pr (fun ω => readout ω g = b) =
            (K.qtilde C pool W g).w b := by
          calc
            sourceLaw.pr (fun ω => readout ω g = b) =
                sourceLaw.pr (fun ω => ω.2 g = b) := by
              apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
              intro ω _
              rw [hread ω]
            _ = tailLaw.pr (fun a => a g = b) := by
              simpa [sourceLaw] using
                (Lane_q_s16_prod2.finLaw_bind_pr_snd Qlab tailLaw (fun a => a g = b))
            _ = (K.qtilde C pool W g).w b := hTailMarg
        exact hMapped.trans hsource
  have hBinFeasible : ∀ C pool W, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → PT.tiling.mode.isCluster →
      (K.binProblem C pool W).feasible (binLaw C pool W) := by
    intro C pool W htyp hgate hw hcl
    have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
    have hbin := Classical.choose_spec (calibrated_group_bins hκ (K.binProblem C pool W)
      (hGroupInput C pool W hcl htyp hload hw))
    simpa [binLaw, hcl, htyp, hload, hw, calibratedBinLaw] using hbin.1
  have hClusterRoleData (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0)
      (ha : (binLaw C pool W).w a ≠ 0) :
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem ∧
        ∃ Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)),
          L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
    have hgateMem : W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hload⟩
    have hbinFeas := hBinFeasible C pool W htyp hgateMem hw hcl
    have hsafe : (K.binProblem C pool W).safe a := hbinFeas.1 a ha
    have hwa : 0 < (binLaw C pool W).w a :=
      lt_of_le_of_ne ((binLaw C pool W).nonneg a) (Ne.symm ha)
    have hqpos : ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0 := by
      intro g
      have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr (binLaw C pool W)
        (fun a' => a' g = a g) a rfl
      have hMarg := hBinMarg C pool W g (a g) htyp hgateMem hw
      have hPos : 0 < (K.qtilde C pool W g).w (a g) := by
        rw [← hMarg]
        exact lt_of_lt_of_le hwa hAtom
      exact ne_of_gt hPos
    obtain ⟨L, hL⟩ := hRoleInput C pool W a htyp hload hw (fun _ => hsafe) (fun _ => hqpos)
    obtain ⟨Qlab, hFeasible, hMarg⟩ := calibrated_role_labels hκ L.problem hL
    exact ⟨L, hL, Qlab, hFeasible, hMarg⟩
  let productLabelLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) :=
    FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
  let labelLaw : ∀ C (pool : CellPool H.geom C) (W : R.Hist C),
      (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) →
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) := fun C pool W a =>
    if hcl : PT.tiling.mode.isCluster then
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            if ha : (binLaw C pool W).w a ≠ 0 then
              Classical.choose ((Classical.choose_spec
                (hClusterRoleData C pool W a hcl htyp hload hw ha)).2)
            else productLabelLaw C pool W a
          else productLabelLaw C pool W a
        else productLabelLaw C pool W a
      else productLabelLaw C pool W a
    else
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then directLabelLaw C a hcl
          else productLabelLaw C pool W a
        else productLabelLaw C pool W a
      else productLabelLaw C pool W a
  have hLabelMarg : ∀ C pool W a r y, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
      (labelLaw C pool W a).pr (fun ys => ys r = y) =
        (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y := by
    intro C pool W a r y htyp hgate hw ha
    by_cases hcl : PT.tiling.mode.isCluster
    · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
      have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
        simp [labelLaw, hcl, htyp, hload, hw, ha]
      rw [hLaw]
      have hQ := Classical.choose_spec ((Classical.choose_spec hData).2)
      have hMarg := hQ.2 r y
      have hTarget : ((Classical.choose hData).problem.target r).w y =
          (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y := by
        simpa [hcl] using (Classical.choose hData).targets_eq r y
      rw [hTarget] at hMarg
      exact hMarg
    · letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
      have hU : (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y =
          (if y ∈ (a (R.groupOf C r)).1 then 1 else 0) := by
        rcases hSource with ⟨hmode, _hUniform, _hCells⟩ | ⟨_hnot, hCells⟩
        · have hcluster : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
          exact False.elim (hcl hcluster)
        · rcases hCells C with ⟨_hInjective, _hValues, _hPass, _hRaw, _hTrim, hU, _hPrior⟩
          exact hU W (R.groupOf C r) (a (R.groupOf C r)) y
      let D := a (R.groupOf C r)
      have hcard := hBinSingleton C hcl D
      have hBinSet : D.1 = {binLabel C hcl D} :=
        Classical.choose_spec (Finset.card_eq_one.mp hcard)
      have hLaw : labelLaw C pool W a = directLabelLaw C a hcl := by
        simp [labelLaw, hcl, htyp, (Finset.mem_filter.mp hgate).2, hw]
      rw [hLaw]
      dsimp [directLabelLaw]
      rw [Lane_q_s16_prod2.finLaw_dirac_pr, hU]
      simp [D, hBinSet, eq_comm]
  have hDirectJoint : ∀ C (pool : CellPool H.geom C) (W : R.Hist C)
      (Sset : Finset (OddCellRole H.geom C)) (ys : OddCellRole H.geom C → Fin (T.S.N k)),
      (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → ¬ PT.tiling.mode.isCluster →
      (Sset.card : ℝ) ≤ Real.rpow (H.geom.nslot C : ℝ) 0.025 →
      (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr
        (fun ω => ∀ r ∈ Sset, ω.2 r = ys r) ≤
      Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
        ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w (ys r)) := by
    intro C pool W Sset ys htyp hgate hw hnot hsize
    have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
    let hData := hDirectRoleData C pool W htyp hload hw hnot
    let L := Classical.choose hData
    let hQexists := (Classical.choose_spec hData).2
    let Qlab := directRoleLaw C pool W htyp hload hw hnot
    have hQspec : L.problem.feasible Qlab ∧
        ∀ r y, Qlab.pr (fun z => z r = y) = (L.problem.target r).w y := by
      dsimp [Qlab, directRoleLaw, L, hData]
      exact Classical.choose_spec hQexists
    have hRoleLaw : directRoleLaw C pool W htyp hload hw hnot = Qlab := rfl
    let sourceLaw := FinLaw.bind Qlab (fun _ => FinLaw.pi fun g => K.qtilde C pool W g)
    let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
        (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
      groupBinReadout C pool ω.1 ω.2
    let decode := fun a : R.Group C → Bin PT.tiling (H.geom.cellPatch C) =>
      fun r => binLabel C hnot (a (R.groupOf C r))
    let cylinder := fun z : OddCellRole H.geom C → Fin (T.S.N k) =>
      ∀ r ∈ Sset, z r = ys r
    let event : ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
        (OddCellRole H.geom C → Fin (T.S.N k))) → Prop :=
      fun ω => ∀ r ∈ Sset, ω.2 r = ys r
    have hBinLaw : binLaw C pool W = FinLaw.map sourceLaw readout := by
      simp [binLaw, hnot, htyp, hload, hw, directBinLaw, sourceLaw, readout,
        productBinLaw, hRoleLaw]
    have hLabelLaw : labelLaw C pool W = fun a => FinLaw.dirac (decode a) := by
      funext a
      simp [labelLaw, hnot, htyp, hload, hw, directLabelLaw, decode]
    have hStageEvent :
        (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr event =
          sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) := by
      rw [hBinLaw, hLabelLaw]
      letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
      exact Lane_q_s16_prod2.finLaw_map_bind_dirac_pr sourceLaw readout decode event
    have hDecodeSupport :
        sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) =
          sourceLaw.pr (fun ω => cylinder ω.1) := by
      apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
      intro ω hω
      have hQpos : Qlab.w ω.1 ≠ 0 := by
        intro hzero
        apply hω
        simp [sourceLaw, FinLaw.bind, hzero]
      constructor
      · intro hEvent r hr
        have hdec := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
          Qlab hQspec.2 hnot ω.1 hQpos r
        exact hdec.symm.trans (hEvent r hr)
      · intro hCylinder r hr
        have hdec := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
          Qlab hQspec.2 hnot ω.1 hQpos r
        exact hdec.trans (hCylinder r hr)
    have hSourceCylinder : sourceLaw.pr (fun ω => cylinder ω.1) = Qlab.pr cylinder := by
      dsimp [sourceLaw]
      rw [Lane_q_s16_prod2.finLaw_bind_pr]
      simp_rw [Lane_q_s16_prod2.finLaw_pr_const]
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hcyl : cylinder z <;> simp [hcyl]
    have hQueries : L.problem.queries Sset := by
      simpa [RoleLabelProblem.queries, L.regime_eq, L.scale_eq, hnot] using hsize
    have hQbound := hQspec.1.2 Sset ys hQueries
    have hTargets : ∀ r y, (L.problem.target r).w y =
        ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w y := by
      intro r y
      simpa [hnot] using L.targets_eq r y
    have hBound : Qlab.pr cylinder ≤
        Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := by
      change Qlab.pr cylinder ≤ Real.exp (L.problem.rate * (Sset.card : ℝ)) *
        ∏ r ∈ Sset, (L.problem.target r).w (ys r) at hQbound
      have hrate : L.problem.rate = Real.rpow (H.geom.nslot C : ℝ) (-0.04 : ℝ) := by
        simp [RoleLabelProblem.rate, L.regime_eq, L.scale_eq, hnot]
      rw [hrate] at hQbound
      have hprod : ∏ r ∈ Sset, (L.problem.target r).w (ys r) =
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact hTargets r (ys r)
      rw [hprod] at hQbound
      exact hQbound
    calc
      (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr event =
          sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) := hStageEvent
      _ = sourceLaw.pr (fun ω => cylinder ω.1) := hDecodeSupport
      _ = Qlab.pr cylinder := hSourceCylinder
      _ ≤ Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := hBound
  refine ⟨{
    typical := fun C pool => (Ds.diagnostic C).typical pool
    gate := fun C pool => Finset.univ.filter ((Ds.diagnostic C).loadGate pool)
    gate_pos := ?_
    binLaw := binLaw
    bin_marginals := hBinMarg
    bin_feasible := hBinFeasible
    labelLaw := labelLaw
    label_marginals := hLabelMarg
    label_injective := by
      intro C pool W a ys htyp hgate hw ha hys
      by_cases hcl : PT.tiling.mode.isCluster
      · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
        let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
        have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
          simp [labelLaw, hcl, htyp, hload, hw, ha]
        rw [hLaw] at hys
        have hSafe := (Classical.choose_spec ((Classical.choose_spec hData).2)).1.1 ys hys
        exact hSafe.1
      · have hnot := hcl
        have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
        let hData := hDirectRoleData C pool W htyp hload hw hnot
        let L := Classical.choose hData
        let hQexists := (Classical.choose_spec hData).2
        let Qlab := directRoleLaw C pool W htyp hload hw hnot
        have hQspec := Classical.choose_spec hQexists
        have hMarg : ∀ r y, Qlab.pr (fun z => z r = y) = (L.problem.target r).w y := by
          simpa [Qlab, directRoleLaw, L, hData] using hQspec.2
        let sourceLaw := FinLaw.bind Qlab (fun _ => FinLaw.pi fun g => K.qtilde C pool W g)
        let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
          groupBinReadout C pool ω.1 ω.2
        have hBinEq : binLaw C pool W = FinLaw.map sourceLaw readout := by
          simp [binLaw, hnot, htyp, (Finset.mem_filter.mp hgate).2, hw,
            directBinLaw, sourceLaw, readout, productBinLaw, directRoleLaw, Qlab, hData]
        have hpre : ∃ ω, readout ω = a ∧ sourceLaw.w ω ≠ 0 := by
          have ha' : (FinLaw.map sourceLaw readout).w a ≠ 0 := by
            rw [← hBinEq]
            exact ha
          exact Lane_q_s16_prod2.finLaw_map_nonzero_preimage sourceLaw readout a ha'
        obtain ⟨ω, hωa, hωpos⟩ := hpre
        have hQpos : Qlab.w ω.1 ≠ 0 := by
          intro hz
          apply hωpos
          simp [sourceLaw, FinLaw.bind, hz]
        have hysEq : ys = fun r => binLabel C hnot (a (R.groupOf C r)) := by
          by_contra hneq
          have hzero : (labelLaw C pool W a).w ys = 0 := by
            simp [labelLaw, hnot, htyp, (Finset.mem_filter.mp hgate).2, hw,
              directLabelLaw, FinLaw.dirac, hneq]
          exact hys hzero
        have hinj : Function.Injective ω.1 :=
          ((hQspec.1.1 ω.1 hQpos).1)
        have hysToQ (r : OddCellRole H.geom C) : ys r = ω.1 r := by
          have hdecode := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
            Qlab hMarg hnot ω.1 hQpos r
          have hread : groupBinReadout C pool ω.1 ω.2 = a := by
            simpa [readout] using hωa
          have hdecodeA : binLabel C hnot (a (R.groupOf C r)) = ω.1 r := by
            calc
              binLabel C hnot (a (R.groupOf C r)) =
                  binLabel C hnot (groupBinReadout C pool ω.1 ω.2 (R.groupOf C r)) := by
                rw [hread]
              _ = ω.1 r := hdecode
          have hy := congrFun hysEq r
          exact hy.trans hdecodeA
        intro r r' hrr'
        apply hinj
        calc
          ω.1 r = ys r := (hysToQ r).symm
          _ = ys r' := hrr'
          _ = ω.1 r' := hysToQ r'
    cluster_label_feasible := by
      intro C pool W a htyp hgate hw ha hcl
      have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
      refine ⟨Classical.choose hData, ?_⟩
      have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
        simp [labelLaw, hcl, htyp, hload, hw, ha]
      rw [hLaw]
      exact (Classical.choose_spec ((Classical.choose_spec hData).2)).1
    direct_joint := hDirectJoint
  }, ?_, ?_⟩
  · intro C pool ht
    obtain ⟨hgate, _⟩ :=
      ((history_load_gate_concentration (Ds.diagnostic C) (Ds.load C) pool ht).2
        (fun _ => 0) (by intro; norm_num))
    rw [(Ds.linked C).history_eq pool] at hgate
    exact hgate
  · intro C pool
    rfl
  · intro C pool
    rfl

/-- Transport identities for the constructed fresh state. Histories and
groups are reindexed explicitly, so the calibration record cannot choose
unrelated kernels or labels. -/
structure FreshConstructionLink {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} {K : CellRestrictedKernels R Perm}
    (S : CellCalibratedStages K) (F : FreshCell G) (Cal : FreshLabelCalibration F) where
  histories : ∀ C, Cal.Hist C ≃ R.Hist C
  groups : ∀ C, Cal.Group C ≃ R.Group C
  history_eq : ∀ C, Cal.history C = FinLaw.map (R.history C) (histories C).symm
  group_eq : ∀ C r, groups C (Cal.groupOf C r) = R.groupOf C r
  incoming_eq : ∀ C W g, Cal.qin C W g = R.qin C (histories C W) (groups C g)
  U_eq : ∀ C W g b, Cal.U C W g b = R.U C (histories C W) (groups C g) b
  permission_eq : ∀ C g, Cal.permitted C g = (Perm.table C).permitted (groups C g)
  restricted_eq : ∀ C pool W g, Cal.qtilde C pool W g = K.qtilde C pool (histories C W) (groups C g)
  typical_eq : ∀ C pool, F.typical C pool ↔ S.typical C pool
  gate_eq : ∀ C pool, Cal.gate C pool = (S.gate C pool).image (histories C).symm
  bin_eq : ∀ C pool W, Cal.binSampler C pool W =
    FinLaw.map (S.binLaw C pool (histories C W)) (fun a g => a (groups C g))
  label_eq : ∀ C pool W a, Cal.labelSampler C pool W a =
    S.labelLaw C pool (histories C W) (fun g => a ((groups C).symm g))
  prior_eq : ∀ C pool W a ys v, F.typical C pool → (Cal.gatedHistory C pool).w W ≠ 0 →
    (Cal.binSampler C pool W).w a ≠ 0 → (Cal.labelSampler C pool W a).w ys ≠ 0 →
    G.cellOf v = C → IsEvenRole v →
    F.prior C (Cal.encode C (W, a, ys)) v = R.rawPrior C (histories C W) ys v

/-- S3 fresh calibration producer (T16:294–296,469–482). Its inputs are
physical stages already certified by P16.3/P16.4; exact identities and all
three scalar denominator budgets are outputs. -/
theorem fresh_label_calibration_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      ∃ F : FreshCell H.geom, ∃ Cal : FreshLabelCalibration F,
        Nonempty (FreshConstructionLink S F Cal) := by
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  obtain ⟨nCost, hCost⟩ := Lane_q_s16_prod2.exp_denominator_slack_cutoff
    κ.cperm hκ.cperm_rng.1
  refine ⟨max (max (max nG nR) 2) (max nCost 8), ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S hSource hn hPerm hTypical hGate
  have hnBase : max (max nG nR) 2 ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hn
  have hn0 : max nG nR ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hnBase
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left nG nR).trans hn0
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right nG nR).trans hn0
  have hn2 : 2 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnBase
  have hnCostBase : max nCost 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hnCost : nCost ≤ T.S.n k := (Nat.le_max_left _ _).trans hnCostBase
  have hn8 : 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnCostBase
  have hFallback : ∀ C : H.geom.Cell,
      ∃ ys : OddCellRole H.geom C → Fin (T.S.N k), Function.Injective ys := by
    intro C
    let D := Ds.diagnostic C
    have hPoolHyp : PoolConcentrationHypotheses D := Ds.concentration C
    have hBad := pool_typicality_concentration_after_permission D hPoolHyp
    have hSmall : D.poolLaw.pr (fun pool => ¬ D.typical pool) < 1 := by
      calc
        D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤
            Real.exp (-(T.S.n k : ℝ) ^ c0) / 2 := hBad.1
        _ < 1 := by
          have hc0 : c0 = 1 / 2 := Ds.exponent_half
          rw [hc0]
          have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
          have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
          have hexp : Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) < 1 :=
            Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
          have hexppos : 0 < Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) := Real.exp_pos _
          linarith
    have hTypicalProb : 0 < D.poolLaw.pr (fun pool => D.typical pool) := by
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl D.poolLaw (fun pool => D.typical pool)
      linarith
    obtain ⟨pool, hDtyp, hPoolW⟩ :=
      Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom D.poolLaw
        (fun pool => D.typical pool) hTypicalProb
    have hStyp : S.typical C pool := (hTypical C pool).2 hDtyp
    have hGatePos : 0 < ∑ W ∈ S.gate C pool, (R.history C).w W := S.gate_pos C pool hStyp
    obtain ⟨W, hWgate, hWpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := S.gate C pool)
        (f := fun W => (R.history C).w W)
        (by intro W hW; exact (R.history C).nonneg W)).mp hGatePos
    have hBinProb : 0 < (S.binLaw C pool W).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨a, _haTrue, ha⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.binLaw C pool W) (fun _ => True) hBinProb
    have hLabelProb : 0 < (S.labelLaw C pool W a).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨ys, _hysTrue, hys⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.labelLaw C pool W a) (fun _ => True) hLabelProb
    exact ⟨ys, S.label_injective C pool W a ys hStyp hWgate (ne_of_gt hWpos) ha hys⟩
  let RawState : H.geom.Cell → Type := fun C =>
    R.Hist C × ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
      (OddCellRole H.geom C → Fin (T.S.N k)))
  let encode := fun (C : H.geom.Cell) (z : RawState C) =>
    if hz : Function.Injective z.2.2 then some z else none
  let defaultLabels : ∀ C : H.geom.Cell, OddCellRole H.geom C → Fin (T.S.N k) :=
    fun C => Classical.choose (hFallback C)
  let gatedHistory : ∀ C : H.geom.Cell, CellPool H.geom C → FinLaw (R.Hist C) :=
    fun C pool => if ht : S.typical C pool then
      FinLaw.cond (R.history C) (S.gate C pool) (S.gate_pos C pool ht) else R.history C
  have hGatedSupport {C : H.geom.Cell} (pool : CellPool H.geom C) (W : R.Hist C)
      (ht : S.typical C pool) (hW : (gatedHistory C pool).w W ≠ 0) :
      W ∈ S.gate C pool ∧ (R.history C).w W ≠ 0 := by
    by_cases hmem : W ∈ S.gate C pool
    · refine ⟨hmem, ?_⟩
      by_contra hzero
      have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem, hzero]
      exact hW hz
    · have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem]
      exact False.elim (hW hz)
  let F : FreshCell H.geom := {
    State := fun C => Option (RawState C)
    fresh := fun C pool =>
      if htyp : S.typical C pool then
        FinLaw.map (FinLaw.bind (gatedHistory C pool)
          (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
          (encode C)
      else FinLaw.dirac none
    fallback := fun _ => none
    label := fun C s b =>
      if hb : H.geom.cellOf b = C ∧ ¬ IsEvenRole b then
        match s with
        | none => defaultLabels C ⟨b, hb⟩
        | some z => if hz : Function.Injective z.2.2 then
            z.2.2 ⟨b, hb⟩ else defaultLabels C ⟨b, hb⟩
      else ⟨0, T.S.N_pos k⟩
    prior := fun C s b y =>
      match s with
      | none => 0
      | some z => R.rawPrior C z.1 z.2.2 b y
    typical := S.typical
  }
  let δperm : ℝ := Real.exp (-(κ.cperm * (T.S.n k : ℝ)) / 2)
  let δgate : ℝ := Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ))
  let Cal : FreshLabelCalibration F := {
    Hist := R.Hist
    Group := R.Group
    groupOf := R.groupOf
    history := R.history
    gatedHistory := gatedHistory
    gate := S.gate
    gate_pos := S.gate_pos
    gated_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp only [gatedHistory, dif_pos ht]
    qin := R.qin
    U := R.U
    U_support := R.U_support
    permitted := fun C g => (Perm.table C).permitted g
    qtilde := K.qtilde
    qtilde_eq := by
      intro C pool W g D ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        have hpos : 0 < 1 - Real.exp (-c * (Perm.table C).n) := sub_pos.mpr hexp
        exact lt_of_lt_of_le hpos hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hzBoth : 0 < zBoth := by
        have hratio' : 0 < zBoth / zPerm := by rw [← hzImageEq]; exact hzImage
        have hmul := mul_pos hratio' hzPerm
        have heq : (zBoth / zPerm) * zPerm = zBoth := div_mul_cancel₀ _ (ne_of_gt hzPerm)
        rw [heq] at hmul
        exact hmul
      have hdenEq :
          (∑ D' ∈ (Perm.table C).permitted g ∩ Finset.image pool Finset.univ,
            (R.qin C W g).w D') = zBoth := by
        simp [zBoth, E, I, Finset.inter_comm]
      have hqtilde := K.qtilde_eq C pool W g D hW (ne_of_gt hzImage)
      rw [hqtilde, hqbar D]
      have hsumQbar : (∑ D' ∈ I, (K.qbar C W g).w D') = zImage := rfl
      rw [hsumQbar, hzImageEq, hdenEq]
      by_cases hDperm : D ∈ E <;> by_cases hDimage : D ∈ I
      · simp [E, I, hDperm, hDimage]
        field_simp [ne_of_gt hzPerm, ne_of_gt hzBoth]
      · have hPermD : D ∈ (Perm.table C).permitted g := by simpa [E] using hDperm
        have hNoPre : ¬ ∃ a, pool a = D := by
          intro hpre
          obtain ⟨a, ha⟩ := hpre
          apply hDimage
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
        simp [hDimage, hNoPre, hPermD]
      · simp [E, I, hDperm, hDimage]
      · simp [E, I, hDperm, hDimage]
    binSampler := S.binLaw
    labelSampler := S.labelLaw
    bin_marginals := by
      intro C pool W g D ht hW
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.bin_marginals C pool W g D ht hGateW hHistW
    label_marginals := by
      intro C pool W a r y ht hW ha
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.label_marginals C pool W a r y ht hGateW hHistW ha
    encode := encode
    fresh_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp [F, gatedHistory, ht, encode]
    label_eq := by
      intro C pool W a ys r ht hW ha hys
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hrole : H.geom.cellOf r.1 = C ∧ ¬ IsEvenRole r.1 := r.2
      simp [F, encode, hinj, hrole]
    raw_profile := by
      intro C r y
      rcases hSource with ⟨hmode, _hUniform, hSourceCell⟩ | _hDirect
      · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
          _hgroupOf, hqraw, hpretrim, hU, _hprior⟩ := hSourceCell C
        let gRaw := R.groupOf C r
        let sourcePair := groups.symm gRaw
        let s := sourcePair.1
        let gSol := sourcePair.2
        have hgroups : groups (s, gSol) = gRaw := by
          dsimp [s, gSol, sourcePair]
          exact groups.apply_symm_apply gRaw
        let rowRaw : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W gRaw).w D * (R.U C W gRaw D).w y
        let rowSol : (∀ t, Ssol.Val t) → ℝ := fun W =>
          ∑ D, Ssol.qin W gSol D * Ssol.U gSol W D y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            rowRaw W = rowSol (records s (W s)) := by
          intro W hW
          have hProd :
              (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            simpa [CellRawData.history, FinLaw.pi] using hW
          have hFactor : ∀ t,
              (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t) ≠ 0 := by
            intro t hzero
            apply hProd
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hcond := hFactor t
            have hpass : W t ∈ R.slicePass C t := by
              by_contra hnot
              apply hcond
              simp [FinLaw.cond, hnot]
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              by_contra hzero
              apply hcond
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          have hqin : ∀ D,
              (R.qin C W gRaw).w D = Ssol.qin (records s (W s)) gSol D := by
            intro D
            rw [← hgroups]
            rw [R.qin_eq C W (groups (s, gSol)) D hLocalInput]
            simp only [SliceSolver.qin, hpretrim W s gSol, hqraw W s gSol]
            by_cases hD : D ∈ Ssol.pretrimBins (records s (W s)) gSol <;> simp [hD]
          have hUeq : ∀ D,
              (R.U C W gRaw D).w y = Ssol.U gSol (records s (W s)) D y := by
            intro D
            rw [← hgroups]
            exact hU W s gSol D y
          dsimp [rowRaw, rowSol]
          apply Finset.sum_congr rfl
          intro D hD
          rw [hqin D, hUeq D]
        have hsupportAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) rowRaw (fun W => rowSol (records s (W s))) hrow
        have hcoordAvg :
            (R.history C).E (fun W => rowSol (records s (W s))) =
              (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := by
          simpa [CellRawData.history] using
            (Lane_q_s16_prod2.finLaw_pi_E_coordinate
              (fun t => FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)) s (fun z => rowSol (records s z)))
        have hPassMap : ∀ z,
            ((records s).symm z ∈ R.slicePass C s) ↔ Ssol.AllGood z := by
          intro z
          simpa using hslicePass s ((records s).symm z)
        have hsliceMap : R.sliceLaw C s =
            FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm := hsliceLaw s
        have hden :
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
              (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          calc
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
                (R.sliceLaw C s).pr (fun z => z ∈ R.slicePass C s) :=
              (Lane_q_s16_prod2.finLaw_pr_finset (R.sliceLaw C s)
                (R.slicePass C s)).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).pr
                  (fun z => z ∈ R.slicePass C s) := by rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).pr
                  (fun z => (records s).symm z ∈ R.slicePass C s) :=
              Lane_q_s16_prod2.finLaw_map_pr _ _ _
            _ = (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
              unfold FinLaw.pr
              apply Finset.sum_congr rfl
              intro z hz
              simp [hPassMap z]
        have hrecPos : 0 < (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          rw [← hden]
          exact R.slice_pos C s
        have hnum :
            (∑ z ∈ R.slicePass C s,
              (R.sliceLaw C s).w z * rowSol (records s z)) =
              (Ssol.recLaw PT.parameter).E
                (fun z => if Ssol.AllGood z then rowSol z else 0) := by
          let fVal : R.Value C s → ℝ := fun z =>
            if z ∈ R.slicePass C s then rowSol (records s z) else 0
          calc
            (∑ z ∈ R.slicePass C s,
                (R.sliceLaw C s).w z * rowSol (records s z)) =
              (R.sliceLaw C s).E fVal :=
                (Lane_q_s16_prod2.finLaw_E_finset (R.sliceLaw C s)
                  (R.slicePass C s) (fun z => rowSol (records s z))).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).E fVal := by
              rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => fVal ((records s).symm z)) :=
              Lane_q_s16_prod2.finLaw_map_E _ _ _
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => if Ssol.AllGood z then rowSol z else 0) := by
              congr 1
              funext z
              simp [fVal, hPassMap z]
        have hcondAvg :
            (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
              (R.slice_pos C s)).E (fun z => rowSol (records s z)) =
                Ssol.lowOut PT.parameter gSol y := by
          rw [Lane_q_s16_prod2.finLaw_cond_E]
          rw [hnum, hden]
          simp [SliceSolver.lowOut, rowSol, FinLaw.E]
        have hpi := Q.profiled_valid.low_profile hmode
          (H.geom.cellPatch C) Ssol hsolver gSol y
        calc
          (R.history C).E rowRaw =
              (R.history C).E (fun W => rowSol (records s (W s))) := hsupportAvg
          _ = (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := hcoordAvg
          _ = Ssol.lowOut PT.parameter gSol y := hcondAvg
          _ = (PT.π (H.geom.cellPatch C)).w y := hpi.symm
      · obtain ⟨hnot, hDirectCells⟩ := _hDirect
        let i := H.geom.cellPatch C
        let Y := (PT.tiling.P i).Y
        have hY : Y.Nonempty := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
        have hd : (PT.tiling.P i).d = 1 := by
          cases hmode' : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode'
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode') i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode']; simp [Mode.isCluster]
              exact (hnot hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode'] at hlow
              have hf : False := by simpa [Mode.isLow] using hlow
              exact hf.elim
        obtain ⟨hGroupInjective, _hValues, hSlicePass, hqrawDirect,
          hpretrimDirect, hUDirect, _hPrior⟩ := hDirectCells C
        have hBinSingleton : ∀ D : Bin PT.tiling i, D.1.card = 1 := by
          intro D
          calc
            D.1.card = (PT.tiling.P i).d :=
              Q.profiled_valid.tiling_valid.bins_card i D.1 D.2
            _ = 1 := hd
        let labelOfBin : Bin PT.tiling i → {z : Fin (T.S.N k) // z ∈ Y} := fun D => by
          let z : Fin (T.S.N k) := Classical.choose (Finset.card_eq_one.mp (hBinSingleton D))
          have hset : D.1 = {z} := Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
          have hmemSingleton : z ∈ ({z} : Finset (Fin (T.S.N k))) := Finset.mem_singleton_self z
          have hmem : z ∈ D.1 := by simpa [hset] using hmemSingleton
          exact ⟨z, (PT.tiling.P i).bins.le D.2 hmem⟩
        have hBinSet (D : Bin PT.tiling i) : D.1 = { (labelOfBin D).1 } :=
          Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
        have hlabelInj : Function.Injective labelOfBin := by
          intro D D' hEq
          apply Subtype.ext
          have hval := congrArg Subtype.val hEq
          rw [hBinSet D, hBinSet D']
          simp [hval]
        have hlabelSurj : Function.Surjective labelOfBin := by
          intro z
          have hzCover : z.1 ∈ (PT.tiling.P i).bins.parts.biUnion id := by
            rw [(PT.tiling.P i).bins.biUnion_parts]
            exact z.2
          obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hzCover
          let D : Bin PT.tiling i := ⟨B, hB⟩
          refine ⟨D, ?_⟩
          apply Subtype.ext
          have hzSingle : z.1 ∈ ({ (labelOfBin D).1 } : Finset (Fin (T.S.N k))) := by
            rw [← hBinSet D]
            exact hzB
          exact (Finset.mem_singleton.mp hzSingle).symm
        let binEquiv : Bin PT.tiling i ≃ {z : Fin (T.S.N k) // z ∈ Y} :=
          Equiv.ofBijective labelOfBin ⟨hlabelInj, hlabelSurj⟩
        have hBinCard : (Fintype.card (Bin PT.tiling i) : ℝ) = (Y.card : ℝ) := by
          have hcard : Fintype.card (Bin PT.tiling i) = Y.card := by
            calc
              Fintype.card (Bin PT.tiling i) =
                  Fintype.card {z : Fin (T.S.N k) // z ∈ Y} := Fintype.card_congr binEquiv
              _ = Y.card := by simp [Y]
          exact_mod_cast hcard
        have hlabelCount :
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
              if y ∈ Y then 1 else 0 := by
          calc
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
                ∑ D : Bin PT.tiling i, if y = (labelOfBin D).1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro D hD
              rw [hBinSet D]
              simp [eq_comm]
            _ = ∑ z : {z : Fin (T.S.N k) // z ∈ Y},
                  if y = z.1 then (1 : ℝ) else 0 := by
              exact Fintype.sum_equiv binEquiv
                (fun D => if y = (labelOfBin D).1 then (1 : ℝ) else 0)
                (fun z => if y = z.1 then (1 : ℝ) else 0)
                (by intro D; rfl)
            _ = if y ∈ Y then 1 else 0 := by
              by_cases hy : y ∈ Y
              · simp only [if_pos hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = {⟨y, hy⟩} := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro hz
                    exact Finset.mem_singleton.mpr (Subtype.ext hz.symm)
                  · intro hz
                    exact (congrArg Subtype.val (Finset.mem_singleton.mp hz)).symm
                rw [← Finset.sum_filter, hfilter]
                simp
              · simp only [if_neg hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = ∅ := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro heq
                    exact False.elim (hy (heq.symm ▸ z.2))
                  · intro hfalse
                    cases hfalse
                rw [← Finset.sum_filter, hfilter]
                simp
        have hRawDirect (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
            ∀ D, (R.qin C W (R.groupOf C r)).w D =
              (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ := by
          have hHistoryPos : ∀ t,
              ((FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            intro t hzero
            apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hHistoryPos t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          intro D
          rw [R.qin_eq C W (R.groupOf C r) D hLocalInput]
          rw [hpretrimDirect W (R.groupOf C r)]
          have hsum :
              (∑ D' ∈ (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))),
                (R.qraw C W (R.groupOf C r)).w D') = 1 := by
            simpa using (R.qraw C W (R.groupOf C r)).sum_one
          rw [hsum, hqrawDirect W (R.groupOf C r) D]
          simp [i]
        have hpiLaw : PT.π i = Law.unifCore Y hY :=
          (Q.profiled_valid.law_uniform_direct.resolve_left hnot) i
        rw [hpiLaw]
        let row : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W (R.groupOf C r)).w D * (R.U C W (R.groupOf C r) D).w y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            row W = (Law.unifCore Y hY).w y := by
          intro W hW
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            have hFactor : ∀ t,
                (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t) ≠ 0 := by
              intro t hz
              apply hprod
              exact Finset.prod_eq_zero (Finset.mem_univ t) hz
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hFactor t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          calc
            row W = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) := by
              dsimp [row]
              calc
                (∑ D : Bin PT.tiling (H.geom.cellPatch C), (R.qin C W (R.groupOf C r)).w D *
                    (R.U C W (R.groupOf C r) D).w y) =
                    ∑ D : Bin PT.tiling (H.geom.cellPatch C), (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (if y ∈ D.1 then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro (D : Bin PT.tiling (H.geom.cellPatch C)) hD
                  simpa [hUDirect W (R.groupOf C r) D y] using
                    congrArg (fun q : ℝ => q * (R.U C W (R.groupOf C r) D).w y)
                      (hRawDirect W hW D)
                _ = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (∑ D : Bin PT.tiling (H.geom.cellPatch C),
                        if y ∈ D.1 then (1 : ℝ) else 0) := by
                  rw [← Finset.mul_sum]
            _ = (Law.unifCore Y hY).w y := by
              rw [hlabelCount]
              by_cases hy : y ∈ Y <;> simp [Law.unifCore, hBinCard, hy]
        have hAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) row (fun _ => (Law.unifCore Y hY).w y) hrow
        calc
          (R.history C).E row = (R.history C).E (fun _ => (Law.unifCore Y hY).w y) := hAvg
          _ = (Law.unifCore Y hY).w y := by
            unfold FinLaw.E
            rw [← Finset.sum_mul, (R.history C).sum_one]
            ring
    δperm := δperm
    δgate := δgate
    perm_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
        have hc : 0 < κ.cperm := hκ.cperm_rng.1
        have hprod : 0 < κ.cperm * (T.S.n k : ℝ) := mul_pos hc hnreal
        have harg : -(κ.cperm * (T.S.n k : ℝ)) / 2 < 0 := by linarith
        exact Real.exp_lt_one_iff.mpr harg
    gate_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
        have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
    permission_mass := by
      intro C W g hW
      have h := Lane_q_s16_prod2.permission_mass_explicit_lower
        (Perm.table C) (R.qin C W) (hPerm C W hW) g
      simpa [Perm.rate_eq C, Perm.n_eq C, mul_assoc, mul_comm, mul_left_comm] using h
    pool_normalizer := by
      intro C pool W g ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        exact lt_of_lt_of_le (sub_pos.mpr hexp) hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hnormLower :
          theta * (1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hratioLower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          have habs := abs_le.mp hclose
          linarith
        have hmul := mul_le_mul_of_nonneg_left hratioLower (le_of_lt htheta)
        have heq : theta *
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          field_simp [ne_of_gt htheta]
        rw [heq] at hmul
        exact hmul
      calc
        theta * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          simpa using hnormLower
        _ = zBoth / zPerm := by
          rw [hnormEq]
          exact hzImageEq
        _ = (∑ D' ∈ ((Perm.table C).permitted g ∩ Finset.univ.image pool),
              (R.qin C W g).w D') /
              (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D') := rfl
    gate_mass := by
      intro C pool ht
      have htyp : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let D := Ds.diagnostic C
      have hBad := history_load_gate_concentration D (Ds.load C) pool htyp
      have hfail : (R.history C).pr (fun W => ¬ D.loadGate pool W) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [(Ds.linked C).history_eq pool] at hBad
        simpa [Ds.exponent_half] using hBad.1
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl (R.history C)
        (fun W => D.loadGate pool W)
      have hgateProb : (R.history C).pr (fun W => D.loadGate pool W) =
          ∑ W ∈ S.gate C pool, (R.history C).w W := by
        unfold FinLaw.pr
        rw [← Finset.sum_filter, hGate C pool]
      calc
        1 - Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) ≤
            (R.history C).pr (fun W => D.loadGate pool W) := by
          linarith [hcomp, hfail]
        _ = ∑ W ∈ S.gate C pool, (R.history C).w W := hgateProb
    slot_pos := by
      intro C
      simpa using (Ds.concentration C).slots_pos
    cost_budget := by
      have htails := hCost (T.S.n k) hnCost
      have hnreal : 1 ≤ (T.S.n k : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 8) hn8)
      have hq0 : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
      have hq1 : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnreal (by norm_num)
      simpa [δgate, δperm] using
        (Lane_q_s16_prod2.inverse_three_slacks hq0 hq1
          (by positivity) (by positivity) (by positivity)
          htails.1 htails.2.1 htails.2.2)
  }
  let Link : FreshConstructionLink S F Cal := {
    histories := fun _ => Equiv.refl _
    groups := fun _ => Equiv.refl _
    history_eq := by
      intro C
      change R.history C = FinLaw.map (R.history C) id
      exact (Lane_q_s16_prod2.finLaw_map_id (R.history C)).symm
    group_eq := by intro C r; rfl
    incoming_eq := by intro C W g; rfl
    U_eq := by intro C W g b; rfl
    permission_eq := by intro C g; rfl
    restricted_eq := by intro C pool W g; rfl
    typical_eq := by intro C pool; rfl
    gate_eq := by
      intro C pool
      change S.gate C pool = Finset.image id (S.gate C pool)
      ext W
      simp
    bin_eq := by
      intro C pool W
      change S.binLaw C pool W = FinLaw.map (S.binLaw C pool W) id
      exact (Lane_q_s16_prod2.finLaw_map_id (S.binLaw C pool W)).symm
    label_eq := by
      intro C pool W a
      rfl
    prior_eq := by
      intro C pool W a ys v ht hW ha hys hcell hEven
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hencode : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl, hencode]
      rfl
  }
  exact ⟨F, Cal, ⟨Link⟩⟩

/-- The intended internal validity: exact probability priors at every even
site, with support on common neighbors of its internal odd labels. -/
def InternallyValid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G)
    (Cal : FreshLabelCalibration F) (C : G.Cell) (pool : F.Pool C) (s : F.State C) : Prop :=
  (∀ b, G.cellOf b = C → ¬ IsEvenRole b →
    F.label C s b ∈ Cal.permittedLabels C pool b ∧ poolContainsLabel pool (F.label C s b)) ∧
  ∀ v, G.cellOf v = C → IsEvenRole v →
    (∑ y, F.prior C s v y) = 1 ∧
      ∀ y, F.prior C s v y ≠ 0 → y ∈ PT.envelope (G.cellPatch C) ∧
        ∀ j ∈ PT.tiling.Icoord (G.cellPatch C),
          Hits (T.S.E k) PT.tiling.c y (F.label C s (flipPos v j))

/-- S3's omitted validity assertion is a separate output, preserving the
six existing comparison export types (T16:457–459). Arbitrary fresh states
need not satisfy it; the construction chooses the finite state space. -/
theorem fresh_cell_spec_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      ∃ F : FreshCell H.geom, ∃ Cal : FreshLabelCalibration F,
        Nonempty (FreshConstructionLink S F Cal) ∧
        FreshCell.Spec F (InternallyValid F Cal) Cal.permittedLabels := by
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  obtain ⟨nCost, hCost⟩ := Lane_q_s16_prod2.exp_denominator_slack_cutoff
    κ.cperm hκ.cperm_rng.1
  refine ⟨max (max (max nG nR) 2) (max nCost 8), ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S hSource hn hPerm hTypical hGate
  have hnBase : max (max nG nR) 2 ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hn
  have hn0 : max nG nR ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hnBase
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left nG nR).trans hn0
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right nG nR).trans hn0
  have hn2 : 2 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnBase
  have hnCostBase : max nCost 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hnCost : nCost ≤ T.S.n k := (Nat.le_max_left _ _).trans hnCostBase
  have hn8 : 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnCostBase
  have hFallback : ∀ C : H.geom.Cell,
      ∃ ys : OddCellRole H.geom C → Fin (T.S.N k), Function.Injective ys := by
    intro C
    let D := Ds.diagnostic C
    have hPoolHyp : PoolConcentrationHypotheses D := Ds.concentration C
    have hBad := pool_typicality_concentration_after_permission D hPoolHyp
    have hSmall : D.poolLaw.pr (fun pool => ¬ D.typical pool) < 1 := by
      calc
        D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤
            Real.exp (-(T.S.n k : ℝ) ^ c0) / 2 := hBad.1
        _ < 1 := by
          have hc0 : c0 = 1 / 2 := Ds.exponent_half
          rw [hc0]
          have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
          have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
          have hexp : Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) < 1 :=
            Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
          have hexppos : 0 < Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) := Real.exp_pos _
          linarith
    have hTypicalProb : 0 < D.poolLaw.pr (fun pool => D.typical pool) := by
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl D.poolLaw (fun pool => D.typical pool)
      linarith
    obtain ⟨pool, hDtyp, hPoolW⟩ :=
      Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom D.poolLaw
        (fun pool => D.typical pool) hTypicalProb
    have hStyp : S.typical C pool := (hTypical C pool).2 hDtyp
    have hGatePos : 0 < ∑ W ∈ S.gate C pool, (R.history C).w W := S.gate_pos C pool hStyp
    obtain ⟨W, hWgate, hWpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := S.gate C pool)
        (f := fun W => (R.history C).w W)
        (by intro W hW; exact (R.history C).nonneg W)).mp hGatePos
    have hBinProb : 0 < (S.binLaw C pool W).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨a, _haTrue, ha⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.binLaw C pool W) (fun _ => True) hBinProb
    have hLabelProb : 0 < (S.labelLaw C pool W a).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨ys, _hysTrue, hys⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.labelLaw C pool W a) (fun _ => True) hLabelProb
    exact ⟨ys, S.label_injective C pool W a ys hStyp hWgate (ne_of_gt hWpos) ha hys⟩
  let RawState : H.geom.Cell → Type := fun C =>
    R.Hist C × ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
      (OddCellRole H.geom C → Fin (T.S.N k)))
  let encode := fun (C : H.geom.Cell) (z : RawState C) =>
    if hz : Function.Injective z.2.2 then some z else none
  let defaultLabels : ∀ C : H.geom.Cell, OddCellRole H.geom C → Fin (T.S.N k) :=
    fun C => Classical.choose (hFallback C)
  let gatedHistory : ∀ C : H.geom.Cell, CellPool H.geom C → FinLaw (R.Hist C) :=
    fun C pool => if ht : S.typical C pool then
      FinLaw.cond (R.history C) (S.gate C pool) (S.gate_pos C pool ht) else R.history C
  have hGatedSupport {C : H.geom.Cell} (pool : CellPool H.geom C) (W : R.Hist C)
      (ht : S.typical C pool) (hW : (gatedHistory C pool).w W ≠ 0) :
      W ∈ S.gate C pool ∧ (R.history C).w W ≠ 0 := by
    by_cases hmem : W ∈ S.gate C pool
    · refine ⟨hmem, ?_⟩
      by_contra hzero
      have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem, hzero]
      exact hW hz
    · have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem]
      exact False.elim (hW hz)
  let F : FreshCell H.geom := {
    State := fun C => Option (RawState C)
    fresh := fun C pool =>
      if htyp : S.typical C pool then
        FinLaw.map (FinLaw.bind (gatedHistory C pool)
          (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
          (encode C)
      else FinLaw.dirac none
    fallback := fun _ => none
    label := fun C s b =>
      if hb : H.geom.cellOf b = C ∧ ¬ IsEvenRole b then
        match s with
        | none => defaultLabels C ⟨b, hb⟩
        | some z => if hz : Function.Injective z.2.2 then
            z.2.2 ⟨b, hb⟩ else defaultLabels C ⟨b, hb⟩
      else ⟨0, T.S.N_pos k⟩
    prior := fun C s b y =>
      match s with
      | none => 0
      | some z => R.rawPrior C z.1 z.2.2 b y
    typical := S.typical
  }
  let δperm : ℝ := Real.exp (-(κ.cperm * (T.S.n k : ℝ)) / 2)
  let δgate : ℝ := Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ))
  let Cal : FreshLabelCalibration F := {
    Hist := R.Hist
    Group := R.Group
    groupOf := R.groupOf
    history := R.history
    gatedHistory := gatedHistory
    gate := S.gate
    gate_pos := S.gate_pos
    gated_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp only [gatedHistory, dif_pos ht]
    qin := R.qin
    U := R.U
    U_support := R.U_support
    permitted := fun C g => (Perm.table C).permitted g
    qtilde := K.qtilde
    qtilde_eq := by
      intro C pool W g D ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        have hpos : 0 < 1 - Real.exp (-c * (Perm.table C).n) := sub_pos.mpr hexp
        exact lt_of_lt_of_le hpos hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hzBoth : 0 < zBoth := by
        have hratio' : 0 < zBoth / zPerm := by rw [← hzImageEq]; exact hzImage
        have hmul := mul_pos hratio' hzPerm
        have heq : (zBoth / zPerm) * zPerm = zBoth := div_mul_cancel₀ _ (ne_of_gt hzPerm)
        rw [heq] at hmul
        exact hmul
      have hdenEq :
          (∑ D' ∈ (Perm.table C).permitted g ∩ Finset.image pool Finset.univ,
            (R.qin C W g).w D') = zBoth := by
        simp [zBoth, E, I, Finset.inter_comm]
      have hqtilde := K.qtilde_eq C pool W g D hW (ne_of_gt hzImage)
      rw [hqtilde, hqbar D]
      have hsumQbar : (∑ D' ∈ I, (K.qbar C W g).w D') = zImage := rfl
      rw [hsumQbar, hzImageEq, hdenEq]
      by_cases hDperm : D ∈ E <;> by_cases hDimage : D ∈ I
      · simp [E, I, hDperm, hDimage]
        field_simp [ne_of_gt hzPerm, ne_of_gt hzBoth]
      · have hPermD : D ∈ (Perm.table C).permitted g := by simpa [E] using hDperm
        have hNoPre : ¬ ∃ a, pool a = D := by
          intro hpre
          obtain ⟨a, ha⟩ := hpre
          apply hDimage
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
        simp [hDimage, hNoPre, hPermD]
      · simp [E, I, hDperm, hDimage]
      · simp [E, I, hDperm, hDimage]
    binSampler := S.binLaw
    labelSampler := S.labelLaw
    bin_marginals := by
      intro C pool W g D ht hW
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.bin_marginals C pool W g D ht hGateW hHistW
    label_marginals := by
      intro C pool W a r y ht hW ha
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.label_marginals C pool W a r y ht hGateW hHistW ha
    encode := encode
    fresh_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp [F, gatedHistory, ht, encode]
    label_eq := by
      intro C pool W a ys r ht hW ha hys
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hrole : H.geom.cellOf r.1 = C ∧ ¬ IsEvenRole r.1 := r.2
      simp [F, encode, hinj, hrole]
    raw_profile := by
      intro C r y
      rcases hSource with ⟨hmode, _hUniform, hSourceCell⟩ | _hDirect
      · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
          _hgroupOf, hqraw, hpretrim, hU, _hprior⟩ := hSourceCell C
        let gRaw := R.groupOf C r
        let sourcePair := groups.symm gRaw
        let s := sourcePair.1
        let gSol := sourcePair.2
        have hgroups : groups (s, gSol) = gRaw := by
          dsimp [s, gSol, sourcePair]
          exact groups.apply_symm_apply gRaw
        let rowRaw : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W gRaw).w D * (R.U C W gRaw D).w y
        let rowSol : (∀ t, Ssol.Val t) → ℝ := fun W =>
          ∑ D, Ssol.qin W gSol D * Ssol.U gSol W D y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            rowRaw W = rowSol (records s (W s)) := by
          intro W hW
          have hProd :
              (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            simpa [CellRawData.history, FinLaw.pi] using hW
          have hFactor : ∀ t,
              (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t) ≠ 0 := by
            intro t hzero
            apply hProd
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hcond := hFactor t
            have hpass : W t ∈ R.slicePass C t := by
              by_contra hnot
              apply hcond
              simp [FinLaw.cond, hnot]
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              by_contra hzero
              apply hcond
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          have hqin : ∀ D,
              (R.qin C W gRaw).w D = Ssol.qin (records s (W s)) gSol D := by
            intro D
            rw [← hgroups]
            rw [R.qin_eq C W (groups (s, gSol)) D hLocalInput]
            simp only [SliceSolver.qin, hpretrim W s gSol, hqraw W s gSol]
            by_cases hD : D ∈ Ssol.pretrimBins (records s (W s)) gSol <;> simp [hD]
          have hUeq : ∀ D,
              (R.U C W gRaw D).w y = Ssol.U gSol (records s (W s)) D y := by
            intro D
            rw [← hgroups]
            exact hU W s gSol D y
          dsimp [rowRaw, rowSol]
          apply Finset.sum_congr rfl
          intro D hD
          rw [hqin D, hUeq D]
        have hsupportAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) rowRaw (fun W => rowSol (records s (W s))) hrow
        have hcoordAvg :
            (R.history C).E (fun W => rowSol (records s (W s))) =
              (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := by
          simpa [CellRawData.history] using
            (Lane_q_s16_prod2.finLaw_pi_E_coordinate
              (fun t => FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)) s (fun z => rowSol (records s z)))
        have hPassMap : ∀ z,
            ((records s).symm z ∈ R.slicePass C s) ↔ Ssol.AllGood z := by
          intro z
          simpa using hslicePass s ((records s).symm z)
        have hsliceMap : R.sliceLaw C s =
            FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm := hsliceLaw s
        have hden :
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
              (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          calc
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
                (R.sliceLaw C s).pr (fun z => z ∈ R.slicePass C s) :=
              (Lane_q_s16_prod2.finLaw_pr_finset (R.sliceLaw C s)
                (R.slicePass C s)).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).pr
                  (fun z => z ∈ R.slicePass C s) := by rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).pr
                  (fun z => (records s).symm z ∈ R.slicePass C s) :=
              Lane_q_s16_prod2.finLaw_map_pr _ _ _
            _ = (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
              unfold FinLaw.pr
              apply Finset.sum_congr rfl
              intro z hz
              simp [hPassMap z]
        have hrecPos : 0 < (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          rw [← hden]
          exact R.slice_pos C s
        have hnum :
            (∑ z ∈ R.slicePass C s,
              (R.sliceLaw C s).w z * rowSol (records s z)) =
              (Ssol.recLaw PT.parameter).E
                (fun z => if Ssol.AllGood z then rowSol z else 0) := by
          let fVal : R.Value C s → ℝ := fun z =>
            if z ∈ R.slicePass C s then rowSol (records s z) else 0
          calc
            (∑ z ∈ R.slicePass C s,
                (R.sliceLaw C s).w z * rowSol (records s z)) =
              (R.sliceLaw C s).E fVal :=
                (Lane_q_s16_prod2.finLaw_E_finset (R.sliceLaw C s)
                  (R.slicePass C s) (fun z => rowSol (records s z))).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).E fVal := by
              rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => fVal ((records s).symm z)) :=
              Lane_q_s16_prod2.finLaw_map_E _ _ _
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => if Ssol.AllGood z then rowSol z else 0) := by
              congr 1
              funext z
              simp [fVal, hPassMap z]
        have hcondAvg :
            (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
              (R.slice_pos C s)).E (fun z => rowSol (records s z)) =
                Ssol.lowOut PT.parameter gSol y := by
          rw [Lane_q_s16_prod2.finLaw_cond_E]
          rw [hnum, hden]
          simp [SliceSolver.lowOut, rowSol, FinLaw.E]
        have hpi := Q.profiled_valid.low_profile hmode
          (H.geom.cellPatch C) Ssol hsolver gSol y
        calc
          (R.history C).E rowRaw =
              (R.history C).E (fun W => rowSol (records s (W s))) := hsupportAvg
          _ = (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := hcoordAvg
          _ = Ssol.lowOut PT.parameter gSol y := hcondAvg
          _ = (PT.π (H.geom.cellPatch C)).w y := hpi.symm
      · obtain ⟨hnot, hDirectCells⟩ := _hDirect
        let i := H.geom.cellPatch C
        let Y := (PT.tiling.P i).Y
        have hY : Y.Nonempty := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
        have hd : (PT.tiling.P i).d = 1 := by
          cases hmode' : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode'
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode') i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode']; simp [Mode.isCluster]
              exact (hnot hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode'] at hlow
              have hf : False := by simpa [Mode.isLow] using hlow
              exact hf.elim
        obtain ⟨hGroupInjective, _hValues, hSlicePass, hqrawDirect,
          hpretrimDirect, hUDirect, _hPrior⟩ := hDirectCells C
        have hBinSingleton : ∀ D : Bin PT.tiling i, D.1.card = 1 := by
          intro D
          calc
            D.1.card = (PT.tiling.P i).d :=
              Q.profiled_valid.tiling_valid.bins_card i D.1 D.2
            _ = 1 := hd
        let labelOfBin : Bin PT.tiling i → {z : Fin (T.S.N k) // z ∈ Y} := fun D => by
          let z : Fin (T.S.N k) := Classical.choose (Finset.card_eq_one.mp (hBinSingleton D))
          have hset : D.1 = {z} := Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
          have hmemSingleton : z ∈ ({z} : Finset (Fin (T.S.N k))) := Finset.mem_singleton_self z
          have hmem : z ∈ D.1 := by simpa [hset] using hmemSingleton
          exact ⟨z, (PT.tiling.P i).bins.le D.2 hmem⟩
        have hBinSet (D : Bin PT.tiling i) : D.1 = { (labelOfBin D).1 } :=
          Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
        have hlabelInj : Function.Injective labelOfBin := by
          intro D D' hEq
          apply Subtype.ext
          have hval := congrArg Subtype.val hEq
          rw [hBinSet D, hBinSet D']
          simp [hval]
        have hlabelSurj : Function.Surjective labelOfBin := by
          intro z
          have hzCover : z.1 ∈ (PT.tiling.P i).bins.parts.biUnion id := by
            rw [(PT.tiling.P i).bins.biUnion_parts]
            exact z.2
          obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hzCover
          let D : Bin PT.tiling i := ⟨B, hB⟩
          refine ⟨D, ?_⟩
          apply Subtype.ext
          have hzSingle : z.1 ∈ ({ (labelOfBin D).1 } : Finset (Fin (T.S.N k))) := by
            rw [← hBinSet D]
            exact hzB
          exact (Finset.mem_singleton.mp hzSingle).symm
        let binEquiv : Bin PT.tiling i ≃ {z : Fin (T.S.N k) // z ∈ Y} :=
          Equiv.ofBijective labelOfBin ⟨hlabelInj, hlabelSurj⟩
        have hBinCard : (Fintype.card (Bin PT.tiling i) : ℝ) = (Y.card : ℝ) := by
          have hcard : Fintype.card (Bin PT.tiling i) = Y.card := by
            calc
              Fintype.card (Bin PT.tiling i) =
                  Fintype.card {z : Fin (T.S.N k) // z ∈ Y} := Fintype.card_congr binEquiv
              _ = Y.card := by simp [Y]
          exact_mod_cast hcard
        have hlabelCount :
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
              if y ∈ Y then 1 else 0 := by
          calc
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
                ∑ D : Bin PT.tiling i, if y = (labelOfBin D).1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro D hD
              rw [hBinSet D]
              simp [eq_comm]
            _ = ∑ z : {z : Fin (T.S.N k) // z ∈ Y},
                  if y = z.1 then (1 : ℝ) else 0 := by
              exact Fintype.sum_equiv binEquiv
                (fun D => if y = (labelOfBin D).1 then (1 : ℝ) else 0)
                (fun z => if y = z.1 then (1 : ℝ) else 0)
                (by intro D; rfl)
            _ = if y ∈ Y then 1 else 0 := by
              by_cases hy : y ∈ Y
              · simp only [if_pos hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = {⟨y, hy⟩} := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro hz
                    exact Finset.mem_singleton.mpr (Subtype.ext hz.symm)
                  · intro hz
                    exact (congrArg Subtype.val (Finset.mem_singleton.mp hz)).symm
                rw [← Finset.sum_filter, hfilter]
                simp
              · simp only [if_neg hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = ∅ := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro heq
                    exact False.elim (hy (heq.symm ▸ z.2))
                  · intro hfalse
                    cases hfalse
                rw [← Finset.sum_filter, hfilter]
                simp
        have hRawDirect (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
            ∀ D, (R.qin C W (R.groupOf C r)).w D =
              (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ := by
          have hHistoryPos : ∀ t,
              ((FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            intro t hzero
            apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hHistoryPos t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          intro D
          rw [R.qin_eq C W (R.groupOf C r) D hLocalInput]
          rw [hpretrimDirect W (R.groupOf C r)]
          have hsum :
              (∑ D' ∈ (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))),
                (R.qraw C W (R.groupOf C r)).w D') = 1 := by
            simpa using (R.qraw C W (R.groupOf C r)).sum_one
          rw [hsum, hqrawDirect W (R.groupOf C r) D]
          simp [i]
        have hpiLaw : PT.π i = Law.unifCore Y hY :=
          (Q.profiled_valid.law_uniform_direct.resolve_left hnot) i
        rw [hpiLaw]
        let row : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W (R.groupOf C r)).w D * (R.U C W (R.groupOf C r) D).w y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            row W = (Law.unifCore Y hY).w y := by
          intro W hW
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            have hFactor : ∀ t,
                (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t) ≠ 0 := by
              intro t hz
              apply hprod
              exact Finset.prod_eq_zero (Finset.mem_univ t) hz
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hFactor t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          calc
            row W = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) := by
              dsimp [row]
              calc
                (∑ D : Bin PT.tiling (H.geom.cellPatch C), (R.qin C W (R.groupOf C r)).w D *
                    (R.U C W (R.groupOf C r) D).w y) =
                    ∑ D : Bin PT.tiling (H.geom.cellPatch C), (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (if y ∈ D.1 then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro (D : Bin PT.tiling (H.geom.cellPatch C)) hD
                  simpa [hUDirect W (R.groupOf C r) D y] using
                    congrArg (fun q : ℝ => q * (R.U C W (R.groupOf C r) D).w y)
                      (hRawDirect W hW D)
                _ = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (∑ D : Bin PT.tiling (H.geom.cellPatch C),
                        if y ∈ D.1 then (1 : ℝ) else 0) := by
                  rw [← Finset.mul_sum]
            _ = (Law.unifCore Y hY).w y := by
              rw [hlabelCount]
              by_cases hy : y ∈ Y <;> simp [Law.unifCore, hBinCard, hy]
        have hAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) row (fun _ => (Law.unifCore Y hY).w y) hrow
        calc
          (R.history C).E row = (R.history C).E (fun _ => (Law.unifCore Y hY).w y) := hAvg
          _ = (Law.unifCore Y hY).w y := by
            unfold FinLaw.E
            rw [← Finset.sum_mul, (R.history C).sum_one]
            ring
    δperm := δperm
    δgate := δgate
    perm_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
        have hc : 0 < κ.cperm := hκ.cperm_rng.1
        have hprod : 0 < κ.cperm * (T.S.n k : ℝ) := mul_pos hc hnreal
        have harg : -(κ.cperm * (T.S.n k : ℝ)) / 2 < 0 := by linarith
        exact Real.exp_lt_one_iff.mpr harg
    gate_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
        have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
    permission_mass := by
      intro C W g hW
      have h := Lane_q_s16_prod2.permission_mass_explicit_lower
        (Perm.table C) (R.qin C W) (hPerm C W hW) g
      simpa [Perm.rate_eq C, Perm.n_eq C, mul_assoc, mul_comm, mul_left_comm] using h
    pool_normalizer := by
      intro C pool W g ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        exact lt_of_lt_of_le (sub_pos.mpr hexp) hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hnormLower :
          theta * (1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hratioLower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          have habs := abs_le.mp hclose
          linarith
        have hmul := mul_le_mul_of_nonneg_left hratioLower (le_of_lt htheta)
        have heq : theta *
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          field_simp [ne_of_gt htheta]
        rw [heq] at hmul
        exact hmul
      calc
        theta * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          simpa using hnormLower
        _ = zBoth / zPerm := by
          rw [hnormEq]
          exact hzImageEq
        _ = (∑ D' ∈ ((Perm.table C).permitted g ∩ Finset.univ.image pool),
              (R.qin C W g).w D') /
              (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D') := rfl
    gate_mass := by
      intro C pool ht
      have htyp : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let D := Ds.diagnostic C
      have hBad := history_load_gate_concentration D (Ds.load C) pool htyp
      have hfail : (R.history C).pr (fun W => ¬ D.loadGate pool W) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [(Ds.linked C).history_eq pool] at hBad
        simpa [Ds.exponent_half] using hBad.1
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl (R.history C)
        (fun W => D.loadGate pool W)
      have hgateProb : (R.history C).pr (fun W => D.loadGate pool W) =
          ∑ W ∈ S.gate C pool, (R.history C).w W := by
        unfold FinLaw.pr
        rw [← Finset.sum_filter, hGate C pool]
      calc
        1 - Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) ≤
            (R.history C).pr (fun W => D.loadGate pool W) := by
          linarith [hcomp, hfail]
        _ = ∑ W ∈ S.gate C pool, (R.history C).w W := hgateProb
    slot_pos := by
      intro C
      simpa using (Ds.concentration C).slots_pos
    cost_budget := by
      have htails := hCost (T.S.n k) hnCost
      have hnreal : 1 ≤ (T.S.n k : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 8) hn8)
      have hq0 : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
      have hq1 : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnreal (by norm_num)
      simpa [δgate, δperm] using
        (Lane_q_s16_prod2.inverse_three_slacks hq0 hq1
          (by positivity) (by positivity) (by positivity)
          htails.1 htails.2.1 htails.2.2)
  }
  let Link : FreshConstructionLink S F Cal := {
    histories := fun _ => Equiv.refl _
    groups := fun _ => Equiv.refl _
    history_eq := by
      intro C
      change R.history C = FinLaw.map (R.history C) id
      exact (Lane_q_s16_prod2.finLaw_map_id (R.history C)).symm
    group_eq := by intro C r; rfl
    incoming_eq := by intro C W g; rfl
    U_eq := by intro C W g b; rfl
    permission_eq := by intro C g; rfl
    restricted_eq := by intro C pool W g; rfl
    typical_eq := by intro C pool; rfl
    gate_eq := by
      intro C pool
      change S.gate C pool = Finset.image id (S.gate C pool)
      ext W
      simp
    bin_eq := by
      intro C pool W
      change S.binLaw C pool W = FinLaw.map (S.binLaw C pool W) id
      exact (Lane_q_s16_prod2.finLaw_map_id (S.binLaw C pool W)).symm
    label_eq := by
      intro C pool W a
      rfl
    prior_eq := by
      intro C pool W a ys v ht hW ha hys hcell hEven
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hencode : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl, hencode]
      rfl
  }
  let Spec : FreshCell.Spec F (InternallyValid F Cal) Cal.permittedLabels := {
    fresh_valid := by
      intro C pool s ht hs
      change S.typical C pool at ht
      let sourceLaw := FinLaw.bind (gatedHistory C pool) fun W =>
        FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)
      rw [Cal.fresh_eq C pool ht] at hs
      obtain ⟨src, henc, hsrcPos⟩ :=
        Lane_q_s16_prod2.finLaw_map_nonzero_preimage sourceLaw (encode C) s (ne_of_gt hs)
      rcases src with ⟨W, ab⟩
      rcases ab with ⟨a, ys⟩
      have hGatePos : (gatedHistory C pool).w W ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      have hBinPos : (S.binLaw C pool W).w a ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      have hLabelPos : (S.labelLaw C pool W a).w ys ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      obtain ⟨hGateW, hHistPos⟩ := hGatedSupport pool W ht hGatePos
      have hinj := S.label_injective C pool W a ys ht hGateW hHistPos hBinPos hLabelPos
      have hEncEq : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      have hStateEq : s = some (W, (a, ys)) := henc.symm.trans hEncEq
      subst s
      refine ⟨?_, ?_⟩
      · intro b hcell hodd
        let r : OddCellRole H.geom C := ⟨b, ⟨hcell, hodd⟩⟩
        let g := Cal.groupOf C r
        let D := a g
        have hBinAtomPos : 0 < (S.binLaw C pool W).w a :=
          lt_of_le_of_ne ((S.binLaw C pool W).nonneg a) (Ne.symm hBinPos)
        have hBinEvent := Lane_q_s16_prod2.finLaw_weight_le_pr
          (S.binLaw C pool W) (fun a' => a' g = D) a rfl
        have hQtildePos : 0 < (K.qtilde C pool W g).w D := by
          have hPrPos : 0 < (S.binLaw C pool W).pr (fun a' => a' g = D) :=
            lt_of_lt_of_le hBinAtomPos hBinEvent
          rw [S.bin_marginals C pool W g D ht hGateW hHistPos] at hPrPos
          exact hPrPos
        have hAllowedPool : D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image pool := by
          by_cases hmem : D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image pool
          · exact hmem
          · have hzero : (K.qtilde C pool W g).w D = 0 := by
              rw [Cal.qtilde_eq C pool W g D ht hHistPos]
              rcases not_and_or.mp hmem with hnotPerm | hnotPool
              · simp [hnotPerm]
              · simp [hnotPool]
            exact False.elim (ne_of_gt hQtildePos hzero)
        have hUPos : (R.U C W g D).w (ys r) ≠ 0 := by
          have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr
            (S.labelLaw C pool W a) (fun y' => y' r = ys r) ys rfl
          have hLabelAtomPos : 0 < (S.labelLaw C pool W a).w ys :=
            lt_of_le_of_ne ((S.labelLaw C pool W a).nonneg ys) (Ne.symm hLabelPos)
          have hPrPos : 0 < (S.labelLaw C pool W a).pr (fun y' => y' r = ys r) :=
            lt_of_lt_of_le hLabelAtomPos hAtom
          have hMarg := S.label_marginals C pool W a r (ys r)
            ht hGateW hHistPos hBinPos
          rw [hMarg] at hPrPos
          exact ne_of_gt hPrPos
        have hLabelInBin : ys r ∈ D.1 := R.U_support C W g D (ys r) hUPos
        obtain ⟨slot, hslot, hslotEq⟩ := Finset.mem_image.mp hAllowedPool.2
        have hpoolContains : poolContainsLabel pool (ys r) := by
          refine ⟨slot, ?_⟩
          simpa [hslotEq] using hLabelInBin
        have hpermitted : ys r ∈ Cal.permittedLabels C pool b := by
          have hrole : H.geom.cellOf b = C ∧ ¬ IsEvenRole b := ⟨hcell, hodd⟩
          simp only [FreshLabelCalibration.permittedLabels, hrole, dite_true]
          exact Finset.mem_biUnion.mpr ⟨D, hAllowedPool.1, hLabelInBin⟩
        have hFLabel : F.label C (some (W, (a, ys))) b = ys r := by
          simp [F, r, hcell, hodd, hinj]
        rw [hEncEq, hFLabel]
        exact ⟨hpermitted, hpoolContains⟩
      · intro v hcell hEven
        by_cases hcluster : PT.tiling.mode.isCluster
        · rcases hSource with ⟨hsourceMode, _hUniform, hSourceCell⟩ | ⟨hnot, _hDirectCells⟩
          · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
              _hGroupOf, _hqraw, _hpretrim, _hU, hPriorLink⟩ := hSourceCell C
            let sourcePair := (R.cellWords C).symm ⟨v, hcell⟩
            let sourceSlice := sourcePair.1
            let word := sourcePair.2
            have hCellWord : R.cellWords C (sourceSlice, word) = ⟨v, hcell⟩ := by
              dsimp [sourceSlice, word, sourcePair]
              exact Equiv.apply_symm_apply (R.cellWords C) ⟨v, hcell⟩
            have hCellWordVal : (R.cellWords C (sourceSlice, word)).1 = v :=
              congrArg Subtype.val hCellWord
            have hEvenWord : IsEvenRole word := by
              have hpar := R.word_parity hcluster C sourceSlice word
              rw [hCellWord] at hpar
              exact hpar.mp hEven
            let w : EvenRole PT.tiling (H.geom.cellPatch C) := ⟨word, hEvenWord⟩
            let ev : EvenCellRole H.geom C := ⟨v, ⟨hcell, hEven⟩⟩
            obtain ⟨L, hFeasible⟩ :=
              S.cluster_label_feasible C pool W a ht hGateW hHistPos hBinPos hcluster
            have hSafe : L.problem.safe ys := hFeasible.1 ys hLabelPos
            have hRawRowPos : R.rawPrior C W ys v ≠ 0 := by
              intro hz
              have hbad : L.problem.starBad ev ys :=
                (L.tests_eq ev ys).2 ⟨hcluster, hz⟩
              exact hSafe.2 ev hbad
            let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
            have hPriorEq := hPriorLink W sourceSlice w ys fallback
            rw [hCellWordVal] at hPriorEq
            have hSigmaPos :
                Ssol.σ w (records sourceSlice (W sourceSlice))
                  (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) ≠ 0 := by
              intro hz
              apply hRawRowPos
              rw [hPriorEq]
              exact hz
            have hHistProd :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hHistPos
            have hSlicePos : (R.sliceLaw C sourceSlice).w (W sourceSlice) ≠ 0 := by
              have hcond :
                  (FinLaw.cond (R.sliceLaw C sourceSlice) (R.slicePass C sourceSlice)
                    (R.slice_pos C sourceSlice)).w (W sourceSlice) ≠ 0 := by
                intro hz
                apply hHistProd
                exact Finset.prod_eq_zero (Finset.mem_univ sourceSlice) hz
              have hpass : W sourceSlice ∈ R.slicePass C sourceSlice := by
                by_contra hnotPass
                apply hcond
                simp [FinLaw.cond, hnotPass]
              intro hz
              apply hcond
              simp [FinLaw.cond, hpass, hz]
            have hMapPos :
                (FinLaw.map (Ssol.recLaw PT.parameter) (records sourceSlice).symm).w
                  (W sourceSlice) ≠ 0 := by
              rw [← hsliceLaw sourceSlice]
              exact hSlicePos
            obtain ⟨record, hRecordMap, hRecordPos⟩ :=
              Lane_q_s16_prod2.finLaw_map_nonzero_preimage
                (Ssol.recLaw PT.parameter) (records sourceSlice).symm
                (W sourceSlice) hMapPos
            have hRecordEq : record = records sourceSlice (W sourceSlice) := by
              calc
                record = records sourceSlice ((records sourceSlice).symm record) :=
                  (records sourceSlice).apply_symm_apply record |>.symm
                _ = records sourceSlice (W sourceSlice) := by rw [hRecordMap]
            have hRecordPos' :
                (Ssol.recLaw PT.parameter).w (records sourceSlice (W sourceSlice)) ≠ 0 := by
              rw [← hRecordEq]
              exact hRecordPos
            have hRecordPositive :
                0 < (Ssol.recLaw PT.parameter).w (records sourceSlice (W sourceSlice)) :=
              lt_of_le_of_ne
                ((Ssol.recLaw PT.parameter).nonneg (records sourceSlice (W sourceSlice)))
                (Ne.symm hRecordPos')
            obtain ⟨activeVertex, hActive, hSigmaSupport⟩ :=
              Ssol.σ_support w (records sourceSlice (W sourceSlice))
                (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) hSigmaPos
            have hActivePos : 0 < PT.mesh.wt activeVertex PT.parameter :=
              hActive PT.parameter (by simpa [SliceSolver.recLaw] using hRecordPositive)
            have hActiveMem : activeVertex ∈ PT.activeVertices := by
              simp [ProfiledTiling.activeVertices, hActivePos]
            have hPriorEqFun (y : Fin (T.S.N k)) :
                F.prior C (encode C (W, (a, ys))) v y =
                  Ssol.σ w (records sourceSlice (W sourceSlice))
                    (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y := by
              rw [hEncEq]
              change R.rawPrior C W ys v y = _
              exact congrFun hPriorEq y
            constructor
            · calc
                (∑ y, F.prior C (encode C (W, (a, ys))) v y) =
                    ∑ y, Ssol.σ w (records sourceSlice (W sourceSlice))
                      (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  exact hPriorEqFun y
                _ = 1 := Ssol.σ_prob w (records sourceSlice (W sourceSlice))
                  (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) hSigmaPos
            · intro y hy
              have hSigmaY :
                  Ssol.σ w (records sourceSlice (W sourceSlice))
                    (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y ≠ 0 := by
                rw [← hPriorEqFun y]
                exact hy
              obtain ⟨hCorner, hHits⟩ := hSigmaSupport y hSigmaY
              have hEnvelope : y ∈ PT.envelope (H.geom.cellPatch C) := by
                rw [Q.profiled_valid.envelope_eq (H.geom.cellPatch C)]
                exact Finset.mem_biUnion.mpr ⟨activeVertex, hActiveMem, hCorner⟩
              refine ⟨hEnvelope, ?_⟩
              intro j hj
              have hAxisMem : j ∈ Finset.univ.image (R.axis C) := by
                rw [R.axes_eq C]
                exact hj
              obtain ⟨l, _hl, hAxis⟩ := Finset.mem_image.mp hAxisMem
              have hFlipWord := R.word_flip C sourceSlice word l
              rw [hCellWordVal] at hFlipWord
              rw [hAxis] at hFlipWord
              have hOddInternal : ¬ IsEvenRole (flipPos word l) := by
                intro hflip
                exact (HypercubeRamsey.S15.evenRole_flipPos word l).mp hflip hEvenWord
              have hParityFlip := R.word_parity hcluster C sourceSlice (flipPos word l)
              have hOddCellWord : ¬ IsEvenRole
                  ((R.cellWords C (sourceSlice, flipPos word l)).1) := by
                intro heven
                exact hOddInternal (hParityFlip.mp heven)
              have hCellFlip : H.geom.cellOf (flipPos v j) = C := by
                have hc := (R.cellWords C (sourceSlice, flipPos word l)).2
                rw [hFlipWord] at hc
                exact hc
              have hOddFlip : ¬ IsEvenRole (flipPos v j) := by
                have ho := hOddCellWord
                rw [hFlipWord] at ho
                exact ho
              let roleFlip : OddCellRole H.geom C :=
                ⟨flipPos v j, ⟨hCellFlip, hOddFlip⟩⟩
              have hWordLabel :
                  R.wordLabel C ys sourceSlice fallback (flipPos word l) = ys roleFlip := by
                simp [CellRawData.wordLabel, hOddFlip, hFlipWord, roleFlip]
              have hCalLabel := Cal.label_eq C pool W a ys roleFlip
                ht hGatePos hBinPos hLabelPos
              rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl] at hCalLabel
              have hLabelsEq :
                  F.label C (encode C (W, (a, ys))) (flipPos v j) =
                    R.wordLabel C ys sourceSlice fallback (flipPos word l) := by
                exact hCalLabel.trans hWordLabel.symm
              rw [hLabelsEq]
              exact hHits l
          · exact False.elim (hnot hcluster)
        · rcases hSource with ⟨hmode, _hUniform, _hSourceCell⟩ | ⟨hnot, hDirectData⟩
          · have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
            exact False.elim (hcluster hc)
          · obtain ⟨_, _, _, _, _, _, hEnvExists⟩ := hDirectData C
            obtain ⟨hEnv, hPrior⟩ := hEnvExists
            have hHeightZero : (PT.tiling.P (H.geom.cellPatch C)).h = 0 := by
              cases hmode : PT.tiling.mode with
              | bounded =>
                  have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
                  exact (hdata.2 (H.geom.cellPatch C)).2.1
              | lowDirect =>
                  have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode)
                    (H.geom.cellPatch C)
                  exact hdata.2.2.2.2.1
              | lowCluster =>
                  have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
                  exact (hnot hc).elim
              | highDirect | highSmall | highLarge =>
                  have hlow := Q.mode_low
                  rw [hmode] at hlow
                  have hf : False := by simpa [Mode.isLow] using hlow
                  exact hf.elim
            have hIcoord : PT.tiling.Icoord (H.geom.cellPatch C) = ∅ := by
              ext j
              simp [Tiling.Icoord, topCoordinates, hHeightZero]
            have hPriorFun (y : Fin (T.S.N k)) :
                F.prior C (encode C (W, (a, ys))) v y =
                  (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).w y := by
              rw [hEncEq]
              change R.rawPrior C W ys v y = _
              exact congrFun (hPrior W ys v hcell hEven) y
            constructor
            · calc
                (∑ y, F.prior C (encode C (W, (a, ys))) v y) =
                    ∑ y, (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).w y := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  exact hPriorFun y
                _ = 1 := (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).sum_eq_one
            · intro y hy
              have hEnvY : y ∈ PT.envelope (H.geom.cellPatch C) := by
                rw [hPriorFun y] at hy
                by_contra hnotEnv
                apply hy
                simp [Law.unifCore, hnotEnv]
              refine ⟨hEnvY, ?_⟩
              intro j hj
              rw [hIcoord] at hj
              simp at hj
    fresh_atypical := by
      intro C pool hnot
      change ¬ S.typical C pool at hnot
      change (if ht : S.typical C pool then
          FinLaw.map (FinLaw.bind (gatedHistory C pool)
            (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
            (encode C) else FinLaw.dirac none) = FinLaw.dirac none
      by_cases ht : S.typical C pool
      · exact (hnot ht).elim
      · simp [ht]
    label_permitted := by
      intro C pool s b hvalid hcell hodd
      exact (hvalid.1 b hcell hodd).1
    labels_injective := by
      intro C s b b' hcell hcell' hodd hodd' hne
      let rb : OddCellRole H.geom C := ⟨b, ⟨hcell, hodd⟩⟩
      let rb' : OddCellRole H.geom C := ⟨b', ⟨hcell', hodd'⟩⟩
      intro hlabels
      cases s with
      | none =>
          have hvals : defaultLabels C rb = defaultLabels C rb' := by
            simpa [F, rb, rb', hcell, hodd, hcell', hodd'] using hlabels
          have hinj := Classical.choose_spec (hFallback C)
          exact hne (congrArg Subtype.val (hinj hvals))
      | some z =>
          by_cases hz : Function.Injective z.2.2
          · have hvals : z.2.2 rb = z.2.2 rb' := by
              simpa [F, rb, rb', hcell, hodd, hcell', hodd', hz] using hlabels
            exact hne (congrArg Subtype.val (hz hvals))
          · have hvals : defaultLabels C rb = defaultLabels C rb' := by
              simpa [F, rb, rb', hcell, hodd, hcell', hodd', hz] using hlabels
            have hinj := Classical.choose_spec (hFallback C)
            exact hne (congrArg Subtype.val (hinj hvals))
    prior_nonneg := by
      intro C s b y
      cases s with
      | none => simp [F]
      | some z => exact R.prior_nonneg C z.1 z.2.2 b y
    prior_subprob := by
      intro C s b
      cases s with
      | none => simp [F]
      | some z => exact R.prior_subprob C z.1 z.2.2 b
  }
  exact ⟨F, Cal, ⟨Link⟩, Spec⟩
set_option maxHeartbeats 2000000 in
/-- S3 prior pipeline producer (T16:513–529). It uses the same fresh state,
calibrated stages and raw readout as the singleton construction; the source
identity and the equality of base expectations are outputs. -/
theorem fresh_prior_pipeline_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K)
      (F : FreshCell H.geom) (Cal : FreshLabelCalibration F),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      FreshConstructionLink S F Cal →
      ∀ C v, H.geom.cellOf v = C → IsEvenRole v →
      ∃ P : FreshPriorPipeline F C v, FreshPriorSourceValid P ∧
        ∀ Φ, P.baseExperiment.expect Φ = (R.baseExperiment C v).expect Φ := by
  classical
  refine ⟨2, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S F Cal hSource hn hPerm
    hTypical hGate hLink C v hcell hEven
  rcases hSource with hCluster | ⟨hDirect, hDirectData⟩
  · rcases hCluster with ⟨hmode, hUniform, hSourceCell⟩
    obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
      hgroupReadout, hqraw, hpretrim, hU, hpriorReadout⟩ := hSourceCell C
    let sourcePair := (R.cellWords C).symm ⟨v, hcell⟩
    let sourceSlice := sourcePair.1
    let word := sourcePair.2
    have hCellWord : R.cellWords C (sourceSlice, word) = ⟨v, hcell⟩ := by
      dsimp [sourceSlice, word, sourcePair]
      exact Equiv.apply_symm_apply (R.cellWords C) ⟨v, hcell⟩
    have hCellWordVal : (R.cellWords C (sourceSlice, word)).1 = v :=
      congrArg Subtype.val hCellWord
    have hClusterMode : PT.tiling.mode.isCluster := by
      rw [hmode]
      simp [Mode.isCluster]
    have hEvenWord : IsEvenRole word := by
      have hpar := R.word_parity hClusterMode C sourceSlice word
      rw [hCellWord] at hpar
      exact hpar.mp hEven
    let w : EvenRole PT.tiling (H.geom.cellPatch C) := ⟨word, hEvenWord⟩
    let loc : SliceStarLocation H.geom C v w := {
      axis := R.axis C
      axis_injective := R.axis_injective C
      axes_eq := R.axes_eq C
      embed := fun z => (R.cellWords C (sourceSlice, z)).1
      site_eq := hCellWordVal
      flip_eq := by
        intro z j
        exact R.word_flip C sourceSlice z j
      outer_eq := by
        intro z j hj
        have hout := R.word_outer C sourceSlice z word j hj
        rw [hCellWordVal] at hout
        exact hout
    }
    have hStarCell (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) :
        H.geom.cellOf (flipPos v (R.axis C j)) = C := by
      have hflip := R.word_flip C sourceSlice word j
      rw [hCellWordVal] at hflip
      have hmem := (R.cellWords C (sourceSlice, flipPos word j)).2
      rw [hflip] at hmem
      exact hmem
    have hStarOdd (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) :
        ¬ IsEvenRole (flipPos v (R.axis C j)) := by
      have hInternalOdd : ¬ IsEvenRole (flipPos word j) := by
        intro heven
        exact ((HypercubeRamsey.S15.evenRole_flipPos word j).mp heven) hEvenWord
      have hflip := R.word_flip C sourceSlice word j
      rw [hCellWordVal] at hflip
      have hParity := R.word_parity hClusterMode C sourceSlice (flipPos word j)
      rw [hflip] at hParity
      intro heven
      exact hInternalOdd (hParity.mp heven)
    let starRole (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) : OddCellRole H.geom C :=
      ⟨flipPos v (R.axis C j), ⟨hStarCell j, hStarOdd j⟩⟩
    let roleScope : Finset (OddCellRole H.geom C) := Finset.univ.image starRole
    let groupScope : Finset (Cal.Group C) := roleScope.image (Cal.groupOf C)
    have hScopesClosed : ∀ r ∈ roleScope, Cal.groupOf C r ∈ groupScope := by
      intro r hr
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    let recordsLocal : R.Hist C → (∀ r, Ssol.Val r) :=
      fun W => records sourceSlice (W sourceSlice)
    have hPriorIdentity (W : R.Hist C) (ys : OddCellRole H.geom C → Fin (T.S.N k)) :
        R.rawPrior C W ys v =
          Ssol.σ w (recordsLocal W) (fun j => ys (starRole j)) := by
      let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
      have hread := hpriorReadout W sourceSlice w ys fallback
      rw [hCellWordVal] at hread
      have hlabels :
          nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback) = fun j => ys (starRole j) := by
        funext j
        have hflip := R.word_flip C sourceSlice word j
        rw [hCellWordVal] at hflip
        have hOddCellWord :
            ¬ IsEvenRole ((R.cellWords C (sourceSlice, flipPos word j)).1) := by
          rw [hflip]
          exact hStarOdd j
        simp only [nbrLabels, w]
        change R.wordLabel C ys sourceSlice fallback (flipPos word j) = ys (starRole j)
        unfold CellRawData.wordLabel
        rw [dif_pos hOddCellWord]
        apply congrArg ys
        apply Subtype.ext
        exact hflip
      rw [hread, hlabels]
    let rawFactors : ∀ s : R.Slice C, FinLaw (R.Value C s) := fun s =>
      if hs : s = sourceSlice then hs.symm ▸ R.sliceLaw C sourceSlice else
        FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s)
    let rawHistory : FinLaw (R.Hist C) := FinLaw.pi rawFactors
    let localPass : Finset (R.Hist C) :=
      Finset.univ.filter fun W => W sourceSlice ∈ R.slicePass C sourceSlice
    have hLocalPassMass :
        rawHistory.pr (fun W => W sourceSlice ∈ R.slicePass C sourceSlice) =
          (R.sliceLaw C sourceSlice).pr (fun x => x ∈ R.slicePass C sourceSlice) := by
      simpa [rawHistory, rawFactors] using
        (Lane_q_s16_prod2.finLaw_pi_coordinate_pr rawFactors sourceSlice
          (R.slicePass C sourceSlice))
    have hLocalPassPr : rawHistory.pr (fun W => W ∈ localPass) =
        (R.sliceLaw C sourceSlice).pr (fun x => x ∈ R.slicePass C sourceSlice) := by
      simpa [localPass] using hLocalPassMass
    have hSlicePos : 0 < ∑ W ∈ localPass, rawHistory.w W := by
      rw [← Lane_q_s16_prod2.finLaw_pr_finset rawHistory localPass, hLocalPassPr,
        Lane_q_s16_prod2.finLaw_pr_finset]
      exact R.slice_pos C sourceSlice
    let splitEquiv := Lane_q_s16_prod2.finLaw_pi_splitEquiv
      (Ω := fun s : R.Slice C => R.Value C s) sourceSlice
    let otherFactors : ∀ j : {s : R.Slice C // s ≠ sourceSlice}, FinLaw (R.Value C j.1) :=
      fun j => FinLaw.cond (R.sliceLaw C j.1) (R.slicePass C j.1) (R.slice_pos C j.1)
    let otherLaw := FinLaw.pi otherFactors
    let pairPass : Finset (R.Value C sourceSlice ×
        (∀ j : {s : R.Slice C // s ≠ sourceSlice}, R.Value C j.1)) :=
      Finset.univ.filter fun p => p.1 ∈ R.slicePass C sourceSlice
    have hRawSource : rawFactors sourceSlice = R.sliceLaw C sourceSlice := by
      simp [rawFactors]
    have hRawOtherFactor (j : {s : R.Slice C // s ≠ sourceSlice}) :
        rawFactors j.1 = otherFactors j := by
      simp [rawFactors, otherFactors, j.2]
    have hRawOther :
        FinLaw.pi (fun j : {s : R.Slice C // s ≠ sourceSlice} => rawFactors j.1) = otherLaw := by
      apply Lane_q_s16_prod2.finLaw_ext
      intro a
      simp only [FinLaw.pi]
      apply Finset.prod_congr rfl
      intro j hj
      rw [hRawOtherFactor j]
    have hRawSplit :
        FinLaw.map rawHistory splitEquiv =
          FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw) := by
      calc
        FinLaw.map rawHistory splitEquiv =
            FinLaw.bind (rawFactors sourceSlice)
              (fun _ => FinLaw.pi (fun j : {s : R.Slice C // s ≠ sourceSlice} => rawFactors j.1)) := by
          simpa [rawHistory, splitEquiv, Lane_q_s16_prod2.finLaw_pi_splitEquiv] using
            (Lane_q_s16_prod2.finLaw_pi_split rawFactors sourceSlice)
        _ = FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw) := by
          rw [hRawSource, hRawOther]
    have hPassImage : localPass.image splitEquiv = pairPass := by
      apply Finset.ext
      intro p
      rcases p with ⟨x, other⟩
      constructor
      · intro hp
        rcases Finset.mem_image.mp hp with ⟨W, hW, hEq⟩
        have hWPass : W sourceSlice ∈ R.slicePass C sourceSlice := by
          simpa [localPass] using hW
        have hx : W sourceSlice = x := by
          simpa [splitEquiv, Lane_q_s16_prod2.finLaw_pi_splitEquiv] using
            congrArg Prod.fst hEq
        rw [hx] at hWPass
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWPass⟩
      · intro hp
        have hxPass : x ∈ R.slicePass C sourceSlice := (Finset.mem_filter.mp hp).2
        refine Finset.mem_image.mpr ⟨splitEquiv.symm (x, other), ?_, ?_⟩
        · simpa [localPass, splitEquiv, Lane_q_s16_prod2.finLaw_pi_splitEquiv] using hxPass
        · exact splitEquiv.apply_symm_apply (x, other)
    have hPairMass :
        (FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw)).pr
            (fun p => p ∈ pairPass) =
          ∑ x ∈ R.slicePass C sourceSlice, (R.sliceLaw C sourceSlice).w x := by
      rw [Lane_q_s16_prod2.finLaw_bind_pr]
      calc
        (∑ x, (R.sliceLaw C sourceSlice).w x *
            otherLaw.pr (fun y => (x, y) ∈ pairPass)) =
            ∑ x, if x ∈ R.slicePass C sourceSlice then
              (R.sliceLaw C sourceSlice).w x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hconst : otherLaw.pr (fun y => (x, y) ∈ pairPass) =
              if x ∈ R.slicePass C sourceSlice then 1 else 0 := by
            by_cases hmem : x ∈ R.slicePass C sourceSlice
            · simp [FinLaw.pr, pairPass, hmem, otherLaw.sum_one]
            · simp [FinLaw.pr, pairPass, hmem]
          rw [hconst]
          by_cases hmem : x ∈ R.slicePass C sourceSlice <;> simp [hmem]
        _ = ∑ x ∈ R.slicePass C sourceSlice, (R.sliceLaw C sourceSlice).w x := by
          rw [← Finset.sum_filter]
          simp
    have hPairPos : 0 < ∑ p ∈ pairPass,
        (FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw)).w p := by
      rw [← Lane_q_s16_prod2.finLaw_pr_finset,
        hPairMass]
      exact R.slice_pos C sourceSlice
    have hCondPair :
        FinLaw.cond (FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw))
            pairPass hPairPos =
          FinLaw.bind (FinLaw.cond (R.sliceLaw C sourceSlice)
            (R.slicePass C sourceSlice) (R.slice_pos C sourceSlice)) (fun _ => otherLaw) := by
      simpa [pairPass] using
        (Lane_q_s16_prod2.finLaw_cond_bind_left (R.sliceLaw C sourceSlice) otherLaw
          (R.slicePass C sourceSlice) (R.slice_pos C sourceSlice))
    have hCondSplit :
        FinLaw.map (FinLaw.cond rawHistory localPass hSlicePos) splitEquiv =
          FinLaw.bind (FinLaw.cond (R.sliceLaw C sourceSlice)
            (R.slicePass C sourceSlice) (R.slice_pos C sourceSlice)) (fun _ => otherLaw) := by
      calc
        FinLaw.map (FinLaw.cond rawHistory localPass hSlicePos) splitEquiv =
          FinLaw.cond (FinLaw.map rawHistory splitEquiv) (localPass.image splitEquiv) _ :=
          Lane_q_s16_prod2.finLaw_map_cond_equiv rawHistory splitEquiv localPass hSlicePos
        _ = FinLaw.cond (FinLaw.bind (R.sliceLaw C sourceSlice) (fun _ => otherLaw))
              pairPass hPairPos := by
          apply Lane_q_s16_prod2.finLaw_ext
          intro p
          simp [FinLaw.cond, hRawSplit, hPassImage, pairPass]
        _ = FinLaw.bind (FinLaw.cond (R.sliceLaw C sourceSlice)
              (R.slicePass C sourceSlice) (R.slice_pos C sourceSlice)) (fun _ => otherLaw) := hCondPair
    let goodFactors : ∀ s : R.Slice C, FinLaw (R.Value C s) := fun s =>
      FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s)
    have hOtherGood : otherLaw = FinLaw.pi (fun j : {s : R.Slice C // s ≠ sourceSlice} =>
        goodFactors j.1) := by
      apply Lane_q_s16_prod2.finLaw_ext
      intro a
      simp only [FinLaw.pi, otherLaw]
      apply Finset.prod_congr rfl
      intro j hj
      rfl
    have hGoodSplit :
        FinLaw.map (R.history C) splitEquiv =
          FinLaw.bind (goodFactors sourceSlice) (fun _ => otherLaw) := by
      calc
        FinLaw.map (R.history C) splitEquiv =
            FinLaw.bind (goodFactors sourceSlice)
              (fun _ => FinLaw.pi (fun j : {s : R.Slice C // s ≠ sourceSlice} =>
                goodFactors j.1)) := by
          simpa [CellRawData.history, goodFactors, splitEquiv,
            Lane_q_s16_prod2.finLaw_pi_splitEquiv] using
            (Lane_q_s16_prod2.finLaw_pi_split goodFactors sourceSlice)
        _ = FinLaw.bind (goodFactors sourceSlice) (fun _ => otherLaw) := by
          rw [← hOtherGood]
    have hCondRaw : FinLaw.cond rawHistory localPass hSlicePos = R.history C := by
      apply Lane_q_s16_prod2.finLaw_ext
      intro W
      have h := congrArg (fun law => law.w (splitEquiv W)) (hCondSplit.trans hGoodSplit.symm)
      have hMapWeight (law : FinLaw (R.Hist C)) :
          (FinLaw.map law splitEquiv).w (splitEquiv W) = law.w W := by
        exact Lane_q_s16_prod2.finLaw_map_equiv_weight law splitEquiv W
      rw [hMapWeight] at h
      rw [hMapWeight] at h
      exact h
    let localBase : FinLaw (Cal.Hist C) :=
      FinLaw.map rawHistory (fun W => (hLink.histories C).symm W)
    let localPassCal : Finset (Cal.Hist C) :=
      localPass.image (hLink.histories C).symm
    have hLocalCalPassPr :
        localBase.pr (fun W => W ∈ localPassCal) =
          rawHistory.pr (fun W => W ∈ localPass) := by
      change (FinLaw.map rawHistory (fun W => (hLink.histories C).symm W)).pr _ = _
      rw [Lane_q_s16_prod2.finLaw_map_pr]
      congr 1
      funext W
      simp [localPassCal, localPass]
    have hSlicePosCal : 0 < ∑ W ∈ localPassCal, localBase.w W := by
      rw [← Lane_q_s16_prod2.finLaw_pr_finset localBase localPassCal,
        hLocalCalPassPr, Lane_q_s16_prod2.finLaw_pr_finset]
      exact hSlicePos
    have hLocalPassCalImage :
        localPass.image (hLink.histories C).symm = localPassCal := by
      rfl
    have hLocalCondMap :
        FinLaw.map (FinLaw.cond rawHistory localPass hSlicePos) (hLink.histories C).symm =
          FinLaw.cond localBase localPassCal hSlicePosCal := by
      simpa [localBase, localPassCal] using
        (Lane_q_s16_prod2.finLaw_map_cond_equiv rawHistory (hLink.histories C).symm
          localPass hSlicePos)
    have hCalHistory : FinLaw.cond localBase localPassCal hSlicePosCal = Cal.history C := by
      calc
        FinLaw.cond localBase localPassCal hSlicePosCal =
            FinLaw.map (FinLaw.cond rawHistory localPass hSlicePos) (hLink.histories C).symm :=
          hLocalCondMap.symm
        _ = FinLaw.map (R.history C) (hLink.histories C).symm :=
          congrArg (fun law => FinLaw.map law (hLink.histories C).symm) hCondRaw
        _ = Cal.history C := (hLink.history_eq C).symm
    let histMap : Cal.Hist C → Cal.Hist C × Unit := fun W => (W, ())
    let histLaw : FinLaw (Cal.Hist C × Unit) :=
      FinLaw.map (FinLaw.cond localBase localPassCal hSlicePosCal) histMap
    have hHistLaw : histLaw = FinLaw.map (Cal.history C) histMap := by
      simp [histLaw, hCalHistory]
    have hHistWeight (W : Cal.Hist C) : histLaw.w (W, ()) = (Cal.history C).w W := by
      rw [hHistLaw]
      simp [FinLaw.map, histMap]
    have hGatedWeight (pool : F.Pool C) (W : Cal.Hist C) :
        (FinLaw.map (Cal.gatedHistory C pool) histMap).w (W, ()) =
          (Cal.gatedHistory C pool).w W := by
      simp [FinLaw.map, histMap]
    let histGate (pool : F.Pool C) : Finset (Cal.Hist C × Unit) :=
      Finset.univ.filter fun z => z.1 ∈ Cal.gate C pool
    have hGateMass (pool : F.Pool C) :
        (∑ z ∈ histGate pool, histLaw.w z) =
          ∑ W ∈ Cal.gate C pool, (Cal.history C).w W := by
      calc
        (∑ z ∈ histGate pool, histLaw.w z) =
            histLaw.pr (fun z => z ∈ histGate pool) :=
          (Lane_q_s16_prod2.finLaw_pr_finset histLaw (histGate pool)).symm
        _ = (Cal.history C).pr (fun W => W ∈ Cal.gate C pool) := by
          rw [hHistLaw, Lane_q_s16_prod2.finLaw_map_pr]
          simp [histGate, histMap]
        _ = ∑ W ∈ Cal.gate C pool, (Cal.history C).w W :=
          Lane_q_s16_prod2.finLaw_pr_finset (Cal.history C) (Cal.gate C pool)
    have hCalGatedSupport (pool : F.Pool C) (ht : F.typical C pool)
        (W : Cal.Hist C) (hW : (Cal.gatedHistory C pool).w W ≠ 0) :
        W ∈ Cal.gate C pool ∧ (Cal.history C).w W ≠ 0 := by
      rw [Cal.gated_eq C pool ht] at hW
      by_cases hmem : W ∈ Cal.gate C pool
      · refine ⟨hmem, ?_⟩
        by_contra hzero
        apply hW
        simp [FinLaw.cond, hmem, hzero]
      · exact False.elim (hW (by simp [FinLaw.cond, hmem]))
    have hRawHistSupport (W : Cal.Hist C) (hW : (Cal.history C).w W ≠ 0) :
        (R.history C).w (hLink.histories C W) ≠ 0 := by
      have hMap : (FinLaw.map (R.history C) (hLink.histories C).symm).w W ≠ 0 := by
        rw [← hLink.history_eq C]
        exact hW
      have hWeight := Lane_q_s16_prod2.finLaw_map_equiv_weight (R.history C)
        (hLink.histories C).symm (hLink.histories C W)
      have hInv : (hLink.histories C).symm (hLink.histories C W) = W :=
        (hLink.histories C).symm_apply_apply W
      rw [hInv] at hWeight
      rw [hWeight] at hMap
      exact hMap
    have hRawGateSupport (pool : F.Pool C) (W : Cal.Hist C)
        (hW : W ∈ Cal.gate C pool) : hLink.histories C W ∈ S.gate C pool := by
      rw [hLink.gate_eq C pool] at hW
      rcases Finset.mem_image.mp hW with ⟨Wraw, hRawGate, hEq⟩
      have hEq' : Wraw = hLink.histories C W := by
        calc
          Wraw = (hLink.histories C) ((hLink.histories C).symm Wraw) :=
            ((hLink.histories C).apply_symm_apply Wraw).symm
          _ = (hLink.histories C) W := congrArg (hLink.histories C) hEq
      rw [hEq'] at hRawGate
      exact hRawGate
    let groupScopeRaw : Finset (R.Group C) := groupScope.image (hLink.groups C)
    have hGroupScopeRawCard : groupScopeRaw.card = groupScope.card := by
      dsimp [groupScopeRaw]
      exact Finset.card_image_of_injective groupScope (hLink.groups C).injective
    have hRoleScopeCard : roleScope.card ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by
      calc
        roleScope.card = (Finset.univ.image starRole).card := rfl
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = Fintype.card (Fin (PT.tiling.P (H.geom.cellPatch C)).h) := by simp
        _ = (PT.tiling.P (H.geom.cellPatch C)).h := Fintype.card_fin _
    let encPipe : (Cal.Hist C × Unit) ×
        ((Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
        (OddCellRole H.geom C → Fin (T.S.N k))) → F.State C := fun z =>
      Cal.encode C (z.1.1, z.2.1, z.2.2)
    let P : FreshPriorPipeline F C v := {
      LocalHist := Cal.Hist C
      localFin := Cal.histFin C
      localDec := Cal.histDec C
      Aux := Unit
      auxFin := inferInstance
      Group := Cal.Group C
      groupFin := Cal.groupFin C
      groupDec := Cal.groupDec C
      Role := OddCellRole H.geom C
      roleFin := inferInstance
      roleDec := inferInstance
      baseHistory := localBase
      slicePass := localPassCal
      slice_pos := hSlicePosCal
      auxHistory := FinLaw.dirac ()
      history := histLaw
      history_eq := by
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        simp [histLaw, histMap, FinLaw.map, FinLaw.bind, FinLaw.dirac]
      gate := histGate
      gate_pos := by
        intro pool ht
        rw [hGateMass pool]
        exact Cal.gate_pos C pool ht
      gatedHistory := fun pool =>
        FinLaw.map (Cal.gatedHistory C pool) histMap
      gated_eq := by
        intro pool ht
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        rw [hGatedWeight pool W, Cal.gated_eq C pool ht]
        simp only [FinLaw.cond]
        rw [hGateMass pool, hHistWeight]
        by_cases hmem : W ∈ Cal.gate C pool <;> simp [histGate, hmem]
      qraw := fun W g => R.qraw C (hLink.histories C W) (hLink.groups C g)
      U := fun W g D => R.U C (hLink.histories C W) (hLink.groups C g) D
      U_support := by
        intro W g D y hy
        exact R.U_support C (hLink.histories C W) (hLink.groups C g) D y hy
      groupOf := Cal.groupOf C
      rolePosition := fun r => r.1
      role_cell := fun r => r.2.1
      role_odd := fun r => r.2.2
      groupScope := groupScope
      roleScope := roleScope
      scopes_closed := by
        intro r hr
        exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
      rawPrior := fun W ys y => R.rawPrior C (hLink.histories C W) ys v y
      prior_local := by
        intro W ys ys' hys
        change R.rawPrior C (hLink.histories C W) ys v =
          R.rawPrior C (hLink.histories C W) ys' v
        rw [hPriorIdentity, hPriorIdentity]
        congr 1
        funext j
        apply hys (starRole j)
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      pretrim := fun W g => R.pretrim C (hLink.histories C W) (hLink.groups C g)
      permitted := Cal.permitted C
      qtilde := Cal.qtilde C
      qtilde_eq := by
        intro pool W g D ht hW hbase
        have hCalHist : (Cal.history C).w W ≠ 0 := by
          have hCondHist :
              (FinLaw.cond localBase localPassCal hSlicePosCal).w W ≠ 0 := by
            simp only [FinLaw.cond]
            rw [if_pos hW]
            exact div_ne_zero hbase (ne_of_gt hSlicePosCal)
          have hEq := congrArg (fun law => law.w W) hCalHistory
          rw [← hEq]
          exact hCondHist
        let Wraw := hLink.histories C W
        let graw := hLink.groups C g
        let raw := R.qraw C Wraw graw
        let preSet := R.pretrim C Wraw graw
        let permSet := Cal.permitted C g
        let poolSet := Finset.univ.image pool
        let bothSet := (preSet ∩ permSet) ∩ poolSet
        let zPre : ℝ := ∑ b ∈ preSet, raw.w b
        have hIncoming : Cal.qin C W g = R.qin C Wraw graw :=
          hLink.incoming_eq C W g
        have hRHist : (R.history C).w Wraw ≠ 0 := by
          have hmap : (FinLaw.map (R.history C) (hLink.histories C).symm).w W ≠ 0 := by
            rw [← hLink.history_eq C]
            exact hCalHist
          have hSymm : (hLink.histories C).symm Wraw = W := by
            simp [Wraw]
          rw [← hSymm, Lane_q_s16_prod2.finLaw_map_equiv_weight] at hmap
          exact hmap
        have hGoodCoord (s : R.Slice C) :
            (goodFactors s).w (Wraw s) ≠ 0 := by
          intro hzero
          apply hRHist
          change (∏ s : R.Slice C, (goodFactors s).w (Wraw s)) = 0
          exact Finset.prod_eq_zero (Finset.mem_univ s) hzero
        have hSliceInput : ∀ s : R.Slice C,
            Wraw s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (Wraw s) ≠ 0 := by
          intro s
          have hpass : Wraw s ∈ R.slicePass C s := by
            by_contra hnot
            apply hGoodCoord s
            simp [goodFactors, FinLaw.cond, hnot]
          have hmass : (R.sliceLaw C s).w (Wraw s) ≠ 0 := by
            intro hz
            apply hGoodCoord s
            simp [goodFactors, FinLaw.cond, hpass, hz]
          exact ⟨hpass, hmass⟩
        have hQin (b : Bin PT.tiling (H.geom.cellPatch C)) :
            (R.qin C Wraw graw).w b =
              (if b ∈ preSet then raw.w b else 0) / zPre := by
          have h := R.qin_eq C Wraw graw b hSliceInput
          simpa [preSet, raw, zPre] using h
        have hPreNe : zPre ≠ 0 := by
          intro hz
          have hZero (b : Bin PT.tiling (H.geom.cellPatch C)) :
              (R.qin C Wraw graw).w b = 0 := by
            rw [hQin b]
            by_cases hb : b ∈ preSet <;> simp [hb, hz]
          have hsum : ∑ b, (R.qin C Wraw graw).w b = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            exact hZero b
          have hone := (R.qin C Wraw graw).sum_one
          rw [hsum] at hone
          norm_num at hone
        have hPreNonneg : 0 ≤ zPre := by
          apply Finset.sum_nonneg
          intro b hb
          exact raw.nonneg b
        have hPrePos : 0 < zPre := lt_of_le_of_ne hPreNonneg (Ne.symm hPreNe)
        let zPerm : ℝ := ∑ b ∈ permSet, (Cal.qin C W g).w b
        let zPool : ℝ := ∑ b ∈ permSet ∩ poolSet, (Cal.qin C W g).w b
        let zBoth : ℝ := ∑ b ∈ bothSet, raw.w b
        have hPermPos : 0 < zPerm := by
          have hMass := Cal.permission_mass C W g hCalHist
          have hDen := Cal.perm_range.2
          have hEq : zPerm = ∑ b ∈ Cal.permitted C g, (Cal.qin C W g).w b := by
            rfl
          rw [hEq]
          linarith
        have hBinNonempty : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := by
          have hPr : 0 < (Cal.qin C W g).pr (fun _ => True) := by
            rw [Lane_q_s16_prod2.finLaw_pr_const]
            norm_num
          obtain ⟨b, _, _⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
            (Cal.qin C W g) (fun _ => True) hPr
          exact ⟨b⟩
        letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := hBinNonempty
        have hBinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) :=
          Fintype.card_pos
        have hTheta : 0 < (H.geom.nslot C : ℝ) /
            (Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) : ℝ) := by
          exact div_pos (by exact_mod_cast Cal.slot_pos C) (by exact_mod_cast hBinCard)
        have hnR : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) Q.n_large)
        have hnPow : (T.S.n k : ℝ) ^ (-4 : ℝ) < 1 := by
          exact Real.rpow_lt_one_of_one_lt_of_neg hnR (by norm_num)
        let normFactor : ℝ :=
          ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) *
            (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))
        have hNormFactor : 0 < normFactor :=
          mul_pos hTheta (sub_pos.mpr hnPow)
        have hPoolPos : 0 < zPool := by
          have hPoolReq := Cal.pool_normalizer C pool W g ht hCalHist
          have hLower : normFactor ≤ zPool / zPerm := by
            simpa [normFactor, zPool, zPerm, poolSet, permSet] using hPoolReq
          have hRatio : 0 < zPool / zPerm := lt_of_lt_of_le hNormFactor hLower
          have hzPoolNe : zPool ≠ 0 := by
            intro hz
            simp [hz, zPerm] at hRatio
          have hzPoolNonneg : 0 ≤ zPool := by
            dsimp [zPool]
            apply Finset.sum_nonneg
            intro b hb
            exact (Cal.qin C W g).nonneg b
          exact lt_of_le_of_ne hzPoolNonneg (Ne.symm hzPoolNe)
        have hZBothEq : zPool = zBoth / zPre := by
          calc
            zPool = ∑ b ∈ permSet ∩ poolSet,
                (if b ∈ preSet then raw.w b else 0) / zPre := by
              dsimp [zPool]
              apply Finset.sum_congr rfl
              intro b hb
              rw [hIncoming, hQin b]
            _ = (∑ b ∈ permSet ∩ poolSet,
                if b ∈ preSet then raw.w b else 0) / zPre := by
              rw [Finset.sum_div]
            _ = zBoth / zPre := by
              congr 1
              have hSet : (permSet ∩ poolSet).filter (fun b => b ∈ preSet) = bothSet := by
                ext b
                simp [bothSet, and_assoc, and_left_comm, and_comm]
              rw [← Finset.sum_filter, hSet]
        have hZBothPos : 0 < zBoth := by
          have hmul : zPool * zPre = zBoth := by
            rw [hZBothEq]
            field_simp [hPreNe]
          rw [← hmul]
          exact mul_pos hPoolPos hPrePos
        have hTargetDen :
            (∑ b ∈ (R.pretrim C Wraw graw ∩ Cal.permitted C g) ∩
              Finset.univ.image pool,
              (R.qraw C Wraw graw).w b) = zBoth := by
          change (∑ b ∈ bothSet, raw.w b) = zBoth
          rfl
        have hCalQtilde := Cal.qtilde_eq C pool W g D ht hCalHist
        rw [hCalQtilde, hLink.incoming_eq C W g]
        rw [hQin]
        have hcalDen :
            (∑ b ∈ permSet ∩ poolSet, (R.qin C Wraw graw).w b) = zPool := by
          rw [← hIncoming]
        rw [hcalDen, hZBothEq, hTargetDen]
        by_cases hpre : D ∈ preSet
        · by_cases hperm : D ∈ permSet
          · have hpermCal : D ∈ Cal.permitted C g := by
              simpa [permSet] using hperm
            by_cases hpool : D ∈ poolSet
            · have hpreRaw : D ∈ R.pretrim C Wraw graw := by
                simpa [preSet] using hpre
              have hpoolImage : D ∈ Finset.univ.image pool := by
                simpa [poolSet] using hpool
              simp [preSet, raw, Wraw, graw, hpre, hpreRaw, hpermCal, hpoolImage]
              field_simp [ne_of_gt hPrePos, ne_of_gt hZBothPos]
            · have hpoolNot : D ∉ Finset.univ.image pool := by
                simpa [poolSet] using hpool
              simp [preSet, raw, Wraw, graw, hpre, hpermCal, hpoolNot]
          · have hpermNot : D ∉ Cal.permitted C g := by
              simpa [permSet] using hperm
            simp [preSet, raw, Wraw, graw, hpre, hpermNot]
        · have hpreNot : D ∉ R.pretrim C Wraw graw := by
            simpa [preSet] using hpre
          simp [preSet, raw, Wraw, graw, hpre, hpreNot]
      binSampler := fun pool W => Cal.binSampler C pool W.1
      labelSampler := fun pool W a => Cal.labelSampler C pool W.1 a
      groupRate := Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.05 : ℝ)
      labelRate := Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.01 : ℝ)
      rates_nonneg := by
        have hRoom := hCalibration.room hClusterMode (H.geom.cellPatch C)
        have hd : 0 < ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) := by
          exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2)
            (le_trans (by norm_num : 2 ≤ 10 ^ 100) hRoom.2.1)
        constructor
        · exact le_of_lt (Real.rpow_pos_of_pos hd _)
        · exact le_of_lt (Real.rpow_pos_of_pos hd _)
      bin_joint := by
        intro pool W a ht hW
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hGatedWeight pool W.1]
          exact hW
        obtain ⟨hGateCal, hCalHist⟩ := hCalGatedSupport pool ht W.1 hWCal
        let Wraw := hLink.histories C W.1
        have hRawHist := hRawHistSupport W.1 hCalHist
        have hRawGate := hRawGateSupport pool W.1 hGateCal
        have hStyp : S.typical C pool := (hLink.typical_eq C pool).mp ht
        have hBinFeas := S.bin_feasible C pool Wraw hStyp hRawGate hRawHist hClusterMode
        let aRaw : R.Group C → Bin PT.tiling (H.geom.cellPatch C) :=
          fun rg => a ((hLink.groups C).symm rg)
        have hGroupMapInjOn : Set.InjOn (hLink.groups C) groupScope := by
          intro g hg g' hg' heq
          exact (hLink.groups C).injective heq
        have hEvent (x : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :
            (∀ gc ∈ groupScope, x (hLink.groups C gc) = a gc) ↔
              ∀ rg ∈ groupScopeRaw, x rg = aRaw rg := by
          constructor
          · intro hall rg hrg
            rcases Finset.mem_image.mp hrg with ⟨gc, hgc, rfl⟩
            simpa [aRaw] using hall gc hgc
          · intro hall gc hgc
            simpa [aRaw] using
              hall (hLink.groups C gc) (Finset.mem_image.mpr ⟨gc, hgc, rfl⟩)
        have hBinProbability :
            (Cal.binSampler C pool W.1).pr
                (fun x => ∀ gc ∈ groupScope, x gc = a gc) =
              (S.binLaw C pool Wraw).pr (fun x => ∀ rg ∈ groupScopeRaw, x rg = aRaw rg) := by
          rw [hLink.bin_eq C pool W.1, Lane_q_s16_prod2.finLaw_map_pr]
          apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
          intro x _
          exact hEvent x
        have hSBound :
            (S.binLaw C pool Wraw).pr (fun x => ∀ rg ∈ groupScopeRaw, x rg = aRaw rg) ≤
              Real.exp (Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.05) *
                groupScopeRaw.card) *
              ∏ rg ∈ groupScopeRaw, (K.qtilde C pool Wraw rg).w (aRaw rg) := by
          simpa [CellRestrictedKernels.binProblem, GroupBinProblem.feasible] using
            (hBinFeas.2 groupScopeRaw aRaw)
        have hProduct :
            (∏ rg ∈ groupScopeRaw, (K.qtilde C pool Wraw rg).w (aRaw rg)) =
              (∏ gc ∈ groupScope, (Cal.qtilde C pool W.1 gc).w (a gc) : ℝ) := by
          calc
            (∏ rg ∈ groupScopeRaw, (K.qtilde C pool Wraw rg).w (aRaw rg)) =
                ∏ gc ∈ groupScope,
                  (K.qtilde C pool Wraw (hLink.groups C gc)).w (aRaw (hLink.groups C gc)) := by
              change (∏ rg ∈ Finset.image (hLink.groups C) groupScope,
                  (K.qtilde C pool Wraw rg).w (aRaw rg)) = _
              rw [Finset.prod_image hGroupMapInjOn]
            _ = ∏ gc ∈ groupScope, (Cal.qtilde C pool W.1 gc).w (a gc) := by
              apply Finset.prod_congr rfl
              intro gc hgc
              have hRestricted := hLink.restricted_eq C pool W.1 gc
              rw [← hRestricted]
              simp [aRaw]
        have hCardR : (groupScopeRaw.card : ℝ) = (groupScope.card : ℝ) := by
          exact_mod_cast hGroupScopeRawCard
        calc
          (Cal.binSampler C pool W.1).pr (fun x => ∀ gc ∈ groupScope, x gc = a gc) =
              (S.binLaw C pool Wraw).pr
                (fun x => ∀ rg ∈ groupScopeRaw, x rg = aRaw rg) := hBinProbability
          _ ≤ Real.exp
                (Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.05) *
                  groupScopeRaw.card) *
                ∏ rg ∈ groupScopeRaw, (K.qtilde C pool Wraw rg).w (aRaw rg) := hSBound
          _ = Real.exp (Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.05) *
                groupScope.card) * ∏ gc ∈ groupScope, (Cal.qtilde C pool W.1 gc).w (a gc) := by
            rw [hCardR, hProduct]
      bins_distinct := by
        intro pool W a ht hW ha
        sorry
      label_joint := by
        intro pool W a ys ht hW ha
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hGatedWeight pool W.1]
          exact hW
        obtain ⟨hGateCal, hCalHist⟩ := hCalGatedSupport pool ht W.1 hWCal
        let Wraw := hLink.histories C W.1
        have hRawHist := hRawHistSupport W.1 hCalHist
        have hRawGate := hRawGateSupport pool W.1 hGateCal
        have hStyp : S.typical C pool := (hLink.typical_eq C pool).mp ht
        have hBinFeas := S.bin_feasible C pool Wraw hStyp hRawGate hRawHist hClusterMode
        let aRaw : R.Group C → Bin PT.tiling (H.geom.cellPatch C) :=
          fun rg => a ((hLink.groups C).symm rg)
        have hMapPos : (FinLaw.map (S.binLaw C pool Wraw)
            (fun x gc => x (hLink.groups C gc))).w a ≠ 0 := by
          rw [← hLink.bin_eq C pool W.1]
          exact ha
        obtain ⟨a0, haMap, ha0⟩ := Lane_q_s16_prod2.finLaw_map_nonzero_preimage
          (S.binLaw C pool Wraw) (fun x gc => x (hLink.groups C gc)) a hMapPos
        have haRawEq : aRaw = a0 := by
          funext rg
          have h := congrFun haMap ((hLink.groups C).symm rg)
          simpa [aRaw] using h.symm
        have hSourceA : (fun rg => a ((hLink.groups C).symm rg)) = a0 := by
          funext rg
          have h := congrFun haMap ((hLink.groups C).symm rg)
          simpa using h.symm
        have hLabelSource :
            Cal.labelSampler C pool W.1 a = S.labelLaw C pool Wraw a0 := by
          calc
            Cal.labelSampler C pool W.1 a =
                S.labelLaw C pool Wraw (fun rg => a ((hLink.groups C).symm rg)) :=
              hLink.label_eq C pool W.1 a
            _ = S.labelLaw C pool Wraw a0 := by rw [hSourceA]
        obtain ⟨L, hL⟩ := S.cluster_label_feasible C pool Wraw a0 hStyp hRawGate
          hRawHist ha0 hClusterMode
        have hRegime : L.problem.regime = .cluster := by
          rw [L.regime_eq]
          simp [hClusterMode]
        have hRoleQueries : L.problem.queries roleScope := by
          rw [RoleLabelProblem.queries, hRegime]
          intro b
          calc
            (roleScope.filter fun r => L.problem.blockOf r = b).card ≤ roleScope.card :=
              Finset.card_filter_le _ _
            _ ≤ (PT.tiling.P (H.geom.cellPatch C)).h := hRoleScopeCard
            _ = L.problem.h := L.height_eq.symm
        have hLabelBound := hL.2 roleScope ys hRoleQueries
        have hRate : L.problem.rate =
            Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.01 : ℝ) := by
          simp [RoleLabelProblem.rate, hRegime, L.scale_eq, hClusterMode]
        have hTarget (r : OddCellRole H.geom C) :
            (L.problem.target r).w (ys r) =
              (R.U C Wraw (hLink.groups C (Cal.groupOf C r))
                (a (Cal.groupOf C r))).w (ys r) := by
          have h := L.targets_eq r (ys r)
          simpa [hClusterMode, aRaw, ← haRawEq, ← hLink.group_eq C r] using h
        have hTargetProd :
            ∏ r ∈ roleScope, (L.problem.target r).w (ys r) =
              ∏ r ∈ roleScope,
                (R.U C Wraw (hLink.groups C (Cal.groupOf C r))
                  (a (Cal.groupOf C r))).w (ys r) := by
          apply Finset.prod_congr rfl
          intro r hr
          exact hTarget r
        calc
          (Cal.labelSampler C pool W.1 a).pr
              (fun ys' => ∀ r ∈ roleScope, ys' r = ys r) =
              (S.labelLaw C pool Wraw a0).pr
                (fun ys' => ∀ r ∈ roleScope, ys' r = ys r) := by rw [hLabelSource]
          _ ≤ Real.exp (Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ)
                (-0.01) * roleScope.card) *
              ∏ r ∈ roleScope,
                (R.U C Wraw (hLink.groups C (Cal.groupOf C r))
                  (a (Cal.groupOf C r))).w (ys r) := by
            rw [← hRate, ← hTargetProd]
            exact hLabelBound
          _ = Real.exp (Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.01) *
                roleScope.card) *
              ∏ r ∈ roleScope,
                (R.U C Wraw (hLink.groups C (Cal.groupOf C r))
                  (a (Cal.groupOf C r))).w (ys r) := by rfl
      encode := encPipe
      fresh_eq := by
        intro pool ht
        rw [Cal.fresh_eq C pool ht]
        apply Lane_q_s16_prod2.finLaw_ext
        intro s
        simp only [FinLaw.map, FinLaw.bind]
        let StageState := (Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
          (OddCellRole H.geom C → Fin (T.S.N k))
        let dropUnit : (Cal.Hist C × StageState) ≃ ((Cal.Hist C × Unit) × StageState) := {
          toFun := fun z => ((z.1, ()), z.2)
          invFun := fun z => (z.1.1, z.2)
          left_inv := by intro z; rfl
          right_inv := by intro z; rcases z with ⟨⟨W, u⟩, a⟩; cases u; rfl }
        apply Fintype.sum_equiv dropUnit
        intro z
        rcases z with ⟨W, a⟩
        simp [FinLaw.map, FinLaw.bind, encPipe, histMap, dropUnit,
          hGatedWeight pool W]
      prior_eq := by
        intro pool W a ys ht hW ha hys
        have hGatedWeight :
            (FinLaw.map (Cal.gatedHistory C pool) histMap).w W =
              (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hCalW : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hGatedWeight]
          exact hW
        exact hLink.prior_eq C pool W.1 a ys v ht hCalW ha hys hcell hEven
      label_eq := by
        intro pool W a ys r ht hW ha hys
        have hGatedWeight :
            (FinLaw.map (Cal.gatedHistory C pool) histMap).w W =
              (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hCalW : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hGatedWeight]
          exact hW
        exact Cal.label_eq C pool W.1 a ys r ht hCalW ha hys
      δgate := Cal.δgate
      δpre := Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-10 : ℝ)
      δperm := Cal.δperm
      error_ranges := by
        refine ⟨⟨Cal.gate_range.1, Cal.gate_range.2⟩,
          ⟨?_, ?_⟩, ⟨Cal.perm_range.1, Cal.perm_range.2⟩⟩
        · exact Real.rpow_nonneg (by positivity) _
        · have hRoom := hCalibration.room hClusterMode (H.geom.cellPatch C)
          have hd2Nat : 2 ≤ (PT.tiling.P (H.geom.cellPatch C)).d :=
            (le_trans (by norm_num : 2 ≤ 10 ^ 100) hRoom.2.1)
          have hd2 : (1 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).d := by
            exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd2Nat)
          have hd : 0 < ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) := by positivity
          have hpow : 0 < Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-10 : ℝ) :=
            Real.rpow_pos_of_pos hd _
          have hlt : Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-10 : ℝ) < 1 := by
            apply Real.rpow_lt_one_of_one_lt_of_neg
            · exact hd2
            · norm_num
          exact hlt
      gate_mass := by
        intro pool ht
        rw [hGateMass pool]
        exact Cal.gate_mass C pool ht
      pretrim_mass := by
        intro W g hW hbase hg
        sorry
      permission_mass := by
        intro W g hW hbase hg
        sorry
      normalizer_mass := by
        intro pool W g ht hW hbase hg
        sorry
      slot_pos := Cal.slot_pos C
      stage_cost := by
        sorry
      slice_cost := by
        sorry
    }
    refine ⟨P, ?_, ?_⟩
    · sorry
    · intro Φ
      sorry
  · obtain ⟨hGroupInj, hValueUnit, hPassAll, hQUniform, hPretrimAll,
      hUDirect, hEnvExists⟩ := hDirectData C
    obtain ⟨hEnv, hRawPrior⟩ := hEnvExists
    let priorLaw := Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv
    let histMap : Cal.Hist C → Cal.Hist C × Unit := fun W => (W, ())
    let histLaw : FinLaw (Cal.Hist C × Unit) := FinLaw.map (Cal.history C) histMap
    let histGate (pool : F.Pool C) : Finset (Cal.Hist C × Unit) :=
      Finset.univ.filter fun z => z.1 ∈ Cal.gate C pool
    have hSlicePos : 0 < ∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
        (Cal.history C).w W := by
      have hsum : (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
          (Cal.history C).w W) = 1 := by simpa using (Cal.history C).sum_one
      rw [hsum]
      norm_num
    have hCalHistSum : ∑ W, (Cal.history C).w W = 1 := (Cal.history C).sum_one
    have hHistWeight (W : Cal.Hist C) : histLaw.w (W, ()) = (Cal.history C).w W := by
      simp [histLaw, histMap, FinLaw.map]
    have hGatedWeight (pool : F.Pool C) (W : Cal.Hist C) :
        (FinLaw.map (Cal.gatedHistory C pool) histMap).w (W, ()) =
          (Cal.gatedHistory C pool).w W := by
      simp [FinLaw.map, histMap]
    have hGateMass (pool : F.Pool C) :
        (∑ z ∈ histGate pool, histLaw.w z) =
          ∑ W ∈ Cal.gate C pool, (Cal.history C).w W := by
      calc
        (∑ z ∈ histGate pool, histLaw.w z) =
            histLaw.pr (fun z => z ∈ histGate pool) :=
          (Lane_q_s16_prod2.finLaw_pr_finset histLaw (histGate pool)).symm
        _ = (Cal.history C).pr (fun W => W ∈ Cal.gate C pool) := by
          rw [Lane_q_s16_prod2.finLaw_map_pr]
          simp [histGate, histMap]
        _ = ∑ W ∈ Cal.gate C pool, (Cal.history C).w W :=
          Lane_q_s16_prod2.finLaw_pr_finset (Cal.history C) (Cal.gate C pool)
    have hGatePos (pool : F.Pool C) (ht : F.typical C pool) :
        0 < ∑ z ∈ histGate pool, histLaw.w z := by
      rw [hGateMass]
      exact Cal.gate_pos C pool ht
    let gatedLaw (pool : F.Pool C) (ht : F.typical C pool) :=
      FinLaw.cond histLaw (histGate pool) (hGatePos pool ht)
    let encodePipe : (Cal.Hist C × Unit) ×
        ((Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
        (OddCellRole H.geom C → Fin (T.S.N k))) → F.State C := fun z =>
      Cal.encode C (z.1.1, z.2.1, z.2.2)
    let binPipe (pool : F.Pool C) (z : Cal.Hist C × Unit) :=
      Cal.binSampler C pool z.1
    let labelPipe (pool : F.Pool C) (z : Cal.Hist C × Unit)
        (a : Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
      Cal.labelSampler C pool z.1 a
    let P : FreshPriorPipeline F C v := {
      LocalHist := Cal.Hist C
      localFin := Cal.histFin C
      localDec := Cal.histDec C
      Aux := Unit
      auxFin := inferInstance
      Group := Cal.Group C
      groupFin := Cal.groupFin C
      groupDec := Cal.groupDec C
      Role := OddCellRole H.geom C
      roleFin := inferInstance
      roleDec := inferInstance
      baseHistory := Cal.history C
      slicePass := Finset.univ
      slice_pos := hSlicePos
      auxHistory := FinLaw.dirac ()
      history := histLaw
      history_eq := by
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        simp [histLaw, histMap, FinLaw.map, FinLaw.bind, FinLaw.cond,
          FinLaw.dirac, hCalHistSum]
      gate := histGate
      gate_pos := hGatePos
      gatedHistory := fun pool => FinLaw.map (Cal.gatedHistory C pool) histMap
      gated_eq := by
        intro pool ht
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        rw [hGatedWeight pool W, Cal.gated_eq C pool ht]
        simp only [FinLaw.cond]
        rw [hGateMass pool]
        simp [histGate, hHistWeight]
        by_cases hmem : W ∈ Cal.gate C pool <;> simp [hmem]
      qraw := fun W g => Cal.qin C W g
      U := fun W g D => Cal.U C W g D
      U_support := Cal.U_support C
      groupOf := Cal.groupOf C
      rolePosition := fun r => r.1
      role_cell := fun r => r.2.1
      role_odd := fun r => r.2.2
      groupScope := ∅
      roleScope := ∅
      scopes_closed := by intro r hr; simp at hr
      rawPrior := fun W ys y => priorLaw.w y
      prior_local := by intro W ys ys' hys; rfl
      pretrim := fun _ _ => Finset.univ
      permitted := Cal.permitted C
      qtilde := Cal.qtilde C
      qtilde_eq := by
        intro pool W g D ht hW hbase
        rw [Cal.qtilde_eq C pool W g D ht hbase]
        simp [Finset.univ_inter, Finset.inter_univ]
      binSampler := binPipe
      labelSampler := labelPipe
      groupRate := 0
      labelRate := 0
      rates_nonneg := by norm_num
      bin_joint := by
        intro pool W a ht hW
        simp [Lane_q_s16_prod2.finLaw_pr_const]
      bins_distinct := by
        intro pool W a ht hW ha
        simp
      label_joint := by
        intro pool W a ys ht hW ha
        simp [Lane_q_s16_prod2.finLaw_pr_const]
      encode := encodePipe
      fresh_eq := by
        intro pool ht
        rw [Cal.fresh_eq C pool ht]
        apply Lane_q_s16_prod2.finLaw_ext
        intro s
        simp only [FinLaw.map, FinLaw.bind]
        let StageState := (Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
          (OddCellRole H.geom C → Fin (T.S.N k))
        let dropUnit : (Cal.Hist C × StageState) ≃ ((Cal.Hist C × Unit) × StageState) := {
          toFun := fun z => ((z.1, ()), z.2)
          invFun := fun z => (z.1.1, z.2)
          left_inv := by intro z; rfl
          right_inv := by intro z; rcases z with ⟨⟨W, u⟩, a⟩; cases u; rfl }
        apply Fintype.sum_equiv dropUnit
        intro z
        rcases z with ⟨W, a⟩
        simp [FinLaw.map, FinLaw.bind, encodePipe, binPipe, labelPipe,
          histMap, dropUnit, hGatedWeight pool W]
      prior_eq := by
        intro pool W a ys ht hW ha hys
        have hMapW : ((Cal.gatedHistory C pool).map histMap).w W =
            (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hMapW]
          exact hW
        have hPrior := hLink.prior_eq C pool W.1 a ys v ht hWCal ha hys hcell hEven
        rw [hPrior]
        exact hRawPrior (hLink.histories C W.1) ys v hcell hEven
      label_eq := by
        intro pool W a ys r ht hW ha hys
        have hMapW : ((Cal.gatedHistory C pool).map histMap).w W =
            (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hMapW]
          exact hW
        exact Cal.label_eq C pool W.1 a ys r ht hWCal ha hys
      δgate := Cal.δgate
      δpre := 0
      δperm := 0
      error_ranges := by
        exact ⟨⟨Cal.gate_range.1, Cal.gate_range.2⟩,
          ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
      gate_mass := by
        intro pool ht
        rw [hGateMass]
        exact Cal.gate_mass C pool ht
      pretrim_mass := by intro W g hW hbase hg; simp at hg
      permission_mass := by intro W g hW hbase hg; simp at hg
      normalizer_mass := by intro pool W g ht hW hbase hg; simp at hg
      slot_pos := by
        change 0 < H.data.cells.nslot C
        have hDirectD1 (i : Fin PT.tiling.m) : (PT.tiling.P i).d = 1 := by
          cases hmode : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode) i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
              exact (hDirect hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode] at hlow
              have hfalse : False := by simpa [Mode.isLow] using hlow
              exact hfalse.elim
        have hnR : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) Q.n_large)
        have hTheta : 0 < κ.θstar := hκ.bucket.2.2.2.2
        have hKcell : 0 < κ.Kcell :=
          lt_of_lt_of_le (div_pos (by norm_num : (0 : ℝ) < 100) hTheta) hκ.Kcell_big
        rw [H.cell_partition.slot_count C]
        rw [hDirectD1 (H.data.cells.cellPatch C)]
        have hRpow : 0 < Real.rpow (T.S.n k : ℝ) (κ.Ac : ℝ) :=
          Real.rpow_pos_of_pos hnR _
        have hnum : 0 < κ.Kcell * Real.rpow (T.S.n k : ℝ) (κ.Ac : ℝ) / 1 := by
          rw [hκ.Ac_eq]
          exact div_pos (mul_pos hKcell (Real.rpow_pos_of_pos hnR _)) (by norm_num)
        exact Nat.ceil_pos.mpr (by simpa using hnum)
      stage_cost := by
        have hδg := Cal.gate_range
        have hδp := Cal.perm_range
        have hnR : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) Q.n_large)
        have hnNonneg : 0 ≤ (T.S.n k : ℝ) := le_of_lt (lt_trans (by norm_num) hnR)
        have hpow3eq : (T.S.n k : ℝ) ^ (-3 : ℝ) =
            ((T.S.n k : ℝ) ^ 3)⁻¹ := by
          calc
            (T.S.n k : ℝ) ^ (-3 : ℝ) =
                ((T.S.n k : ℝ) ^ (3 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt (by linarith)) 3
            _ = ((T.S.n k : ℝ) ^ 3)⁻¹ :=
              congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (T.S.n k : ℝ) 3)
        have hpow4eq : (T.S.n k : ℝ) ^ (-4 : ℝ) =
            ((T.S.n k : ℝ) ^ 4)⁻¹ := by
          calc
            (T.S.n k : ℝ) ^ (-4 : ℝ) =
                ((T.S.n k : ℝ) ^ (4 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt (by linarith)) 4
            _ = ((T.S.n k : ℝ) ^ 4)⁻¹ :=
              congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (T.S.n k : ℝ) 4)
        have hnR2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
        have hn3 : 1 ≤ (T.S.n k : ℝ) ^ 3 := by
          calc
            1 ≤ (2 : ℝ) ^ 3 := by norm_num
            _ ≤ (T.S.n k : ℝ) ^ 3 := by gcongr
        have hn4 : 1 < (T.S.n k : ℝ) ^ 4 := by
          calc
            1 < (2 : ℝ) ^ 4 := by norm_num
            _ ≤ (T.S.n k : ℝ) ^ 4 := by gcongr
        have hnPow3Le : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 := by
          rw [hpow3eq]
          exact inv_le_one_of_one_le₀ hn3
        have hnPow4Lt : (T.S.n k : ℝ) ^ (-4 : ℝ) < 1 := by
          rw [hpow4eq]
          exact inv_lt_one_of_one_lt₀ hn4
        have hdenG : 0 < 1 - Cal.δgate := by linarith [hδg.2]
        have hdenP : 0 < 1 - Cal.δperm := by linarith [hδp.2]
        have hdenN : 0 < 1 - (T.S.n k : ℝ) ^ (-4 : ℝ) := by linarith
        have hInvP : 1 ≤ (1 - Cal.δperm)⁻¹ :=
          (one_le_inv₀ hdenP).2 (by linarith [hδp.1])
        have hnPow4Nonneg : 0 ≤ (T.S.n k : ℝ) ^ (-4 : ℝ) := by positivity
        have hInvN : 1 ≤ (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ :=
          (one_le_inv₀ hdenN).2 (by linarith [hnPow4Nonneg])
        have hInvGpos : 0 < (1 - Cal.δgate)⁻¹ := inv_pos.mpr hdenG
        have hCost := Cal.cost_budget
        have hBC : 1 ≤ (1 - Cal.δperm)⁻¹ *
            (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ := by
          calc
            1 = (1 : ℝ) * 1 := by ring
            _ ≤ (1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ :=
              mul_le_mul hInvP hInvN (by norm_num) (by positivity)
        have hThree : (1 - Cal.δgate)⁻¹ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
          calc
            (1 - Cal.δgate)⁻¹ = (1 - Cal.δgate)⁻¹ * 1 := by ring
            _ ≤ (1 - Cal.δgate)⁻¹ * ((1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹) :=
              mul_le_mul_of_nonneg_left hBC hInvGpos.le
            _ = (1 - Cal.δgate)⁻¹ * (1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ := by ring
            _ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := hCost
        have hGateSmall : (1 - Cal.δgate)⁻¹ ≤ 2 := by linarith [hThree, hnPow3Le]
        rcases hκ.bucket with ⟨hKp, hcp, hKpTheta, hcpTheta, hTheta⟩
        rcases hκ.clock with ⟨_, hTheta0, _⟩
        have hKpR : (40 : ℝ) ≤ (κ.Kp : ℝ) := by exact_mod_cast hKp
        have hProdLo : 40 * κ.θstar ≤ (κ.Kp : ℝ) * κ.θstar := by
          exact mul_le_mul_of_nonneg_right hKpR hTheta.le
        have hThetaBound : κ.θstar ≤ 1 := by
          rw [hTheta0] at hKpTheta
          nlinarith
        have hInvTheta : 1 ≤ κ.θstar⁻¹ := (one_le_inv₀ hTheta).2 hThetaBound
        have hKcell100 : 100 ≤ κ.Kcell := by
          have hBig : 100 * κ.θstar⁻¹ ≤ κ.Kcell := by
            simpa [div_eq_mul_inv] using hκ.Kcell_big
          have hle : 100 ≤ 100 * κ.θstar⁻¹ := by
            calc
              100 = 100 * 1 := by ring
              _ ≤ 100 * κ.θstar⁻¹ := mul_le_mul_of_nonneg_left hInvTheta (by norm_num)
          exact le_trans hle hBig
        have hFinal : (1 - Cal.δgate)⁻¹ ≤ 10 * κ.Kcell := by
          linarith [hGateSmall, hKcell100]
        simpa [Finset.card_empty] using hFinal
      slice_cost := by
        have hKp : (40 : ℝ) ≤ (κ.Kp : ℝ) := by exact_mod_cast hκ.bucket.1
        have hsum : (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
            (Cal.history C).w W) = 1 := by simpa using (Cal.history C).sum_one
        calc
          (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)), (Cal.history C).w W)⁻¹ = 1 := by
            rw [hsum]
            norm_num
          _ ≤ 10 * (κ.Kp : ℝ) := by nlinarith
    }
    refine ⟨P, ?_, ?_⟩
    · exact Or.inr ⟨hDirect, hEnv, by intro W ys; simp [P, priorLaw]⟩
    · intro Φ
      have hPprior (z : P.baseExperiment.State) : P.baseExperiment.prior z = priorLaw.w := by
        rfl
      have hRprior (z : (R.baseExperiment C v).State) :
          (R.baseExperiment C v).prior z = priorLaw.w := by
        exact hRawPrior z.1 z.2.2 v hcell hEven
      have hConstP : P.baseExperiment.law.E (fun _ => Φ priorLaw.w) = Φ priorLaw.w := by
        unfold FinLaw.E
        rw [← Finset.sum_mul, P.baseExperiment.law.sum_one]
        ring
      have hConstR : (R.baseExperiment C v).law.E (fun _ => Φ priorLaw.w) = Φ priorLaw.w := by
        unfold FinLaw.E
        rw [← Finset.sum_mul, (R.baseExperiment C v).law.sum_one]
        ring
      calc
        P.baseExperiment.expect Φ = P.baseExperiment.law.E (fun _ => Φ priorLaw.w) := by
          unfold PriorExperiment.expect
          apply Lane_q_s16_prod2.finLaw_E_congr_of_supported
          intro z hz
          simp [hPprior z]
        _ = Φ priorLaw.w := hConstP
        _ = (R.baseExperiment C v).expect Φ := by
          symm
          calc
            (R.baseExperiment C v).expect Φ =
                (R.baseExperiment C v).law.E (fun _ => Φ priorLaw.w) := by
              unfold PriorExperiment.expect
              apply Lane_q_s16_prod2.finLaw_E_congr_of_supported
              intro z hz
              simp [hRprior z]
            _ = Φ priorLaw.w := hConstR

end Lane_sol_fix2_s16
end HypercubeRamsey.S16
