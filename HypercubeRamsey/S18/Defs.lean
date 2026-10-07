import HypercubeRamsey.S18.Needs

/-!
# Section 18 data definitions

This file fixes the finite experiments used by the Section 18 nodes. The
initial law, reference transition, and actual class sampler remain distinct;
the shared `LateEncoding` supplies the history and reference-process encoding.
-/

namespace HypercubeRamsey
namespace S18

open Classical Filter
open scoped BigOperators

/-- Host density `C_n = N / 2^n`. -/
noncomputable def densityScale (T : Stage) (k : ℕ) : ℝ :=
  (T.S.N k : ℝ) / (2 : ℝ) ^ T.S.n k

/-- The low-mode error budget `e_{w,j}` from Section 18. -/
noncomputable def lateError (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (j : ℕ) : ℝ :=
  Real.rpow (densityScale T k) (-κ.β) *
    Real.exp (-κ.β * PT.tiling.gain i) *
    Real.rpow 2 (-κ.β * j)

/-- The finite-index conclusions of the summable late-error schedule. -/
def ScheduleAt (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (G : LowGeom PT) (Kβ : ℝ) : Prop :=
  ∀ i : Fin PT.tiling.m,
    (∀ j : Fin G.r, (T.S.n k : ℝ) ^ (-0.02 : ℝ) ≤
      lateError κ T k PT i j.val) ∧
    (∑ j : Fin G.r, lateError κ T k PT i j.val) ≤
      Kβ * Real.rpow (densityScale T k) (-κ.β) *
        Real.exp (-κ.β * PT.tiling.gain i)

/-- A sufficiently large stage index: enough to enter every fixed-constant
asymptotic regime used by the Section 18 estimates. -/
def LargeIndex (κ : CConsts) (T : Stage) (k : ℕ) : Prop :=
  Real.exp κ.Q0 ≤ (T.S.n k : ℝ)

/-- A bad sequence eventually enters the fixed-constant Section 18 range. -/
theorem eventually_largeIndex (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, LargeIndex κ T k := by
  let n₀ := ⌈Real.exp κ.Q0⌉₊
  have hn : ∀ᶠ k in atTop, n₀ ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop n₀
  filter_upwards [hn] with k hk
  have hcast : (n₀ : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hk
  have hceil : Real.exp κ.Q0 ≤ (n₀ : ℝ) := Nat.le_ceil _
  exact le_trans hceil hcast

/-- D18.L: data for the initial lists and late-process experiment. The initial
and current priors are kept separate; a current prior is indexed by the
entering history and therefore reads only data already exposed at that point. -/
structure LateData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) where
  geom : LowGeom PT
  fresh : FreshCell geom
  events : ListEvent fresh
  encoding : LateEncoding fresh
  l16_valid : L16QuantitativeValidity geom fresh
  large_index : LargeIndex κ T k
  events_eq : encoding.events = events
  initialPrior : Pos T k → Config fresh → Law (T.S.N k)
  currentPrior : ∀ j : Fin geom.r, Pos T k →
    encoding.base.History j.castSucc → Law (T.S.N k)
  palette : Pos T k → Finset (Fin (T.S.N k))
  fallback : Pos T k → Fin (T.S.N k)
  initialValid : Pos T k → Config fresh → Prop
  remainingNeighbors : Pos T k → Fin geom.r → ℕ

/-- D18.T: the requirement predicates and deletion kernels at fixed entering
histories. The predicates are attached to the row outputs of the specified
reference process, not to a reconditioned process. -/
structure TransitionData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) where
  gate : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc → Prop
  R1 : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    D.encoding.base.ClassRows j → Prop
  R2 : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    D.encoding.base.ClassRows j → Prop
  R3 : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    D.encoding.base.ClassRows j → Prop
  prefixMass : ∀ j : Fin D.geom.r,
    ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j},
    D.encoding.base.History j.castSucc → D.encoding.base.ClassRows j → ℝ
  deleted : ∀ j : Fin D.geom.r,
    ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j},
    D.encoding.base.History j.castSucc → FinLaw (D.encoding.base.RowOut b.1)
  deletionLength : ∀ j : Fin D.geom.r,
    ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j}, ℕ
  bad : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    Finset (D.encoding.base.ClassRows j)
  alarm : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    Finset (D.encoding.base.ClassRows j)

/-- D18.C: the critical-cell transfer data for one local Requirement-2 failure.
The protocol is total on all block inputs and seeds. -/
structure CriticalTransferData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) where
  criticalCells : Finset D.geom.Cell
  noncriticalState : ∀ C, D.fresh.State C
  block : D.geom.Cell → ℕ
  blockCount : ℕ
  block_lt : ∀ C, C ∈ criticalCells → block C < blockCount
  Transcript : Type
  [transcriptFin : Fintype Transcript]
  [transcriptDec : DecidableEq Transcript]
  Seed : Type
  [seedFin : Fintype Seed]
  blockLaw : FinLaw (Fin blockCount → ∀ C, D.fresh.State C)
  protocol : (Fin blockCount → ∀ C, D.fresh.State C) →
    (∀ C, D.fresh.State C) → Seed → Transcript
  stepFailure : Fin 12 → Finset Transcript
  badTranscripts : Finset Transcript

/-- D18.G: terminal requirements on the initial input law. The late bad-event
probabilities are evaluated under the reference kernels at the fixed initial
state. -/
abbrev PairAssignment (T : Stage) (k : ℕ) :=
  Pos T k → Fin (T.S.N k) × Fin (T.S.N k)

structure TerminalRequirements {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) where
  poolGood : D.encoding.InitInput → Prop
  initialAvoid : D.encoding.InitInput → Prop
  pLate : D.encoding.InitInput → ℝ
  failureEvents : Fin 5 → Finset D.encoding.InitInput

/-- D18.I: fixed pair-test data for rows in one palette. -/
structure InitialPairData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) where
  rows : Finset (Pos T k)
  palette : Finset (Fin (T.S.N k))
  validPair : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → Prop
  initialWeight : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ
  consultationScope : Pos T k → Finset D.geom.Cell
  nonisolates : ℕ
  rank : ℕ
  pairSampler : D.encoding.base.History (Fin.last D.geom.r) →
    FinLaw (PairAssignment T k)
  endpointStepEvents : Fin 5 → Finset (PairAssignment T k)
  hallObstructionEvents : Fin 3 → Finset (PairAssignment T k)

/-- A final two-endpoint assignment on the even and odd cube roles. This is
the output consumed by the existing rows-to-cube embedding lemma. -/
structure CubeAssignment (T : Stage) (k : ℕ) (c : Colour) where
  evenLabel : {v : CubePos (T.S.n k) // IsEvenRole v} → Fin (T.S.N k)
  oddLabel : {v : CubePos (T.S.n k) // ¬ IsEvenRole v} → Fin (T.S.N k)
  even_injective : Function.Injective evenLabel
  odd_injective : Function.Injective oddLabel
  edge : ∀ a b, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj a.1 b.1 →
    Hits (T.S.E k) c (evenLabel a) (oddLabel b)

/-- L18.1's three local probability and comparison conclusions. -/
def CurrentListCapFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) : Prop :=
  (∀ j : Fin D.geom.r, ∀ h : D.encoding.base.History j.castSucc,
    R.gate j h → ∀ b : Pos T k, b ∈ D.encoding.base.classes j →
      ∀ i : Fin (T.S.n k), IsEvenRole (flipPos b i) → ∀ y,
        (T.S.N k : ℝ) * (D.currentPrior j (flipPos b i) h).w y ≤
          8 * κ.KB / densityScale T k *
            Real.exp (-199 * PT.tiling.gain (D.geom.patchOf (flipPos b i))) *
              Real.rpow 2 (-(D.remainingNeighbors (flipPos b i) j : ℝ))) ∧
  (∀ j : Fin D.geom.r, ∀ w : Pos T k, ∀ h : D.encoding.base.History j.castSucc,
    ¬ D.initialValid w h.1 →
      D.currentPrior j w h = Law.dirac (D.fallback w))

/-- L18.1's local probability and comparison conclusions, including the
current-list cap supplied by L18.0b. -/
def LocalTransitionFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) : Prop :=
  LargeIndex κ T k ∧ CurrentListCapFacts D R ∧
  (∀ j h, R.gate j h →
    (D.encoding.kernels.referenceTransition j h).pr
      (fun out => ¬ R.R1 j h out) ≤ Real.exp (-(T.S.n k : ℝ) ^ (0.09 : ℝ))) ∧
  (∀ j h, R.gate j h → ∀ out, R.R1 j h out → R.R2 j h out →
    ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j},
      Real.exp (-((κ.α / 100) * (T.S.n k : ℝ))) ≤ R.prefixMass j b h out ∧
      (D.encoding.kernels.refK j b h).w (out b) ≤
        Real.exp (1000 * R.deletionLength j b *
          lateError κ T k PT (D.geom.patchOf b.1) j.val) *
          (R.deleted j b h).w (out b)) ∧
  (∀ j h, R.gate j h →
    (D.encoding.kernels.referenceTransition j h).pr
      (fun out => R.R1 j h out ∧ R.R2 j h out ∧ ¬ R.R3 j h out) ≤
        Real.exp (-(T.S.n k : ℝ) ^ (0.09 : ℝ)))

/-- L18.2's transfer estimate for every fixed noncritical configuration and
mask profile, also when one critical cell is omitted. -/
def TransferBound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    {R : TransitionData D} (X : CriticalTransferData D R) : Prop :=
  L16QuantitativeValidity D.geom D.fresh ∧ D.encoding.events = D.events ∧
    ∀ seed : X.Seed,
      X.blockLaw.pr
        (fun blocks => X.protocol blocks X.noncriticalState seed ∈ X.badTranscripts) ≤
        Real.exp (-(T.S.n k : ℝ) ^ (0.01 : ℝ))

/-- One of the twelve transcript estimates in the L18.2 decomposition. -/
def TransferStepBound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    {R : TransitionData D} (X : CriticalTransferData D R) (s : Fin 12) : Prop :=
  ∀ seed : X.Seed,
    X.blockLaw.pr
      (fun blocks => X.protocol blocks X.noncriticalState seed ∈ X.stepFailure s) ≤
      Real.exp (-(T.S.n k : ℝ) ^ (0.01 : ℝ))

/-- P18.3 output: a positive terminal event satisfying all three requirements. -/
structure TerminalCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) where
  requirements : TerminalRequirements D R
  terminal : Finset D.encoding.InitInput
  positive : 0 < ∑ x ∈ terminal, D.encoding.permLaw.w x
  pools : ∀ x ∈ terminal, requirements.poolGood x
  initial : ∀ x ∈ terminal, requirements.initialAvoid x
  late : ∀ x ∈ terminal,
    requirements.pLate x ≤ Real.exp (-(T.S.n k : ℝ) ^ (0.01 : ℝ))

/-- P18.4b's fixed-history sampler data before the reached-history load
estimate is applied. -/
structure ClassSamplerData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) where
  act : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc →
    FinLaw (D.encoding.base.ClassRows j)
  enter : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc → Prop
  sampler : D.encoding.SamplerSpec act enter R.bad R.alarm

/-- P18.4 output: a fixed-history conditional sampler and a high-probability full late run. -/
structure CompletionCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R) where
  samplers : ClassSamplerData D R
  full : D.encoding.base.History (Fin.last D.geom.r) → Prop
  fullRun :
    (FinLaw.bind (D.encoding.terminalLaw C.terminal C.positive)
      (fun x => D.encoding.base.runFull samplers.act (D.encoding.initialState x))).pr
      (fun pair => full pair.2) ≥ 1 - (T.S.n k : ℝ)⁻¹

/-- P18.4c's reached-history full-run estimate. -/
def FullRunProbability {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : ClassSamplerData D R) (full : D.encoding.base.History (Fin.last D.geom.r) → Prop) : Prop :=
  (FinLaw.bind (D.encoding.terminalLaw C.terminal C.positive)
    (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).pr
    (fun pair => full pair.2) ≥ 1 - (T.S.n k : ℝ)⁻¹

/-- P18.5 output: a symmetric kernel family bounding the joint endpoint law. -/
structure EndpointCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C) where
  K : ℝ
  Cprime : ℝ
  kernel : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ
  K_pos : 0 < K
  Cprime_pos : 0 < Cprime
  palette_nonempty : A.palette.Nonempty
  kernel_nonneg : ∀ v x z, 0 ≤ kernel v x z
  row_sum : ∀ v x, ∑ z, kernel v x z ≤ K / (A.palette.card : ℝ)
  entry_bound : ∀ v x z,
    kernel v x z ≤ (A.palette.card : ℝ)⁻¹ ^ 2 * Real.exp (0.01 * (T.S.n k : ℝ))
  jointBound : ∀ assignment : PairAssignment T k,
    (D.encoding.experiment C.terminal C.positive H.samplers.act
      (pairSampler := A.pairSampler)).pr
      (fun out => H.full out.1.2 ∧
        ∀ v ∈ A.rows, out.2 v = assignment v) ≤
      Real.exp (2 * (D.geom.r : ℝ)) * K ^ A.rows.card *
        Real.exp (0.01 * (T.S.n k : ℝ) * A.nonisolates +
          Cprime * A.rows.card * A.rank) *
        ∏ v ∈ A.rows, kernel v (assignment v).1 (assignment v).2

/-- L18.6 output: the palette matchings assembled into an injective cube assignment. -/
structure HallCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) where
  assignment : CubeAssignment T k PT.tiling.c

/-- One P18.3 local terminal-event estimate. -/
def TerminalStepBound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R) (s : Fin 5) : Prop :=
  D.encoding.permLaw.pr (fun x => x ∈ Q.failureEvents s) ≤
    Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))

/-- P18.5a's initial pair and palette facts. -/
def PairInitialFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (A : InitialPairData D) : Prop :=
  A.palette.Nonempty ∧
  (∀ v x z, A.validPair v x z ↔ A.validPair v z x) ∧
  (∀ v x z, 0 ≤ A.initialWeight v x z) ∧
  (∀ v, (A.consultationScope v).card ≤ T.S.n k * (T.S.n k + 1)) ∧
  (∀ v, A.palette ⊆ D.palette v) ∧
  (∀ v s, D.initialValid v s →
    (D.initialPrior v s).SupportedIn (PT.tiling.P (D.geom.patchOf v)).X) ∧
  (∀ v ∈ A.rows, ∃ x ∈ A.palette, ∃ z ∈ A.palette,
    x ≠ z ∧ A.validPair v x z)

/-- One of the P18.5b–f comparison steps in the fixed endpoint experiment. -/
def EndpointStepBound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C) (s : Fin 5) : Prop :=
    FullRunProbability D R C H.samplers H.full ∧
    D.encoding.SamplerSpec H.samplers.act H.samplers.enter R.bad R.alarm ∧
    (∀ j h, H.samplers.enter j h →
      ∀ out, 0 ≤ (H.samplers.act j h).w out) ∧
    (D.encoding.experiment C.terminal C.positive H.samplers.act
    (pairSampler := A.pairSampler)).pr
    (fun out => H.full out.1.2 ∧ out.2 ∈ A.endpointStepEvents s) ≤
      Real.exp (-(T.S.n k : ℝ) ^ (0.01 : ℝ))

/-- One L18.6 obstruction sum in the endpoint multigraph. -/
def HallStepBound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H) (s : Fin 3) : Prop :=
  FullRunProbability D R C H.samplers H.full ∧
  (D.encoding.experiment C.terminal C.positive H.samplers.act
    (pairSampler := A.pairSampler)).pr
    (fun out => H.full out.1.2 ∧ out.2 ∈ A.hallObstructionEvents s) < 1 / 3

/-- P18.4a's balanced-mask marginal bound in the iid-slot baseline. -/
def MaskBalance {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) : Prop :=
  ∀ b j, D.geom.classOf b = some j → ∀ y,
    (∑ m : D.encoding.base.AllowedMask b,
      (D.encoding.kernels.maskProfile b).w m *
        (if y ∈ m.1 then 1 / (m.1.card : ℝ) else 0)) ≤
      2 / (T.S.N k / 3 / D.geom.r : ℝ)


end S18
end HypercubeRamsey
