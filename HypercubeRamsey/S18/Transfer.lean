import HypercubeRamsey.S18.Transitions

namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- A fixed actual prefix failure; one critical cell may be held fixed. -/
structure CriticalTransferData (D : LateData hPT) where
  failure : PrefixIndex D
  valid : D.prefixValid failure
  omitted : Option D.geom.Cell
  fixed : Config D.fresh

namespace CriticalTransferData
variable {D : LateData hPT} (X : CriticalTransferData D)
noncomputable def target : Pos T k := flipPos X.failure.2.1.1 X.failure.2.2.2.2
noncomputable def criticalCoords : Finset (Fin (T.S.n k)) :=
  (PT.tiling.bulkCoords (D.geom.patchOf X.target)).filter fun a =>
    D.geom.ids a - D.geom.syndrome X.target ∉ D.geom.Lsub ∧
      X.omitted ≠ some (D.geom.cellOf (flipPos X.target a))
noncomputable def criticalCells : Finset D.geom.Cell :=
  X.criticalCoords.image (fun a => D.geom.cellOf (flipPos X.target a))
abbrev Raw (X : CriticalTransferData D) := ∀ C, D.fresh.Pool C × D.fresh.State C
noncomputable def rawLaw : FinLaw X.Raw :=
  FinLaw.pi fun C => if C ∈ X.criticalCells then D.typicalFresh C
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
def state (s : X.Raw) : Config D.fresh := fun C => (s C).2
noncomputable def experiment := FinLaw.bind X.rawLaw (fun s => D.encoding.kernels.refRun (X.state s))
noncomputable def criticalLabel (s : X.Raw) (a : Fin (T.S.n k)) :=
  D.earlyLabel (X.state s) (flipPos X.target a)
noncomputable def sameBlock (a a' : Fin (T.S.n k)) : Prop :=
  D.geom.ids a - D.geom.ids a' ∈ D.geom.Lsub ∨
    ((∃ t ∈ PT.tiling.Icoord (D.geom.patchOf X.target), D.geom.ids a - D.geom.ids t ∈ D.geom.Lsub) ∧
     (∃ t ∈ PT.tiling.Icoord (D.geom.patchOf X.target), D.geom.ids a' - D.geom.ids t ∈ D.geom.Lsub))
noncomputable def blockCells (a : Fin (T.S.n k)) :=
  (X.criticalCoords.filter (X.sameBlock a)).image (fun t => D.geom.cellOf (flipPos X.target t))
/-- Actual predecessor closure. Only earlier-class two-edge predecessors are added. -/
noncomputable def predecessors (X : CriticalTransferData D) : ℕ → Finset (Pos T k)
  | 0 => {X.failure.2.1.1}
  | n + 1 => let prev := X.predecessors n
    prev ∪ (Finset.univ.filter fun b' => ∃ b ∈ prev, ∃ j j' : Fin D.geom.r,
      D.geom.classOf b = some j ∧ D.geom.classOf b' = some j' ∧ j'.val < j.val ∧
        ∃ a a', flipPos b a = flipPos b' a')
noncomputable def directEven := (X.predecessors D.geom.r).biUnion fun b =>
  Finset.univ.image (flipPos b)
noncomputable def erased := X.directEven.filter fun w =>
  ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = X.target a

/-- Single and pair witness semantics are fixed independently of any protocol. -/
noncomputable def allowed (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) : Prop :=
  x ∈ PT.envelope (D.geom.patchOf X.target) ∧
    ∀ y, z = some y → y ∈ PT.envelope (D.geom.patchOf X.target) ∧ D.nonconflict X.target x y
noncomputable def survives (s : X.Raw) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) : Prop :=
  ∀ a ∈ X.criticalCoords, Hits (T.S.E k) PT.tiling.c x (X.criticalLabel s a) ∧
    ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y (X.criticalLabel s a)
noncomputable def deviates (X : CriticalTransferData D) (U : Law (T.S.N k)) (x : Fin (T.S.N k))
    (z : Option (Fin (T.S.N k))) : Prop :=
  match z with
  | none => 10 * bstar T k < |rowDeg (T.S.E k) PT.tiling.c x U - 1 / 2|
  | some y => 10 * bstar T k <
    |(∑ u, U.w u * (if Hits (T.S.E k) PT.tiling.c x u ∧ Hits (T.S.E k) PT.tiling.c y u
      then 1 else 0)) - 1 / 4|
end CriticalTransferData

/-- Geometry needed to erase one outer word and assign one responding block
per remaining sketch. This replaces probability bounds on geometry nodes. -/
structure TransferGeometry {D : LateData hPT} (X : CriticalTransferData D) : Prop where
  critical_count : (T.S.n k : ℝ) - (κ.KB + 4 * κ.A0 + 10) * Real.log (T.S.n k) ≤ X.criticalCoords.card
  distinct_cells : ∀ a ∈ X.criticalCoords, ∀ a' ∈ X.criticalCoords,
    D.geom.cellOf (flipPos X.target a) = D.geom.cellOf (flipPos X.target a') → a = a'
  predecessor_radius : ∀ b ∈ X.predecessors D.geom.r,
    b ∈ cubeBall X.failure.2.1.1 (2 * D.geom.r)
  erased_internal : X.erased ⊆ {X.target} ∨
    ∃ a ∈ PT.tiling.Icoord (D.geom.patchOf X.target),
      X.erased ⊆ (PT.tiling.Icoord (D.geom.patchOf X.target)).image (flipPos (flipPos X.target a))
  block_size : ∀ a, (X.criticalCoords.filter (X.sameBlock a)).card ≤
    max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r
  /-- An affected un-erased direct site consults a single block of whole cells. -/
  one_block : ∀ w ∈ X.directEven \ X.erased,
    ∃ a, D.directCells w ∩ X.criticalCells ⊆ X.blockCells a

/-- Total finite adaptive protocol. Requests depend on preceding replies;
answers read only the requested block. Seeds have their own independent law.
The recurrence determines all replies, including off-path abort behavior. -/
structure TransferProtocol {D : LateData hPT} (X : CriticalTransferData D) where
  Seed : Type
  [seedFin : Fintype Seed]
  seedLaw : FinLaw Seed
  Reply : Type
  [replyFin : Fintype Reply]
  defaultReply : Reply
  reply_card : (Fintype.card Reply : ℝ) ≤
    1 + Real.exp (Real.log (T.S.n k) ^ 8 * sketchLength T k)
  steps : ℕ
  steps_bound : (steps : ℝ) ≤ (T.S.n k : ℝ) * Real.log (T.S.n k) ^ 20
  request : Seed → List Reply → Fin (T.S.n k)
  answer : Seed → List Reply → X.Raw → Reply
  answer_local : ∀ seed t s s',
    (∀ C ∈ X.blockCells (request seed t), s C = s' C) → answer seed t s = answer seed t s'
  replies : Seed → X.Raw → ℕ → List Reply
  replies_zero : ∀ seed s, replies seed s 0 = []
  replies_step : ∀ seed s t, replies seed s (t + 1) =
    replies seed s t ++ [answer seed (replies seed s t) s]
  calls_bound : ∀ seed s a,
    ((Finset.range steps).filter fun t => X.sameBlock a (request seed (replies seed s t))).card ≤
      ⌈Real.log (T.S.n k) ^ 20⌉₊
  output : Seed → List Reply → Law (T.S.N k)
  broad : ∀ seed s, (output seed (replies seed s steps)).WidthLE (κ.α * T.S.n k / 2)
  /-- Pointwise deletion and integration of erased sketches precede seed fixing. -/
  reduction : X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
    Real.exp (1000 * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℝ) *
      ∑ j : Fin D.geom.r, D.error X.target j) *
    (FinLaw.bind X.rawLaw (fun _ => seedLaw)).pr (fun sseed =>
      ∃ x z, X.allowed x z ∧ X.survives sseed.1 x z ∧
        X.deviates (output sseed.2 (replies sseed.2 sseed.1 steps)) x z)

attribute [instance] TransferProtocol.seedFin TransferProtocol.replyFin

/-- An actual complete reply range for each block, with other blocks fixed. -/
def ReplyRangeBound {D : LateData hPT} {X : CriticalTransferData D} (P : TransferProtocol X) : Prop :=
  ∀ (seed : P.Seed) (a : Fin (T.S.n k)) (fixed : X.Raw),
    ((Finset.univ.filter fun s : X.Raw => ∀ C, C ∉ X.blockCells a → s C = fixed C).image
      (fun s => P.replies seed s P.steps)).card ≤ Real.exp (Real.rpow (T.S.n k : ℝ) 0.4)

/-- Cylinder factorization follows the actual request/answer recurrence. -/
def CylinderFacts {D : LateData hPT} {X : CriticalTransferData D} (P : TransferProtocol X) : Prop :=
  ∀ seed t transcript, t ≤ P.steps →
    ∃ cylinders : Fin (T.S.n k) → X.Raw → Prop,
      (∀ a s s', (∀ C ∈ X.blockCells a, s C = s' C) → (cylinders a s ↔ cylinders a s')) ∧
      (∀ s, P.replies seed s t = transcript ↔ ∀ a, cylinders a s)

/-- Exact tilted whole-state law, conditioned on witness survival. -/
noncomputable def tiltedLaw {D : LateData hPT} (X : CriticalTransferData D)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) : FinLaw X.Raw :=
  let good := Finset.univ.filter fun s => X.survives s x z
  if h : 0 < ∑ s ∈ good, X.rawLaw.w s then FinLaw.cond X.rawLaw good h else X.rawLaw

/-- The integrated tilt estimate uses a uniform witness independent of raw
blocks. Singleton and pair estimates are separate, avoiding a factor N. -/
def TiltedDeviationBound {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) (c : ℝ) : Prop :=
  ∀ seed,
    ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x none then (tiltedLaw X x none).pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x none) else 0) /
      (PT.tiling.P (D.geom.patchOf X.target)).M ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) c)) ∧
    ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      ∑ z ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x (some z) then (tiltedLaw X x (some z)).pr (fun s =>
        X.deviates (P.output seed (P.replies seed s P.steps)) x (some z)) else 0) /
      (PT.tiling.P (D.geom.patchOf X.target)).M ^ 2 ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) c))

/-- Whole-cell survival and uniform witness moments. The fixed coefficient
`64 * κ.KB` absorbs the low-mode degree drift and marginal perturbations
(17:334–347 and 18:630–645), and is chosen before the eventual stage. -/
def SurvivalFacts {D : LateData hPT} (X : CriticalTransferData D) : Prop :=
  (∀ a ∈ X.criticalCoords, ∀ x z, X.allowed x z →
    (D.typicalFresh (D.geom.cellOf (flipPos X.target a))).pr (fun Ps =>
      Hits (T.S.E k) PT.tiling.c x (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a)) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y
        (D.fresh.label (D.geom.cellOf (flipPos X.target a)) Ps.2 (flipPos X.target a))) ≥ 0.15) ∧
  ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    if X.allowed x none then ((2 : ℝ) ^ X.criticalCoords.card * X.rawLaw.pr (fun s => X.survives s x none)) ^ 2 else 0) /
      (PT.tiling.P (D.geom.patchOf X.target)).M ≤ Real.exp ((64 * κ.KB) * Real.log (T.S.n k))) ∧
  ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    ∑ z ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    if X.allowed x (some z) then ((4 : ℝ) ^ X.criticalCoords.card *
      X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 else 0) /
      (PT.tiling.P (D.geom.patchOf X.target)).M ^ 2 ≤ Real.exp ((64 * κ.KB) * Real.log (T.S.n k)))

/-- Witness averaging is against the full patch, independently of raw blocks. -/
noncomputable def witnessMean {D : LateData hPT} (X : CriticalTransferData D) (pair : Bool)
    (f : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ) : ℝ :=
  if pair then (∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
    ∑ z ∈ (PT.tiling.P (D.geom.patchOf X.target)).X, f x (some z)) /
      (PT.tiling.P (D.geom.patchOf X.target)).M ^ 2
  else (∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X, f x none) /
    (PT.tiling.P (D.geom.patchOf X.target)).M
noncomputable def likelihood {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) (seed : P.Seed) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (s : X.Raw) (t : ℕ) : ℝ :=
  (tiltedLaw X x z).pr (fun s' => P.replies seed s' t = P.replies seed s t) /
    X.rawLaw.pr (fun s' => P.replies seed s' t = P.replies seed s t)
noncomputable def factorException {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) (seed : P.Seed) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (s : X.Raw) (t : ℕ) : Prop :=
  t > 0 ∧ |likelihood P seed x z s t / likelihood P seed x z s (t - 1) - 1| >
    κ.KB * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℝ) * bstar T k
noncomputable def stoppingTime {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) (seed : P.Seed) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (s : X.Raw) (cstop : ℝ) : ℕ :=
  let stops := (Finset.range (P.steps + 1)).filter fun t =>
    factorException P seed x z s t ∨ Real.exp (Real.rpow (T.S.n k : ℝ) cstop) < likelihood P seed x z s t
  if h : stops.Nonempty then stops.min' h else P.steps

/-- Stopped second moment and integrated exception stops. The likelihood is
an actual prefix Radon–Nikodym ratio; it is not a free martingale field. -/
def StopFacts {D : LateData hPT} {X : CriticalTransferData D}
    (P : TransferProtocol X) (cstop : ℝ) : Prop :=
  ∀ seed pair,
    (∀ t, witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.E (fun s =>
      likelihood P seed x z s (min t (stoppingTime P seed x z s cstop)) ^ 2) else 0) ≤ 2) ∧
    witnessMean X pair (fun x z => if X.allowed x z then (tiltedLaw X x z).pr (fun s =>
      factorException P seed x z s (stoppingTime P seed x z s cstop)) else 0) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) cstop)

def TransferBound (D : LateData hPT) (c : ℝ) : Prop :=
  ∀ X : CriticalTransferData D,
    X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) c)

end HypercubeRamsey.S18
