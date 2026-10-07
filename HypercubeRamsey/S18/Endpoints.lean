import HypercubeRamsey.S18.Completion

namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
abbrev PairAssignment (T : Stage) (k : ℕ) := Pos T k → Fin (T.S.N k) × Fin (T.S.N k)
abbrev PaletteIndex (D : LateData hPT) := Σ i : Fin PT.tiling.m, Fin (D.chi i)
namespace LateData
variable (D : LateData hPT)
def rolePalette (v : Pos T k) : PaletteIndex D := ⟨D.geom.patchOf v, D.colourOf v⟩
noncomputable def paletteRows (p : PaletteIndex D) :=
  Finset.univ.filter fun v : Pos T k => IsEvenRole v ∧ D.rolePalette v = p
noncomputable def paletteScale (p : PaletteIndex D) : ℝ := (PT.tiling.P p.1).M / (D.chi p.1 : ℝ)
noncomputable def finalPrior (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k) :=
  D.priorAt (Fin.last D.geom.r) v h
noncomputable def pairLaw (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k) :
    FinLaw (Fin (T.S.N k) × Fin (T.S.N k)) :=
  let q := D.finalPrior h v
  let law : FinLaw (Fin (T.S.N k)) := ⟨q.w, q.nonneg, q.sum_eq_one⟩
  let product := FinLaw.bind law (fun _ => law)
  let good := Finset.univ.filter fun p => D.nonconflict v p.1 p.2
  if hz : 0 < ∑ p ∈ good, product.w p then FinLaw.cond product good hz
  else FinLaw.dirac (D.fallback, D.fallback)
noncomputable def pairSampler (h : D.encoding.base.History (Fin.last D.geom.r)) : FinLaw (PairAssignment T k) :=
  FinLaw.pi (D.pairLaw h)
noncomputable def geometricAdj (v w : Pos T k) : Prop :=
  v ≠ w ∧ (¬ Disjoint (D.directCells v) (D.directCells w) ∨
    ∃ b, (∃ j, D.geom.classOf b = some j) ∧
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b ∧
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj w b)
noncomputable def overlapGraph (S : Finset (Pos T k)) : SimpleGraph {v // v ∈ S} where
  Adj v w := D.geometricAdj v.1 w.1
  symm := by
    constructor
    intro v w h
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨b, hb, hv, hw⟩
    · exact Or.inl (fun hd => h hd.symm)
    · exact Or.inr ⟨b, hb, hw, hv⟩
  loopless := by constructor; intro v h; exact h.1 rfl
noncomputable def rank (S : Finset (Pos T k)) : ℕ := S.card - Nat.card (D.overlapGraph S).ConnectedComponent
noncomputable def nonisolates (S : Finset (Pos T k)) : Finset (Pos T k) :=
  S.filter fun v => ∃ w ∈ S, D.geometricAdj v w
end LateData

/-- One fixed tuple in one actual palette. All weights, scopes and graph
statistics are definitions of this tuple rather than free fields. -/
structure InitialPairData (D : LateData hPT) where
  paletteIndex : PaletteIndex D
  rows : Finset (Pos T k)
  rows_subset : rows ⊆ D.paletteRows paletteIndex
  small : rows.card ≤ T.S.n k
namespace InitialPairData
variable {D : LateData hPT} (A : InitialPairData D)
noncomputable def scope := A.rows.biUnion D.directCells
noncomputable def validPair (A : InitialPairData D) (v : Pos T k) (x z : Fin (T.S.N k)) : Prop :=
  x ∈ D.palette v ∧ z ∈ D.palette v ∧ x ∈ PT.envelope (D.geom.patchOf v) ∧
    z ∈ PT.envelope (D.geom.patchOf v) ∧ D.nonconflict v x z
noncomputable def phi (assignment : PairAssignment T k) (s : Config D.fresh) : ℝ :=
  if ∀ v ∈ A.rows, D.initialValid v s then
    (D.chi A.paletteIndex.1 : ℝ) ^ (2 * A.rows.card) * ∏ v ∈ A.rows,
      if A.validPair v (assignment v).1 (assignment v).2 ∧
        (D.initialPrior v s).w (assignment v).1 ≠ 0 ∧ (D.initialPrior v s).w (assignment v).2 ≠ 0 then
        D.initialWeight v s (assignment v).1 * D.initialWeight v s (assignment v).2 else 0
  else 0
noncomputable def termTest {δ ε : ℝ} (C : TerminalCertificate D δ ε) (assignment : PairAssignment T k) :=
  (D.encoding.terminalLaw (terminalSet D δ) C.positive).E fun x =>
    if D.poolGate (D.expandCells A.scope) x then A.phi assignment (D.encoding.initialState x) else 0
noncomputable def permTest (assignment : PairAssignment T k) := D.encoding.permLaw.E fun x =>
  if D.poolGate (D.expandCells A.scope) x then A.phi assignment (D.encoding.initialState x) else 0
noncomputable def permFreshTest (assignment : PairAssignment T k) := D.encoding.permLaw.E fun x =>
  if D.poolGate (D.expandCells A.scope) x then (D.freshConfigLaw x.1).E (A.phi assignment) else 0
noncomputable def iidFreshTest (assignment : PairAssignment T k) := D.encoding.iidLaw.E fun pools =>
  if ∀ C ∈ A.scope, D.fresh.typical C (pools C) then
    (D.freshConfigLaw pools).E (A.phi assignment) else 0
end InitialPairData

noncomputable def pairExperiment (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun) :=
  D.encoding.experiment (terminalSet D δ) C.positive H.samplers.act D.pairSampler
noncomputable def endpointProbability (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (A : InitialPairData D) (assignment : PairAssignment T k) :=
  (pairExperiment D C H).pr fun out => D.full δ out.1.1 out.1.2 ∧
    ∀ v ∈ A.rows, out.2 v = assignment v

def PairInitialFacts (D : LateData hPT) (δ : ℝ) (K : ℝ) : Prop :=
  (∀ p, (D.paletteRows p).card ≤ K * D.paletteScale p / densityScale T k) ∧
  (∀ p, (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) ≤ (D.paletteRows p).card) ∧
  (∀ v, ((Finset.univ.filter fun w => D.geometricAdj v w).card : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.Ac + 5)) ∧
  (∀ S, (D.nonisolates S).card ≤ 2 * D.rank S) ∧
  ∀ x h, D.full δ x h → ∀ v, IsEvenRole v →
    (∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) ≥ 1 / 2 ∧
    ∀ p, 0 < (D.pairLaw h v).w p → p.1 ≠ p.2 ∧ p.1 ∈ D.palette v ∧ p.2 ∈ D.palette v ∧
      ∀ b : {b : Pos T k // ¬ IsEvenRole b}, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
        Hits (T.S.E k) PT.tiling.c p.1 (D.oddAt h b) ∧ Hits (T.S.E k) PT.tiling.c p.2 (D.oddAt h b)

/-- The isolate kernel of TeX 1064–1068, with no initial-list gates. -/
noncomputable def isolatedWeight (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) : ℝ :=
  if x ∈ D.palette v ∧ z ∈ D.palette v ∧ x ∈ PT.envelope (D.geom.patchOf v) ∧
    z ∈ PT.envelope (D.geom.patchOf v) ∧ D.nonconflict v x z then
    (D.chi (D.geom.patchOf v) : ℝ) ^ 2 * D.encoding.iidLaw.E (fun pools =>
      if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
        (D.freshConfigLaw pools).E (fun s => D.sigma v s x * D.sigma v s z *
          ∏ a ∈ D.externalEarly v,
            (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) ∧
              Hits (T.S.E k) PT.tiling.c z (D.earlyLabel s (flipPos v a)) then 1 else 0) /
              (rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) *
               rowDeg (T.S.E k) PT.tiling.c z (PT.π (D.geom.patchOf (flipPos v a))))) else 0)
  else 0

def IsolateKernelFacts (D : LateData hPT) (K : ℝ) : Prop :=
  ∀ v, IsEvenRole v → ∀ x z, 0 ≤ isolatedWeight D v x z ∧ isolatedWeight D v x z = isolatedWeight D v z x ∧
    (∑ y, isolatedWeight D v x y) ≤ K / D.paletteScale (D.rolePalette v) ∧
    isolatedWeight D v x z ≤ (D.paletteScale (D.rolePalette v))⁻¹ ^ 2 * Real.exp (0.01 * (T.S.n k : ℝ))

/-- Kept early pair-hit queries, indexed by actual even/odd roles. One outer
word is retained per observed slice. Slice/group separation is required. -/
structure PairQueries (D : LateData hPT) (A : InitialPairData D) where
  count : ℕ
  row : Fin count → Pos T k
  coordinate : Fin count → Fin (T.S.n k)
  row_mem : ∀ q, row q ∈ D.nonisolates A.rows
  early : ∀ q, coordinate q ∈ D.externalEarly (row q)
  bulk : ∀ q, coordinate q ∈ PT.tiling.bulkCoords (D.geom.patchOf (row q))
  count_bound : count ≤ (D.nonisolates A.rows).card * T.S.n k
  distinct_roles : Function.Injective (fun q => flipPos (row q) (coordinate q))
  /-- The word margin also separates primitive centres, each one flip away,
  before consulting radius-10ρh groups (18:1116–1123). -/
  separated : ∀ q q', q ≠ q' →
    D.geom.cellOf (flipPos (row q) (coordinate q)) = D.geom.cellOf (flipPos (row q') (coordinate q')) →
    hammingDist (flipPos (row q) (coordinate q)) (flipPos (row q') (coordinate q')) >
      50 * κ.ρ * (PT.tiling.P A.paletteIndex.1).h

namespace PairQueries
variable {D : LateData hPT} {A : InitialPairData D} (Q : PairQueries D A)
noncomputable def integral (assignment : PairAssignment T k) : ℝ :=
  D.encoding.iidLaw.E (fun pools =>
    if ∀ q, D.fresh.typical (D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q)))
      (pools (D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q)))) then
      (D.freshConfigLaw pools).E (fun s => ∏ q,
        if Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).1 (D.earlyLabel s (flipPos (Q.row q) (Q.coordinate q))) ∧
           Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).2 (D.earlyLabel s (flipPos (Q.row q) (Q.coordinate q)))
        then (1 : ℝ) else 0) else 0)
end PairQueries

/-- Label/bin comparisons, reverse repeat summation, and iid containment
are exposed as an actual integral bound, with k=0 giving one. -/
def PairQueryBound (D : LateData hPT) (A : InitialPairData D) (Q : PairQueries D A) : Prop :=
  ∀ assignment, (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
    Q.integral assignment ≤ (4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.005 * Q.count)

/-- Deterministic symmetric kernels for *every* small tuple, before endpoint
values. All three constants are supplied uniformly before the stage index. -/
structure EndpointCertificate (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (K Cprime Cstage : ℝ) : Prop where
  pair_facts : PairInitialFacts D δ K
  joint : ∀ A : InitialPairData D,
    ∃ kernel : Pos T k → Fin (T.S.N k) → Fin (T.S.N k) → ℝ,
      (∀ v ∈ A.rows, ∀ x z, 0 ≤ kernel v x z) ∧
      (∀ v ∈ A.rows, ∀ x z, kernel v x z = kernel v z x) ∧
      (∀ v ∈ A.rows, ∀ x, ∑ z, kernel v x z ≤ K / D.paletteScale A.paletteIndex) ∧
      (∀ v ∈ A.rows, ∀ x z, kernel v x z ≤ (D.paletteScale A.paletteIndex)⁻¹ ^ 2 *
        Real.exp (0.01 * (T.S.n k : ℝ))) ∧
      (∀ assignment, endpointProbability D C H A assignment ≤
        Real.exp (Cstage * D.geom.r) * K ^ A.rows.card *
          Real.exp (0.01 * (T.S.n k : ℝ) * (D.nonisolates A.rows).card +
            Cprime * A.rows.card * D.rank A.rows) *
          ∏ v ∈ A.rows, kernel v (assignment v).1 (assignment v).2)

/-- Connected sets and Hall violations in the actual drawn endpoint multigraph. -/
noncomputable def endpointGraph (S : Finset (Pos T k)) (a : PairAssignment T k) :
    SimpleGraph {v // v ∈ S} where
  Adj v w := v ≠ w ∧ ((a v).1 = (a w).1 ∨ (a v).1 = (a w).2 ∨
    (a v).2 = (a w).1 ∨ (a v).2 = (a w).2)
  symm := by
    constructor
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))
  loopless := by constructor; intro v h; exact h.1 rfl
noncomputable def endpointVertices (S : Finset (Pos T k)) (a : PairAssignment T k) :=
  S.biUnion fun v => {(a v).1, (a v).2}
noncomputable def HallObstruction (D : LateData hPT) (t₀ : ℕ) (a : PairAssignment T k) : Prop :=
  ∃ p : PaletteIndex D, ∃ S : Finset (Pos T k), S ⊆ D.paletteRows p ∧
    (endpointGraph S a).Connected ∧
    (S.card = t₀ ∨ (3 ≤ S.card ∧ S.card < t₀ ∧ (endpointVertices S a).card < S.card))

/-- Palette matchings on a positive-probability full run. This does not
contain a preassembled cube; the final assembly supplies edges and odd labels. -/
structure HallCertificate (D : LateData hPT) (δ : ℝ) where
  input : D.encoding.InitInput
  history : D.encoding.base.History (Fin.last D.geom.r)
  pairs : PairAssignment T k
  full : D.full δ input history
  pair_supported : ∀ v, IsEvenRole v → 0 < (D.pairLaw history v).w (pairs v)
  matching : {v : Pos T k // IsEvenRole v} → Fin (T.S.N k)
  chosen : ∀ v, matching v = (pairs v.1).1 ∨ matching v = (pairs v.1).2
  palette_injective : ∀ v w, D.rolePalette v.1 = D.rolePalette w.1 → matching v = matching w → v = w

end HypercubeRamsey.S18
