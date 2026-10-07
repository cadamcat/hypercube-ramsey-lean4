import HypercubeRamsey.PartC.All
import HypercubeRamsey.Framework.Embedding

/-!
Finite objects for the high modes in Section 15.  The direct assignment uses the odd-role product
law from the profiled tiling.  Cluster sampling is represented by its entering history, bin, and
label stages; the later propositions state the stage-specific comparison contracts.
-/

namespace HypercubeRamsey.S15

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

/-- A position of the cube at one stage index. -/
abbrev Position (T : Stage) (k : ℕ) := CubeVertex (T.S.n k)

/-- Even and odd positions of the target cube. -/
abbrev EvenPosition (T : Stage) (k : ℕ) :=
  {v : Position T k // HypercubeRamsey.IsEvenRole v}
abbrev OddPosition (T : Stage) (k : ℕ) :=
  {v : Position T k // ¬ HypercubeRamsey.IsEvenRole v}

/-- An assignment of second-side labels to the odd roles of the target cube. -/
abbrev OddAssignment (T : Stage) (k : ℕ) := OddPosition T k → Fin (T.S.N k)

noncomputable instance oddAssignmentFintype (T : Stage) (k : ℕ) :
    Fintype (OddAssignment T k) := by
  classical
  exact Pi.instFintype

noncomputable instance evenPositionFintype (T : Stage) (k : ℕ) : Fintype (EvenPosition T k) :=
  Fintype.subtype (Finset.univ.filter fun v : Position T k => HypercubeRamsey.IsEvenRole v)
    (by intro v; simp)

noncomputable instance oddPositionFintype (T : Stage) (k : ℕ) : Fintype (OddPosition T k) :=
  Fintype.subtype (Finset.univ.filter fun v : Position T k => ¬ HypercubeRamsey.IsEvenRole v)
    (by intro v; simp)

/-- Cube adjacency, viewed from an even role to an odd role. -/
def Adjacent {T : Stage} {k : ℕ} (a : EvenPosition T k) (b : OddPosition T k) : Prop :=
  (cube (T.S.n k)).Adj a.1 b.1

private theorem even_iff_not_even_succ (m : ℕ) : Even m ↔ ¬ Even (m + 1) := by
  constructor
  · intro hm hsucc
    exact (Nat.not_even_iff_odd.mpr hm.add_one) hsucc
  · intro hsucc
    rcases Nat.even_or_odd m with hm | hm
    · exact hm
    · exact (hsucc hm.add_one).elim

private theorem even_succ_iff_not_even (m : ℕ) : Even (m + 1) ↔ ¬ Even m :=
  Nat.even_add_one

/-- Flipping one coordinate reverses the parity class of a cube position. -/
theorem evenRole_flipPos {n : ℕ} (v : CubeVertex n) (j : Fin n) :
    HypercubeRamsey.IsEvenRole (flipPos v j) ↔ ¬ HypercubeRamsey.IsEvenRole v := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter fun i => v i = true
  let B : Finset (Fin n) := Finset.univ.filter fun i => flipPos v j i = true
  change Even B.card ↔ ¬ Even A.card
  cases hv : v j with
  | true =>
    have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    have hBA : B = A.erase j := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [A, B, flipPos, hv]
      · simp [A, B, flipPos, hij, Ne.symm hij, hv]
    have hcard := Finset.card_erase_of_mem hjA
    rw [hBA, hcard]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨j, hjA⟩
    have hEq : A.card = (A.card - 1) + 1 := by omega
    rw [hEq]
    exact even_iff_not_even_succ (A.card - 1)
  | false =>
    have hjA : j ∉ A := by simp [A, hv]
    have hBA : B = insert j A := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [A, B, flipPos, hv]
      · simp [A, B, flipPos, hij, Ne.symm hij, hv]
    rw [hBA, Finset.card_insert_of_notMem hjA]
    exact even_succ_iff_not_even A.card

theorem highMode_isCluster {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    PT.tiling.mode.isCluster := by
  rcases hm with h | h <;> simp [HypercubeRamsey.Mode.isCluster, h]

/-- The unique patch whose prefix leaf contains a cube position. -/
noncomputable def patchAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v : Position T k) : Fin PT.tiling.m :=
  Classical.choose (hPT.tiling_valid.prefix_complete v)

/-- The slice solver fixed by the valid high profiled tiling at patch `i`. -/
noncomputable def clusterSolver {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) : SliceSolver κ PT.tiling i PT.mesh :=
  Classical.choose (hPT.cluster_solver (highMode_isCluster PT hm) i)

/-- A slice is a patch together with the fixed word outside its internal coordinates. -/
abbrev ClusterSlice {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) :=
  Σ i : Fin PT.tiling.m, {o : CubeVertex (T.S.n k - (PT.tiling.P i).h) //
    ∀ j : Fin (T.S.n k - (PT.tiling.P i).h), j.val < (PT.tiling.P i).ℓ →
      o j = PT.tiling.w i ⟨j.val, by have := j.isLt; omega⟩}

noncomputable instance clusterSliceDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : DecidableEq (ClusterSlice PT) := Classical.decEq _

noncomputable instance clusterSliceFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Fintype (ClusterSlice PT) := by
  classical
  infer_instance

/-- The internal dimension of a high-cluster patch is positive. -/
theorem clusterHeight_pos {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) : 0 < (PT.tiling.P i).h := by
  have hcluster : PT.tiling.mode = .lowCluster ∨
      PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge := by
    rcases hm with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hPT.tiling_valid.cluster_data hcluster i with
    ⟨_, _, _, _, _, _, hpow, _, _, _, _, _⟩
  rw [hpow]
  exact Nat.pow_pos (by decide)

/-- Each patch's internal coordinates fit in the target cube dimension. -/
theorem clusterHeight_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (PT.tiling.P i).h ≤ T.S.n k := by
  have hlen := hPT.tiling_valid.prefix_internal_length
  have hh : (PT.tiling.P i).h ≤ Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
  omega

/-- Coordinates outside a patch's internal block index its slices. -/
def outsideWord {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v : Position T k) : CubeVertex (T.S.n k - (PT.tiling.P i).h) :=
  fun j => v ⟨j.val, by have := j.isLt; have hn := Nat.sub_le (T.S.n k) (PT.tiling.P i).h; omega⟩

/-- The internal-coordinate word of a full cube position in patch `i`. -/
def internalWord {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v : Position T k) : IWord PT.tiling i :=
  fun j => v ⟨T.S.n k - (PT.tiling.P i).h + j.val, by
    have hh := clusterHeight_le PT hPT i
    have hj := j.isLt
    omega⟩

/-- The patch-slice containing a full cube position. -/
noncomputable def clusterSliceAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v : Position T k) : ClusterSlice PT := by
  refine ⟨patchAt PT hPT v, outsideWord PT hPT (patchAt PT hPT v) v, ?_⟩
  intro j hj
  exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete v)).1
    ⟨j.val, by have := j.isLt; omega⟩ hj

/-- The internal word of a full cube position. -/
noncomputable def clusterWordAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v : Position T k) :
    IWord PT.tiling (patchAt PT hPT v) :=
  internalWord PT hPT (patchAt PT hPT v) v

/-- Solver coordinates. Equality of internal and full parity means the outer word is even;
otherwise translate the whole slice by `e₀`. This parity test avoids a dependent word split. -/
noncomputable def solverWordAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (v : Position T k) :
    IWord PT.tiling (patchAt PT hPT v) :=
  let z := clusterWordAt PT hPT v
  if HypercubeRamsey.IsEvenRole z ↔ HypercubeRamsey.IsEvenRole v then z
  else flipPos z ⟨0, clusterHeight_pos PT hPT hm (patchAt PT hPT v)⟩

/-- A group in one high-cluster slice. -/
abbrev ClusterGroupIndex {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) :=
  Σ s : ClusterSlice PT, Group PT.tiling s.1

noncomputable instance clusterGroupIndexDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : DecidableEq (ClusterGroupIndex PT) := Classical.decEq _

noncomputable instance clusterGroupIndexFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Fintype (ClusterGroupIndex PT) := by
  classical
  infer_instance

/-- The physical-bin type attached to a slice group. -/
def clusterBinType {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (g : ClusterGroupIndex PT) :=
  Bin PT.tiling g.1.1

noncomputable instance clusterBinTypeFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (g : ClusterGroupIndex PT) : Fintype (clusterBinType g) := by
  change Fintype (Bin PT.tiling g.1.1)
  exact HypercubeRamsey.instBinFintype PT.tiling g.1.1

/-- A bin choice for every group in every high-cluster slice. -/
abbrev ClusterBinAssignment {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) := ∀ g : ClusterGroupIndex PT, clusterBinType g

noncomputable instance clusterBinAssignmentFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Fintype (ClusterBinAssignment PT) := by
  classical
  exact Pi.instFintype

/-- The slice group that supplies an odd position's label law. -/
noncomputable def clusterGroupIndexAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) : ClusterGroupIndex PT := by
  let s := clusterSliceAt PT hPT b.1
  exact ⟨s, (clusterSolver PT hPT hm s.1).groupOf (solverWordAt PT hPT hm b.1)⟩

/-- Translate the internal center to the even-role convention of its slice solver. -/
noncomputable def clusterCenterRole {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (v : EvenPosition T k) : EvenRole PT.tiling (patchAt PT hPT v.1) := by
  classical
  let z := clusterWordAt PT hPT v.1
  refine ⟨solverWordAt PT hPT hm v.1, ?_⟩
  by_cases hz : HypercubeRamsey.IsEvenRole z
  · simpa [solverWordAt, z, hz, v.2] using hz
  · simpa [solverWordAt, z, hz, v.2] using
      (evenRole_flipPos z ⟨0, clusterHeight_pos PT hPT hm (patchAt PT hPT v.1)⟩).2 hz

/-- One primitive record in one high-cluster slice. -/
abbrev ClusterRecordIndex {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :=
  Σ s : ClusterSlice PT, (clusterSolver PT hPT hm s.1).Rec

noncomputable instance clusterRecordIndexDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    DecidableEq (ClusterRecordIndex PT hPT hm) := Classical.decEq _

noncomputable instance clusterRecordIndexFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    Fintype (ClusterRecordIndex PT hPT hm) := by
  classical
  infer_instance

/-- The value type of a primitive high-cluster record. -/
def ClusterRecordValue {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (r : ClusterRecordIndex PT hPT hm) : Type :=
  (clusterSolver PT hPT hm r.1.1).Val r.2

noncomputable instance clusterRecordValueFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (r : ClusterRecordIndex PT hPT hm) : Fintype (ClusterRecordValue r) :=
  (clusterSolver PT hPT hm r.1.1).valFin r.2

/-- All primitive records, independently sampled across patches and slices. -/
abbrev ClusterHistory {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :=
  ∀ r : ClusterRecordIndex PT hPT hm, ClusterRecordValue r

noncomputable instance clusterHistoryFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    Fintype (ClusterHistory PT hPT hm) := by
  classical
  exact Pi.instFintype

/-- The records of one patch-slice, projected from the global history. -/
def historyOnSlice {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (s : ClusterSlice PT) :
    ∀ r, (clusterSolver PT hPT hm s.1).Val r :=
  fun r => W ⟨s, r⟩

/-- The product law of the raw primitive slice histories. -/
noncomputable def clusterHistoryLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    FinLaw (ClusterHistory PT hPT hm) := by
  classical
  exact FinLaw.pi fun (r : ClusterRecordIndex PT hPT hm) =>
    ⟨(clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_nonneg PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_sum PT.parameter r.2⟩

/-- The per-slice bin and label reference outcome from D14.S. -/
abbrev ClusterSliceOutcome {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) :=
  (Group PT.tiling i → Bin PT.tiling i) ×
    (IWord PT.tiling i → Fin (T.S.N k))

/-- Product reference outcomes for every high-cluster slice. -/
abbrev ClusterInternalData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) :=
  ∀ s : ClusterSlice PT, ClusterSliceOutcome PT s.1

noncomputable instance clusterInternalDataFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Fintype (ClusterInternalData PT) := by
  classical
  exact Pi.instFintype

/-- Given the primitive records, sample the internal reference experiment independently by slice. -/
noncomputable def clusterInternalKernel {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : FinLaw (ClusterInternalData PT) := by
  classical
  exact FinLaw.pi fun (s : ClusterSlice PT) =>
    (clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s)

/-- The conditional odd-label marginal attached to a full odd position's slice group. -/
noncomputable def clusterMarginal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) (y : Fin (T.S.N k)) : ℝ := by
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  exact S.oddMarginal (S.groupOf (solverWordAt PT hPT hm b.1)) (historyOnSlice W s) y

/-- Conditional first-side degree of an odd position in the high-cluster history. -/
noncomputable def clusterDegree {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  deg (T.S.E k) PT.tiling.c (clusterMarginal PT hPT hm W b) x

/-- The bulk odd neighbours of a cluster row, outside its internal slice. -/
noncomputable def clusterBulkNeighbours {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) : Finset (OddPosition T k) :=
  Finset.univ.filter fun b => Adjacent a b ∧
    patchAt PT hPT b.1 = patchAt PT hPT a.1 ∧
      clusterSliceAt PT hPT b.1 ≠ clusterSliceAt PT hPT a.1

/-- The crossing odd neighbours of a cluster row, in other patches. -/
noncomputable def clusterCrossingNeighbours {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) : Finset (OddPosition T k) :=
  Finset.univ.filter fun b => Adjacent a b ∧
    patchAt PT hPT b.1 ≠ patchAt PT hPT a.1

/-- `J_v^0`: bulk degree gates and the product-of-degrees test. -/
def clusterJ0 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (x : Fin (T.S.N k)) : Prop :=
  x ∈ (PT.tiling.P (patchAt PT hPT a.1)).X ∧
  (∀ b ∈ clusterBulkNeighbours PT hPT a,
    |clusterDegree PT hPT hm W b x - 1 / 2| ≤ 2 * bstar T k) ∧
  let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w x
  0 < d ∧
    (1 / 2 : ℝ) ≤
      (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) /
        d ^ (clusterBulkNeighbours PT hPT a).card ∧
    (∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b x) /
      d ^ (clusterBulkNeighbours PT hPT a).card ≤ 2

/-- `J_v`: `J_v^0` together with crossing degree gates. -/
def clusterJ {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (x : Fin (T.S.N k)) : Prop :=
  clusterJ0 PT hPT hm W a x ∧
    ∀ b ∈ clusterCrossingNeighbours PT hPT a,
      |clusterDegree PT hPT hm W b x - 1 / 2| ≤ 2 * bstar T k

/-- The internal profile row `σ_v`, read from the records and internal odd labels. -/
noncomputable def clusterSigma {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  exact S.σ v (historyOnSlice W s) (nbrLabels v.1 (I s).2) x

/-- One conditional hit ratio for a high-cluster bulk or crossing label. -/
noncomputable def clusterFactor {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (b : OddPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  let d := clusterDegree PT hPT hm W b x
  if 0 < d then hit (T.S.E k) PT.tiling.c x ((I (clusterSliceAt PT hPT b.1)).2 (solverWordAt PT hPT hm b.1)) / d
  else 0

/-- Crossing-filter mass for a cluster row before its bulk factors are exposed. -/
noncomputable def clusterCrossingMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) : ℝ :=
  ∑ x, clusterSigma PT hPT hm W I a x *
    ∏ b ∈ clusterCrossingNeighbours PT hPT a, clusterFactor PT hPT hm W I a b x

/-- Equation (15.18): the high-cluster unnormalized even row. -/
noncomputable def clusterRowWeight {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  clusterSigma PT hPT hm W I a x * (if clusterJ PT hPT hm W a x then 1 else 0) *
    ∏ b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a,
      clusterFactor PT hPT hm W I a b x

/-- Total mass in the conditional high-cluster row. -/
noncomputable def clusterRowMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) (a : EvenPosition T k) : ℝ :=
  ∑ x, clusterRowWeight PT hPT hm W I a x

/-- The first local alarm: too much uniform mass is removed by `J_v^0`. -/
noncomputable def clusterAlarm1 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : Prop :=
  (∑ x, if clusterJ0 PT hPT hm W a x then 0 else
    (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
      (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x) >
        Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2)

/-- The third local alarm: the D14 slice solver's local test fails. -/
def clusterAlarm3 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : Prop :=
  ¬ (clusterSolver PT hPT hm (patchAt PT hPT a.1)).Hgood
    (clusterCenterRole PT hPT hm a)
    (historyOnSlice W (clusterSliceAt PT hPT a.1))

/-- The global odd-label history-load success event `𝓗`. -/
def clusterHistoryLoad {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : Prop :=
  ∀ y, ∑ s : ClusterSlice PT,
    ∑ g : Group PT.tiling s.1,
      (PT.tiling.P s.1).h *
        (clusterSolver PT hPT hm s.1).oddMarginal g (historyOnSlice W s) y < κ.θstar

/-- A nominal hit ratio using the profiled law of the even row's own patch. -/
noncomputable def clusterNominalRatio {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (x y : Fin (T.S.N k)) : ℝ :=
  let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w x
  if 0 < d then hit (T.S.E k) PT.tiling.c x y / d else 0

/-- The centered interaction of a bulk group's history law with a tuple of first labels. -/
noncomputable def clusterInteraction {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k)
    (J : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
  ∑ y, clusterMarginal PT hPT hm W b y *
    ∏ j ∈ J,
      (let d := clusterDegree PT hPT hm W b (xs j)
       if 0 < d then hit (T.S.E k) PT.tiling.c (xs j) y / d - 1 else -1)

/-- The positive comparison envelope in the large-interaction alarm. -/
noncomputable def clusterInteractionEnvelope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
  ∑ J : Finset (Fin κ.u),
    ∏ b ∈ clusterBulkNeighbours PT hPT a,
      ∑ y, clusterMarginal PT hPT hm W b y *
        ∏ j ∈ J, clusterNominalRatio PT hPT a (xs j) y

/-- The raw large-interaction statistic `T_v(W)` from §15. -/
noncomputable def clusterInteractionCost {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : ℝ := by
  classical
  exact (clusterInternalKernel PT hPT hm W).E fun I =>
    ∑ xs : Fin κ.u → Fin (T.S.N k),
      (∏ j, clusterSigma PT hPT hm W I a (xs j)) *
        (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
            ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
              2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| then
          clusterInteractionEnvelope PT hPT hm W a xs else 0)

/-- The second local alarm: the large-interaction statistic exceeds its permitted budget. -/
def clusterAlarm2 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : Prop :=
  clusterInteractionCost PT hPT hm W a >
    Real.exp (-100 * PT.tiling.gain (patchAt PT hPT a.1))

/-- The three D15.A history alarms are all avoided. -/
def clusterAlarmsAvoided {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : Prop :=
  ∀ a, ¬ clusterAlarm1 PT hPT hm W a ∧
    ¬ clusterAlarm2 PT hPT hm W a ∧ ¬ clusterAlarm3 PT hPT hm W a

/-- The cluster-mode part of L15.1a's reusable crossing-filter estimate. -/
def ClusterCrossingClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in Filter.atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    ∀ W, clusterAlarmsAvoided PT hPT hm W → ∀ a : EvenPosition T k,
      (clusterInternalKernel PT hPT hm W).pr (fun I =>
        (∑ x, clusterSigma PT hPT hm W I a x) = 1 ∧
          |clusterCrossingMass PT hPT hm W I a - 1| >
            Real.exp (20 * (PT.tiling.P (patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- The raw history law conditioned to avoid the D15.A alarms. -/
noncomputable def clusterAvoidedHistoryLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hpositive : 0 < (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm)) :
    FinLaw (ClusterHistory PT hPT hm) := by
  classical
  let A := Finset.univ.filter (fun W : ClusterHistory PT hPT hm => clusterAlarmsAvoided PT hPT hm W)
  have hA : 0 < ∑ W ∈ A, (clusterHistoryLaw PT hPT hm).w W := by
    have heq : (∑ W ∈ A, (clusterHistoryLaw PT hPT hm).w W) =
        (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm) := by
      unfold FinLaw.pr
      rw [← Finset.sum_filter]
    rw [heq]
    exact hpositive
  exact (clusterHistoryLaw PT hPT hm).cond A hA

/-- A real-valued bin function depends only on the queried slice groups in `S`. -/
def ClusterBinDependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (F : ClusterBinAssignment PT → ℝ)
    (S : Finset (ClusterGroupIndex PT)) : Prop :=
  ∀ B B', (∀ g ∈ S, B g = B' g) → F B = F B'

/-- Raw histories followed by the independent per-slice D14 reference experiments. -/
noncomputable def clusterRawReferenceLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    FinLaw (ClusterHistory PT hPT hm × ClusterInternalData PT) :=
  FinLaw.bind (clusterHistoryLaw PT hPT hm) (clusterInternalKernel PT hPT hm)

/-- The label at a full cube position read from its internal slice experiment. -/
noncomputable def clusterLabelFromInternal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (I : ClusterInternalData PT) (b : OddPosition T k) : Fin (T.S.N k) :=
  (I (clusterSliceAt PT hPT b.1)).2 (solverWordAt PT hPT hm b.1)

/-- The odd-label marginal of the raw history and product-by-groups reference experiment. -/
noncomputable def clusterRawOddLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    FinLaw (OddAssignment T k) := by
  classical
  exact FinLaw.map (clusterRawReferenceLaw PT hPT hm)
    (fun z => fun b => clusterLabelFromInternal (hPT := hPT) hm z.2 b)

/-- The patch label law attached to an odd cube position. -/
noncomputable def lawAtOdd {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (b : OddPosition T k) : Law (T.S.N k) :=
  PT.π (patchAt PT hPT b.1)

/-- Convert the shared host-side law to the equivalent Part C finite-law interface. -/
def lawToFinLaw {N : ℕ} (P : Law N) : FinLaw (Fin N) where
  w := P.w
  nonneg := P.nonneg
  sum_one := P.sum_eq_one

/-- The raw product law of independent odd labels, with each coordinate sampled from its profile. -/
noncomputable def directRawLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) : FinLaw (OddAssignment T k) := by
  classical
  exact FinLaw.pi fun b => lawToFinLaw (lawAtOdd PT hPT b)

/-- A normalized hit factor, set to zero when its denominator vanishes. -/
noncomputable def normalizedHit {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x y : Fin N) : ℝ :=
  let d := deg E c π.w x
  if 0 < d then hit E c x y / d else 0

/-- The direct-mode first-row law, uniform on the cleaned envelope of its patch. -/
noncomputable def directBaseWeight {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  let C := PT.envelope (patchAt PT hPT a.1)
  if x ∈ C then (C.card : ℝ)⁻¹ else 0

/-- Odd neighbours in other patches (the crossing positions of a direct star). -/
noncomputable def crossingNeighbours {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) : Finset (OddPosition T k) :=
  Finset.univ.filter fun b => Adjacent a b ∧
    patchAt PT hPT b.1 ≠ patchAt PT hPT a.1

/-- Odd neighbours in the same patch (the bulk positions of a direct star). -/
noncomputable def bulkNeighbours {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) : Finset (OddPosition T k) :=
  Finset.univ.filter fun b => Adjacent a b ∧
    patchAt PT hPT b.1 = patchAt PT hPT a.1

/-- The patch-normalized likelihood factor for one odd label. -/
noncomputable def directFactor {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (ys : OddAssignment T k) (b : OddPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  normalizedHit (T.S.E k) PT.tiling.c (lawAtOdd PT hPT b) x (ys b)

/-- The direct crossing-filter mass before the bulk labels are exposed. -/
noncomputable def directCrossingMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) : ℝ :=
  ∑ x, directBaseWeight PT hPT a x *
    ∏ b ∈ crossingNeighbours PT hPT a, directFactor PT hPT a ys b x

/-- The normalized post-crossing first law, defined as zero after a zero-mass filter. -/
noncomputable def directPostCrossingWeight {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  let m := directCrossingMass PT hPT ys a
  if 0 < m then
    (directBaseWeight PT hPT a x *
      ∏ b ∈ crossingNeighbours PT hPT a, directFactor PT hPT a ys b x) / m
  else 0

/-- The post-crossing bulk mass for one even row. -/
noncomputable def directBulkMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) : ℝ :=
  ∑ x, directPostCrossingWeight PT hPT ys a x *
    ∏ b ∈ bulkNeighbours PT hPT a, directFactor PT hPT a ys b x

/-- The full unnormalized direct-mode row (`eq:source-17` with `h = 0`). -/
noncomputable def directRowWeight {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  directCrossingMass PT hPT ys a * directPostCrossingWeight PT hPT ys a x *
    ∏ b ∈ bulkNeighbours PT hPT a,
      directFactor PT hPT a ys b x

/-- Total mass of an unnormalized direct row. -/
noncomputable def directRowMass {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) : ℝ :=
  directCrossingMass PT hPT ys a * directBulkMass PT hPT ys a

/-- Normalize a direct row on its positive-mass event. -/
noncomputable def directNormalizedRow {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (ys : OddAssignment T k)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  let m := directRowMass PT hPT ys a
  if 0 < m then directRowWeight PT hPT ys a x / m else 0

/-- A fractional Hall system on the parity classes of the target cube. -/
structure DirectHallRows {T : Stage} {k : ℕ} (c : Colour) where
  oddLabel : OddPosition T k → Fin (T.S.N k)
  odd_injective : Function.Injective oddLabel
  odd_in_Y : ∀ b, oddLabel b ∈ T.Y k
  row : EvenPosition T k → Fin (T.S.N k) → ℝ
  row_nonneg : ∀ a x, 0 ≤ row a x
  row_sum : ∀ a, ∑ x, row a x = 1
  row_supported : ∀ a x, row a x ≠ 0 → x ∈ T.X k
  common_neighbour : ∀ a x, row a x ≠ 0 → ∀ b, Adjacent a b →
    Hits (T.S.E k) c x (oddLabel b)
  column_load : ∀ x, ∑ a, row a x ≤ 1

/-- C15.R: Hall's theorem and the cube embedding interface turn fractional rows into a cube. -/
theorem rows_to_cube {T : Stage} {k : ℕ} (c : Colour) (H : DirectHallRows (T := T) (k := k) c) :
    CubeIn T k c ∧ (∀ b, H.oddLabel b ∈ T.Y k) ∧
      (∀ a x, H.row a x ≠ 0 → x ∈ T.X k) := by
  classical
  let L : EvenPosition T k → Finset (Fin (T.S.N k)) := fun a =>
    Finset.univ.filter fun x => H.row a x ≠ 0
  obtain ⟨f, hf, hmem⟩ := exists_injective_of_fractional H.row L
    H.row_nonneg H.row_sum
    (by
      intro a x hx
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩))
    H.column_load
  have hedge : ∀ a b, Adjacent a b → Hits (T.S.E k) c (f a) (H.oddLabel b) := by
    intro a b hab
    have hrow : H.row a (f a) ≠ 0 := (Finset.mem_filter.mp (hmem a)).2
    exact H.common_neighbour a (f a) hrow b hab
  refine ⟨cube_copy_of_parts f H.oddLabel hf H.odd_injective hedge, H.odd_in_Y, ?_⟩
  exact H.row_supported

/-- Even positions belonging to patch `i`. -/
noncomputable def evenPatchPositions {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Finset (EvenPosition T k) := by
  classical
  exact Finset.univ.filter fun a => a.1 ∈ 𝒯.leaf i

/-- The normalized column statistic used in the direct and cluster moment estimates. -/
noncomputable def patchColumnAverage {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (rows : (OddAssignment T k) → EvenPosition T k → Fin (T.S.N k) → ℝ)
    (ys : OddAssignment T k) (x : Fin (T.S.N k)) : ℝ :=
  let Eᵢ := evenPatchPositions PT.tiling i
  (Eᵢ.card : ℝ)⁻¹ *
    ∑ a ∈ Eᵢ, (PT.tiling.P i).M * rows ys a x

/-- Clock-conditioned odd assignment together with the mass gates from L15.1d. -/
structure DirectSampler {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) where
  rawLaw : FinLaw (OddAssignment T k)
  rawLaw_eq : rawLaw = directRawLaw PT hPT
  law : FinLaw (OddAssignment T k)
  local_upper_comparison : ∀ F : OddAssignment T k → ℝ,
    (∀ ys, 0 ≤ F ys) → ∀ S : Finset (OddPosition T k),
      (∀ ys ys', (∀ b ∈ S, ys b = ys' b) → F ys = F ys') →
      (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 → law.E F ≤ 2 * rawLaw.E F
  label_supported : ∀ ys, law.w ys ≠ 0 → ∀ b,
    ys b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y
  injective_on_support : ∀ ys, law.w ys ≠ 0 → Function.Injective ys
  row_mass_gate : ∀ ys, law.w ys ≠ 0 → ∀ a, (1 / 2 : ℝ) ≤ directRowMass PT hPT ys a

/-- The independent bin kernel at a fixed primitive history. -/
noncomputable def clusterIndependentBinKernel {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : FinLaw (ClusterBinAssignment PT) := by
  classical
  exact FinLaw.pi fun (g : ClusterGroupIndex PT) =>
    let Sg : SliceSolver κ PT.tiling g.1.1 PT.mesh := clusterSolver PT hPT hm g.1.1
    let Wg := historyOnSlice W g.1
    (⟨Sg.q g.2 Wg, Sg.q_nonneg g.2 Wg, Sg.q_sum g.2 Wg⟩ : FinLaw (clusterBinType g))

/-- Project all slice reference outcomes to their group-bin assignment. -/
def clusterBinsOfInternal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (I : ClusterInternalData PT) : ClusterBinAssignment PT :=
  fun g => (I g.1).1 g.2

/-- Bin-column load from the per-group in-bin laws. -/
noncomputable def clusterGivenBinColumn {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (y : Fin (T.S.N k)) : ℝ :=
  ∑ g : ClusterGroupIndex PT,
    (PT.tiling.P g.1.1).h *
      (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) (B g) y

/-- Probability of a star row failing its mass gate when labels are sampled independently by group,
conditional on all group bins. -/
noncomputable def clusterBinStarFailure {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) (a : EvenPosition T k) : ℝ := by
  classical
  let P := clusterInternalKernel PT hPT hm W
  let pB := P.pr (fun I => clusterBinsOfInternal I = B)
  let qB := P.pr (fun I => clusterBinsOfInternal I = B ∧
    clusterRowMass PT hPT hm W I a < 1 / 2)
  exact if 0 < pB then qB / pB else 0

/-- Consultation sites count local solver reads, independently of record multiplicity. -/
abbrev ClusterConsultation {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) := Σ s : ClusterSlice PT, IWord PT.tiling s.1

/-- All records within one of the queried `10ρh` consultation domains. -/
noncomputable def clusterConsultationScope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (U : Finset (ClusterConsultation PT)) : Finset (ClusterRecordIndex PT hPT hm) :=
  Finset.univ.filter fun r => ∃ c ∈ U, ∃ e : c.1 = r.1,
    (hammingDist ((clusterSolver PT hPT hm r.1.1).loc r.2) (e ▸ c.2) : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P r.1.1).h

/-- Dependence on specified primitive records. The budget counts consultation domains. -/
def ClusterHistoryDependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (F : ClusterHistory PT hPT hm → ℝ) (S : Finset (ClusterRecordIndex PT hPT hm)) : Prop :=
  ∀ W W', (∀ r ∈ S, W r = W' r) → F W = F W'

/-- Per-bin mass gates and capacity certificates from P15.3's bin stage. -/
noncomputable def clusterBinGood {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) : Prop :=
  (∀ a, clusterBinStarFailure PT hPT hm W B a ≤
    (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) ∧
  (∀ y, clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0) ∧
  (PT.tiling.mode = .highSmall → ∀ a b b', Adjacent a b → Adjacent a b' →
    clusterGroupIndexAt PT hPT hm b ≠ clusterGroupIndexAt PT hPT hm b' →
      (B (clusterGroupIndexAt PT hPT hm b)).1 ≠
        (B (clusterGroupIndexAt PT hPT hm b')).1)

/-- The conditional bin stage after history avoidance. -/
structure ClusterBinStage {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) where
  history_positive : 0 <
    (clusterHistoryLaw PT hPT hm).pr (clusterAlarmsAvoided PT hPT hm)
  historyLaw : FinLaw (ClusterHistory PT hPT hm)
  historyLaw_eq : historyLaw = clusterAvoidedHistoryLaw PT hPT hm history_positive
  binLaw : ClusterHistory PT hPT hm → FinLaw (ClusterBinAssignment PT)
  history_local_upper_comparison : ∀ F : ClusterHistory PT hPT hm → ℝ,
    (∀ W, 0 ≤ F W) → ∀ U : Finset (ClusterConsultation PT),
      ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U) →
      (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 →
        historyLaw.E F ≤ (1 + 1 / (T.S.n k : ℝ)) *
          (clusterHistoryLaw PT hPT hm).E F
  history_avoids_alarms : ∀ W, historyLaw.w W ≠ 0 → clusterAlarmsAvoided PT hPT hm W
  history_load_probability : (99 / 100 : ℝ) ≤
    historyLaw.pr (fun W => clusterHistoryLoad PT hPT hm W)
  bin_requirements : ∀ W, historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W → ∀ B,
    (binLaw W).w B ≠ 0 → clusterBinGood PT hPT hm W B
  local_upper_comparison : ∀ W, historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W →
    ∀ F : ClusterBinAssignment PT → ℝ,
    (∀ B, 0 ≤ F B) → ∀ S : Finset (ClusterGroupIndex PT),
      ClusterBinDependsOn F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 →
        (binLaw W).E F ≤ (1 + 1 / (T.S.n k : ℝ)) *
          (clusterIndependentBinKernel PT hPT hm W).E F

/-- Reference labels conditional on fixed group bins; every role is independent. -/
noncomputable def clusterIndependentLabelKernel {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) :
    FinLaw (ClusterInternalData PT) := by
  classical
  let P : FinLaw (∀ s : ClusterSlice PT, IWord PT.tiling s.1 → Fin (T.S.N k)) :=
    FinLaw.pi fun s => FinLaw.pi fun z =>
      let S := clusterSolver PT hPT hm s.1
      let g := S.groupOf z
      ⟨S.U g (historyOnSlice W s) (B ⟨s, g⟩),
        S.U_nonneg g (historyOnSlice W s) (B ⟨s, g⟩),
        S.U_sum g (historyOnSlice W s) (B ⟨s, g⟩)⟩
  exact FinLaw.map P (fun ys s => (fun g => B ⟨s, g⟩, ys s))

/-- Tests read only the transported labels of the queried physical odd roles. -/
def ClusterLabelDependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (F : ClusterInternalData PT → ℝ) (S : Finset (OddPosition T k)) : Prop :=
  ∀ I I', (∀ b ∈ S, clusterLabelFromInternal (hPT := hPT) hm I b =
    clusterLabelFromInternal (hPT := hPT) hm I' b) → F I = F I'

/-- Physical bin multiplicity of a queried role. -/
noncomputable def clusterBinQueryCount {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (S : Finset (OddPosition T k)) (b : OddPosition T k) : ℕ :=
  (S.filter fun b' => (B (clusterGroupIndexAt PT hPT hm b')).1 =
    (B (clusterGroupIndexAt PT hPT hm b)).1).card

/-- L3.9 applies only up to `d^.025` observations of each small physical bin. -/
def ClusterLabelQueryOK {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (S : Finset (OddPosition T k)) : Prop :=
  PT.tiling.mode = .highSmall → ∀ b ∈ S,
    (clusterBinQueryCount PT hPT hm B S b : ℝ) ≤
      ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (0.025 : ℝ)

/-- Exact singletons incur no L3.9 error; multi-observations use its `d^-.04` error. -/
noncomputable def clusterLabelError {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (S : Finset (OddPosition T k)) : ℝ :=
  if PT.tiling.mode = .highSmall then Real.exp (∑ b ∈ S,
    if 2 ≤ clusterBinQueryCount PT hPT hm B S b then
      ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) else 0) else 1

/-- A cluster sample records normalized conditional kernels without reweighting incoming histories. -/
structure ClusterSample {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) where
  Outcome : Type
  [outcomeFinite : Fintype Outcome]
  law : FinLaw Outcome
  binStage : ClusterBinStage PT hPT hm
  history : Outcome → ClusterHistory PT hPT hm
  internal : Outcome → ClusterInternalData PT
  bins : Outcome → ClusterBinAssignment PT
  label : Outcome → OddAssignment T k
  /-- Before mass-failure avoidance: calibrated per-bin injection, exact singleton marginals. -/
  preLabelKernel : ClusterHistory PT hPT hm → ClusterBinAssignment PT → FinLaw (ClusterInternalData PT)
  labelKernel : ClusterHistory PT hPT hm → ClusterBinAssignment PT → FinLaw (ClusterInternalData PT)
  label_disintegration : FinLaw.map law (fun ω => ((history ω, bins ω), internal ω)) =
    FinLaw.bind (FinLaw.bind binStage.historyLaw binStage.binLaw)
      (fun wb => labelKernel wb.1 wb.2)
  prelabel_singleton : ∀ W, binStage.historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W →
    ∀ B, (binStage.binLaw W).w B ≠ 0 → ∀ b y,
      (preLabelKernel W B).pr (fun I => clusterLabelFromInternal (hPT := hPT) hm I b = y) =
        (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U
          (clusterGroupIndexAt PT hPT hm b).2
          (historyOnSlice W (clusterSliceAt PT hPT b.1)) (B (clusterGroupIndexAt PT hPT hm b)) y
  prelabel_upper_comparison : ∀ W, binStage.historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W →
    ∀ B, (binStage.binLaw W).w B ≠ 0 → ∀ F : ClusterInternalData PT → ℝ,
    (∀ I, 0 ≤ F I) → ∀ S : Finset (OddPosition T k),
    ClusterLabelDependsOn hPT hm F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
    ClusterLabelQueryOK PT hPT hm B S →
      (preLabelKernel W B).E F ≤ clusterLabelError PT hPT hm B S *
        (clusterIndependentLabelKernel PT hPT hm W B).E F
  label_local_upper_comparison : ∀ W, binStage.historyLaw.w W ≠ 0 → clusterHistoryLoad PT hPT hm W →
    ∀ B, (binStage.binLaw W).w B ≠ 0 → ∀ F : ClusterInternalData PT → ℝ,
    (∀ I, 0 ≤ F I) → ∀ S : Finset (OddPosition T k),
    ClusterLabelDependsOn hPT hm F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
      (labelKernel W B).E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (preLabelKernel W B).E F
  row : Outcome → EvenPosition T k → Fin (T.S.N k) → ℝ
  historyLoad : Outcome → Prop
  history_eq : ∀ ω, historyLoad ω ↔ clusterHistoryLoad PT hPT hm (history ω)
  history_load_probability : 1 - (1 / 100 : ℝ) ≤ law.pr historyLoad
  bins_eq : ∀ ω g, bins ω g = (internal ω g.1).1 g.2
  bin_stage_marginal_eq : ∀ W B,
    law.pr (fun ω => history ω = W ∧ bins ω = B) =
      (FinLaw.bind binStage.historyLaw binStage.binLaw).pr (fun wb => wb = (W, B))
  label_eq : ∀ ω b, label ω b =
    (internal ω (clusterSliceAt PT hPT b.1)).2 (solverWordAt PT hPT hm b.1)
  label_supported : ∀ ω, law.w ω ≠ 0 → historyLoad ω → ∀ b,
    label ω b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y
  row_eq : ∀ ω a x, row ω a x =
    clusterRowWeight PT hPT hm (history ω) (internal ω) a x
  injective_on_support : ∀ ω, law.w ω ≠ 0 → historyLoad ω → Function.Injective (label ω)
  row_nonneg : ∀ ω a x, 0 ≤ row ω a x
  mass_gate : ∀ ω, law.w ω ≠ 0 → historyLoad ω → ∀ a, (1 / 2 : ℝ) ≤ ∑ x, row ω a x
  row_support : ∀ ω, law.w ω ≠ 0 → historyLoad ω → ∀ a x, row ω a x ≠ 0 →
    x ∈ PT.envelope (patchAt PT hPT a.1)
  common_neighbour : ∀ ω, law.w ω ≠ 0 → historyLoad ω → ∀ a x, row ω a x ≠ 0 →
    ∀ b, Adjacent a b → Hits (T.S.E k) PT.tiling.c x (label ω b)

attribute [instance] ClusterSample.outcomeFinite

end HypercubeRamsey.S15
