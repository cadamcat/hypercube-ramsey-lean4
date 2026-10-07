import HypercubeRamsey.PartC.Resampling

/-!
# Section 16 low-mode geometry and shared quantitative assumptions

The geometry certificates attach the combinatorial data from L16.1 to the
audited `LowGeom` interface. `LowModeQuantFacts` is the common quantitative
predicate used by later low-mode sections; it contains scale and conflict
bounds, but no syndrome, cell, pool, or sampler conclusion.
-/

namespace HypercubeRamsey.S16

open Classical
open scoped BigOperators

/-- L16.0: quantitative hypotheses shared with Sections 17 and 18. The fixed
exponent `1/2` is the precise reading of the paper's little-oh bounds.
`hκ` supplies the `c14_pos`, `h0_pos`, and `cChernoff_pos` contracts from
`CConsts.Admissible`; `ProfiledTiling.Valid` carries the Section 14 solver
contracts using `c14`. -/
structure LowModeQuantFacts {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} (K16 : ℝ) : Prop where
  profiled_valid : PT.Valid
  mode_low : PT.tiling.mode.isLow
  n_large : 2 ≤ T.S.n k
  K16_pos : 0 < K16
  height_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).h : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ)
  prefix_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ))
  patch_mass_bound : ∀ i : Fin PT.tiling.m,
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
      Real.sqrt (Real.log (T.S.n k : ℝ))
  bin_count_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))
  interaction_scale_bound : ∀ i : Fin PT.tiling.m,
    Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ κ.KB * Real.log (T.S.n k : ℝ)
  degree_bound : ∀ i : Fin PT.tiling.m, ∀ x ∈ PT.envelope i,
    (T.S.n k : ℝ) * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
      K16 * Real.log (T.S.n k : ℝ)
  conflict_bound : ∀ i : Fin PT.tiling.m, ∀ v ∈ PT.activeVertices,
    ∀ x : Fin (T.S.N k),
      (((PT.mesh.corner v i).filter fun z =>
        κ.ξ < |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|).card ≤
        K16 * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)))

/-- Numerical feasibility for L16.1. These are scale inequalities, not
syndrome/cell existence assumptions. The uniform cutoff node produces them. -/
structure LowModeScaleFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16) : Prop where
  n_four : 4 ≤ T.S.n k
  class_scale : 2 ≤ κ.A0 * Real.log (T.S.n k : ℝ)
  coset_room :
    4 * κ.A0 * Real.log (T.S.n k : ℝ) *
      max 1 ((Finset.univ.biUnion fun i : Fin PT.tiling.m =>
        PT.tiling.Icoord i).card : ℝ) ≤ T.S.n k
  slice_room : ∀ i : Fin PT.tiling.m,
    2 * (2 ^ (PT.tiling.P i).h : ℕ) ≤
      ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊
  coloring_room :
    1 + (∑ j ∈ Finset.range (⌈Real.rpow (Real.log (T.S.n k : ℝ)) 3⌉₊ + 1),
      (Nat.choose (T.S.n k) j : ℝ)) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  patch_capacity : ∀ i : Fin PT.tiling.m,
    (3 * Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
      Real.rpow (T.S.n k : ℝ) κ.Ac +
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)) *
      (⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
        (PT.tiling.P i).d⌉₊ : ℝ) ≤ Fintype.card (Bin PT.tiling i)
  cell_scope_bound : ∀ i : Fin PT.tiling.m,
    (⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊ : ℝ) ≤
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10)
  comparison_room : ∀ i : Fin PT.tiling.m,
    2 * (Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) + 1) ^ 2 ≤
      Fintype.card (Bin PT.tiling i)

/-- Fixed constants precede every dimension, host size, and tiling.
The dyadic mass allocation in `Tiling.Valid` supplies the host capacity;
its lower bound on `S` is essential here (16:106–107). -/
theorem low_geometry_thresholds {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16),
        n₀ ≤ T.S.n k → C₀ * (2 : ℝ) ^ T.S.n k ≤ T.S.N k →
        LowModeScaleFacts hκ Q := by
  sorry

/-- L16.1a data: coordinate IDs, the hyperplane, and ordered syndrome classes. -/
structure SyndromeData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Hdim : ℕ
  ids : Fin (T.S.n k) → (Fin Hdim → ZMod 2)
  H0 : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  Lsub : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  r : ℕ
  classEnum : Fin r ≃ Lsub

namespace SyndromeData

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

def syndrome (S : SyndromeData PT) (z : Pos T k) : Fin S.Hdim → ZMod 2 :=
  ∑ j, if z j = true then S.ids j else 0

noncomputable def classOf (S : SyndromeData PT) (z : Pos T k) : Option (Fin S.r) :=
  if h : ¬ IsEvenRole z ∧ S.syndrome z ∈ S.Lsub then
    some (S.classEnum.symm ⟨S.syndrome z, h.2⟩)
  else none

def internalAxes (_S : SyndromeData PT) : Finset (Fin (T.S.n k)) :=
  Finset.univ.biUnion fun i : Fin PT.tiling.m => PT.tiling.Icoord i

def suffix (S : SyndromeData PT) (j : ℕ) : Finset (Fin S.r) :=
  Finset.univ.filter fun t => S.r - j ≤ t.val

noncomputable def suffixNeighbours (S : SyndromeData PT) (v : Pos T k) (j : ℕ) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun i => ∃ t ∈ S.suffix j,
    S.classOf (flipPos v i) = some t

noncomputable def lateNeighbours (S : SyndromeData PT) (v : Pos T k) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun i => (S.classOf (flipPos v i)).isSome

end SyndromeData

/-- L16.1a (16:49–77): one consistent ID assignment and balanced class order. -/
structure SyndromeFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (S : SyndromeData PT) : Prop where
  group_size : T.S.n k ≤ 2 ^ S.Hdim ∧ 2 ^ S.Hdim < 2 * T.S.n k
  hyperplane_card : Fintype.card S.H0 = 2 ^ (S.Hdim - 1)
  ids_injective : Function.Injective S.ids
  hyperplane_in_ids : ∀ a : S.H0, ∃ i, S.ids i = a.1
  subspace_size :
    (κ.A0 * Real.log (T.S.n k : ℝ) ≤ (S.r : ℝ)) ∧
      (S.r : ℝ) < 2 * κ.A0 * Real.log (T.S.n k : ℝ)
  class_enum_card : Fintype.card S.Lsub = S.r
  late_subspace_not_hyperplane : ¬ S.Lsub ≤ S.H0
  internal_cosets_distinct : ∀ i ∈ S.internalAxes, ∀ j ∈ S.internalAxes,
    i ≠ j → S.ids i - S.ids j ∉ S.Lsub
  class_size : ∀ t : Fin S.r,
    Fintype.card {z : Pos T k // ¬ IsEvenRole z ∧
      S.syndrome z = S.classEnum t} = 2 ^ (T.S.n k - 1) / 2 ^ S.Hdim
  one_neighbour_per_class : ∀ v : Pos T k, IsEvenRole v → ∀ t : Fin S.r,
    ((Finset.univ.filter fun i : Fin (T.S.n k) =>
      S.classOf (flipPos v i) = some t).card : ℕ) ≤ 1
  suffix_neighbour_bounds : ∀ v : Pos T k, IsEvenRole v → ∀ j ≤ S.r,
    j / 2 ≤ (S.suffixNeighbours v j).card ∧
      (S.suffixNeighbours v j).card ≤ j
  total_late_neighbour_bounds : ∀ v : Pos T k, IsEvenRole v →
    S.r / 2 ≤ (S.lateNeighbours v).card ∧ (S.lateNeighbours v).card ≤ S.r
  at_most_one_internal_late_neighbour : ∀ v : Pos T k, IsEvenRole v →
    ((S.internalAxes.filter fun i => (S.classOf (flipPos v i)).isSome).card : ℕ) ≤ 1
  coset_criterion : ∀ v : Pos T k, IsEvenRole v → ∀ i : Fin (T.S.n k),
    (S.classOf (flipPos v i)).isSome ↔ S.ids i + S.syndrome v ∈ S.Lsub

/-- L16.1b data: cell maps are independent of the syndrome allocation. -/
structure CellData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Cell : Type
  [cellFin : Fintype Cell]
  [cellDec : DecidableEq Cell]
  cellOf : Pos T k → Cell
  patchOf : Pos T k → Fin PT.tiling.m
  patchOf_leaf : ∀ b, b ∈ PT.tiling.leaf (patchOf b)
  cellPatch : Cell → Fin PT.tiling.m
  cellOf_patch : ∀ b, cellPatch (cellOf b) = patchOf b
  nslot : Cell → ℕ

instance instCellDataFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (C : CellData PT) : Fintype C.Cell := C.cellFin

instance instCellDataDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (C : CellData PT) : DecidableEq C.Cell := C.cellDec

namespace CellData

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

def positions (C : CellData PT) (c : C.Cell) : Finset (Pos T k) :=
  Finset.univ.filter fun b => C.cellOf b = c

def cellsInPatch (C : CellData PT) (i : Fin PT.tiling.m) : Finset C.Cell :=
  Finset.univ.filter fun c => C.cellPatch c = i

def sameSlice (i : Fin PT.tiling.m) (b b' : Pos T k) : Prop :=
  ∀ j, j ∉ PT.tiling.Icoord i → b j = b' j

end CellData

/-- L16.1b (16:90–96): whole-slice cells and the batching count bound. -/
structure CellPartitionFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (C : CellData PT) : Prop where
  cells_nonempty : ∀ c, (C.positions c).Nonempty
  cell_size : ∀ c, (C.positions c).card ≤
    ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊
  /-- Complete batches have at least n^Ac/3 positions; one short batch
  per color is allowed. This is the counting input, not just an upper size. -/
  short_batches : ∀ i : Fin PT.tiling.m,
    (((C.cellsInPatch i).filter fun c =>
      ((C.positions c).card : ℝ) < Real.rpow (T.S.n k : ℝ) κ.Ac / 3).card : ℝ) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  whole_slices : ∀ c b, C.cellOf b = c → ∀ b',
    CellData.sameSlice (C.cellPatch c) b b' → C.cellOf b' = c
  slice_separation : ∀ c b b', C.cellOf b = c → C.cellOf b' = c →
    ¬ CellData.sameSlice (C.cellPatch c) b b' →
    Real.rpow (Real.log (T.S.n k : ℝ)) 3 < (hammingDist b b' : ℝ)
  cell_count : ∀ i : Fin PT.tiling.m,
    ((C.cellsInPatch i).card : ℝ) ≤
      3 * Real.rpow (2 : ℝ) ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
        Real.rpow (T.S.n k : ℝ) κ.Ac +
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  slot_count : ∀ c,
    C.nslot c = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (C.cellPatch c)).d⌉₊
  slots_fit : ∀ i : Fin PT.tiling.m,
    (∑ c ∈ C.cellsInPatch i, C.nslot c) ≤ Fintype.card (Bin PT.tiling i)

/-- L16.1 assembly data: independent syndrome and cell allocations. -/
structure LowGeometryData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  syndrome : SyndromeData PT
  cells : CellData PT

def LowGeometryData.toLowGeom {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : LowGeometryData PT) : LowGeom PT :=
  { Hdim := D.syndrome.Hdim
    ids := D.syndrome.ids
    Lsub := D.syndrome.Lsub
    r := D.syndrome.r
    classEnum := D.syndrome.classEnum
    Cell := D.cells.Cell
    cellFin := D.cells.cellFin
    cellDec := D.cells.cellDec
    cellOf := D.cells.cellOf
    patchOf := D.cells.patchOf
    patchOf_leaf := D.cells.patchOf_leaf
    cellPatch := D.cells.cellPatch
    cellOf_patch := D.cells.cellOf_patch
    nslot := D.cells.nslot }

/-- L16.1c (16:98–121): patchwise permutation pools dominate iid slots on
small scopes, including after a single global slot pin. -/
abbrev CellSlot {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) :=
  Σ c : G.Cell, Fin (G.nslot c)

abbrev PoolAssignment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) := ∀ c, CellPool G c

def DependsOnCellSlots {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (S : Finset (CellSlot G)) (F : PoolAssignment G → ℝ) : Prop :=
  ∀ P Q, (∀ s ∈ S, P s.1 s.2 = Q s.1 s.2) → F P = F Q

noncomputable def poolPinEvent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (s : CellSlot G) (D : Bin PT.tiling (G.cellPatch s.1)) :
    Finset (PoolAssignment G) :=
  Finset.univ.filter fun P => P s.1 s.2 = D

noncomputable def PoolComparison {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : Prop :=
  ∀ (i : Fin PT.tiling.m) (hperm : (permPools G).Nonempty)
    (S : Finset (CellSlot G)),
    (∀ s ∈ S, G.cellPatch s.1 = i) →
    (S.card : ℝ) ≤ Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) →
    2 * ((S.card : ℝ) + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i) →
    ∀ F : PoolAssignment G → ℝ, (∀ P, 0 ≤ F P) → DependsOnCellSlots S F →
      (permPoolLaw G hperm).E F ≤
        (1 + (S.card : ℝ) ^ 2 / Fintype.card (Bin PT.tiling i)) *
          (iidPoolLaw G hperm).E F ∧
      ∀ (s : CellSlot G) (D : Bin PT.tiling (G.cellPatch s.1)),
        (G.cellPatch s.1 = i) →
        (hpermPin : 0 < ∑ P ∈ poolPinEvent s D, (permPoolLaw G hperm).w P) →
        (hiidPin : 0 < ∑ P ∈ poolPinEvent s D, (iidPoolLaw G hperm).w P) →
        (FinLaw.cond (permPoolLaw G hperm) (poolPinEvent s D) hpermPin).E F ≤
          (1 + ((insert s S).card : ℝ) ^ 2 / Fintype.card (Bin PT.tiling i)) *
            (FinLaw.cond (iidPoolLaw G hperm) (poolPinEvent s D) hiidPin).E F

/-- Shared validity of the actual `LowGeom` consumed in Sections 17–18.
The witness ties all syndrome and cell facts to this exact geometry. -/
def LowGeomValid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (G : LowGeom PT) : Prop :=
  ∃ D : LowGeometryData PT, D.toLowGeom = G ∧
    SyndromeFacts D.syndrome ∧ CellPartitionFacts hκ Q D.cells ∧
    (permPools G).Nonempty ∧ PoolComparison G

/-- L16.1: existence assembled from the syndrome, cell, and pool subnodes. -/
structure LowGeometryCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16) where
  data : LowGeometryData PT
  scale : LowModeScaleFacts hκ Q
  late_classes : SyndromeFacts data.syndrome
  cell_partition : CellPartitionFacts hκ Q data.cells
  perm_pool_nonempty : (permPools data.toLowGeom).Nonempty
  pool_comparison : PoolComparison data.toLowGeom

namespace LowGeometryCertificate

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k} {hκ : κ.Admissible}
variable {K16 : ℝ} {Q : LowModeQuantFacts hκ (PT := PT) K16}

def geom (G : LowGeometryCertificate hκ Q) : LowGeom PT := G.data.toLowGeom

theorem geom_valid (G : LowGeometryCertificate hκ Q) : LowGeomValid hκ Q G.geom :=
  ⟨G.data, rfl, G.late_classes, G.cell_partition, G.perm_pool_nonempty, G.pool_comparison⟩

end LowGeometryCertificate

/-- L16.1a (16:49–77): syndrome IDs and the balanced class order. -/
theorem syndrome_data_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    ∃ S : SyndromeData PT, SyndromeFacts S := by
  sorry

/-- L16.1b (16:90–96): separated cells made from whole slices. -/
theorem cell_data_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    ∃ C : CellData PT, CellPartitionFacts hκ Q C := by
  sorry

/-- L16.1c (16:98–121): the pool comparison; the finite tape law is already
defined as `PartC.tapeLaw` from L16.1c's indexed lookup representation. -/
theorem pool_comparison_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) (D : LowGeometryData PT)
    (hC : CellPartitionFacts hκ Q D.cells) :
    (permPools D.toLowGeom).Nonempty ∧ PoolComparison D.toLowGeom := by
  sorry

/-- L16.1: late classes, separated cells, persistent slot pools, and tapes. -/
theorem low_geometry_at_scale {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    Nonempty (LowGeometryCertificate hκ Q) := by
  obtain ⟨S, hS⟩ := syndrome_data_exists hκ Q hScale
  obtain ⟨C, hC⟩ := cell_data_exists hκ Q hScale
  let D : LowGeometryData PT := ⟨S, C⟩
  obtain ⟨hNonempty, hPool⟩ := pool_comparison_exists hκ Q hScale D hC
  exact ⟨⟨D, hScale, hS, hC, hNonempty, hPool⟩⟩

/-- L16.1 in its eventual form. Neither cutoff may depend on the index,
the dimension, the host size, or the chosen profiled tiling. -/
theorem late_classes_and_cell_inputs {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16),
        n₀ ≤ T.S.n k → C₀ * (2 : ℝ) ^ T.S.n k ≤ T.S.N k →
        Nonempty (LowGeometryCertificate hκ Q) := by
  obtain ⟨n₀, C₀, hC₀, hScale⟩ := low_geometry_thresholds hκ
  exact ⟨n₀, C₀, hC₀, fun Q hn hN =>
    low_geometry_at_scale hκ Q (hScale Q hn hN)⟩

end HypercubeRamsey.S16
