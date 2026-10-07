import HypercubeRamsey.PartC.Resampling
import HypercubeRamsey.S16.Geometry_q_s16_geom

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
  classical
  let n := T.S.n k
  let hPT := Q.profiled_valid
  let R : ℕ := ⌈Real.rpow (Real.log (n : ℝ)) 3⌉₊
  let D : ℕ := ∑ j ∈ Finset.range (R + 1), Nat.choose n j
  have hEllH (i : Fin PT.tiling.m) :
      (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := by
    have hlen := hPT.tiling_valid.prefix_internal_length
    have hell := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
      (Finset.mem_univ i)
    omega
  let SliceValid (i : Fin PT.tiling.m) (s : CubePos n) : Prop :=
    (∀ j : Fin (PT.tiling.P i).ℓ,
      s ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ =
        (PT.tiling.w i) ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩) ∧
    (∀ j, j ∈ PT.tiling.Icoord i → s j = false)
  have hD : (∑ j ∈ Finset.range (R + 1), Nat.choose n j) ≤ D := by
    dsimp [D]
    exact le_rfl
  have sliceColoring := Lane_q_s16_geom.cube_hamming_coloring
    (m := n) (r := R) (d := D) hD
  let colors : CubePos n → Fin (D + 1) := Classical.choose sliceColoring
  have colorsProper {s t : CubePos n}
      (hst : s ≠ t) (hdist : hammingDist s t ≤ R) : colors s ≠ colors t :=
    (Classical.choose_spec sliceColoring) hst hdist
  let batchSize (i : Fin PT.tiling.m) : ℕ :=
    ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ / 2 ^ (PT.tiling.P i).h
  have batchSize_pos (i : Fin PT.tiling.m) : 0 < batchSize i := by
    have hs : 2 * 2 ^ (PT.tiling.P i).h ≤
        ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
      simpa [n] using hScale.slice_room i
    have hden : 0 < 2 ^ (PT.tiling.P i).h := Nat.pow_pos (by decide)
    have hdenle : 2 ^ (PT.tiling.P i).h ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
      calc
        2 ^ (PT.tiling.P i).h ≤ 2 * 2 ^ (PT.tiling.P i).h := by omega
        _ ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := hs
    dsimp [batchSize]
    exact Nat.div_pos hdenle hden
  let SliceClass (i : Fin PT.tiling.m) (c : Fin (D + 1)) : Finset (CubePos n) :=
    Finset.univ.filter fun s => SliceValid i s ∧ colors s = c
  let Key : Type := Σ i : Fin PT.tiling.m, Fin (D + 1) × ℕ
  letI : DecidableEq Key := Classical.decEq Key
  let patchOf : Pos T k → Fin PT.tiling.m := fun b =>
    Classical.choose (hPT.tiling_valid.prefix_complete b)
  have patchOf_leaf (b : Pos T k) : b ∈ PT.tiling.leaf (patchOf b) :=
    (Classical.choose_spec (hPT.tiling_valid.prefix_complete b)).1
  let sliceAt (i : Fin PT.tiling.m) (b : Pos T k)
      (_hb : b ∈ PT.tiling.leaf i) : CubePos n :=
    fun j => if j ∈ PT.tiling.Icoord i then false else b j
  have sliceAt_valid (i : Fin PT.tiling.m) (b : Pos T k)
      (hb : b ∈ PT.tiling.leaf i) : SliceValid i (sliceAt i b hb) := by
    constructor
    · intro j
      have hj : (⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ : Fin n) ∉
          PT.tiling.Icoord i := by
        simp [Tiling.Icoord, topCoordinates]
        have hlen := hEllH i
        omega
      simp [sliceAt, hj]
      exact hb ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ j.isLt
    · intro j hj
      simp [sliceAt, hj]
  let keyOfAt (i : Fin PT.tiling.m) (s : CubePos n) : Key := by
    classical
    let c := colors s
    if h : s ∈ SliceClass i c then
      let r := (SliceClass i c).equivFin ⟨s, h⟩
      exact ⟨i, (c, Lane_q_s16_geom.batchStart r.1 (batchSize i))⟩
    else
      exact ⟨i, (c, 0)⟩
  let sliceOf (b : Pos T k) : CubePos n :=
    sliceAt (patchOf b) b (patchOf_leaf b)
  let keyOf (b : Pos T k) : Key := keyOfAt (patchOf b) (sliceOf b)
  let keys : Finset Key := Finset.univ.image keyOf
  let Cell : Type := {key : Key // key ∈ keys}
  letI : Fintype Cell := by classical infer_instance
  letI : DecidableEq Cell := Classical.decEq Cell
  let cellPatch : Cell → Fin PT.tiling.m := fun c => c.1.1
  let cellOf (b : Pos T k) : Cell :=
    ⟨keyOf b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  let nslot (c : Cell) : ℕ :=
    ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac /
      (PT.tiling.P (cellPatch c)).d⌉₊
  have cellOf_patch (b : Pos T k) : cellPatch (cellOf b) = patchOf b := by
    dsimp [cellPatch, cellOf, keyOf, keyOfAt]
    split_ifs <;> rfl
  let C : CellData PT := @CellData.mk κ T k PT Cell
    (inferInstance : Fintype Cell) (Classical.decEq Cell)
    cellOf patchOf patchOf_leaf cellPatch cellOf_patch nslot
  have hCells_nonempty : ∀ c : Cell, (CellData.positions C c).Nonempty := by
    intro c₀
    rcases Finset.mem_image.mp c₀.2 with ⟨b, hb, hkey⟩
    refine ⟨b, ?_⟩
    have hEq : C.cellOf b = c₀ := by
      change cellOf b = c₀
      apply Subtype.ext
      exact hkey
    simpa [CellData.positions] using hEq
  have hSlotCount (c : Cell) :
      C.nslot c = ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac /
        (PT.tiling.P (C.cellPatch c)).d⌉₊ := rfl

  have hWholeSlices : ∀ c b, C.cellOf b = c → ∀ b',
      CellData.sameSlice (C.cellPatch c) b b' → C.cellOf b' = c := by
    intro c b hbc b' hsame
    let i := patchOf b
    have hpc : C.cellPatch c = i := by
      calc
        C.cellPatch c = C.cellPatch (C.cellOf b) := by rw [hbc]
        _ = patchOf b := C.cellOf_patch b
    have hsame' : CellData.sameSlice i b b' := by
      simpa [i, hpc] using hsame
    have hb'leaf : b' ∈ PT.tiling.leaf i := by
      intro j hj
      have hnot : j ∉ PT.tiling.Icoord i := by
        simp [Tiling.Icoord, topCoordinates]
        have hlen := hEllH i
        omega
      have hbits := hsame' j hnot
      rw [← hbits]
      exact patchOf_leaf b j hj
    have hpatch' : patchOf b' = i := by
      rcases hPT.tiling_valid.prefix_complete b' with ⟨j, hj, hjuniq⟩
      exact (hjuniq (patchOf b') (patchOf_leaf b')).trans
        (hjuniq i hb'leaf).symm
    have hpc' : patchOf b' = patchOf b := by
      simpa [i] using hpatch'
    have hslice : sliceOf b = sliceOf b' := by
      funext j
      dsimp [sliceOf, sliceAt]
      rw [hpc']
      by_cases hj : j ∈ PT.tiling.Icoord i
      · have hj' : j ∈ PT.tiling.Icoord (patchOf b) := by simpa [i] using hj
        simp [hj']
      · have hj' : j ∉ PT.tiling.Icoord (patchOf b) := by simpa [i] using hj
        simp [hj', hsame' j hj]
    have hkey : keyOf b = keyOf b' := by
      dsimp [keyOf]
      rw [hpc', hslice]
    have hcell : cellOf b' = cellOf b := by
      apply Subtype.ext
      exact hkey.symm
    exact hcell.trans hbc

  have hSliceSeparation : ∀ c b b', C.cellOf b = c → C.cellOf b' = c →
      ¬ CellData.sameSlice (C.cellPatch c) b b' →
      Real.rpow (Real.log (n : ℝ)) 3 < (hammingDist b b' : ℝ) := by
    intro c b b' hbc hbc' hnot
    let i := C.cellPatch c
    have hp1 : patchOf b = i := by
      dsimp [i]
      calc
        patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
        _ = C.cellPatch c := congrArg C.cellPatch hbc
    have hp2 : patchOf b' = i := by
      dsimp [i]
      calc
        patchOf b' = C.cellPatch (C.cellOf b') := (C.cellOf_patch b').symm
        _ = C.cellPatch c := congrArg C.cellPatch hbc'
    have hslices_ne : sliceOf b ≠ sliceOf b' := by
      intro hslice
      apply hnot
      intro j hj
      have h1 : sliceOf b j = b j := by
        simp [sliceOf, sliceAt, hp1, i, hj]
      have h2 : sliceOf b' j = b' j := by
        simp [sliceOf, sliceAt, hp2, i, hj]
      rw [← h1, hslice, h2]
    have hkey : keyOf b = keyOf b' := by
      have hcell : C.cellOf b = C.cellOf b' := hbc.trans hbc'.symm
      exact congrArg Subtype.val hcell
    have hk1 : (keyOf b).2.1 = colors (sliceOf b) := by
      dsimp [keyOf, keyOfAt]
      split_ifs <;> rfl
    have hk2 : (keyOf b').2.1 = colors (sliceOf b') := by
      dsimp [keyOf, keyOfAt]
      split_ifs <;> rfl
    have hcolors : colors (sliceOf b) = colors (sliceOf b') := by
      have hckey := congrArg (fun q : Key => q.2.1) hkey
      exact hk1.symm.trans (hckey.trans hk2)
    have hdistSlice : R < hammingDist (sliceOf b) (sliceOf b') := by
      by_contra hle
      have hle' : hammingDist (sliceOf b) (sliceOf b') ≤ R := Nat.le_of_not_gt hle
      exact (colorsProper hslices_ne hle') hcolors
    have hdistSub : hammingDist (sliceOf b) (sliceOf b') ≤ hammingDist b b' := by
      classical
      change (Finset.univ.filter (fun j : Fin n => sliceOf b j ≠ sliceOf b' j)).card ≤ _
      apply Finset.card_le_card
      intro j hj
      have hdiff := (Finset.mem_filter.mp hj).2
      have hjnot : j ∉ PT.tiling.Icoord i := by
        intro hjmem
        have h1 : sliceOf b j = false := by
          simp [sliceOf, sliceAt, hp1, i, hjmem]
        have h2 : sliceOf b' j = false := by
          simp [sliceOf, sliceAt, hp2, i, hjmem]
        rw [h1, h2] at hdiff
        exact hdiff rfl
      have h1 : sliceOf b j = b j := by
        simp [sliceOf, sliceAt, hp1, i, hjnot]
      have h2 : sliceOf b' j = b' j := by
        simp [sliceOf, sliceAt, hp2, i, hjnot]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [h1, h2] using hdiff⟩
    have hRle : Real.rpow (Real.log (n : ℝ)) 3 ≤ (R : ℝ) := by
      dsimp [R]
      exact Nat.le_ceil _
    have hdistReal : (R : ℝ) < (hammingDist (sliceOf b) (sliceOf b') : ℝ) := by
      exact_mod_cast hdistSlice
    have hsubReal : (hammingDist (sliceOf b) (sliceOf b') : ℝ) ≤
        (hammingDist b b' : ℝ) := by
      exact_mod_cast hdistSub
    calc
      Real.rpow (Real.log (n : ℝ)) 3 ≤ (R : ℝ) := hRle
      _ < (hammingDist (sliceOf b) (sliceOf b') : ℝ) := hdistReal
      _ ≤ (hammingDist b b' : ℝ) := hsubReal

  let innerAt (i : Fin PT.tiling.m) (b : Pos T k) :
      CubePos (PT.tiling.P i).h := fun j =>
    b ⟨n - (PT.tiling.P i).h + j.val, by
      have hj := j.isLt
      have hlen := hEllH i
      omega⟩
  let rankAt (i : Fin PT.tiling.m) (col : Fin (D + 1))
      (b : Pos T k) : ℕ := by
    classical
    if h : SliceValid i (sliceOf b) ∧ colors (sliceOf b) = col then
      have hmem : sliceOf b ∈ SliceClass i col := by
        simp [SliceClass, h]
      exact ((SliceClass i col).equivFin ⟨sliceOf b, hmem⟩).val
    else
      exact 0
  have hCellSize : ∀ c : Cell,
      (C.positions c).card ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
    intro c
    let i := C.cellPatch c
    let q := batchSize i
    have hpatchOfCell (b : Pos T k) (hb : b ∈ C.positions c) : patchOf b = i := by
      have hcell : C.cellOf b = c := (Finset.mem_filter.mp hb).2
      dsimp [i]
      calc
        patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
        _ = C.cellPatch c := congrArg C.cellPatch hcell
    have hRankBatch (b : Pos T k) (hb : b ∈ C.positions c) :
        Lane_q_s16_geom.batchStart (rankAt i (colors (sliceOf b)) b) q = c.1.2.2 := by
      let hp := hpatchOfCell b hb
      let col := colors (sliceOf b)
      have hvalid : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hp] using sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hmem : sliceOf b ∈ SliceClass i col := by
        simp [SliceClass, col, hvalid]
      let r := (SliceClass i col).equivFin ⟨sliceOf b, hmem⟩
      have hrank : rankAt i col b = r.val := by
        simp [rankAt, col, hvalid, hmem, r]
      have hkey : keyOf b = c.1 := by
        have hcell : cellOf b = c := (Finset.mem_filter.mp hb).2
        simpa [cellOf] using congrArg Subtype.val hcell
      have hstart : (keyOf b).2.2 = c.1.2.2 := congrArg (fun z : Key => z.2.2) hkey
      calc
        Lane_q_s16_geom.batchStart (rankAt i col b) q =
            Lane_q_s16_geom.batchStart r.val (batchSize i) := by
              simp [hrank, q]
        _ = (keyOf b).2.2 := by
          dsimp [keyOf, keyOfAt]
          rw [hp]
          simp [col, hmem, r]
        _ = c.1.2.2 := hstart
    let f : {b : Pos T k // b ∈ C.positions c} → Fin q × CubePos (PT.tiling.P i).h :=
      fun x => ⟨⟨rankAt i (colors (sliceOf x.1)) x.1 % q,
        Nat.mod_lt _ (batchSize_pos i)⟩, innerAt i x.1⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply funext
      intro j
      let b := x.1
      let b' := y.1
      have hp1 := hpatchOfCell b x.2
      have hp2 := hpatchOfCell b' y.2
      have hmod : rankAt i (colors (sliceOf b)) b % q =
          rankAt i (colors (sliceOf b')) b' % q :=
        congrArg (fun z : Fin q × CubePos (PT.tiling.P i).h => z.1.val) hxy
      have hinner : innerAt i b = innerAt i b' := congrArg Prod.snd hxy
      have hstart : Lane_q_s16_geom.batchStart
          (rankAt i (colors (sliceOf b)) b) q =
          Lane_q_s16_geom.batchStart (rankAt i (colors (sliceOf b')) b') q := by
        rw [hRankBatch b x.2, hRankBatch b' y.2]
      have hmul : rankAt i (colors (sliceOf b)) b / q * q =
          rankAt i (colors (sliceOf b')) b' / q * q := by
        simpa [Lane_q_s16_geom.batchStart] using hstart
      have hqpos : 0 < q := by dsimp [q]; exact batchSize_pos i
      have hdiv : rankAt i (colors (sliceOf b)) b / q =
          rankAt i (colors (sliceOf b')) b' / q :=
        Nat.mul_right_cancel hqpos hmul
      have hrank := Lane_q_s16_geom.rank_eq_of_same_batch hdiv hmod
      have hkey : keyOf b = keyOf b' := by
        have hcell₁ : cellOf b = c := (Finset.mem_filter.mp x.2).2
        have hcell₂ : cellOf b' = c := (Finset.mem_filter.mp y.2).2
        have hcell : cellOf b = cellOf b' := hcell₁.trans hcell₂.symm
        simpa [cellOf] using congrArg Subtype.val hcell
      have hk1 : (keyOf b).2.1 = colors (sliceOf b) := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hk2 : (keyOf b').2.1 = colors (sliceOf b') := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hcolors : colors (sliceOf b) = colors (sliceOf b') := by
        exact hk1.symm.trans
          ((congrArg (fun z : Key => z.2.1) hkey).trans hk2)
      have hv1 : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hp1] using sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hv2 : SliceValid i (sliceOf b') := by
        simpa [sliceOf, hp2] using sliceAt_valid (patchOf b') b' (patchOf_leaf b')
      have hm1 : sliceOf b ∈ SliceClass i (colors (sliceOf b)) := by
        simp [SliceClass, hv1]
      have hm2 : sliceOf b' ∈ SliceClass i (colors (sliceOf b)) := by
        simp [SliceClass, hv2, hcolors]
      have hslice : sliceOf b = sliceOf b' := by
        let col := colors (sliceOf b)
        have hrank' : rankAt i col b = rankAt i col b' := by
          simpa [col, hcolors] using hrank
        have hval1 : rankAt i col b =
            ((SliceClass i (colors (sliceOf b))).equivFin ⟨sliceOf b, hm1⟩).val := by
          simp [rankAt, col, hv1, hm1]
        have hval2 : rankAt i col b' =
            ((SliceClass i col).equivFin ⟨sliceOf b', hm2⟩).val := by
          simp [rankAt, col, hv2, hcolors.symm, hm2]
        have hfin : (SliceClass i (colors (sliceOf b))).equivFin
              ⟨sliceOf b, hm1⟩ =
            (SliceClass i (colors (sliceOf b))).equivFin ⟨sliceOf b', hm2⟩ := by
          apply Fin.ext
          rw [← hval1, ← hval2]
          exact hrank'
        exact congrArg Subtype.val
          ((SliceClass i (colors (sliceOf b))).equivFin.injective hfin)
      change b j = b' j
      by_cases hj : j ∈ PT.tiling.Icoord i
      · have htop : n - (PT.tiling.P i).h ≤ j.val := by
          simpa [Tiling.Icoord, topCoordinates] using hj
        let t : Fin (PT.tiling.P i).h :=
          ⟨j.val - (n - (PT.tiling.P i).h), by
            have hjlt := j.isLt
            omega⟩
        have hcoord : (⟨n - (PT.tiling.P i).h + t.val,
            by have ht := t.isLt; have hlen := hEllH i; omega⟩ : Fin n) = j := by
          apply Fin.ext
          dsimp [t]
          omega
        have hbit := congrFun hinner t
        change b ⟨n - (PT.tiling.P i).h + t.val, by
          have ht := t.isLt; have hlen := hEllH i; omega⟩ =
          b' ⟨n - (PT.tiling.P i).h + t.val, by
            have ht := t.isLt; have hlen := hEllH i; omega⟩ at hbit
        rw [← hcoord]
        exact hbit
      · have h1 : sliceOf b j = b j := by simp [sliceOf, sliceAt, hp1, i, hj]
        have h2 : sliceOf b' j = b' j := by simp [sliceOf, sliceAt, hp2, i, hj]
        rw [← h1, hslice, h2]
    have hcard : (C.positions c).card ≤ Fintype.card (Fin q × CubePos (PT.tiling.P i).h) := by
      have hsubtype : Fintype.card {b : Pos T k // b ∈ C.positions c} =
          (C.positions c).card := by
        rw [Fintype.card_subtype]
        simp
      rw [← hsubtype]
      exact Fintype.card_le_of_injective f hf
    calc
      (C.positions c).card ≤ Fintype.card (Fin q × CubePos (PT.tiling.P i).h) := hcard
      _ = q * 2 ^ (PT.tiling.P i).h := by simp
      _ = (⌊Real.rpow (n : ℝ) κ.Ac⌋₊ / 2 ^ (PT.tiling.P i).h) *
          2 ^ (PT.tiling.P i).h := by rfl
      _ ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := Nat.div_mul_le_self _ _

  have hCellCount : ∀ i : Fin PT.tiling.m,
      ((C.cellsInPatch i).card : ℝ) ≤
        3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
          Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
    intro i
    classical
    let cells := C.cellsInPatch i
    let q := batchSize i
    have hq : 0 < q := batchSize_pos i
    let validSlices : Finset (CubePos n) := Finset.univ.filter (SliceValid i)
    have hClassEq (col : Fin (D + 1)) :
        SliceClass i col = validSlices.filter (fun s => colors s = col) := by
      ext s
      simp [SliceClass, validSlices, and_assoc]
    have hsumClasses :
        (∑ col : Fin (D + 1), (SliceClass i col).card) = validSlices.card := by
      simpa [hClassEq] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (s := validSlices) (t := (Finset.univ : Finset (Fin (D + 1))))
          (g := colors))
    have hEllH' : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := hEllH i
    have hValidCard : validSlices.card ≤
        2 ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) := by
      let freeAt : Fin (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) → Fin n :=
        fun j => ⟨(PT.tiling.P i).ℓ + j.val, by
          have hj := j.isLt
          omega⟩
      let encode : {s : CubePos n // SliceValid i s} →
          CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) :=
        fun s j => s.1 (freeAt j)
      have hEncode : Function.Injective encode := by
        intro x y hxy
        apply Subtype.ext
        funext a
        by_cases hprefix : a.val < (PT.tiling.P i).ℓ
        · let p : Fin (PT.tiling.P i).ℓ := ⟨a.val, hprefix⟩
          have hidx :
              (⟨p.val, by have hp := p.isLt; omega⟩ : Fin n) = a := by
            apply Fin.ext
            rfl
          rw [← hidx]
          rw [x.2.1 p, y.2.1 p]
        · by_cases htop : n - (PT.tiling.P i).h ≤ a.val
          · have hmem : a ∈ PT.tiling.Icoord i := by
              simpa [Tiling.Icoord, topCoordinates] using htop
            rw [x.2.2 a hmem, y.2.2 a hmem]
          · let j : Fin (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) :=
              ⟨a.val - (PT.tiling.P i).ℓ, by omega⟩
            have hfree : freeAt j = a := by
              apply Fin.ext
              simp [freeAt, j]
              omega
            have h := congrFun hxy j
            change x.1 (freeAt j) = y.1 (freeAt j) at h
            simpa [hfree] using h
      have hsub : Fintype.card {s : CubePos n // SliceValid i s} ≤
          Fintype.card (CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h)) :=
        Fintype.card_le_of_injective encode hEncode
      have hcard : validSlices.card =
          Fintype.card {s : CubePos n // SliceValid i s} := by
        rw [Fintype.card_subtype]
      rw [hcard]
      calc
        Fintype.card {s : CubePos n // SliceValid i s} ≤
            Fintype.card (CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h)) := hsub
        _ = 2 ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) := by
          simp [CubePos, Fintype.card_fun]
    let Starts : Fin (D + 1) → Type := fun col =>
      {r : Fin (SliceClass i col).card // r.val % q = 0}
    have hstartBound (col : Fin (D + 1)) :
        Fintype.card (Starts col) ≤ (SliceClass i col).card / q + 1 := by
      exact Lane_q_s16_geom.card_rank_starts_le (SliceClass i col).card q
    let toStarts : {c : Cell // c ∈ cells} → Σ col, Starts col := fun x => by
      let c := x.1
      let b : Pos T k := Classical.choose (hCells_nonempty c)
      have hb : b ∈ C.positions c := Classical.choose_spec (hCells_nonempty c)
      have hcell : C.cellOf b = c := (Finset.mem_filter.mp hb).2
      have hkey : keyOf b = c.1 := by
        change cellOf b = c at hcell
        exact congrArg Subtype.val hcell
      have hpatchC : c.1.1 = i := by
        change C.cellPatch c = i
        exact (Finset.mem_filter.mp x.2).2
      have hpatch : patchOf b = i := by
        calc
          patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
          _ = C.cellPatch c := congrArg C.cellPatch hcell
          _ = i := hpatchC
      have hvalid : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hpatch] using
          sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hkcolor : (keyOf b).2.1 = colors (sliceOf b) := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hcolor : colors (sliceOf b) = c.1.2.1 := by
        exact hkcolor.symm.trans (congrArg (fun z : Key => z.2.1) hkey)
      have hmem : sliceOf b ∈ SliceClass i c.1.2.1 := by
        simp [SliceClass, hvalid, hcolor]
      let r := (SliceClass i c.1.2.1).equivFin ⟨sliceOf b, hmem⟩
      have hstart : c.1.2.2 = Lane_q_s16_geom.batchStart r.val q := by
        calc
          c.1.2.2 = (keyOf b).2.2 := (congrArg (fun z : Key => z.2.2) hkey).symm
          _ = Lane_q_s16_geom.batchStart r.val q := by
            dsimp [keyOf, keyOfAt]
            rw [hpatch]
            rw [hcolor]
            simp [r, hmem, q]
      have hlt : c.1.2.2 < (SliceClass i c.1.2.1).card := by
        rw [hstart]
        exact (Lane_q_s16_geom.batchStart_le_rank r.val q).trans_lt r.isLt
      have hmod : c.1.2.2 % q = 0 := by
        rw [hstart]
        exact Lane_q_s16_geom.batchStart_mod r.val q
      exact ⟨c.1.2.1, ⟨⟨c.1.2.2, hlt⟩, hmod⟩⟩
    have hInjective : Function.Injective toStarts := by
      intro x y hxy
      have hpatchX : x.1.1.1 = i := by
        change C.cellPatch x.1 = i
        exact (Finset.mem_filter.mp x.2).2
      have hpatchY : y.1.1.1 = i := by
        change C.cellPatch y.1 = i
        exact (Finset.mem_filter.mp y.2).2
      have hcolor : x.1.1.2.1 = y.1.1.2.1 := congrArg Sigma.fst hxy
      have hstart : x.1.1.2.2 = y.1.1.2.2 :=
        congrArg (fun z : Σ col, Starts col => z.2.1.val) hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Sigma.ext
      · exact hpatchX.trans hpatchY.symm
      · exact heq_of_eq (Prod.ext hcolor hstart)
    have hcardCells : cells.card ≤
        ∑ col : Fin (D + 1), Fintype.card (Starts col) := by
      have hsubcard : Fintype.card {c : Cell // c ∈ cells} = cells.card := by
        rw [Fintype.card_subtype]
        simp
      calc
        cells.card = Fintype.card {c : Cell // c ∈ cells} := hsubcard.symm
        _ ≤ Fintype.card (Σ col, Starts col) := Fintype.card_le_of_injective toStarts hInjective
        _ = ∑ col : Fin (D + 1), Fintype.card (Starts col) := by
          simp [Fintype.card_sigma]
    have hcountNat : cells.card ≤
        ∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1) := by
      calc
        cells.card ≤ ∑ col : Fin (D + 1), Fintype.card (Starts col) := hcardCells
        _ ≤ ∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1) := by
          apply Finset.sum_le_sum
          intro col hcol
          exact hstartBound col
    have hsumDiv :
        (∑ col : Fin (D + 1), (((SliceClass i col).card / q : ℕ) : ℝ)) ≤
          (validSlices.card : ℝ) / (q : ℝ) := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      calc
        (∑ col : Fin (D + 1), (((SliceClass i col).card / q : ℕ) : ℝ)) ≤
            ∑ col : Fin (D + 1),
              ((SliceClass i col).card : ℝ) / (q : ℝ) := by
          apply Finset.sum_le_sum
          intro col hcol
          apply (le_div_iff₀ hqR).2
          exact_mod_cast (Nat.div_mul_le_self (SliceClass i col).card q)
        _ = (∑ col : Fin (D + 1), (SliceClass i col).card : ℝ) / (q : ℝ) := by
          rw [Finset.sum_div]
        _ = ((∑ col : Fin (D + 1), (SliceClass i col).card : ℕ) : ℝ) / (q : ℝ) := by
          rw [Nat.cast_sum]
        _ = (validSlices.card : ℝ) / (q : ℝ) := by rw [hsumClasses]
    have hcountReal : (cells.card : ℝ) ≤
        (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := by
      have hcast : (cells.card : ℝ) ≤
          ((∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1 : ℕ)) : ℝ) := by
        exact_mod_cast hcountNat
      simp only [Nat.cast_add, Nat.cast_one] at hcast
      calc
        (cells.card : ℝ) ≤
            ∑ col : Fin (D + 1),
              (((SliceClass i col).card / q : ℕ) : ℝ) + (D + 1 : ℝ) := by
                simpa [Finset.sum_add_distrib] using hcast
        _ ≤ (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := by
          gcongr
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by
        dsimp [n]
        exact lt_of_lt_of_le (by norm_num) hScale.n_four
      exact_mod_cast this
    have hpow : 0 < Real.rpow (n : ℝ) κ.Ac := Real.rpow_pos_of_pos hn _
    let F : ℕ := ⌊Real.rpow (n : ℝ) κ.Ac⌋₊
    let d : ℕ := 2 ^ (PT.tiling.P i).h
    have hd : 0 < d := by dsimp [d]; exact Nat.pow_pos (by decide)
    have hF : 2 * d ≤ F := by
      dsimp [F, d, n]
      simpa using hScale.slice_room i
    have hqEq : q = F / d := by rfl
    have hqTwo : 2 ≤ q := by
      rw [hqEq]
      exact (Nat.le_div_iff_mul_le hd).2 (by nlinarith)
    have hrem : F % d < d := Nat.mod_lt _ hd
    have hdecomp : F = F % d + d * (F / d) := (Nat.mod_add_div F d).symm
    have hFlt : F < 2 * (q * d) := by
      rw [hqEq]
      nlinarith [hdecomp, hrem, hqTwo]
    have hRealX : Real.rpow (n : ℝ) κ.Ac ≤ 3 * (q : ℝ) * (d : ℝ) := by
      have hfloor : Real.rpow (n : ℝ) κ.Ac < (F : ℝ) + 1 := by
        dsimp [F]
        exact Nat.lt_floor_add_one (Real.rpow (n : ℝ) κ.Ac)
      have hFcast : (F : ℝ) < 2 * (q : ℝ) * (d : ℝ) := by
        have hFltCast : (F : ℝ) < 2 * ((q : ℝ) * (d : ℝ)) := by
          exact_mod_cast hFlt
        simpa [mul_assoc] using hFltCast
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqTwo
      have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
      have hqd : (1 : ℝ) ≤ (q : ℝ) * (d : ℝ) := by nlinarith
      nlinarith
    have hDivBound :
        (validSlices.card : ℝ) / (q : ℝ) ≤
          3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            Real.rpow (n : ℝ) κ.Ac := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hvalidR : (validSlices.card : ℝ) ≤
          Real.rpow (2 : ℝ)
            ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) := by
        have hpowNat (m : ℕ) : Real.rpow (2 : ℝ) (m : ℝ) = (2 : ℝ) ^ m :=
          Real.rpow_natCast (2 : ℝ) m
        rw [hpowNat]
        exact_mod_cast hValidCard
      have hexp : (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) +
          (PT.tiling.P i).h = n - (PT.tiling.P i).ℓ := by omega
      have hpow2 :
          Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
              (2 : ℝ) ^ (PT.tiling.P i).h =
            Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) := by
        have hpowNat (m : ℕ) : Real.rpow (2 : ℝ) (m : ℝ) = (2 : ℝ) ^ m :=
          Real.rpow_natCast (2 : ℝ) m
        rw [hpowNat, hpowNat]
        calc
          (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) *
              (2 : ℝ) ^ (PT.tiling.P i).h =
              (2 : ℝ) ^ ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) +
                (PT.tiling.P i).h) := by rw [← pow_add]
          _ = (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) := by rw [hexp]
      have hrecip : (1 : ℝ) / (q : ℝ) ≤
          3 * (2 : ℝ) ^ (PT.tiling.P i).h / Real.rpow (n : ℝ) κ.Ac := by
        have hmul : Real.rpow (n : ℝ) κ.Ac ≤
            3 * (q : ℝ) * (2 : ℝ) ^ (PT.tiling.P i).h := by
          simpa [d] using hRealX
        rw [div_le_div_iff₀ hqR hpow]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      calc
        (validSlices.card : ℝ) / (q : ℝ) ≤
            Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) / (q : ℝ) :=
                (div_le_div_of_nonneg_right hvalidR hqR.le)
        _ = Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) * (1 / (q : ℝ)) := by ring
        _ ≤ Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
              (3 * (2 : ℝ) ^ (PT.tiling.P i).h / Real.rpow (n : ℝ) κ.Ac) := by
                exact mul_le_mul_of_nonneg_left hrecip
                  (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        _ = 3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
              Real.rpow (n : ℝ) κ.Ac := by
                calc
                  _ = 3 *
                      (Real.rpow (2 : ℝ)
                        ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
                        (2 : ℝ) ^ (PT.tiling.P i).h) /
                        Real.rpow (n : ℝ) κ.Ac := by ring
                  _ = _ := by rw [hpow2]
    have hColorCast : (D + 1 : ℝ) ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
      calc
        (D + 1 : ℝ) = 1 +
            ∑ j ∈ Finset.range (R + 1), (Nat.choose n j : ℝ) := by
              simp [D, Nat.cast_sum, add_comm]
        _ ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
              simpa [R, n] using hScale.coloring_room
    calc
      ((C.cellsInPatch i).card : ℝ) = (cells.card : ℝ) := rfl
      _ ≤ (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := hcountReal
      _ ≤ 3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
              exact add_le_add hDivBound hColorCast
  have hSlotsFit : ∀ i : Fin PT.tiling.m,
      (∑ c ∈ C.cellsInPatch i, C.nslot c) ≤ Fintype.card (Bin PT.tiling i) := by
    intro i
    let cells := C.cellsInPatch i
    let q : ℕ := ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊
    have hslots : ∀ c ∈ cells, C.nslot c = q := by
      intro c hc
      have hpatch : C.cellPatch c = i := (Finset.mem_filter.mp hc).2
      rw [hSlotCount c]
      simp [q, hpatch]
    have hsum : (∑ c ∈ cells, C.nslot c) = cells.card * q := by
      calc
        (∑ c ∈ cells, C.nslot c) = ∑ c ∈ cells, q := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hslots c hc
        _ = cells.card * q := by simp
    have hcount := hCellCount i
    have hprod : (cells.card : ℝ) * (q : ℝ) ≤
        (3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
          Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg q)
    have hcap := hScale.patch_capacity i
    have htotal : ((cells.card * q : ℕ) : ℝ) ≤ Fintype.card (Bin PT.tiling i) := by
      rw [Nat.cast_mul]
      dsimp [q] at hprod hcap ⊢
      exact hprod.trans hcap
    rw [hsum]
    exact_mod_cast htotal

  refine ⟨C, ?_⟩
  refine ⟨hCells_nonempty, hCellSize, ?_, hWholeSlices, ?_, hCellCount, hSlotCount, hSlotsFit⟩
  · sorry
  · intro c b b' hbc hbc' hnot
    simpa [n] using hSliceSeparation c b b' hbc hbc' hnot

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
