import HypercubeRamsey.PartC.ProfiledTiling

/-!
# Section 16 low-mode geometry and fresh-cell interface (D16.F)
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Cube positions at one stage index. -/
abbrev Pos (T : Stage) (k : ℕ) := CubePos (T.S.n k)

/-- Syndrome classes, separated cells, and slot counts for a profiled tiling (L16.1).

The late classes are determined by the coordinate IDs and the subspace `Lsub`: an odd role `z` is late
iff its syndrome `s(z) = ∑ₖ aₖ zₖ` lies in `Lsub`, and its class is `s(z)`; `classEnum` fixes the
numbering of the `r = |Lsub|` classes (the processing order). -/
structure LowGeom {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Hdim : ℕ
  ids : Fin (T.S.n k) → (Fin Hdim → ZMod 2)
  Lsub : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  r : ℕ
  classEnum : Fin r ≃ Lsub
  Cell : Type
  [cellFin : Fintype Cell]
  [cellDec : DecidableEq Cell]
  cellOf : Pos T k → Cell
  patchOf : Pos T k → Fin PT.tiling.m
  /-- `patchOf b` is the patch whose prefix leaf contains `b`. -/
  patchOf_leaf : ∀ b, b ∈ PT.tiling.leaf (patchOf b)
  /-- Every cell lies in one patch. -/
  cellPatch : Cell → Fin PT.tiling.m
  cellOf_patch : ∀ b, cellPatch (cellOf b) = patchOf b
  nslot : Cell → ℕ

namespace LowGeom

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

/-- Syndrome `s(z) = ∑ₖ aₖ zₖ` of a cube position. -/
def syndrome (G : LowGeom PT) (z : Pos T k) : Fin G.Hdim → ZMod 2 :=
  ∑ j, if z j = true then G.ids j else 0

/-- Late class of a position: `some t` iff it is an odd role with syndrome in `Lsub`. -/
noncomputable def classOf (G : LowGeom PT) (z : Pos T k) : Option (Fin G.r) :=
  if h : ¬ IsEvenRole z ∧ G.syndrome z ∈ G.Lsub then
    some (G.classEnum.symm ⟨G.syndrome z, h.2⟩)
  else none

end LowGeom

instance instCellFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : Fintype G.Cell := G.cellFin

instance instCellDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : DecidableEq G.Cell := G.cellDec

/-- The pool of a cell (L16.1c): the images of its `nslot C` slots among the physical bins of its
patch. -/
abbrev CellPool {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (G : LowGeom PT) (C : G.Cell) :=
  Fin (G.nslot C) → Bin PT.tiling (G.cellPatch C)

/-- Global pool assignments in which distinct slots of one patch have distinct images (the support
of the permutation pool law). -/
noncomputable def permPools {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (G : LowGeom PT) : Finset (∀ C, CellPool G C) :=
  Finset.univ.filter fun P => ∀ (C C' : G.Cell) (s : Fin (G.nslot C)) (s' : Fin (G.nslot C')),
    G.cellPatch C = G.cellPatch C' → (P C s).1 = (P C' s').1 → C = C' ∧ s.val = s'.val

/-- Permutation pools (L16.1c): an independent uniform injection of each patch's slots into its
bins, i.e. the uniform law on patch-wise injective assignments. -/
noncomputable def permPoolLaw {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (G : LowGeom PT) (h : (permPools G).Nonempty) : FinLaw (∀ C, CellPool G C) :=
  FinLaw.uniform (permPools G) h

/-- iid uniform slots: the uniform law on all assignments. -/
noncomputable def iidPoolLaw {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (G : LowGeom PT) (h : (permPools G).Nonempty) : FinLaw (∀ C, CellPool G C) :=
  FinLaw.uniform Finset.univ ⟨h.choose, Finset.mem_univ _⟩

/-- Fresh finite-state sampler for each cell and each possible pool of the cell. -/
structure FreshCell {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) where
  State : G.Cell → Type
  [stFin : ∀ C, Fintype (State C)]
  fresh : ∀ C, CellPool G C → FinLaw (State C)
  fallback : ∀ C, State C
  label : ∀ C, State C → Pos T k → Fin (T.S.N k)
  prior : ∀ C, State C → Pos T k → Fin (T.S.N k) → ℝ
  typical : ∀ C, CellPool G C → Prop

/-- The pools of a cell, as seen from a fresh-cell sampler. -/
abbrev FreshCell.Pool {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (_F : FreshCell G) (C : G.Cell) :=
  CellPool G C

instance instStateFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :
    ∀ C, Fintype (F.State C) := F.stFin

noncomputable instance instPoolFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :
    ∀ C, Fintype (F.Pool C) := fun _ => inferInstance

/-- D16.F: fixed permission table; bins with a frequently forbidden label are removed. -/
structure PermissionTable (Group Bin Label Incidence : Type*)
    [Fintype Group] [Fintype Bin] [Fintype Label] where
  n : ℕ
  n_pos : 0 < n
  cperm : ℝ
  cperm_pos : 0 < cperm
  groupOf : Incidence → Group
  labels : Bin → Finset Label
  badMass : Incidence → Label → ℝ
  permitted : Group → Finset Bin
  permitted_iff : ∀ g D, D ∈ permitted g ↔
    ∀ inc, groupOf inc = g → ∀ y ∈ labels D, badMass inc y ≤ Real.exp (-cperm * n)

/-- Group law after excluding the permission-table-forbidden bins. -/
noncomputable def permissionRestrictedLaw {Group Bin Label Incidence : Type*}
    [Fintype Group] [Fintype Bin] [Fintype Label] [DecidableEq Bin]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (g : Group) (hpos : 0 < ∑ D ∈ P.permitted g, (qin g).w D) : FinLaw Bin :=
  FinLaw.cond (qin g) (P.permitted g) hpos

/-- Pool-restricted group law at a typical cell pool. -/
noncomputable def poolRestrictedLaw {Group Bin Label Incidence : Type*}
    [Fintype Group] [Fintype Bin] [Fintype Label] [DecidableEq Bin]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (g : Group) (pool : Finset Bin)
    (hpos : 0 < ∑ D ∈ P.permitted g, (qin g).w D)
    (hpool : 0 < ∑ D ∈ pool, (permissionRestrictedLaw P qin g hpos).w D) : FinLaw Bin :=
  FinLaw.cond (permissionRestrictedLaw P qin g hpos) pool hpool

/-- D16.F: individual pool typicality (sections/16 lines 178–190), as a predicate of the actual
pool data and of the actual normalizers and internal failure probabilities, which the caller
supplies: distinct slot images; every normalizer `∑_{D ∈ pool} q̄_g(D)` equals
`(L^slot/Bᵢ)(1 ± n⁻⁴)` (`Bᵢ` = number of physical bins); internal star failures at most `ε^{1/4}`,
also with one group-bin pin. -/
structure PoolTypical {Slot Bin Group Hist : Type*} [DecidableEq Bin]
    [Fintype Slot] [Fintype Bin] [Fintype Group] [Fintype Hist]
    (pool : Finset Bin) (slots : Finset Slot) (images : Slot → Bin) (n : ℕ) (ε : ℝ)
    (normalizer internalFailure pinnedInternalFailure : Group → Hist → ℝ) : Prop where
  pool_eq : pool = slots.image images
  injective_on_slots : ∀ s ∈ slots, ∀ s' ∈ slots, images s = images s' → s = s'
  normalizer_close : ∀ g h,
    |normalizer g h / ((slots.card : ℝ) / Fintype.card Bin) - 1| ≤ Real.rpow (n : ℝ) (-4)
  internal_bound : ∀ g h, internalFailure g h ≤ Real.rpow ε (1 / 4 : ℝ)
  pinned_internal_bound : ∀ g h, pinnedInternalFailure g h ≤ Real.rpow ε (1 / 4 : ℝ)

/-- D16.F: structural properties (F1) and (F4) of a fresh-cell sampler, relative to the caller's
state-validity predicate and permitted-label table (both determined by the profiled tiling and
the permission table in Section 16). Atypical pools use the fixed fallback state; labels are read
on the odd roles of the cell, and are injective there. -/
structure FreshCell.Spec {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (F : FreshCell G)
    (validState : ∀ C : G.Cell, F.Pool C → F.State C → Prop)
    (permittedLabels : ∀ C : G.Cell, F.Pool C → Pos T k → Finset (Fin (T.S.N k))) : Prop where
  fresh_valid : ∀ (C : G.Cell) (P : F.Pool C) (s : F.State C),
    F.typical C P → 0 < (F.fresh C P).w s → validState C P s
  fresh_atypical : ∀ (C : G.Cell) (P : F.Pool C),
    ¬ F.typical C P → F.fresh C P = FinLaw.dirac (F.fallback C)
  label_permitted : ∀ (C : G.Cell) (P : F.Pool C) (s : F.State C) (b : Pos T k),
    validState C P s → G.cellOf b = C → ¬ IsEvenRole b →
    F.label C s b ∈ permittedLabels C P b
  labels_injective : ∀ (C : G.Cell) (s : F.State C) (b b' : Pos T k),
    G.cellOf b = C → G.cellOf b' = C → ¬ IsEvenRole b → ¬ IsEvenRole b' → b ≠ b' →
    F.label C s b ≠ F.label C s b'
  prior_nonneg : ∀ (C : G.Cell) (s : F.State C) (b : Pos T k) y, 0 ≤ F.prior C s b y
  prior_subprob : ∀ (C : G.Cell) (s : F.State C) (b : Pos T k), ∑ y, F.prior C s b y ≤ 1

/-- Full cell-state configuration for a fresh-cell sampler. -/
abbrev Config {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :=
  ∀ C, F.State C

end HypercubeRamsey
