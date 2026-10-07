import HypercubeRamsey.PartC.ProfiledTiling

/-!
# Section 16 low-mode geometry and fresh-cell interface (D16.F)
-/

namespace HypercubeRamsey

open Classical

/-- Cube positions at one stage index. -/
abbrev Pos (T : Stage) (k : ℕ) := CubePos (T.S.n k)

/-- Syndrome classes, separated cells, and slot counts for a profiled tiling. -/
structure LowGeom {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Hdim : ℕ
  ids : Fin (T.S.n k) → (Fin Hdim → ZMod 2)
  Lsub : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  r : ℕ
  classOf : Pos T k → Option (Fin r)
  Cell : Type
  [cellFin : Fintype Cell]
  [cellDec : DecidableEq Cell]
  cellOf : Pos T k → Cell
  patchOf : Pos T k → Fin PT.tiling.m
  nslot : Cell → ℕ

/-- Fresh finite-state sampler for each cell and its assigned pool. -/
structure FreshCell {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) where
  State : G.Cell → Type
  [stFin : ∀ C, Fintype (State C)]
  Pool : G.Cell → Type
  [poolFin : ∀ C, Fintype (Pool C)]
  fresh : ∀ C, Pool C → FinLaw (State C)
  fallback : ∀ C, State C
  label : ∀ C, State C → Pos T k → Fin (T.S.N k)
  prior : ∀ C, State C → Pos T k → Fin (T.S.N k) → ℝ
  typical : ∀ C, Pool C → Prop

instance instCellFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : Fintype G.Cell := G.cellFin

instance instCellDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : DecidableEq G.Cell := G.cellDec

instance instStateFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :
    ∀ C, Fintype (F.State C) := F.stFin

instance instPoolFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :
    ∀ C, Fintype (F.Pool C) := F.poolFin

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

/-- D16.F: typical pool gates for the normalizer and internal failure estimates. -/
structure PoolTypical {Slot Bin Group Hist : Type*} [DecidableEq Bin]
    [Fintype Slot] [Fintype Bin] [Fintype Group] [Fintype Hist] where
  pool : Finset Bin
  pool_nonempty : pool.Nonempty
  slots : Finset Slot
  images : Slot → Bin
  injective_on_slots : ∀ s ∈ slots, ∀ s' ∈ slots, images s = images s' → s = s'
  inPool : ∀ s ∈ slots, images s ∈ pool
  n : ℕ
  n_pos : 0 < n
  ε : ℝ
  ε_pos : 0 < ε
  slotRate : ℝ
  slotRate_eq : slotRate = (slots.card : ℝ) / pool.card
  relativeError : ℝ
  relativeError_bound : relativeError ≤ Real.rpow (n : ℝ) (-4)
  internalError : ℝ
  internalError_bound : internalError ≤ Real.rpow ε (1 / 4 : ℝ)
  normalizer : Group → Hist → ℝ
  internalFailure : Group → Hist → ℝ
  pinnedInternalFailure : Group → Hist → ℝ
  normalizer_close : ∀ g h,
    |normalizer g h / slotRate - 1| ≤ relativeError
  internal_bound : ∀ g h, internalFailure g h ≤ internalError
  pinned_internal_bound : ∀ g h, pinnedInternalFailure g h ≤ internalError

/-- D16.F: structural correctness properties of the fresh-cell sampler (F1) and (F4). -/
structure FreshCell.Spec {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (F : FreshCell G) where
  validState : ∀ C : G.Cell, F.Pool C → F.State C → Prop
  permittedLabels : ∀ C, F.Pool C → Pos T k → Finset (Fin (T.S.N k))
  inCell : Pos T k → Prop
  fresh_valid : ∀ (C : G.Cell) (P : F.Pool C) (s : F.State C),
    F.typical C P → 0 < (F.fresh C P).w s → validState C P s
  fallback_valid : ∀ (C : G.Cell) (P : F.Pool C),
    ¬ F.typical C P → validState C P (F.fallback C)
  label_permitted : ∀ (C : G.Cell) (P : F.Pool C) (s : F.State C) (b : Pos T k),
    validState C P s → inCell b →
    F.label C s b ∈ permittedLabels C P b
  labels_injective : ∀ (C : G.Cell) (s : F.State C) (b b' : Pos T k),
    inCell b → inCell b' → b ≠ b' →
    F.label C s b ≠ F.label C s b'
  prior_nonneg : ∀ (C : G.Cell) (s : F.State C) (b : Pos T k) y, 0 ≤ F.prior C s b y
  prior_subprob : ∀ (C : G.Cell) (s : F.State C) (b : Pos T k), ∑ y, F.prior C s b y ≤ 1

/-- Full cell-state configuration for a fresh-cell sampler. -/
abbrev Config {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) :=
  ∀ C, F.State C

end HypercubeRamsey
