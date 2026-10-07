import HypercubeRamsey.S16.Calibrations

/-!
# Section 16 typical pools and fresh comparisons

Pool concentration is separated from the history load gate. Fresh singleton
and internal-prior comparisons are assembled from fixed-pool calibration and
the iid-slot cancellation nodes.
-/

namespace HypercubeRamsey.S16

open Classical
open scoped BigOperators

/-- L16.2 input: a finite slot experiment. `typical` is represented by the
normalizer and pinned-star diagnostics; history draws and the load gate are
kept conditional on the realized pool. -/
structure CellPoolDiagnostics (Slot Bin Hist Check : Type*)
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] where
  slots_nonempty : Nonempty Slot
  bins_nonempty : Nonempty Bin
  checks_nonempty : Nonempty Check
  n : ℕ
  ε : ℝ
  c0 : ℝ
  c0_pos : 0 < c0
  iidSlotLaw : Slot → FinLaw Bin
  poolLaw : FinLaw (Slot → Bin)
  poolLaw_eq : poolLaw = FinLaw.pi iidSlotLaw
  pinLaw : Slot → Bin → FinLaw (Slot → Bin)
  normalizer : (Slot → Bin) → Check → ℝ
  center : Check → ℝ
  tolerance : Check → ℝ
  historyLaw : (Slot → Bin) → FinLaw Hist
  loadGate : (Slot → Bin) → Hist → Prop
  loadValue : (Slot → Bin) → Hist → ℝ
  loadThreshold : ℝ
  loadGate_iff : ∀ pool h, loadGate pool h ↔ loadValue pool h ≤ loadThreshold

namespace CellPoolDiagnostics

variable {Slot Bin Hist Check : Type*}
variable [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
variable [Fintype Hist] [Fintype Check]

def typical (D : CellPoolDiagnostics Slot Bin Hist Check) (pool : Slot → Bin) : Prop :=
  ∀ c, |D.normalizer pool c - D.center c| ≤ D.tolerance c

end CellPoolDiagnostics

/-- L16.2 concentration inputs: raw means, one-slot sensitivities, and history count are
inputs to X-McDiarmid. These are the empirical-measure expansion estimates
from the L16.2 proof, prior to the union bound. -/
structure PoolConcentrationHypotheses {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check]
    (D : CellPoolDiagnostics Slot Bin Hist Check) : Prop where
  n_large : 2 ≤ D.n
  slots_large : 2 ≤ Fintype.card Slot
  epsilon_pos : 0 < D.ε ∧ D.ε ≤ 1
  tolerance_pos : ∀ c, 0 < D.tolerance c
  center_nonneg : ∀ c, 0 ≤ D.center c
  mean_close : ∀ c,
    |D.poolLaw.E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2
  one_slot_change : ∀ c s x y,
    (∀ s', s' ≠ s → x s' = y s') →
    |D.normalizer x c - D.normalizer y c| ≤
      D.tolerance c / (4 * Real.sqrt (Fintype.card Slot : ℝ))
  pinned_mean_close : ∀ s b c,
    |(D.pinLaw s b).E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2
  pinned_one_slot_change : ∀ c (s₀ s : Slot) (b₀ : Bin) x y,
    s ≠ s₀ → x s₀ = b₀ → y s₀ = b₀ →
    (∀ s', s' ≠ s → x s' = y s') →
    |D.normalizer x c - D.normalizer y c| ≤
      D.tolerance c / (4 * Real.sqrt (Fintype.card Slot : ℝ))
  check_count : (Fintype.card Check : ℝ) ≤ Real.exp (Real.rpow (D.n : ℝ) 1.01)
  history_count : (Fintype.card Hist : ℝ) ≤ Real.exp (Real.rpow (D.n : ℝ) 1.01)

/-- L16.2 load input: each slice is independent before the cell gate, its
expected contribution is below the load threshold, and one slice has a small
maximum contribution. -/
structure LoadGateHypotheses {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check]
    (D : CellPoolDiagnostics Slot Bin Hist Check) where
  loadMean_small : ∀ pool, D.typical pool →
    (D.historyLaw pool).E (D.loadValue pool) ≤ D.loadThreshold / 2
  sliceContribution : ℝ
  sliceContribution_pos : 0 < sliceContribution
  sliceContribution_small : sliceContribution ≤ (D.n : ℝ) ^ (-100 : ℝ)

/-- L16.2 output consumed by Sections 17 and 18. -/
structure TypicalPoolCertificate {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check]
    (D : CellPoolDiagnostics Slot Bin Hist Check) (c0 : ℝ) where
  c0_pos : 0 < c0
  typical_probability : D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤
    Real.exp (-(D.n : ℝ) ^ c0)
  pinned_probability : ∀ s b,
    (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤
      Real.exp (-(D.n : ℝ) ^ c0)
  gate_failure : ∀ pool, D.typical pool →
    (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) ≤
      Real.exp (-(D.n : ℝ) ^ c0)
  gate_conditioning_cost : ∀ pool (_hpool : D.typical pool)
      (hgate : 0 < ∑ h ∈ Finset.univ.filter (fun h => D.loadGate pool h),
        (D.historyLaw pool).w h)
      (F : Hist → ℝ), (∀ h, 0 ≤ F h) →
      (FinLaw.cond (D.historyLaw pool)
        (Finset.univ.filter fun h => D.loadGate pool h) hgate).E F ≤
        (1 - Real.exp (-(D.n : ℝ) ^ c0))⁻¹ *
          (D.historyLaw pool).E F

def PermissionLossFact {Group Bin Label Incidence : Type*}
    [Fintype Group] [Fintype Bin] [Fintype Label]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ g, ((P.permitted g).card : ℝ) ≥
      (1 - Real.exp (-c * P.n)) * Fintype.card Bin) ∧
    (∀ g, ∑ b ∈ P.permitted g, (qin g).w b ≥ 1 - Real.exp (-c * P.n))

def permissionIncidences {Group Bin Label Incidence : Type*}
    [Fintype Group] [Fintype Bin] [Fintype Label] [Fintype Incidence]
    [DecidableEq Incidence] [DecidableEq Group]
    (P : PermissionTable Group Bin Label Incidence) (g : Group) : Finset Incidence :=
  Finset.univ.filter fun inc => P.groupOf inc = g

def binsContainingLabel {Group Bin Label Incidence : Type*}
    [Fintype Group] [Fintype Bin] [Fintype Label] [DecidableEq Bin] [DecidableEq Label]
    (P : PermissionTable Group Bin Label Incidence) (y : Label) : Finset Bin :=
  Finset.univ.filter fun D => y ∈ P.labels D

/-- L16.2a inputs: nonnegative bad masses with the deep-discrepancy mean
bound, few incidences per group, disjoint bin labels, and the D14.S atom cap. -/
structure PermissionLossHypotheses {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin) : Prop where
  groups_nonempty : Nonempty Group
  bins_nonempty : Nonempty Bin
  labels_nonempty : Nonempty Label
  incidences_nonempty : Nonempty Incidence
  mean_bad_mass : ∀ inc y, 0 ≤ P.badMass inc y ∧ P.badMass inc y ≤ 1
  average_bad_mass : ∀ inc,
    (∑ y, P.badMass inc y) ≤ Real.exp (-3 * P.cperm * P.n) * Fintype.card Label
  incidence_label_ratio : ∀ g,
    ((permissionIncidences P g).card : ℝ) *
        ((Fintype.card Label : ℝ) / Fintype.card Bin) ≤
      Real.exp (P.cperm * P.n)
  labels_disjoint : ∀ y, (binsContainingLabel P y).card ≤ 1
  incoming_cap : ∀ g D, (qin g).w D ≤ 2 / Fintype.card Bin
  threshold_large : P.n * P.cperm ≥ Real.log 4

/-- L16.2a permission trim. The hypotheses bound bad-mass averages, the
number of incidences per group, overlap of bin labels, and the incoming bin
atoms; the conclusion controls removed-bin and restricted-law mass. -/
theorem permission_loss {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Label Incidence : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [DecidableEq Bin] [Fintype Label] [DecidableEq Label]
    [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence)
    (qin : Group → FinLaw Bin) (hInput : PermissionLossHypotheses P qin) :
    PermissionLossFact P qin := by
  sorry

/-- L16.2b: typical pool probability, both unpinned
and conditional on any one slot image. -/
theorem pool_typicality_concentration_after_permission {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q)
    {Group Label Incidence Slot Bin Hist Check : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Label] [DecidableEq Label]
    [Fintype Incidence] [DecidableEq Incidence]
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check]
    (Perm : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hPerm : PermissionLossFact Perm qin)
    (D : CellPoolDiagnostics Slot Bin Hist Check)
    (hD : PoolConcentrationHypotheses D) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ D.c0 ∧
      D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(D.n : ℝ) ^ c0) ∧
      ∀ s b, (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤
        Real.exp (-(D.n : ℝ) ^ c0) := by
  sorry

/-- L16.2b assembly consumes L16.2a permission loss before applying the pool
concentration step. -/
theorem pool_typicality_concentration {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q)
    {Group Label Incidence Slot Bin Hist Check : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Hist] [Fintype Check]
    (Perm : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hPermission : PermissionLossHypotheses Perm qin)
    (D : CellPoolDiagnostics Slot Bin Hist Check)
    (hD : PoolConcentrationHypotheses D) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ D.c0 ∧
      D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(D.n : ℝ) ^ c0) ∧
      ∀ s b, (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤
        Real.exp (-(D.n : ℝ) ^ c0) := by
  have hPerm := permission_loss hκ Perm qin hPermission
  exact pool_typicality_concentration_after_permission hκ Q H Perm qin hPerm D hD

/-- L16.2c: history load gate at a fixed typical
pool, with its relative conditioning cost for every nonnegative test. -/
theorem history_load_gate_concentration {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q)
    {Slot Bin Hist Check : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] [Fintype Hist] [Fintype Check]
    (D : CellPoolDiagnostics Slot Bin Hist Check)
    (hD : LoadGateHypotheses D) (c0 : ℝ) (hc0 : 0 < c0) :
    ∀ pool, D.typical pool →
      (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) ≤
        Real.exp (-(D.n : ℝ) ^ c0) ∧
      ∀ (F : Hist → ℝ), (∀ h, 0 ≤ F h) →
        ∃ hgate : 0 < ∑ h ∈ Finset.univ.filter (fun h => D.loadGate pool h),
          (D.historyLaw pool).w h,
          (FinLaw.cond (D.historyLaw pool)
            (Finset.univ.filter fun h => D.loadGate pool h) hgate).E F ≤
            (1 - Real.exp (-(D.n : ℝ) ^ c0))⁻¹ *
              (D.historyLaw pool).E F := by
  sorry

/-- L16.2: package the pool estimate and the independent history gate
estimate for one cell. -/
theorem typical_cell_pools {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q)
    {Group Label Incidence Slot Bin Hist Check : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    [Fintype Slot] [DecidableEq Slot]
    [Fintype Hist] [Fintype Check]
    (Perm : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hPermission : PermissionLossHypotheses Perm qin)
    (D : CellPoolDiagnostics Slot Bin Hist Check)
    (hPool : PoolConcentrationHypotheses D) (hGate : LoadGateHypotheses D) :
    ∃ c0 : ℝ, Nonempty (TypicalPoolCertificate D c0) := by
  obtain ⟨c0, hc0, hc0D, hunpinned, hpinned⟩ :=
    pool_typicality_concentration hκ Q H Perm qin hPermission D hPool
  have hGateEst := history_load_gate_concentration hκ Q H D hGate c0 hc0
  refine ⟨c0, ⟨{
    c0_pos := hc0
    typical_probability := ?_
    pinned_probability := ?_
    gate_failure := ?_
    gate_conditioning_cost := ?_ }⟩⟩
  · exact hunpinned
  · intro s b
    exact hpinned s b
  · intro pool htyp
    exact (hGateEst pool htyp).1
  · intro pool htyp hgate F hF
    obtain ⟨hgate', hcost⟩ := (hGateEst pool htyp).2 F hF
    have heq : hgate' = hgate := Subsingleton.elim _ _
    subst hgate'
    exact hcost

def poolContainsLabel {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (P : CellPool G C) (y : Fin (T.S.N k)) : Prop :=
  ∃ slot, y ∈ (P slot).1

/-- L16.6 construction data: the calibrated role mass is factored into a
pool correction and the raw low-profile marginal. The correction bound is
the normalization, permission, and load-gate estimate. -/
structure FreshLabelCalibration {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  permittedLabels : ∀ C, F.Pool C → Pos T k → Finset (Fin (T.S.N k))
  targetMass : ∀ C, F.Pool C → Pos T k → Fin (T.S.N k) → ℝ
  rawMass : Pos T k → Fin (T.S.N k) → ℝ
  poolFactor : ∀ C, F.Pool C → Pos T k → Fin (T.S.N k) → ℝ
  exactMarginal : ∀ C P b, G.cellOf b = C → ¬ IsEvenRole b → ∀ y,
    (F.fresh C P).pr (fun s => F.label C s b = y) = targetMass C P b y
  targetFactorization : ∀ C P b y,
    targetMass C P b y = poolFactor C P b y * rawMass b y
  rawProfile : ∀ b y,
    rawMass b y = (PT.π (G.patchOf b)).w y
  poolFactor_nonneg : ∀ C P b y, 0 ≤ poolFactor C P b y
  poolFactor_bound : ∀ C P b y, F.typical C P →
    poolFactor C P b y ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) / G.nslot C *
          (if poolContainsLabel P y ∧ y ∈ permittedLabels C P b then 1 else 0)

/-- L16.1c: iid cell pools use an independent uniform bin at every slot. -/
noncomputable def iidCellPoolLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (_C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch _C))).Nonempty) :
    FinLaw (CellPool G _C) := by
  classical
  exact FinLaw.pi fun _ : Fin (G.nslot _C) => FinLaw.uniform Finset.univ hBins

/-- L16.6a: derive the pool-restricted calibrated marginal bound from the
normalizer, permission, and load-gate estimates. -/
theorem fresh_singleton_target_bound {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    (_hF : FreshCell.Spec F validState Cal.permittedLabels)
    (C : H.geom.Cell) (P : F.Pool C) (hpool : F.typical C P)
    (b : Pos T k) (y : Fin (T.S.N k)) (i : Fin PT.tiling.m)
    (hcell : H.geom.cellOf b = C) (_hOdd : ¬ IsEvenRole b)
    (hpatch : H.geom.patchOf b = i) :
    Cal.targetMass C P b y ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
  have hCellPatch : H.geom.cellPatch C = i := by
    calc
      H.geom.cellPatch C = H.geom.cellPatch (H.geom.cellOf b) := congrArg _ hcell.symm
      _ = H.geom.patchOf b := H.geom.cellOf_patch b
      _ = i := hpatch
  have hFactor := Cal.poolFactor_bound C P b y hpool
  rw [hCellPatch] at hFactor
  have hRawNonneg : 0 ≤ Cal.rawMass b y := by
    rw [Cal.rawProfile, hpatch]
    exact (PT.π i).nonneg y
  calc
    Cal.targetMass C P b y = Cal.poolFactor C P b y * Cal.rawMass b y :=
      Cal.targetFactorization C P b y
    _ ≤ ((1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) *
        Cal.rawMass b y :=
      mul_le_mul_of_nonneg_right hFactor hRawNonneg
    _ = (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
          rw [Cal.rawProfile, hpatch]
          ring

/-- L16.6b: use exact calibration to identify the fresh output marginal with
the target mass bounded in L16.6a. -/
theorem fresh_singleton_fixed_pool_node {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F) (C : H.geom.Cell)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    (_hF : FreshCell.Spec F validState Cal.permittedLabels)
    (P : F.Pool C) (_hpool : F.typical C P) (b : Pos T k) (y : Fin (T.S.N k))
    (hcell : H.geom.cellOf b = C) (hOdd : ¬ IsEvenRole b)
    (i : Fin PT.tiling.m) (_hpatch : H.geom.patchOf b = i)
    (hTarget : Cal.targetMass C P b y ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) :
    (F.fresh C P).pr (fun s => F.label C s b = y) ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
  rw [Cal.exactMarginal C P b hcell hOdd y]
  exact hTarget

/-- L16.6c: averaging the fixed-pool estimate over iid slots conditioned on
individual typicality costs the stated additional factor. -/
theorem fresh_singleton_iid_pool_node {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    (_hF : FreshCell.Spec F validState Cal.permittedLabels) (C : H.geom.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hTypicalFailure : (iidCellPoolLaw (G := H.geom) C hBins).pr
      (fun P => ¬ F.typical C P) ≤ δ)
    (hδ_small : δ ≤ (T.S.n k : ℝ) ^ (-3 : ℝ))
    (hTypical : 0 < ∑ P ∈ Finset.univ.filter (F.typical C),
      (iidCellPoolLaw (G := H.geom) C hBins).w P)
    (i : Fin PT.tiling.m) (b : Pos T k) (_hpatch : H.geom.patchOf b = i)
    (_hcell : H.geom.cellOf b = C) (_hOdd : ¬ IsEvenRole b)
    (y : Fin (T.S.N k)) :
    (FinLaw.cond (iidCellPoolLaw (G := H.geom) C hBins)
      (Finset.univ.filter (F.typical C)) hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
      (1 + 2 * (T.S.n k : ℝ) ^ (-3 : ℝ)) * (PT.π i).w y := by
  sorry

/-- L16.6: fixed-pool and iid-pool fresh singleton comparisons. -/
theorem fresh_singleton_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    (hF : FreshCell.Spec F validState Cal.permittedLabels) (C : H.geom.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hTypicalFailure : (iidCellPoolLaw (G := H.geom) C hBins).pr
      (fun P => ¬ F.typical C P) ≤ δ)
    (hδ_small : δ ≤ (T.S.n k : ℝ) ^ (-3 : ℝ))
    (hTypical : 0 < ∑ P ∈ Finset.univ.filter (F.typical C),
      (iidCellPoolLaw (G := H.geom) C hBins).w P)
    (i : Fin PT.tiling.m) (b : Pos T k) (hpatch : H.geom.patchOf b = i)
    (hcell : H.geom.cellOf b = C) (hOdd : ¬ IsEvenRole b)
    (y : Fin (T.S.N k)) :
    (∀ P, F.typical C P →
      (F.fresh C P).pr (fun s => F.label C s b = y) ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
          (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
            (PT.π i).w y *
              (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) ∧
    (FinLaw.cond (iidCellPoolLaw (G := H.geom) C hBins)
      (Finset.univ.filter (F.typical C)) hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
      (1 + 2 * (T.S.n k : ℝ) ^ (-3 : ℝ)) * (PT.π i).w y := by
  constructor
  · intro P hP
    have hTarget := fresh_singleton_target_bound hκ Q H Cal hF C P hP b y i hcell hOdd
      hpatch
    exact fresh_singleton_fixed_pool_node hκ Q H Cal C hF P hP b y hcell hOdd i hpatch
      hTarget
  · exact fresh_singleton_iid_pool_node hκ Q H Cal hF C hBins δ hδ hTypicalFailure
      hδ_small hTypical i b hpatch
      hcell hOdd y

/-- L16.7 experiment: compare a nonnegative prior test under typical iid pools
and fresh states with a base finite law on prior vectors. -/
noncomputable def freshPriorTest {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (C : G.Cell) (v : Pos T k)
    (_hcell : G.cellOf v = C) (_hEven : IsEvenRole v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) : ℝ :=
  (iidCellPoolLaw (G := G) C (hBins C)).E fun P => if F.typical C P then
    (F.fresh C P).E (fun s => Φ (F.prior C s v)) else 0

/-- Finite reference experiment on prior vectors; its underlying state type
may be larger than the prior readout range. -/
structure PriorExperiment (N : ℕ) where
  State : Type
  [stateFin : Fintype State]
  law : FinLaw State
  prior : State → Fin N → ℝ

namespace PriorExperiment

variable {N : ℕ}

instance instStateFintype (P : PriorExperiment N) : Fintype P.State := P.stateFin

noncomputable def expect (P : PriorExperiment N) (Φ : (Fin N → ℝ) → ℝ) : ℝ :=
  P.law.E (fun s => Φ (P.prior s))

end PriorExperiment

/-- L16.7a: after role/bin upper comparisons, an arbitrary nonnegative prior
test is bounded by a constant times the unrestricted reference test. -/
theorem fresh_prior_stage_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    {permittedLabels : ∀ C, F.Pool C → Pos T k → Finset (Fin (T.S.N k))}
    (_hF : FreshCell.Spec F validState permittedLabels)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (C : H.geom.Cell)
    (v : Pos T k) (hcell : H.geom.cellOf v = C) (hEven : IsEvenRole v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ)
    (hΦ : ∀ σ, 0 ≤ Φ σ) (hΦ0 : Φ 0 = 0)
    (intermediate : PriorExperiment (T.S.N k)) :
    freshPriorTest F hBins C v hcell hEven Φ ≤
      (10 * κ.Kcell) * PriorExperiment.expect intermediate Φ := by
  sorry

/-- L16.7b: the iid-slot containment and cancellation transfers the remaining
cell comparison to the unrestricted base law. -/
theorem iid_slot_prior_cancellation {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    {permittedLabels : ∀ C, F.Pool C → Pos T k → Finset (Fin (T.S.N k))}
    (_hF : FreshCell.Spec F validState permittedLabels)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (C : H.geom.Cell)
    (v : Pos T k) (_hcell : H.geom.cellOf v = C) (_hEven : IsEvenRole v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ)
    (hΦ : ∀ σ, 0 ≤ Φ σ) (hΦ0 : Φ 0 = 0)
    (intermediate base : PriorExperiment (T.S.N k)) :
    PriorExperiment.expect intermediate Φ ≤
      (10 * (κ.Kp : ℝ)) * PriorExperiment.expect base Φ := by
  sorry

/-- L16.7: fresh internal-prior comparison for every nonnegative test
that vanishes at the zero prior. -/
theorem fresh_internal_prior_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (H : LowGeometryCertificate hκ Q) {F : FreshCell H.geom}
    (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    {permittedLabels : ∀ C, F.Pool C → Pos T k → Finset (Fin (T.S.N k))}
    (hF : FreshCell.Spec F validState permittedLabels)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (C : H.geom.Cell)
    (v : Pos T k) (hcell : H.geom.cellOf v = C) (hEven : IsEvenRole v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ)
    (hΦ : ∀ σ, 0 ≤ Φ σ) (hΦ0 : Φ 0 = 0)
    (intermediate base : PriorExperiment (T.S.N k)) :
    freshPriorTest F hBins C v hcell hEven Φ ≤
      (100 * κ.Kcell * (κ.Kp : ℝ)) * PriorExperiment.expect base Φ := by
  have hStage := fresh_prior_stage_comparison hκ Q H Cal hF hBins C v hcell hEven Φ hΦ hΦ0 intermediate
  have hSlots := iid_slot_prior_cancellation hκ Q H Cal hF hBins C v hcell hEven Φ hΦ hΦ0 intermediate base
  have hKcell : 0 < κ.Kcell := by
    have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
    exact lt_of_lt_of_le (by positivity) hκ.Kcell_big
  calc
    freshPriorTest F hBins C v hcell hEven Φ ≤
      (10 * κ.Kcell) * PriorExperiment.expect intermediate Φ := hStage
    _ ≤ (10 * κ.Kcell) * ((10 * (κ.Kp : ℝ)) * PriorExperiment.expect base Φ) :=
      mul_le_mul_of_nonneg_left hSlots (by positivity)
    _ = (100 * κ.Kcell * (κ.Kp : ℝ)) * PriorExperiment.expect base Φ := by ring

end HypercubeRamsey.S16
