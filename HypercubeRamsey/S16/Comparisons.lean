import HypercubeRamsey.S16.Calibrations
import HypercubeRamsey.S16.Comparisons_q_s16_comp2

/-! Section 16 pool/history estimates and comparisons of the constructed
sampling pipeline. Every reference experiment shares its primitive kernels
and raw prior readout with the fresh sampler. -/

namespace HypercubeRamsey.S16
open Classical
open scoped BigOperators

/-- A fixed exponent is chosen before any cell experiment. Histories here
are the admissible finite slice histories, not arbitrary unsupported data. -/
structure CellPoolDiagnostics (Slot Bin Hist Check : Type*)
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] (n : ℕ) (c0 : ℝ) where
  bins_nonempty : Nonempty Bin
  ε : ℝ
  iidSlotLaw : Slot → FinLaw Bin
  uniform_slots : ∀ s b, (iidSlotLaw s).w b = 1 / (Fintype.card Bin : ℝ)
  normalizer : (Slot → Bin) → Check → ℝ
  center : Check → ℝ
  tolerance : Check → ℝ
  Group : Type
  [groupFin : Fintype Group]
  poolNormalizer : (Slot → Bin) → Group → Hist → ℝ
  internalFailure : (Slot → Bin) → Group → Hist → ℝ
  pinnedInternalFailure : (Slot → Bin) → Group → Hist → ℝ
  checks_cover : ∀ pool, (∀ c, |normalizer pool c - center c| ≤ tolerance c) →
    (∀ g h, |poolNormalizer pool g h / ((Fintype.card Slot : ℝ) / Fintype.card Bin) - 1| ≤
      Real.rpow (n : ℝ) (-4)) ∧
    (∀ g h, internalFailure pool g h ≤ Real.rpow ε (1 / 4 : ℝ)) ∧
    (∀ g h, pinnedInternalFailure pool g h ≤ Real.rpow ε (1 / 4 : ℝ))
  LoadColumn : Type
  [columnFin : Fintype LoadColumn]
  historyLaw : (Slot → Bin) → FinLaw Hist
  loadValue : (Slot → Bin) → Hist → LoadColumn → ℝ
  loadThreshold : ℝ

namespace CellPoolDiagnostics
variable {Slot Bin Hist Check : Type*} [Fintype Slot] [DecidableEq Slot]
variable [Fintype Bin] [DecidableEq Bin] [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}

instance (D : CellPoolDiagnostics Slot Bin Hist Check n c0) : Fintype D.Group := D.groupFin
instance (D : CellPoolDiagnostics Slot Bin Hist Check n c0) : Fintype D.LoadColumn := D.columnFin

noncomputable def poolLaw (D : CellPoolDiagnostics Slot Bin Hist Check n c0) := FinLaw.pi D.iidSlotLaw
/-- An actual iid-slot pin, including pins to any bin (uniform mass is positive). -/
noncomputable def pinLaw (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (s : Slot) (b : Bin) :=
  FinLaw.pi fun t => if t = s then FinLaw.dirac b else D.iidSlotLaw t

def typical (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (pool : Slot → Bin) : Prop :=
  Function.Injective pool ∧ ∀ c, |D.normalizer pool c - D.center c| ≤ D.tolerance c

def loadGate (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (pool : Slot → Bin) (h : Hist) : Prop :=
  ∀ y, D.loadValue pool h y ≤ D.loadThreshold

end CellPoolDiagnostics

/-- Exact bounded-difference variance and union budgets. A zero variance is
handled separately; n^{c0} alone would not pay for the union over checks. -/
structure PoolConcentrationHypotheses {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) where
  n_large : 2 ≤ n
  exponent_pos : 0 < c0
  slots_pos : 0 < Fintype.card Slot
  epsilon_pos : 0 < D.ε ∧ D.ε ≤ 1
  tolerance_pos : ∀ c, 0 < D.tolerance c
  sensitivity : Check → Slot → ℝ
  sensitivity_nonneg : ∀ c s, 0 ≤ sensitivity c s
  mean_close : ∀ c, |D.poolLaw.E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2
  pinned_mean_close : ∀ s b c,
    |(D.pinLaw s b).E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2
  one_slot_change : ∀ c s x y, (∀ t, t ≠ s → x t = y t) →
    |D.normalizer x c - D.normalizer y c| ≤ sensitivity c s
  variance_budget : ∀ c,
    (∑ s, sensitivity c s ^ 2) = 0 ∨
    (0 < ∑ s, sensitivity c s ^ 2) ∧
      (n : ℝ) ^ c0 + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
        2 * (D.tolerance c / 2) ^ 2 / (∑ s, sensitivity c s ^ 2)
  /-- Birthday bound, also after a single slot pin. -/
  collision_budget : (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin ≤
    Real.exp (-(n : ℝ) ^ c0) / 4

/-- Independent slice variables, a pushforward identity for histories, and
an actual sum of bounded nonnegative column contributions. -/
structure LoadGateHypotheses {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) where
  n_large : 2 ≤ n
  exponent_pos : 0 < c0
  Slice : Type
  [sliceFin : Fintype Slice]
  [sliceDec : DecidableEq Slice]
  Value : Slice → Type
  [valueFin : ∀ s, Fintype (Value s)]
  sliceLaw : (Slot → Bin) → ∀ s, FinLaw (Value s)
  encode : (∀ s, Value s) → Hist
  history_eq : ∀ pool, D.historyLaw pool = FinLaw.map (FinLaw.pi (sliceLaw pool)) encode
  contribution : (Slot → Bin) → ∀ s, Value s → D.LoadColumn → ℝ
  range : Slice → ℝ
  range_nonneg : ∀ s, 0 ≤ range s
  contribution_range : ∀ pool s z y, 0 ≤ contribution pool s z y ∧ contribution pool s z y ≤ range s
  load_eq : ∀ pool z y, D.loadValue pool (encode z) y = ∑ s, contribution pool s (z s) y
  threshold_pos : 0 < D.loadThreshold
  mean_small : ∀ pool, D.typical pool → ∀ y,
    (D.historyLaw pool).E (fun h => D.loadValue pool h y) ≤ D.loadThreshold / 2
  variance_budget : (∑ s, range s ^ 2) = 0 ∨
    (0 < ∑ s, range s ^ 2) ∧
      (n : ℝ) ^ c0 + Real.log (max 1 (Fintype.card D.LoadColumn : ℝ)) ≤
        2 * (D.loadThreshold / 2) ^ 2 / (∑ s, range s ^ 2)

structure TypicalPoolCertificate {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) where
  c0_pos : 0 < c0
  typical_probability : D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0)
  pinned_probability : ∀ s b, (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0)
  realized_requirements : ∀ pool, D.typical pool →
    PoolTypical (Finset.univ.image pool) Finset.univ pool n D.ε
      (D.poolNormalizer pool) (D.internalFailure pool) (D.pinnedInternalFailure pool)
  gate_failure : ∀ pool, D.typical pool →
    (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) ≤ Real.exp (-(n : ℝ) ^ c0)
  gate_conditioning_cost : ∀ pool (_hpool : D.typical pool)
    (hgate : 0 < ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h)
    (F : Hist → ℝ), (∀ h, 0 ≤ F h) →
    (FinLaw.cond (D.historyLaw pool) (Finset.univ.filter (D.loadGate pool)) hgate).E F ≤
      (1 - Real.exp (-(n : ℝ) ^ c0))⁻¹ * (D.historyLaw pool).E F

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
bound, few incidences per group, disjoint bin labels, and subexponential
inflation of the internally pretrimmed solver atoms (T16:147–156). -/
structure PermissionLossHypotheses {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin) : Prop where
  bins_nonempty : Nonempty Bin
  labels_nonempty : Nonempty Label
  mean_bad_mass : ∀ inc y, 0 ≤ P.badMass inc y ∧ P.badMass inc y ≤ 1
  average_bad_mass : ∀ inc,
    (∑ y, P.badMass inc y) ≤ Real.exp (-3 * P.cperm * P.n) * Fintype.card Label
  incidence_label_ratio : ∀ g,
    ((permissionIncidences P g).card : ℝ) *
        ((Fintype.card Label : ℝ) / Fintype.card Bin) ≤
      Real.exp (P.cperm * P.n)
  labels_disjoint : ∀ y, (binsContainingLabel P y).card ≤ 1
  incoming_cap : ∀ g D, (qin g).w D ≤
    Real.exp (P.cperm * P.n / 2) / Fintype.card Bin
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

/-- L16.2b: independent-slot concentration, including a genuine iid pin.
Permission and geometry assumptions belong to the producer of the diagnostic
means/sensitivities; they are not unused arguments of this analytic lemma. -/
theorem pool_typicality_concentration_after_permission {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (hD : PoolConcentrationHypotheses D) :
    D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0) / 2 ∧
    ∀ s b, (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0) / 2 := by
  sorry

/-- Diagnostic realization supplies the concrete Part C typicality predicate. -/
theorem pool_requirements_realized {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) :
    ∀ pool, D.typical pool →
      PoolTypical (Finset.univ.image pool) Finset.univ pool n D.ε
        (D.poolNormalizer pool) (D.internalFailure pool) (D.pinnedInternalFailure pool) := by
  sorry

/-- L16.2c: concentration of actual independent slice contributions, using
this same fixed exponent and the label union budget. -/
theorem history_load_gate_concentration {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (hD : LoadGateHypotheses D) :
    ∀ pool, D.typical pool →
      (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) ≤ Real.exp (-(n : ℝ) ^ c0) ∧
      ∀ (F : Hist → ℝ), (∀ h, 0 ≤ F h) →
        ∃ hgate : 0 < ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h,
          (FinLaw.cond (D.historyLaw pool) (Finset.univ.filter (D.loadGate pool)) hgate).E F ≤
            (1 - Real.exp (-(n : ℝ) ^ c0))⁻¹ * (D.historyLaw pool).E F := by
  sorry

/-- The analytic iid certificate plus actual permutation-pool conclusions.
The pin remains in the global pool experiment, even when it is in another cell. -/
structure GeometryTypicalPoolCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hκ : κ.Admissible} {K16 : ℝ}
    {Q : LowModeQuantFacts hκ (PT := PT) K16} (H : LowGeometryCertificate hκ Q)
    (C : H.geom.Cell) {Hist Check : Type*} [Fintype Hist] [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C)) Hist Check (T.S.n k) c0) where
  iid : TypicalPoolCertificate D
  permutation_probability : (permPoolLaw H.geom H.perm_pool_nonempty).pr
    (fun P => ¬ D.typical (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0)
  global_pinned_probability : ∀ (s : CellSlot H.geom) (b : Bin PT.tiling (H.geom.cellPatch s.1))
    (hpin : 0 < ∑ P ∈ poolPinEvent s b, (permPoolLaw H.geom H.perm_pool_nonempty).w P),
    (FinLaw.cond (permPoolLaw H.geom H.perm_pool_nonempty) (poolPinEvent s b) hpin).pr
      (fun P => ¬ D.typical (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0)

/-- L16.1's small-scope comparison transfers a half-budget iid tail to the
actual pools, keeping any one global slot pin in both laws. -/
theorem pool_typicality_permutation_transfer {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (C : H.geom.Cell) {Hist Check : Type*} [Fintype Hist] [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C)) Hist Check (T.S.n k) c0)
    (hu : D.poolLaw.pr (fun P => ¬ D.typical P) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) / 2)
    (hp : ∀ s b, (D.pinLaw s b).pr (fun P => ¬ D.typical P) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) / 2) :
    (permPoolLaw H.geom H.perm_pool_nonempty).pr (fun P => ¬ D.typical (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) ∧
    ∀ (s : CellSlot H.geom) (b : Bin PT.tiling (H.geom.cellPatch s.1))
      (hpin : 0 < ∑ P ∈ poolPinEvent s b, (permPoolLaw H.geom H.perm_pool_nonempty).w P),
      (FinLaw.cond (permPoolLaw H.geom H.perm_pool_nonempty) (poolPinEvent s b) hpin).pr
        (fun P => ¬ D.typical (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
  sorry

/-- L16.2 fixes c0 before cells, links n and slot/bin types to the actual
geometry, and returns permission, iid, permutation, and history estimates. -/
theorem typical_cell_pools {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (C : H.geom.Cell) {Group Label Incidence Hist Check : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Label] [DecidableEq Label]
    [Fintype Incidence] [DecidableEq Incidence] [Fintype Hist] [Fintype Check] {c0 : ℝ}
    (Perm : PermissionTable Group (Bin PT.tiling (H.geom.cellPatch C)) Label Incidence)
    (qin : Group → FinLaw (Bin PT.tiling (H.geom.cellPatch C)))
    (hPermission : PermissionLossHypotheses Perm qin)
    (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C)) Hist Check (T.S.n k) c0)
    (hPool : PoolConcentrationHypotheses D) (hGate : LoadGateHypotheses D) :
    PermissionLossFact Perm qin ∧ Nonempty (GeometryTypicalPoolCertificate H C D) := by
  have hPerm := permission_loss hκ Perm qin hPermission
  obtain ⟨hu, hp⟩ := pool_typicality_concentration_after_permission D hPool
  obtain ⟨hperm, hpin⟩ := pool_typicality_permutation_transfer hκ Q H C D hu hp
  have hg := history_load_gate_concentration D hGate
  have iid : TypicalPoolCertificate D := {
    c0_pos := hPool.exponent_pos
    typical_probability := hu.trans (by linarith [Real.exp_pos (-(T.S.n k : ℝ) ^ c0)])
    pinned_probability := fun s b => (hp s b).trans (by linarith [Real.exp_pos (-(T.S.n k : ℝ) ^ c0)])
    realized_requirements := pool_requirements_realized D
    gate_failure := fun pool ht => (hg pool ht).1
    gate_conditioning_cost := by
      intro pool ht hgate F hF
      obtain ⟨hgate', hcost⟩ := (hg pool ht).2 F hF
      have heq : hgate' = hgate := Subsingleton.elim _ _
      subst hgate'
      exact hcost }
  exact ⟨hPerm, ⟨⟨iid, hperm, hpin⟩⟩⟩

def poolContainsLabel {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (P : CellPool G C) (y : Fin (T.S.N k)) : Prop :=
  ∃ slot, y ∈ (P slot).1

/-- Odd output coordinates of a cell. -/
abbrev OddCellRole {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) :=
  {b : Pos T k // G.cellOf b = C ∧ ¬ IsEvenRole b}

/-- Concrete bin and label stages, with the conditional marginals supplied
by P16.3/P16.4. The fresh state is the pushforward of these stages; raw
profile, permission, pool normalizer, and load-gate inputs remain primitive.
There is no assumed singleton upper bound or pool correction factor. -/
structure FreshLabelCalibration {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  Hist : G.Cell → Type
  [histFin : ∀ C, Fintype (Hist C)]
  [histDec : ∀ C, DecidableEq (Hist C)]
  Group : G.Cell → Type
  [groupFin : ∀ C, Fintype (Group C)]
  [groupDec : ∀ C, DecidableEq (Group C)]
  groupOf : ∀ C, OddCellRole G C → Group C
  history : ∀ C, FinLaw (Hist C)
  gatedHistory : ∀ C, F.Pool C → FinLaw (Hist C)
  gate : ∀ C, F.Pool C → Finset (Hist C)
  gate_pos : ∀ C P, F.typical C P → 0 < ∑ W ∈ gate C P, (history C).w W
  gated_eq : ∀ C P (ht : F.typical C P),
    gatedHistory C P = FinLaw.cond (history C) (gate C P) (gate_pos C P ht)
  qin : ∀ C, Hist C → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  U : ∀ C, Hist C → Group C → Bin PT.tiling (G.cellPatch C) → FinLaw (Fin (T.S.N k))
  U_support : ∀ C W g D y, (U C W g D).w y ≠ 0 → y ∈ D.1
  permitted : ∀ C, Group C → Finset (Bin PT.tiling (G.cellPatch C))
  qtilde : ∀ C, F.Pool C → Hist C → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  /-- Exactly the two successive restrictions of T16:150–174. -/
  qtilde_eq : ∀ C P W g D, F.typical C P → (history C).w W ≠ 0 →
    (qtilde C P W g).w D =
      (if D ∈ permitted C g ∧ D ∈ Finset.univ.image P then (qin C W g).w D else 0) /
      (∑ D' ∈ ((permitted C g) ∩ (Finset.univ.image P)), (qin C W g).w D')
  binSampler : ∀ C, F.Pool C → Hist C → FinLaw (Group C → Bin PT.tiling (G.cellPatch C))
  labelSampler : ∀ C, F.Pool C → Hist C →
    (Group C → Bin PT.tiling (G.cellPatch C)) → FinLaw (OddCellRole G C → Fin (T.S.N k))
  bin_marginals : ∀ C P W g D, F.typical C P → (gatedHistory C P).w W ≠ 0 →
    (binSampler C P W).pr (fun a => a g = D) = (qtilde C P W g).w D
  label_marginals : ∀ C P W a r y, F.typical C P → (gatedHistory C P).w W ≠ 0 →
    (binSampler C P W).w a ≠ 0 →
    (labelSampler C P W a).pr (fun ys => ys r = y) = (U C W (groupOf C r) (a (groupOf C r))).w y
  encode : ∀ C, Hist C × ((Group C → Bin PT.tiling (G.cellPatch C)) ×
    (OddCellRole G C → Fin (T.S.N k))) → F.State C
  fresh_eq : ∀ C P, F.typical C P → F.fresh C P =
    FinLaw.map (FinLaw.bind (gatedHistory C P) fun W =>
      FinLaw.bind (binSampler C P W) (labelSampler C P W)) (encode C)
  /-- Invalid encodings may use the injective fallback state. Readout is
  required only on inputs actually charged by the sampling stages. -/
  label_eq : ∀ C P W a ys r, F.typical C P → (gatedHistory C P).w W ≠ 0 →
    (binSampler C P W).w a ≠ 0 → (labelSampler C P W a).w ys ≠ 0 →
    F.label C (encode C (W, a, ys)) r.1 = ys r
  raw_profile : ∀ C (r : OddCellRole G C) y,
    (history C).E (fun W => ∑ D, (qin C W (groupOf C r)).w D *
      (U C W (groupOf C r) D).w y) = (PT.π (G.cellPatch C)).w y
  δperm : ℝ
  δgate : ℝ
  perm_range : 0 ≤ δperm ∧ δperm < 1
  gate_range : 0 ≤ δgate ∧ δgate < 1
  permission_mass : ∀ C W g, (history C).w W ≠ 0 →
    1 - δperm ≤ ∑ D ∈ permitted C g, (qin C W g).w D
  pool_normalizer : ∀ C P W g, F.typical C P → (history C).w W ≠ 0 →
    ((G.nslot C : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C))) *
      (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
      (∑ D ∈ ((permitted C g) ∩ (Finset.univ.image P)), (qin C W g).w D) /
        (∑ D ∈ permitted C g, (qin C W g).w D)
  gate_mass : ∀ C P, F.typical C P → 1 - δgate ≤ ∑ W ∈ gate C P, (history C).w W
  slot_pos : ∀ C, 0 < G.nslot C
  /-- Explicit scalar slack for the three denominators; no output probability. -/
  cost_budget : (1 - δgate)⁻¹ * (1 - δperm)⁻¹ *
    (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ)

namespace FreshLabelCalibration
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
variable {G : LowGeom PT} {F : FreshCell G}
instance (Cal : FreshLabelCalibration F) : ∀ C, Fintype (Cal.Hist C) := Cal.histFin
instance (Cal : FreshLabelCalibration F) : ∀ C, DecidableEq (Cal.Hist C) := Cal.histDec
instance (Cal : FreshLabelCalibration F) : ∀ C, Fintype (Cal.Group C) := Cal.groupFin
instance (Cal : FreshLabelCalibration F) : ∀ C, DecidableEq (Cal.Group C) := Cal.groupDec

noncomputable def permittedLabels (Cal : FreshLabelCalibration F) (C : G.Cell)
    (_P : F.Pool C) (b : Pos T k) : Finset (Fin (T.S.N k)) :=
  if hb : G.cellOf b = C ∧ ¬ IsEvenRole b then
    (Cal.permitted C (Cal.groupOf C ⟨b, hb⟩)).biUnion fun D => D.1 else ∅

noncomputable def targetMass (Cal : FreshLabelCalibration F) (C : G.Cell)
    (P : F.Pool C) (b : Pos T k) (y : Fin (T.S.N k)) : ℝ :=
  if hb : G.cellOf b = C ∧ ¬ IsEvenRole b then
    (Cal.gatedHistory C P).E fun W => ∑ D,
      (Cal.qtilde C P W (Cal.groupOf C ⟨b, hb⟩)).w D *
        (Cal.U C W (Cal.groupOf C ⟨b, hb⟩) D).w y else 0
end FreshLabelCalibration

/-- Exact calibration is derived from the bin/label stage identities. -/
theorem fresh_calibration_exact_marginal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (Cal : FreshLabelCalibration F) (C : G.Cell) (P : F.Pool C)
    (ht : F.typical C P) (b : Pos T k) (hb : G.cellOf b = C) (ho : ¬ IsEvenRole b) (y : Fin (T.S.N k)) :
    (F.fresh C P).pr (fun s => F.label C s b = y) = Cal.targetMass C P b y := by
  sorry

/-- L16.1c: iid cell pools use an independent uniform bin at every slot. -/
noncomputable def iidCellPoolLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (_C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch _C))).Nonempty) :
    FinLaw (CellPool G _C) := by
  classical
  exact FinLaw.pi fun _ : Fin (G.nslot _C) => FinLaw.uniform Finset.univ hBins

/-- L16.6a: the actual restriction denominators and load gate bound the
history-averaged target; the low profile identity then supplies π_i. -/
theorem fresh_singleton_target_bound {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (Cal : FreshLabelCalibration F)
    (C : H.geom.Cell) (P : F.Pool C) (hpool : F.typical C P)
    (b : Pos T k) (y : Fin (T.S.N k)) (i : Fin PT.tiling.m)
    (hcell : H.geom.cellOf b = C) (hOdd : ¬ IsEvenRole b) (hpatch : H.geom.patchOf b = i) :
    Cal.targetMass C P b y ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
        (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C * (PT.π i).w y *
          (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
  classical
  let BinType := Bin PT.tiling (H.geom.cellPatch C)
  let Role := OddCellRole H.geom C
  let role : Role := ⟨b, hcell, hOdd⟩
  let g := Cal.groupOf C role
  let A : Finset BinType := Cal.permitted C g ∩ Finset.univ.image P
  let eps4 : ℝ := (T.S.n k : ℝ) ^ (-4 : ℝ)
  let dp : ℝ := Cal.δperm
  let dg : ℝ := Cal.δgate
  let B : ℝ := Fintype.card BinType
  let L : ℝ := H.geom.nslot C
  let permMass (W : Cal.Hist C) : ℝ :=
    ∑ D ∈ Cal.permitted C g, (Cal.qin C W g).w D
  let poolMass (W : Cal.Hist C) : ℝ :=
    ∑ D ∈ A, (Cal.qin C W g).w D
  let rawMass (W : Cal.Hist C) : ℝ :=
    ∑ D, (Cal.qin C W g).w D * (Cal.U C W g D).w y
  let gatedMass (W : Cal.Hist C) : ℝ :=
    ∑ D, (Cal.qtilde C P W g).w D * (Cal.U C W g D).w y
  let lower (W : Cal.Hist C) : ℝ :=
    (L / B) * (1 - eps4) * (1 - dp)
  let other : ℝ := (B / L) * (1 - eps4)⁻¹ * (1 - dp)⁻¹
  let gateMass : ℝ := ∑ W ∈ Cal.gate C P, (Cal.history C).w W
  let gateLaw : FinLaw (Cal.Hist C) := Cal.gatedHistory C P
  have hpatchCell : H.geom.cellPatch C = i := by
    calc
      H.geom.cellPatch C = H.geom.cellPatch (H.geom.cellOf b) :=
        congrArg H.geom.cellPatch hcell.symm
      _ = H.geom.patchOf b := H.geom.cellOf_patch b
      _ = i := hpatch
  have hBinNonempty : Nonempty BinType := by
    obtain ⟨_, hY⟩ := Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)
    obtain ⟨z, hz⟩ := hY
    obtain ⟨D, hD, _⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.exists_mem hz
    exact ⟨⟨D, hD⟩⟩
  have hBinUniv : (Finset.univ : Finset BinType).Nonempty := by
    rcases hBinNonempty with ⟨D⟩
    exact ⟨D, Finset.mem_univ _⟩
  have hB : 0 < B := by
    dsimp [B, BinType]
    exact_mod_cast Finset.card_pos.mpr hBinUniv
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast Cal.slot_pos C
  have hLne : L ≠ 0 := ne_of_gt hL
  have hBne : B ≠ 0 := ne_of_gt hB
  have hdp0 : 0 ≤ dp := Cal.perm_range.1
  have hdp1 : dp < 1 := Cal.perm_range.2
  have hdg0 : 0 ≤ dg := Cal.gate_range.1
  have hdg1 : dg < 1 := Cal.gate_range.2
  have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
  have heps : eps4 ≤ 1 / 16 := by
    have hpow : (T.S.n k : ℝ) ^ (-4 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hnR (by norm_num)
    have htwo : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
    simpa [eps4, htwo] using hpow
  have heps0 : 0 ≤ eps4 := by dsimp [eps4]; positivity
  have heps1 : eps4 < 1 := by linarith [heps]
  have hfactorNonneg : 0 ≤ (L / B) * (1 - eps4) := by positivity
  have hlowerPos (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      0 < lower W := by
    dsimp [lower]
    positivity
  have hPermLower (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      1 - dp ≤ permMass W := by
    simpa [dp, permMass] using Cal.permission_mass C W g hHist
  have hPermPos (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      0 < permMass W := by
    have h := hPermLower W hHist
    dsimp [permMass]
    linarith [hdp1]
  have hPoolNorm (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      (L / B) * (1 - eps4) ≤ poolMass W / permMass W := by
    simpa [L, B, eps4, A, poolMass] using Cal.pool_normalizer C P W g hpool hHist
  have hPoolLower (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      lower W ≤ poolMass W := by
    have hmul := (le_div_iff₀ (hPermPos W hHist)).mp (hPoolNorm W hHist)
    have hperm := hPermLower W hHist
    calc
      lower W = (L / B) * (1 - eps4) * (1 - dp) := by rfl
      _ ≤ (L / B) * (1 - eps4) * permMass W :=
        mul_le_mul_of_nonneg_left hperm hfactorNonneg
      _ ≤ poolMass W := hmul
  have hPoolPos (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      0 < poolMass W := lt_of_lt_of_le (hlowerPos W hHist) (hPoolLower W hHist)
  have hLowerInv (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
      (poolMass W)⁻¹ ≤ (lower W)⁻¹ :=
    (inv_le_inv₀ (hPoolPos W hHist) (hlowerPos W hHist)).2 (hPoolLower W hHist)
  have hLowerInvEq (W : Cal.Hist C) : (lower W)⁻¹ = other := by
    dsimp [lower, other]
    field_simp [hLne, hBne, ne_of_gt (by linarith [heps, hdp1] : 0 < 1 - eps4),
      ne_of_gt (by linarith [hdp1] : 0 < 1 - dp)]
    <;> ring
  have hLabels : Cal.permittedLabels C P b =
      (Cal.permitted C g).biUnion fun D => D.1 := by
    simp [FreshLabelCalibration.permittedLabels, hcell, hOdd, role, g]
  have hTargetEq : Cal.targetMass C P b y = gateLaw.E gatedMass := by
    simp [FreshLabelCalibration.targetMass, hcell, hOdd, role, g, gateLaw, gatedMass]
  have hGateEq : gateLaw =
      FinLaw.cond (Cal.history C) (Cal.gate C P) (Cal.gate_pos C P hpool) :=
    Cal.gated_eq C P hpool
  have hHistorySupport (W : Cal.Hist C) (hGate : gateLaw.w W ≠ 0) :
      (Cal.history C).w W ≠ 0 := by
    rw [hGateEq] at hGate
    by_contra hzero
    simp [FinLaw.cond, hzero] at hGate
  have hQtildeSupport (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0)
      (D : BinType) (hq : (Cal.qtilde C P W g).w D ≠ 0) :
      D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image P := by
    by_cases hD : D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image P
    · exact hD
    · have hnot' : ¬ (D ∈ Cal.permitted C g ∧ ∃ s, P s = D) := by
        simpa [Finset.mem_image] using hD
      have hzero : (Cal.qtilde C P W g).w D = 0 := by
        rw [Cal.qtilde_eq C P W g D hpool hHist]
        simp [hnot']
      exact (hq hzero).elim
  by_cases hIndicator : poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b
  · have hqFormula (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0)
        (D : BinType) :
        (Cal.qtilde C P W g).w D =
          (if D ∈ A then (Cal.qin C W g).w D else 0) / poolMass W := by
      rw [Cal.qtilde_eq C P W g D hpool hHist]
      simp [A, poolMass, Finset.mem_image] <;> rfl
    have hsum (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
        gatedMass W =
          (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) / poolMass W := by
      unfold gatedMass
      calc
        (∑ D, (Cal.qtilde C P W g).w D * (Cal.U C W g D).w y) =
            ∑ D, (if D ∈ A then (Cal.qin C W g).w D / poolMass W else 0) *
              (Cal.U C W g D).w y := by
                apply Finset.sum_congr rfl
                intro D hD
                rw [hqFormula W hHist D]
                by_cases hD' : D ∈ A <;> simp [hD']
        _ = ∑ D ∈ A, ((Cal.qin C W g).w D / poolMass W) *
              (Cal.U C W g D).w y := by
                calc
                  (∑ D, (if D ∈ A then (Cal.qin C W g).w D / poolMass W else 0) *
                      (Cal.U C W g D).w y) =
                    ∑ D, if D ∈ A then
                      (Cal.qin C W g).w D / poolMass W * (Cal.U C W g D).w y else 0 := by
                        apply Finset.sum_congr rfl
                        intro D hD
                        by_cases hA : D ∈ A <;> simp [hA]
                  _ = ∑ D ∈ A, (Cal.qin C W g).w D / poolMass W *
                        (Cal.U C W g D).w y := by
                          rw [Finset.sum_ite_mem_eq]
        _ = (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) /
              poolMass W := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro D hD
                ring
    have hnumNonneg (W : Cal.Hist C) :
        0 ≤ ∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y :=
      Finset.sum_nonneg fun D hD => mul_nonneg
        ((Cal.qin C W g).nonneg D) ((Cal.U C W g D).nonneg y)
    have hRawMassNonneg (W : Cal.Hist C) : 0 ≤ rawMass W := by
      unfold rawMass
      exact Finset.sum_nonneg fun D hD => mul_nonneg
        ((Cal.qin C W g).nonneg D) ((Cal.U C W g D).nonneg y)
    have hnumLe (W : Cal.Hist C) :
        (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) ≤ rawMass W := by
      unfold rawMass
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by
        intro D hD hnot
        exact mul_nonneg ((Cal.qin C W g).nonneg D) ((Cal.U C W g D).nonneg y))
    have hTargetW (W : Cal.Hist C) (hHist : (Cal.history C).w W ≠ 0) :
        gatedMass W ≤ other * rawMass W := by
      rw [hsum W hHist]
      calc
        (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) / poolMass W =
            (poolMass W)⁻¹ *
              (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) := by
                rw [div_eq_mul_inv, mul_comm]
        _ ≤ (lower W)⁻¹ * rawMass W := by
              calc
                (poolMass W)⁻¹ *
                    (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) ≤
                  (lower W)⁻¹ *
                    (∑ D ∈ A, (Cal.qin C W g).w D * (Cal.U C W g D).w y) :=
                    mul_le_mul_of_nonneg_right (hLowerInv W hHist) (hnumNonneg W)
                _ ≤ (lower W)⁻¹ * rawMass W :=
                    mul_le_mul_of_nonneg_left (hnumLe W)
                      (inv_nonneg.mpr (hlowerPos W hHist).le)
        _ = other * rawMass W := by rw [hLowerInvEq W]
    have hGateCompare : gateLaw.E gatedMass ≤ other * gateLaw.E rawMass := by
      unfold FinLaw.E
      calc
        (∑ W, gateLaw.w W * gatedMass W) ≤
            ∑ W, gateLaw.w W * (other * rawMass W) := by
              apply Finset.sum_le_sum
              intro W hW
              by_cases hGate : gateLaw.w W = 0
              · simp [hGate]
              · exact mul_le_mul_of_nonneg_left (hTargetW W (hHistorySupport W hGate))
                  (gateLaw.nonneg W)
        _ = other * ∑ W, gateLaw.w W * rawMass W := by
              calc
                (∑ W, gateLaw.w W * (other * rawMass W)) =
                    ∑ W, other * (gateLaw.w W * rawMass W) := by
                      apply Finset.sum_congr rfl
                      intro W hW
                      ring
                _ = other * ∑ W, gateLaw.w W * rawMass W := by rw [Finset.mul_sum]
    have hGateCompare' :
        (FinLaw.cond (Cal.history C) (Cal.gate C P) (Cal.gate_pos C P hpool)).E gatedMass ≤
          other * (FinLaw.cond (Cal.history C) (Cal.gate C P)
            (Cal.gate_pos C P hpool)).E rawMass := by
      have hh := hGateCompare
      rw [hGateEq] at hh
      exact hh
    have hGateLower : 1 - dg ≤ gateMass := by
      simpa [dg, gateMass] using Cal.gate_mass C P hpool
    have hGatePos : 0 < gateMass := Cal.gate_pos C P hpool
    have hGateLowerPos : 0 < 1 - dg := by linarith [hdg1]
    have hGateInv : gateMass⁻¹ ≤ (1 - dg)⁻¹ :=
      (inv_le_inv₀ hGatePos hGateLowerPos).2 hGateLower
    have hRawE : 0 ≤ (Cal.history C).E rawMass := by
      unfold FinLaw.E
      exact Finset.sum_nonneg fun W hW =>
        mul_nonneg ((Cal.history C).nonneg W) (hRawMassNonneg W)
    have hGateCond :
        (FinLaw.cond (Cal.history C) (Cal.gate C P) (Cal.gate_pos C P hpool)).E rawMass ≤
          (1 - dg)⁻¹ * (Cal.history C).E rawMass := by
      let gatePos := Cal.gate_pos C P hpool
      let gateSet := Cal.gate C P
      let gm := ∑ W ∈ gateSet, (Cal.history C).w W
      have hnum : (∑ W ∈ gateSet, (Cal.history C).w W * rawMass W) ≤
          (Cal.history C).E rawMass := by
        unfold FinLaw.E
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intro W hW hnot
          exact mul_nonneg ((Cal.history C).nonneg W) (hRawMassNonneg W))
      have hform : (FinLaw.cond (Cal.history C) gateSet gatePos).E rawMass =
          (∑ W ∈ gateSet, (Cal.history C).w W * rawMass W) / gm := by
        simp [FinLaw.E, FinLaw.cond, gateSet, gm, Finset.sum_div, Finset.sum_ite_mem,
          Finset.univ_inter, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        rw [Finset.mul_sum]
      have hgmpos : 0 < gm := by simpa [gm, gateSet, gatePos] using gatePos
      have hgmLower : 1 - dg ≤ gm := by simpa [gm, gateSet, dg] using hGateLower
      have hgmInv : gm⁻¹ ≤ (1 - dg)⁻¹ := by
        exact (inv_le_inv₀ hgmpos hGateLowerPos).2 hgmLower
      rw [hform]
      calc
        (∑ W ∈ gateSet, (Cal.history C).w W * rawMass W) / gm ≤
            gm⁻¹ * (Cal.history C).E rawMass := by
              rw [div_eq_mul_inv, mul_comm]
              exact mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hgmpos.le)
        _ ≤ (1 - dg)⁻¹ * (Cal.history C).E rawMass :=
              mul_le_mul_of_nonneg_right hgmInv hRawE
    have hpiEq : PT.π (H.geom.cellPatch C) = PT.π i := congrArg PT.π hpatchCell
    have hProfile : (Cal.history C).E rawMass = (PT.π i).w y := by
      have h := Cal.raw_profile C role y
      rw [hpiEq] at h
      simpa [rawMass] using h
    have hpi : 0 ≤ (PT.π i).w y := (PT.π i).nonneg y
    have hCost :
        (1 - dg)⁻¹ * (1 - dp)⁻¹ * (1 - eps4)⁻¹ ≤ 1 +
          (T.S.n k : ℝ) ^ (-3 : ℝ) := by
      simpa [dg, dp, eps4] using Cal.cost_budget
    have hOtherGate : other * (1 - dg)⁻¹ =
        (B / L) * ((1 - dg)⁻¹ * (1 - dp)⁻¹ * (1 - eps4)⁻¹) := by
      dsimp [other]
      ring
    have hOtherNonneg : 0 ≤ other := by dsimp [other]; positivity
    have hcardB : B = (Fintype.card (Bin PT.tiling i) : ℝ) := by
      dsimp [B, BinType]
      rw [hpatchCell]
    have hCoefficient :
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) * (PT.π i).w y =
          (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
            (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C * (PT.π i).w y := by
      rw [hcardB]
      dsimp [L]
      ring
    have hCoeffFinal : other * (1 - dg)⁻¹ ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) := by
      rw [hOtherGate]
      calc
        (B / L) * ((1 - dg)⁻¹ * (1 - dp)⁻¹ * (1 - eps4)⁻¹) ≤
            (B / L) * (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hCost (div_nonneg hB.le hL.le)
        _ = (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) := by ring
    have hPosInner : Cal.targetMass C P b y ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) * (PT.π i).w y := by
      rw [hTargetEq, hGateEq]
      calc
        (FinLaw.cond (Cal.history C) (Cal.gate C P) (Cal.gate_pos C P hpool)).E gatedMass ≤
            other * (FinLaw.cond (Cal.history C) (Cal.gate C P)
              (Cal.gate_pos C P hpool)).E rawMass := by
                exact hGateCompare'
        _ ≤ other * (1 - dg)⁻¹ * (Cal.history C).E rawMass := by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left hGateCond hOtherNonneg
        _ ≤ (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) * (PT.π i).w y := by
              rw [hProfile]
              exact mul_le_mul_of_nonneg_right hCoeffFinal hpi
    calc
      Cal.targetMass C P b y ≤
          (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (B / L) * (PT.π i).w y := hPosInner
      _ = (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
          (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C * (PT.π i).w y := by
            exact hCoefficient
      _ = (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) *
          (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C * (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
              simp [hIndicator]
  · have hZeroTarget : Cal.targetMass C P b y = 0 := by
      rw [hTargetEq]
      unfold FinLaw.E
      apply Finset.sum_eq_zero
      intro W hW
      by_cases hGate : gateLaw.w W = 0
      · simp [hGate]
      · have hHist := hHistorySupport W hGate
        have hZeroInner : gatedMass W = 0 := by
          unfold gatedMass
          apply Finset.sum_eq_zero
          intro D hD
          by_cases hq : (Cal.qtilde C P W g).w D = 0
          · simp [hq]
          · by_cases hu : (Cal.U C W g D).w y = 0
            · simp [hu]
            · have hSupport := Cal.U_support C W g D y hu
              have hqSupport := hQtildeSupport W hHist D hq
              have hnot := not_and_or.mp hIndicator
              rcases hnot with hnotHit | hnotPerm
              · rcases Finset.mem_image.mp hqSupport.2 with ⟨s, hs, heq⟩
                have hval : (P s).1 = D.1 := congrArg Subtype.val heq
                apply False.elim (hnotHit ⟨s, by rw [hval]; exact hSupport⟩)
              · have hyPerm : y ∈ Cal.permittedLabels C P b := by
                  rw [hLabels]
                  exact Finset.mem_biUnion.mpr ⟨D, hqSupport.1, hSupport⟩
                exact False.elim (hnotPerm hyPerm)
        simp [hZeroInner]
    simp [hZeroTarget, hIndicator]

/-- L16.6b: assembly from the two calibrated stages and the denominator estimate. -/
theorem fresh_singleton_fixed_pool_node {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (Cal : FreshLabelCalibration F)
    (C : H.geom.Cell) (P : F.Pool C) (ht : F.typical C P)
    (b : Pos T k) (y : Fin (T.S.N k)) (i : Fin PT.tiling.m)
    (hb : H.geom.cellOf b = C) (ho : ¬ IsEvenRole b)
    (hTarget : Cal.targetMass C P b y ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (Fintype.card (Bin PT.tiling i) : ℝ) /
        H.geom.nslot C * (PT.π i).w y *
          (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) :
    (F.fresh C P).pr (fun s => F.label C s b = y) ≤
      (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (Fintype.card (Bin PT.tiling i) : ℝ) /
        H.geom.nslot C * (PT.π i).w y *
          (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
  rw [fresh_calibration_exact_marginal Cal C P ht b hb ho y]
  exact hTarget

/-- L16.6c: genuine iid containment and conditioning, with quantitative slack. -/
theorem fresh_singleton_iid_pool_node {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (Cal : FreshLabelCalibration F) (C : H.geom.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hTypicalFailure : (iidCellPoolLaw (G := H.geom) C hBins).pr (fun P => ¬ F.typical C P) ≤ δ)
    (hδ_small : δ ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) / 2)
    (hTypical : 0 < ∑ P ∈ Finset.univ.filter (F.typical C), (iidCellPoolLaw (G := H.geom) C hBins).w P)
    (i : Fin PT.tiling.m) (b : Pos T k) (hpatch : H.geom.patchOf b = i)
    (hcell : H.geom.cellOf b = C) (hOdd : ¬ IsEvenRole b) (y : Fin (T.S.N k))
    (hFixed : ∀ P, F.typical C P →
      (F.fresh C P).pr (fun s => F.label C s b = y) ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (Fintype.card (Bin PT.tiling i) : ℝ) /
          H.geom.nslot C * (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) :
    (FinLaw.cond (iidCellPoolLaw (G := H.geom) C hBins)
      (Finset.univ.filter (F.typical C)) hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
      (1 + 2 * (T.S.n k : ℝ) ^ (-3 : ℝ)) * (PT.π i).w y := by
  classical
  let BinType := Bin PT.tiling (H.geom.cellPatch C)
  let Slot := Fin (H.geom.nslot C)
  let PoolLaw := iidCellPoolLaw (G := H.geom) C hBins
  let TypicalSet := Finset.univ.filter (F.typical C)
  let Mass : ℝ := ∑ P ∈ TypicalSet, PoolLaw.w P
  let Hit (P : F.Pool C) : Prop := poolContainsLabel P y
  let Indicator (P : F.Pool C) : ℝ :=
    if Hit P ∧ y ∈ Cal.permittedLabels C P b then 1 else 0
  let a : ℝ := (T.S.n k : ℝ) ^ (-3 : ℝ)
  let B : ℝ := Fintype.card BinType
  let L : ℝ := H.geom.nslot C
  let K : ℝ := (1 + a) * (B / L) * (PT.π i).w y
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast Cal.slot_pos C
  have hB : 0 < B := by
    dsimp [B, BinType]
    exact_mod_cast Finset.card_pos.mpr hBins
  have hδsmall : δ ≤ a / 2 := by simpa [a] using hδ_small
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
  have ha_le : a ≤ 1 / 8 := by
    have hpow : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hnR (by norm_num)
    have htwo : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by norm_num
    simpa [a, htwo] using hpow
  have hden : 0 < 1 - δ := by linarith
  have hMass : 1 - δ ≤ Mass := by
    have hsplit : Mass +
        (∑ P ∈ Finset.univ.filter (fun P : F.Pool C => ¬ F.typical C P), PoolLaw.w P) = 1 := by
      dsimp [Mass, TypicalSet]
      rw [Finset.sum_filter_add_sum_filter_not]
      exact PoolLaw.sum_one
    have hfail : PoolLaw.pr (fun P => ¬ F.typical C P) =
        ∑ P ∈ Finset.univ.filter (fun P : F.Pool C => ¬ F.typical C P), PoolLaw.w P := by
      classical
      unfold FinLaw.pr
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases ht : F.typical C P <;> simp [ht]
    linarith [hsplit, hTypicalFailure]
  have hMassPos : 0 < Mass := hTypical
  have hBinsYCard :
      (Finset.univ.filter (fun D : BinType => y ∈ D.1)).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro D₁ D₂ hD₁ hD₂
    apply Subtype.ext
    have hy₁ : y ∈ D₁.1 := (Finset.mem_filter.mp hD₁).2
    have hy₂ : y ∈ D₂.1 := (Finset.mem_filter.mp hD₂).2
    exact (PT.tiling.P (H.geom.cellPatch C)).bins.eq_of_mem_parts D₁.2 D₂.2 hy₁ hy₂
  have hAtom (s : Slot) (D : BinType) : PoolLaw.pr (fun P => P s = D) = 1 / B := by
    have h := HypercubeRamsey.S16.Lane_q_s16_comp2.pi_pr_cylinder
      (fun _ : Slot => FinLaw.uniform (Finset.univ : Finset BinType) hBins)
      ({s} : Finset Slot) (fun _ => D)
    simpa [PoolLaw, iidCellPoolLaw, BinType, Slot, FinLaw.uniform, Finset.mem_univ,
      Finset.prod_const] using h
  have hslotHit (s : Slot) : PoolLaw.pr (fun P => y ∈ (P s).1) ≤ 1 / B := by
    let binsY : Finset BinType := Finset.univ.filter fun D => y ∈ D.1
    have hEvent : (fun P : F.Pool C => y ∈ (P s).1) =
        (fun P => ∃ D : BinType, D ∈ binsY ∧ P s = D) := by
      funext P
      apply propext
      constructor
      · intro hy
        exact ⟨P s, by simp [binsY, hy], rfl⟩
      · rintro ⟨D, hD, hEq⟩
        have hval : (P s).1 = D.1 := congrArg Subtype.val hEq
        rw [hval]
        exact (Finset.mem_filter.mp hD).2
    rw [hEvent]
    calc
      PoolLaw.pr (fun P => ∃ D : BinType, D ∈ binsY ∧ P s = D) ≤
          ∑ D : BinType, PoolLaw.pr (fun P => D ∈ binsY ∧ P s = D) :=
        HypercubeRamsey.S16.Lane_q_s16_comp2.pr_exists_le_sum PoolLaw _
      _ = (binsY.card : ℝ) * (1 / B) := by
        calc
          (∑ D : BinType, PoolLaw.pr (fun P => D ∈ binsY ∧ P s = D)) =
              ∑ D : BinType, if D ∈ binsY then 1 / B else 0 := by
                apply Finset.sum_congr rfl
                intro D hD
                by_cases hD' : D ∈ binsY
                · simpa [hD'] using hAtom s D
                · simp [hD', FinLaw.pr]
          _ = (binsY.card : ℝ) * (1 / B) := by
                rw [Finset.sum_ite_mem]
                simp [nsmul_eq_mul]
      _ ≤ 1 / B := by
        have hcardReal : (binsY.card : ℝ) ≤ 1 := by
          simpa [binsY] using hBinsYCard
        have hInvB : 0 ≤ 1 / B := div_nonneg (by norm_num) hB.le
        simpa using mul_le_mul_of_nonneg_right hcardReal hInvB
  have hHit : PoolLaw.pr Hit ≤ L / B := by
    change PoolLaw.pr (fun P : F.Pool C => ∃ s : Slot, y ∈ (P s).1) ≤ L / B
    calc
      PoolLaw.pr (fun P => ∃ s : Slot, y ∈ (P s).1) ≤
          ∑ s : Slot, PoolLaw.pr (fun P => y ∈ (P s).1) :=
        HypercubeRamsey.S16.Lane_q_s16_comp2.pr_exists_le_sum PoolLaw _
      _ ≤ ∑ s : Slot, 1 / B := Finset.sum_le_sum fun s hs => hslotHit s
      _ = L / B := by
        conv_rhs => rw [div_eq_mul_inv]
        simp [Slot, L, Finset.sum_const, nsmul_eq_mul] <;> rfl
  have hpi : 0 ≤ (PT.π i).w y := (PT.π i).nonneg y
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by linarith [ha_nonneg])
      (div_nonneg hB.le hL.le)) hpi
  have hPoint : ∀ P, Indicator P ≤ (if Hit P then 1 else 0) := by
    intro P
    by_cases hHit' : Hit P <;> by_cases hPerm : y ∈ Cal.permittedLabels C P b <;>
      simp [Indicator, Hit, hHit', hPerm]
  have hCondIndicator :
      (FinLaw.cond PoolLaw TypicalSet hTypical).E Indicator ≤
        (FinLaw.cond PoolLaw TypicalSet hTypical).pr Hit := by
    calc
      (FinLaw.cond PoolLaw TypicalSet hTypical).E Indicator ≤
          (FinLaw.cond PoolLaw TypicalSet hTypical).E (fun P => if Hit P then 1 else 0) :=
            HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _ hPoint
      _ = (FinLaw.cond PoolLaw TypicalSet hTypical).pr Hit := by
        simp [FinLaw.E, FinLaw.pr, mul_ite]
  have hCondPr :
      (FinLaw.cond PoolLaw TypicalSet hTypical).pr Hit ≤ PoolLaw.pr Hit / Mass := by
    have hnum :
        (∑ P ∈ TypicalSet, if Hit P then PoolLaw.w P else 0) ≤ PoolLaw.pr Hit := by
      unfold FinLaw.pr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro P hP hnot
        by_cases hh : Hit P
        · simpa [hh] using PoolLaw.nonneg P
        · simp [hh])
    have hcond : (FinLaw.cond PoolLaw TypicalSet hTypical).pr Hit =
        (∑ P ∈ TypicalSet, if Hit P then PoolLaw.w P else 0) / Mass := by
      unfold FinLaw.pr
      calc
        (∑ P, if Hit P then (FinLaw.cond PoolLaw TypicalSet hTypical).w P else 0) =
            ∑ P, if P ∈ TypicalSet then
              (if Hit P then PoolLaw.w P else 0) / Mass else 0 := by
                apply Finset.sum_congr rfl
                intro P hP
                by_cases ht : P ∈ TypicalSet
                · by_cases hh : Hit P <;> simp [FinLaw.cond, ht, hh, Mass]
                · simp [FinLaw.cond, ht, Mass]
        _ = (∑ P ∈ TypicalSet, if Hit P then PoolLaw.w P else 0) / Mass := by
              rw [Finset.sum_ite_mem]
              rw [Finset.sum_div]
              rw [Finset.univ_inter]
    rw [hcond]
    exact div_le_div_of_nonneg_right hnum hMassPos.le
  have hcoef : (1 + a) / (1 - δ) ≤ 1 + 2 * a := by
    have hprod : 2 * a * δ ≤ a ^ 2 := by
      have := mul_le_mul_of_nonneg_left hδsmall (by positivity : 0 ≤ 2 * a)
      nlinarith
    have hslack : 0 ≤ a - δ - 2 * a * δ := by nlinarith [hδ, hδsmall, ha_le, hprod]
    rw [div_le_iff₀ hden]
    nlinarith [hslack]
  have hcancel : K * ((L / B) / (1 - δ)) = ((1 + a) / (1 - δ)) * (PT.π i).w y := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have hBne : B ≠ 0 := ne_of_gt hB
    dsimp [K]
    field_simp [hLne, hBne, ne_of_gt hden]
    <;> ring
  have hpatchCell : H.geom.cellPatch C = i := by
    calc
      H.geom.cellPatch C = H.geom.cellPatch (H.geom.cellOf b) :=
        congrArg H.geom.cellPatch hcell.symm
      _ = H.geom.patchOf b := H.geom.cellOf_patch b
      _ = i := hpatch
  have hcoeffCell :
      (1 + a) * (Fintype.card (Bin PT.tiling i) : ℝ) / H.geom.nslot C *
          (PT.π i).w y = K := by
    dsimp [K, B, L, BinType]
    rw [← hpatchCell]
    ring
  have hMain :
      (FinLaw.cond PoolLaw TypicalSet hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤ K *
          (FinLaw.cond PoolLaw TypicalSet hTypical).E Indicator := by
    unfold FinLaw.E
    calc
      (∑ P, (FinLaw.cond PoolLaw TypicalSet hTypical).w P *
          (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
        ∑ P, (FinLaw.cond PoolLaw TypicalSet hTypical).w P * (K * Indicator P) := by
          apply Finset.sum_le_sum
          intro P hP
          by_cases ht : F.typical C P
          · have hfixed' :
                (F.fresh C P).pr (fun s => F.label C s b = y) ≤ K * Indicator P := by
              have hh := hFixed P ht
              have hh' :
                  (F.fresh C P).pr (fun s => F.label C s b = y) ≤
                    ((1 + a) * (Fintype.card (Bin PT.tiling i) : ℝ) /
                      H.geom.nslot C * (PT.π i).w y) * Indicator P := by
                simpa [Indicator, Hit, a] using hh
              rw [hcoeffCell] at hh'
              exact hh'
            exact mul_le_mul_of_nonneg_left hfixed'
              ((FinLaw.cond PoolLaw TypicalSet hTypical).nonneg P)
          · have hzero : (FinLaw.cond PoolLaw TypicalSet hTypical).w P = 0 := by
              simp [FinLaw.cond, TypicalSet, ht]
            simp [hzero]
      _ = K * ∑ P, (FinLaw.cond PoolLaw TypicalSet hTypical).w P * Indicator P := by
          calc
            (∑ P, (FinLaw.cond PoolLaw TypicalSet hTypical).w P * (K * Indicator P)) =
                ∑ P, K * ((FinLaw.cond PoolLaw TypicalSet hTypical).w P * Indicator P) := by
                  apply Finset.sum_congr rfl
                  intro P hP
                  ring
            _ = K * ∑ P, (FinLaw.cond PoolLaw TypicalSet hTypical).w P * Indicator P := by
                  rw [Finset.mul_sum]
  calc
    (FinLaw.cond PoolLaw TypicalSet hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
      K * (FinLaw.cond PoolLaw TypicalSet hTypical).E Indicator := hMain
    _ ≤ K * ((L / B) / Mass) :=
      mul_le_mul_of_nonneg_left (hCondIndicator.trans (hCondPr.trans (by
        exact div_le_div_of_nonneg_right hHit (le_of_lt hMassPos)))) hK
    _ ≤ K * ((L / B) / (1 - δ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact div_le_div_of_nonneg_left (div_nonneg (by positivity) (by positivity)) hden hMass
      · exact hK
    _ = ((1 + a) / (1 - δ)) * (PT.π i).w y := hcancel
    _ ≤ (1 + 2 * a) * (PT.π i).w y :=
      mul_le_mul_of_nonneg_right hcoef hpi

/-- L16.6: exact stage calibration, fixed-pool bound, then iid averaging. -/
theorem fresh_singleton_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (Cal : FreshLabelCalibration F)
    {validState : ∀ C : H.geom.Cell, F.Pool C → F.State C → Prop}
    (hF : FreshCell.Spec F validState Cal.permittedLabels) (C : H.geom.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hTypicalFailure : (iidCellPoolLaw (G := H.geom) C hBins).pr (fun P => ¬ F.typical C P) ≤ δ)
    (hδ_small : δ ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) / 2)
    (hTypical : 0 < ∑ P ∈ Finset.univ.filter (F.typical C), (iidCellPoolLaw (G := H.geom) C hBins).w P)
    (i : Fin PT.tiling.m) (b : Pos T k) (hpatch : H.geom.patchOf b = i)
    (hcell : H.geom.cellOf b = C) (hOdd : ¬ IsEvenRole b) (y : Fin (T.S.N k)) :
    (∀ P, F.typical C P →
      (F.fresh C P).pr (fun s => F.label C s b = y) ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (Fintype.card (Bin PT.tiling i) : ℝ) /
          H.geom.nslot C * (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0)) ∧
    (FinLaw.cond (iidCellPoolLaw (G := H.geom) C hBins)
      (Finset.univ.filter (F.typical C)) hTypical).E
        (fun P => (F.fresh C P).pr (fun s => F.label C s b = y)) ≤
      (1 + 2 * (T.S.n k : ℝ) ^ (-3 : ℝ)) * (PT.π i).w y := by
  have hf : ∀ P, F.typical C P →
      (F.fresh C P).pr (fun s => F.label C s b = y) ≤
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * (Fintype.card (Bin PT.tiling i) : ℝ) /
          H.geom.nslot C * (PT.π i).w y *
            (if poolContainsLabel P y ∧ y ∈ Cal.permittedLabels C P b then 1 else 0) := by
    intro P ht
    exact fresh_singleton_fixed_pool_node hκ Q H Cal C P ht b y i hcell hOdd
      (fresh_singleton_target_bound hκ Q H Cal C P ht b y i hcell hOdd hpatch)
  exact ⟨hf, fresh_singleton_iid_pool_node hκ Q H Cal C hBins δ hδ hTypicalFailure
    hδ_small hTypical i b hpatch hcell hOdd y hf⟩

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

/-- The actual unrestricted slice experiment, with the solver's unchanged
raw posterior readout. -/
noncomputable def solverBasePriorExperiment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (v : EvenRole PT.tiling i) :
    PriorExperiment (T.S.N k) where
  State := (∀ r, S.Val r) × ((HypercubeRamsey.Group PT.tiling i → Bin PT.tiling i) ×
    (IWord PT.tiling i → Fin (T.S.N k)))
  law := FinLaw.bind (S.recLaw PT.parameter) S.refLaw
  prior := fun ω => S.σ v ω.1 (nbrLabels v.1 ω.2.2)

/-- A local star's actual sampling pipeline. `LocalHist` is its slice data;
`Aux` contains the independent histories of other slices. The cell gate is
retained on their product until the calibrated bin and label stages have
been compared. Only the local history enters raw kernels and raw σ. -/
structure FreshPriorPipeline {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G)
    (C : G.Cell) (v : Pos T k) where
  LocalHist : Type
  [localFin : Fintype LocalHist]
  [localDec : DecidableEq LocalHist]
  Aux : Type
  [auxFin : Fintype Aux]
  Group : Type
  [groupFin : Fintype Group]
  [groupDec : DecidableEq Group]
  Role : Type
  [roleFin : Fintype Role]
  [roleDec : DecidableEq Role]
  baseHistory : FinLaw LocalHist
  slicePass : Finset LocalHist
  slice_pos : 0 < ∑ W ∈ slicePass, baseHistory.w W
  auxHistory : FinLaw Aux
  history : FinLaw (LocalHist × Aux)
  history_eq : history = FinLaw.bind (FinLaw.cond baseHistory slicePass slice_pos) (fun _ => auxHistory)
  gate : F.Pool C → Finset (LocalHist × Aux)
  gate_pos : ∀ pool, F.typical C pool → 0 < ∑ W ∈ gate pool, history.w W
  gatedHistory : F.Pool C → FinLaw (LocalHist × Aux)
  gated_eq : ∀ pool (ht : F.typical C pool),
    gatedHistory pool = FinLaw.cond history (gate pool) (gate_pos pool ht)
  qraw : LocalHist → Group → FinLaw (Bin PT.tiling (G.cellPatch C))
  U : LocalHist → Group → Bin PT.tiling (G.cellPatch C) → FinLaw (Fin (T.S.N k))
  U_support : ∀ W g D y, (U W g D).w y ≠ 0 → y ∈ D.1
  groupOf : Role → Group
  rolePosition : Role → Pos T k
  role_cell : ∀ r, G.cellOf (rolePosition r) = C
  role_odd : ∀ r, ¬ IsEvenRole (rolePosition r)
  groupScope : Finset Group
  roleScope : Finset Role
  scopes_closed : ∀ r ∈ roleScope, groupOf r ∈ groupScope
  rawPrior : LocalHist → (Role → Fin (T.S.N k)) → Fin (T.S.N k) → ℝ
  prior_local : ∀ W ys ys', (∀ r ∈ roleScope, ys r = ys' r) → rawPrior W ys = rawPrior W ys'
  pretrim : LocalHist → Group → Finset (Bin PT.tiling (G.cellPatch C))
  permitted : Group → Finset (Bin PT.tiling (G.cellPatch C))
  qtilde : F.Pool C → LocalHist → Group → FinLaw (Bin PT.tiling (G.cellPatch C))
  qtilde_eq : ∀ pool W g D, F.typical C pool → W ∈ slicePass → baseHistory.w W ≠ 0 →
    (qtilde pool W g).w D =
      (if D ∈ pretrim W g ∧ D ∈ permitted g ∧ D ∈ Finset.univ.image pool then (qraw W g).w D else 0) /
      (∑ D' ∈ ((pretrim W g ∩ permitted g) ∩ Finset.univ.image pool), (qraw W g).w D')
  binSampler : F.Pool C → (LocalHist × Aux) → FinLaw (Group → Bin PT.tiling (G.cellPatch C))
  labelSampler : F.Pool C → (LocalHist × Aux) →
    (Group → Bin PT.tiling (G.cellPatch C)) → FinLaw (Role → Fin (T.S.N k))
  groupRate : ℝ
  labelRate : ℝ
  rates_nonneg : 0 ≤ groupRate ∧ 0 ≤ labelRate
  bin_joint : ∀ pool W (a : Group → Bin PT.tiling (G.cellPatch C)), F.typical C pool → (gatedHistory pool).w W ≠ 0 →
    (binSampler pool W).pr (fun a' => ∀ g ∈ groupScope, a' g = a g) ≤
      Real.exp (groupRate * groupScope.card) * ∏ g ∈ groupScope, (qtilde pool W.1 g).w (a g)
  bins_distinct : ∀ pool W (a : Group → Bin PT.tiling (G.cellPatch C)), F.typical C pool → (gatedHistory pool).w W ≠ 0 →
    (binSampler pool W).w a ≠ 0 → Set.InjOn a (groupScope : Set Group)
  label_joint : ∀ pool W (a : Group → Bin PT.tiling (G.cellPatch C)) (ys : Role → Fin (T.S.N k)), F.typical C pool → (gatedHistory pool).w W ≠ 0 →
    (binSampler pool W).w a ≠ 0 →
    (labelSampler pool W a).pr (fun ys' => ∀ r ∈ roleScope, ys' r = ys r) ≤
      Real.exp (labelRate * roleScope.card) * ∏ r ∈ roleScope, (U W.1 (groupOf r) (a (groupOf r))).w (ys r)
  encode : (LocalHist × Aux) × ((Group → Bin PT.tiling (G.cellPatch C)) ×
    (Role → Fin (T.S.N k))) → F.State C
  fresh_eq : ∀ pool, F.typical C pool → F.fresh C pool =
    FinLaw.map (FinLaw.bind (gatedHistory pool) fun W =>
      FinLaw.bind (binSampler pool W) (labelSampler pool W)) encode
  /-- The raw posterior readout is retained exactly, through every stage. -/
  prior_eq : ∀ pool W a ys, F.typical C pool → (gatedHistory pool).w W ≠ 0 →
    (binSampler pool W).w a ≠ 0 → (labelSampler pool W a).w ys ≠ 0 →
    F.prior C (encode (W, a, ys)) v = rawPrior W.1 ys
  label_eq : ∀ pool W a ys r, F.typical C pool → (gatedHistory pool).w W ≠ 0 →
    (binSampler pool W).w a ≠ 0 → (labelSampler pool W a).w ys ≠ 0 →
    F.label C (encode (W, a, ys)) (rolePosition r) = ys r
  δgate : ℝ
  δpre : ℝ
  δperm : ℝ
  error_ranges : (0 ≤ δgate ∧ δgate < 1) ∧ (0 ≤ δpre ∧ δpre < 1) ∧ (0 ≤ δperm ∧ δperm < 1)
  gate_mass : ∀ pool, F.typical C pool → 1 - δgate ≤ ∑ W ∈ gate pool, history.w W
  pretrim_mass : ∀ W g, W ∈ slicePass → baseHistory.w W ≠ 0 → g ∈ groupScope →
    1 - δpre ≤ ∑ D ∈ pretrim W g, (qraw W g).w D
  permission_mass : ∀ W g, W ∈ slicePass → baseHistory.w W ≠ 0 → g ∈ groupScope →
    1 - δperm ≤ (∑ D ∈ (pretrim W g ∩ permitted g), (qraw W g).w D) /
      (∑ D ∈ pretrim W g, (qraw W g).w D)
  normalizer_mass : ∀ pool W g, F.typical C pool → W ∈ slicePass → baseHistory.w W ≠ 0 → g ∈ groupScope →
    ((G.nslot C : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C))) *
      (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
      (∑ D ∈ ((pretrim W g ∩ permitted g) ∩ Finset.univ.image pool), (qraw W g).w D) /
        (∑ D ∈ (pretrim W g ∩ permitted g), (qraw W g).w D)
  slot_pos : 0 < G.nslot C
  stage_cost : (1 - δgate)⁻¹ * Real.exp (groupRate * groupScope.card + labelRate * roleScope.card) *
    (1 - δpre)⁻¹ ^ groupScope.card * (1 - δperm)⁻¹ ^ groupScope.card *
      (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ ^ groupScope.card ≤ 10 * κ.Kcell
  slice_cost : (∑ W ∈ slicePass, baseHistory.w W)⁻¹ ≤ 10 * (κ.Kp : ℝ)

namespace FreshPriorPipeline
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
variable {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
instance (P : FreshPriorPipeline F C v) : Fintype P.LocalHist := P.localFin
instance (P : FreshPriorPipeline F C v) : DecidableEq P.LocalHist := P.localDec
instance (P : FreshPriorPipeline F C v) : Fintype P.Aux := P.auxFin
instance (P : FreshPriorPipeline F C v) : Fintype P.Group := P.groupFin
instance (P : FreshPriorPipeline F C v) : DecidableEq P.Group := P.groupDec
instance (P : FreshPriorPipeline F C v) : Fintype P.Role := P.roleFin
instance (P : FreshPriorPipeline F C v) : DecidableEq P.Role := P.roleDec

noncomputable def rawLaw (P : FreshPriorPipeline F C v) (W : P.LocalHist) :=
  FinLaw.bind (FinLaw.pi (P.qraw W)) fun a => FinLaw.pi fun r => P.U W (P.groupOf r) (a (P.groupOf r))

noncomputable def baseExperiment (P : FreshPriorPipeline F C v) : PriorExperiment (T.S.N k) where
  State := P.LocalHist × ((P.Group → Bin PT.tiling (G.cellPatch C)) × (P.Role → Fin (T.S.N k)))
  law := FinLaw.bind P.baseHistory P.rawLaw
  prior := fun ω => P.rawPrior ω.1 ω.2.2

noncomputable def sliceExperiment (P : FreshPriorPipeline F C v) : PriorExperiment (T.S.N k) where
  State := P.LocalHist × ((P.Group → Bin PT.tiling (G.cellPatch C)) × (P.Role → Fin (T.S.N k)))
  law := FinLaw.bind (FinLaw.cond P.baseHistory P.slicePass P.slice_pos) P.rawLaw
  prior := fun ω => P.rawPrior ω.1 ω.2.2

/-- Retain distinct target bins while restoring raw q and U. This integral
is intentionally unnormalized; it is not an unrelated probability law. -/
noncomputable def restrictedIntegral (P : FreshPriorPipeline F C v) (pool : F.Pool C)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) : ℝ :=
  (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).E fun W =>
    (P.rawLaw W).E fun ω =>
      if Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
        (∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool) then
        ((Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) / G.nslot C) ^ P.groupScope.card *
          Φ (P.rawPrior W ω.2) else 0

noncomputable def iidRestrictedIntegral (P : FreshPriorPipeline F C v)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) :=
  (iidCellPoolLaw (G := G) C hBins).E (fun pool => P.restrictedIntegral pool Φ)
end FreshPriorPipeline

/-- Transport an internal solver star to the actual cell's cube slice.
Flip preservation allows the parity-changing translation needed when the
fixed outer slice word has odd parity. -/
structure SliceStarLocation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) (v : Pos T k)
    (w : EvenRole PT.tiling (G.cellPatch C)) where
  axis : Fin (PT.tiling.P (G.cellPatch C)).h → Fin (T.S.n k)
  axis_injective : Function.Injective axis
  axes_eq : Finset.univ.image axis = PT.tiling.Icoord (G.cellPatch C)
  embed : IWord PT.tiling (G.cellPatch C) → Pos T k
  site_eq : embed w.1 = v
  flip_eq : ∀ z j, embed (flipPos z j) = flipPos (embed z) (axis j)
  outer_eq : ∀ z j, j ∉ PT.tiling.Icoord (G.cellPatch C) → embed z j = v j

/-- Construction identity with the actual slice solver, expressed as a
the exact joint law of records and internal neighbor labels. Direct modes retain the specified
uniform cleaned-support prior. Neither branch assumes a comparison bound. -/
def FreshPriorSourceValid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
    (P : FreshPriorPipeline F C v) : Prop :=
  (PT.tiling.mode = .lowCluster ∧
    ∃ (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh),
      PT.solver (G.cellPatch C) = some S ∧
      ∃ w : EvenRole PT.tiling (G.cellPatch C),
        ∃ loc : SliceStarLocation G C v w,
        ∃ records : P.LocalHist → (∀ r, S.Val r),
        ∃ roleAt : Fin (PT.tiling.P (G.cellPatch C)).h → P.Role,
          (∀ j, P.rolePosition (roleAt j) = flipPos v (loc.axis j)) ∧
          (∀ W ys, P.rawPrior W ys = S.σ w (records W) (fun j => ys (roleAt j))) ∧
          (∀ W₀ ys₀,
            P.baseExperiment.law.pr (fun ω => records ω.1 = W₀ ∧
              (fun j => ω.2.2 (roleAt j)) = ys₀) =
            (solverBasePriorExperiment S w).law.pr (fun ω =>
              ω.1 = W₀ ∧ nbrLabels w.1 ω.2.2 = ys₀))) ∨
  (¬ PT.tiling.mode.isCluster ∧ ∃ h : (PT.envelope (G.cellPatch C)).Nonempty,
    ∀ W ys, P.rawPrior W ys = (Law.unifCore (PT.envelope (G.cellPatch C)) h).w)

/-- L16.7a: use the actual conditional samplers, their joint comparisons,
and restriction denominator budgets, retaining distinct target bins. -/
theorem fresh_prior_stage_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (C : H.geom.Cell) (v : Pos T k) (hcell : H.geom.cellOf v = C) (hEven : IsEvenRole v)
    (P : FreshPriorPipeline F C v) (hSource : FreshPriorSourceValid P)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) (hΦ0 : Φ 0 = 0) :
    freshPriorTest F hBins C v hcell hEven Φ ≤
      (10 * κ.Kcell) * P.iidRestrictedIntegral (hBins C) Φ := by
  classical
  let StageFactor : ℝ :=
    (1 - P.δgate)⁻¹ * Real.exp (P.groupRate * P.groupScope.card +
      P.labelRate * P.roleScope.card) *
      (1 - P.δpre)⁻¹ ^ P.groupScope.card *
      (1 - P.δperm)⁻¹ ^ P.groupScope.card *
      (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ ^ P.groupScope.card
  have hStageNonneg : 0 ≤ StageFactor := by
    dsimp [StageFactor]
    rcases P.error_ranges with ⟨⟨hg0, hg1⟩, ⟨hp0, hp1⟩, ⟨hperm0, hperm1⟩⟩
    have hn : 2 ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
    have he : (T.S.n k : ℝ) ^ (-4 : ℝ) ≤ 1 / 16 := by
      have hpow := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ))
        (y := (T.S.n k : ℝ)) (z := (-4 : ℝ)) (by norm_num) hn (by norm_num)
      have htwo : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
      rw [htwo] at hpow
      exact hpow
    have heps_lt : (T.S.n k : ℝ) ^ (-4 : ℝ) < 1 := by linarith [he]
    have hgden : 0 < 1 - P.δgate := by linarith
    have hpden : 0 < 1 - P.δpre := by linarith
    have hpermden : 0 < 1 - P.δperm := by linarith
    have hdeneps : 0 < 1 - (T.S.n k : ℝ) ^ (-4 : ℝ) := by linarith
    positivity
  have hFreshRaw (pool : F.Pool C) (ht : F.typical C pool) :
      (F.fresh C pool).E (fun s => Φ (F.prior C s v)) =
        (FinLaw.bind (P.gatedHistory pool) fun W =>
          FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
          (fun ω => Φ (P.rawPrior ω.1.1 ω.2.2)) := by
    rw [P.fresh_eq pool ht, HypercubeRamsey.S16.Lane_q_s16_comp2.map_expect]
    apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
    intro ω hω
    have hweights :
        (P.gatedHistory pool).w ω.1 *
          ((P.binSampler pool ω.1).w ω.2.1 * (P.labelSampler pool ω.1 ω.2.1).w ω.2.2) ≠ 0 := by
      simpa [FinLaw.bind] using hω
    have hgate : (P.gatedHistory pool).w ω.1 ≠ 0 := by
      intro hz
      apply hweights
      simp [hz]
    have hrest :
        (P.binSampler pool ω.1).w ω.2.1 *
          (P.labelSampler pool ω.1 ω.2.1).w ω.2.2 ≠ 0 := by
      intro hz
      apply hweights
      simp [hz]
    have hbin : (P.binSampler pool ω.1).w ω.2.1 ≠ 0 := by
      intro hz
      apply hrest
      simp [hz]
    have hlabel : (P.labelSampler pool ω.1 ω.2.1).w ω.2.2 ≠ 0 := by
      intro hz
      apply hrest
      simp [hz]
    have hprior := P.prior_eq pool ω.1 ω.2.1 ω.2.2 ht hgate hbin hlabel
    exact congrArg Φ hprior
  have hPoolBound : ∀ pool, F.typical C pool →
      (F.fresh C pool).E (fun s => Φ (F.prior C s v)) ≤
        StageFactor * P.restrictedIntegral pool Φ := by
    intro pool ht
    have hRaw := hFreshRaw pool ht
    let GroupScope := {g : P.Group // g ∈ P.groupScope}
    let RoleScope := {r : P.Role // r ∈ P.roleScope}
    letI groupScopeFin : Fintype GroupScope :=
      Fintype.ofFinset P.groupScope (fun _ => Iff.rfl)
    letI roleScopeFin : Fintype RoleScope :=
      Fintype.ofFinset P.roleScope (fun _ => Iff.rfl)
    let BinType := Bin PT.tiling (H.geom.cellPatch C)
    let Label := Fin (T.S.N k)
    let bin0 : BinType := Classical.choose (hBins C)
    let extendBins : (GroupScope → BinType) → P.Group → BinType := fun b g =>
      if hg : g ∈ P.groupScope then b ⟨g, hg⟩ else bin0
    let projectBins : (P.Group → BinType) → (GroupScope → BinType) :=
      fun a g => a g.1
    let extendLabels : (RoleScope → Label) → P.Role → Label := fun y r =>
      if hr : r ∈ P.roleScope then y ⟨r, hr⟩ else ⟨0, T.S.N_pos k⟩
    let projectLabels : (P.Role → Label) → (RoleScope → Label) :=
      fun ys r => ys r.1
    let GroupLaw (W : P.LocalHist) : FinLaw (GroupScope → BinType) :=
      FinLaw.pi fun g : GroupScope => P.qraw W g.1
    let RoleLaw (W : P.LocalHist) (b : GroupScope → BinType) :
        FinLaw (RoleScope → Label) :=
      FinLaw.pi fun r : RoleScope =>
        P.U W (P.groupOf r.1)
          (b ⟨P.groupOf r.1, P.scopes_closed r.1 r.2⟩)
    let Scale : ℝ :=
      ((Fintype.card BinType : ℝ) / H.geom.nslot C) ^ P.groupScope.card
    let B : ℝ := Fintype.card BinType
    let L : ℝ := H.geom.nslot C
    let eps4 : ℝ := (T.S.n k : ℝ) ^ (-4 : ℝ)
    let preInv : ℝ := (1 - P.δpre)⁻¹
    let permInv : ℝ := (1 - P.δperm)⁻¹
    let epsInv : ℝ := (1 - eps4)⁻¹
    let AtomFactor : ℝ := (B / L) * epsInv * permInv * preInv
    let LocalFactor : ℝ := Real.exp (P.groupRate * P.groupScope.card +
      P.labelRate * P.roleScope.card) * preInv ^ P.groupScope.card *
        permInv ^ P.groupScope.card * epsInv ^ P.groupScope.card
    let GoodScope (pool : F.Pool C) (b : GroupScope → BinType) : Prop :=
      Set.InjOn (extendBins b) (P.groupScope : Set P.Group) ∧
        ∀ g ∈ P.groupScope, extendBins b g ∈ Finset.univ.image pool
    let TestScope (pool : F.Pool C) (W : P.LocalHist)
        (b : GroupScope → BinType) (ys : RoleScope → Label) : ℝ :=
      if GoodScope pool b then Φ (P.rawPrior W (extendLabels ys)) else 0
    let ScopeLaw (W : P.LocalHist) :=
      FinLaw.bind (GroupLaw W) (RoleLaw W)
    have hB : 0 < B := by
      dsimp [B, BinType]
      exact_mod_cast Finset.card_pos.mpr (hBins C)
    have hL : 0 < L := by
      dsimp [L]
      exact_mod_cast P.slot_pos
    have hPre0 : 0 ≤ P.δpre := P.error_ranges.2.1.1
    have hPre1 : P.δpre < 1 := P.error_ranges.2.1.2
    have hPerm0 : 0 ≤ P.δperm := P.error_ranges.2.2.1
    have hPerm1 : P.δperm < 1 := P.error_ranges.2.2.2
    have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
    have hepsBound : eps4 ≤ 1 / 16 := by
      have hpow := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ))
        (y := (T.S.n k : ℝ)) (z := (-4 : ℝ)) (by norm_num) hnR (by norm_num)
      have htwo : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
      dsimp [eps4]
      rw [htwo] at hpow
      exact hpow
    have heps0 : 0 ≤ eps4 := by dsimp [eps4]; positivity
    have heps1 : eps4 < 1 := by linarith [hepsBound]
    have hprePos : 0 < 1 - P.δpre := by linarith
    have hpermPos : 0 < 1 - P.δperm := by linarith
    have hepsPos : 0 < 1 - eps4 := by linarith
    have hBne : B ≠ 0 := ne_of_gt hB
    have hLne : L ≠ 0 := ne_of_gt hL
    have hAtomNonneg : 0 ≤ AtomFactor := by
      dsimp [AtomFactor, B, L, epsInv, permInv, preInv]
      positivity
    have hLocalNonneg : 0 ≤ LocalFactor := by
      dsimp [LocalFactor, epsInv, permInv, preInv]
      positivity
    have hLocalSupport (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) :
        W.1 ∈ P.slicePass ∧ P.baseHistory.w W.1 ≠ 0 := by
      have hHist : P.history.w W ≠ 0 := by
        rw [P.gated_eq pool ht, FinLaw.cond] at hW
        by_cases hm : W ∈ P.gate pool
        · simp only [if_pos hm] at hW
          have hnum : P.history.w W ≠ 0 := by
            intro hz
            apply hW
            simp [hz]
          exact hnum
        · simp [hm] at hW
      have hCond :
          (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).w W.1 ≠ 0 := by
        rw [P.history_eq, FinLaw.bind] at hHist
        intro hz
        apply hHist
        simp [hz]
      have hmem : W.1 ∈ P.slicePass := by
        by_contra hm
        apply hCond
        simp [FinLaw.cond, hm]
      have hbase : P.baseHistory.w W.1 ≠ 0 := by
        intro hz
        apply hCond
        simp [FinLaw.cond, hmem, hz]
      exact ⟨hmem, hbase⟩
    have hQtildePoint (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (g : GroupScope) (D : BinType) :
        (P.qtilde pool W.1 g.1).w D ≤
          AtomFactor * (P.qraw W.1 g.1).w D := by
      have hlocal := hLocalSupport W hW
      let massPre : ℝ := ∑ D' ∈ P.pretrim W.1 g.1, (P.qraw W.1 g.1).w D'
      let massPerm : ℝ := ∑ D' ∈ (P.pretrim W.1 g.1 ∩ P.permitted g.1),
        (P.qraw W.1 g.1).w D'
      let massPool : ℝ := ∑ D' ∈ ((P.pretrim W.1 g.1 ∩ P.permitted g.1) ∩
        Finset.univ.image pool), (P.qraw W.1 g.1).w D'
      have hpre : 1 - P.δpre ≤ massPre := by
        simpa [massPre] using P.pretrim_mass W.1 g.1 hlocal.1 hlocal.2 g.2
      have hperm : 1 - P.δperm ≤ massPerm / massPre := by
        simpa [massPerm, massPre] using
          P.permission_mass W.1 g.1 hlocal.1 hlocal.2 g.2
      have hnorm : (L / B) * (1 - eps4) ≤ massPool / massPerm := by
        simpa [massPool, massPerm, L, B, eps4] using
          P.normalizer_mass pool W.1 g.1 ht hlocal.1 hlocal.2 g.2
      have hmassPrePos : 0 < massPre := by
        dsimp [massPre]
        linarith [hpre, hprePos]
      have hpermMul : (1 - P.δperm) * massPre ≤ massPerm :=
        (le_div_iff₀ hmassPrePos).mp hperm
      have hmassPermPos : 0 < massPerm := by
        have hmulpos : 0 < (1 - P.δperm) * massPre := mul_pos hpermPos hmassPrePos
        exact lt_of_lt_of_le hmulpos hpermMul
      have hnormMul : (L / B) * (1 - eps4) * massPerm ≤ massPool := by
        exact (le_div_iff₀ hmassPermPos).mp hnorm
      have hlower :
          (L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre) ≤ massPool := by
        calc
          (L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre) =
              (L / B) * (1 - eps4) * ((1 - P.δperm) * (1 - P.δpre)) := by ring
          _ ≤
              (L / B) * (1 - eps4) * ((1 - P.δperm) * massPre) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpre (le_of_lt hpermPos))
                  (mul_nonneg (div_nonneg hL.le hB.le) (sub_nonneg.mpr heps1.le))
          _ ≤ (L / B) * (1 - eps4) * massPerm :=
                mul_le_mul_of_nonneg_left hpermMul
                  (mul_nonneg (div_nonneg hL.le hB.le) (sub_nonneg.mpr heps1.le))
          _ ≤ massPool := hnormMul
      have hlowerPos :
          0 < (L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre) := by
        positivity
      have hmassPoolPos : 0 < massPool := lt_of_lt_of_le hlowerPos hlower
      have hinv : massPool⁻¹ ≤
          ((L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre))⁻¹ :=
        (inv_le_inv₀ hmassPoolPos hlowerPos).2 hlower
      have hinvEq :
          ((L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre))⁻¹ = AtomFactor := by
        dsimp [AtomFactor, B, L, epsInv, permInv, preInv]
        field_simp [hBne, hLne, ne_of_gt hepsPos, ne_of_gt hpermPos, ne_of_gt hprePos]
        <;> ring
      have hformula := P.qtilde_eq pool W.1 g.1 D ht hlocal.1 hlocal.2
      by_cases hallowed :
          D ∈ P.pretrim W.1 g.1 ∧ D ∈ P.permitted g.1 ∧ D ∈ Finset.univ.image pool
      · rw [hformula]
        simp only [if_pos hallowed]
        calc
          (P.qraw W.1 g.1).w D / massPool =
              (P.qraw W.1 g.1).w D * massPool⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ (P.qraw W.1 g.1).w D *
              ((L / B) * (1 - eps4) * (1 - P.δperm) * (1 - P.δpre))⁻¹ :=
                mul_le_mul_of_nonneg_left hinv ((P.qraw W.1 g.1).nonneg D)
          _ = AtomFactor * (P.qraw W.1 g.1).w D := by rw [hinvEq]; ring
      · rw [hformula]
        simp only [if_neg hallowed, zero_div]
        exact mul_nonneg hAtomNonneg ((P.qraw W.1 g.1).nonneg D)
    let TildeGroupLaw (W : P.LocalHist × P.Aux) :=
      FinLaw.pi fun g : GroupScope => P.qtilde pool W.1 g.1
    have hTildeWeight (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) (b : GroupScope → BinType) :
        (TildeGroupLaw W).w b ≤
          AtomFactor ^ P.groupScope.card * (GroupLaw W.1).w b := by
      change (∏ g : GroupScope, (P.qtilde pool W.1 g.1).w (b g)) ≤
        AtomFactor ^ P.groupScope.card *
          (∏ g : GroupScope, (P.qraw W.1 g.1).w (b g))
      calc
        (∏ g : GroupScope, (P.qtilde pool W.1 g.1).w (b g)) ≤
            ∏ g : GroupScope, AtomFactor * (P.qraw W.1 g.1).w (b g) := by
              apply Finset.prod_le_prod₀
              · intro g hg
                exact (P.qtilde pool W.1 g.1).nonneg (b g)
              · intro g hg
                exact hQtildePoint W hW g (b g)
        _ = AtomFactor ^ P.groupScope.card *
              (∏ g : GroupScope, (P.qraw W.1 g.1).w (b g)) := by
                rw [Finset.prod_mul_distrib]
                have hcard : (Finset.univ : Finset GroupScope).card =
                    P.groupScope.card := by
                  change P.groupScope.attach.card = P.groupScope.card
                  exact Finset.card_attach
                have hconst : (∏ g : GroupScope, AtomFactor) =
                    AtomFactor ^ P.groupScope.card := by
                  rw [Finset.prod_const]
                  rw [hcard]
                rw [hconst]
    have hAtomPower : AtomFactor ^ P.groupScope.card =
        Scale * preInv ^ P.groupScope.card * permInv ^ P.groupScope.card *
          epsInv ^ P.groupScope.card := by
      simp only [AtomFactor, Scale, mul_pow]
      ring
    have hGroupAtom (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (b : GroupScope → BinType) :
        (P.binSampler pool W).pr (fun a => projectBins a = b) ≤
          Real.exp (P.groupRate * P.groupScope.card) * (TildeGroupLaw W).w b := by
      have hPred (a : P.Group → BinType) : projectBins a = b ↔
          ∀ g ∈ P.groupScope, a g = extendBins b g := by
        constructor
        · intro heq g hg
          have h := congrFun heq ⟨g, hg⟩
          simpa [projectBins, extendBins, hg] using h
        · intro h
          funext g
          simpa [projectBins, extendBins, g.2] using h g.1 g.2
      have hPredFun : (fun a : P.Group → BinType => projectBins a = b) =
          (fun a => ∀ g ∈ P.groupScope, a g = extendBins b g) :=
        funext fun a => propext (hPred a)
      have hprod :
          (∏ g ∈ P.groupScope, (P.qtilde pool W.1 g).w (extendBins b g)) =
            (TildeGroupLaw W).w b := by
        have hsub := Finset.prod_subtype (F := groupScopeFin)
          (s := P.groupScope) (h := fun _ => Iff.rfl)
          (fun g => (P.qtilde pool W.1 g).w (extendBins b g))
        calc
          (∏ g ∈ P.groupScope, (P.qtilde pool W.1 g).w (extendBins b g)) =
              ∏ g : GroupScope, (P.qtilde pool W.1 g.1).w (b g) := by
                simpa [extendBins] using hsub
          _ = (TildeGroupLaw W).w b :=
                (HypercubeRamsey.S16.Lane_q_s16_comp2.pi_subtype_weight
                  (fun g : P.Group => P.qtilde pool W.1 g) P.groupScope b).symm
      rw [hPredFun]
      have hj := P.bin_joint pool W (extendBins b) ht hW
      simpa [hprod] using hj
    have hLabelAtom (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (a : P.Group → BinType) (ha : (P.binSampler pool W).w a ≠ 0)
        (ys : RoleScope → Label) :
        (P.labelSampler pool W a).pr (fun ys' => projectLabels ys' = ys) ≤
          Real.exp (P.labelRate * P.roleScope.card) *
            (RoleLaw W.1 (projectBins a)).w ys := by
      have hPred (ys' : P.Role → Label) : projectLabels ys' = ys ↔
          ∀ r ∈ P.roleScope, ys' r = extendLabels ys r := by
        constructor
        · intro heq r hr
          have h := congrFun heq ⟨r, hr⟩
          simpa [projectLabels, extendLabels, hr] using h
        · intro h
          funext r
          simpa [extendLabels, r.2] using h r.1 r.2
      have hPredFun : (fun ys' : P.Role → Label => projectLabels ys' = ys) =
          (fun ys' => ∀ r ∈ P.roleScope, ys' r = extendLabels ys r) :=
        funext fun ys' => propext (hPred ys')
      have hprod :
          (∏ r ∈ P.roleScope,
            (P.U W.1 (P.groupOf r) (a (P.groupOf r))).w (extendLabels ys r)) =
              (RoleLaw W.1 (projectBins a)).w ys := by
        have hsub := Finset.prod_subtype (F := roleScopeFin)
          (s := P.roleScope) (h := fun _ => Iff.rfl)
          (fun r => (P.U W.1 (P.groupOf r)
            (a (P.groupOf r))).w (extendLabels ys r))
        have hcoord (r : RoleScope) :
            a (P.groupOf r.1) = (projectBins a)
              ⟨P.groupOf r.1, P.scopes_closed r.1 r.2⟩ := rfl
        change (∏ r ∈ P.roleScope,
          (P.U W.1 (P.groupOf r) (a (P.groupOf r))).w (extendLabels ys r)) =
            ∏ r : RoleScope,
              (P.U W.1 (P.groupOf r.1)
                ((projectBins a) ⟨P.groupOf r.1, P.scopes_closed r.1 r.2⟩)).w (ys r)
        simpa [RoleLaw, extendLabels, projectBins, hcoord] using hsub
      rw [hPredFun]
      have hj := P.label_joint pool W a (extendLabels ys) ht hW ha
      simpa [hprod] using hj
    have hGoodSupport (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (a : P.Group → BinType) (ha : (P.binSampler pool W).w a ≠ 0) :
        GoodScope pool (projectBins a) := by
      have hlocal := hLocalSupport W hW
      have hEqX (x : P.Group) (hx : x ∈ P.groupScope) :
          extendBins (projectBins a) x = a x := by
        simp [extendBins, projectBins, hx]
      have hEqY (y : P.Group) (hy : y ∈ P.groupScope) :
          extendBins (projectBins a) y = a y := by
        simp [extendBins, projectBins, hy]
      constructor
      · intro x hx y hy hxy
        apply P.bins_distinct pool W a ht hW ha hx hy
        calc
          a x = extendBins (projectBins a) x := (hEqX x hx).symm
          _ = extendBins (projectBins a) y := hxy
          _ = a y := hEqY y hy
      · intro g hg
        have hAtomPos : 0 < (P.binSampler pool W).w a :=
          lt_of_le_of_ne ((P.binSampler pool W).nonneg a) (Ne.symm ha)
        let Cylinder : (P.Group → BinType) → Prop :=
          fun a' => ∀ g ∈ P.groupScope, a' g = a g
        letI : DecidablePred Cylinder := fun a' => Classical.propDecidable (Cylinder a')
        have hAtomle : (P.binSampler pool W).w a ≤
            (P.binSampler pool W).pr Cylinder := by
          unfold FinLaw.pr
          have hsum :
              (if Cylinder a then (P.binSampler pool W).w a else 0) ≤
                ∑ a' ∈ (Finset.univ : Finset (P.Group → BinType)),
                  if Cylinder a' then (P.binSampler pool W).w a' else 0 :=
            Finset.single_le_sum
              (f := fun a' => if Cylinder a' then (P.binSampler pool W).w a' else 0)
              (a := a) (s := Finset.univ)
              (fun a' _ => by
                by_cases hc : Cylinder a'
                · simp [hc, (P.binSampler pool W).nonneg a']
                · simp [hc])
              (Finset.mem_univ a)
          simpa [Cylinder] using hsum
        have hCylinderPos : 0 < (P.binSampler pool W).pr Cylinder :=
          lt_of_lt_of_le hAtomPos hAtomle
        have hjoint := P.bin_joint pool W a ht hW
        have hqnonzero : (P.qtilde pool W.1 g).w (a g) ≠ 0 := by
          by_contra hz
          have hprod :
              (∏ g' ∈ P.groupScope, (P.qtilde pool W.1 g').w (a g')) = 0 :=
            Finset.prod_eq_zero (s := P.groupScope) hg hz
          have hupper : (P.binSampler pool W).pr Cylinder ≤ 0 := by
            simpa [Cylinder, hprod] using hjoint
          linarith
        have hallowed :
            a g ∈ P.pretrim W.1 g ∧ a g ∈ P.permitted g ∧
              a g ∈ Finset.univ.image pool := by
          by_contra hn
          have hzero : (P.qtilde pool W.1 g).w (a g) = 0 := by
            rw [P.qtilde_eq pool W.1 g (a g) ht hlocal.1 hlocal.2]
            rw [if_neg hn]
            simp
          exact hqnonzero hzero
        simpa [GoodScope, extendBins, projectBins, hg] using hallowed.2.2
    have hRawLawProject (W : P.LocalHist)
        (f : (GroupScope → BinType) → (RoleScope → Label) → ℝ) :
        (P.rawLaw W).E (fun ω => f (projectBins ω.1) (projectLabels ω.2)) =
          (FinLaw.bind (GroupLaw W) fun b => RoleLaw W b).E
            (fun ω => f ω.1 ω.2) := by
      change (FinLaw.bind (FinLaw.pi (P.qraw W))
        (fun a => FinLaw.pi fun r => P.U W (P.groupOf r) (a (P.groupOf r)))).E _ = _
      rw [HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
      calc
        (FinLaw.pi (P.qraw W)).E (fun a =>
            (FinLaw.pi (fun r => P.U W (P.groupOf r) (a (P.groupOf r)))).E
              (fun ys => f (projectBins a) (projectLabels ys))) =
          (FinLaw.pi (P.qraw W)).E (fun a =>
            (RoleLaw W (projectBins a)).E (fun ys => f (projectBins a) ys)) := by
              apply congrArg
              funext a
              have hsub := HypercubeRamsey.S16.Lane_q_s16_comp2.pi_subtype_expect
                (fun r : P.Role => P.U W (P.groupOf r) (a (P.groupOf r)))
                P.roleScope (fun ys => f (projectBins a) ys)
              have hcoord :
                  (fun r : RoleScope => P.U W (P.groupOf r.1) (a (P.groupOf r.1))) =
                    (fun r : RoleScope => P.U W (P.groupOf r.1)
                      ((projectBins a) ⟨P.groupOf r.1, P.scopes_closed r.1 r.2⟩)) := by
                funext r
                rfl
              rw [hcoord] at hsub
              exact hsub
        _ = (FinLaw.bind (GroupLaw W) fun b => RoleLaw W b).E
              (fun ω => f ω.1 ω.2) := by
                rw [HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
                exact HypercubeRamsey.S16.Lane_q_s16_comp2.pi_subtype_expect
                  (fun g : P.Group => P.qraw W g) P.groupScope
                  (fun b => (RoleLaw W b).E (fun ys => f b ys))
    have hextendBin (a : P.Group → BinType) (g : P.Group) (hg : g ∈ P.groupScope) :
        extendBins (projectBins a) g = a g := by simp [extendBins, projectBins, hg]
    have hGoodProject (pool : F.Pool C) (a : P.Group → BinType) :
        GoodScope pool (projectBins a) ↔
          Set.InjOn a (P.groupScope : Set P.Group) ∧
            ∀ g ∈ P.groupScope, a g ∈ Finset.univ.image pool := by
      constructor
      · intro h
        constructor
        · intro x hx y hy hxy
          apply h.1 hx hy
          calc
            extendBins (projectBins a) x = a x := hextendBin a x hx
            _ = a y := hxy
            _ = extendBins (projectBins a) y := (hextendBin a y hy).symm
        · intro g hg
          simpa [hextendBin a g hg] using h.2 g hg
      · intro h
        constructor
        · intro x hx y hy hxy
          apply h.1 hx hy
          calc
            a x = extendBins (projectBins a) x := (hextendBin a x hx).symm
            _ = extendBins (projectBins a) y := hxy
            _ = a y := hextendBin a y hy
        · intro g hg
          simpa [hextendBin a g hg] using h.2 g hg
    have hpriorExt (W : P.LocalHist) (ys : P.Role → Label) :
        P.rawPrior W ys = P.rawPrior W (extendLabels (projectLabels ys)) := by
      apply P.prior_local
      intro r hr
      simp [extendLabels, projectLabels, hr]
    have hRawScoreProject (pool : F.Pool C) (W : P.LocalHist) :
        (P.rawLaw W).E (fun ω =>
          if GoodScope pool (projectBins ω.1) then
            Scale * Φ (P.rawPrior W ω.2) else 0) =
          Scale * (ScopeLaw W).E (fun ω => TestScope pool W ω.1 ω.2) := by
      have hTest (ω : (P.Group → BinType) × (P.Role → Label)) :
          (if GoodScope pool (projectBins ω.1) then
            Φ (P.rawPrior W ω.2) else 0) =
            TestScope pool W (projectBins ω.1) (projectLabels ω.2) := by
        by_cases hg : GoodScope pool (projectBins ω.1)
        · simp [TestScope, hg, hpriorExt W ω.2]
        · simp [TestScope, hg]
      calc
        (P.rawLaw W).E (fun ω =>
            if GoodScope pool (projectBins ω.1) then
              Scale * Φ (P.rawPrior W ω.2) else 0) =
          (P.rawLaw W).E (fun ω => Scale *
            (if GoodScope pool (projectBins ω.1) then
              Φ (P.rawPrior W ω.2) else 0)) := by
                apply congrArg
                funext ω
                by_cases hg : GoodScope pool (projectBins ω.1) <;> simp [hg]
        _ = Scale * (P.rawLaw W).E (fun ω =>
              if GoodScope pool (projectBins ω.1) then
                Φ (P.rawPrior W ω.2) else 0) :=
              HypercubeRamsey.S16.Lane_q_s16_comp2.expect_const_mul
                (P.rawLaw W) Scale _
        _ = Scale * (P.rawLaw W).E (fun ω =>
              TestScope pool W (projectBins ω.1) (projectLabels ω.2)) := by
                congr 1
                apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
                intro ω _
                exact hTest ω
        _ = Scale * (ScopeLaw W).E (fun ω => TestScope pool W ω.1 ω.2) := by
                rw [hRawLawProject W (fun b ys => TestScope pool W b ys)]
    have hFullGoodScore (pool : F.Pool C) (W : P.LocalHist)
        (ω : (P.Group → BinType) × (P.Role → Label)) :
        (if Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
              ∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool then
            Scale * Φ (P.rawPrior W ω.2) else 0) =
          (if GoodScope pool (projectBins ω.1) then
            Scale * Φ (P.rawPrior W ω.2) else 0) := by
      have hgood := hGoodProject pool ω.1
      by_cases h : Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
          ∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool
      · have hg : GoodScope pool (projectBins ω.1) := hgood.mpr h
        rw [if_pos h, if_pos hg]
      · have hn : ¬ GoodScope pool (projectBins ω.1) := fun hg => h (hgood.mp hg)
        rw [if_neg h, if_neg hn]
    have hRestrictedEq (pool : F.Pool C) :
        P.restrictedIntegral pool Φ =
          (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).E
            (fun W => Scale * (ScopeLaw W).E
              (fun ω => TestScope pool W ω.1 ω.2)) := by
      unfold FreshPriorPipeline.restrictedIntegral
      apply congrArg (fun f : P.LocalHist → ℝ =>
        (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).E f)
      funext W
      calc
        (P.rawLaw W).E (fun ω => if
            Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
              ∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool then
            Scale * Φ (P.rawPrior W ω.2) else 0) =
          (P.rawLaw W).E (fun ω => if GoodScope pool (projectBins ω.1) then
            Scale * Φ (P.rawPrior W ω.2) else 0) := by
              apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
              intro ω _
              exact hFullGoodScore pool W ω
        _ = Scale * (ScopeLaw W).E (fun ω => TestScope pool W ω.1 ω.2) :=
              hRawScoreProject pool W
    let LabelFactor : ℝ := Real.exp (P.labelRate * P.roleScope.card)
    let GroupFactor : ℝ := Real.exp (P.groupRate * P.groupScope.card)
    let RefLabelTest (W : P.LocalHist) (ys : RoleScope → Label) : ℝ :=
      Φ (P.rawPrior W (extendLabels ys))
    let RefLabelAverage (W : P.LocalHist) (b : GroupScope → BinType) : ℝ :=
      (RoleLaw W b).E (RefLabelTest W)
    let TestBin (pool : F.Pool C) (W : P.LocalHist)
        (b : GroupScope → BinType) : ℝ :=
      if GoodScope pool b then RefLabelAverage W b else 0
    let RawScore (W : P.LocalHist) : ℝ :=
      (P.rawLaw W).E (fun ω =>
        if GoodScope pool (projectBins ω.1) then
          Scale * Φ (P.rawPrior W ω.2) else 0)
    have hRefLabelAverageNonneg (W : P.LocalHist) (b : GroupScope → BinType) :
        0 ≤ RefLabelAverage W b := by
      calc
        0 = (RoleLaw W b).E (fun _ => 0) := by simp [FinLaw.E]
        _ ≤ (RoleLaw W b).E (RefLabelTest W) :=
          HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _
            (fun ys => hΦ (P.rawPrior W (extendLabels ys)))
    have hTestBinNonneg (W : P.LocalHist) (b : GroupScope → BinType) :
        0 ≤ TestBin pool W b := by
      dsimp [TestBin]
      split_ifs
      · exact hRefLabelAverageNonneg W b
      · exact le_rfl
    have hLabelBound (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (a : P.Group → BinType) (ha : (P.binSampler pool W).w a ≠ 0) :
        (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys)) ≤
          LabelFactor * RefLabelAverage W.1 (projectBins a) := by
      have hmap := HypercubeRamsey.S16.Lane_q_s16_comp2.expect_map_le
        (P.labelSampler pool W a) projectLabels (RoleLaw W.1 (projectBins a))
        LabelFactor (RefLabelTest W.1)
        (fun ys => hΦ (P.rawPrior W.1 (extendLabels ys)))
        (hLabelAtom W hW a ha)
      calc
        (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys)) =
            (P.labelSampler pool W a).E
              (fun ys => RefLabelTest W.1 (projectLabels ys)) := by
                apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
                intro ys _
                exact congrArg Φ (hpriorExt W.1 ys)
        _ ≤ LabelFactor * RefLabelAverage W.1 (projectBins a) := by
              simpa [LabelFactor, RefLabelAverage] using hmap
    have hScopeReference (W : P.LocalHist) :
        (ScopeLaw W).E (fun ω => TestScope pool W ω.1 ω.2) =
          (GroupLaw W).E (TestBin pool W) := by
      rw [HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
      apply congrArg
      funext b
      by_cases hg : GoodScope pool b
      · simp [TestScope, TestBin, RefLabelAverage, RefLabelTest, hg]
      · simp [TestScope, TestBin, RefLabelAverage, RefLabelTest, hg, FinLaw.E]
    have hRawScoreGroup (W : P.LocalHist) :
        RawScore W = Scale * (GroupLaw W).E (TestBin pool W) := by
      dsimp [RawScore]
      rw [hRawScoreProject pool W, hScopeReference W]
    have hRawScoreNonneg (W : P.LocalHist) : 0 ≤ RawScore W := by
      dsimp [RawScore, FinLaw.E]
      apply Finset.sum_nonneg
      intro ω hω
      apply mul_nonneg
      · exact (P.rawLaw W).nonneg ω
      · by_cases hg : GoodScope pool (projectBins ω.1)
        · simp only [if_pos hg]
          exact mul_nonneg (by dsimp [Scale]; positivity) (hΦ _)
        · rw [if_neg hg]
    have hGoodTestSupport (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0)
        (a : P.Group → BinType) (ha : (P.binSampler pool W).w a ≠ 0) :
        TestBin pool W.1 (projectBins a) = RefLabelAverage W.1 (projectBins a) := by
      simp [TestBin, hGoodSupport W hW a ha]
    have hBinPoint (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) (a : P.Group → BinType) :
        (if (P.binSampler pool W).w a = 0 then 0 else
          (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys))) ≤
          LabelFactor * TestBin pool W.1 (projectBins a) := by
      by_cases ha0 : (P.binSampler pool W).w a = 0
      · simp [ha0]
        exact mul_nonneg (Real.exp_pos _).le (hTestBinNonneg W.1 (projectBins a))
      · have hb := hLabelBound W hW a ha0
        rw [if_neg ha0, hGoodTestSupport W hW a ha0]
        exact hb
    have hBinExpectation (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) :
        (P.binSampler pool W).E (fun a =>
          (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys))) ≤
            LabelFactor * (P.binSampler pool W).E
              (fun a => TestBin pool W.1 (projectBins a)) := by
      calc
        (P.binSampler pool W).E (fun a =>
            (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys))) =
          (P.binSampler pool W).E (fun a =>
            if (P.binSampler pool W).w a = 0 then 0 else
              (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys))) := by
                apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
                intro a ha
                simp [ha]
        _ ≤ (P.binSampler pool W).E (fun a =>
              LabelFactor * TestBin pool W.1 (projectBins a)) :=
                HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _ (hBinPoint W hW)
        _ = LabelFactor * (P.binSampler pool W).E
              (fun a => TestBin pool W.1 (projectBins a)) := by
                calc
                  _ = LabelFactor * (P.binSampler pool W).E
                        (fun a => TestBin pool W.1 (projectBins a)) :=
                        HypercubeRamsey.S16.Lane_q_s16_comp2.expect_const_mul
                          (P.binSampler pool W) LabelFactor _
                  _ = _ := rfl
    have hGroupExpectation (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) :
        (P.binSampler pool W).E (fun a => TestBin pool W.1 (projectBins a)) ≤
          GroupFactor * (TildeGroupLaw W).E (TestBin pool W.1) :=
      HypercubeRamsey.S16.Lane_q_s16_comp2.expect_map_le
        (P.binSampler pool W) projectBins (TildeGroupLaw W) GroupFactor
        (TestBin pool W.1) (hTestBinNonneg W.1) (hGroupAtom W hW)
    have hTildeExpectation (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) :
        (TildeGroupLaw W).E (TestBin pool W.1) ≤
          AtomFactor ^ P.groupScope.card * (GroupLaw W.1).E (TestBin pool W.1) := by
      unfold FinLaw.E
      calc
        (∑ b, (TildeGroupLaw W).w b * TestBin pool W.1 b) ≤
            ∑ b, (AtomFactor ^ P.groupScope.card * (GroupLaw W.1).w b) *
              TestBin pool W.1 b := by
                apply Finset.sum_le_sum
                intro b hb
                exact mul_le_mul_of_nonneg_right (hTildeWeight W hW b)
                  (hTestBinNonneg W.1 b)
        _ = AtomFactor ^ P.groupScope.card *
              ∑ b, (GroupLaw W.1).w b * TestBin pool W.1 b := by
                calc
                  (∑ b, (AtomFactor ^ P.groupScope.card * (GroupLaw W.1).w b) *
                      TestBin pool W.1 b) =
                    ∑ b, AtomFactor ^ P.groupScope.card *
                      ((GroupLaw W.1).w b * TestBin pool W.1 b) := by
                        apply Finset.sum_congr rfl
                        intro b hb
                        ring
                  _ = _ := by rw [Finset.mul_sum]
    have hSamplerLocal (W : P.LocalHist × P.Aux)
        (hW : (P.gatedHistory pool).w W ≠ 0) :
        (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
          (fun ω => Φ (P.rawPrior W.1 ω.2)) ≤ LocalFactor * RawScore W.1 := by
      have hLabelFactor : 0 ≤ LabelFactor := (Real.exp_pos _).le
      have hGroupFactor : 0 ≤ GroupFactor := (Real.exp_pos _).le
      have hRates : LabelFactor * GroupFactor =
          Real.exp (P.groupRate * P.groupScope.card + P.labelRate * P.roleScope.card) := by
        dsimp [LabelFactor, GroupFactor]
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
            (fun ω => Φ (P.rawPrior W.1 ω.2)) =
          (P.binSampler pool W).E (fun a =>
            (P.labelSampler pool W a).E (fun ys => Φ (P.rawPrior W.1 ys))) :=
              HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect
                (P.binSampler pool W) (P.labelSampler pool W) _
        _ ≤ LabelFactor * (P.binSampler pool W).E
              (fun a => TestBin pool W.1 (projectBins a)) := hBinExpectation W hW
        _ ≤ LabelFactor * (GroupFactor * (TildeGroupLaw W).E (TestBin pool W.1)) :=
              mul_le_mul_of_nonneg_left (hGroupExpectation W hW) hLabelFactor
        _ ≤ LabelFactor * GroupFactor *
              (AtomFactor ^ P.groupScope.card * (GroupLaw W.1).E (TestBin pool W.1)) := by
                have h := hTildeExpectation W hW
                have hconst : 0 ≤ LabelFactor * GroupFactor := mul_nonneg hLabelFactor hGroupFactor
                calc
                  LabelFactor * (GroupFactor * (TildeGroupLaw W).E (TestBin pool W.1)) =
                      (LabelFactor * GroupFactor) * (TildeGroupLaw W).E (TestBin pool W.1) := by ring
                  _ ≤ (LabelFactor * GroupFactor) *
                        (AtomFactor ^ P.groupScope.card *
                          (GroupLaw W.1).E (TestBin pool W.1)) :=
                        mul_le_mul_of_nonneg_left h hconst
                  _ = _ := by ring
        _ = LocalFactor * RawScore W.1 := by
              rw [hAtomPower, hRates, hRawScoreGroup]
              dsimp [LocalFactor, preInv, permInv, epsInv]
              ring
    let BaseSliceLaw := FinLaw.cond P.baseHistory P.slicePass P.slice_pos
    let gateSet := P.gate pool
    let gatePos := P.gate_pos pool ht
    let gm : ℝ := ∑ W ∈ gateSet, P.history.w W
    have hGateError : P.δgate < 1 := P.error_ranges.1.2
    have hGateLower : 1 - P.δgate ≤ gm := by
      simpa [gm, gateSet] using P.gate_mass pool ht
    have hGatePos : 0 < gm := by
      simpa [gm, gateSet, gatePos] using gatePos
    have hGateLowerPos : 0 < 1 - P.δgate := by linarith
    have hGateInv : gm⁻¹ ≤ (1 - P.δgate)⁻¹ :=
      (inv_le_inv₀ hGatePos hGateLowerPos).2 hGateLower
    have hHistoryRawNonneg : 0 ≤ P.history.E (fun W => RawScore W.1) := by
      unfold FinLaw.E
      exact Finset.sum_nonneg fun W _ =>
        mul_nonneg (P.history.nonneg W) (hRawScoreNonneg W.1)
    have hGateNum : (∑ W ∈ gateSet,
        P.history.w W * RawScore W.1) ≤ P.history.E (fun W => RawScore W.1) := by
      unfold FinLaw.E
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by
          intro W hW hnot
          exact mul_nonneg (P.history.nonneg W) (hRawScoreNonneg W.1))
    have hGateForm : (FinLaw.cond P.history gateSet gatePos).E
        (fun W => RawScore W.1) =
        (∑ W ∈ gateSet, P.history.w W * RawScore W.1) / gm := by
      simp [FinLaw.E, FinLaw.cond, gateSet, gm, Finset.sum_div, Finset.sum_ite_mem,
        Finset.univ_inter, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W hW
      ring
    have hGateCondBound :
        (FinLaw.cond P.history gateSet gatePos).E
          (fun W => RawScore W.1) ≤
        (1 - P.δgate)⁻¹ * P.history.E (fun W => RawScore W.1) := by
      rw [hGateForm]
      calc
        (∑ W ∈ gateSet, P.history.w W * RawScore W.1) / gm ≤
            gm⁻¹ * P.history.E (fun W => RawScore W.1) := by
              rw [div_eq_mul_inv, mul_comm]
              exact mul_le_mul_of_nonneg_left hGateNum (inv_nonneg.mpr hGatePos.le)
        _ ≤ (1 - P.δgate)⁻¹ * P.history.E (fun W => RawScore W.1) :=
              mul_le_mul_of_nonneg_right hGateInv hHistoryRawNonneg
    have hGatedBound : (P.gatedHistory pool).E (fun W => RawScore W.1) ≤
        (1 - P.δgate)⁻¹ * P.history.E (fun W => RawScore W.1) := by
      rw [P.gated_eq pool ht]
      exact hGateCondBound
    have hAuxConstant (W : P.LocalHist) :
        P.auxHistory.E (fun _ => RawScore W) = RawScore W := by
      unfold FinLaw.E
      calc
        (∑ a, P.auxHistory.w a * RawScore W) =
            ∑ a, RawScore W * P.auxHistory.w a := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = RawScore W * ∑ a, P.auxHistory.w a := by rw [Finset.mul_sum]
        _ = RawScore W := by rw [P.auxHistory.sum_one]; ring
    have hHistoryAverage : P.history.E (fun W => RawScore W.1) =
        BaseSliceLaw.E (RawScore) := by
      rw [P.history_eq, HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
      apply congrArg
      funext W
      exact hAuxConstant W
    have hSliceScore : BaseSliceLaw.E RawScore = P.restrictedIntegral pool Φ := by
      calc
        BaseSliceLaw.E RawScore = BaseSliceLaw.E
            (fun W => Scale * (ScopeLaw W).E
              (fun ω => TestScope pool W ω.1 ω.2)) := by
                apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
                intro W _
                exact hRawScoreProject pool W
        _ = P.restrictedIntegral pool Φ := (hRestrictedEq pool).symm
    have hHistoryRestricted : P.history.E (fun W => RawScore W.1) =
        P.restrictedIntegral pool Φ := hHistoryAverage.trans hSliceScore
    have hGatePoint (W : P.LocalHist × P.Aux) :
        (if (P.gatedHistory pool).w W = 0 then 0 else
          (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
            (fun ω => Φ (P.rawPrior W.1 ω.2))) ≤ LocalFactor * RawScore W.1 := by
      by_cases hzero : (P.gatedHistory pool).w W = 0
      · simp [hzero]
        exact mul_nonneg hLocalNonneg (hRawScoreNonneg W.1)
      · rw [if_neg hzero]
        exact hSamplerLocal W hzero
    have hGatedSamplerBound :
        (P.gatedHistory pool).E (fun W =>
          (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
            (fun ω => Φ (P.rawPrior W.1 ω.2))) ≤
          LocalFactor * (P.gatedHistory pool).E (fun W => RawScore W.1) := by
      calc
        (P.gatedHistory pool).E (fun W =>
            (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
              (fun ω => Φ (P.rawPrior W.1 ω.2))) =
          (P.gatedHistory pool).E (fun W =>
            if (P.gatedHistory pool).w W = 0 then 0 else
              (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
                (fun ω => Φ (P.rawPrior W.1 ω.2))) := by
                  apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_congr_of_support
                  intro W hW
                  simp [hW]
        _ ≤ (P.gatedHistory pool).E (fun W => LocalFactor * RawScore W.1) :=
              HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _ hGatePoint
        _ = LocalFactor * (P.gatedHistory pool).E (fun W => RawScore W.1) :=
              HypercubeRamsey.S16.Lane_q_s16_comp2.expect_const_mul
                (P.gatedHistory pool) LocalFactor _
    rw [hRaw, HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
    calc
      (P.gatedHistory pool).E (fun W =>
          (FinLaw.bind (P.binSampler pool W) (P.labelSampler pool W)).E
            (fun ω => Φ (P.rawPrior W.1 ω.2))) ≤
        LocalFactor * (P.gatedHistory pool).E (fun W => RawScore W.1) := hGatedSamplerBound
      _ ≤ LocalFactor * ((1 - P.δgate)⁻¹ *
            P.history.E (fun W => RawScore W.1)) :=
          mul_le_mul_of_nonneg_left hGatedBound hLocalNonneg
      _ = StageFactor * P.restrictedIntegral pool Φ := by
            rw [hHistoryRestricted]
            dsimp [StageFactor, LocalFactor, preInv, permInv, epsInv]
            ring
  have hRestrictedNonneg (pool : F.Pool C) : 0 ≤ P.restrictedIntegral pool Φ := by
    have hScaleNonneg :
        0 ≤ ((Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) : ℝ) /
          H.geom.nslot C) ^ P.groupScope.card :=
      pow_nonneg (div_nonneg (by positivity)
        (by exact_mod_cast (Nat.zero_le (H.geom.nslot C)))) _
    unfold FreshPriorPipeline.restrictedIntegral FinLaw.E
    apply Finset.sum_nonneg
    intro W hW
    apply mul_nonneg
    · exact (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).nonneg W
    · apply Finset.sum_nonneg
      intro ω hω
      apply mul_nonneg
      · exact (P.rawLaw W).nonneg ω
      · simp only [Finset.mem_image, Finset.mem_univ, true_and] at ⊢
        change 0 ≤ if Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
            (∀ g ∈ P.groupScope, ∃ b, pool b = ω.1 g) then
              ((Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) : ℝ) /
                H.geom.nslot C) ^ P.groupScope.card * Φ (P.rawPrior W ω.2) else 0
        by_cases hg : Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
            (∀ g ∈ P.groupScope, ∃ b, pool b = ω.1 g)
        · rw [if_pos hg]
          exact mul_nonneg hScaleNonneg (hΦ _)
        · rw [if_neg hg]
  have hPoint : ∀ pool,
      (if F.typical C pool then
        (F.fresh C pool).E (fun s => Φ (F.prior C s v)) else 0) ≤
        StageFactor * P.restrictedIntegral pool Φ := by
    intro pool
    by_cases ht : F.typical C pool
    · simpa [ht] using hPoolBound pool ht
    · simp [ht]
      exact mul_nonneg hStageNonneg (hRestrictedNonneg pool)
  have hIidNonneg : 0 ≤ P.iidRestrictedIntegral (hBins C) Φ := by
    unfold FreshPriorPipeline.iidRestrictedIntegral
    calc
      0 = (iidCellPoolLaw (G := H.geom) C (hBins C)).E (fun _ => 0) := by simp [FinLaw.E]
      _ ≤ (iidCellPoolLaw (G := H.geom) C (hBins C)).E
            (fun pool => P.restrictedIntegral pool Φ) :=
          HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _
            (fun pool => hRestrictedNonneg pool)
  unfold freshPriorTest
  calc
    (iidCellPoolLaw (G := H.geom) C (hBins C)).E (fun pool =>
        if F.typical C pool then
          (F.fresh C pool).E (fun s => Φ (F.prior C s v)) else 0) ≤
      (iidCellPoolLaw (G := H.geom) C (hBins C)).E
        (fun pool => StageFactor * P.restrictedIntegral pool Φ) :=
          HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le _ _ _ hPoint
    _ = StageFactor * P.iidRestrictedIntegral (hBins C) Φ := by
          unfold FreshPriorPipeline.iidRestrictedIntegral
          exact HypercubeRamsey.S16.Lane_q_s16_comp2.expect_const_mul
            (iidCellPoolLaw (G := H.geom) C (hBins C)) StageFactor
            (fun pool => P.restrictedIntegral pool Φ)
    _ ≤ (10 * κ.Kcell) * P.iidRestrictedIntegral (hBins C) Φ :=
          mul_le_mul_of_nonneg_right P.stage_cost hIidNonneg

/-- Unforced iid slots contain m distinct targets with probability at most
(L/B)^m. The statement includes the empty set and excludes an own-pool pin. -/
theorem iid_distinct_bin_containment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty) :
    ∀ targets : Finset (Bin PT.tiling (G.cellPatch C)),
      (iidCellPoolLaw (G := G) C hBins).pr (fun pool => targets ⊆ Finset.univ.image pool) ≤
        ((G.nslot C : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C))) ^ targets.card := by
  classical
  intro targets
  let Slot := Fin (G.nslot C)
  let BinType := Bin PT.tiling (G.cellPatch C)
  let Targets := {D : BinType // D ∈ targets}
  have hBinNonempty : Nonempty BinType := by
    rcases hBins with ⟨D, hD⟩
    exact ⟨D⟩
  have hcover (pool : Slot → BinType) :
      targets ⊆ Finset.univ.image pool ↔
        ∃ e : Targets ↪ Slot, ∀ t, pool (e t) = t.1 := by
    constructor
    · intro h
      have hex (t : Targets) : ∃ s : Slot, pool s = t.1 := by
        have ht : t.1 ∈ Finset.univ.image pool := h t.2
        rcases Finset.mem_image.mp ht with ⟨s, hs, hsp⟩
        exact ⟨s, hsp⟩
      choose f hf using hex
      have hfi : Function.Injective f := by
        intro t u htu
        apply Subtype.ext
        calc
          t.1 = pool (f t) := (hf t).symm
          _ = pool (f u) := congrArg pool htu
          _ = u.1 := hf u
      exact ⟨⟨f, hfi⟩, hf⟩
    · rintro ⟨e, he⟩ D hD
      exact Finset.mem_image.mpr ⟨e ⟨D, hD⟩, Finset.mem_univ _, he ⟨D, hD⟩⟩
  have hcardEmb (e : Targets ↪ Slot) :
      (Finset.univ.image (fun t : Targets => e t)).card = targets.card := by
    rw [Finset.card_image_of_injective Finset.univ e.injective]
    simp [Targets]
  have hprEmb (e : Targets ↪ Slot) :
      (iidCellPoolLaw (G := G) C hBins).pr
        (fun pool => ∀ t : Targets, pool (e t) = t.1) =
          (1 / (Fintype.card BinType : ℝ)) ^ targets.card := by
    let S : Finset Slot := Finset.univ.image (fun t : Targets => e t)
    have hsource : ∀ s : Slot, s ∈ S → ∃ t : Targets, e t = s := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
      exact ⟨t, hts⟩
    choose pick hpick using hsource
    let x : Slot → BinType := fun s => if hs : s ∈ S then (pick s hs).1 else Classical.choice hBinNonempty
    have hxe (t : Targets) : x (e t) = t.1 := by
      have hs : e t ∈ S := by simp [S]
      dsimp [x]
      rw [dif_pos hs]
      exact congrArg Subtype.val (e.injective (hpick (e t) hs))
    have hevent (pool : Slot → BinType) :
        (∀ t : Targets, pool (e t) = t.1) ↔ ∀ s ∈ S, pool s = x s := by
      constructor
      · intro h s hs
        calc
          pool s = pool (e (pick s hs)) := congrArg pool (hpick s hs).symm
          _ = (pick s hs).1 := h (pick s hs)
          _ = x s := by simp [x, hs]
      · intro h t
        calc
          pool (e t) = x (e t) := h (e t) (by simp [S])
          _ = t.1 := hxe t
    have hS : S.card = targets.card := hcardEmb e
    rw [show (fun pool : Slot → BinType => ∀ t : Targets, pool (e t) = t.1) =
      (fun pool => ∀ s ∈ S, pool s = x s) from funext fun pool => propext (hevent pool)]
    change (FinLaw.pi (fun _ : Slot =>
      FinLaw.uniform (Finset.univ : Finset BinType) hBins)).pr _ = _
    rw [HypercubeRamsey.S16.Lane_q_s16_comp2.pi_pr_cylinder]
    simp [iidCellPoolLaw, FinLaw.uniform, Finset.mem_univ, Finset.prod_const, hS]
  have hfunCard : Fintype.card (Targets → Slot) = G.nslot C ^ targets.card := by
    simp [Slot, Targets, Fintype.card_coe]
  have hEmbedCard :
      (Fintype.card (Targets ↪ Slot) : ℝ) ≤ (G.nslot C : ℝ) ^ targets.card := by
    have hle : Fintype.card (Targets ↪ Slot) ≤ Fintype.card (Targets → Slot) :=
      Fintype.card_le_of_injective (fun e : Targets ↪ Slot => (e : Targets → Slot))
        (by
          intro e₁ e₂ h
          apply Function.Embedding.ext
          intro t
          exact congrFun h t)
    rw [hfunCard] at hle
    exact_mod_cast hle
  calc
    (iidCellPoolLaw (G := G) C hBins).pr
        (fun pool => targets ⊆ Finset.univ.image pool) ≤
      ∑ e : Targets ↪ Slot,
        (iidCellPoolLaw (G := G) C hBins).pr
          (fun pool => ∀ t : Targets, pool (e t) = t.1) := by
            have hEq : (fun pool : Slot → BinType => targets ⊆ Finset.univ.image pool) =
                (fun pool => ∃ e : Targets ↪ Slot, ∀ t, pool (e t) = t.1) :=
              funext fun pool => propext (hcover pool)
            rw [hEq]
            exact HypercubeRamsey.S16.Lane_q_s16_comp2.pr_exists_le_sum _ _
    _ ≤ (Fintype.card (Targets ↪ Slot) : ℝ) *
        (1 / (Fintype.card BinType : ℝ)) ^ targets.card := by
          calc
            _ ≤ ∑ e : Targets ↪ Slot,
                (1 / (Fintype.card BinType : ℝ)) ^ targets.card :=
                  Finset.sum_le_sum fun e he => (hprEmb e).le
            _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (G.nslot C : ℝ) ^ targets.card *
        (1 / (Fintype.card BinType : ℝ)) ^ targets.card :=
          mul_le_mul_of_nonneg_right hEmbedCard (by positivity)
    _ = ((G.nslot C : ℝ) / Fintype.card BinType) ^ targets.card := by
          have hBne : (Fintype.card BinType : ℝ) ≠ 0 := by
            exact_mod_cast (Finset.card_pos.mpr hBins).ne'
          field_simp [hBne]
          ring

/-- The containment calculation cancels precisely the retained restriction factors. -/
theorem iid_prior_containment_cancellation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
    (P : FreshPriorPipeline F C v)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (hContain : ∀ targets : Finset (Bin PT.tiling (G.cellPatch C)),
      (iidCellPoolLaw (G := G) C hBins).pr (fun pool => targets ⊆ Finset.univ.image pool) ≤
        ((G.nslot C : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C))) ^ targets.card)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) :
    P.iidRestrictedIntegral hBins Φ ≤ P.sliceExperiment.expect Φ := by
  classical
  let BinType := Bin PT.tiling (G.cellPatch C)
  let PoolLaw := iidCellPoolLaw (G := G) C hBins
  let HistLaw := FinLaw.cond P.baseHistory P.slicePass P.slice_pos
  let B : ℝ := Fintype.card BinType
  let L : ℝ := G.nslot C
  let c : ℝ := B / L
  let m : ℕ := P.groupScope.card
  let Good (pool : F.Pool C)
      (ω : (P.Group → BinType) × (P.Role → Fin (T.S.N k))) : Prop :=
    Set.InjOn ω.1 (P.groupScope : Set P.Group) ∧
      ∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool
  let Test (W : P.LocalHist)
      (ω : (P.Group → BinType) × (P.Role → Fin (T.S.N k))) : ℝ :=
    Φ (P.rawPrior W ω.2)
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast P.slot_pos
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast Finset.card_pos.mpr hBins
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hBne : B ≠ 0 := ne_of_gt hB
  have hLne : L ≠ 0 := ne_of_gt hL
  have hcancel : c ^ m * (L / B) ^ m = 1 := by
    have hunit : c * (L / B) = 1 := by
      dsimp [c]
      field_simp [hBne, hLne]
    rw [← mul_pow, hunit, one_pow]
  have hPoolBound (W : P.LocalHist)
      (ω : (P.Group → BinType) × (P.Role → Fin (T.S.N k))) :
      PoolLaw.E (fun pool => if Good pool ω then c ^ m * Test W ω else 0) ≤ Test W ω := by
    by_cases hinj : Set.InjOn ω.1 (P.groupScope : Set P.Group)
    · let targets := P.groupScope.image ω.1
      have hevent (pool : F.Pool C) :
          (∀ g ∈ P.groupScope, ω.1 g ∈ Finset.univ.image pool) ↔
            targets ⊆ Finset.univ.image pool := by
        constructor
        · intro h D hD
          rcases Finset.mem_image.mp hD with ⟨g, hg, rfl⟩
          exact h g hg
        · intro h g hg
          have htg : ω.1 g ∈ targets := by
            exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
          exact h htg
      have hcard : targets.card = P.groupScope.card := by
        dsimp [targets]
        exact Finset.card_image_of_injOn (s := P.groupScope) (f := ω.1) hinj
      have hprob : PoolLaw.pr (fun pool => Good pool ω) ≤ (L / B) ^ m := by
        have hsub : ∀ pool, Good pool ω → targets ⊆ Finset.univ.image pool := by
          intro pool hg
          exact (hevent pool).mp hg.2
        have hmono := HypercubeRamsey.S16.Lane_q_s16_comp2.pr_mono
          PoolLaw (fun pool => Good pool ω)
            (fun pool => targets ⊆ Finset.univ.image pool) hsub
        have htarget := hContain targets
        dsimp [L, B, BinType, m] at htarget ⊢
        rw [← hcard]
        exact hmono.trans htarget
      have hExp : PoolLaw.E (fun pool => if Good pool ω then c ^ m * Test W ω else 0) =
          (c ^ m * Test W ω) * PoolLaw.pr (fun pool => Good pool ω) := by
        unfold FinLaw.E FinLaw.pr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pool hp
        by_cases hg : Good pool ω
        · simp [hg]
          ring
        · simp [hg]
      have hcoeff : c ^ m * PoolLaw.pr (fun pool => Good pool ω) ≤ 1 := by
        calc
          c ^ m * PoolLaw.pr (fun pool => Good pool ω) ≤ c ^ m * (L / B) ^ m :=
            mul_le_mul_of_nonneg_left hprob (pow_nonneg hc _)
          _ = 1 := hcancel
      rw [hExp]
      calc
        (c ^ m * Test W ω) * PoolLaw.pr (fun pool => Good pool ω) =
            Test W ω * (c ^ m * PoolLaw.pr (fun pool => Good pool ω)) := by ring
        _ ≤ Test W ω * 1 := mul_le_mul_of_nonneg_left hcoeff (hΦ _)
        _ = Test W ω := by ring
    · have hzero : PoolLaw.E
          (fun pool => if Good pool ω then c ^ m * Test W ω else 0) = 0 := by
            unfold FinLaw.E
            apply Finset.sum_eq_zero
            intro pool hp
            have hnot : ¬ Good pool ω := fun hg => hinj hg.1
            simp [hnot]
      rw [hzero]
      exact hΦ _
  have hrewrite : P.iidRestrictedIntegral hBins Φ =
      HistLaw.E (fun W => (P.rawLaw W).E (fun ω =>
        PoolLaw.E (fun pool => if Good pool ω then c ^ m * Test W ω else 0))) := by
    change PoolLaw.E (fun pool => HistLaw.E (fun W =>
      (P.rawLaw W).E (fun ω => if Good pool ω then c ^ m * Test W ω else 0))) = _
    calc
      _ = HistLaw.E (fun W => PoolLaw.E (fun pool =>
            (P.rawLaw W).E (fun ω => if Good pool ω then c ^ m * Test W ω else 0))) :=
          HypercubeRamsey.S16.Lane_q_s16_comp2.expect_indep_comm PoolLaw HistLaw
            (fun pool W => (P.rawLaw W).E (fun ω =>
              if Good pool ω then c ^ m * Test W ω else 0))
      _ = HistLaw.E (fun W => (P.rawLaw W).E (fun ω =>
            PoolLaw.E (fun pool => if Good pool ω then c ^ m * Test W ω else 0))) := by
          apply congrArg
          funext W
          exact HypercubeRamsey.S16.Lane_q_s16_comp2.expect_indep_comm PoolLaw
            (P.rawLaw W) (fun pool ω => if Good pool ω then c ^ m * Test W ω else 0)
  have hslice : HistLaw.E (fun W => (P.rawLaw W).E (fun ω => Test W ω)) =
      P.sliceExperiment.expect Φ := by
    symm
    change (FinLaw.bind HistLaw (fun W => P.rawLaw W)).E
      (fun ω => Φ (P.rawPrior ω.1 ω.2.2)) =
        HistLaw.E (fun W => (P.rawLaw W).E (fun ω => Test W ω))
    rw [HypercubeRamsey.S16.Lane_q_s16_comp2.bind_expect]
  rw [hrewrite]
  calc
    HistLaw.E (fun W => (P.rawLaw W).E (fun ω =>
        PoolLaw.E (fun pool => if Good pool ω then c ^ m * Test W ω else 0))) ≤
      HistLaw.E (fun W => (P.rawLaw W).E (fun ω => Test W ω)) := by
        apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le
        intro W
        apply HypercubeRamsey.S16.Lane_q_s16_comp2.expect_le
        intro ω
        exact hPoolBound W ω
    _ = P.sliceExperiment.expect Φ := hslice

/-- Remove only the local slice's conditioning; other slice histories have
already integrated out. The primitive slice mass supplies its cost. -/
theorem slice_prior_conditioning_cost {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
    (P : FreshPriorPipeline F C v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) :
    P.sliceExperiment.expect Φ ≤ (10 * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ := by
  classical
  let f : P.LocalHist → ℝ := fun W =>
    (P.rawLaw W).E (fun ω => Φ (P.rawPrior W ω.2))
  have hf : ∀ W, 0 ≤ f W := by
    intro W
    dsimp [f, FinLaw.E]
    exact Finset.sum_nonneg fun ω _ => mul_nonneg ((P.rawLaw W).nonneg ω) (hΦ _)
  have hslice : P.sliceExperiment.expect Φ =
      (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).E f := by
    change (FinLaw.bind (FinLaw.cond P.baseHistory P.slicePass P.slice_pos)
        (fun W => P.rawLaw W)).E (fun ω => Φ (P.rawPrior ω.1 ω.2.2)) = _
    simp only [FinLaw.E, FinLaw.bind]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro W hW
    simp only [f, FinLaw.E]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hbase : P.baseExperiment.expect Φ = P.baseHistory.E f := by
    change (FinLaw.bind P.baseHistory (P.rawLaw)).E
        (fun ω => Φ (P.rawPrior ω.1 ω.2.2)) = _
    simp only [FinLaw.E, FinLaw.bind]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro W hW
    simp only [f, FinLaw.E]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hcond : (FinLaw.cond P.baseHistory P.slicePass P.slice_pos).E f =
      (∑ W ∈ P.slicePass, P.baseHistory.w W * f W) /
        (∑ W ∈ P.slicePass, P.baseHistory.w W) := by
    simp [FinLaw.E, FinLaw.cond, Finset.sum_div, Finset.sum_ite_mem,
      Finset.univ_inter, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.mul_sum]
  have hnum : (∑ W ∈ P.slicePass, P.baseHistory.w W * f W) ≤
      P.baseHistory.E f := by
    rw [FinLaw.E]
    calc
      (∑ W ∈ P.slicePass, P.baseHistory.w W * f W) ≤
          ∑ W ∈ Finset.univ, P.baseHistory.w W * f W := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (by intro W hW hnot; exact mul_nonneg (P.baseHistory.nonneg W) (hf W))
      _ = ∑ W, P.baseHistory.w W * f W := rfl
  have hcost := P.slice_cost
  have hmasspos : 0 < ∑ W ∈ P.slicePass, P.baseHistory.w W := P.slice_pos
  have hbaseNonneg : 0 ≤ P.baseHistory.E f := by
    unfold FinLaw.E
    exact Finset.sum_nonneg fun W _ => mul_nonneg (P.baseHistory.nonneg W) (hf W)
  rw [hslice, hcond, hbase]
  calc
    (∑ W ∈ P.slicePass, P.baseHistory.w W * f W) /
        (∑ W ∈ P.slicePass, P.baseHistory.w W) ≤
      (∑ W ∈ P.slicePass, P.baseHistory.w W)⁻¹ * P.baseHistory.E f := by
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hmasspos.le)
    _ ≤ (10 * (κ.Kp : ℝ)) * P.baseHistory.E f := by
        exact mul_le_mul_of_nonneg_right hcost hbaseNonneg

/-- L16.7b assembly on the same experiment throughout. -/
theorem iid_slot_prior_cancellation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
    (P : FreshPriorPipeline F C v)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) :
    P.iidRestrictedIntegral hBins Φ ≤ (10 * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ := by
  exact (iid_prior_containment_cancellation P hBins (iid_distinct_bin_containment C hBins) Φ hΦ).trans
    (slice_prior_conditioning_cost P Φ hΦ)

/-- L16.7: fresh versus the raw unrestricted experiment constructed from
these same kernels. No arbitrary intermediate or base law is quantified. -/
theorem fresh_internal_prior_comparison {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    {F : FreshCell H.geom} (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty)
    (C : H.geom.Cell) (v : Pos T k) (hcell : H.geom.cellOf v = C) (hEven : IsEvenRole v)
    (P : FreshPriorPipeline F C v) (hSource : FreshPriorSourceValid P)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) (hΦ0 : Φ 0 = 0) :
    freshPriorTest F hBins C v hcell hEven Φ ≤
      (100 * κ.Kcell * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ := by
  have hStage := fresh_prior_stage_comparison hκ Q H hBins C v hcell hEven P hSource Φ hΦ hΦ0
  have hSlots := iid_slot_prior_cancellation P (hBins C) Φ hΦ
  have hKcell : 0 < κ.Kcell := by
    have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
    exact lt_of_lt_of_le (by positivity) hκ.Kcell_big
  calc
    freshPriorTest F hBins C v hcell hEven Φ ≤ (10 * κ.Kcell) * P.iidRestrictedIntegral (hBins C) Φ := hStage
    _ ≤ (10 * κ.Kcell) * ((10 * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ) :=
      mul_le_mul_of_nonneg_left hSlots (by positivity)
    _ = (100 * κ.Kcell * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ := by ring

end HypercubeRamsey.S16
