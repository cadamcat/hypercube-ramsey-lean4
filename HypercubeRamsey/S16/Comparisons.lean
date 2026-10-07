import HypercubeRamsey.S16.Calibrations

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
  sorry

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
  sorry

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
  sorry

/-- Unforced iid slots contain m distinct targets with probability at most
(L/B)^m. The statement includes the empty set and excludes an own-pool pin. -/
theorem iid_distinct_bin_containment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty) :
    ∀ targets : Finset (Bin PT.tiling (G.cellPatch C)),
      (iidCellPoolLaw (G := G) C hBins).pr (fun pool => targets ⊆ Finset.univ.image pool) ≤
        ((G.nslot C : ℝ) / Fintype.card (Bin PT.tiling (G.cellPatch C))) ^ targets.card := by
  sorry

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
  sorry

/-- Remove only the local slice's conditioning; other slice histories have
already integrated out. The primitive slice mass supplies its cost. -/
theorem slice_prior_conditioning_cost {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} {C : G.Cell} {v : Pos T k}
    (P : FreshPriorPipeline F C v)
    (Φ : (Fin (T.S.N k) → ℝ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) :
    P.sliceExperiment.expect Φ ≤ (10 * (κ.Kp : ℝ)) * P.baseExperiment.expect Φ := by
  sorry

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
