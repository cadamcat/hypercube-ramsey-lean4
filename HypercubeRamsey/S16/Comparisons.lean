import HypercubeRamsey.S16.Calibrations
import HypercubeRamsey.S16.Comparisons_q_s16_comp1

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
  classical
  let α : ℝ := P.cperm * P.n
  let δ : ℝ := Real.exp (-α)
  let badLabels : Incidence → Finset Label := fun inc =>
    Finset.univ.filter fun y => δ < P.badMass inc y
  let removed (g : Group) : Finset Bin := Finset.univ \ P.permitted g
  let incs (g : Group) := permissionIncidences P g
  let badBins (g : Group) : Finset Bin :=
    (incs g).biUnion fun inc => (badLabels inc).biUnion (binsContainingLabel P)
  have hα : 0 < α := by dsimp [α]; exact mul_pos P.cperm_pos (Nat.cast_pos.mpr P.n_pos)
  have hδ : 0 < δ := Real.exp_pos _
  have hB : 0 < (Fintype.card Bin : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hInput.bins_nonempty
  have hbadLabel_card (inc : Incidence) :
      ((badLabels inc).card : ℝ) ≤ Real.exp (-2 * α) * Fintype.card Label := by
    have hsumLower : ((badLabels inc).card : ℝ) * δ ≤ ∑ y, P.badMass inc y := by
      calc
        ((badLabels inc).card : ℝ) * δ = ∑ y ∈ badLabels inc, δ := by simp [Finset.sum_const]
        _ ≤ ∑ y ∈ badLabels inc, P.badMass inc y := by
          apply Finset.sum_le_sum
          intro y hy
          exact (Finset.mem_filter.mp hy).2.le
        _ ≤ ∑ y, P.badMass inc y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
            intro y _ _
            exact (hInput.mean_bad_mass inc y).1)
    have hbound := hsumLower.trans (hInput.average_bad_mass inc)
    have hbound' : ((badLabels inc).card : ℝ) * δ ≤
        Real.exp (-3 * α) * Fintype.card Label := by
      calc
        _ ≤ Real.exp (-3 * P.cperm * P.n) * Fintype.card Label := hbound
        _ = Real.exp (-3 * α) * Fintype.card Label := by
          congr 1
          dsimp [α]
          ring
    have hdiv : ((badLabels inc).card : ℝ) ≤
        (Real.exp (-3 * α) * Fintype.card Label) / δ :=
      (le_div_iff₀ hδ).2 hbound'
    calc
      _ ≤ (Real.exp (-3 * α) * Fintype.card Label) / δ := hdiv
      _ = Real.exp (-2 * α) * Fintype.card Label := by
        dsimp [δ]
        have he : Real.exp (-3 * α) / Real.exp (-α) = Real.exp (-2 * α) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        rw [show (Real.exp (-3 * α) * Fintype.card Label) / Real.exp (-α) =
          (Real.exp (-3 * α) / Real.exp (-α)) * Fintype.card Label by ring, he]
  have hbadBins_card (g : Group) :
      (badBins g).card ≤ ∑ inc ∈ incs g, ∑ y ∈ badLabels inc,
        (binsContainingLabel P y).card := by
    calc
      _ ≤ ∑ inc ∈ incs g, ((badLabels inc).biUnion (binsContainingLabel P)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ inc ∈ incs g, ∑ y ∈ badLabels inc, (binsContainingLabel P y).card := by
        apply Finset.sum_le_sum
        intro inc _
        exact Finset.card_biUnion_le
  have hbadBins_cast (g : Group) :
      ((badBins g).card : ℝ) ≤
        ∑ inc ∈ incs g, ∑ y ∈ badLabels inc,
          ((binsContainingLabel P y).card : ℝ) := by
    simpa only [Nat.cast_sum] using
      (Nat.cast_le.mpr (hbadBins_card g) :
        ((badBins g).card : ℝ) ≤
          ((∑ inc ∈ incs g, ∑ y ∈ badLabels inc,
            (binsContainingLabel P y).card : ℕ) : ℝ))
  have hbadBins_real (g : Group) :
      ((badBins g).card : ℝ) ≤ (incs g).card *
        (Real.exp (-2 * α) * Fintype.card Label) := by
    calc
      ((badBins g).card : ℝ) ≤
          ∑ inc ∈ incs g, ∑ y ∈ badLabels inc,
            ((binsContainingLabel P y).card : ℝ) := by
        exact hbadBins_cast g
      _ ≤ ∑ inc ∈ incs g, ∑ y ∈ badLabels inc, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro inc _
        apply Finset.sum_le_sum
        intro y _
        exact_mod_cast hInput.labels_disjoint y
      _ = ∑ inc ∈ incs g, ((badLabels inc).card : ℝ) := by simp
      _ ≤ ∑ inc ∈ incs g, (Real.exp (-2 * α) * Fintype.card Label) := by
        apply Finset.sum_le_sum
        intro inc _
        exact hbadLabel_card inc
      _ = (incs g).card * (Real.exp (-2 * α) * Fintype.card Label) := by simp
  have hremoved_subset (g : Group) : removed g ⊆ badBins g := by
    intro D hD
    have hnperm : D ∉ P.permitted g := (Finset.mem_sdiff.mp hD).2
    have hnot := hnperm
    rw [P.permitted_iff] at hnot
    push_neg at hnot
    obtain ⟨inc, hinc, y, hy, hbad⟩ := hnot
    have hinc' : inc ∈ incs g := by simp [incs, permissionIncidences, hinc]
    have hdelta : δ = Real.exp (-P.cperm * P.n) := by
      dsimp [δ, α]
      congr 1
      ring
    have hy' : y ∈ badLabels inc := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [hdelta]; exact hbad⟩
    have hD' : D ∈ binsContainingLabel P y := by simp [binsContainingLabel, hy]
    exact Finset.mem_biUnion.mpr ⟨inc, hinc', Finset.mem_biUnion.mpr ⟨y, hy', hD'⟩⟩
  have hremoved_ratio (g : Group) :
      ((removed g).card : ℝ) / Fintype.card Bin ≤ Real.exp (-α) := by
    have hcard : ((removed g).card : ℝ) ≤
        (incs g).card * (Real.exp (-2 * α) * Fintype.card Label) :=
      (Nat.cast_le.mpr (Finset.card_le_card (hremoved_subset g))).trans (hbadBins_real g)
    calc
      ((removed g).card : ℝ) / Fintype.card Bin ≤
          ((incs g).card * (Real.exp (-2 * α) * Fintype.card Label)) / Fintype.card Bin :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = ((incs g).card * (Fintype.card Label / Fintype.card Bin)) * Real.exp (-2 * α) := by ring
      _ ≤ Real.exp (α) * Real.exp (-2 * α) := by
        exact mul_le_mul_of_nonneg_right (hInput.incidence_label_ratio g)
          (Real.exp_pos _).le
      _ = Real.exp (-α) := by rw [← Real.exp_add]; congr 1; ring
  have hremoved_mass (g : Group) :
      ∑ D ∈ removed g, (qin g).w D ≤ Real.exp (-(α / 2)) := by
    calc
      _ ≤ ∑ D ∈ removed g, Real.exp (α / 2) / Fintype.card Bin := by
        apply Finset.sum_le_sum
        intro D hD
        simpa [α] using hInput.incoming_cap g D
      _ = (removed g).card * (Real.exp (α / 2) / Fintype.card Bin) := by simp
      _ = ((removed g).card / Fintype.card Bin) * Real.exp (α / 2) := by ring
      _ ≤ Real.exp (-α) * Real.exp (α / 2) :=
        mul_le_mul_of_nonneg_right (hremoved_ratio g) (Real.exp_pos _).le
      _ = Real.exp (-(α / 2)) := by rw [← Real.exp_add]; congr 1; ring
  have hcover (g : Group) : P.permitted g ∪ removed g = Finset.univ := by
    ext D
    simp [removed]
  have hdisjoint (g : Group) : Disjoint (P.permitted g) (removed g) := by
    change Disjoint (P.permitted g) (Finset.univ \ P.permitted g)
    exact Finset.disjoint_sdiff
  have hmass_split (g : Group) :
      (∑ D ∈ P.permitted g, (qin g).w D) +
        (∑ D ∈ removed g, (qin g).w D) = 1 := by
    calc
      _ = ∑ D ∈ P.permitted g ∪ removed g, (qin g).w D :=
        (Finset.sum_union (hdisjoint g)).symm
      _ = ∑ D, (qin g).w D := by rw [hcover g]
      _ = 1 := (qin g).sum_one
  have hpermitted_mass (g : Group) :
      1 - Real.exp (-(α / 2)) ≤ ∑ D ∈ P.permitted g, (qin g).w D := by
    have hs := hmass_split g
    have hr := hremoved_mass g
    linarith
  have hcard_split (g : Group) :
      ((P.permitted g).card : ℝ) + (removed g).card = Fintype.card Bin := by
    have hc := Finset.card_union_of_disjoint (hdisjoint g)
    rw [hcover g, Finset.card_univ] at hc
    exact_mod_cast hc.symm
  have hpermitted_card (g : Group) :
      (1 - Real.exp (-(α / 2))) * Fintype.card Bin ≤ (P.permitted g).card := by
    have hnum : ((P.permitted g).card : ℝ) =
        (Fintype.card Bin : ℝ) - (removed g).card := by
      linarith [hcard_split g]
    have hfrac : ((P.permitted g).card : ℝ) / (Fintype.card Bin : ℝ) =
        1 - (removed g).card / (Fintype.card Bin : ℝ) := by
      have hden : (Fintype.card Bin : ℝ) ≠ 0 := ne_of_gt hB
      calc
        _ = ((Fintype.card Bin : ℝ) - (removed g).card) / (Fintype.card Bin : ℝ) := by rw [hnum]
        _ = 1 - (removed g).card / (Fintype.card Bin : ℝ) := by
          field_simp [hden]
          <;> ring
    have hexp : Real.exp (-α) ≤ Real.exp (-(α / 2)) :=
      Real.exp_le_exp.mpr (by linarith [le_of_lt hα])
    have hf := hremoved_ratio g
    have hlow : 1 - Real.exp (-(α / 2)) ≤
        ((P.permitted g).card : ℝ) / (Fintype.card Bin : ℝ) := by
      rw [hfrac]
      linarith
    exact (le_div_iff₀ hB).mp hlow
  have he : P.cperm / 2 * P.n = α / 2 := by dsimp [α]; ring
  have hcpermhalf : 0 < P.cperm / 2 := div_pos P.cperm_pos (by norm_num)
  refine ⟨P.cperm / 2, hcpermhalf, ?_, ?_⟩
  · intro g
    simpa [he] using hpermitted_card g
  · intro g
    simpa [he] using hpermitted_mass g

/-- L16.2b: independent-slot concentration, including a genuine iid pin.
Permission and geometry assumptions belong to the producer of the diagnostic
means/sensitivities; they are not unused arguments of this analytic lemma. -/
theorem pool_typicality_concentration_after_permission {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (hD : PoolConcentrationHypotheses D) :
    D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0) / 2 ∧
    ∀ s b, (D.pinLaw s b).pr (fun pool => ¬ D.typical pool) ≤ Real.exp (-(n : ℝ) ^ c0) / 2 := by
  classical
  let ε : ℝ := Real.exp (-(n : ℝ) ^ c0)
  let K : ℝ := max 1 (Fintype.card Check : ℝ)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKcard : (Fintype.card Check : ℝ) ≤ K := by dsimp [K]; exact le_max_right _ _
  have hBpos : 0 < (Fintype.card Bin : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr D.bins_nonempty
  have hNpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD.n_large)
  have hrpow : 0 < (n : ℝ) ^ c0 := Real.rpow_pos_of_pos hNpos c0
  have hεpos : 0 < ε := Real.exp_pos _
  have hεlt : ε < 1 := by
    dsimp [ε]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  let pinLaws (s : Slot) (b : Bin) : Slot → FinLaw Bin := fun t =>
    if t = s then FinLaw.dirac b else D.iidSlotLaw t
  have hpairPool (i j : Slot) (hij : i ≠ j) :
      D.poolLaw.pr (fun pool => pool i = pool j) = 1 / (Fintype.card Bin : ℝ) := by
    change (FinLaw.pi D.iidSlotLaw).pr (fun pool => pool i = pool j) = _
    exact HypercubeRamsey.Lane_q_s16_comp1.pi_pair_collision_uniform
      D.iidSlotLaw hBpos D.uniform_slots i j hij
  have hpairPin (s : Slot) (b : Bin) (i j : Slot) (hij : i ≠ j) :
      (D.pinLaw s b).pr (fun pool => pool i = pool j) = 1 / (Fintype.card Bin : ℝ) := by
    change (FinLaw.pi (pinLaws s b)).pr (fun pool => pool i = pool j) = _
    rw [HypercubeRamsey.Lane_q_s16_comp1.pi_pair_collision (pinLaws s b) i j hij]
    have hsumConst (r : ℝ) :
        ∑ _a : Bin, r = (Fintype.card Bin : ℝ) * r := by
      calc
        _ = ∑ _a : Bin, (1 : ℝ) * r := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = (∑ _a : Bin, (1 : ℝ)) * r := by rw [← Finset.sum_mul]
        _ = _ := by simp
    by_cases hi : i = s
    · subst i
      have hj : j ≠ s := by intro h; exact hij h.symm
      have hleft (a : Bin) : (pinLaws s b s).w a = if a = b then 1 else 0 := by
        simp [pinLaws, FinLaw.dirac]
      have hright (a : Bin) : (pinLaws s b j).w a = 1 / (Fintype.card Bin : ℝ) := by
        simp [pinLaws, hj, D.uniform_slots]
      calc
        _ = ∑ a, (if a = b then 1 else 0) * (1 / (Fintype.card Bin : ℝ)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hleft, hright]
        _ = _ := by simp [Finset.sum_ite_eq']
    · by_cases hj : j = s
      · subst j
        have hleft (a : Bin) : (pinLaws s b i).w a = 1 / (Fintype.card Bin : ℝ) := by
          simp [pinLaws, hi, D.uniform_slots]
        have hright (a : Bin) : (pinLaws s b s).w a = if a = b then 1 else 0 := by
          simp [pinLaws, FinLaw.dirac]
        calc
          _ = ∑ a, (1 / (Fintype.card Bin : ℝ)) * (if a = b then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hleft, hright]
          _ = _ := by simp [Finset.sum_ite_eq', mul_comm]
      · have hleft (a : Bin) : (pinLaws s b i).w a = 1 / (Fintype.card Bin : ℝ) := by
          simp [pinLaws, hi, D.uniform_slots]
        have hright (a : Bin) : (pinLaws s b j).w a = 1 / (Fintype.card Bin : ℝ) := by
          simp [pinLaws, hj, D.uniform_slots]
        calc
          _ = ∑ a, (1 / (Fintype.card Bin : ℝ)) * (1 / (Fintype.card Bin : ℝ)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hleft, hright]
          _ = (Fintype.card Bin : ℝ) *
              ((1 / (Fintype.card Bin : ℝ)) * (1 / (Fintype.card Bin : ℝ))) :=
            hsumConst _
          _ = _ := by
            field_simp [ne_of_gt hBpos]
            <;> ring
  have hcollision_bound (Q : FinLaw (Slot → Bin))
      (hpair : ∀ i j, i ≠ j → Q.pr (fun pool => pool i = pool j) =
        1 / (Fintype.card Bin : ℝ)) :
      Q.pr (fun pool => ¬ Function.Injective pool) ≤
        (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin := by
    have hbad_iff (pool : Slot → Bin) :
        ¬ Function.Injective pool ↔
          ∃ ij : Slot × Slot, ij.1 ≠ ij.2 ∧ pool ij.1 = pool ij.2 := by
      constructor
      · intro hnot
        by_contra hno
        apply hnot
        intro i j hij
        by_contra hne
        exact hno ⟨(i, j), hne, hij⟩
      · rintro ⟨⟨i, j⟩, hne, heq⟩ hinj
        exact hne (hinj heq)
    have hbadpr : Q.pr (fun pool => ¬ Function.Injective pool) =
        Q.pr (fun pool => ∃ ij : Slot × Slot, ij.1 ≠ ij.2 ∧ pool ij.1 = pool ij.2) := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro pool _
      simp [hbad_iff pool]
    rw [hbadpr]
    calc
      _ ≤ ∑ ij : Slot × Slot, Q.pr (fun pool => ij.1 ≠ ij.2 ∧ pool ij.1 = pool ij.2) :=
        HypercubeRamsey.Lane_q_s16_comp1.finlaw_union_le Q _
      _ ≤ ∑ ij : Slot × Slot, if ij.1 ≠ ij.2 then 1 / (Fintype.card Bin : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro ij _
        by_cases hne : ij.1 ≠ ij.2
        · simpa [hne] using (hpair ij.1 ij.2 hne).le
        · simp [hne, FinLaw.pr]
      _ ≤ ∑ ij : Slot × Slot, 1 / (Fintype.card Bin : ℝ) := by
        apply Finset.sum_le_sum
        intro ij _
        by_cases hne : ij.1 ≠ ij.2
        · simp [hne]
        · simp only [if_neg hne]
          exact div_nonneg (by norm_num) hBpos.le
      _ = (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin := by
        simp [Fintype.card_prod]
        ring
  have hcollisionPool :
      D.poolLaw.pr (fun pool => ¬ Function.Injective pool) ≤ ε / 4 := by
    exact (hcollision_bound D.poolLaw (hpairPool)).trans hD.collision_budget
  have hcollisionPin (s : Slot) (b : Bin) :
      (D.pinLaw s b).pr (fun pool => ¬ Function.Injective pool) ≤ ε / 4 := by
    exact (hcollision_bound (D.pinLaw s b) (hpairPin s b)).trans hD.collision_budget
  have hnormalizer_bad (L : Slot → FinLaw Bin)
      (hmean : ∀ c, |(FinLaw.pi L).E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2) :
      (FinLaw.pi L).pr (fun pool => ∃ c, D.tolerance c <
        |D.normalizer pool c - D.center c|) ≤ ε / 4 := by
    have hcheck (c : Check) : (FinLaw.pi L).pr
        (fun pool => D.tolerance c < |D.normalizer pool c - D.center c|) ≤ ε / (4 * K) := by
      rcases hD.variance_budget c with hzero | ⟨hvar, hbudget⟩
      · have hconst := HypercubeRamsey.Lane_q_s16_comp1.zero_weight_change_constant
          (D.normalizer · c) (hD.sensitivity c)
          (fun s x y hxy => hD.one_slot_change c s x y hxy) hzero
        have hEconst (pool : Slot → Bin) :
            (FinLaw.pi L).E (D.normalizer · c) = D.normalizer pool c := by
          unfold FinLaw.E
          change (∑ q, (FinLaw.pi L).w q * D.normalizer q c) = D.normalizer pool c
          calc
            _ = ∑ q, (FinLaw.pi L).w q * D.normalizer pool c := by
              apply Finset.sum_congr rfl
              intro q _
              rw [hconst q pool]
            _ = (∑ q, (FinLaw.pi L).w q) * D.normalizer pool c := by
              rw [Finset.sum_mul]
            _ = D.normalizer pool c := by rw [(FinLaw.pi L).sum_one, one_mul]
        have hfalse : ∀ pool, ¬ D.tolerance c <
            |D.normalizer pool c - D.center c| := by
          intro pool hbad
          have hm := hmean c
          rw [hEconst pool] at hm
          have hclose : |D.normalizer pool c - D.center c| ≤ D.tolerance c := by
            linarith [hm, hD.tolerance_pos c]
          exact (not_lt_of_ge hclose) hbad
        have hzpr : (FinLaw.pi L).pr (fun pool =>
            D.tolerance c < |D.normalizer pool c - D.center c|) = 0 := by
          unfold FinLaw.pr
          apply Finset.sum_eq_zero
          intro pool _
          simp [hfalse pool]
        rw [hzpr]
        exact div_nonneg (Real.exp_pos _).le (by positivity)
      · let mass : (Slot → Bin) → ℝ := fun pool => ∏ s, (L s).w (pool s)
        have hp (s : Slot) (b : Bin) : 0 ≤ (L s).w b := (L s).nonneg b
        have hone (s : Slot) : ∑ b, (L s).w b = 1 := (L s).sum_one
        have htail := HypercubeRamsey.Lane_q_s16_comp1.weighted_product_abs_tail
          (fun s b => (L s).w b) hp hone (D.normalizer · c) (hD.sensitivity c)
          (fun s x y hxy => hD.one_slot_change c s x y hxy)
          (a := D.tolerance c / 2) (div_pos (hD.tolerance_pos c) (by norm_num)) hvar
        have hsub (pool : Slot → Bin) :
            D.tolerance c < |D.normalizer pool c - D.center c| →
              D.tolerance c / 2 <
                |D.normalizer pool c - (FinLaw.pi L).E (D.normalizer · c)| := by
          intro hbad
          have htri : |D.normalizer pool c - D.center c| ≤
              |D.normalizer pool c - (FinLaw.pi L).E (D.normalizer · c)| +
                |(FinLaw.pi L).E (D.normalizer · c) - D.center c| := by
            calc
              _ = |(D.normalizer pool c - (FinLaw.pi L).E (D.normalizer · c)) +
                    ((FinLaw.pi L).E (D.normalizer · c) - D.center c)| := by congr 1 <;> ring
              _ ≤ _ := abs_add_le _ _
          linarith [hmean c]
        have hmono := HypercubeRamsey.Lane_q_s16_comp1.finiteProbability_mono
          mass (fun pool => Finset.prod_nonneg fun s _ => hp s (pool s)) hsub
        have hcompare : (FinLaw.pi L).pr
            (fun pool => D.tolerance c < |D.normalizer pool c - D.center c|) ≤
              HypercubeRamsey.Lane_q_s16_comp1.finiteProbability mass
                (fun pool => D.tolerance c / 2 <
                  |D.normalizer pool c - (FinLaw.pi L).E (D.normalizer · c)|) := by
          simpa [FinLaw.pr, FinLaw.pi, mass,
            HypercubeRamsey.Lane_q_s16_comp1.finiteProbability,
            HypercubeRamsey.Lane_q_s16_comp1.siteProductMass] using hmono
        have hExpBound : Real.exp (-2 * (D.tolerance c / 2) ^ 2 /
              (∑ s, hD.sensitivity c s ^ 2)) ≤ ε / (8 * K) := by
          calc
            _ ≤ Real.exp (-((n : ℝ) ^ c0 + Real.log (8 * K))) := by
              apply Real.exp_le_exp.mpr
              have hneg := neg_le_neg hbudget
              have hexp : -2 * (D.tolerance c / 2) ^ 2 /
                  (∑ s, hD.sensitivity c s ^ 2) =
                    -(2 * (D.tolerance c / 2) ^ 2 /
                      (∑ s, hD.sensitivity c s ^ 2)) := by ring
              rw [hexp]
              simpa [K] using hneg
            _ = ε / (8 * K) := by
              dsimp [ε]
              rw [neg_add, Real.exp_add]
              have hlog : Real.exp (-Real.log (8 * K)) = (8 * K)⁻¹ := by
                rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 8 * K)]
              rw [hlog]
              ring
        have hcheckBound := hcompare.trans htail
        calc
          _ ≤ 2 * Real.exp (-2 * (D.tolerance c / 2) ^ 2 /
                (∑ s, hD.sensitivity c s ^ 2)) := hcheckBound
          _ ≤ 2 * (ε / (8 * K)) :=
            mul_le_mul_of_nonneg_left hExpBound (by norm_num)
          _ = ε / (4 * K) := by ring
    calc
      _ ≤ ∑ c, (FinLaw.pi L).pr (fun pool =>
          D.tolerance c < |D.normalizer pool c - D.center c|) :=
        HypercubeRamsey.Lane_q_s16_comp1.finlaw_union_le (FinLaw.pi L) _
      _ ≤ ∑ c, ε / (4 * K) := Finset.sum_le_sum fun c _ => hcheck c
      _ = (Fintype.card Check : ℝ) * (ε / (4 * K)) := by simp
      _ ≤ ε / 4 := by
        have hratio : (Fintype.card Check : ℝ) / K ≤ 1 :=
          (div_le_one hKpos).2 hKcard
        calc
          _ = ((Fintype.card Check : ℝ) / K) * (ε / 4) := by ring
          _ ≤ 1 * (ε / 4) := mul_le_mul_of_nonneg_right hratio (by positivity)
          _ = ε / 4 := by ring
  have hnormalizerPool : D.poolLaw.pr
      (fun pool => ∃ c, D.tolerance c < |D.normalizer pool c - D.center c|) ≤ ε / 4 := by
    have hmean : ∀ c, |D.poolLaw.E (D.normalizer · c) - D.center c| ≤ D.tolerance c / 2 :=
      hD.mean_close
    change (FinLaw.pi D.iidSlotLaw).pr _ ≤ _
    exact hnormalizer_bad D.iidSlotLaw hmean
  have hnormalizerPin (s : Slot) (b : Bin) : (D.pinLaw s b).pr
      (fun pool => ∃ c, D.tolerance c < |D.normalizer pool c - D.center c|) ≤ ε / 4 := by
    have hmean : ∀ c, |(FinLaw.pi (pinLaws s b)).E (D.normalizer · c) - D.center c| ≤
        D.tolerance c / 2 := by
      intro c
      exact hD.pinned_mean_close s b c
    change (FinLaw.pi (pinLaws s b)).pr _ ≤ _
    exact hnormalizer_bad (pinLaws s b) hmean
  have htypical_bad (Qlaw : FinLaw (Slot → Bin))
      (hcollision : Qlaw.pr (fun pool => ¬ Function.Injective pool) ≤ ε / 4)
      (hnormal : Qlaw.pr (fun pool => ∃ c, D.tolerance c <
        |D.normalizer pool c - D.center c|) ≤ ε / 4) :
      Qlaw.pr (fun pool => ¬ D.typical pool) ≤ ε / 2 := by
    have hdecomp (pool : Slot → Bin) :
        ¬ D.typical pool ↔ ¬ Function.Injective pool ∨
          ∃ c, D.tolerance c < |D.normalizer pool c - D.center c| := by
      by_cases hinj : Function.Injective pool <;>
        simp [CellPoolDiagnostics.typical, hinj, not_le]
    unfold FinLaw.pr
    calc
      _ ≤ ∑ pool, ((if ¬ Function.Injective pool then Qlaw.w pool else 0) +
            (if ∃ c, D.tolerance c < |D.normalizer pool c - D.center c| then Qlaw.w pool else 0)) := by
        apply Finset.sum_le_sum
        intro pool _
        have hcolw : 0 ≤ if ¬ Function.Injective pool then Qlaw.w pool else 0 := by
          by_cases hcol : ¬ Function.Injective pool <;> simp [hcol, Qlaw.nonneg pool]
        have hnormw : 0 ≤ if ∃ c, D.tolerance c <
            |D.normalizer pool c - D.center c| then Qlaw.w pool else 0 := by
          by_cases hnorm : ∃ c, D.tolerance c <
              |D.normalizer pool c - D.center c| <;> simp [hnorm, Qlaw.nonneg pool]
        have hcolw' : 0 ≤ if Function.Injective pool then 0 else Qlaw.w pool := by
          by_cases hcol : Function.Injective pool <;> simp [hcol, Qlaw.nonneg pool]
        by_cases hbad : ¬ D.typical pool
        · rcases hdecomp pool |>.mp hbad with hcol | hnorm
          · by_cases hnorm' : ∃ c, D.tolerance c <
                |D.normalizer pool c - D.center c|
            · simp [hbad, hcol, hnorm']
              exact Qlaw.nonneg pool
            · simp [hbad, hcol, hnorm']
          · by_cases hcol' : ¬ Function.Injective pool
            · simp [hbad, hnorm, hcol']
              exact Qlaw.nonneg pool
            · simp [hbad, hnorm, hcol']
        · simp [hbad]
          exact add_nonneg hcolw' hnormw
      _ = Qlaw.pr (fun pool => ¬ Function.Injective pool) +
            Qlaw.pr (fun pool => ∃ c, D.tolerance c < |D.normalizer pool c - D.center c|) := by
        simp only [FinLaw.pr]
        rw [Finset.sum_add_distrib]
        apply congrArg₂ (fun x y : ℝ => x + y)
        · apply Finset.sum_congr rfl
          intro x _
          by_cases hx : Function.Injective x <;> simp [hx]
        · apply Finset.sum_congr rfl
          intro x _
          by_cases hx : ∃ c, D.tolerance c <
              |D.normalizer x c - D.center c| <;> simp [hx]
      _ ≤ ε / 4 + ε / 4 := add_le_add hcollision hnormal
      _ = ε / 2 := by ring
  refine ⟨?_, ?_⟩
  · have h := htypical_bad D.poolLaw hcollisionPool hnormalizerPool
    simpa [ε] using h
  · intro s b
    have h := htypical_bad (D.pinLaw s b) (hcollisionPin s b) (hnormalizerPin s b)
    simpa [ε] using h

/-- Diagnostic realization supplies the concrete Part C typicality predicate. -/
theorem pool_requirements_realized {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) :
    ∀ pool, D.typical pool →
      PoolTypical (Finset.univ.image pool) Finset.univ pool n D.ε
        (D.poolNormalizer pool) (D.internalFailure pool) (D.pinnedInternalFailure pool) := by
  intro pool ht
  rcases ht with ⟨hinj, hnormal⟩
  obtain ⟨hnormal', hfailure, hpinned⟩ := D.checks_cover pool hnormal
  refine ⟨rfl, ?_, ?_, hfailure, hpinned⟩
  · intro s _ s' _ heq
    exact hinj heq
  · simpa using hnormal'

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
  classical
  intro pool hpool
  letI : Fintype hD.Slice := hD.sliceFin
  letI : DecidableEq hD.Slice := hD.sliceDec
  letI : ∀ s, Fintype (hD.Value s) := hD.valueFin
  let sliceLaw := hD.sliceLaw pool
  let poolLaw := FinLaw.pi sliceLaw
  let poolMass : (∀ s : hD.Slice, hD.Value s) → ℝ := fun z => ∏ s, (sliceLaw s).w (z s)
  let loadFn (y : D.LoadColumn) (z : ∀ s : hD.Slice, hD.Value s) : ℝ :=
    ∑ s, hD.contribution pool s (z s) y
  let M : ℝ := max 1 (Fintype.card D.LoadColumn : ℝ)
  let ε : ℝ := Real.exp (-(n : ℝ) ^ c0)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMcard : (Fintype.card D.LoadColumn : ℝ) ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hp (s : hD.Slice) (z : hD.Value s) : 0 ≤ (sliceLaw s).w z :=
    (sliceLaw s).nonneg z
  have hone (s : hD.Slice) : ∑ z, (sliceLaw s).w z = 1 := (sliceLaw s).sum_one
  have hfail_map :
      (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) =
        poolLaw.pr (fun z => ∃ y, D.loadThreshold < loadFn y z) := by
    rw [hD.history_eq pool, HypercubeRamsey.Lane_q_s16_comp1.finlaw_map_pr]
    congr 1
    funext z
    simp [CellPoolDiagnostics.loadGate, loadFn, hD.load_eq]
  have hmean (y : D.LoadColumn) :
      HypercubeRamsey.Lane_q_s16_comp1.finiteExpectation poolMass (loadFn y) ≤
        D.loadThreshold / 2 := by
    have hm := hD.mean_small pool hpool y
    rw [hD.history_eq pool] at hm
    rw [HypercubeRamsey.Lane_q_s16_comp1.finlaw_map_E] at hm
    simpa [FinLaw.E, FinLaw.pi, HypercubeRamsey.Lane_q_s16_comp1.finiteExpectation,
      HypercubeRamsey.Lane_q_s16_comp1.dependentProductMass, poolMass, loadFn, hD.load_eq] using hm
  have hLip (y : D.LoadColumn) :
      ∀ s : hD.Slice, ∀ x x', (∀ t, t ≠ s → x t = x' t) →
        |loadFn y x - loadFn y x'| ≤ hD.range s := by
    intro s x x' hxy
    calc
      |loadFn y x - loadFn y x'| =
          |∑ t, (hD.contribution pool t (x t) y - hD.contribution pool t (x' t) y)| := by
            simp only [loadFn]
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ t, |hD.contribution pool t (x t) y - hD.contribution pool t (x' t) y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, if t = s then hD.range s else 0 := by
        apply Finset.sum_le_sum
        intro t _
        by_cases hts : t = s
        · subst t
          have hx := hD.contribution_range pool s (x s) y
          have hx' := hD.contribution_range pool s (x' s) y
          have hd : |hD.contribution pool s (x s) y - hD.contribution pool s (x' s) y| ≤ hD.range s :=
            abs_le.mpr ⟨by linarith [hx.1, hx'.2], by linarith [hx.2, hx'.1]⟩
          simpa using hd
        · have heq := hxy t hts
          simp [hts, heq]
      _ = hD.range s := by simp [Finset.sum_ite_eq']
  have hcolumn (y : D.LoadColumn) :
      poolLaw.pr (fun z => D.loadThreshold < loadFn y z) ≤ ε / M := by
    rcases hD.variance_budget with hzero | ⟨hvar, hbudget⟩
    · have hrangeZero (s : hD.Slice) : hD.range s = 0 := by
        have hs := Finset.single_le_sum (f := fun t => hD.range t ^ 2)
          (fun t _ => sq_nonneg (hD.range t)) (Finset.mem_univ s)
        rw [hzero] at hs
        have hn := hD.range_nonneg s
        nlinarith
      have hcontributionZero (s : hD.Slice) (z : hD.Value s) :
          hD.contribution pool s z y = 0 := by
        have hr := hD.contribution_range pool s z y
        rw [hrangeZero s] at hr
        exact le_antisymm hr.2 hr.1
      have hloadZero (z : ∀ s : hD.Slice, hD.Value s) : loadFn y z = 0 := by
        simp [loadFn, hcontributionZero]
      have hfalse (z : ∀ s : hD.Slice, hD.Value s) : ¬ D.loadThreshold < loadFn y z := by
        rw [hloadZero z]
        linarith [hD.threshold_pos]
      have hzeroPr : poolLaw.pr (fun z => D.loadThreshold < loadFn y z) = 0 := by
        unfold FinLaw.pr
        simp [hfalse]
      rw [hzeroPr]
      exact div_nonneg (Real.exp_pos _).le hMpos.le
    · let a : ℝ := D.loadThreshold / 2
      have ha : 0 < a := by dsimp [a]; linarith [hD.threshold_pos]
      have htail := HypercubeRamsey.Lane_q_s16_comp1.weighted_product_tail_dep
        (fun s z => (sliceLaw s).w z)
        (fun s z => (sliceLaw s).nonneg z)
        (fun s => (sliceLaw s).sum_one) (loadFn y) hD.range (hLip y) ha hvar
      have hsub (z : ∀ s : hD.Slice, hD.Value s) :
          D.loadThreshold < loadFn y z →
            a < loadFn y z - HypercubeRamsey.Lane_q_s16_comp1.finiteExpectation poolMass (loadFn y) := by
        intro hz
        dsimp [a]
        linarith [hmean y]
      have hmono := HypercubeRamsey.Lane_q_s16_comp1.finiteProbability_mono
        poolMass (fun z => Finset.prod_nonneg fun s _ => hp s (z s)) hsub
      have hcompare : poolLaw.pr (fun z => D.loadThreshold < loadFn y z) ≤
          HypercubeRamsey.Lane_q_s16_comp1.finiteProbability poolMass
            (fun z => a < loadFn y z -
              HypercubeRamsey.Lane_q_s16_comp1.finiteExpectation poolMass (loadFn y)) := by
        simpa [poolLaw, poolMass, FinLaw.pr, FinLaw.pi,
          HypercubeRamsey.Lane_q_s16_comp1.finiteProbability,
          HypercubeRamsey.Lane_q_s16_comp1.dependentProductMass] using hmono
      have hExpBudget :
          Real.exp (-2 * a ^ 2 / (∑ s, hD.range s ^ 2)) ≤ ε / M := by
        calc
          _ ≤ Real.exp (-((n : ℝ) ^ c0 + Real.log M)) := by
            apply Real.exp_le_exp.mpr
            have hneg := neg_le_neg hbudget
            have hexp : -2 * a ^ 2 / (∑ s, hD.range s ^ 2) =
                -(2 * (D.loadThreshold / 2) ^ 2 / (∑ s, hD.range s ^ 2)) := by
              dsimp [a]
              ring
            rw [hexp]
            simpa [M] using hneg
          _ = ε / M := by
            dsimp [ε]
            rw [neg_add, Real.exp_add]
            have hlog : Real.exp (-Real.log M) = M⁻¹ := by
              rw [Real.exp_neg, Real.exp_log hMpos]
            rw [hlog]
            ring
      exact hcompare.trans (htail.trans hExpBudget)
  have hfail : (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) ≤ ε := by
    rw [hfail_map]
    calc
      _ ≤ ∑ y, poolLaw.pr (fun z => D.loadThreshold < loadFn y z) :=
        HypercubeRamsey.Lane_q_s16_comp1.finlaw_union_le poolLaw _
      _ ≤ ∑ _y : D.LoadColumn, ε / M :=
        Finset.sum_le_sum fun y _ => hcolumn y
      _ = (Fintype.card D.LoadColumn : ℝ) * (ε / M) := by simp
      _ ≤ ε := by
        have hratio : (Fintype.card D.LoadColumn : ℝ) / M ≤ 1 :=
          (div_le_one hMpos).2 hMcard
        calc
          _ = ε * ((Fintype.card D.LoadColumn : ℝ) / M) := by ring
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
          _ = ε := by ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD.n_large)
  have hrpow : 0 < (n : ℝ) ^ c0 := Real.rpow_pos_of_pos hnpos c0
  have hεlt : ε < 1 := by
    dsimp [ε]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgood :
      (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) =
        ∑ h, if D.loadGate pool h then (D.historyLaw pool).w h else 0 := by
    rw [Finset.sum_filter]
  have hgate :
      (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) +
        (D.historyLaw pool).pr (fun h => ¬ D.loadGate pool h) = 1 := by
    rw [hgood, FinLaw.pr, ← Finset.sum_add_distrib]
    calc
      _ = ∑ h, (D.historyLaw pool).w h := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hh : D.loadGate pool h <;> simp [hh]
      _ = 1 := (D.historyLaw pool).sum_one
  have hgatepos : 0 < ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h := by
    linarith [hgate, hfail, hεlt]
  refine ⟨hfail, ?_⟩
  intro F hF
  refine ⟨hgatepos, ?_⟩
  have hnum :
      (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h * F h) ≤
        (D.historyLaw pool).E F := by
    calc
      _ ≤ ∑ h, (D.historyLaw pool).w h * F h :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
          intro h _ _
          exact mul_nonneg ((D.historyLaw pool).nonneg h) (hF h))
      _ = _ := rfl
  have hEpos : 0 ≤ (D.historyLaw pool).E F :=
    Finset.sum_nonneg fun h _ => mul_nonneg ((D.historyLaw pool).nonneg h) (hF h)
  have hfilterF :
      (∑ h, if h ∈ Finset.univ.filter (D.loadGate pool) then
        (D.historyLaw pool).w h * F h else 0) =
        ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h * F h := by
    rw [← Finset.sum_filter]
    simp
  have hcond :
      (FinLaw.cond (D.historyLaw pool)
          (Finset.univ.filter (D.loadGate pool)) hgatepos).E F =
        (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h * F h) /
          ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h := by
    unfold FinLaw.E FinLaw.cond
    calc
      _ = ∑ h,
          ((if h ∈ Finset.univ.filter (D.loadGate pool) then
              (D.historyLaw pool).w h else 0) * F h) /
            (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hh : h ∈ Finset.univ.filter (D.loadGate pool) <;> simp [hh] <;> ring
      _ = ∑ h,
          ((if h ∈ Finset.univ.filter (D.loadGate pool) then
              (D.historyLaw pool).w h * F h else 0) /
            (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h)) := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hh : h ∈ Finset.univ.filter (D.loadGate pool) <;> simp [hh] <;> ring
      _ = (∑ h, if h ∈ Finset.univ.filter (D.loadGate pool) then
            (D.historyLaw pool).w h * F h else 0) /
            (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) := by
        rw [Finset.sum_div]
      _ = _ := by rw [hfilterF]
  have hdenLower : 1 - ε ≤
      ∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h := by
    linarith [hgate, hfail]
  have hEden : 0 < 1 - ε := by linarith [hεlt]
  calc
    _ = (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h * F h) /
          (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) := hcond
    _ ≤ (D.historyLaw pool).E F /
          (∑ h ∈ Finset.univ.filter (D.loadGate pool), (D.historyLaw pool).w h) :=
      div_le_div_of_nonneg_right hnum hgatepos.le
    _ ≤ (D.historyLaw pool).E F / (1 - ε) :=
      div_le_div_of_nonneg_left hEpos hEden hdenLower
    _ = (1 - ε)⁻¹ * (D.historyLaw pool).E F := by ring

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

/- L16.1's small-scope comparison transfers a half-budget iid tail to the
actual pools, keeping any one global slot pin in both laws. -/
set_option maxHeartbeats 1000000 in
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
  classical
  let G := H.geom
  let i : Fin PT.tiling.m := G.cellPatch C
  let S : Finset (CellSlot G) :=
    Finset.univ.image fun t : Fin (G.nslot C) => (⟨C, t⟩ : CellSlot G)
  let bad : CellPool G C → Prop := fun pool => ¬ D.typical pool
  let test : PoolAssignment G → ℝ := fun P => if bad (P C) then 1 else 0
  let P₀ : PoolAssignment G := H.perm_pool_nonempty.choose
  have hP₀ : P₀ ∈ permPools G := H.perm_pool_nonempty.choose_spec
  have hScard : S.card = G.nslot C := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (by
      intro t t' h
      exact Fin.ext (congrArg (fun z : CellSlot G => z.2.val) h))]
    simp
  have hSmem (t : Fin (G.nslot C)) : (⟨C, t⟩ : CellSlot G) ∈ S := by
    simp [S]
  have hS_patch : ∀ s ∈ S, G.cellPatch s.1 = i := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨t, _, hEq⟩
    rw [← hEq]
  have hScope : (S.card : ℝ) ≤
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) := by
    rw [hScard]
    change (H.data.cells.nslot C : ℝ) ≤ _
    rw [H.cell_partition.slot_count C]
    exact H.scale.cell_scope_bound i
  have hRoom : 2 * ((S.card : ℝ) + 1) ^ 2 ≤
      (Fintype.card (Bin PT.tiling i) : ℝ) := by
    let y : ℝ := Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) + 1
    have hxy : (S.card : ℝ) + 1 ≤ y := by
      dsimp [y]
      exact add_le_add_left hScope 1
    have hpow : ((S.card : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hxy) (by positivity : 0 ≤ y + ((S.card : ℝ) + 1))
      nlinarith [hprod]
    calc
      _ = 2 * ((S.card : ℝ) + 1) ^ 2 := rfl
      _ ≤ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (Fintype.card (Bin PT.tiling i) : ℝ) := by
        simpa [y] using H.scale.comparison_room i
  have hBinPos : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) := by
    have hleft : 0 < 2 * ((S.card : ℝ) + 1) ^ 2 := by positivity
    exact lt_of_lt_of_le hleft hRoom
  have hScopeSq : (S.card : ℝ) ^ 2 ≤
      (Fintype.card (Bin PT.tiling i) : ℝ) := by
    have hScardNonneg : 0 ≤ (S.card : ℝ) := by positivity
    nlinarith
  have hCoeff : 1 + (S.card : ℝ) ^ 2 /
      (Fintype.card (Bin PT.tiling i) : ℝ) ≤ 2 := by
    have hratio : (S.card : ℝ) ^ 2 /
        (Fintype.card (Bin PT.tiling i) : ℝ) ≤ 1 :=
      (div_le_one hBinPos).2 hScopeSq
    linarith
  have hCoeffInsert (pin : CellSlot G) :
      1 + ((insert pin S).card : ℝ) ^ 2 /
        (Fintype.card (Bin PT.tiling i) : ℝ) ≤ 2 := by
    have hcardInsert : (insert pin S).card ≤ S.card + 1 := Finset.card_insert_le pin S
    have hxy : ((insert pin S).card : ℝ) ≤ (S.card : ℝ) + 1 := by
      exact_mod_cast hcardInsert
    have hySq : ((S.card : ℝ) + 1) ^ 2 ≤
        (Fintype.card (Bin PT.tiling i) : ℝ) := by
      nlinarith [sq_nonneg ((S.card : ℝ) + 1), hRoom]
    have hxSq : ((insert pin S).card : ℝ) ^ 2 ≤
        (Fintype.card (Bin PT.tiling i) : ℝ) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hxy)
        (by positivity : 0 ≤ ((insert pin S).card : ℝ) + ((S.card : ℝ) + 1))
      have hmono : ((insert pin S).card : ℝ) ^ 2 ≤ ((S.card : ℝ) + 1) ^ 2 := by
        nlinarith [hprod]
      exact hmono.trans hySq
    have hratio : ((insert pin S).card : ℝ) ^ 2 /
        (Fintype.card (Bin PT.tiling i) : ℝ) ≤ 1 :=
      (div_le_one hBinPos).2 hxSq
    linarith
  have htest_nonneg (P : PoolAssignment G) : 0 ≤ test P := by
    by_cases h : bad (P C) <;> simp [test, h]
  have htest_dep : DependsOnCellSlots S test := by
    intro P Q hAgree
    have hlocal : P C = Q C := by
      funext t
      exact hAgree ⟨C, t⟩ (hSmem t)
    simp [test, hlocal]
  let comp := H.pool_comparison i H.perm_pool_nonempty S hS_patch hScope hRoom
    test htest_nonneg htest_dep
  have hIndicator (μ : FinLaw (PoolAssignment G)) :
      μ.E test = μ.pr (fun P => bad (P C)) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro P _
    by_cases h : bad (P C) <;> simp [test, h]
  let Rest : Type := ∀ c : {c : G.Cell // c ≠ C}, CellPool G c.1
  let split : (∀ c, CellPool G c) ≃ CellPool G C × Rest :=
    Equiv.piSplitAt C (fun c => CellPool G c)
  let uPool : FinLaw (CellPool G C) :=
    FinLaw.uniform Finset.univ ⟨P₀ C, Finset.mem_univ _⟩
  let uRest : FinLaw Rest :=
    FinLaw.uniform Finset.univ ⟨(fun c => P₀ c.1), Finset.mem_univ _⟩
  let pairLaw : FinLaw (CellPool G C × Rest) :=
    FinLaw.uniform Finset.univ ⟨(P₀ C, fun c => P₀ c.1), Finset.mem_univ _⟩
  have hPairBind : pairLaw =
      FinLaw.bind uPool (fun _ => uRest) := by
    simpa [pairLaw, uPool, uRest] using
      HypercubeRamsey.Lane_q_s16_comp1.uniform_prod_eq_bind
        (⟨P₀ C⟩ : Nonempty (CellPool G C))
        (⟨fun c => P₀ c.1⟩ : Nonempty Rest)
  have hDconstant (pool : CellPool G C) :
      D.poolLaw.w pool = ∏ t : Fin (G.nslot C),
        (1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ)) := by
    simp [CellPoolDiagnostics.poolLaw, FinLaw.pi, D.uniform_slots, G]
  have huconstant (pool : CellPool G C) :
      uPool.w pool = 1 / (Fintype.card (CellPool G C) : ℝ) := by
    simp [uPool, FinLaw.uniform]
  have hlocalLaw : D.poolLaw = uPool :=
    HypercubeRamsey.Lane_q_s16_comp1.finlaw_eq_of_const_weights
      D.poolLaw uPool
      (∏ t : Fin (G.nslot C),
        (1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ)))
      (1 / (Fintype.card (CellPool G C) : ℝ))
      ⟨P₀ C⟩ hDconstant huconstant
  have hIidMap (A : CellPool G C × Rest → Prop) :
      (iidPoolLaw G H.perm_pool_nonempty).pr (fun P => A (split P)) =
        pairLaw.pr A := by
    have hsource : (Finset.univ : Finset (PoolAssignment G)).Nonempty :=
      ⟨P₀, Finset.mem_univ _⟩
    have htarget : (Finset.univ : Finset (CellPool G C × Rest)).Nonempty :=
      ⟨(P₀ C, fun c => P₀ c.1), Finset.mem_univ _⟩
    have hcard : (Finset.univ : Finset (PoolAssignment G)).card =
        (Finset.univ : Finset (CellPool G C × Rest)).card := by
      simpa using Fintype.card_congr split
    change (FinLaw.uniform Finset.univ hsource).pr (fun P => A (split P)) =
      (FinLaw.uniform Finset.univ htarget).pr A
    exact HypercubeRamsey.Lane_q_s16_comp1.uniform_pr_equiv
      Finset.univ hsource Finset.univ htarget split
      (by intro P; simp) hcard A
  have hIidMarginal :
      (iidPoolLaw G H.perm_pool_nonempty).pr (fun P => bad (P C)) =
        D.poolLaw.pr bad := by
    have hmap := hIidMap (fun z => bad z.1)
    have hprod := HypercubeRamsey.Lane_q_s16_comp1.uniform_prod_pr_fst
      (⟨P₀ C⟩ : Nonempty (CellPool G C))
      (⟨fun c => P₀ c.1⟩ : Nonempty Rest) bad
    calc
      _ = pairLaw.pr (fun z => bad z.1) := by
        simpa [split, Equiv.piSplitAt, iidPoolLaw] using hmap
      _ = uPool.pr bad := by
        simpa [pairLaw, uPool, uRest] using hprod
      _ = D.poolLaw.pr bad := by rw [hlocalLaw]
  have hUnconditional :
      (permPoolLaw G H.perm_pool_nonempty).pr (fun P => ¬ D.typical (P C)) ≤
        Real.exp (-(T.S.n k : ℝ) ^ c0) := by
    have hpermE := hIndicator (permPoolLaw G H.perm_pool_nonempty)
    have hiidE := hIndicator (iidPoolLaw G H.perm_pool_nonempty)
    have hqnonneg : 0 ≤ (iidPoolLaw G H.perm_pool_nonempty).E test := by
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro P _
      exact mul_nonneg ((iidPoolLaw G H.perm_pool_nonempty).nonneg P)
        (htest_nonneg P)
    calc
      _ = (permPoolLaw G H.perm_pool_nonempty).E test := hpermE.symm
      _ ≤ (1 + (S.card : ℝ) ^ 2 /
          (Fintype.card (Bin PT.tiling i) : ℝ)) *
          (iidPoolLaw G H.perm_pool_nonempty).E test := comp.1
      _ ≤ 2 * (iidPoolLaw G H.perm_pool_nonempty).E test :=
        mul_le_mul_of_nonneg_right hCoeff hqnonneg
      _ = 2 * D.poolLaw.pr bad := by rw [hiidE, hIidMarginal]
      _ ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
        nlinarith [Real.exp_pos (-(T.S.n k : ℝ) ^ c0), hu]
  refine ⟨hUnconditional, ?_⟩
  intro s b hpin
  have hEventNonempty : (poolPinEvent s b).Nonempty := by
    by_contra hempty
    have hEq : poolPinEvent s b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [hEq] at hpin
  have hPpin := hEventNonempty.choose_spec
  have hGlobalCardPos : 0 < (Fintype.card (PoolAssignment G) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨P₀⟩)
  have hIidPinPos : 0 < ∑ P ∈ poolPinEvent s b,
      (iidPoolLaw G H.perm_pool_nonempty).w P := by
    have hweight : 0 < (iidPoolLaw G H.perm_pool_nonempty).w hEventNonempty.choose := by
      change 0 < if hEventNonempty.choose ∈ Finset.univ then
        1 / (Fintype.card (PoolAssignment G) : ℝ) else 0
      rw [if_pos (Finset.mem_univ _)]
      exact one_div_pos.mpr hGlobalCardPos
    have hle := Finset.single_le_sum
      (f := fun P => (iidPoolLaw G H.perm_pool_nonempty).w P)
      (fun P _ => (iidPoolLaw G H.perm_pool_nonempty).nonneg P) hPpin
    exact lt_of_lt_of_le hweight hle
  by_cases hSame : s.1 = C
  · rcases s with ⟨cell, slot⟩
    dsimp at hSame
    subst cell
    let pinset : Finset (CellPool G C) := Finset.univ.filter fun pool => pool slot = b
    let poolb : CellPool G C := fun _ => b
    have hpoolb : poolb ∈ pinset := by simp [pinset, poolb]
    have hPinSetNonempty : pinset.Nonempty := ⟨poolb, hpoolb⟩
    have hUpin : 0 < ∑ pool ∈ pinset, uPool.w pool := by
      have hweight : 0 < uPool.w poolb := by
        simp [uPool, FinLaw.uniform]
        positivity
      have hle := Finset.single_le_sum (f := fun pool => uPool.w pool)
        (fun pool _ => uPool.nonneg pool) hpoolb
      exact lt_of_lt_of_le hweight hle
    let uPin : FinLaw (CellPool G C) := FinLaw.cond uPool pinset hUpin
    let cDpin : ℝ := ∏ t : Fin (G.nslot C),
      if t = slot then 1 else 1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ)
    let cUpin : ℝ := (1 / (Fintype.card (CellPool G C) : ℝ)) /
      (∑ pool ∈ pinset, uPool.w pool)
    have hDpinZero (pool : CellPool G C) (hpool : pool ∉ pinset) :
        (D.pinLaw slot b).w pool = 0 := by
      have hne : pool slot ≠ b := by
        intro hEq
        exact hpool (by simp [pinset, hEq])
      dsimp [CellPoolDiagnostics.pinLaw, FinLaw.pi]
      apply Finset.prod_eq_zero (Finset.mem_univ slot)
      simp [FinLaw.dirac, hne]
    have huPinZero (pool : CellPool G C) (hpool : pool ∉ pinset) :
        uPin.w pool = 0 := by
      simp only [uPin, FinLaw.cond]
      simp [hpool]
    have hDpinConst (pool : CellPool G C) (hpool : pool ∈ pinset) :
        (D.pinLaw slot b).w pool = cDpin := by
      have hpinned : pool slot = b := by simpa [pinset] using hpool
      dsimp [CellPoolDiagnostics.pinLaw, FinLaw.pi]
      simp only [cDpin]
      apply Finset.prod_congr rfl
      intro t _
      by_cases hts : t = slot
      · subst t
        simp [FinLaw.dirac, hpinned]
      · simp only [if_neg hts]
        rw [D.uniform_slots t (pool t)]
    have huPinConst (pool : CellPool G C) (hpool : pool ∈ pinset) :
        uPin.w pool = cUpin := by
      simp only [uPin, FinLaw.cond]
      rw [if_pos hpool, huconstant pool]
    have hPinLawEq : D.pinLaw slot b = uPin :=
      HypercubeRamsey.Lane_q_s16_comp1.finlaw_eq_of_const_on_set
        (D.pinLaw slot b) uPin pinset hPinSetNonempty cDpin cUpin
        hDpinZero huPinZero hDpinConst huPinConst
    let Bpair : CellPool G C × Rest → Prop := fun z => z.1 slot = b
    let pinpair : Finset (CellPool G C × Rest) :=
      Finset.univ.filter Bpair
    have hIidPinMap :
        (iidPoolLaw G H.perm_pool_nonempty).pr
          (fun P => P C slot = b) = pairLaw.pr Bpair := by
      have hm := hIidMap Bpair
      simpa [Bpair, split, Equiv.piSplitAt] using hm
    have hIidPinBadMap :
        (iidPoolLaw G H.perm_pool_nonempty).pr
          (fun P => P C slot = b ∧ bad (P C)) =
        pairLaw.pr (fun z => Bpair z ∧ bad z.1) := by
      have hm := hIidMap (fun z => Bpair z ∧ bad z.1)
      simpa [Bpair, split, Equiv.piSplitAt] using hm
    have hIidCondRatio := HypercubeRamsey.Lane_q_s16_comp1.finlaw_cond_pr_ratio_event
      (iidPoolLaw G H.perm_pool_nonempty) (poolPinEvent ⟨C, slot⟩ b)
      hIidPinPos (fun P => bad (P C))
    simp only [poolPinEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hIidCondRatio
    rw [hIidPinBadMap, hIidPinMap] at hIidCondRatio
    have hPairMarginal (E : CellPool G C → Prop) :
        pairLaw.pr (fun z => E z.1) = uPool.pr E := by
      simpa [pairLaw, uPool, uRest] using
        HypercubeRamsey.Lane_q_s16_comp1.uniform_prod_pr_fst
          (⟨P₀ C⟩ : Nonempty (CellPool G C))
          (⟨fun c => P₀ c.1⟩ : Nonempty Rest) E
    have hLocalCondRatio := HypercubeRamsey.Lane_q_s16_comp1.finlaw_cond_pr_ratio_event
      uPool pinset hUpin bad
    simp only [pinset, Finset.mem_filter, Finset.mem_univ, true_and] at hLocalCondRatio
    have hcondIidBad :
        (FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
          (poolPinEvent ⟨C, slot⟩ b) hIidPinPos).pr (fun P => bad (P C)) =
          (D.pinLaw slot b).pr bad := by
      rw [hPairMarginal (fun pool => pool slot = b ∧ bad pool),
        hPairMarginal (fun pool => pool slot = b)] at hIidCondRatio
      calc
        _ = uPin.pr bad := hIidCondRatio.trans hLocalCondRatio.symm
        _ = (D.pinLaw slot b).pr bad := by rw [← hPinLawEq]
    have hscopePin : insert (⟨C, slot⟩ : CellSlot G) S = S :=
      Finset.insert_eq_of_mem (hSmem slot)
    have hCoeffPin : 1 + (insert (⟨C, slot⟩ : CellSlot G) S).card ^ 2 /
        (Fintype.card (Bin PT.tiling i) : ℝ) ≤ 2 := by
      simpa [hscopePin] using hCoeff
    have hcmpPin := comp.2 ⟨C, slot⟩ b rfl hpin hIidPinPos
    have hpinPrNonneg : 0 ≤ (D.pinLaw slot b).pr bad := by
      unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro pool _
      by_cases hbad : bad pool
      · simp [hbad, (D.pinLaw slot b).nonneg pool]
      · simp [hbad]
    have hcondNonneg :
        0 ≤ (FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
          (poolPinEvent ⟨C, slot⟩ b) hIidPinPos).E test := by
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro P _
      exact mul_nonneg
        ((FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
          (poolPinEvent ⟨C, slot⟩ b) hIidPinPos).nonneg P)
        (htest_nonneg P)
    have hpinBound :
        ((permPoolLaw G H.perm_pool_nonempty).cond
          (poolPinEvent ⟨C, slot⟩ b) hpin).pr
          (fun P => ¬ D.typical (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
      let μperm := FinLaw.cond (permPoolLaw G H.perm_pool_nonempty)
        (poolPinEvent ⟨C, slot⟩ b) hpin
      let μiid := FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
        (poolPinEvent ⟨C, slot⟩ b) hIidPinPos
      have hEperm := hIndicator μperm
      have hEiid := hIndicator μiid
      calc
        _ = μperm.E test := hEperm.symm
        _ ≤ (1 + ((insert (⟨C, slot⟩ : CellSlot G) S).card : ℝ) ^ 2 /
            (Fintype.card (Bin PT.tiling i) : ℝ)) *
            μiid.E test := hcmpPin
        _ = (1 + ((insert (⟨C, slot⟩ : CellSlot G) S).card : ℝ) ^ 2 /
            (Fintype.card (Bin PT.tiling i) : ℝ)) *
            (D.pinLaw slot b).pr bad := by
              rw [hEiid, hcondIidBad]
        _ ≤ 2 * (D.pinLaw slot b).pr bad :=
          mul_le_mul_of_nonneg_right hCoeffPin hpinPrNonneg
        _ ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
          calc
            _ ≤ 2 * (Real.exp (-(T.S.n k : ℝ) ^ c0) / 2) :=
              mul_le_mul_of_nonneg_left (hp slot b) (by norm_num)
            _ = Real.exp (-(T.S.n k : ℝ) ^ c0) := by ring
    simpa using hpinBound
  · have hCellNe : s.1 ≠ C := hSame
    by_cases hPatchSame : G.cellPatch s.1 = i
    · let r : {c : G.Cell // c ≠ C} := ⟨s.1, hCellNe⟩
      let BRest : Rest → Prop := fun rest => rest r s.2 = b
      let Bpair : CellPool G C × Rest → Prop := fun z => BRest z.2
      have hIidPinMap :
          (iidPoolLaw G H.perm_pool_nonempty).pr
            (fun P => P s.1 s.2 = b) = pairLaw.pr Bpair := by
        have hm := hIidMap Bpair
        simpa [Bpair, BRest, r, split, Equiv.piSplitAt] using hm
      have hIidPinBadMap :
          (iidPoolLaw G H.perm_pool_nonempty).pr
            (fun P => P s.1 s.2 = b ∧ bad (P C)) =
          pairLaw.pr (fun z => Bpair z ∧ bad z.1) := by
        have hm := hIidMap (fun z => Bpair z ∧ bad z.1)
        simpa [Bpair, BRest, r, split, Equiv.piSplitAt] using hm
      have hIidCondRatio := HypercubeRamsey.Lane_q_s16_comp1.finlaw_cond_pr_ratio_event
        (iidPoolLaw G H.perm_pool_nonempty) (poolPinEvent s b) hIidPinPos
        (fun P => bad (P C))
      simp only [poolPinEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hIidCondRatio
      rw [hIidPinBadMap, hIidPinMap] at hIidCondRatio
      have hGlobalPinMass :
          (∑ P ∈ poolPinEvent s b, (iidPoolLaw G H.perm_pool_nonempty).w P) =
            (iidPoolLaw G H.perm_pool_nonempty).pr (fun P => P s.1 s.2 = b) := by
        have hm := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_filter
          (iidPoolLaw G H.perm_pool_nonempty) (poolPinEvent s b)
        simpa [poolPinEvent, Finset.mem_filter, Finset.mem_univ] using hm
      have hGlobalPinPrPos :
          0 < (iidPoolLaw G H.perm_pool_nonempty).pr (fun P => P s.1 s.2 = b) := by
        rw [← hGlobalPinMass]
        exact hIidPinPos
      have hPairPinPrPos : 0 < pairLaw.pr Bpair := by
        rw [← hIidPinMap]
        exact hGlobalPinPrPos
      let pairPinset := Finset.univ.filter Bpair
      have hPairPinMass :
          (∑ z ∈ pairPinset, pairLaw.w z) = pairLaw.pr Bpair := by
        have hm := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_filter pairLaw pairPinset
        simpa [pairPinset, Finset.mem_filter, Finset.mem_univ] using hm
      have hPairPinMassPos : 0 < ∑ z ∈ pairPinset, pairLaw.w z := by
        rw [hPairPinMass]
        exact hPairPinPrPos
      have hBindPinMass :
          (∑ z ∈ pairPinset, (FinLaw.bind uPool (fun _ => uRest)).w z) =
            ∑ z ∈ pairPinset, pairLaw.w z := by
        simp [hPairBind]
      have hBindPinMassPos :
          0 < ∑ z ∈ pairPinset, (FinLaw.bind uPool (fun _ => uRest)).w z := by
        rw [hBindPinMass]
        exact hPairPinMassPos
      have hBindCond := HypercubeRamsey.Lane_q_s16_comp1.finlaw_bind_cond_pr_right
        uPool uRest BRest bad hBindPinMassPos
      have hBindCondRatio := HypercubeRamsey.Lane_q_s16_comp1.finlaw_cond_pr_ratio_event
        (FinLaw.bind uPool (fun _ => uRest)) pairPinset hBindPinMassPos
        (fun z => bad z.1)
      simp only [pairPinset, Finset.mem_filter, Finset.mem_univ, true_and] at hBindCondRatio
      have hPairPrEq (E : CellPool G C × Rest → Prop) :
          pairLaw.pr E = (FinLaw.bind uPool (fun _ => uRest)).pr E := by
        rw [hPairBind]
      rw [hPairPrEq (fun z => Bpair z ∧ bad z.1), hPairPrEq Bpair] at hIidCondRatio
      have hIidCondBad :
          (FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
            (poolPinEvent s b) hIidPinPos).pr (fun P => bad (P C)) =
            D.poolLaw.pr bad := by
        calc
          _ = (FinLaw.bind uPool (fun _ => uRest)).pr
                (fun z => Bpair z ∧ bad z.1) /
                (FinLaw.bind uPool (fun _ => uRest)).pr Bpair := hIidCondRatio
          _ = (FinLaw.cond (FinLaw.bind uPool (fun _ => uRest))
                pairPinset hBindPinMassPos).pr (fun z => bad z.1) :=
                hBindCondRatio.symm
          _ = uPool.pr bad := hBindCond
          _ = D.poolLaw.pr bad := by rw [hlocalLaw]
      let μperm := FinLaw.cond (permPoolLaw G H.perm_pool_nonempty)
        (poolPinEvent s b) hpin
      let μiid := FinLaw.cond (iidPoolLaw G H.perm_pool_nonempty)
        (poolPinEvent s b) hIidPinPos
      have hEperm := hIndicator μperm
      have hEiid := hIndicator μiid
      have hcmpPin := comp.2 s b hPatchSame hpin hIidPinPos
      have hDpoolBadNonneg : 0 ≤ D.poolLaw.pr bad := by
        unfold FinLaw.pr
        apply Finset.sum_nonneg
        intro pool _
        by_cases hbad : bad pool
        · simp [hbad, D.poolLaw.nonneg pool]
        · simp [hbad]
      have hpinBound :
          μperm.pr (fun P => bad (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
        calc
          _ = μperm.E test := hEperm.symm
          _ ≤ (1 + ((insert s S).card : ℝ) ^ 2 /
              (Fintype.card (Bin PT.tiling i) : ℝ)) * μiid.E test := hcmpPin
          _ = (1 + ((insert s S).card : ℝ) ^ 2 /
              (Fintype.card (Bin PT.tiling i) : ℝ)) * D.poolLaw.pr bad := by
                rw [hEiid, hIidCondBad]
          _ ≤ 2 * D.poolLaw.pr bad :=
            mul_le_mul_of_nonneg_right (hCoeffInsert s) hDpoolBadNonneg
          _ ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
            calc
              _ ≤ 2 * (Real.exp (-(T.S.n k : ℝ) ^ c0) / 2) :=
                mul_le_mul_of_nonneg_left hu (by norm_num)
              _ = Real.exp (-(T.S.n k : ℝ) ^ c0) := by ring
      simpa [μperm] using hpinBound
    · let pinPatch := G.cellPatch s.1
      have hTargetNe : G.cellPatch C ≠ pinPatch := by
        intro hEq
        apply hPatchSame
        simpa [pinPatch, i] using hEq.symm
      let swapSet (d : Bin PT.tiling pinPatch) (j : Fin PT.tiling.m) :
          Finset (Fin (T.S.N k)) ≃ Finset (Fin (T.S.N k)) :=
        if hj : j = pinPatch then Equiv.swap d.1 b.1 else Equiv.refl _
      let swapBin : ∀ d : Bin PT.tiling pinPatch, ∀ j : Fin PT.tiling.m,
          Bin PT.tiling j ≃ Bin PT.tiling j := fun d j =>
        if hj : j = pinPatch then
          let castBin : Bin PT.tiling pinPatch ≃ Bin PT.tiling j :=
            Equiv.cast (congrArg (Bin PT.tiling) hj.symm)
          Equiv.swap (castBin d) (castBin b)
        else Equiv.refl _
      have hvalSwap (d : Bin PT.tiling pinPatch) (j : Fin PT.tiling.m)
          (x : Bin PT.tiling j) :
          (swapBin d j x).1 = swapSet d j x.1 := by
        by_cases hj : j = pinPatch
        · subst j
          simp only [swapBin, swapSet, if_pos rfl, dif_pos True.intro]
          change (Equiv.swap d b x).1 = Equiv.swap d.1 b.1 x.1
          by_cases hxd : x.1 = d.1
          · have hx : x = d := Subtype.ext hxd
            subst x
            simp [Equiv.swap_apply_left]
          · by_cases hxb : x.1 = b.1
            · have hx : x = b := Subtype.ext hxb
              subst x
              simp [Equiv.swap_apply_right]
            · have hxd' : x ≠ d := fun h => hxd (congrArg Subtype.val h)
              have hxb' : x ≠ b := fun h => hxb (congrArg Subtype.val h)
              rw [Equiv.swap_apply_of_ne_of_ne hxd' hxb',
                Equiv.swap_apply_of_ne_of_ne hxd hxb]
        · simp [swapBin, swapSet, hj]
      let swapCell (d : Bin PT.tiling pinPatch) (c : G.Cell) :
          CellPool G c ≃ CellPool G c :=
        Equiv.piCongrRight fun _ : Fin (G.nslot c) => swapBin d (G.cellPatch c)
      let swapAll (d : Bin PT.tiling pinPatch) :
          PoolAssignment G ≃ PoolAssignment G :=
        Equiv.piCongrRight fun c => swapCell d c
      have hpoint (d : Bin PT.tiling pinPatch) (P : PoolAssignment G)
          (c : G.Cell) (t : Fin (G.nslot c)) :
          (swapAll d P) c t = swapBin d (G.cellPatch c) (P c t) := by
        rfl
      have hSupport (d : Bin PT.tiling pinPatch) (P : PoolAssignment G) :
          P ∈ permPools G ↔ swapAll d P ∈ permPools G := by
        classical
        simp only [permPools, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hvalid C₁ C₂ t₁ t₂ hpatch heq
          have hSwapEq : swapSet d (G.cellPatch C₁) =
              swapSet d (G.cellPatch C₂) := congrArg (swapSet d) hpatch
          have heqSet :
              swapSet d (G.cellPatch C₁) (P C₁ t₁).1 =
                swapSet d (G.cellPatch C₂) (P C₂ t₂).1 := by
            calc
              _ = (swapAll d P C₁ t₁).1 := (hvalSwap d (G.cellPatch C₁) (P C₁ t₁)).symm
              _ = (swapAll d P C₂ t₂).1 := heq
              _ = _ := hvalSwap d (G.cellPatch C₂) (P C₂ t₂)
          have heqSet' :
              swapSet d (G.cellPatch C₁) (P C₁ t₁).1 =
                swapSet d (G.cellPatch C₁) (P C₂ t₂).1 := by
            calc
              _ = swapSet d (G.cellPatch C₂) (P C₂ t₂).1 := heqSet
              _ = _ := by rw [← hSwapEq]
          have heqVal := (swapSet d (G.cellPatch C₁)).injective heqSet'
          exact hvalid C₁ C₂ t₁ t₂ hpatch heqVal
        · intro hvalid C₁ C₂ t₁ t₂ hpatch heq
          have hSwapEq : swapSet d (G.cellPatch C₁) =
              swapSet d (G.cellPatch C₂) := congrArg (swapSet d) hpatch
          have heqSet :
              swapSet d (G.cellPatch C₁) (P C₁ t₁).1 =
                swapSet d (G.cellPatch C₂) (P C₂ t₂).1 := by
            calc
              _ = swapSet d (G.cellPatch C₁) (P C₂ t₂).1 :=
                congrArg (swapSet d (G.cellPatch C₁)) heq
              _ = _ := by rw [← hSwapEq]
          have heqVal :
              (swapAll d P C₁ t₁).1 = (swapAll d P C₂ t₂).1 := by
            calc
              _ = swapSet d (G.cellPatch C₁) (P C₁ t₁).1 :=
                hvalSwap d (G.cellPatch C₁) (P C₁ t₁)
              _ = swapSet d (G.cellPatch C₂) (P C₂ t₂).1 := heqSet
              _ = _ := (hvalSwap d (G.cellPatch C₂) (P C₂ t₂)).symm
          exact hvalid C₁ C₂ t₁ t₂ hpatch heqVal
      have hFixed (d : Bin PT.tiling pinPatch) (P : PoolAssignment G) :
          (swapAll d P) C = P C := by
        funext t
        rw [hpoint]
        simp [swapBin, pinPatch, i, hTargetNe]
      have hPinAction (d : Bin PT.tiling pinPatch) (P : PoolAssignment G) :
          (swapAll d P) s.1 s.2 = Equiv.swap d b (P s.1 s.2) := by
        rw [hpoint]
        simp [swapBin, pinPatch]
      have hSwapInv (d : Bin PT.tiling pinPatch) (x : Bin PT.tiling pinPatch) :
          Equiv.swap d b (Equiv.swap d b x) = x := by
        by_cases hdb : d = b
        · subst b
          simp
        · by_cases hxd : x = d
          · subst x
            simp
          · by_cases hxb : x = b
            · subst x
              simp
            · rw [Equiv.swap_apply_of_ne_of_ne hxd hxb,
                Equiv.swap_apply_of_ne_of_ne hxd hxb]
      have hSwapPreimage (d : Bin PT.tiling pinPatch) (x : Bin PT.tiling pinPatch) :
          Equiv.swap d b x = b ↔ x = d := by
        constructor
        · intro hx
          have hx' := congrArg (Equiv.swap d b) hx
          rw [hSwapInv d x, Equiv.swap_apply_right] at hx'
          exact hx'
        · intro hx
          subst x
          simp
      have hUniformSymmetry (d : Bin PT.tiling pinPatch)
          (A : PoolAssignment G → Prop) :
          (permPoolLaw G H.perm_pool_nonempty).pr
              (fun P => A (swapAll d P)) =
            (permPoolLaw G H.perm_pool_nonempty).pr A := by
        simpa [permPoolLaw] using
          (HypercubeRamsey.Lane_q_s16_comp1.uniform_pr_equiv
            (permPools G) H.perm_pool_nonempty (permPools G) H.perm_pool_nonempty
            (swapAll d) (hSupport d) rfl A)
      have hEventPreimage (d : Bin PT.tiling pinPatch) (P : PoolAssignment G) :
          (bad ((swapAll d P) C) ∧ (swapAll d P) s.1 s.2 = b) ↔
            (bad (P C) ∧ P s.1 s.2 = d) := by
        rw [hFixed d P, hPinAction d P]
        constructor
        · rintro ⟨hbad, hpin⟩
          exact ⟨hbad, (hSwapPreimage d (P s.1 s.2)).mp hpin⟩
        · rintro ⟨hbad, hpin⟩
          exact ⟨hbad, (hSwapPreimage d (P s.1 s.2)).mpr hpin⟩
      have hSymBad (d : Bin PT.tiling pinPatch) :
          (permPoolLaw G H.perm_pool_nonempty).pr
            (fun P => bad (P C) ∧ P s.1 s.2 = d) =
          (permPoolLaw G H.perm_pool_nonempty).pr
            (fun P => bad (P C) ∧ P s.1 s.2 = b) := by
        have hsym := hUniformSymmetry d (fun P => bad (P C) ∧ P s.1 s.2 = b)
        have hpre := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_congr
          (permPoolLaw G H.perm_pool_nonempty) (hEventPreimage d)
        exact hpre.symm.trans hsym
      have hPinPreimage (d : Bin PT.tiling pinPatch) (P : PoolAssignment G) :
          (swapAll d P) s.1 s.2 = b ↔ P s.1 s.2 = d := by
        rw [hPinAction d P]
        exact hSwapPreimage d (P s.1 s.2)
      have hSymPin (d : Bin PT.tiling pinPatch) :
          (permPoolLaw G H.perm_pool_nonempty).pr
            (fun P => P s.1 s.2 = d) =
          (permPoolLaw G H.perm_pool_nonempty).pr
            (fun P => P s.1 s.2 = b) := by
        have hsym := hUniformSymmetry d (fun P => P s.1 s.2 = b)
        have hpre := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_congr
          (permPoolLaw G H.perm_pool_nonempty) (hPinPreimage d)
        exact hpre.symm.trans hsym
      let μ := permPoolLaw G H.perm_pool_nonempty
      let qAB : ℝ := μ.pr (fun P => P s.1 s.2 = b ∧ bad (P C))
      let qB : ℝ := μ.pr (fun P => P s.1 s.2 = b)
      have hBinNonempty : Nonempty (Bin PT.tiling pinPatch) :=
        ⟨P₀ s.1 s.2⟩
      have hBinCardNe : (Fintype.card (Bin PT.tiling pinPatch) : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos_iff.mpr hBinNonempty).ne'
      have hsumAB :
          (∑ d : Bin PT.tiling pinPatch,
            μ.pr (fun P => P s.1 s.2 = d ∧ bad (P C))) =
              μ.pr (fun P => bad (P C)) := by
        calc
          _ = ∑ d : Bin PT.tiling pinPatch,
                μ.pr (fun P => bad (P C) ∧ P s.1 s.2 = d) := by
            apply Finset.sum_congr rfl
            intro d _
            exact (HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_congr μ
              (fun _ => and_comm)).symm
          _ = μ.pr (fun P => bad (P C)) :=
            HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_fiber_sum μ
              (fun P => P s.1 s.2) (fun P => bad (P C))
      have hsumPin :
          (∑ d : Bin PT.tiling pinPatch, μ.pr (fun P => P s.1 s.2 = d)) = 1 := by
        have h := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_fiber_sum μ
          (fun P => P s.1 s.2) (fun _ => True)
        have htrue : μ.pr (fun _ => True) = 1 := by
          simpa [FinLaw.pr] using μ.sum_one
        simpa [htrue] using h
      have hcommBad (d : Bin PT.tiling pinPatch) :
          μ.pr (fun P => P s.1 s.2 = d ∧ bad (P C)) =
            μ.pr (fun P => bad (P C) ∧ P s.1 s.2 = d) := by
        apply HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_congr μ
        intro P
        constructor
        · rintro ⟨hpin, hbad⟩
          exact ⟨hbad, hpin⟩
        · rintro ⟨hbad, hpin⟩
          exact ⟨hpin, hbad⟩
      have hcardAB :
          (Fintype.card (Bin PT.tiling pinPatch) : ℝ) * qAB =
            μ.pr (fun P => bad (P C)) := by
        calc
          _ = ∑ d : Bin PT.tiling pinPatch, qAB := by simp [qAB]
          _ = ∑ d : Bin PT.tiling pinPatch,
              μ.pr (fun P => P s.1 s.2 = d ∧ bad (P C)) := by
            apply Finset.sum_congr rfl
            intro d _
            calc
              _ = μ.pr (fun P => bad (P C) ∧ P s.1 s.2 = b) := hcommBad b
              _ = μ.pr (fun P => bad (P C) ∧ P s.1 s.2 = d) := (hSymBad d).symm
              _ = μ.pr (fun P => P s.1 s.2 = d ∧ bad (P C)) := (hcommBad d).symm
          _ = μ.pr (fun P => bad (P C)) := hsumAB
      have hcardPin :
          (Fintype.card (Bin PT.tiling pinPatch) : ℝ) * qB = 1 := by
        calc
          _ = ∑ d : Bin PT.tiling pinPatch, qB := by simp [qB]
          _ = ∑ d : Bin PT.tiling pinPatch, μ.pr (fun P => P s.1 s.2 = d) := by
            apply Finset.sum_congr rfl
            intro d _
            exact (hSymPin d).symm
          _ = 1 := hsumPin
      have hpinPrPos : 0 < qB := by
        have hmass := HypercubeRamsey.Lane_q_s16_comp1.finlaw_pr_filter μ
          (poolPinEvent s b)
        have hmass' : (∑ P ∈ poolPinEvent s b, μ.w P) = qB := by
          simpa [qB, poolPinEvent, Finset.mem_filter, Finset.mem_univ] using hmass
        rw [← hmass']
        exact hpin
      have hratio : qAB / qB = μ.pr (fun P => bad (P C)) := by
        calc
          _ = ((Fintype.card (Bin PT.tiling pinPatch) : ℝ) * qAB) /
                ((Fintype.card (Bin PT.tiling pinPatch) : ℝ) * qB) := by
                  field_simp [hBinCardNe, ne_of_gt hpinPrPos]
                  <;> ring
          _ = μ.pr (fun P => bad (P C)) / 1 := by rw [hcardAB, hcardPin]
          _ = μ.pr (fun P => bad (P C)) := by ring
      have hcondRatio :
          (FinLaw.cond μ (poolPinEvent s b) hpin).pr
            (fun P => bad (P C)) = qAB / qB := by
        have h := HypercubeRamsey.Lane_q_s16_comp1.finlaw_cond_pr_ratio_event
          μ (poolPinEvent s b) hpin (fun P => bad (P C))
        simpa [qAB, qB, poolPinEvent, Finset.mem_filter, Finset.mem_univ,
          true_and, and_comm] using h
      have hcross :
          (FinLaw.cond μ (poolPinEvent s b) hpin).pr
            (fun P => bad (P C)) ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := by
        calc
          _ = qAB / qB := hcondRatio
          _ = μ.pr (fun P => bad (P C)) := hratio
          _ ≤ Real.exp (-(T.S.n k : ℝ) ^ c0) := hUnconditional
      simpa [μ] using hcross

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
  classical
  let r : OddCellRole G C := ⟨b, hb, ho⟩
  let g := Cal.groupOf C r
  let Hlaw := Cal.gatedHistory C P
  let binLaw := fun W => Cal.binSampler C P W
  let labelLaw := fun W a => Cal.labelSampler C P W a
  let stageLaw := FinLaw.bind Hlaw fun W =>
    FinLaw.bind (binLaw W) (labelLaw W)
  have hstage0 : stageLaw.pr
      (fun z => F.label C (Cal.encode C z) b = y) =
      ∑ W, Hlaw.w W * ∑ a, (binLaw W).w a *
        (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y) := by
    calc
      _ = ∑ W, Hlaw.w W * (FinLaw.bind (binLaw W) (labelLaw W)).pr
            (fun rest => F.label C (Cal.encode C (W, rest)) b = y) := by
        simpa [stageLaw] using
          (HypercubeRamsey.Lane_q_s16_comp1.finlaw_bind_pr Hlaw
            (fun W => FinLaw.bind (binLaw W) (labelLaw W))
            (fun W rest => F.label C (Cal.encode C (W, rest)) b = y))
      _ = ∑ W, Hlaw.w W * ∑ a, (binLaw W).w a *
            (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y) := by
        apply Finset.sum_congr rfl
        intro W _
        have hbind := HypercubeRamsey.Lane_q_s16_comp1.finlaw_bind_pr
          (binLaw W) (labelLaw W)
          (fun a ys => F.label C (Cal.encode C (W, (a, ys))) b = y)
        simpa using congrArg (fun q => Hlaw.w W * q) hbind
  have hlabel_pr (W : Cal.Hist C) (a : Cal.Group C → Bin PT.tiling (G.cellPatch C))
      (hW : Hlaw.w W ≠ 0) (ha : (binLaw W).w a ≠ 0) :
      (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y) =
        (labelLaw W a).pr (fun ys => ys r = y) := by
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro ys _
    by_cases hys : (labelLaw W a).w ys = 0
    · simp [hys]
    · have hread : F.label C (Cal.encode C (W, (a, ys))) b = ys r := by
        simpa [r] using Cal.label_eq C P W a ys r ht hW ha hys
      simp [hread]
  have hlabel_weighted (W : Cal.Hist C) (a : Cal.Group C → Bin PT.tiling (G.cellPatch C)) :
      Hlaw.w W * ((binLaw W).w a *
        (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y)) =
      Hlaw.w W * ((binLaw W).w a *
        (Cal.U C W g (a g)).w y) := by
    by_cases hW : Hlaw.w W = 0
    · simp [hW]
    by_cases ha : (binLaw W).w a = 0
    · simp [ha]
    rw [hlabel_pr W a hW ha, Cal.label_marginals C P W a r y ht hW ha]
  have hstage1 : stageLaw.pr
      (fun z => F.label C (Cal.encode C z) b = y) =
      ∑ W, Hlaw.w W * ∑ a, (binLaw W).w a * (Cal.U C W g (a g)).w y := by
    calc
      _ = ∑ W, Hlaw.w W * ∑ a, (binLaw W).w a *
            (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y) := hstage0
      _ = _ := by
        apply Finset.sum_congr rfl
        intro W _
        calc
          _ = ∑ a, Hlaw.w W * ((binLaw W).w a *
                (labelLaw W a).pr (fun ys => F.label C (Cal.encode C (W, (a, ys))) b = y)) := by
            rw [Finset.mul_sum]
          _ = ∑ a, Hlaw.w W * ((binLaw W).w a * (Cal.U C W g (a g)).w y) := by
            apply Finset.sum_congr rfl
            intro a _
            exact hlabel_weighted W a
          _ = Hlaw.w W * ∑ a, (binLaw W).w a * (Cal.U C W g (a g)).w y := by
            rw [Finset.mul_sum]
  have hbin_push (W : Cal.Hist C) :
      ∑ a, (binLaw W).w a * (Cal.U C W g (a g)).w y =
        ∑ D, (binLaw W).pr (fun a => a g = D) * (Cal.U C W g D).w y := by
    let eval : (Cal.Group C → Bin PT.tiling (G.cellPatch C)) → Bin PT.tiling (G.cellPatch C) :=
      fun a => a g
    let pushed := FinLaw.map (binLaw W) eval
    have hpushw (D : Bin PT.tiling (G.cellPatch C)) :
        pushed.w D = (binLaw W).pr (fun a => a g = D) := by
      change (∑ a, if eval a = D then (binLaw W).w a else 0) =
        ∑ a, if eval a = D then (binLaw W).w a else 0
      rfl
    calc
      _ = pushed.E (fun D => (Cal.U C W g D).w y) := by
        change (binLaw W).E (fun a => (Cal.U C W g (eval a)).w y) = _
        exact (HypercubeRamsey.Lane_q_s16_comp1.finlaw_map_E
          (binLaw W) eval (fun D => (Cal.U C W g D).w y)).symm
      _ = _ := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro D _
        rw [hpushw]
  have hbin_weighted (W : Cal.Hist C) :
      Hlaw.w W * (∑ a, (binLaw W).w a * (Cal.U C W g (a g)).w y) =
        Hlaw.w W * (∑ D, (Cal.qtilde C P W g).w D * (Cal.U C W g D).w y) := by
    by_cases hW : Hlaw.w W = 0
    · simp [hW]
    rw [hbin_push W]
    congr 1
    apply Finset.sum_congr rfl
    intro D _
    rw [Cal.bin_marginals C P W g D ht hW]
  have hstage2 : stageLaw.pr
      (fun z => F.label C (Cal.encode C z) b = y) =
      ∑ W, Hlaw.w W * ∑ D, (Cal.qtilde C P W g).w D * (Cal.U C W g D).w y := by
    rw [hstage1]
    apply Finset.sum_congr rfl
    intro W _
    exact hbin_weighted W
  have htarget : (F.fresh C P).pr (fun s => F.label C s b = y) =
      stageLaw.pr (fun z => F.label C (Cal.encode C z) b = y) := by
    rw [Cal.fresh_eq C P ht, HypercubeRamsey.Lane_q_s16_comp1.finlaw_map_pr]
  rw [htarget, hstage2, FreshLabelCalibration.targetMass]
  simp [hb, ho, FinLaw.E, Hlaw, g, r]

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
