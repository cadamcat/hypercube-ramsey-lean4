import HypercubeRamsey.S16.Comparisons
import HypercubeRamsey.S16.Producers_q_s16_prod1
import HypercubeRamsey.S16.Producers_sol_s16_prod1

/-! Construction contracts connecting the conditional Section 16 estimates
to physical cells. These nodes are separate proof obligations: none assumes
an avoidance certificate, calibrated marginal, or fresh comparison bound. -/

namespace HypercubeRamsey.S16
namespace Lane_sol_fix2_s16

open Classical
open scoped BigOperators

abbrev EvenCellRole {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (C : G.Cell) :=
  {v : Pos T k // G.cellOf v = C ∧ IsEvenRole v}

/-- T14:75 and T16:415–417 use uniform-subset in-bin laws. D14.S currently
records only their support size, so this missing upstream input is explicit. -/
def SolverLabelsUniform {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop :=
  PT.tiling.mode.isCluster → ∀ i (S : SliceSolver κ PT.tiling i PT.mesh), PT.solver i = some S →
    ∀ g W D, 0 < S.q g W D → ∃ support : Finset (Fin (T.S.N k)),
      ∃ hs : support.Nonempty, ∀ y, S.U g W D y = (FinLaw.uniform support hs).w y

/-- Fixed Q0 room used in T16:338–342 and 400–427. Low scales need not
grow with n, so an eventual dimension cutoff cannot supply this input.
The current QCond records h ≤ d^.01, which alone does not bound h². -/
structure CellCalibrationScale {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Prop where
  room : PT.tiling.mode.isCluster → ∀ i,
    κ.d0 ≤ (PT.tiling.P i).d ∧
    (10 ^ 100 : ℕ) ≤ (PT.tiling.P i).d ∧
    4 * Real.exp (1.5 * (sliceK κ (PT.tiling.P i).h : ℝ) * sliceT κ (PT.tiling.P i).h) ≤
      Real.rpow ((PT.tiling.P i).d : ℝ) 0.05 ∧
    2 * ((PT.tiling.P i).h : ℝ) ^ 2 ≤ Real.rpow ((PT.tiling.P i).d : ℝ) 0.01 ∧
    ((PT.tiling.P i).h + 1 : ℝ) ≤ Real.rpow ((PT.tiling.P i).d : ℝ) 0.025 ∧
    16 * ((PT.tiling.P i).d : ℝ) ^ 2 * ((PT.tiling.P i).h + 1 : ℝ) ^ 2 *
      Real.rpow (sliceEps κ (PT.tiling.P i).h) (1 / 16 : ℝ) ≤
        Real.rpow ((PT.tiling.P i).d : ℝ) (-20)

/-- Raw data only. Slice laws are unrestricted; each slice is conditioned
separately. Pool restrictions and calibrated samplers are not fields. -/
structure CellRawData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) where
  Slice : G.Cell → Type
  [sliceFin : ∀ C, Fintype (Slice C)]
  [sliceDec : ∀ C, DecidableEq (Slice C)]
  Value : ∀ C, Slice C → Type
  [valueFin : ∀ C s, Fintype (Value C s)]
  [valueDec : ∀ C s, DecidableEq (Value C s)]
  sliceLaw : ∀ C s, FinLaw (Value C s)
  slicePass : ∀ C s, Finset (Value C s)
  slice_pos : ∀ C s, 0 < ∑ W ∈ slicePass C s, (sliceLaw C s).w W
  Group : G.Cell → Type
  [groupFin : ∀ C, Fintype (Group C)]
  [groupDec : ∀ C, DecidableEq (Group C)]
  groupOf : ∀ C, OddCellRole G C → Group C
  cellWords : ∀ C, (Slice C × IWord PT.tiling (G.cellPatch C)) ≃
    {v : Pos T k // G.cellOf v = C}
  axis : ∀ C, Fin (PT.tiling.P (G.cellPatch C)).h → Fin (T.S.n k)
  axis_injective : ∀ C, Function.Injective (axis C)
  axes_eq : ∀ C, Finset.univ.image (axis C) = PT.tiling.Icoord (G.cellPatch C)
  word_parity : PT.tiling.mode.isCluster → ∀ C s z,
    IsEvenRole (cellWords C (s, z)).1 ↔ IsEvenRole z
  word_flip : ∀ C s z j,
    (cellWords C (s, flipPos z j)).1 = flipPos (cellWords C (s, z)).1 (axis C j)
  word_outer : ∀ C s z z' j, j ∉ PT.tiling.Icoord (G.cellPatch C) →
    (cellWords C (s, z)).1 j = (cellWords C (s, z')).1 j
  qraw : ∀ C, (∀ s, Value C s) → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  pretrim : ∀ C, (∀ s, Value C s) → Group C → Finset (Bin PT.tiling (G.cellPatch C))
  qin : ∀ C, (∀ s, Value C s) → Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qin_eq : ∀ C W g D, (∀ s, W s ∈ slicePass C s ∧ (sliceLaw C s).w (W s) ≠ 0) →
    (qin C W g).w D = (if D ∈ pretrim C W g then (qraw C W g).w D else 0) /
      (∑ D' ∈ pretrim C W g, (qraw C W g).w D')
  U : ∀ C, (∀ s, Value C s) → Group C → Bin PT.tiling (G.cellPatch C) →
    FinLaw (Fin (T.S.N k))
  U_support : ∀ C W g D y, (U C W g D).w y ≠ 0 → y ∈ D.1
  rawPrior : ∀ C, (∀ s, Value C s) → (OddCellRole G C → Fin (T.S.N k)) →
    Pos T k → Fin (T.S.N k) → ℝ
  prior_nonneg : ∀ C W ys v y, 0 ≤ rawPrior C W ys v y
  prior_subprob : ∀ C W ys v, ∑ y, rawPrior C W ys v y ≤ 1

namespace CellRawData
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
instance instSliceFintype (R : CellRawData G) : ∀ C, Fintype (R.Slice C) := R.sliceFin
instance instSliceDecidableEq (R : CellRawData G) : ∀ C, DecidableEq (R.Slice C) := R.sliceDec
instance instValueFintype (R : CellRawData G) : ∀ C s, Fintype (R.Value C s) := R.valueFin
instance instValueDecidableEq (R : CellRawData G) : ∀ C s, DecidableEq (R.Value C s) := R.valueDec
instance instGroupFintype (R : CellRawData G) : ∀ C, Fintype (R.Group C) := R.groupFin
instance instGroupDecidableEq (R : CellRawData G) : ∀ C, DecidableEq (R.Group C) := R.groupDec
abbrev Hist (R : CellRawData G) (C : G.Cell) := ∀ s, R.Value C s
noncomputable def rawHistory (R : CellRawData G) (C : G.Cell) := FinLaw.pi (R.sliceLaw C)
noncomputable def history (R : CellRawData G) (C : G.Cell) :=
  FinLaw.pi fun s => FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s)

noncomputable def wordLabel (R : CellRawData G) (C : G.Cell)
    (ys : OddCellRole G C → Fin (T.S.N k)) (s : R.Slice C)
    (fallback : Fin (T.S.N k)) (z : IWord PT.tiling (G.cellPatch C)) :=
  if hz : ¬ IsEvenRole (R.cellWords C (s, z)).1 then
    ys ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ else fallback

/-- Exact links to D14.S, including its raw posterior, and to the direct
cleaned prior. The equivalences prevent an arbitrary prior experiment. -/
def SourceValid (R : CellRawData G) : Prop :=
  (PT.tiling.mode = .lowCluster ∧ SolverLabelsUniform PT ∧ ∀ C,
    ∃ S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh,
      PT.solver (G.cellPatch C) = some S ∧
      ∃ records : ∀ s, R.Value C s ≃ (∀ r, S.Val r),
      ∃ groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C,
        (∀ s, R.sliceLaw C s = FinLaw.map (S.recLaw PT.parameter) (records s).symm) ∧
        (∀ s W, W ∈ R.slicePass C s ↔ S.AllGood (records s W)) ∧
        (∀ s z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
          R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
            groups (s, S.groupOf z)) ∧
        (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) ∧
        (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) ∧
        (∀ W s g D y, (R.U C W (groups (s, g)) D).w y = S.U g (records s (W s)) D y) ∧
        (∀ W s (w : EvenRole PT.tiling (G.cellPatch C)) ys fallback,
          R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
            S.σ w (records s (W s)) (nbrLabels w.1 (R.wordLabel C ys s fallback)))) ∨
  (¬ PT.tiling.mode.isCluster ∧ ∀ C,
    Function.Injective (R.groupOf C) ∧
    (∀ s, Nonempty (R.Value C s ≃ Unit)) ∧
    (∀ s, R.slicePass C s = Finset.univ) ∧
    (∀ W g D, (R.qraw C W g).w D = 1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ)) ∧
    (∀ W g, R.pretrim C W g = Finset.univ) ∧
    (∀ W g D y, (R.U C W g D).w y = if y ∈ D.1 then 1 else 0) ∧
    ∃ h : (PT.envelope (G.cellPatch C)).Nonempty,
      ∀ W ys v, G.cellOf v = C → IsEvenRole v →
        R.rawPrior C W ys v = (Law.unifCore (PT.envelope (G.cellPatch C)) h).w)

noncomputable def rawLaw (R : CellRawData G) (C : G.Cell) (W : R.Hist C) :=
  FinLaw.bind (FinLaw.pi (R.qraw C W)) fun a =>
    FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
noncomputable def baseExperiment (R : CellRawData G) (C : G.Cell) (v : Pos T k) :
    PriorExperiment (T.S.N k) where
  State := R.Hist C × ((R.Group C → Bin PT.tiling (G.cellPatch C)) ×
    (OddCellRole G C → Fin (T.S.N k)))
  law := FinLaw.bind (R.rawHistory C) (R.rawLaw C)
  prior := fun ω => R.rawPrior C ω.1 ω.2.2 v
end CellRawData

/-- T16:167–177,259–288. A physical-kernel producer, before any estimates. -/
theorem cell_raw_data_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q),
      SolverLabelsUniform PT → n₀ ≤ T.S.n k →
      ∃ R : CellRawData H.geom, R.SourceValid := by
  classical
  refine ⟨0, ?_⟩
  intro T k PT K16 Q H hUniform hn
  by_cases hCluster : PT.tiling.mode.isCluster
  · have hMode : PT.tiling.mode = .lowCluster := by
      have hLow := Q.mode_low
      cases hm : PT.tiling.mode <;>
        simp_all [Mode.isCluster, Mode.isLow]
    let S : ∀ C : H.geom.Cell,
        SliceSolver κ PT.tiling (H.geom.cellPatch C) PT.mesh :=
      fun C => Classical.choose (Q.profiled_valid.cluster_solver hCluster (H.geom.cellPatch C))
    have hS : ∀ C, PT.solver (H.geom.cellPatch C) = some (S C) :=
      fun C => Classical.choose_spec
        (Q.profiled_valid.cluster_solver hCluster (H.geom.cellPatch C))
    have hh : ∀ i, (PT.tiling.P i).h ≤ T.S.n k := by
      intro i
      have hle : (PT.tiling.P i).h ≤
          Finset.univ.sup (fun i : Fin PT.tiling.m => (PT.tiling.P i).h) :=
        Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h) (Finset.mem_univ i)
      have := Q.profiled_valid.tiling_valid.prefix_internal_length
      omega
    have hp : ∀ i, 0 < (PT.tiling.P i).h := by
      intro i
      have hdy := (Q.profiled_valid.tiling_valid.cluster_data (Or.inl hMode) i).2.2.2.2.2.2.1
      rw [hdy]
      positivity
    let words := fun C => Lane_q_s16_prod1.clusterCellWords C
      (H.cell_partition.whole_slices C) (hh (H.geom.cellPatch C)) (hp (H.geom.cellPatch C))
    let q : ∀ C, (∀ _ : Lane_q_s16_prod1.ClusterCellSlice H.geom C, ∀ r, (S C).Val r) →
        (Lane_q_s16_prod1.ClusterCellSlice H.geom C × HypercubeRamsey.Group PT.tiling (H.geom.cellPatch C)) →
        FinLaw (Bin PT.tiling (H.geom.cellPatch C)) :=
      fun C W g => ⟨(S C).q g.2 (W g.1), (S C).q_nonneg g.2 (W g.1),
        (S C).q_sum g.2 (W g.1)⟩
    let trim := fun C (W : ∀ _ : Lane_q_s16_prod1.ClusterCellSlice H.geom C, ∀ r, (S C).Val r)
        (g : Lane_q_s16_prod1.ClusterCellSlice H.geom C ×
        HypercubeRamsey.Group PT.tiling (H.geom.cellPatch C)) =>
      (S C).pretrimBins (W g.1) g.2
    let prior := fun C (W : ∀ _ : Lane_q_s16_prod1.ClusterCellSlice H.geom C, ∀ r, (S C).Val r)
        (ys : OddCellRole H.geom C → Fin (T.S.N k)) (v : Pos T k) =>
      if hv : H.geom.cellOf v = C then
        let x := (words C).symm ⟨v, hv⟩
        if hz : IsEvenRole x.2 then
          (S C).σ ⟨x.2, hz⟩ (W x.1) (nbrLabels x.2 fun z =>
            if ho : ¬ IsEvenRole (words C (x.1, z)).1 then
              ys ⟨(words C (x.1, z)).1, (words C (x.1, z)).2, ho⟩
            else Classical.choose (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2)
        else 0
      else 0
    have σ_subprob : ∀ C (w : EvenRole PT.tiling (H.geom.cellPatch C)) W ls,
        (∑ y, (S C).σ w W ls y) ≤ 1 := by
      intro C w W ls
      by_cases hzero : (S C).σ w W ls = 0
      · simp [hzero]
      · exact le_of_eq ((S C).σ_prob w W ls hzero)
    have prior_on_word : ∀ C W ys s (w : EvenRole PT.tiling (H.geom.cellPatch C)),
        prior C W ys (words C (s, w.1)).1 =
          (S C).σ w (W s) (nbrLabels w.1 fun z =>
            if ho : ¬ IsEvenRole (words C (s, z)).1 then
              ys ⟨(words C (s, z)).1, (words C (s, z)).2, ho⟩
            else Classical.choose (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2) := by
      intro C W ys s w
      have hcell := (words C (s, w.1)).2
      have hback : (words C).symm ⟨(words C (s, w.1)).1, hcell⟩ = (s, w.1) :=
        (words C).symm_apply_apply (s, w.1)
      simp only [prior, dif_pos hcell, hback, w.2, ↓reduceDIte]
      rfl
    let R : CellRawData H.geom :=
      { Slice := fun C => Lane_q_s16_prod1.ClusterCellSlice H.geom C
        sliceFin := fun C => inferInstance
        sliceDec := fun C => Classical.decEq _
        Value := fun C _ => ∀ r, (S C).Val r
        valueFin := fun C s => inferInstance
        valueDec := fun C s => Classical.decEq _
        sliceLaw := fun C _ => (S C).recLaw PT.parameter
        slicePass := fun C _ => Finset.univ.filter (S C).AllGood
        slice_pos := by
          intro C s
          simpa [FinLaw.pr, Finset.sum_filter] using
            Lane_sol_s16_prod1.solver_good_pos Q.profiled_valid hMode (S C) (hS C)
        Group := fun C => Lane_q_s16_prod1.ClusterCellSlice H.geom C ×
          HypercubeRamsey.Group PT.tiling (H.geom.cellPatch C)
        groupFin := fun C => inferInstance
        groupDec := fun C => Classical.decEq _
        groupOf := fun C r =>
          let x := (words C).symm ⟨r.1, r.2.1⟩
          (x.1, (S C).groupOf x.2)
        cellWords := words
        axis := fun C => Lane_q_s16_prod1.cellAxis (H.geom.cellPatch C) (hh (H.geom.cellPatch C))
        axis_injective := fun C => Lane_q_s16_prod1.cellAxis_injective _ _
        axes_eq := fun C => Lane_q_s16_prod1.cellAxis_image _ _
        word_parity := by
          intro _ C s z
          exact Lane_sol_s16_prod1.combine_parity _ s z _
        word_flip := by
          intro C s z j
          exact Lane_sol_s16_prod1.combine_flip _ s z _ j
        word_outer := by
          intro C s z z' j hj
          simp [words, Lane_q_s16_prod1.clusterCellWords,
            Lane_q_s16_prod1.clusterCombine, hj]
        qraw := q
        pretrim := trim
        qin := fun C W g =>
          if hmass : 0 < ∑ D ∈ trim C W g, (q C W g).w D then
            FinLaw.cond (q C W g) (trim C W g) hmass else q C W g
        qin_eq := by
          intro C W g D hW
          have hg := hW g.1
          have hgood : (S C).AllGood (W g.1) := by simpa using hg.1
          have hmass := Lane_sol_s16_prod1.solver_pretrim_pos Q.profiled_valid hMode
            (S C) (hS C) (W g.1) hgood hg.2 g.2
          dsimp [q, trim] at hmass ⊢
          simp only [hmass, ↓reduceDIte, FinLaw.cond]
        U := fun C W g D => ⟨(S C).U g.2 (W g.1) D,
          (S C).U_nonneg g.2 (W g.1) D, (S C).U_sum g.2 (W g.1) D⟩
        U_support := by
          intro C W g D y hy
          exact (S C).U_support g.2 (W g.1) D y hy
        rawPrior := prior
        prior_nonneg := by
          intro C W ys v y
          dsimp [prior]
          split_ifs <;> first | exact (S C).σ_nonneg _ _ _ _ | exact le_rfl
        prior_subprob := by
          intro C W ys v
          dsimp [prior]
          split_ifs with hv hz
          · exact σ_subprob C _ _ _
          · simp
          · simp }
    refine ⟨R, Or.inl ⟨hMode, hUniform, ?_⟩⟩
    intro C
    refine ⟨S C, hS C, fun _ => Equiv.refl _, Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      exact (@Lane_sol_s16_prod1.map_refl (R.Value C s)
        (R.instValueFintype C s) (R.instValueDecidableEq C s)
        ((S C).recLaw PT.parameter)).symm
    · intro s W
      simp [R]
    · intro s z hz
      dsimp [R]
      rw [Equiv.symm_apply_apply]
    · intro W s g D
      rfl
    · intro W s g
      rfl
    · intro W s g D y
      rfl
    · intro W s w ys fallback
      change prior C W ys (words C (s, w.1)).1 =
        (S C).σ w (W s) (nbrLabels w.1 (R.wordLabel C ys s fallback))
      rw [prior_on_word]
      apply congrArg ((S C).σ w (W s))
      funext j
      have hodd : ¬ IsEvenRole (words C (s, flipPos w.1 j)).1 := by
        change ¬ IsEvenRole (Lane_q_s16_prod1.clusterCombine _ s (flipPos w.1 j) _)
        rw [Lane_sol_s16_prod1.combine_parity]
        intro he
        exact ((Lane_sol_s16_prod1.flip_parity w.1 j).mp he) w.2
      simp [nbrLabels, CellRawData.wordLabel, R, hodd]
  · have hDirect : PT.tiling.mode = .bounded ∨ PT.tiling.mode = .lowDirect := by
      cases hmode : PT.tiling.mode with
      | bounded => exact Or.inl rfl
      | lowDirect => exact Or.inr rfl
      | highDirect => have := Q.mode_low; simp [Mode.isLow, hmode] at this
      | lowCluster => exact False.elim (hCluster (by simp [Mode.isCluster, hmode]))
      | highSmall => have := Q.mode_low; simp [Mode.isLow, hmode] at this
      | highLarge => have := Q.mode_low; simp [Mode.isLow, hmode] at this
    have hHeight : ∀ i, (PT.tiling.P i).h = 0 := by
      intro i
      rcases hDirect with hb | hd
      · rcases Q.profiled_valid.tiling_valid.bounded_data hb with ⟨_, hdata⟩
        rcases hdata i with ⟨_, hh, _, _⟩
        exact hh
      · rcases Q.profiled_valid.tiling_valid.direct_data (Or.inl hd) i with
          ⟨_, _, _, _, hh, _, _⟩
        exact hh
    have hBinSize : ∀ i, (PT.tiling.P i).d = 1 := by
      intro i
      rcases hDirect with hb | hd
      · rcases Q.profiled_valid.tiling_valid.bounded_data hb with ⟨_, hdata⟩
        rcases hdata i with ⟨_, _, hd, _⟩
        exact hd
      · rcases Q.profiled_valid.tiling_valid.direct_data (Or.inl hd) i with
          ⟨_, _, _, _, _, hd, _⟩
        exact hd
    have hEnvelope : ∀ i, (PT.envelope i).Nonempty := by
      intro i
      have hcard : 0 < PT.activeVertices.card := by
        rw [Q.profiled_valid.direct_single_corner hCluster]
        norm_num
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
      obtain ⟨x, hx⟩ := (Q.profiled_valid.corner_clean i v hv).nonempty
      refine ⟨x, ?_⟩
      rw [Q.profiled_valid.envelope_eq i]
      exact Finset.mem_biUnion.mpr ⟨v, hv, hx⟩
    have hBins (i : Fin PT.tiling.m) : Nonempty (Bin PT.tiling i) := by
      have hY := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
      have hYne : (PT.tiling.P i).Y ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hY
      obtain ⟨D, hD⟩ := (PT.tiling.P i).bins.parts_nonempty hYne
      exact ⟨⟨D, hD⟩⟩
    have hBinUniv (i : Fin PT.tiling.m) :
        (Finset.univ : Finset (Bin PT.tiling i)).Nonempty := by
      obtain ⟨D⟩ := hBins i
      exact ⟨D, Finset.mem_univ D⟩
    have hBinCard (i : Fin PT.tiling.m) (D : Bin PT.tiling i) : D.1.card = 1 := by
      have h := Q.profiled_valid.tiling_valid.bins_card i D.1 D.2
      rw [hBinSize i] at h
      exact h
    let point : ∀ (i : Fin PT.tiling.m) (D : Bin PT.tiling i), Fin (T.S.N k) :=
      fun i D => Classical.choose (Finset.card_eq_one.mp (hBinCard i D))
    have point_spec (i : Fin PT.tiling.m) (D : Bin PT.tiling i) :
        D.1 = {point i D} := Classical.choose_spec (Finset.card_eq_one.mp (hBinCard i D))
    let R : CellRawData H.geom :=
      { Slice := fun C => Lane_q_s16_prod1.CellSlice H.geom C
        sliceFin := fun C => inferInstance
        sliceDec := fun C => Classical.decEq _
        Value := fun _ _ => Unit
        valueFin := fun _ _ => inferInstance
        valueDec := fun _ _ => Classical.decEq _
        sliceLaw := fun _ _ => FinLaw.dirac ()
        slicePass := fun _ _ => Finset.univ
        slice_pos := by
          intro C s
          simp [FinLaw.dirac]
        Group := fun C => OddCellRole H.geom C
        groupFin := fun C => inferInstance
        groupDec := fun C => Classical.decEq _
        groupOf := fun _ r => r
        cellWords := fun C => Lane_q_s16_prod1.directCellWords H.geom C
          (hHeight (H.geom.cellPatch C))
        axis := fun C j => by
          have hh := hHeight (H.geom.cellPatch C)
          rw [hh] at j
          exact Fin.elim0 j
        axis_injective := by
          intro C j j' hj
          have hh := hHeight (H.geom.cellPatch C)
          rw [hh] at j j'
          exact Fin.elim0 j
        axes_eq := by
          intro C
          apply Finset.ext
          intro j
          simp [Tiling.Icoord, topCoordinates, hHeight (H.geom.cellPatch C)]
        word_parity := by
          intro h C s z
          exact (hCluster h).elim
        word_flip := by
          intro C s z j
          have hh := hHeight (H.geom.cellPatch C)
          rw [hh] at j
          exact Fin.elim0 j
        word_outer := by
          intro C s z z' j hj
          rfl
        qraw := fun C _ _ => FinLaw.uniform Finset.univ (hBinUniv (H.geom.cellPatch C))
        pretrim := fun _ _ _ => Finset.univ
        qin := fun C _ _ => FinLaw.uniform Finset.univ (hBinUniv (H.geom.cellPatch C))
        qin_eq := by
          intro C W g D hW
          have hsum : ∑ D' ∈ Finset.univ,
              (FinLaw.uniform Finset.univ (hBinUniv (H.geom.cellPatch C))).w D' = 1 := by
            simpa using (FinLaw.uniform Finset.univ (hBinUniv (H.geom.cellPatch C))).sum_one
          simp [FinLaw.uniform, hsum]
        U := fun C _ _ D => FinLaw.dirac (point (H.geom.cellPatch C) D)
        U_support := by
          intro C W g D y hy
          have hy' : y = point (H.geom.cellPatch C) D := by
            simpa [FinLaw.dirac] using hy
          rw [point_spec (H.geom.cellPatch C) D]
          simp [hy']
        rawPrior := fun C _ _ _ y =>
          (Law.unifCore (PT.envelope (H.geom.cellPatch C)) (hEnvelope (H.geom.cellPatch C))).w y
        prior_nonneg := by
          intro C W ys v y
          exact (Law.unifCore (PT.envelope (H.geom.cellPatch C))
            (hEnvelope (H.geom.cellPatch C))).nonneg y
        prior_subprob := by
          intro C W ys v
          change ∑ y, (Law.unifCore (PT.envelope (H.geom.cellPatch C))
            (hEnvelope (H.geom.cellPatch C))).w y ≤ 1
          rw [(Law.unifCore (PT.envelope (H.geom.cellPatch C))
            (hEnvelope (H.geom.cellPatch C))).sum_eq_one] }
    refine ⟨R, ?_⟩
    right
    refine ⟨hCluster, ?_⟩
    intro C
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r r' h
      exact h
    · intro s
      exact ⟨Equiv.refl Unit⟩
    · intro s
      rfl
    · intro W g D
      simp [R, FinLaw.uniform]
    · intro W g
      rfl
    · intro W g D y
      rw [point_spec (H.geom.cellPatch C) D]
      simp [R, FinLaw.dirac]
    · exact hEnvelope (H.geom.cellPatch C)
    · intro W ys v hv he
      rfl

/-- The permission table uses unrestricted priors at the actual external
neighbor, including neighbors in other cells. No fresh prior is substituted. -/
structure CellPermissions {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G) where
  table : ∀ C, PermissionTable (R.Group C) (Bin PT.tiling (G.cellPatch C))
    (Fin (T.S.N k)) (OddCellRole G C × Fin (T.S.n k))
  n_eq : ∀ C, (table C).n = T.S.n k
  rate_eq : ∀ C, (table C).cperm = κ.cperm
  labels_eq : ∀ C D, (table C).labels D = D.1
  group_eq : ∀ C inc, (table C).groupOf inc = R.groupOf C inc.1
  bad_eq : ∀ C inc y, (table C).badMass inc y =
    if y ∈ (PT.tiling.P (G.cellPatch C)).Y ∧
        inc.2 ∉ PT.tiling.Icoord (G.cellPatch C) ∧ G.classOf inc.1.1 = none then
      (R.baseExperiment (G.cellOf (flipPos inc.1.1 inc.2)) (flipPos inc.1.1 inc.2)).expect
        (fun σ => if σ ≠ 0 ∧ |∑ x, σ x * hit (T.S.E k) PT.tiling.c x y - 1 / 2| >
          2 * bstar T k then 1 else 0)
    else 0

/-- S1 producer: retain the solver cap and its pretrim denominator, then
absorb their subexponential inflation at one uniform cutoff (T16:147–156). -/
theorem cell_permission_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage}, DeepDisc T κ.xs κ.α 0.04 →
      ∀ {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → n₀ ≤ T.S.n k →
      TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
        (κ.α * T.S.n k) ((T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))) →
      ∃ Perm : CellPermissions R, ∀ C W, (R.history C).w W ≠ 0 →
        PermissionLossHypotheses (Perm.table C) (R.qin C W) := by
  sorry

/-- A pool restriction of the actual incoming and permission kernels.
The fallback row handles zero denominators, as in T16:176. -/
structure CellRestrictedKernels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) where
  qbar : ∀ C, R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qtilde : ∀ C, CellPool G C → R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C))
  qbar_eq : ∀ C W g D, (R.history C).w W ≠ 0 →
    (qbar C W g).w D = (if D ∈ (Perm.table C).permitted g then (R.qin C W g).w D else 0) /
      (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D')
  qtilde_eq : ∀ C pool W g D, (R.history C).w W ≠ 0 →
    (∑ D' ∈ Finset.univ.image pool, (qbar C W g).w D') ≠ 0 →
    (qtilde C pool W g).w D =
      (if D ∈ Finset.univ.image pool then (qbar C W g).w D else 0) /
        (∑ D' ∈ Finset.univ.image pool, (qbar C W g).w D')

namespace CellRestrictedKernels
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
variable {R : CellRawData G} {Perm : CellPermissions R}
noncomputable def participants (_K : CellRestrictedKernels R Perm) (C : G.Cell)
    (v : EvenCellRole G C) : Finset (OddCellRole G C) :=
  Finset.univ.filter fun r => ∃ j ∈ PT.tiling.Icoord (G.cellPatch C), r.1 = flipPos v.1 j
noncomputable def labelLaw (_K : CellRestrictedKernels R Perm) (C : G.Cell) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :=
  FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
noncomputable def failure (K : CellRestrictedKernels R Perm) (C : G.Cell) (W : R.Hist C)
    (v : EvenCellRole G C) (a : R.Group C → Bin PT.tiling (G.cellPatch C)) : ℝ :=
  if PT.tiling.mode.isCluster then (K.labelLaw C W a).pr (fun ys => R.rawPrior C W ys v.1 = 0) else 0
noncomputable def binProblem (K : CellRestrictedKernels R Perm) (C : G.Cell)
    (pool : CellPool G C) (W : R.Hist C) :
    GroupBinProblem (R.Group C) (Bin PT.tiling (G.cellPatch C)) (EvenCellRole G C) (Fin (T.S.N k)) where
  target := K.qtilde C pool W
  participants := fun v => (K.participants C v).image (R.groupOf C)
  failureMass := K.failure C W
  contribution := fun g D y => ∑ r : OddCellRole G C,
    if R.groupOf C r = g then (R.U C W g D).w y else 0
  d := (PT.tiling.P (G.cellPatch C)).d
  ε := sliceEps κ (PT.tiling.P (G.cellPatch C)).h
end CellRestrictedKernels

/-- Diagnostic identities use sums over pool images, actual independent
role failures, their group-bin pins, and the actual label load. Probe maps
allow the finite check family to index groups, stars, and all positive pins. -/
structure CellDiagnosticLink {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell)
    {Check : Type} [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
      (R.Hist C) Check (T.S.n k) c0) where
  groupProbe : R.Group C → D.Group
  starProbe : EvenCellRole G C → D.Group
  pinProbe : EvenCellRole G C → R.Group C → Bin PT.tiling (G.cellPatch C) → D.Group
  epsilon_eq : D.ε = sliceEps κ (PT.tiling.P (G.cellPatch C)).h
  normalizer_eq : ∀ pool W g, (R.history C).w W ≠ 0 →
    D.poolNormalizer pool (groupProbe g) W = ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b
  failure_eq : ∀ pool W v, (R.history C).w W ≠ 0 →
    D.internalFailure pool (starProbe v) W = (K.binProblem C pool W).independentFailure v
  pinned_failure_eq : ∀ pool W v g b, (R.history C).w W ≠ 0 →
    D.pinnedInternalFailure pool (pinProbe v g b) W = (K.binProblem C pool W).pinnedFailure v g b
  history_eq : ∀ pool, D.historyLaw pool = R.history C
  Column : D.LoadColumn ≃ Fin (T.S.N k)
  load_eq : ∀ pool W y, D.loadValue pool W y =
    ∑ r : OddCellRole G C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w (Column y)
  threshold_eq : D.loadThreshold = κ.θstar

/-- S3 diagnostic producer. The exponent and cutoff precede every stage,
cell, history and pin; means and sensitivities are conclusions, not inputs.
T16:207–257 and 259–288 supply the two different concentration budgets. -/
theorem cell_pool_diagnostics_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ c0 : ℝ, c0 = 1 / 2 ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
        (R : CellRawData H.geom) (Perm : CellPermissions R),
        R.SourceValid → n₀ ≤ T.S.n k →
        (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
        ∃ K : CellRestrictedKernels R Perm, ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
          ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
            (R.Hist C) Check (T.S.n k) c0,
            Nonempty (CellDiagnosticLink K C D) ∧
            Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
  sorry

/-- S2 group producer at successful physical data. The capacity subset
certificates of T16:330–342 and the actual star tests produce hP.certificates. -/
theorem successful_group_bin_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
      (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
        (R.Hist C) Check (T.S.n k) c0),
      R.SourceValid → PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      CellDiagnosticLink K C D → ∀ pool W, D.typical pool → D.loadGate pool W →
      (R.history C).w W ≠ 0 → GroupBinHypotheses hκ (K.binProblem C pool W) := by
  sorry

private theorem group_bin_dirac_obstruction {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (r : OddCellRole G C) (b : Bin PT.tiling (G.cellPatch C)) (y : Fin (T.S.N k))
    (hdirac : (R.U C W (R.groupOf C r) b).w y = 1)
    (hd : 2 ≤ (PT.tiling.P (G.cellPatch C)).d) :
    ¬ GroupBinHypotheses hκ (K.binProblem C pool W) := by
  intro hP
  have hlo : (R.U C W (R.groupOf C r) b).w y ≤
      (K.binProblem C pool W).contribution (R.groupOf C r) b y := by
    change _ ≤ ∑ r' : OddCellRole G C,
      if R.groupOf C r' = R.groupOf C r then (R.U C W (R.groupOf C r) b).w y else 0
    have hs := Finset.single_le_sum (s := Finset.univ) (a := r)
      (f := fun r' : OddCellRole G C =>
        if R.groupOf C r' = R.groupOf C r then (R.U C W (R.groupOf C r) b).w y else 0)
      (by intro r' _; split_ifs <;> first | exact (R.U C W _ b).nonneg y | exact le_rfl)
      (Finset.mem_univ r)
    simpa using hs
  have hcap := (hP.contribution_range (R.groupOf C r) b y).2
  have hlt : Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.5) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hd)
    · norm_num
  rw [hdirac] at hlo
  exact (not_le_of_gt hlt) (hlo.trans hcap)

/-- A role problem linked to the successful physical bins, not arbitrary
targets/tests. In direct modes its single block is the whole cell pool. -/
structure CellRoleProblem {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell)
    (pool : CellPool G C) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) where
  Block : Type
  [blockFin : Fintype Block]
  [blockDec : DecidableEq Block]
  problem : RoleLabelProblem (OddCellRole G C) (Fin (T.S.N k)) (EvenCellRole G C) Block
  regime_eq : problem.regime = if PT.tiling.mode.isCluster then .cluster else .direct
  scale_eq : problem.d = if PT.tiling.mode.isCluster then (PT.tiling.P (G.cellPatch C)).d else G.nslot C
  height_eq : problem.h = (PT.tiling.P (G.cellPatch C)).h
  targets_eq : ∀ r y, (problem.target r).w y =
    if PT.tiling.mode.isCluster then (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y else
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
  participants_eq : ∀ v, problem.participants v = K.participants C v
  tests_eq : ∀ v ys, problem.starBad v ys ↔ PT.tiling.mode.isCluster ∧ R.rawPrior C W ys v.1 = 0
  cluster_blocks : PT.tiling.mode.isCluster →
    ∃ bins : Block ≃ Bin PT.tiling (G.cellPatch C),
      (∀ b, problem.blockLabels b = (bins b).1) ∧
      ∀ r, bins (problem.blockOf r) = a (R.groupOf C r)
  direct_block : ¬ PT.tiling.mode.isCluster →
    ∃ _one : Block ≃ Unit, ∀ b, problem.blockLabels b = (Finset.univ.image pool).biUnion (fun D => D.1)

attribute [instance] CellRoleProblem.blockFin CellRoleProblem.blockDec

/-- S2 role producer. The two independent failure endpoints now belong to
the physical producer contract (T16:409–417); the certificate uses independent
whole-bin injection variables, not independent individual role labels. -/
theorem successful_role_label_hypotheses {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
      (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
        (R.Hist C) Check (T.S.n k) c0),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      CellDiagnosticLink K C D →
      ∀ pool W a, D.typical pool → D.loadGate pool W → (R.history C).w W ≠ 0 →
      (PT.tiling.mode.isCluster → (K.binProblem C pool W).safe a) →
      (PT.tiling.mode.isCluster → ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0) →
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem ∧
        (∀ v, L.problem.independentStarFailure v ≤
          Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ)) ∧
        (∀ v r y, L.problem.pinnedStarFailure v r y ≤
          2 * (PT.tiling.P (H.geom.cellPatch C)).d *
            Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ)) := by
  sorry

/-- Selected lookup kernels after applying the two unchanged calibration
exports. Direct modes omit the group calibration and use only P16.4. -/
structure CellCalibratedStages {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) where
  typical : ∀ C, CellPool G C → Prop
  gate : ∀ C, CellPool G C → Finset (R.Hist C)
  gate_pos : ∀ C pool, typical C pool → 0 < ∑ W ∈ gate C pool, (R.history C).w W
  binLaw : ∀ C, CellPool G C → R.Hist C → FinLaw (R.Group C → Bin PT.tiling (G.cellPatch C))
  bin_marginals : ∀ C pool W g b, typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 →
    (binLaw C pool W).pr (fun a => a g = b) = (K.qtilde C pool W g).w b
  bin_feasible : ∀ C pool W, typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 →
    PT.tiling.mode.isCluster → (K.binProblem C pool W).feasible (binLaw C pool W)
  labelLaw : ∀ C, CellPool G C → R.Hist C →
    (R.Group C → Bin PT.tiling (G.cellPatch C)) → FinLaw (OddCellRole G C → Fin (T.S.N k))
  label_marginals : ∀ C pool W a r y, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    (labelLaw C pool W a).pr (fun ys => ys r = y) =
      (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y
  label_injective : ∀ C pool W a ys, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    (labelLaw C pool W a).w ys ≠ 0 → Function.Injective ys
  cluster_label_feasible : ∀ C pool W a, typical C pool → W ∈ gate C pool →
    (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
    PT.tiling.mode.isCluster → ∃ L : CellRoleProblem K C pool W a,
      L.problem.feasible (labelLaw C pool W a)
  /-- In direct modes P16.4 calibrates the whole label law first; bins are
  then its singleton-bin readout, and the conditional label stage is Dirac. -/
  direct_joint : ∀ C pool W (S : Finset (OddCellRole G C)) (ys : OddCellRole G C → Fin (T.S.N k)),
    typical C pool → W ∈ gate C pool → (R.history C).w W ≠ 0 → ¬ PT.tiling.mode.isCluster →
    (S.card : ℝ) ≤ Real.rpow (G.nslot C : ℝ) 0.025 →
    (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr (fun ω => ∀ r ∈ S, ω.2 r = ys r) ≤
      Real.exp (Real.rpow (G.nslot C : ℝ) (-0.04) * S.card) *
        ∏ r ∈ S, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w (ys r))

/-- Keep every chosen diagnostic linked when assembling the lookup kernels. -/
structure CellDiagnostics {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (c0 : ℝ) where
  exponent_half : c0 = 1 / 2
  Check : G.Cell → Type
  [checkFin : ∀ C, Fintype (Check C)]
  diagnostic : ∀ C, CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
    (R.Hist C) (Check C) (T.S.n k) c0
  linked : ∀ C, CellDiagnosticLink K C (diagnostic C)
  concentration : ∀ C, PoolConcentrationHypotheses (diagnostic C)
  load : ∀ C, LoadGateHypotheses (diagnostic C)

attribute [instance] CellDiagnostics.checkFin

/-- This assembly consumes the hypotheses produced above and the two
calibration exports; it does not assume any calibrated law as an input. -/
theorem cell_calibrated_stages_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0), R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∃ S : CellCalibratedStages K,
        (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) ∧
        ∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool) := by
  sorry

/-- Transport identities for the constructed fresh state. Histories and
groups are reindexed explicitly, so the calibration record cannot choose
unrelated kernels or labels. -/
structure FreshConstructionLink {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} {K : CellRestrictedKernels R Perm}
    (S : CellCalibratedStages K) (F : FreshCell G) (Cal : FreshLabelCalibration F) where
  histories : ∀ C, Cal.Hist C ≃ R.Hist C
  groups : ∀ C, Cal.Group C ≃ R.Group C
  history_eq : ∀ C, Cal.history C = FinLaw.map (R.history C) (histories C).symm
  group_eq : ∀ C r, groups C (Cal.groupOf C r) = R.groupOf C r
  incoming_eq : ∀ C W g, Cal.qin C W g = R.qin C (histories C W) (groups C g)
  U_eq : ∀ C W g b, Cal.U C W g b = R.U C (histories C W) (groups C g) b
  permission_eq : ∀ C g, Cal.permitted C g = (Perm.table C).permitted (groups C g)
  restricted_eq : ∀ C pool W g, Cal.qtilde C pool W g = K.qtilde C pool (histories C W) (groups C g)
  typical_eq : ∀ C pool, F.typical C pool ↔ S.typical C pool
  gate_eq : ∀ C pool, Cal.gate C pool = (S.gate C pool).image (histories C).symm
  bin_eq : ∀ C pool W, Cal.binSampler C pool W =
    FinLaw.map (S.binLaw C pool (histories C W)) (fun a g => a (groups C g))
  label_eq : ∀ C pool W a, Cal.labelSampler C pool W a =
    S.labelLaw C pool (histories C W) (fun g => a ((groups C).symm g))
  prior_eq : ∀ C pool W a ys v, F.typical C pool → (Cal.gatedHistory C pool).w W ≠ 0 →
    (Cal.binSampler C pool W).w a ≠ 0 → (Cal.labelSampler C pool W a).w ys ≠ 0 →
    G.cellOf v = C → IsEvenRole v →
    F.prior C (Cal.encode C (W, a, ys)) v = R.rawPrior C (histories C W) ys v

/-- S3 fresh calibration producer (T16:294–296,469–482). Its inputs are
physical stages already certified by P16.3/P16.4; exact identities and all
three scalar denominator budgets are outputs. -/
theorem fresh_label_calibration_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      ∃ F : FreshCell H.geom, ∃ Cal : FreshLabelCalibration F,
        Nonempty (FreshConstructionLink S F Cal) := by
  sorry

/-- The intended internal validity: exact probability priors at every even
site, with support on common neighbors of its internal odd labels. -/
def InternallyValid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G)
    (Cal : FreshLabelCalibration F) (C : G.Cell) (pool : F.Pool C) (s : F.State C) : Prop :=
  (∀ b, G.cellOf b = C → ¬ IsEvenRole b →
    F.label C s b ∈ Cal.permittedLabels C pool b ∧ poolContainsLabel pool (F.label C s b)) ∧
  ∀ v, G.cellOf v = C → IsEvenRole v →
    (∑ y, F.prior C s v y) = 1 ∧
      ∀ y, F.prior C s v y ≠ 0 → y ∈ PT.envelope (G.cellPatch C) ∧
        ∀ j ∈ PT.tiling.Icoord (G.cellPatch C),
          Hits (T.S.E k) PT.tiling.c y (F.label C s (flipPos v j))

/-- S3's omitted validity assertion is a separate output, preserving the
six existing comparison export types (T16:457–459). Arbitrary fresh states
need not satisfy it; the construction chooses the finite state space. -/
theorem fresh_cell_spec_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      ∃ F : FreshCell H.geom, ∃ Cal : FreshLabelCalibration F,
        Nonempty (FreshConstructionLink S F Cal) ∧
        FreshCell.Spec F (InternallyValid F Cal) Cal.permittedLabels := by
  sorry

/-- S3 prior pipeline producer (T16:513–529). It uses the same fresh state,
calibrated stages and raw readout as the singleton construction; the source
identity and the equality of base expectations are outputs. -/
theorem fresh_prior_pipeline_exists {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (_hCalibration : CellCalibrationScale PT)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      {c0 : ℝ} (Ds : CellDiagnostics K c0) (S : CellCalibratedStages K)
      (F : FreshCell H.geom) (Cal : FreshLabelCalibration F),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C pool, S.typical C pool ↔ (Ds.diagnostic C).typical pool) →
      (∀ C pool, S.gate C pool = Finset.univ.filter ((Ds.diagnostic C).loadGate pool)) →
      FreshConstructionLink S F Cal →
      ∀ C v, H.geom.cellOf v = C → IsEvenRole v →
      ∃ P : FreshPriorPipeline F C v, FreshPriorSourceValid P ∧
        ∀ Φ, P.baseExperiment.expect Φ = (R.baseExperiment C v).expect Φ := by
  sorry

end Lane_sol_fix2_s16
end HypercubeRamsey.S16
