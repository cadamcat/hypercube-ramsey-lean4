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

private theorem finLaw_indicator_range {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ P.E (fun ω => if A ω then 1 else 0) ∧
      P.E (fun ω => if A ω then 1 else 0) ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg fun ω _ => by
      dsimp
      split_ifs <;> simp [P.nonneg]
  · calc
      P.E (fun ω => if A ω then 1 else 0) ≤ ∑ ω, P.w ω := by
        apply Finset.sum_le_sum
        intro ω _
        dsimp only
        split_ifs <;> simp [P.nonneg]
      _ = 1 := P.sum_one

private theorem physical_bins_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (b b' : Bin PT.tiling i) (hne : b ≠ b') : Disjoint b.1 b'.1 := by
  exact (PT.tiling.P i).bins.disjoint b.2 b'.2
    (fun h => hne (Subtype.ext h))

private noncomputable def physical_permissions {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) : CellPermissions R := by
  classical
  let bad : ∀ C, OddCellRole G C × Fin (T.S.n k) → Fin (T.S.N k) → ℝ :=
    fun C inc y =>
      if y ∈ (PT.tiling.P (G.cellPatch C)).Y ∧
          inc.2 ∉ PT.tiling.Icoord (G.cellPatch C) ∧ G.classOf inc.1.1 = none then
        (R.baseExperiment (G.cellOf (flipPos inc.1.1 inc.2)) (flipPos inc.1.1 inc.2)).expect
          (fun σ => if σ ≠ 0 ∧ |∑ x, σ x * hit (T.S.E k) PT.tiling.c x y - 1 / 2| >
            2 * bstar T k then 1 else 0)
      else 0
  refine {
    table := fun C => {
      n := T.S.n k
      n_pos := lt_of_lt_of_le (by omega) Q.n_large
      cperm := κ.cperm
      cperm_pos := hκ.cperm_rng.1
      groupOf := fun inc => R.groupOf C inc.1
      labels := fun D => D.1
      badMass := bad C
      permitted := fun g => Finset.univ.filter fun D =>
        ∀ inc, R.groupOf C inc.1 = g → ∀ y ∈ D.1,
          bad C inc y ≤ Real.exp (-κ.cperm * T.S.n k)
      permitted_iff := by intro g D; simp }
    n_eq := fun _ => rfl
    rate_eq := fun _ => rfl
    labels_eq := fun _ _ => rfl
    group_eq := fun _ _ => rfl
    bad_eq := fun _ _ _ => rfl }

private theorem permissions_range {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    (Perm : CellPermissions R) (C : G.Cell) (inc : OddCellRole G C × Fin (T.S.n k))
    (y : Fin (T.S.N k)) :
    0 ≤ (Perm.table C).badMass inc y ∧ (Perm.table C).badMass inc y ≤ 1 := by
  rw [Perm.bad_eq]
  split_ifs
  · let P := R.baseExperiment (G.cellOf (flipPos inc.1.1 inc.2)) (flipPos inc.1.1 inc.2)
    simpa only [PriorExperiment.expect, P] using
      (finLaw_indicator_range P.law (fun ω =>
        P.prior ω ≠ 0 ∧ |∑ x, P.prior ω x * hit (T.S.E k) PT.tiling.c x y - 1 / 2| >
          2 * bstar T k))
  · norm_num

private theorem permissions_labels_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    (Perm : CellPermissions R) (C : G.Cell) (y : Fin (T.S.N k)) :
    (binsContainingLabel (Perm.table C) y).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  have hy : y ∈ b.1 := by simpa [binsContainingLabel, Perm.labels_eq] using hb
  have hy' : y ∈ b'.1 := by simpa [binsContainingLabel, Perm.labels_eq] using hb'
  by_contra hne
  exact Finset.disjoint_left.mp (physical_bins_disjoint _ b b' hne) hy hy'

private theorem direct_incoming_uniform {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : ¬ PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C)
    (hSlices : ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0)
    (g : R.Group C) (D : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w D = 1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) := by
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · exact (hc (by simp [hMode, Mode.isCluster])).elim
  · obtain ⟨hInj, hVal, hPass, hQ, hTrim, hU, h, hPrior⟩ := hSource C
    rw [R.qin_eq C W g D hSlices, hTrim]
    simp only [Finset.mem_univ, if_true, FinLaw.sum_one, div_one]
    exact hQ W g D

private theorem permission_estimates {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R),
      R.SourceValid → n₀ ≤ T.S.n k →
      TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs)
        (κ.α * T.S.n k) ((T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))) →
      ∀ C W, (R.history C).w W ≠ 0 →
        (∀ inc, (∑ y, (Perm.table C).badMass inc y) ≤
          Real.exp (-3 * (Perm.table C).cperm * (Perm.table C).n) *
            Fintype.card (Fin (T.S.N k))) ∧
        (∀ g, ((permissionIncidences (Perm.table C) g).card : ℝ) *
          ((Fintype.card (Fin (T.S.N k)) : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
            Real.exp ((Perm.table C).cperm * (Perm.table C).n)) ∧
        (∀ g D, (R.qin C W g).w D ≤
          Real.exp ((Perm.table C).cperm * (Perm.table C).n / 2) /
            Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) := by
  -- Remaining: exceptional_second for the actual raw posterior, the h*n
  -- incidence bound, and the quantitative pretrim denominator.
  sorry

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
  classical
  obtain ⟨n₁, hEstimates⟩ := permission_estimates hκ
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (Real.log 4 / κ.cperm)
  refine ⟨max n₁ n₂, ?_⟩
  intro T _hDeep k PT K16 Q H R hR hn hDisc
  let Perm := physical_permissions hκ Q R
  refine ⟨Perm, ?_⟩
  intro C W hW
  obtain ⟨hav, hratio, hcap⟩ := hEstimates Q H R Perm hR
    (le_trans (Nat.le_max_left _ _) hn) hDisc C W hW
  have hBins : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := by
    have hY := (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2
    obtain ⟨b, hb⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty
      (Finset.nonempty_iff_ne_empty.mp hY)
    exact ⟨⟨b, hb⟩⟩
  have hLabels : Nonempty (Fin (T.S.N k)) := by
    obtain ⟨y, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2
    exact ⟨y⟩
  refine {
    bins_nonempty := hBins
    labels_nonempty := hLabels
    mean_bad_mass := permissions_range Perm C
    average_bad_mass := hav
    incidence_label_ratio := hratio
    labels_disjoint := permissions_labels_disjoint Perm C
    incoming_cap := hcap
    threshold_large := ?_ }
  rw [Perm.n_eq, Perm.rate_eq]
  have hn₂' : (n₂ : ℝ) ≤ T.S.n k := by
    exact_mod_cast le_trans (Nat.le_max_right n₁ n₂) hn
  have hdiv : Real.log 4 / κ.cperm ≤ (T.S.n k : ℝ) := hn₂.trans hn₂'
  have hmul := (div_le_iff₀ hκ.cperm_rng.1).mp hdiv
  nlinarith

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
  -- zero on null-target bins: the producers bound atoms only where the target is positive (sol-s16-prod1)
  contribution := fun g D y =>
    if (K.qtilde C pool W g).w D = 0 then 0 else
      ∑ r : OddCellRole G C, if R.groupOf C r = g then (R.U C W g D).w y else 0
  d := (PT.tiling.P (G.cellPatch C)).d
  ε := sliceEps κ (PT.tiling.P (G.cellPatch C)).h
end CellRestrictedKernels

private theorem supported_history {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
    ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
  intro s
  exact Lane_sol_s16_prod1.cond_support _ _ _ _
    (Lane_sol_s16_prod1.pi_support _ W hW s)

private theorem restricted_kernels_exists {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (R : CellRawData G) (Perm : CellPermissions R)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W)) :
    ∃ K : CellRestrictedKernels R Perm, True := by
  classical
  let mass := fun C W g => ∑ D ∈ (Perm.table C).permitted g, (R.qin C W g).w D
  have hmass : ∀ C W g, (R.history C).w W ≠ 0 → 0 < mass C W g := by
    intro C W g hW
    obtain ⟨c, hc, _hcount, hretained⟩ := permission_loss hκ (Perm.table C) (R.qin C W)
      (hPerm C W hW)
    have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hn : (0 : ℝ) < (Perm.table C).n := by exact_mod_cast (Perm.table C).n_pos
      nlinarith
    have h := hretained g
    dsimp [mass]
    linarith
  let qbar : ∀ C, R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C)) :=
    fun C W g => if hm : 0 < mass C W g then
      FinLaw.cond (R.qin C W g) ((Perm.table C).permitted g) hm else R.qin C W g
  let qtilde : ∀ C, CellPool G C → R.Hist C → R.Group C → FinLaw (Bin PT.tiling (G.cellPatch C)) :=
    fun C pool W g =>
      if hm : 0 < ∑ D ∈ Finset.univ.image pool, (qbar C W g).w D then
        FinLaw.cond (qbar C W g) (Finset.univ.image pool) hm else qbar C W g
  refine ⟨{
    qbar := qbar
    qtilde := qtilde
    qbar_eq := ?_
    qtilde_eq := ?_ }, trivial⟩
  · intro C W g D hW
    simp only [qbar, dif_pos (hmass C W g hW)]
    rfl
  · intro C pool W g D _hW hm
    have hnonneg : 0 ≤ ∑ D ∈ Finset.univ.image pool, (qbar C W g).w D :=
      Finset.sum_nonneg fun D _ => (qbar C W g).nonneg D
    have hpos : 0 < ∑ D ∈ Finset.univ.image pool, (qbar C W g).w D :=
      lt_of_le_of_ne hnonneg (Ne.symm hm)
    simp only [qtilde, dif_pos hpos]
    rfl

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

private theorem typical_pool_mass_ne_zero {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
      (R.Hist C) Check (T.S.n k) c0)
    (L : CellDiagnosticLink K C D) (pool : CellPool G C) (ht : D.typical pool)
    (W : R.Hist C) (hW : (R.history C).w W ≠ 0) (g : R.Group C) :
    (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0 := by
  have hnorm := (D.checks_cover pool ht.2).1 (L.groupProbe g) W
  rw [L.normalizer_eq pool W g hW] at hnorm
  have hn : (1 : ℝ) < T.S.n k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) Q.n_large
  have hsmall : Real.rpow (T.S.n k : ℝ) (-4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hn (by norm_num)
  intro hz
  rw [hz] at hnorm
  norm_num only [zero_div, zero_sub, abs_neg, abs_one] at hnorm
  linarith

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
  classical
  -- The physical restrictions are independent of the concentration estimates.
  -- The cutoff must still precede the cell/history/pin union budgets.
  have hBudgets : ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R)
      (K : CellRestrictedKernels R Perm),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
        ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
          (R.Hist C) Check (T.S.n k) (1 / 2),
          Nonempty (CellDiagnosticLink K C D) ∧
          Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
    -- Requires unnormalized empirical star/pin polynomials; normalizing first
    -- does not give a uniform one-slot sensitivity at zero denominators.
    sorry
  obtain ⟨n₀, hBudgets⟩ := hBudgets
  refine ⟨n₀, 1 / 2, rfl, ?_⟩
  intro T k PT K16 Q H R Perm hR hn hPerm
  obtain ⟨K, _⟩ := restricted_kernels_exists hκ R Perm hPerm
  exact ⟨K, hBudgets Q H R Perm K hR hn hPerm⟩

private theorem physical_participants_count {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (v : EvenCellRole G C) :
    (K.participants C v).card ≤ (PT.tiling.P (G.cellPatch C)).h := by
  classical
  have hsub : (K.participants C v).image Subtype.val ⊆
      (PT.tiling.Icoord (G.cellPatch C)).image (flipPos v.1) := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, heq⟩ := (Finset.mem_filter.mp hr).2
    exact Finset.mem_image.mpr ⟨j, hj, heq.symm⟩
  have haxes : (PT.tiling.Icoord (G.cellPatch C)).card = (PT.tiling.P (G.cellPatch C)).h := by
    rw [← R.axes_eq C, Finset.card_image_of_injective _ (R.axis_injective C)]
    simp
  calc
    (K.participants C v).card = ((K.participants C v).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((PT.tiling.Icoord (G.cellPatch C)).image (flipPos v.1)).card :=
      Finset.card_le_card hsub
    _ ≤ (PT.tiling.Icoord (G.cellPatch C)).card := Finset.card_image_le
    _ = (PT.tiling.P (G.cellPatch C)).h := haxes

private theorem slice_epsilon_range {κ : CConsts} (hκ : κ.Admissible) (h : ℕ) :
    0 < sliceEps κ h ∧ sliceEps κ h ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have hk : (0 : ℝ) ≤ sliceK κ h := Nat.cast_nonneg _
    have := mul_nonneg (mul_nonneg ha.le hk) hh
    nlinarith

private theorem group_contribution_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) (y : Fin (T.S.N k)) :
    0 ≤ (K.binProblem C pool W).contribution g b y := by
  classical
  simp only [CellRestrictedKernels.binProblem]
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro r _
    split_ifs <;> first | exact (R.U C W g b).nonneg y | exact le_rfl

private theorem thetaStar_slack {κ : CConsts} (hκ : κ.Admissible) :
    κ.θstar ≤ 1 / 10 := by
  have htheta := hκ.clock.2.1
  have hb := hκ.bucket
  rw [htheta] at hb
  have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hb.1
  nlinarith [mul_le_mul_of_nonneg_right hKp hb.2.2.2.2.le]

private theorem nominal_load_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C) (y : Fin (T.S.N k)) :
    (K.binProblem C pool W).nominalColumnLoad y =
      ∑ r : OddCellRole G C, ∑ b,
        (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y := by
  classical
  let P := K.binProblem C pool W
  have hmul (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
      (P.target g).w b * P.contribution g b y =
      ∑ r : OddCellRole G C, if R.groupOf C r = g then
        (P.target g).w b * (R.U C W g b).w y else 0 := by
    by_cases hb : (K.qtilde C pool W g).w b = 0
    · simp [P, CellRestrictedKernels.binProblem, hb]
    · simp only [P, CellRestrictedKernels.binProblem, hb, ↓reduceIte]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
  calc
    P.nominalColumnLoad y = ∑ g, (FinLaw.pi P.target).E (fun a => P.contribution g (a g) y) := by
      unfold GroupBinProblem.nominalColumnLoad GroupBinProblem.independentLaw
        GroupBinProblem.columnLoad FinLaw.E
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ g, ∑ b, (P.target g).w b * P.contribution g b y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Lane_sol_s16_prod1.pi_coordinate_E P.target g (fun b => P.contribution g b y)
    _ = ∑ g, ∑ b, ∑ r : OddCellRole G C, if R.groupOf C r = g then
        (P.target g).w b * (R.U C W g b).w y else 0 := by simp_rw [hmul]
    _ = ∑ g, ∑ r : OddCellRole G C, ∑ b, if R.groupOf C r = g then
        (P.target g).w b * (R.U C W g b).w y else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = ∑ r : OddCellRole G C, ∑ g, ∑ b, if R.groupOf C r = g then
        (P.target g).w b * (R.U C W g b).w y else 0 := Finset.sum_comm
    _ = ∑ r : OddCellRole G C, ∑ b, ∑ g, if R.groupOf C r = g then
        (P.target g).w b * (R.U C W g b).w y else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = _ := by simp [P, CellRestrictedKernels.binProblem]

private theorem supported_column_load_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C))
    (ha : ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0) (y : Fin (T.S.N k)) :
    (K.binProblem C pool W).columnLoad a y =
      ∑ r : OddCellRole G C, (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y := by
  classical
  unfold GroupBinProblem.columnLoad
  simp only [CellRestrictedKernels.binProblem, ha, if_false]
  rw [Finset.sum_comm]
  simp

private theorem physical_group_count {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (g : R.Group C) :
    (Finset.univ.filter fun r : OddCellRole G C => R.groupOf C r = g).card ≤
      (PT.tiling.P (G.cellPatch C)).h := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨sg, hsg⟩ := groups.surjective g
    obtain ⟨s₀, g₀⟩ := sg
    let V := Finset.univ.filter fun r : OddCellRole G C => R.groupOf C r = g
    let f := fun r : OddCellRole G C => (R.cellWords C).symm ⟨r.1, r.2.1⟩
    have hf : Function.Injective f := by
      intro r r' h
      have heq := (R.cellWords C).symm.injective h
      apply Subtype.ext
      exact congrArg (fun v : {v : Pos T k // G.cellOf v = C} => v.1) heq
    have hsub : V.image f ⊆ ({s₀} : Finset (R.Slice C)) ×ˢ groupFiber g₀ := by
      intro sz hsz
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hsz
      have hv : (R.cellWords C (f r)).1 = r.1 :=
        congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨r.1, r.2.1⟩)
      have hz : ¬ IsEvenRole (f r).2 := by
        intro he
        exact r.2.2 (by rw [← hv]; exact (R.word_parity hc C _ _).mpr he)
      have hrEq : R.groupOf C r = groups ((f r).1, S.groupOf (f r).2) := by
        have h := hGroup (f r).1 (f r).2 (by rw [hv]; exact r.2.2)
        simpa only [hv] using h
      have hgEq : groups ((f r).1, S.groupOf (f r).2) = groups (s₀, g₀) := by
        rw [← hrEq, hsg]
        exact (Finset.mem_filter.mp hr).2
      have hp := groups.injective hgEq
      have hs := congrArg Prod.fst hp
      have hg := congrArg Prod.snd hp
      change S.groupOf (f r).2 = g₀ at hg
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_singleton.mpr hs, ?_⟩
      rw [← hg]
      exact S.groupOf_spec (f r).2 hz
    calc
      V.card = (V.image f).card := (Finset.card_image_of_injective _ hf).symm
      _ ≤ (({s₀} : Finset (R.Slice C)) ×ˢ groupFiber g₀).card := Finset.card_le_card hsub
      _ = (groupFiber g₀).card := by simp
      _ ≤ (PT.tiling.P (G.cellPatch C)).h := by
        change (Finset.univ.image (flipPos g₀.1)).card ≤ _
        exact Finset.card_image_le.trans (by simp)
  · exact (hDirect hc).elim

private theorem positive_pool_bin_raw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0)
    (hm : ∀ g, (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C))
    (hb : (K.qtilde C pool W g).w b ≠ 0) : 0 < (R.qraw C W g).w b := by
  have hin : (R.qin C W g).w b ≠ 0 := by
    intro hz
    apply hb
    rw [K.qtilde_eq C pool W g b hW (hm g), K.qbar_eq C W g b hW]
    simp [hz]
  have hraw : (R.qraw C W g).w b ≠ 0 := by
    intro hz
    apply hin
    rw [R.qin_eq C W g b (supported_history R C W hW)]
    simp [hz]
  exact lt_of_le_of_ne ((R.qraw C W g).nonneg b) (Ne.symm hraw)

private theorem physical_U_atom_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C))
    (hq : 0 < (R.qraw C W g).w b) (y : Fin (T.S.N k)) :
    (R.U C W g b).w y ≤
      2 * Real.exp (1.5 * (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (G.cellPatch C)).h) / (PT.tiling.P (G.cellPatch C)).d := by
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨sg, hsg⟩ := groups.surjective g
    obtain ⟨s, g'⟩ := sg
    rw [← hsg, hQ] at hq
    rw [← hsg, hU]
    exact S.U_atom_cap g' (records s (W s)) b y hq
  · exact (hDirect hc).elim

private theorem physical_role_degree {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (r : OddCellRole G C) :
    (Finset.univ.filter fun v : EvenCellRole G C => r ∈ K.participants C v).card ≤
      (PT.tiling.P (G.cellPatch C)).h := by
  classical
  let V := Finset.univ.filter fun v : EvenCellRole G C => r ∈ K.participants C v
  have hsub : V.image Subtype.val ⊆
      (PT.tiling.Icoord (G.cellPatch C)).image (flipPos r.1) := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, heq⟩ := (Finset.mem_filter.mp ((Finset.mem_filter.mp hv).2)).2
    refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
    rw [heq, Lane_sol_s16_prod1.flip_twice]
  have haxes : (PT.tiling.Icoord (G.cellPatch C)).card = (PT.tiling.P (G.cellPatch C)).h := by
    rw [← R.axes_eq C, Finset.card_image_of_injective _ (R.axis_injective C)]
    simp
  calc
    V.card = (V.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((PT.tiling.Icoord (G.cellPatch C)).image (flipPos r.1)).card := Finset.card_le_card hsub
    _ ≤ (PT.tiling.Icoord (G.cellPatch C)).card := Finset.card_image_le
    _ = _ := haxes

private theorem cell_raw_prior_local {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (C : G.Cell) (W : R.Hist C) (v : EvenCellRole G C)
    (ys ys' : OddCellRole G C → Fin (T.S.N k))
    (hys : ∀ r ∈ K.participants C v, ys r = ys' r) :
    R.rawPrior C W ys v.1 = R.rawPrior C W ys' v.1 := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · have hCluster : PT.tiling.mode.isCluster := by simp [hMode, Mode.isCluster]
    obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let sz := (R.cellWords C).symm ⟨v.1, v.2.1⟩
    have hv : (R.cellWords C (sz.1, sz.2)).1 = v.1 :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v.1, v.2.1⟩)
    have he : IsEvenRole sz.2 := (R.word_parity hCluster C sz.1 sz.2).mp (by rw [hv]; exact v.2.2)
    let w : EvenRole PT.tiling (G.cellPatch C) := ⟨sz.2, he⟩
    obtain ⟨fallback, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty (G.cellPatch C)).2
    rw [← hv, hPrior W sz.1 w ys fallback, hPrior W sz.1 w ys' fallback]
    congr 1
    funext j
    have hodd : ¬ IsEvenRole (R.cellWords C (sz.1, flipPos w.1 j)).1 := by
      rw [R.word_parity hCluster]
      rw [Lane_sol_s16_prod1.flip_parity]
      exact not_not.mpr he
    let r : OddCellRole G C :=
      ⟨(R.cellWords C (sz.1, flipPos w.1 j)).1,
        (R.cellWords C (sz.1, flipPos w.1 j)).2, hodd⟩
    have hr : r ∈ K.participants C v := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, R.axis C j, ?_, ?_⟩
      · rw [← R.axes_eq C]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · change (R.cellWords C (sz.1, flipPos w.1 j)).1 = flipPos v.1 (R.axis C j)
        rw [R.word_flip, hv]
    simpa only [nbrLabels, CellRawData.wordLabel, dif_pos hodd] using hys r hr
  · obtain ⟨hInj, hVal, hPass, hQ, hTrim, hU, h, hPrior⟩ := hSource C
    rw [hPrior W ys v.1 v.2.1 v.2.2, hPrior W ys' v.1 v.2.1 v.2.2]

private theorem physical_U_atom_lower {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C))
    (hq : 0 < (R.qraw C W g).w b) (y : Fin (T.S.N k))
    (hy : (R.U C W g b).w y ≠ 0) :
    1 / (b.1.card : ℝ) ≤ (R.U C W g b).w y := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨sg, hsg⟩ := groups.surjective g
    obtain ⟨s, g'⟩ := sg
    rw [← hsg, hQ] at hq
    obtain ⟨support, hs, hu⟩ := hUniform hc _ S hS g' (records s (W s)) b hq
    have hweight : ∀ z, (R.U C W g b).w z = (FinLaw.uniform support hs).w z := by
      intro z
      rw [← hsg, hU, hu]
    have hcardpos : (0 : ℝ) < support.card := by exact_mod_cast Finset.card_pos.mpr hs
    have hsub : support ⊆ b.1 := by
      intro z hz
      apply R.U_support C W g b z
      rw [hweight]
      change (if z ∈ support then 1 / (support.card : ℝ) else 0) ≠ 0
      rw [if_pos hz]
      exact ne_of_gt (div_pos (by norm_num) hcardpos)
    have hyS : y ∈ support := by
      by_contra hn
      rw [hweight] at hy
      change (if y ∈ support then 1 / (support.card : ℝ) else 0) ≠ 0 at hy
      simp [hn] at hy
    rw [hweight]
    change 1 / (b.1.card : ℝ) ≤ (if y ∈ support then 1 / (support.card : ℝ) else 0)
    rw [if_pos hyS]
    have hcardle : (support.card : ℝ) ≤ b.1.card := by exact_mod_cast Finset.card_le_card hsub
    exact div_le_div_of_nonneg_left (by norm_num) hcardpos hcardle
  · exact (hDirect hc).elim

private theorem role_pinned_failure_bound {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hd : 0 < P.d)
    (hAtoms : ∀ r y, (P.target r).w y ≠ 0 → 1 / (P.d : ℝ) ≤ (P.target r).w y)
    (v : Star) (r : Role) (y : Label) :
    P.pinnedStarFailure v r y ≤ P.d * P.independentStarFailure v := by
  classical
  have hm := Lane_sol_s16_prod1.pi_coordinate_pr P.target r y
  change P.productLaw.pr (fun x => x r = y) = (P.target r).w y at hm
  unfold RoleLabelProblem.pinnedStarFailure
  rw [hm]
  by_cases hy : (P.target r).w y = 0
  · rw [hy, div_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Lane_sol_s16_prod1.pr_range _ _).1
  · have hp : 0 < (P.target r).w y := lt_of_le_of_ne ((P.target r).nonneg y) (Ne.symm hy)
    have hdreal : (0 : ℝ) < P.d := by exact_mod_cast hd
    have hlarge : 1 ≤ (P.d : ℝ) * (P.target r).w y := by
      have h := (div_le_iff₀ hdreal).mp (hAtoms r y hy)
      nlinarith
    have hn := Lane_sol_s16_prod1.pr_mono P.productLaw
      (fun x => x r = y ∧ P.starBad v x) (P.starBad v) (fun x hx => hx.2)
    have hF : 0 ≤ P.independentStarFailure v := (Lane_sol_s16_prod1.pr_range _ _).1
    apply (div_le_iff₀ hp).mpr
    have hmul := mul_le_mul_of_nonneg_right hlarge hF
    change P.productLaw.pr (fun x => x r = y ∧ P.starBad v x) ≤ P.independentStarFailure v at hn
    nlinarith

set_option maxHeartbeats 400000 in
private theorem physical_group_contribution_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hCalibration : CellCalibrationScale PT)
    (hCluster : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0)
    (hm : ∀ g, (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0) :
    ∀ g b y, (K.binProblem C pool W).contribution g b y ≤
      Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) (-0.5) := by
  classical
  have hRoom := hCalibration.room hCluster (G.cellPatch C)
  have hTwo : 2 ≤ (PT.tiling.P (G.cellPatch C)).d := le_trans (by norm_num) hRoom.2.1
  intro g b y
  by_cases hb : (K.qtilde C pool W g).w b = 0
  · simp only [CellRestrictedKernels.binProblem, hb, if_true]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · let d : ℝ := (PT.tiling.P (G.cellPatch C)).d
    let h : ℝ := (PT.tiling.P (G.cellPatch C)).h
    let e : ℝ := Real.exp (1.5 * (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
      sliceT κ (PT.tiling.P (G.cellPatch C)).h)
    let V := Finset.univ.filter fun r : OddCellRole G C => R.groupOf C r = g
    have hd : 1 ≤ d := by
      dsimp only [d]
      exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hTwo
    have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hc : (V.card : ℝ) ≤ h := by
      dsimp only [V, h]
      exact_mod_cast physical_group_count R hR hCluster C g
    have hU : (R.U C W g b).w y ≤ 2 * e / d := physical_U_atom_cap R hR hCluster C W g b
      (positive_pool_bin_raw K C pool W hW
        hm g b hb) y
    have hh : h ≤ Real.rpow d 0.025 := by
      have hh := hRoom.2.2.2.2.1
      dsimp only [h, d] at *
      norm_num only [Nat.cast_add, Nat.cast_one] at hh
      linarith
    have he : 2 * e ≤ Real.rpow d 0.05 := by
      have he := hRoom.2.2.1
      change 4 * e ≤ Real.rpow d 0.05 at he
      have hep : 0 < e := Real.exp_pos _
      linarith
    calc
      (K.binProblem C pool W).contribution g b y = (V.card : ℝ) * (R.U C W g b).w y := by
        simp only [CellRestrictedKernels.binProblem, hb, if_false]
        rw [← Finset.sum_filter]
        simp [V]
      _ ≤ h * (2 * e / d) := mul_le_mul hc hU ((R.U C W g b).nonneg y) (Nat.cast_nonneg _)
      _ ≤ Real.rpow d 0.025 * (Real.rpow d 0.05 / d) :=
        mul_le_mul hh (div_le_div_of_nonneg_right he hdpos.le)
          (div_nonneg (by positivity) hdpos.le) (Real.rpow_nonneg hdpos.le _)
      _ = Real.rpow d (-0.925) := by
        rw [← mul_div_assoc]
        have hprod : Real.rpow d 0.025 * Real.rpow d 0.05 = Real.rpow d 0.075 := by
          have hp : Real.rpow d (0.025 + 0.05) = Real.rpow d 0.025 * Real.rpow d 0.05 := by
            simpa only [Real.rpow_eq_pow] using Real.rpow_add hdpos (0.025 : ℝ) (0.05 : ℝ)
          rw [show (0.025 + 0.05 : ℝ) = 0.075 by norm_num] at hp
          exact hp.symm
        rw [hprod]
        have hp : Real.rpow d (0.075 - 1) = Real.rpow d 0.075 / d := by
          simpa only [Real.rpow_eq_pow] using Real.rpow_sub_one hdpos.ne' (0.075 : ℝ)
        rw [show (0.075 - 1 : ℝ) = -0.925 by norm_num] at hp
        exact hp.symm
      _ ≤ Real.rpow d (-0.5) := Real.rpow_le_rpow_of_exponent_le hd (by norm_num)

private theorem physical_group_star_degree {κ : CConsts}
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hCalibration : CellCalibrationScale PT)
    (hCluster : PT.tiling.mode.isCluster) (C : G.Cell) :
    ∀ g, ((Finset.univ.filter fun v : EvenCellRole G C =>
      g ∈ (K.participants C v).image (R.groupOf C)).card : ℝ) ≤
        Real.rpow ((PT.tiling.P (G.cellPatch C)).d : ℝ) 0.01 := by
  classical
  intro g
  let V := Finset.univ.filter fun r : OddCellRole G C => R.groupOf C r = g
  let stars := fun r : OddCellRole G C =>
    Finset.univ.filter fun v : EvenCellRole G C => r ∈ K.participants C v
  have hset : (Finset.univ.filter fun v => g ∈ (K.participants C v).image (R.groupOf C)) =
      V.biUnion stars := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, hrg⟩
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrg⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    · rintro ⟨r, hrV, hrv⟩
      exact ⟨r, (Finset.mem_filter.mp hrv).2, (Finset.mem_filter.mp hrV).2⟩
  have hcount : (V.biUnion stars).card ≤ (PT.tiling.P (G.cellPatch C)).h ^ 2 := by
    calc
      (V.biUnion stars).card ≤ ∑ r ∈ V, (stars r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ V, (PT.tiling.P (G.cellPatch C)).h :=
        Finset.sum_le_sum fun r _ => physical_role_degree K C r
      _ = V.card * (PT.tiling.P (G.cellPatch C)).h := by simp
      _ ≤ (PT.tiling.P (G.cellPatch C)).h ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul_right _ (physical_group_count R hR hCluster C g)
  rw [hset]
  have hcount' : ((V.biUnion stars).card : ℝ) ≤
      ((PT.tiling.P (G.cellPatch C)).h : ℝ) ^ 2 := by exact_mod_cast hcount
  have hh := (hCalibration.room hCluster (G.cellPatch C)).2.2.2.1
  nlinarith [sq_nonneg ((PT.tiling.P (G.cellPatch C)).h : ℝ)]

private theorem group_atom_estimate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C),
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (R.history C).w W ≠ 0 →
      (∀ g, |(∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) /
          ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4)) →
      ∀ g b, (K.qtilde C pool W g).w b ≤
        Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.95) := by
  -- The n^200 slot count absorbs the q_cap inflation and d^{.95}.
  sorry

set_option maxHeartbeats 400000 in
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
  classical
  obtain ⟨n₀, hAtomCutoff⟩ := group_atom_estimate hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K C Check _ c0 D
    hR hMode hn hPerm L pool W ht hload hW
  have hCluster : PT.tiling.mode.isCluster := by simp [hMode, Mode.isCluster]
  have hRoom := hCalibration.room hCluster (H.geom.cellPatch C)
  have hlarge := hRoom.2.1
  have hTwo : 2 ≤ (PT.tiling.P (H.geom.cellPatch C)).d := by
    exact le_trans (by norm_num) hlarge
  refine {
    scale_large := hRoom.1
    d_pos := hTwo
    perturbation_range := ?_
    price_gap := ?_
    epsilon_pos := slice_epsilon_range hκ _
    failure_range := ?_
    failure_local := ?_
    contribution_range := ?_
    atom_small := ?_
    column_slack := ?_
    star_mean_small := ?_
    pinned_star_mean_small := ?_
    star_size_small := ?_
    star_degree_small := ?_
    certificates := ?_ }
  · exact (Lane_sol_s16_prod1.calibration_power_bounds _ hlarge).1
  · exact Lane_sol_s16_prod1.calibration_price_gap _
      (le_trans (by norm_num) hlarge) 0.1 (by norm_num)
  · intro v a
    simp only [CellRestrictedKernels.binProblem, CellRestrictedKernels.failure, hCluster, ↓reduceIte]
    exact Lane_sol_s16_prod1.pr_range _ _
  · intro v a a' haa
    obtain ⟨y, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2
    letI : Nonempty (Fin (T.S.N k)) := ⟨y⟩
    change K.failure C W v a = K.failure C W v a'
    simp only [CellRestrictedKernels.failure, hCluster, if_true]
    rw [Lane_sol_s16_prod1.pr_eq_indicator_E, Lane_sol_s16_prod1.pr_eq_indicator_E]
    apply Lane_sol_s16_prod1.pi_E_local _ _ (K.participants C v)
    · intro ys ys' hys
      rw [cell_raw_prior_local hκ Q K hR C W v ys ys' hys]
    · intro r hr
      change R.U C W (R.groupOf C r) (a (R.groupOf C r)) =
        R.U C W (R.groupOf C r) (a' (R.groupOf C r))
      rw [haa (R.groupOf C r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)]
  · intro g b y
    refine ⟨group_contribution_nonneg K C pool W g b y, ?_⟩
    exact physical_group_contribution_cap hκ K hR hCalibration hCluster C pool W hW
      (typical_pool_mass_ne_zero hκ Q K C D L pool ht W hW) g b y
  · apply hAtomCutoff Q H R Perm K C pool W hR hn hPerm hW
    intro g
    have h := (D.checks_cover pool ht.2).1 (L.groupProbe g) W
    rw [L.normalizer_eq pool W g hW] at h
    simpa only [Fintype.card_fin] using h
  · intro y
    rw [nominal_load_eq K C pool W y]
    have h := hload (L.Column.symm y)
    rw [L.load_eq, L.threshold_eq, L.Column.apply_symm_apply] at h
    exact h.trans (thetaStar_slack hκ)
  · intro v
    have h := (D.checks_cover pool ht.2).2.1 (L.starProbe v) W
    rw [L.failure_eq pool W v hW, L.epsilon_eq] at h
    exact h
  · intro v g b
    have h := (D.checks_cover pool ht.2).2.2 (L.pinProbe v g b) W
    rw [L.pinned_failure_eq pool W v g b hW, L.epsilon_eq] at h
    exact h
  · intro v
    have hcard : ((K.binProblem C pool W).participants v).card ≤
        (PT.tiling.P (H.geom.cellPatch C)).h :=
      Finset.card_image_le.trans (physical_participants_count K C v)
    have hh : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
        Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) 0.01 := by
      have h := hRoom.2.2.2.1
      have hnat : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
          2 * ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ^ 2 := by
        have hi : (PT.tiling.P (H.geom.cellPatch C)).h = 0 ∨
            1 ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by omega
        rcases hi with hi | hi
        · simp [hi]
        · have hi' : (1 : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by exact_mod_cast hi
          nlinarith
      exact hnat.trans h
    exact le_trans (by exact_mod_cast hcard) hh
  · exact physical_group_star_degree K hR hCalibration hCluster C
  · -- Star/repeated-bin events and capacity-subset certificates, with
    -- reciprocal avoidance factors for every supported singleton pin.
    sorry

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

private theorem qtilde_supported {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0)
    (hm : ∀ g, (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C))
    (hb : (K.qtilde C pool W g).w b ≠ 0) : b ∈ Finset.univ.image pool := by
  rw [K.qtilde_eq C pool W g b hW (hm g)] at hb
  by_contra hnot
  simp [hnot] at hb

private theorem direct_bin_size {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hDirect : ¬ PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) : (PT.tiling.P i).d = 1 := by
  have hMode : PT.tiling.mode = .bounded ∨ PT.tiling.mode = .lowDirect := by
    have hLow := Q.mode_low
    cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
  rcases hMode with hMode | hMode
  · exact (Q.profiled_valid.tiling_valid.bounded_data hMode).2 i |>.2.2.1
  · exact (Q.profiled_valid.tiling_valid.direct_data (Or.inl hMode) i).2.2.2.2.2.1

private theorem direct_height {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hDirect : ¬ PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) : (PT.tiling.P i).h = 0 := by
  have hMode : PT.tiling.mode = .bounded ∨ PT.tiling.mode = .lowDirect := by
    have hLow := Q.mode_low
    cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
  rcases hMode with hMode | hMode
  · exact (Q.profiled_valid.tiling_valid.bounded_data hMode).2 i |>.2.1
  · exact (Q.profiled_valid.tiling_valid.direct_data (Or.inl hMode) i).2.2.2.2.1

private noncomputable def mixed_role_law {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C) (r : OddCellRole G C) :
    FinLaw (Fin (T.S.N k)) where
  w := fun y => ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
  nonneg := fun y => Finset.sum_nonneg fun b _ =>
    mul_nonneg ((K.qtilde C pool W _).nonneg b) ((R.U C W _ b).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinLaw.sum_one, mul_one]
    exact (K.qtilde C pool W _).sum_one

private theorem physical_role_problem_exists {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) (hpool : Function.Injective pool)
    (hW : (R.history C).w W ≠ 0)
    (hm : ∀ g, (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0) :
    Nonempty (CellRoleProblem K C pool W a) := by
  classical
  let tests := fun (v : EvenCellRole G C) (ys : OddCellRole G C → Fin (T.S.N k)) =>
    PT.tiling.mode.isCluster ∧ R.rawPrior C W ys v.1 = 0
  have hlocal : ∀ v ys ys', (∀ r ∈ K.participants C v, ys r = ys' r) →
      (tests v ys ↔ tests v ys') := by
    intro v ys ys' hys
    dsimp only [tests]
    rw [cell_raw_prior_local hκ Q K hR C W v ys ys' hys]
  by_cases hCluster : PT.tiling.mode.isCluster
  · let P : RoleLabelProblem (OddCellRole G C) (Fin (T.S.N k)) (EvenCellRole G C)
        (Bin PT.tiling (G.cellPatch C)) := {
      regime := .cluster
      d := (PT.tiling.P (G.cellPatch C)).d
      h := (PT.tiling.P (G.cellPatch C)).h
      target := fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
      blockOf := fun r => a (R.groupOf C r)
      blockLabels := fun b => b.1
      block_card := fun b => Q.profiled_valid.tiling_valid.bins_card _ b.1 b.2
      blocks_disjoint := physical_bins_disjoint _
      target_support := fun r y hy => R.U_support C W _ _ y hy
      participants := K.participants C
      starBad := tests
      star_local := hlocal }
    refine ⟨{
      Block := Bin PT.tiling (G.cellPatch C)
      problem := P
      regime_eq := by simp [P, hCluster]
      scale_eq := by simp [P, hCluster]
      height_eq := rfl
      targets_eq := by intro r y; simp [P, hCluster]
      participants_eq := fun _ => rfl
      tests_eq := fun _ _ => Iff.rfl
      cluster_blocks := fun _ => ⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩
      direct_block := fun hn => (hn hCluster).elim }⟩
  · let labels := (Finset.univ.image pool).biUnion (fun b => b.1)
    have hcard : labels.card = G.nslot C := by
      rw [Finset.card_biUnion]
      · change (∑ b ∈ Finset.univ.image pool, b.1.card) = G.nslot C
        have hb : ∀ b : Bin PT.tiling (G.cellPatch C), b.1.card = 1 := by
          intro b
          rw [Q.profiled_valid.tiling_valid.bins_card _ b.1 b.2, direct_bin_size hκ Q hCluster]
        simp only [hb, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_image_of_injective _ hpool]
        simp
      · intro b _ b' _ hne
        exact physical_bins_disjoint _ b b' hne
    have hsupport : ∀ r y, (mixed_role_law K C pool W r).w y ≠ 0 → y ∈ labels := by
      intro r y hy
      by_contra hnot
      apply hy
      change (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) = 0
      apply Finset.sum_eq_zero
      intro b _
      by_cases hqb : (K.qtilde C pool W (R.groupOf C r)).w b = 0
      · simp [hqb]
      · have hb := qtilde_supported K C pool W hW hm _ b hqb
        have hUy : (R.U C W (R.groupOf C r) b).w y = 0 := by
          by_contra hUy
          exact hnot (Finset.mem_biUnion.mpr ⟨b, hb, R.U_support C W _ b y hUy⟩)
        simp [hUy]
    let P : RoleLabelProblem (OddCellRole G C) (Fin (T.S.N k)) (EvenCellRole G C) Unit := {
      regime := .direct
      d := G.nslot C
      h := (PT.tiling.P (G.cellPatch C)).h
      target := mixed_role_law K C pool W
      blockOf := fun _ => ()
      blockLabels := fun _ => labels
      block_card := fun _ => hcard
      blocks_disjoint := by intro b b' hne; exact (hne (Subsingleton.elim _ _)).elim
      target_support := hsupport
      participants := K.participants C
      starBad := tests
      star_local := hlocal }
    refine ⟨{
      Block := Unit
      problem := P
      regime_eq := by simp [P, hCluster]
      scale_eq := by simp [P, hCluster]
      height_eq := rfl
      targets_eq := by intro r y; simp [P, mixed_role_law, hCluster]
      participants_eq := fun _ => rfl
      tests_eq := fun _ _ => Iff.rfl
      cluster_blocks := fun hc => (hCluster hc).elim
      direct_block := fun _ => ⟨Equiv.refl _, fun _ => rfl⟩ }⟩

private theorem role_block_count {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block)
    (hColumns : ∀ y, ∑ r, (P.target r).w y ≤ 0.2) (b : Block) :
    (Finset.univ.filter fun r => P.blockOf r = b).card ≤ P.d := by
  classical
  let V := Finset.univ.filter fun r => P.blockOf r = b
  have hmass : ∀ r ∈ V, ∑ y ∈ P.blockLabels b, (P.target r).w y = 1 := by
    intro r hr
    have hrb := (Finset.mem_filter.mp hr).2
    rw [← (P.target r).sum_one]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_contra hn
    apply hy
    rw [← hrb]
    exact P.target_support r y hn
  have hcount : (V.card : ℝ) ≤ (P.d : ℝ) := by
    calc
      (V.card : ℝ) = ∑ r ∈ V, (1 : ℝ) := by simp
      _ = ∑ r ∈ V, ∑ y ∈ P.blockLabels b, (P.target r).w y := by
        apply Finset.sum_congr rfl
        intro r hr
        exact (hmass r hr).symm
      _ = ∑ y ∈ P.blockLabels b, ∑ r ∈ V, (P.target r).w y := Finset.sum_comm
      _ ≤ ∑ y ∈ P.blockLabels b, ∑ r, (P.target r).w y := by
        apply Finset.sum_le_sum
        intro y _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun r _ _ => (P.target r).nonneg y)
      _ ≤ ∑ _y ∈ P.blockLabels b, (0.2 : ℝ) := Finset.sum_le_sum fun y _ => hColumns y
      _ = 0.2 * P.d := by simp [P.block_card]; ring
      _ ≤ P.d := by nlinarith [(Nat.cast_nonneg P.d : (0 : ℝ) ≤ P.d)]
  exact_mod_cast hcount

private theorem role_block_degree {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) (L : CellRoleProblem K C pool W a)
    (hCounts : ∀ b, (Finset.univ.filter fun r => L.problem.blockOf r = b).card ≤ L.problem.d)
    (b : L.Block) :
    (Finset.univ.filter fun v => ∃ r ∈ L.problem.participants v, L.problem.blockOf r = b).card ≤
      L.problem.d * L.problem.h := by
  classical
  let V := Finset.univ.filter fun r : OddCellRole G C => L.problem.blockOf r = b
  let stars := fun r : OddCellRole G C =>
    Finset.univ.filter fun v : EvenCellRole G C => r ∈ L.problem.participants v
  have hset : (Finset.univ.filter fun v => ∃ r ∈ L.problem.participants v, L.problem.blockOf r = b) =
      V.biUnion stars := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, V, stars]
    aesop
  rw [hset]
  calc
    (V.biUnion stars).card ≤ ∑ r ∈ V, (stars r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ V, L.problem.h := by
      apply Finset.sum_le_sum
      intro r _
      simp only [stars, L.participants_eq, L.height_eq]
      exact physical_role_degree K C r
    _ = V.card * L.problem.h := by simp
    _ ≤ L.problem.d * L.problem.h := Nat.mul_le_mul_right _ (hCounts b)

private theorem direct_pool_atom_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    {R : CellRawData G} {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : ¬ PT.tiling.mode.isCluster)
    (C : G.Cell) {Check : Type} [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
      (R.Hist C) Check (T.S.n k) c0)
    (Link : CellDiagnosticLink K C D) (pool : CellPool G C) (ht : D.typical pool)
    (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (hPerm : PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (hslots : 0 < G.nslot C) (g : R.Group C) :
    ∀ b, (K.qtilde C pool W g).w b ≤ 4 / (G.nslot C : ℝ) := by
  classical
  let B := Fintype.card (Bin PT.tiling (G.cellPatch C))
  have hB : (0 : ℝ) < B := by
    letI := hPerm.bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hL : (0 : ℝ) < G.nslot C := by exact_mod_cast hslots
  have hret := Lane_sol_s16_prod1.permission_retained_half _ _ hPerm g
  have hbar : ∀ b, (K.qbar C W g).w b ≤ 2 / (B : ℝ) := by
    intro b
    rw [K.qbar_eq C W g b hW]
    have hnum : (if b ∈ (Perm.table C).permitted g then (R.qin C W g).w b else 0) ≤
        1 / (B : ℝ) := by
      split_ifs
      · exact le_of_eq (direct_incoming_uniform R hR hc C W (supported_history R C W hW) g b)
      · positivity
    calc
      _ ≤ (1 / (B : ℝ)) / (∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b) :=
        div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ (1 / (B : ℝ)) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hret
      _ = _ := by ring
  have hnorm := (D.checks_cover pool ht.2).1 (Link.groupProbe g) W
  rw [Link.normalizer_eq pool W g hW] at hnorm
  simp only [Fintype.card_fin] at hnorm
  have hlower := Lane_sol_s16_prod1.typical_normalizer_lower (T.S.n k) Q.n_large
    (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) (G.nslot C) B hL hB hnorm
  have hm := typical_pool_mass_ne_zero hκ Q K C D Link pool ht W hW g
  simpa only [show (2 * (2 : ℝ)) = 4 by norm_num] using
    Lane_sol_s16_prod1.pool_atom_cap (K.qbar C W g) (K.qtilde C pool W g)
      (Finset.univ.image pool) (G.nslot C) B 2 hL hB (by norm_num) hbar hlower
      (fun b => K.qtilde_eq C pool W g b hW hm)

private theorem direct_role_scale_cutoff {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q),
      n₀ ≤ T.S.n k → ¬ PT.tiling.mode.isCluster → ∀ C,
      κ.d0 ≤ H.geom.nslot C ∧ 2 ≤ H.geom.nslot C ∧
        (10 ^ 100 : ℕ) ≤ H.geom.nslot C := by
  classical
  have hK : 0 < κ.Kcell := lt_of_lt_of_le
    (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
  let B : ℝ := max (κ.d0 : ℝ) (10 ^ 100)
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge (B / κ.Kcell)
  refine ⟨max 2 n₁, ?_⟩
  intro T k PT K16 Q H hn hc C
  have hnreal : (1 : ℝ) ≤ T.S.n k := by
    exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) Q.n_large
  have hpow : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ (200 : ℕ) := by
    calc
      (T.S.n k : ℝ) = (T.S.n k : ℝ) * 1 := by ring
      _ ≤ (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (199 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hnreal) (Nat.cast_nonneg _)
      _ = (T.S.n k : ℝ) ^ (200 : ℕ) := by rw [show 200 = 199 + 1 by rfl, pow_succ]; ring
  have hn₁' : (n₁ : ℝ) ≤ T.S.n k := by
    exact_mod_cast le_trans (Nat.le_max_right 2 n₁) hn
  have hBN : B ≤ κ.Kcell * (T.S.n k : ℝ) := by
    have h := (div_le_iff₀ hK).mp (hn₁.trans hn₁')
    nlinarith
  have hBpow : B ≤ κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac := by
    rw [hκ.Ac_eq]
    have h := mul_le_mul_of_nonneg_left hpow hK.le
    have hp : Real.rpow (T.S.n k : ℝ) ((200 : ℕ) : ℝ) = (T.S.n k : ℝ) ^ (200 : ℕ) := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_natCast (T.S.n k : ℝ) 200
    rw [hp]
    exact hBN.trans h
  have hslots : H.geom.nslot C = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac⌉₊ := by
    change H.data.cells.nslot C = _
    rw [H.cell_partition.slot_count C]
    change ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (H.geom.cellPatch C)).d⌉₊ = _
    rw [direct_bin_size hκ Q hc]
    norm_num
  have hceil : B ≤ (H.geom.nslot C : ℝ) := by
    rw [hslots]
    exact hBpow.trans (Nat.le_ceil _)
  constructor
  · exact_mod_cast le_trans (le_max_left (κ.d0 : ℝ) (10 ^ 100)) hceil
  · have hlarge : ((10 : ℝ) ^ (100 : ℕ)) ≤ H.geom.nslot C :=
      le_trans (le_max_right (κ.d0 : ℝ) (10 ^ 100)) hceil
    refine ⟨?_, ?_⟩
    · exact_mod_cast (le_trans (by norm_num : (2 : ℝ) ≤ 10 ^ 100) hlarge)
    · exact_mod_cast hlarge

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
  classical
  obtain ⟨n₀, hScale⟩ := direct_role_scale_cutoff hκ
  refine ⟨n₀, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K C Check _ c0 D
    hR hn hPerm Link pool W a ht hload hW hsafe hpositive
  have hm := typical_pool_mass_ne_zero hκ Q K C D Link pool ht W hW
  obtain ⟨L⟩ := physical_role_problem_exists hκ Q K hR C pool W a ht.1 hW hm
  have hDscale : κ.d0 ≤ L.problem.d ∧ 2 ≤ L.problem.d := by
    by_cases hc : PT.tiling.mode.isCluster
    · have h := hCalibration.room hc (H.geom.cellPatch C)
      rw [L.scale_eq, if_pos hc]
      exact ⟨h.1, le_trans (by norm_num) h.2.1⟩
    · rw [L.scale_eq, if_neg hc]
      have hs := hScale Q H hn hc C
      exact ⟨hs.1, hs.2.1⟩
  have hRegime : L.problem.regime = .cluster ↔ PT.tiling.mode.isCluster := by
    rw [L.regime_eq]
    by_cases hc : PT.tiling.mode.isCluster <;> simp [hc]
  have hNoTests : L.problem.regime = .direct → ∀ v ys, ¬ L.problem.starBad v ys := by
    intro hd v ys hbad
    have hc := (L.tests_eq v ys).mp hbad |>.1
    have hr := hRegime.mpr hc
    rw [hd] at hr
    cases hr
  have hClusterColumns : L.problem.regime = .cluster → ∀ y,
      ∑ r, (L.problem.target r).w y ≤ 0.2 := by
    intro hr y
    have hc := hRegime.mp hr
    have h := (hsafe hc).2.2 y
    rw [supported_column_load_eq K C pool W a (hpositive hc) y] at h
    simpa only [L.targets_eq, if_pos hc, show (1 / 5 : ℝ) = 0.2 by norm_num] using h
  have hColumns : ∀ y, ∑ r, (L.problem.target r).w y ≤ 0.4 := by
    intro y
    by_cases hc : PT.tiling.mode.isCluster
    · exact (hClusterColumns (hRegime.mpr hc) y).trans (by norm_num)
    · have h := hload (Link.Column.symm y)
      rw [Link.load_eq, Link.threshold_eq, Link.Column.apply_symm_apply] at h
      have h' : (∑ r, (L.problem.target r).w y) ≤ κ.θstar := by
        simpa only [L.targets_eq, if_neg hc] using h
      exact h'.trans ((thetaStar_slack hκ).trans (by norm_num))
  have hRobust : L.problem.regime = .cluster → ∀ r y,
      2 * (L.problem.target r).w y ≤ Real.rpow (L.problem.d : ℝ) (-0.95) := by
    intro hr r y
    have hc := hRegime.mp hr
    have hRoom := hCalibration.room hc (H.geom.cellPatch C)
    have hd : (0 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).d := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 100) hRoom.2.1
    have hcap := physical_U_atom_cap R hR hc C W (R.groupOf C r) (a (R.groupOf C r))
      (positive_pool_bin_raw K C pool W hW hm _ _ (hpositive hc _)) y
    rw [L.targets_eq, if_pos hc, L.scale_eq, if_pos hc]
    calc
      2 * (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y ≤
          4 * Real.exp (1.5 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
            sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) /
              (PT.tiling.P (H.geom.cellPatch C)).d := by
        calc
          _ ≤ 2 * (2 * Real.exp (1.5 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
              sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) /
                (PT.tiling.P (H.geom.cellPatch C)).d) := mul_le_mul_of_nonneg_left hcap (by norm_num)
          _ = _ := by ring
      _ ≤ Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) 0.05 /
          (PT.tiling.P (H.geom.cellPatch C)).d :=
        div_le_div_of_nonneg_right hRoom.2.2.1 hd.le
      _ = Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-0.95) := by
        have hp : Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (0.05 - 1) =
            Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) 0.05 /
              (PT.tiling.P (H.geom.cellPatch C)).d := by
          simpa only [Real.rpow_eq_pow] using Real.rpow_sub_one hd.ne' (0.05 : ℝ)
        rw [show (0.05 - 1 : ℝ) = -0.95 by norm_num] at hp
        exact hp.symm
  have hHyp : RoleLabelHypotheses hκ L.problem := by
    refine {
      scale_large := hDscale.1
      d_pos := hDscale.2
      h_query := ?_
      cluster_range := ?_
      price_gap := ?_
      atom_small := ?_
      column_load := hColumns
      robust_atoms := hRobust
      cluster_columns := hClusterColumns
      bin_roles := ?_
      bin_star_degree := ?_
      direct_no_tests := hNoTests
      certificates := ?_ }
    · by_cases hc : PT.tiling.mode.isCluster
      · rw [L.height_eq, L.scale_eq, if_pos hc]
        have hh := (hCalibration.room hc (H.geom.cellPatch C)).2.2.2.2.1
        have hNat : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
            ((PT.tiling.P (H.geom.cellPatch C)).h + 1 : ℝ) := by norm_num
        exact hNat.trans hh
      · rw [L.height_eq, direct_height hκ Q hc, L.scale_eq, if_neg hc]
        norm_num only [Nat.cast_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro hr
      have hc := hRegime.mp hr
      rw [L.scale_eq, if_pos hc]
      exact (Lane_sol_s16_prod1.calibration_power_bounds _
        (hCalibration.room hc (H.geom.cellPatch C)).2.1).2
    · intro hr
      have hc := hRegime.mp hr
      rw [L.scale_eq, if_pos hc]
      exact Lane_sol_s16_prod1.calibration_price_gap _
        (le_trans (by norm_num) (hCalibration.room hc (H.geom.cellPatch C)).2.1) 0.02 (by norm_num)
    · intro r y
      by_cases hc : PT.tiling.mode.isCluster
      · have h := hRobust (hRegime.mpr hc) r y
        linarith [(L.problem.target r).nonneg y]
      · have hs := hScale Q H hn hc C
        have hcap := direct_pool_atom_cap hκ Q K hR hc C D Link pool ht W hW
          (hPerm C W hW) (lt_of_lt_of_le (by norm_num) hs.2.1) (R.groupOf C r)
        have hU : ∀ b y, (R.U C W (R.groupOf C r) b).w y = if y ∈ b.1 then 1 else 0 := by
          rcases hR with ⟨hMode, _, _⟩ | ⟨_, hSource⟩
          · exact (hc (by simp [hMode, Mode.isCluster])).elim
          · obtain ⟨_, _, _, _, _, hU, _, _⟩ := hSource C
            exact hU W (R.groupOf C r)
        let S := Finset.univ.filter fun b : Bin PT.tiling (H.geom.cellPatch C) => y ∈ b.1
        have hcard : (S.card : ℝ) ≤ 1 := by
          have h := permissions_labels_disjoint Perm C y
          simp only [binsContainingLabel, Perm.labels_eq] at h
          exact_mod_cast h
        have hp : 0 ≤ 4 / (H.geom.nslot C : ℝ) := by positivity
        rw [L.targets_eq, if_neg hc, L.scale_eq, if_neg hc]
        simp_rw [hU, mul_ite, mul_one, mul_zero]
        calc
          _ ≤ ∑ b : Bin PT.tiling (H.geom.cellPatch C),
              if y ∈ b.1 then 4 / (H.geom.nslot C : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro b _
            split_ifs <;> first | exact hcap b | rfl
          _ = (S.card : ℝ) * (4 / (H.geom.nslot C : ℝ)) := by
            rw [← Finset.sum_filter]
            simp [S]
          _ ≤ 4 / (H.geom.nslot C : ℝ) := by nlinarith
          _ ≤ _ := Lane_sol_s16_prod1.four_over_atom_cap _ hs.2.2
    · intro hr b
      exact role_block_count L.problem (hClusterColumns hr) b
    · intro hr b
      exact role_block_degree K C pool W a L (role_block_count L.problem (hClusterColumns hr)) b
    · -- Whole-bin seed comparison at h+1 roles and local-lemma pin budgets.
      sorry
  have hIndependent : ∀ v, L.problem.independentStarFailure v ≤
      Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ) := by
    intro v
    by_cases hc : PT.tiling.mode.isCluster
    · have h := (hsafe hc).2.1 v
      change (K.failure C W v a) ≤ _ at h
      simp only [CellRestrictedKernels.failure, hc, ↓reduceIte] at h
      unfold RoleLabelProblem.independentStarFailure RoleLabelProblem.productLaw
      unfold CellRestrictedKernels.labelLaw at h
      unfold FinLaw.pr FinLaw.pi at *
      simpa only [L.tests_eq, L.targets_eq, hc, true_and, if_true,
        CellRestrictedKernels.binProblem] using h
    · have hpr : L.problem.independentStarFailure v = 0 := by
        unfold RoleLabelProblem.independentStarFailure FinLaw.pr
        have hn : ∀ ys, ¬ L.problem.starBad v ys := by
          intro ys hbad
          exact hc ((L.tests_eq v ys).mp hbad).1
        simp only [hn, if_false, Finset.sum_const_zero]
      rw [hpr]
      apply Real.rpow_nonneg
      exact (slice_epsilon_range hκ _).1.le
  refine ⟨L, hHyp, hIndependent, ?_⟩
  intro v r y
  by_cases hc : PT.tiling.mode.isCluster
  · have hAtoms : ∀ r y, (L.problem.target r).w y ≠ 0 →
        1 / (L.problem.d : ℝ) ≤ (L.problem.target r).w y := by
      intro r y hy
      rw [L.targets_eq, if_pos hc] at hy ⊢
      have h := physical_U_atom_lower R hR hc C W (R.groupOf C r) (a (R.groupOf C r))
        (positive_pool_bin_raw K C pool W hW hm _ _ (hpositive hc _)) y hy
      rw [Q.profiled_valid.tiling_valid.bins_card _ _ (a (R.groupOf C r)).2] at h
      rw [L.scale_eq, if_pos hc]
      exact h
    have hp := role_pinned_failure_bound L.problem
      (lt_of_lt_of_le (by norm_num) hDscale.2) hAtoms v r y
    rw [L.scale_eq, if_pos hc] at hp
    have hi := hIndependent v
    have hn : (0 : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).d := Nat.cast_nonneg _
    have he : 0 ≤ Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 8 : ℝ) :=
      Real.rpow_nonneg (slice_epsilon_range hκ _).1.le _
    nlinarith [mul_le_mul_of_nonneg_left hi hn]
  · have hn : ∀ ys, ¬ L.problem.starBad v ys := by
      intro ys hbad
      exact hc ((L.tests_eq v ys).mp hbad).1
    unfold RoleLabelProblem.pinnedStarFailure FinLaw.pr
    simp only [hn, and_false, if_false, Finset.sum_const_zero, zero_div]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (slice_epsilon_range hκ _).1.le _)

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
