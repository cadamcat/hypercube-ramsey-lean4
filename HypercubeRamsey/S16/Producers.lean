import HypercubeRamsey.S16.Comparisons
import HypercubeRamsey.S16.Producers_q_s16_prod1
import HypercubeRamsey.S16.WordOrder
import HypercubeRamsey.S16.Producers_sol_s16_prod1
import HypercubeRamsey.S16.Producers_sol_s16_group
import HypercubeRamsey.S16.Producers_q_s16_prod2

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
  /-- T16:7–13,167–177 and T17:260–267: solver words use the ordered top coordinates
  with coordinate zero flipped for odd outer parity (T14:35,95).
  Vacuous outside cluster mode. -/
  word_order : PT.tiling.mode.isCluster → ∀ C s z
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (j : Fin (PT.tiling.P (G.cellPatch C)).h),
    z j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (cellWords C (s, z)).1 l) ∧ j.val = 0
      then !((cellWords C (s, z)).1
        (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j))
      else (cellWords C (s, z)).1
        (Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j)
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
        word_order := by
          intro _ C s z hle j
          exact WordOrder.cluster_cell_words_order C
            (H.cell_partition.whole_slices C) hle (hp (H.geom.cellPatch C)) s z j
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
        word_order := by
          intro h
          exact (hCluster h).elim
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

private theorem supported_history {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
    ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
  intro s
  exact Lane_sol_s16_prod1.cond_support _ _ _ _
    (Lane_sol_s16_prod1.pi_support _ W hW s)

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

private theorem physical_bin_count {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (i : Fin PT.tiling.m) :
    (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
  have h := (PT.tiling.P i).bins.sum_card_parts
  have he : ∑ b ∈ (PT.tiling.P i).bins.parts, b.card =
      (PT.tiling.P i).bins.parts.card * (PT.tiling.P i).d := by
    calc
      _ = ∑ _b ∈ (PT.tiling.P i).bins.parts, (PT.tiling.P i).d :=
        Finset.sum_congr rfl (fun b hb => Q.profiled_valid.tiling_valid.bins_card i b hb)
      _ = _ := by simp
  rw [he, (PT.tiling.P i).cardY] at h
  have hn : Fintype.card (Bin PT.tiling i) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
    change Fintype.card {b // b ∈ (PT.tiling.P i).bins.parts} * (PT.tiling.P i).d = _
    rw [Fintype.card_of_subtype (PT.tiling.P i).bins.parts (fun _ => Iff.rfl)]
    exact h
  exact_mod_cast hn

private theorem physical_raw_prior_width {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) (hR : R.SourceValid) (C : G.Cell) (v : Pos T k)
    (hv : G.cellOf v = C) (he : IsEvenRole v)
    (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (ω : (R.baseExperiment C v).State)
    (hω : (R.baseExperiment C v).law.w ω ≠ 0)
    (hσ : (R.baseExperiment C v).prior ω ≠ 0) :
    ∃ τ : Law (T.S.N k), τ.w = (R.baseExperiment C v).prior ω ∧
      τ.SupportedIn (T.X k) ∧ τ.WidthLE (Real.log 2 + 2 * Real.log (T.S.n k : ℝ)) := by
  classical
  let i := G.cellPatch C
  have hN : (0 : ℝ) < T.S.N k := by
    obtain ⟨x, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty i).1
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le x.val) x.isLt)
  have hPatchX : (PT.tiling.P i).X ⊆ T.X k := by
    intro x hx
    exact (Finset.mem_sdiff.mp ((Q.profiled_valid.tiling_valid.patch_supports i).2.1
      ((Q.profiled_valid.tiling_valid.patch_supports i).1 hx))).1
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hc, hSource⟩
  · have hCluster : PT.tiling.mode.isCluster := by simp [hMode, Mode.isCluster]
    obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let sz := (R.cellWords C).symm ⟨v, hv⟩
    have hword : (R.cellWords C (sz.1, sz.2)).1 = v :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v, hv⟩)
    have hEven : IsEvenRole sz.2 := (R.word_parity hCluster C sz.1 sz.2).mp (by rw [hword]; exact he)
    let w : EvenRole PT.tiling i := ⟨sz.2, hEven⟩
    obtain ⟨fallback, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
    let ls := nbrLabels w.1 (R.wordLabel C ω.2.2 sz.1 fallback)
    have hrow : (R.baseExperiment C v).prior ω = S.σ w (records sz.1 (ω.1 sz.1)) ls := by
      change R.rawPrior C ω.1 ω.2.2 v = _
      rw [← hword]
      exact hPrior ω.1 sz.1 w ω.2.2 fallback
    have hσ' : S.σ w (records sz.1 (ω.1 sz.1)) ls ≠ 0 := by rw [← hrow]; exact hσ
    let τ : Law (T.S.N k) :=
      { w := S.σ w (records sz.1 (ω.1 sz.1)) ls
        nonneg := S.σ_nonneg w _ ls
        sum_eq_one := S.σ_prob w _ ls hσ' }
    have hRaw : (R.rawHistory C).w ω.1 ≠ 0 := by
      intro hz
      apply hω
      change (R.rawHistory C).w ω.1 * (R.rawLaw C ω.1).w ω.2 = 0
      rw [hz, zero_mul]
    have hSlice := Lane_sol_s16_prod1.pi_support (R.sliceLaw C) ω.1 hRaw sz.1
    rw [hLaw] at hSlice
    rw [Lane_sol_s16_prod1.map_equiv_weight] at hSlice
    obtain ⟨u, hActive, hSupp⟩ := S.σ_support w (records sz.1 (ω.1 sz.1)) ls hσ'
    have hact : u ∈ PT.activeVertices := by
      simp only [ProfiledTiling.activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      apply hActive PT.parameter
      exact lt_of_le_of_ne (S.recLaw PT.parameter |>.nonneg _) (Ne.symm hSlice)
    refine ⟨τ, hrow.symm, ?_, ?_⟩
    · intro x hx
      by_contra hn
      have hx' := (hSupp x hn).1
      exact hx (hPatchX ((Q.profiled_valid.corner_clean i u hact).sub hx'))
    · intro x
      have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have hGain : 0 ≤ PT.tiling.gain i := by simp [Tiling.gain, hMode]; positivity
      have hExp : Real.exp (-500 * PT.tiling.gain i) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hCap := S.σ_cap w (records sz.1 (ω.1 sz.1)) ls x
      have hCap' : (T.S.N k : ℝ) * τ.w x ≤ (2 : ℝ) ^ (PT.tiling.P i).h := by
        have hh := mul_le_mul_of_nonneg_left hExp
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (PT.tiling.P i).h)
        change _ ≤ _ at hCap
        nlinarith
      have hH : ((PT.tiling.P i).h : ℝ) ≤ Real.log (T.S.n k : ℝ) := by
        apply (Q.height_bound i).trans
        have hh := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1 / 10 : ℝ) ≤ 1)
        simpa only [Real.rpow_one, Real.rpow_eq_pow] using hh
      have hTwo : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hpow : (2 : ℝ) ^ (PT.tiling.P i).h ≤ Real.exp ((PT.tiling.P i).h : ℝ) := by
        calc
          _ ≤ Real.exp 1 ^ (PT.tiling.P i).h := pow_le_pow_left₀ (by norm_num) hTwo _
          _ = _ := by rw [← Real.exp_nat_mul]; simp
      apply (le_div_iff₀ hN).mpr
      have hexp : Real.exp ((PT.tiling.P i).h : ℝ) ≤
          Real.exp (Real.log 2 + 2 * Real.log (T.S.n k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      simpa only [mul_comm] using hCap'.trans (hpow.trans hexp)
  · obtain ⟨_, _, _, _, _, _, hEnv, hPrior⟩ := hSource C
    let τ := Law.unifCore (PT.envelope i) hEnv
    have hrow : (R.baseExperiment C v).prior ω = τ.w := hPrior ω.1 ω.2.2 v hv he
    have hM : (0 : ℝ) < (PT.tiling.P i).M := by
      rw [← (PT.tiling.P i).cardX]
      exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty i).1
    have hEnvCard : (PT.tiling.P i).M / 2 ≤ ((PT.envelope i).card : ℝ) := by
      have hact : PT.activeVertices.Nonempty := by
        have hh := Q.profiled_valid.direct_single_corner hc
        exact Finset.card_pos.mp (by omega)
      obtain ⟨u, hu⟩ := hact
      apply (Q.profiled_valid.corner_clean i u hu).card_lower.trans
      have hsub : PT.mesh.corner u i ⊆ PT.envelope i := by
        rw [Q.profiled_valid.envelope_eq]
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨u, hu, hx⟩
      exact_mod_cast Finset.card_le_card hsub
    refine ⟨τ, hrow.symm, ?_, ?_⟩
    · intro x hx
      have hn : x ∉ PT.envelope i := fun he => hx (hPatchX (Q.profiled_valid.envelope_subset i he))
      simp [τ, Law.unifCore, hn]
    · have hw : τ.WidthLE (Real.log ((T.S.N k : ℝ) / (PT.envelope i).card)) := by
        simpa [τ, Law.unifCore, FinProb.uniform, Law.WidthLE] using Law.uniform_width (PT.envelope i) hEnv
      apply hw.mono
      have hcard : (0 : ℝ) < (PT.envelope i).card := by exact_mod_cast Finset.card_pos.mpr hEnv
      have hratio : (T.S.N k : ℝ) / (PT.envelope i).card ≤ 2 * ((T.S.N k : ℝ) / (PT.tiling.P i).M) := by
        apply (div_le_iff₀ hcard).mpr
        have hh := mul_le_mul_of_nonneg_left hEnvCard (div_nonneg hN.le hM.le)
        have hdiv : (T.S.N k : ℝ) / (PT.tiling.P i).M * (PT.tiling.P i).M = T.S.N k := by field_simp
        nlinarith
      have hlogratio := Real.log_le_log (div_pos hN hcard) hratio
      have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)),
          sq_nonneg (Real.sqrt (Real.log (T.S.n k : ℝ)) - 1)]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (div_pos hN hM))] at hlogratio
      have hpatch := Q.patch_mass_bound i
      linarith

private theorem permission_average_estimate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R),
      R.SourceValid → n₀ ≤ T.S.n k →
      TwoBudgetDisc T k ((T.S.n k : ℝ) ^ κ.xs) (κ.α * T.S.n k) (bstar T k) →
      ∀ C inc, (∑ y, (Perm.table C).badMass inc y) ≤
        Real.exp (-3 * (Perm.table C).cperm * (Perm.table C).n) *
          Fintype.card (Fin (T.S.N k)) := by
  classical
  obtain ⟨n₁, hwidth⟩ := Lane_sol_s16_prod1.logarithmic_room κ.xs 1 (Real.log 2) 2
    hκ.xs_rng.1 (by norm_num) (by norm_num)
  have hc : 0 < κ.α - 3 * κ.cperm := by nlinarith [hκ.cperm_rng.2, hκ.α_rng.1]
  obtain ⟨n₂, haverage⟩ := Lane_sol_s16_prod1.logarithmic_room 1 (κ.α - 3 * κ.cperm)
    (Real.log 2) 0 (by norm_num) hc (by norm_num)
  refine ⟨max (max n₁ n₂) ⌈Real.exp 1⌉₊, ?_⟩
  intro T k PT K16 Q G R Perm hR hn hDisc C inc
  have hn₁ : n₁ ≤ T.S.n k := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hn₂ : n₂ ≤ T.S.n k := le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have he : Real.exp 1 ≤ (T.S.n k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (Nat.le_max_right _ _) hn)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hbudget := hwidth (T.S.n k) hn₁
  simp only [one_mul] at hbudget
  have havg : Real.log 2 ≤ (κ.α - 3 * κ.cperm) * T.S.n k := by
    have hh := haverage (T.S.n k) hn₂
    simpa only [zero_mul, add_zero, Real.rpow_one] using hh
  have hExp : 2 * Real.exp (-(κ.α * T.S.n k)) ≤ Real.exp (-3 * κ.cperm * T.S.n k) := by
    calc
      _ = Real.exp (Real.log 2 - κ.α * T.S.n k) := by rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  rw [Perm.rate_eq, Perm.n_eq, Fintype.card_fin]
  by_cases hinc : inc.2 ∉ PT.tiling.Icoord (G.cellPatch C) ∧ G.classOf inc.1.1 = none
  · obtain ⟨hj, hclass⟩ := hinc
    let A := (PT.tiling.P (G.cellPatch C)).Y
    let v := flipPos inc.1.1 inc.2
    let P := R.baseExperiment (G.cellOf v) v
    have hEven : IsEvenRole v := Lane_sol_s16_prod1.flip_parity _ _ |>.mpr inc.1.2.2
    have hAY : A ⊆ T.Y k := by
      intro y hy
      exact (Finset.mem_sdiff.mp ((Q.profiled_valid.tiling_valid.patch_supports (G.cellPatch C)).2.2.2
        ((Q.profiled_valid.tiling_valid.patch_supports (G.cellPatch C)).2.2.1 hy))).1
    have hrows : ∀ ω, P.law.w ω ≠ 0 → P.prior ω ≠ 0 →
        ∃ τ : Law (T.S.N k), τ.w = P.prior ω ∧ τ.SupportedIn (T.X k) ∧
          τ.WidthLE ((T.S.n k : ℝ) ^ κ.xs) := by
      intro ω hω hσ
      obtain ⟨τ, hw, hs, hwidth⟩ := physical_raw_prior_width hκ Q R hR (G.cellOf v) v rfl hEven hlog ω hω hσ
      exact ⟨τ, hw, hs, hwidth.mono hbudget⟩
    have h := Lane_sol_s16_prod1.prior_bad_count hDisc
      (show 0 ≤ bstar T k from Real.rpow_nonneg (Nat.cast_nonneg _) _) PT.tiling.c P A
      (Q.profiled_valid.tiling_valid.patch_nonempty (G.cellPatch C)).2 hAY hrows
    have heq : (∑ y, (Perm.table C).badMass inc y) =
        ∑ y ∈ A, P.expect (fun σ => if σ ≠ 0 ∧
          2 * bstar T k < |(∑ x, σ x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| then 1 else 0) := by
      simp_rw [Perm.bad_eq]
      simp only [hj, hclass, not_false_eq_true, and_true]
      change (∑ y, if y ∈ A then _ else 0) = _
      exact Finset.sum_ite_mem_eq _ _
    rw [heq]
    exact h.trans (mul_le_mul_of_nonneg_right hExp (Nat.cast_nonneg _))
  · have hz : ∀ y, (Perm.table C).badMass inc y = 0 := by
      intro y
      rw [Perm.bad_eq]
      have hh : ¬ (y ∈ (PT.tiling.P (G.cellPatch C)).Y ∧
          inc.2 ∉ PT.tiling.Icoord (G.cellPatch C) ∧ G.classOf inc.1.1 = none) :=
        fun h => hinc h.2
      rw [if_neg hh]
    simp only [hz, Finset.sum_const_zero]
    positivity

private theorem permission_incidence_count {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) (Perm : CellPermissions R) (hR : R.SourceValid)
    (C : G.Cell) (g : R.Group C) :
    (permissionIncidences (Perm.table C) g).card ≤ (T.S.n k) ^ 2 := by
  classical
  let V := Finset.univ.filter fun r : OddCellRole G C => R.groupOf C r = g
  have hcount : V.card ≤ max 1 (PT.tiling.P (G.cellPatch C)).h := by
    by_cases hc : PT.tiling.mode.isCluster
    · exact (physical_group_count R hR hc C g).trans (Nat.le_max_right _ _)
    · apply le_trans _ (Nat.le_max_left 1 _)
      apply Finset.card_le_one.mpr
      intro r hr r' hr'
      have hInjective : Function.Injective (R.groupOf C) := by
        rcases hR with ⟨hMode, _, _⟩ | ⟨_, hSource⟩
        · exact (hc (by simp [hMode, Mode.isCluster])).elim
        · exact (hSource C).1
      apply hInjective
      rw [(Finset.mem_filter.mp hr).2, (Finset.mem_filter.mp hr').2]
  have hH : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (R.axis C) (R.axis_injective C)
  have hMax : max 1 (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k :=
    max_le (le_trans (by norm_num) Q.n_large) hH
  have heq : permissionIncidences (Perm.table C) g = V ×ˢ Finset.univ := by
    ext inc
    simp [permissionIncidences, Perm.group_eq, V]
  rw [heq, Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_fin]
  simpa only [pow_two] using Nat.mul_le_mul_right (T.S.n k) (hcount.trans hMax)

private theorem physical_incoming_bound {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) (hR : R.SourceValid) (C : G.Cell) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b ≤
      8 * Real.exp (2 * (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (G.cellPatch C)).h) /
        Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
  classical
  have hB : (0 : ℝ) < Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
    have hne : Nonempty (Bin PT.tiling (G.cellPatch C)) := by
      by_contra hn
      letI : IsEmpty (Bin PT.tiling (G.cellPatch C)) := not_nonempty_iff.mp hn
      have hh := (R.qin C W g).sum_one
      simp at hh
    letI := hne
    exact_mod_cast Fintype.card_pos
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨⟨ss, g'⟩, hsg⟩ := groups.surjective g
    have hg : S.AllGood (records ss (W ss)) := (hPass ss (W ss)).mp (supported_history R C W hW ss).1
    have hqin : (R.qin C W g).w b = S.qin (records ss (W ss)) g' b := by
      rw [← hsg, R.qin_eq C W _ b (supported_history R C W hW), hTrim]
      simp_rw [hQ]
      unfold SliceSolver.qin
      split_ifs <;> simp
    rw [hqin]
    have hc := Lane_sol_s16_prod1.solver_qin_cap S (records ss (W ss)) hg g' b
      (Lane_sol_s16_prod1.low_cluster_pretrim_small hκ Q hMode (G.cellPatch C))
    have hM := physical_bin_count hκ Q (G.cellPatch C)
    have hdpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).d := by
      have hMpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).M := by
        rw [← (PT.tiling.P (G.cellPatch C)).cardY]
        exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty _).2
      nlinarith
    apply hc.trans
    rw [← hM]
    simp only [Tiling.kScale, Tiling.tScale]
    field_simp [hB.ne', hdpos.ne']
    norm_num
  · have hRaw : R.SourceValid := Or.inr ⟨hDirect, hSource⟩
    rw [direct_incoming_uniform R hRaw hDirect C W (supported_history R C W hW) g b]
    apply div_le_div_of_nonneg_right _ hB.le
    have he : 1 ≤ Real.exp (2 * (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (G.cellPatch C)).h) := Real.one_le_exp_iff.mpr (by positivity)
    linarith

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
  classical
  obtain ⟨n₁, hAverage⟩ := permission_average_estimate hκ
  obtain ⟨n₂, hCapRoom⟩ := Lane_sol_s16_prod1.logarithmic_room 1 (κ.cperm / 2)
    (Real.log 8) 2 (by norm_num) (div_pos hκ.cperm_rng.1 (by norm_num)) (by norm_num)
  obtain ⟨n₃, hRatioRoom⟩ := Lane_sol_s16_prod1.logarithmic_room 1 κ.cperm
    0 4 (by norm_num) hκ.cperm_rng.1 (by norm_num)
  refine ⟨max n₁ (max n₂ (max n₃ ⌈Real.exp 1⌉₊)), ?_⟩
  intro T k PT K16 Q H R Perm hR hn hDisc C W hW
  have hn₁ : n₁ ≤ T.S.n k := le_trans (Nat.le_max_left _ _) hn
  have hn₂ : n₂ ≤ T.S.n k := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hn₃ : n₃ ≤ T.S.n k := le_trans (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)) hn
  have hnE : ⌈Real.exp 1⌉₊ ≤ T.S.n k := le_trans (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)) hn
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have he : Real.exp 1 ≤ (T.S.n k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnE)
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa only [Real.log_exp] using hh
  have hnpos : (0 : ℝ) < T.S.n k := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)),
      sq_nonneg (Real.sqrt (Real.log (T.S.n k : ℝ)) - 1)]
  have hB : (0 : ℝ) < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := by
    obtain ⟨b, hb⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty
      (Finset.nonempty_iff_ne_empty.mp (Q.profiled_valid.tiling_valid.patch_nonempty _).2)
    letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨⟨b, hb⟩⟩
    exact_mod_cast Fintype.card_pos
  refine ⟨hAverage Q R Perm hR hn₁ hDisc C, ?_, ?_⟩
  · intro g
    rw [Perm.n_eq, Perm.rate_eq, Fintype.card_fin]
    have hcount : ((permissionIncidences (Perm.table C) g).card : ℝ) ≤ (T.S.n k : ℝ) ^ (2 : ℕ) := by
      exact_mod_cast permission_incidence_count hκ Q R Perm hR C g
    have hM : (0 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).M := by
      rw [← (PT.tiling.P (H.geom.cellPatch C)).cardY]
      exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty _).2
    have hN : (0 : ℝ) < T.S.N k := by
      obtain ⟨y, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le y.val) y.isLt)
    have hBin := physical_bin_count hκ Q (H.geom.cellPatch C)
    have hd : (0 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).d := by nlinarith
    have hratio : (T.S.N k : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) =
        ((T.S.N k : ℝ) / (PT.tiling.P (H.geom.cellPatch C)).M) * (PT.tiling.P (H.geom.cellPatch C)).d := by
      rw [← hBin]
      field_simp
    have hNM : (T.S.N k : ℝ) / (PT.tiling.P (H.geom.cellPatch C)).M ≤
        Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ))) := by
      have hh := Real.exp_le_exp.mpr (Q.patch_mass_bound (H.geom.cellPatch C))
      rw [Real.exp_log (div_pos hN hM)] at hh
      exact hh
    have heq : Real.exp (2 * Real.log (T.S.n k : ℝ)) = (T.S.n k : ℝ) ^ (2 : ℕ) := by
      have hh := Real.exp_nat_mul (Real.log (T.S.n k : ℝ)) 2
      simpa only [Nat.cast_ofNat, Real.exp_log hnpos] using hh
    have hroom : 4 * Real.log (T.S.n k : ℝ) ≤ κ.cperm * T.S.n k := by
      simpa only [zero_add, Real.rpow_one] using hRatioRoom (T.S.n k) hn₃
    calc
      _ ≤ (T.S.n k : ℝ) ^ (2 : ℕ) *
          (Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ))) * Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))) := by
        apply mul_le_mul hcount _ (div_nonneg hN.le hB.le) (by positivity)
        rw [hratio]
        exact mul_le_mul hNM (Q.bin_count_bound _) hd.le (Real.exp_pos _).le
      _ = Real.exp (2 * Real.log (T.S.n k : ℝ) + 2 * Real.sqrt (Real.log (T.S.n k : ℝ))) := by
        rw [Real.exp_add, heq]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (4 * Real.log (T.S.n k : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := Real.exp_le_exp.mpr hroom
  · intro g b
    rw [Perm.n_eq, Perm.rate_eq]
    have hkt := Lane_sol_s16_prod1.slice_product_log_bound hκ
      (PT.tiling.P (H.geom.cellPatch C)).h (Real.log (T.S.n k : ℝ)) hlog (Q.height_bound _)
    have hroom : Real.log 8 + 2 * Real.log (T.S.n k : ℝ) ≤ κ.cperm * T.S.n k / 2 := by
      have hh := hCapRoom (T.S.n k) hn₂
      simp only [Real.rpow_one] at hh
      nlinarith
    apply (physical_incoming_bound hκ Q R hR C W hW g b).trans
    apply div_le_div_of_nonneg_right _ hB.le
    calc
      _ = Real.exp (Real.log 8 + 2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
          sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

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

private theorem restricted_kernels_exists {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (R : CellRawData G) (Perm : CellPermissions R)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W)) :
    ∃ K : CellRestrictedKernels R Perm, ∀ C pool W g,
      (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
      K.qtilde C pool W g = K.qbar C W g := by
  classical
  let mass := fun C W g => ∑ D ∈ (Perm.table C).permitted g, (R.qin C W g).w D
  have hmass : ∀ C W g, (R.history C).w W ≠ 0 → 0 < mass C W g := by
    intro C W g hW
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (Lane_sol_s16_prod1.permission_retained_half (Perm.table C) (R.qin C W)
        (hPerm C W hW) g)
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
    qtilde_eq := ?_ }, ?_⟩
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
  · intro C pool W g hz
    change (∑ D ∈ Finset.univ.image pool, (qbar C W g).w D) = 0 at hz
    change qtilde C pool W g = qbar C W g
    simp [qtilde, hz]

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


private theorem cell_pool_birthday_cutoff {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q),
      n₀ ≤ T.S.n k → ∀ C,
      (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ)) / 4 := by
  have hK : 0 < κ.Kcell := lt_of_lt_of_le
    (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
  obtain ⟨n₁, hn₁⟩ := Lane_sol_s16_prod1.polynomial_birthday_room κ.Kcell hK.le
  refine ⟨max n₁ (max 2 ⌈Real.exp 1⌉₊), ?_⟩
  intro T k PT K16 Q H hn C
  let i := H.geom.cellPatch C
  let L := H.geom.nslot C
  have hnp : (0 : ℝ) < T.S.n k := by exact_mod_cast lt_of_lt_of_le (by norm_num) Q.n_large
  have hnreal : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast le_trans (by norm_num) Q.n_large
  have heN : Real.exp 1 ≤ (T.S.n k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_trans
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn))
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) heN
    simpa only [Real.log_exp] using hh
  have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)),
      sq_nonneg (Real.sqrt (Real.log (T.S.n k : ℝ)) - 1)]
  have hprefix : ((PT.tiling.P i).ℓ : ℝ) ≤ Real.log (T.S.n k : ℝ) :=
    (Q.prefix_bound i).trans hsqrt
  have hℓ : (PT.tiling.P i).ℓ ≤ T.S.n k := by
    have hs := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ) (Finset.mem_univ i)
    have hb := Q.profiled_valid.tiling_valid.prefix_internal_length
    omega
  have hd : (0 : ℝ) < (PT.tiling.P i).d := by
    have hM := physical_bin_count hκ Q i
    have hMpos : (0 : ℝ) < (PT.tiling.P i).M := by
      rw [← (PT.tiling.P i).cardY]
      exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty i).2
    by_contra hh
    have hd0 : (PT.tiling.P i).d = 0 := by exact_mod_cast le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
    rw [hd0, Nat.cast_zero, mul_zero] at hM
    linarith
  have hd1 : (1 : ℝ) ≤ (PT.tiling.P i).d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    intro hh
    simp only [hh, Nat.cast_zero, lt_self_iff_false] at hd)
  have hpow : 0 < (T.S.n k : ℝ) ^ (200 : ℕ) := pow_pos hnp _
  have hEq : L = ⌈κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) / (PT.tiling.P i).d⌉₊ := by
    change H.data.cells.nslot C = _
    rw [H.cell_partition.slot_count C, hκ.Ac_eq]
    simp only [Real.rpow_eq_pow, Real.rpow_natCast, i]
    rfl
  have hSlotsPos : 0 < L := by
    rw [hEq]
    exact Nat.ceil_pos.mpr (div_pos (mul_pos hK hpow) hd)
  have hslots : (L : ℝ) ≤ (κ.Kcell + 1) * (T.S.n k : ℝ) ^ (200 : ℕ) := by
    have he := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hK.le hpow.le) hd.le)).le
    rw [← hEq] at he
    have hb : κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) / (PT.tiling.P i).d ≤
        κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) := by
      apply (div_le_iff₀ hd).mpr
      nlinarith [mul_nonneg (mul_nonneg hK.le hpow.le) (sub_nonneg.mpr hd1)]
    have hp1 := one_le_pow₀ hnreal (n := 200)
    nlinarith
  have hcapacity : (Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
      (T.S.n k : ℝ) ^ (200 : ℕ)) * L ≤ Fintype.card (Bin PT.tiling i) := by
    have hcap := H.scale.patch_capacity i
    rw [hκ.Ac_eq] at hcap
    simp only [Real.rpow_eq_pow, Real.rpow_natCast] at hcap
    rw [← hEq] at hcap
    have hx : 0 ≤ Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
        (T.S.n k : ℝ) ^ (200 : ℕ) := div_nonneg (Real.rpow_nonneg (by norm_num) _) hpow.le
    have hh := mul_le_mul_of_nonneg_right
      (show Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) / (T.S.n k : ℝ) ^ (200 : ℕ) ≤
        3 * Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) / (T.S.n k : ℝ) ^ (200 : ℕ) +
          Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5) from by
        calc
          _ ≤ 3 * (Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            (T.S.n k : ℝ) ^ (200 : ℕ)) := by nlinarith only [hx]
          _ ≤ 3 * (Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            (T.S.n k : ℝ) ^ (200 : ℕ)) + Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5) :=
              le_add_of_nonneg_right (Real.exp_pos _).le
          _ = _ := by ring)
      (Nat.cast_nonneg (α := ℝ) L)
    exact hh.trans (by simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hcap)
  exact (Lane_sol_s16_prod1.pool_birthday_from_capacity (T.S.n k) (PT.tiling.P i).ℓ L
    _ κ.Kcell Q.n_large hSlotsPos hK.le hℓ hprefix hslots hcapacity).trans
      (hn₁ _ (le_trans (Nat.le_max_left _ _) hn))

private theorem direct_history_subsingleton {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : ¬ PT.tiling.mode.isCluster) (C : G.Cell) :
    Subsingleton (R.Hist C) := by
  rcases hR with ⟨hMode, _, _⟩ | ⟨_, hSource⟩
  · exact (hc (by simp [hMode, Mode.isCluster])).elim
  · refine ⟨fun W W' => funext fun s => ?_⟩
    obtain ⟨e⟩ := (hSource C).2.1 s
    exact e.injective (Subsingleton.elim _ _)

private theorem law_atom_le_one {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (ω : Ω) :
    P.w ω ≤ 1 := by
  calc
    P.w ω ≤ ∑ x, P.w x := Finset.single_le_sum (fun x _ => P.nonneg x) (Finset.mem_univ ω)
    _ = 1 := P.sum_one

private theorem physical_load_range {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (pool : CellPool G C) (W : R.Hist C) (y : Fin (T.S.N k)) :
    0 ≤ (∑ r : OddCellRole G C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) ∧
    (∑ r : OddCellRole G C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) ≤
      Fintype.card (OddCellRole G C) := by
  constructor
  · exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg ((K.qtilde C pool W (R.groupOf C r)).nonneg b)
        ((R.U C W (R.groupOf C r) b).nonneg y)
  · calc
      _ ≤ ∑ r : OddCellRole G C, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        calc
          _ ≤ ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b := by
            apply Finset.sum_le_sum
            intro b _
            exact mul_le_of_le_one_right ((K.qtilde C pool W (R.groupOf C r)).nonneg b)
              (law_atom_le_one _ y)
          _ = 1 := (K.qtilde C pool W (R.groupOf C r)).sum_one
      _ = _ := by simp

private theorem direct_cell_bin_size {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hc : ¬ PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) : (PT.tiling.P i).d = 1 := by
  have hmodes : PT.tiling.mode = .bounded ∨ PT.tiling.mode = .lowDirect := by
    cases hm : PT.tiling.mode with
    | bounded => exact Or.inl rfl
    | lowDirect => exact Or.inr rfl
    | highDirect => exact (show False by simpa [hm, Mode.isLow] using Q.mode_low).elim
    | lowCluster => exact (hc (by simp [hm, Mode.isCluster])).elim
    | highSmall => exact (hc (by simp [hm, Mode.isCluster])).elim
    | highLarge => exact (hc (by simp [hm, Mode.isCluster])).elim
  rcases hmodes with hm | hm
  · exact (Q.profiled_valid.tiling_valid.bounded_data hm).2 i |>.2.2.1
  · exact (Q.profiled_valid.tiling_valid.direct_data (Or.inl hm) i).2.2.2.2.2.1

set_option maxHeartbeats 400000 in
private theorem direct_cell_load_gate {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : ¬ PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) {Check : Type} [Fintype Check]
    (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
      (R.Hist C) Check (T.S.n k) (1 / 2)) (Link : CellDiagnosticLink K C D) :
    Nonempty (LoadGateHypotheses D) := by
  classical
  letI := direct_history_subsingleton R hR hc C
  refine Lane_sol_s16_prod1.deterministic_history_load_gate D Q.n_large (by norm_num)
    (by rw [Link.threshold_eq]; exact hκ.bucket.2.2.2.2)
    (Fintype.card (OddCellRole H.geom C)) (Nat.cast_nonneg _) ?_ ?_
  · intro pool W y
    rw [Link.load_eq]
    exact physical_load_range K C pool W (Link.Column y)
  · intro pool hp W y
    have hW : (R.history C).w W ≠ 0 := by
      have huniv : (Finset.univ : Finset (R.Hist C)) = {W} := by
        ext W'
        simp [Subsingleton.elim W' W]
      have hw := (R.history C).sum_one
      rw [huniv, Finset.sum_singleton] at hw
      rw [hw]
      norm_num
    let B := Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
    let L := H.geom.nslot C
    have hB : (0 : ℝ) < B := by
      letI := D.bins_nonempty
      exact_mod_cast Fintype.card_pos
    have hK : 0 < κ.Kcell := lt_of_lt_of_le
      (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
    have hn : (0 : ℝ) < T.S.n k := by exact_mod_cast lt_of_lt_of_le (by norm_num) Q.n_large
    have hd := direct_cell_bin_size hκ Q hc (H.geom.cellPatch C)
    have hslots : κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) ≤ (L : ℝ) := by
      have heq := H.cell_partition.slot_count C
      change L = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
        (PT.tiling.P (H.geom.cellPatch C)).d⌉₊ at heq
      rw [hκ.Ac_eq, hd] at heq
      simp only [Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_one, div_one] at heq
      exact (Nat.le_ceil _).trans_eq (by exact_mod_cast heq.symm)
    have hL : (0 : ℝ) < L := lt_of_lt_of_le (mul_pos hK (pow_pos hn _)) hslots
    have hqcap : ∀ g b, (K.qtilde C pool W g).w b ≤ 4 / (L : ℝ) := by
      intro g
      have hmass := Lane_sol_s16_prod1.permission_retained_half (Perm.table C) (R.qin C W)
        (hPerm C W hW) g
      have hbar : ∀ b, (K.qbar C W g).w b ≤ 2 / (B : ℝ) := by
        intro b
        rw [K.qbar_eq C W g b hW]
        have hmpos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hmass
        have hunif := direct_incoming_uniform R hR hc C W (supported_history R C W hW) g b
        by_cases hb : b ∈ (Perm.table C).permitted g
        · rw [if_pos hb, hunif]
          calc
            _ ≤ (1 / (B : ℝ)) / (1 / 2 : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hmass
            _ = _ := by ring
        · rw [if_neg hb, zero_div]
          positivity
      have hnorm := (D.checks_cover pool hp.2).1 (Link.groupProbe g) W
      rw [Link.normalizer_eq pool W g hW, Fintype.card_fin] at hnorm
      have hlower := Lane_sol_s16_prod1.typical_normalizer_lower (T.S.n k) Q.n_large
        _ L B hL hB hnorm
      have hm : (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (by positivity) hlower)
      simpa only [show (2 * (2 : ℝ)) = 4 by norm_num] using Lane_sol_s16_prod1.pool_atom_cap
        (K.qbar C W g) (K.qtilde C pool W g) (Finset.univ.image pool)
        L B 2 hL hB (by norm_num) hbar hlower (fun b => K.qtilde_eq C pool W g b hW hm)
    have hroles : (Fintype.card (OddCellRole H.geom C) : ℝ) ≤ (T.S.n k : ℝ) ^ (200 : ℕ) := by
      let positions : Finset (Pos T k) := Finset.univ.filter fun v => H.geom.cellOf v = C
      let f : OddCellRole H.geom C → {v // v ∈ positions} :=
        fun r => ⟨r.1, by simpa only [positions, Finset.mem_filter, Finset.mem_univ, true_and] using r.2.1⟩
      have hf : Function.Injective f := by
        intro r r' hh
        apply Subtype.ext
        have hv := congrArg Subtype.val hh
        change r.1 = r'.1 at hv
        exact hv
      have hcard := Fintype.card_le_of_injective f hf
      have hsize := H.cell_partition.cell_size C
      change positions.card ≤ ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ at hsize
      have hncard : Fintype.card (OddCellRole H.geom C) ≤ ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ :=
        hcard.trans (by simpa only [Fintype.card_coe] using hsize)
      have hr := (show (Fintype.card (OddCellRole H.geom C) : ℝ) ≤ ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ by exact_mod_cast hncard).trans
        (Nat.floor_le (Real.rpow_nonneg hn.le _))
      simpa only [hκ.Ac_eq, Real.rpow_eq_pow, Real.rpow_natCast] using hr
    rw [Link.load_eq, Link.threshold_eq]
    calc
      _ ≤ (Fintype.card (OddCellRole H.geom C) : ℝ) * (4 / (L : ℝ)) := by
        calc
          _ ≤ ∑ _r : OddCellRole H.geom C, (4 / (L : ℝ)) := by
            apply Finset.sum_le_sum
            intro r _
            have hsupport : ∑ b, (R.U C W (R.groupOf C r) b).w (Link.Column y) ≤ 1 := by
              calc
                _ ≤ ∑ b : Bin PT.tiling (H.geom.cellPatch C), if Link.Column y ∈ b.1 then (1 : ℝ) else 0 := by
                  apply Finset.sum_le_sum
                  intro b _
                  by_cases hy : Link.Column y ∈ b.1
                  · simp only [if_pos hy]
                    exact law_atom_le_one _ _
                  · have hz : (R.U C W (R.groupOf C r) b).w (Link.Column y) = 0 := by
                      by_contra hz
                      exact hy (R.U_support C W (R.groupOf C r) b (Link.Column y) hz)
                    simp [hz, hy]
                _ = ((binsContainingLabel (Perm.table C) (Link.Column y)).card : ℝ) := by
                  simp [binsContainingLabel, Perm.labels_eq, Finset.sum_boole]
                _ ≤ 1 := by exact_mod_cast permissions_labels_disjoint Perm C (Link.Column y)
            calc
              _ ≤ ∑ b, (4 / (L : ℝ)) * (R.U C W (R.groupOf C r) b).w (Link.Column y) :=
                Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right
                  (hqcap _ b) ((R.U C W (R.groupOf C r) b).nonneg _)
              _ ≤ 4 / (L : ℝ) := by
                rw [← Finset.mul_sum]
                exact mul_le_of_le_one_right (by positivity) hsupport
          _ = _ := by simp
      _ ≤ (T.S.n k : ℝ) ^ (200 : ℕ) * (4 / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hroles (by positivity)
      _ ≤ 4 / κ.Kcell := by
        apply (le_div_iff₀ hK).mpr
        have hmul := mul_le_mul_of_nonneg_left hslots (show (0 : ℝ) ≤ 4 by norm_num)
        rw [← mul_div_assoc, div_mul_eq_mul_div]
        apply (div_le_iff₀ hL).mpr
        nlinarith only [hmul]
      _ ≤ κ.θstar / 2 := by
        have hh := (div_le_iff₀ hκ.bucket.2.2.2.2).mp hκ.Kcell_big
        apply (div_le_iff₀ hK).mpr
        nlinarith

set_option maxHeartbeats 400000 in
private theorem direct_diagnostics_with_budgets {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : ¬ PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W)) (C : H.geom.Cell)
    (hslots : 0 < H.geom.nslot C)
    (hbias : 2 * (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) +
      3 / (H.geom.nslot C : ℝ) ≤ Real.rpow (T.S.n k : ℝ) (-4) / 2)
    (hvariance : Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) +
      Real.log (8 * ((2 ^ T.S.n k + 1 : ℕ) : ℝ)) ≤
        (H.geom.nslot C : ℝ) * Real.rpow (T.S.n k : ℝ) (-4) ^ 2 / 8)
    (hcollision : (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ)) / 4) :
    ∃ Check : Type, ∃ _ : Fintype Check,
      ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
        (R.Hist C) Check (T.S.n k) (1 / 2),
        Nonempty (CellDiagnosticLink K C D) ∧
        Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
  classical
  letI := direct_history_subsingleton R hR hc C
  have hHist : Nonempty (R.Hist C) := by
    by_contra hh
    letI : IsEmpty (R.Hist C) := not_nonempty_iff.mp hh
    have hs := (R.history C).sum_one
    simp at hs
  let W0 : R.Hist C := Classical.choice hHist
  have hW0 : (R.history C).w W0 ≠ 0 := by
    have huniv : (Finset.univ : Finset (R.Hist C)) = {W0} := by
      ext W
      simp [Subsingleton.elim W W0]
    have hs := (R.history C).sum_one
    rw [huniv, Finset.sum_singleton] at hs
    rw [hs]
    norm_num
  have hBins : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := by
    obtain ⟨b, hb⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty
      (Finset.nonempty_iff_ne_empty.mp (Q.profiled_valid.tiling_valid.patch_nonempty _).2)
    exact ⟨⟨b, hb⟩⟩
  letI := hBins
  let B : ℝ := Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
  let L : ℝ := H.geom.nslot C
  let ρ : ℝ := Real.rpow (T.S.n k : ℝ) (-4)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Fintype.card_pos
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hslots
  have hρ : 0 < ρ := Real.rpow_pos_of_pos
    (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large) _
  let uniform : FinLaw (Bin PT.tiling (H.geom.cellPatch C)) := FinLaw.uniform Finset.univ Finset.univ_nonempty
  let Check := Option (OddCellRole H.geom C)
  let row : Check → FinLaw (Bin PT.tiling (H.geom.cellPatch C)) :=
    fun r => match r with | none => uniform | some r => K.qbar C W0 (R.groupOf C r)
  let probe : R.Group C → Check := fun g =>
    if h : ∃ r, R.groupOf C r = g then some (Classical.choose h) else none
  have hrow : ∀ g b, (row (probe g)).w b = (K.qbar C W0 g).w b := by
    intro g b
    dsimp only [probe]
    split_ifs with hg
    · dsimp only [row]
      rw [Classical.choose_spec hg]
    · have hp : (Perm.table C).permitted g = Finset.univ := by
        ext b'
        simp only [Finset.mem_univ, iff_true, (Perm.table C).permitted_iff]
        intro inc hi
        rw [Perm.group_eq] at hi
        exact (hg ⟨inc.1, hi⟩).elim
      dsimp only [row]
      rw [K.qbar_eq C W0 g b hW0, hp]
      simp only [Finset.mem_univ, if_true, FinLaw.sum_one, div_one]
      simp only [uniform, FinLaw.uniform, Finset.mem_univ, if_true, Finset.card_univ]
      exact (direct_incoming_uniform R hR hc C W0 (supported_history R C W0 hW0) g b).symm
  have hcap : ∀ c b, (row c).w b ≤ 2 / B := by
    intro c b
    cases c with
    | none =>
      simp only [row, uniform, FinLaw.uniform, Finset.mem_univ, if_true, Finset.card_univ]
      exact div_le_div_of_nonneg_right (by norm_num) hB.le
    | some r =>
      dsimp only [row]
      rw [K.qbar_eq C W0 _ b hW0]
      have hm := Lane_sol_s16_prod1.permission_retained_half _ _ (hPerm C W0 hW0) (R.groupOf C r)
      have hnum : (if b ∈ (Perm.table C).permitted (R.groupOf C r) then (R.qin C W0 (R.groupOf C r)).w b else 0) ≤ 1 / B := by
        split_ifs
        · exact (direct_incoming_uniform R hR hc C W0 (supported_history R C W0 hW0) _ b).le
        · positivity
      calc
        _ ≤ (1 / B) / (∑ b ∈ (Perm.table C).permitted (R.groupOf C r), (R.qin C W0 (R.groupOf C r)).w b) :=
          div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ (1 / B) / (1 / 2 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hm
        _ = _ := by ring
  let D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
      (R.Hist C) Check (T.S.n k) (1 / 2) := {
    bins_nonempty := hBins
    ε := sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h
    iidSlotLaw := fun _ => uniform
    uniform_slots := fun _ b => by simp [uniform, FinLaw.uniform, B]
    normalizer := fun pool c => ∑ b ∈ Finset.univ.image pool, (row c).w b
    center := fun _ => L / B
    tolerance := fun _ => (L / B) * ρ
    Group := Check ⊕ Unit
    poolNormalizer := fun pool g _ => match g with
      | Sum.inl c => ∑ b ∈ Finset.univ.image pool, (row c).w b
      | Sum.inr _ => L / B
    internalFailure := fun _ _ _ => 0
    pinnedInternalFailure := fun _ _ _ => 0
    checks_cover := by
      intro pool hp
      refine ⟨?_, fun _ _ => Real.rpow_nonneg (Real.exp_pos _).le _, fun _ _ => Real.rpow_nonneg (Real.exp_pos _).le _⟩
      intro g W
      cases g with
      | inl c =>
        have heq : |(∑ b ∈ Finset.univ.image pool, (row c).w b) / (L / B) - 1| =
            |(∑ b ∈ Finset.univ.image pool, (row c).w b) - L / B| / (L / B) := by
          have hh : (∑ b ∈ Finset.univ.image pool, (row c).w b) / (L / B) - 1 =
              ((∑ b ∈ Finset.univ.image pool, (row c).w b) - L / B) / (L / B) := by
            field_simp [hL.ne', hB.ne']
          rw [hh, abs_div, abs_of_pos (div_pos hL hB)]
        simp only [Fintype.card_fin]
        rw [heq]
        apply (div_le_iff₀ (div_pos hL hB)).mpr
        simpa only [mul_comm] using hp c
      | inr u =>
        simp only [Fintype.card_fin]
        change |(L / B) / (L / B) - 1| ≤ ρ
        rw [div_self (div_pos hL hB).ne', sub_self, abs_zero]
        exact hρ.le
    LoadColumn := Fin (T.S.N k)
    historyLaw := fun _ => R.history C
    loadValue := fun pool W y => ∑ r : OddCellRole H.geom C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
    loadThreshold := κ.θstar }
  let Link : CellDiagnosticLink K C D := {
    groupProbe := fun g => Sum.inl (probe g)
    starProbe := fun _ => Sum.inr ()
    pinProbe := fun _ _ _ => Sum.inr ()
    epsilon_eq := rfl
    normalizer_eq := by
      intro pool W g _
      have hW : W = W0 := Subsingleton.elim _ _
      subst W
      change (∑ b ∈ Finset.univ.image pool, (row (probe g)).w b) = _
      exact Finset.sum_congr rfl (fun b _ => hrow g b)
    failure_eq := by
      intro pool W v _
      simp [D, GroupBinProblem.independentFailure, FinLaw.E, CellRestrictedKernels.binProblem,
        CellRestrictedKernels.failure, hc]
    pinned_failure_eq := by
      intro pool W v g b _
      simp [D, GroupBinProblem.pinnedFailure, FinLaw.E, CellRestrictedKernels.binProblem,
        CellRestrictedKernels.failure, hc]
    history_eq := fun _ => rfl
    Column := Equiv.refl _
    load_eq := fun _ _ _ => rfl
    threshold_eq := rfl }
  have hcard : (Fintype.card Check : ℝ) ≤ ((2 ^ T.S.n k + 1 : ℕ) : ℝ) := by
    have hh := Fintype.card_le_of_injective (fun r : OddCellRole H.geom C => r.1) Subtype.val_injective
    have hpos : Fintype.card (Pos T k) = 2 ^ T.S.n k := by simp [Pos, CubePos]
    have hbound : Fintype.card Check ≤ 2 ^ T.S.n k + 1 := by
      simpa only [Check, Fintype.card_option] using Nat.add_le_add_right (hh.trans_eq hpos) 1
    exact_mod_cast hbound
  have hConc : Nonempty (PoolConcentrationHypotheses D) := by
    apply Lane_sol_s16_prod1.image_diagnostic_concentration D row (2 / B) ((L / B) * ρ)
      (by positivity) (by positivity) Q.n_large (by norm_num) (by simpa using hslots)
      ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by
        have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
        have hh : 0 ≤ 0.001 * κ.a * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
            (PT.tiling.P (H.geom.cellPatch C)).h := by positivity
        nlinarith only [hh])⟩ hcap (fun _ _ => rfl) (fun _ => by simp [D, L, B]) (fun _ => rfl)
    · simp only [Fintype.card_fin]
      have heq : L * (2 / B) * (L ^ 2 / B) + (2 / B + 1 / B) =
          (L / B) * (2 * L ^ 2 / B + 3 / L) := by field_simp [hL.ne', hB.ne']; ring
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left hbias (div_pos hL hB).le
      simpa only [L, B, ρ, mul_div_assoc] using hh
    · simp only [Fintype.card_fin]
      have heq : 2 * (((L / B) * ρ) / 2) ^ 2 / (L * (2 / B) ^ 2) = L * ρ ^ 2 / 8 := by field_simp [hL.ne', hB.ne']; ring
      rw [heq]
      have hmax : max 1 (Fintype.card Check : ℝ) ≤ ((2 ^ T.S.n k + 1 : ℕ) : ℝ) :=
        max_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)) hcard
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 8 * max 1 (Fintype.card Check : ℝ))
        (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 8))
      have hh := (add_le_add (le_refl (Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ))) hlog).trans hvariance
      simpa only [L, ρ, Real.rpow_eq_pow] using hh
    · simpa only [Fintype.card_fin, Real.rpow_eq_pow] using hcollision
  exact ⟨Check, inferInstance, D, ⟨Link⟩, hConc, direct_cell_load_gate hκ Q H R Perm K hR hc hPerm C D Link⟩


private theorem history_support_iff {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (W : R.Hist C) :
    (R.history C).w W ≠ 0 ↔
      ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
  classical
  constructor
  · intro hW s
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW s)
  · intro hW
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    simp only [FinLaw.cond, if_pos (hW s).1]
    exact div_ne_zero (hW s).2 (R.slice_pos C s).ne'

private theorem cluster_supported_value_count {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (s : R.Slice C) :
    (Fintype.card {z : R.Value C s // z ∈ R.slicePass C s ∧
      (R.sliceLaw C s).w z ≠ 0} : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let A := {z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0}
    let B := {W : (∀ r, S.Val r) // 0 < (S.recLaw PT.parameter).w W}
    let f : A → B := fun z => ⟨records s z.1, by
      have hw := congrArg (fun law : FinLaw (R.Value C s) => law.w z.1) (hLaw s)
      simp only [Lane_sol_s16_prod1.map_equiv_weight, Equiv.symm_symm] at hw
      have hn : (S.recLaw PT.parameter).w (records s z.1) ≠ 0 := by
        intro hz
        exact z.2.2 (hw.trans hz)
      exact lt_of_le_of_ne ((S.recLaw PT.parameter).nonneg _) (Ne.symm hn)⟩
    have hinj : Function.Injective f := by
      intro z z' h
      apply Subtype.ext
      exact (records s).injective (congrArg Subtype.val h)
    have hcount : (Fintype.card A : ℝ) ≤ Fintype.card B := by
      exact_mod_cast Fintype.card_le_of_injective f hinj
    apply hcount.trans
    have hcard : Fintype.card B =
        (Finset.univ.filter fun W : ∀ r, S.Val r => 0 < (S.recLaw PT.parameter).w W).card :=
      Fintype.card_subtype (fun W : ∀ r, S.Val r => 0 < (S.recLaw PT.parameter).w W)
    rw [hcard]
    exact S.low_support hMode PT.parameter
  · exact (hDirect hc).elim

private theorem cluster_qin_row_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
    (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (hQ : ∀ W s g b, (R.qraw C W (groups (s, g))).w b = S.q g (records s (W s)) b)
    (hTrim : ∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (s : R.Slice C) (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C))
    (heq : W s = W' s) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W (groups (s, g))).w b = (R.qin C W' (groups (s, g))).w b := by
  rw [R.qin_eq C W _ b ((history_support_iff R C W).mp hW),
    R.qin_eq C W' _ b ((history_support_iff R C W').mp hW')]
  simp_rw [hTrim, hQ, heq]

private theorem cluster_qbar_row_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
    (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (hQ : ∀ W s g b, (R.qraw C W (groups (s, g))).w b = S.q g (records s (W s)) b)
    (hTrim : ∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (s : R.Slice C) (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C))
    (heq : W s = W' s) (b : Bin PT.tiling (G.cellPatch C)) :
    (K.qbar C W (groups (s, g))).w b = (K.qbar C W' (groups (s, g))).w b := by
  rw [K.qbar_eq C W _ b hW, K.qbar_eq C W' _ b hW']
  simp_rw [cluster_qin_row_local R C S records groups hQ hTrim W W' hW hW' s g heq]

private theorem cluster_normalizer_rows {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) :
    ∃ Check : Type, ∃ _ : Fintype Check,
      ∃ row : Check → FinLaw (Bin PT.tiling (G.cellPatch C)),
        (Fintype.card Check : ℝ) ≤ (Fintype.card (R.Slice C) : ℝ) *
          (2 : ℝ) ^ (PT.tiling.P (G.cellPatch C)).h *
          Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) ∧
        (∀ c, ∃ W g, (R.history C).w W ≠ 0 ∧ row c = K.qbar C W g) ∧
        ∀ W, (R.history C).w W ≠ 0 → ∀ g, ∃ c,
          row c = K.qbar C W g := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · have hR' : R.SourceValid := Or.inl ⟨hMode, hUniform, hSource⟩
    obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    have hSupported : ∃ W : R.Hist C, (R.history C).w W ≠ 0 := by
      by_contra h
      have hz : ∀ W, (R.history C).w W = 0 := by simpa using h
      have hone := (R.history C).sum_one
      simp only [hz, Finset.sum_const_zero] at hone
      norm_num at hone
    obtain ⟨W0, hW0⟩ := hSupported
    let Value := fun s : R.Slice C =>
      {z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0}
    let Check := (s : R.Slice C) × (Value s × HypercubeRamsey.Group PT.tiling (G.cellPatch C))
    let extend := fun (s : R.Slice C) (z : Value s) => Function.update W0 s z.1
    have hExtend : ∀ s z, (R.history C).w (extend s z) ≠ 0 := by
      intro s z
      apply (history_support_iff R C _).mpr
      intro t
      by_cases ht : t = s
      · subst t
        simpa only [extend, Function.update_self] using z.2
      · simpa only [extend, Function.update_of_ne ht] using
          (history_support_iff R C W0).mp hW0 t
    let row := fun c : Check => K.qbar C (extend c.1 c.2.1) (groups (c.1, c.2.2))
    refine ⟨Check, inferInstance, row, ?_, ?_, ?_⟩
    · have hgroups : (Fintype.card (HypercubeRamsey.Group PT.tiling (G.cellPatch C)) : ℝ) ≤
          (2 : ℝ) ^ (PT.tiling.P (G.cellPatch C)).h := by
        have hh := Fintype.card_le_of_injective
          (fun g : HypercubeRamsey.Group PT.tiling (G.cellPatch C) => g.1) Subtype.val_injective
        have heq : Fintype.card (IWord PT.tiling (G.cellPatch C)) =
            2 ^ (PT.tiling.P (G.cellPatch C)).h := by simp [IWord, CubePos]
        exact_mod_cast hh.trans_eq heq
      have hvalue : ∀ s, (Fintype.card (Value s) : ℝ) ≤
          Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) :=
        fun s => cluster_supported_value_count R hR' hc C s
      simp only [Check, Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul]
      calc
        _ ≤ ∑ s : R.Slice C, Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) *
            (2 : ℝ) ^ (PT.tiling.P (G.cellPatch C)).h := by
          apply Finset.sum_le_sum
          intro s _
          exact mul_le_mul (hvalue s) hgroups (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = _ := by simp; ring
    · intro c
      exact ⟨extend c.1 c.2.1, groups (c.1, c.2.2), hExtend _ _, rfl⟩
    · intro W hW g
      obtain ⟨⟨s, g'⟩, hsg⟩ := groups.surjective g
      let z : Value s := ⟨W s, (history_support_iff R C W).mp hW s⟩
      refine ⟨⟨s, z, g'⟩, ?_⟩
      have hlocal : ∀ b, (K.qbar C (extend s z) (groups (s, g'))).w b =
          (K.qbar C W (groups (s, g'))).w b := by
        intro b
        apply cluster_qbar_row_local R Perm K C S records groups hQ hTrim _ W
          (hExtend s z) hW s g' _ b
        simp [extend, z]
      change K.qbar C (extend s z) (groups (s, g')) = K.qbar C W g
      rw [← hsg]
      cases heq1 : K.qbar C (extend s z) (groups (s, g'))
      cases heq2 : K.qbar C W (groups (s, g'))
      congr 1
      exact funext (fun b => by simpa only [heq1, heq2] using hlocal b)
  · exact (hDirect hc).elim

private theorem permission_qbar_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (hPerm : PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ g b, (R.qin C W g).w b ≤ M)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (K.qbar C W g).w b ≤ 2 * M := by
  have hm := Lane_sol_s16_prod1.permission_retained_half (Perm.table C) (R.qin C W) hPerm g
  have hmass : 0 < ∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b := by linarith
  rw [K.qbar_eq C W g b hW]
  have hnum : (if b ∈ (Perm.table C).permitted g then (R.qin C W g).w b else 0) ≤ M := by
    split_ifs
    · exact hcap g b
    · exact hM
  calc
    _ ≤ M / (∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b) :=
      div_le_div_of_nonneg_right hnum hmass.le
    _ ≤ M / (1 / 2 : ℝ) := div_le_div_of_nonneg_left hM (by norm_num) hm
    _ = _ := by ring

/-- Repetition can collapse a pool to one bin. At a positive bin the
restriction is then exactly its in-bin law, without any slot suppression. -/
private theorem constant_pool_load {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (hslots : 0 < G.nslot C) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) (b : Bin PT.tiling (G.cellPatch C))
    (hb : ∀ g, (K.qbar C W g).w b ≠ 0) (y : Fin (T.S.N k)) :
    (∑ r : OddCellRole G C, ∑ D,
      (K.qtilde C (fun _ => b) W (R.groupOf C r)).w D *
        (R.U C W (R.groupOf C r) D).w y) =
      ∑ r : OddCellRole G C, (R.U C W (R.groupOf C r) b).w y := by
  classical
  have himage : Finset.univ.image (fun _ : Fin (G.nslot C) => b) = {b} := by
    ext D
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨s, rfl⟩
      rfl
    · intro h
      subst D
      exact ⟨⟨0, hslots⟩, rfl⟩
  have hmass : ∀ g, (∑ D ∈ Finset.univ.image (fun _ : Fin (G.nslot C) => b),
      (K.qbar C W g).w D) ≠ 0 := by
    intro g
    simpa only [himage, Finset.sum_singleton] using hb g
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [K.qtilde_eq C (fun _ => b) W (R.groupOf C r) _ hW (hmass _)]
  simp only [himage, Finset.mem_singleton, Finset.sum_singleton]
  rw [Finset.sum_eq_single b]
  · simp [hb]
  · intro D _ hDb
    simp [hDb]
  · simp

private theorem cluster_normalizer_rows_bounded {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 →
      PermissionLossHypotheses (Perm.table C) (R.qin C W)) (C : H.geom.Cell) :
    ∃ Check : Type, ∃ _ : Fintype Check,
      ∃ row : Check → FinLaw (Bin PT.tiling (H.geom.cellPatch C)),
        (Fintype.card Check : ℝ) ≤ (T.S.n k : ℝ) ^ (200 : ℕ) *
          Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) ∧
        (∀ c b, (row c).w b ≤
          16 * Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
            sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) /
            Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ∧
        ∀ W, (R.history C).w W ≠ 0 → ∀ g, ∃ c, row c = K.qbar C W g := by
  classical
  obtain ⟨Check, inst, row, hcount, hrows, hcover⟩ := cluster_normalizer_rows R Perm K hR hc C
  letI := inst
  refine ⟨Check, inst, row, ?_, ?_, hcover⟩
  · have heq := Fintype.card_congr (R.cellWords C)
    rw [Fintype.card_prod] at heq
    have hi : Fintype.card (IWord PT.tiling (H.geom.cellPatch C)) =
        2 ^ (PT.tiling.P (H.geom.cellPatch C)).h := by simp [IWord, CubePos]
    rw [hi] at heq
    have hsub : Fintype.card {v : Pos T k // H.geom.cellOf v = C} =
        (H.data.cells.positions C).card :=
      Fintype.card_subtype (fun v : Pos T k => H.geom.cellOf v = C)
    rw [hsub] at heq
    have heq' : (Fintype.card (R.Slice C) : ℝ) *
        (2 : ℝ) ^ (PT.tiling.P (H.geom.cellPatch C)).h = (H.data.cells.positions C).card := by
      exact_mod_cast heq
    have hcell := H.cell_partition.cell_size C
    have hcell' : ((H.data.cells.positions C).card : ℝ) ≤
        (⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊ : ℝ) := by exact_mod_cast hcell
    have hceller : ((H.data.cells.positions C).card : ℝ) ≤
        Real.rpow (T.S.n k : ℝ) κ.Ac :=
      hcell'.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    rw [hκ.Ac_eq] at hceller
    simp only [Real.rpow_eq_pow, Real.rpow_natCast] at hceller
    exact hcount.trans (mul_le_mul_of_nonneg_right (heq'.le.trans hceller) (Real.exp_pos _).le)
  · intro c b
    obtain ⟨W, g, hW, hrow⟩ := hrows c
    rw [hrow]
    have hcap := permission_qbar_cap R Perm K C W hW (hPerm C W hW)
      (8 * Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) /
          Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) (by positivity)
      (physical_incoming_bound hκ Q R hR C W hW) g b
    convert hcap using 1 <;> ring

private theorem low_cluster_height_pos {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hc : PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) : 1 ≤ (PT.tiling.P i).h := by
  have hMode : PT.tiling.mode = .lowCluster := by
    have hLow := Q.mode_low
    cases hm : PT.tiling.mode <;> simp_all [Mode.isCluster, Mode.isLow]
  have hdy := (Q.profiled_valid.tiling_valid.cluster_data (Or.inl hMode) i).2.2.2.2.2.2.1
  have hp : 0 < (PT.tiling.P i).h := by rw [hdy]; positivity
  omega

private theorem physical_slot_polynomial_lower {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (hnE : ⌈Real.exp 1⌉₊ ≤ T.S.n k) (C : H.geom.Cell) :
    (T.S.n k : ℝ) ^ (199 : ℕ) ≤ H.geom.nslot C := by
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have he : Real.exp 1 ≤ (T.S.n k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnE)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hnpos : (0 : ℝ) < T.S.n k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)),
      sq_nonneg (Real.sqrt (Real.log (T.S.n k : ℝ)) - 1)]
  have hdle : ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) ≤ T.S.n k := by
    calc
      _ ≤ Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ))) := Q.bin_count_bound _
      _ ≤ Real.exp (Real.log (T.S.n k : ℝ)) := Real.exp_le_exp.mpr hsqrt
      _ = _ := Real.exp_log hnpos
  have hM : (0 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).M := by
    rw [← (PT.tiling.P (H.geom.cellPatch C)).cardY]
    exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty _).2
  have hBin := physical_bin_count hκ Q (H.geom.cellPatch C)
  have hd : (0 : ℝ) < (PT.tiling.P (H.geom.cellPatch C)).d := by nlinarith
  have htheta : κ.θstar ≤ 1 := by
    have hb := hκ.bucket
    rw [hκ.clock.2.1] at hb
    have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hb.1
    nlinarith [mul_le_mul_of_nonneg_right hKp hb.2.2.2.2.le]
  have hK : 0 < κ.Kcell := lt_of_lt_of_le
    (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
  have hK1 : 1 ≤ κ.Kcell := by
    have hh := (div_le_iff₀ hκ.bucket.2.2.2.2).mp hκ.Kcell_big
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr htheta)]
  have hslot : κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) /
      (PT.tiling.P (H.geom.cellPatch C)).d ≤ H.geom.nslot C := by
    have heq := H.cell_partition.slot_count C
    change H.geom.nslot C = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (H.geom.cellPatch C)).d⌉₊ at heq
    rw [hκ.Ac_eq] at heq
    simp only [Real.rpow_eq_pow, Real.rpow_natCast] at heq
    rw [heq]
    exact Nat.le_ceil _
  apply le_trans _ hslot
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (T.S.n k : ℝ) ^ (199 : ℕ) * T.S.n k :=
      mul_le_mul_of_nonneg_left hdle (pow_nonneg hnpos.le _)
    _ = (T.S.n k : ℝ) ^ (200 : ℕ) := by rw [← pow_succ]
    _ ≤ κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) :=
      le_mul_of_one_le_left (pow_nonneg hnpos.le _) hK1

private theorem physical_global_load_variance_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (C : G.Cell)
    {Check : Type} [Fintype Check] {c0 : ℝ}
    (D : CellPoolDiagnostics (Fin (G.nslot C)) (Bin PT.tiling (G.cellPatch C))
      (R.Hist C) Check (T.S.n k) c0) (Link : CellDiagnosticLink K C D)
    (Gate : LoadGateHypotheses D) (pool : CellPool G C) (y : Fin (T.S.N k)) :
    let F := fun W => ∑ r : OddCellRole G C, ∑ b,
      (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y
    ((T.S.n k : ℝ) ^ c0 + Real.log (max 1 (T.S.N k : ℝ))) *
      (R.history C).E (fun W => (F W - (R.history C).E F) ^ 2) ≤
      2 * (κ.θstar / 2) ^ 2 := by
  classical
  have hh := Lane_sol_s16_prod1.load_gate_global_variance_bound D Gate pool (Link.Column.symm y)
  have hcard : Fintype.card D.LoadColumn = T.S.N k := by
    simpa only [Fintype.card_fin] using Fintype.card_congr Link.Column
  rw [hcard, Link.threshold_eq, Link.history_eq pool] at hh
  simp_rw [Link.load_eq, Equiv.apply_symm_apply] at hh
  exact hh

private theorem cluster_normalizer_setup {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C, (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ)) / 4) →
      ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
        ∃ row : Check → FinLaw (Bin PT.tiling (H.geom.cellPatch C)),
          (Fintype.card Check : ℝ) ≤ (T.S.n k : ℝ) ^ (200 : ℕ) *
            Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) ∧
          (∀ c b, (row c).w b ≤ (T.S.n k : ℝ) /
            Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ∧
          (∀ W, (R.history C).w W ≠ 0 → ∀ g, ∃ c, row c = K.qbar C W g) ∧
          let L : ℝ := H.geom.nslot C
          let B : ℝ := Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
          0 < L ∧ Real.rpow (T.S.n k : ℝ) (-1) ≤ sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h ∧
          (L * ((T.S.n k : ℝ) / B) * (L ^ 2 / B) + ((T.S.n k : ℝ) / B + 1 / B) ≤
            (L / B) * Real.rpow (T.S.n k : ℝ) (-4) / 2) ∧
          (Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
            2 * (((L / B) * Real.rpow (T.S.n k : ℝ) (-4)) / 2) ^ 2 /
              (L * ((T.S.n k : ℝ) / B) ^ 2)) := by
  classical
  obtain ⟨nAmplitude, hAmplitude⟩ := Lane_sol_s16_prod1.cluster_slice_amplitude_room hκ
  obtain ⟨nNormalizer, hNormalizerRoom⟩ := Lane_sol_s16_prod1.cluster_normalizer_budget_room
  refine ⟨max (max nAmplitude nNormalizer) ⌈Real.exp 1⌉₊, ?_⟩
  intro T k PT K16 Q H R Perm K hR hc hn hPerm hBirthday C
  have hnAmplitude := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnNormalizer := le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnExp := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨NormalizerCheck, instNormalizer, row, hrowCount, hrowCap, hrowCover⟩ :=
    cluster_normalizer_rows_bounded hκ Q H R Perm K hR hc hPerm C
  letI := instNormalizer
  have hAmplitudeCell := hAmplitude (T.S.n k) (PT.tiling.P (H.geom.cellPatch C)).h
    hnAmplitude Q.n_large (Q.height_bound (H.geom.cellPatch C))
  have hSlotLower := physical_slot_polynomial_lower hκ Q H hnExp C
  have hHeight := low_cluster_height_pos hκ Q hc (H.geom.cellPatch C)
  have hExp1 : 1 ≤ Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
      sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hRowAmplitude : 16 * Real.exp
      (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) ≤ T.S.n k := by
    apply le_trans _ hAmplitudeCell.1
    exact le_self_pow₀ (by linarith only [hExp1]) (Nat.one_le_iff_ne_zero.mp hHeight)
  let L : ℝ := H.geom.nslot C
  let B : ℝ := Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
  have hB : 0 < B := by
    obtain ⟨b, hb⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty
      (Finset.nonempty_iff_ne_empty.mp (Q.profiled_valid.tiling_valid.patch_nonempty _).2)
    letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨⟨b, hb⟩⟩
    dsimp only [B]
    exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < T.S.n k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hL : 0 < L := lt_of_lt_of_le (pow_pos hnpos _) hSlotLower
  have hRowPoly : ∀ c b, (row c).w b ≤ (T.S.n k : ℝ) / B := by
    intro c b
    exact (hrowCap c b).trans (div_le_div_of_nonneg_right hRowAmplitude hB.le)
  obtain ⟨hNormalizerBias, hNormalizerVariance⟩ := hNormalizerRoom (T.S.n k) L B
    (Fintype.card NormalizerCheck) hnNormalizer Q.n_large hB hSlotLower
    (hBirthday C) hrowCount
  have hImageBias : L * ((T.S.n k : ℝ) / B) * (L ^ 2 / B) +
      ((T.S.n k : ℝ) / B + 1 / B) ≤ (L / B) * Real.rpow (T.S.n k : ℝ) (-4) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hNormalizerBias (div_pos hL hB).le
    convert hh using 1 <;> field_simp [hL.ne', hB.ne'] <;> ring
  have hImageVariance : Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) +
      Real.log (8 * max 1 (Fintype.card NormalizerCheck : ℝ)) ≤
      2 * (((L / B) * Real.rpow (T.S.n k : ℝ) (-4)) / 2) ^ 2 /
        (L * ((T.S.n k : ℝ) / B) ^ 2) := by
    have heq : 2 * (((L / B) * Real.rpow (T.S.n k : ℝ) (-4)) / 2) ^ 2 /
        (L * ((T.S.n k : ℝ) / B) ^ 2) =
        L * Real.rpow (T.S.n k : ℝ) (-4) ^ 2 / (2 * (T.S.n k : ℝ) ^ (2 : ℕ)) := by
      field_simp [hL.ne', hB.ne', hnpos.ne'] <;> ring
    rw [heq]
    apply hNormalizerVariance.trans
    exact div_le_div_of_nonneg_left (mul_nonneg hL.le (sq_nonneg _))
      (by positivity) (by nlinarith only [sq_nonneg (T.S.n k : ℝ)])
  exact ⟨NormalizerCheck, instNormalizer, row, hrowCount, hRowPoly, hrowCover,
    hL, hAmplitudeCell.2, hImageBias, hImageVariance⟩

set_option maxHeartbeats 400000 in
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
  obtain ⟨nBirthday, hBirthday⟩ := cell_pool_birthday_cutoff hκ
  -- The physical restrictions are independent of the concentration estimates.
  -- The cutoff must still precede the cell/history/pin union budgets.
  have hBudgets : ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R)
      (K : CellRestrictedKernels R Perm),
      (∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
        K.qtilde C pool W g = K.qbar C W g) →
      R.SourceValid → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (∀ C, (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ)) / 4) →
      ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
        ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
          (R.Hist C) Check (T.S.n k) (1 / 2),
          Nonempty (CellDiagnosticLink K C D) ∧
          Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
    obtain ⟨nDirect, hDirectRoom⟩ := Lane_sol_s16_prod1.direct_image_budget_room
    have hClusterBudgets : ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
        (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
        (∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
          K.qtilde C pool W g = K.qbar C W g) →
        R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
        (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
        (∀ C, (H.geom.nslot C : ℝ) ^ 2 / Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ)) / 4) →
        ∀ C, ∃ Check : Type, ∃ _ : Fintype Check,
          ∃ D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
            (R.Hist C) Check (T.S.n k) (1 / 2),
            Nonempty (CellDiagnosticLink K C D) ∧
            Nonempty (PoolConcentrationHypotheses D) ∧ Nonempty (LoadGateHypotheses D) := by
      obtain ⟨nNormalizer, hNormalizer⟩ := cluster_normalizer_setup hκ
      refine ⟨nNormalizer, ?_⟩
      intro T k PT K16 Q H R Perm K hFallback hR hc hn hPerm hBirthday C
      obtain ⟨NormalizerCheck, instNormalizer, row, hrowCount, hrowCap, hrowCover,
        hslots, hEpsilonLower, hImageBias, hImageVariance⟩ :=
          hNormalizer Q H R Perm K hR hc hn hPerm hBirthday C
      letI := instNormalizer
      -- The physical normalizer rows now have the complete image bias,
      -- sensitivity and union variance budgets. Star/pin checks and the
      -- slice-load gate remain, including its global variance requirement.
      sorry
    obtain ⟨nCluster, hCluster⟩ := hClusterBudgets
    refine ⟨max nDirect nCluster, ?_⟩
    intro T k PT K16 Q H R Perm K hFallback hR hn hPerm hBirthday C
    by_cases hc : PT.tiling.mode.isCluster
    · exact hCluster Q H R Perm K hFallback hR hc (le_trans (Nat.le_max_right _ _) hn) hPerm hBirthday C
    · have hd := direct_cell_bin_size hκ Q hc (H.geom.cellPatch C)
      have htheta : κ.θstar ≤ 1 := by
        have hb := hκ.bucket
        rw [hκ.clock.2.1] at hb
        have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hb.1
        nlinarith [mul_le_mul_of_nonneg_right hKp hb.2.2.2.2.le]
      have hK : 0 < κ.Kcell := lt_of_lt_of_le
        (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
      have hK1 : 1 ≤ κ.Kcell := by
        have hh := (div_le_iff₀ hκ.bucket.2.2.2.2).mp hκ.Kcell_big
        nlinarith [mul_nonneg hK.le (sub_nonneg.mpr htheta)]
      have hL : (T.S.n k : ℝ) ^ (200 : ℕ) ≤ H.geom.nslot C := by
        have heq := H.cell_partition.slot_count C
        change H.geom.nslot C = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
          (PT.tiling.P (H.geom.cellPatch C)).d⌉₊ at heq
        rw [hκ.Ac_eq, hd] at heq
        simp only [Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_one, div_one] at heq
        have hceil := Nat.le_ceil (κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ))
        have hh : κ.Kcell * (T.S.n k : ℝ) ^ (200 : ℕ) ≤ H.geom.nslot C := by
          simpa only [← heq] using hceil
        exact (le_mul_of_one_le_left (pow_nonneg (Nat.cast_nonneg _) _) hK1).trans hh
      have hnpos : (0 : ℝ) < T.S.n k := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
      have hslots : 0 < H.geom.nslot C := by
        exact_mod_cast lt_of_lt_of_le (pow_pos hnpos _) hL
      have hB : (0 : ℝ) < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := by
        obtain ⟨b, hb⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty
          (Finset.nonempty_iff_ne_empty.mp (Q.profiled_valid.tiling_valid.patch_nonempty _).2)
        letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨⟨b, hb⟩⟩
        exact_mod_cast Fintype.card_pos
      obtain ⟨hbias, hvariance⟩ := hDirectRoom (T.S.n k) (H.geom.nslot C)
        (Fintype.card (Bin PT.tiling (H.geom.cellPatch C)))
        (le_trans (Nat.le_max_left _ _) hn) Q.n_large hB hL (hBirthday C)
      exact direct_diagnostics_with_budgets hκ Q H R Perm K hR hc hPerm C hslots hbias hvariance (hBirthday C)
  obtain ⟨n₀, hBudgets⟩ := hBudgets
  refine ⟨max n₀ nBirthday, 1 / 2, rfl, ?_⟩
  intro T k PT K16 Q H R Perm hR hn hPerm
  obtain ⟨K, hFallback⟩ := restricted_kernels_exists hκ R Perm hPerm
  exact ⟨K, hBudgets Q H R Perm K hFallback hR (le_trans (Nat.le_max_left _ _) hn) hPerm
    (hBirthday Q H (le_trans (Nat.le_max_right _ _) hn))⟩

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

private theorem cluster_incoming_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) (hR : R.SourceValid) (hCal : CellCalibrationScale PT)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b ≤ 8 * (PT.tiling.P (G.cellPatch C)).d /
      Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
  classical
  have hd : 2 ≤ (PT.tiling.P (G.cellPatch C)).d :=
    le_trans (by norm_num) (hCal.room hc (G.cellPatch C)).2.1
  have hdpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).d := by exact_mod_cast (by omega : 0 < (PT.tiling.P (G.cellPatch C)).d)
  have heps := slice_epsilon_range hκ (PT.tiling.P (G.cellPatch C)).h
  have hsmall := Lane_sol_s16_prod1.calibration_pretrim_small _ _ _ hd heps
    (hCal.room hc (G.cellPatch C)).2.2.2.2.2
  have ht : 0 ≤ (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
      sliceT κ (PT.tiling.P (G.cellPatch C)).h := by positivity
  have hexp := Lane_sol_s16_prod1.calibration_exp_cap _ _ (le_trans (by norm_num) hd) ht
    (by simpa only [mul_assoc] using (hCal.room hc (G.cellPatch C)).2.2.1)
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨⟨ss, g'⟩, hsg⟩ := groups.surjective g
    have hs := supported_history R C W hW ss
    have hg : S.AllGood (records ss (W ss)) := (hPass ss (W ss)).mp hs.1
    have hqin : (R.qin C W g).w b = S.qin (records ss (W ss)) g' b := by
      rw [← hsg, R.qin_eq C W _ b (supported_history R C W hW), hTrim]
      simp_rw [hQ]
      unfold SliceSolver.qin
      split_ifs <;> simp
    rw [hqin]
    have hcap := Lane_sol_s16_prod1.solver_qin_cap S (records ss (W ss)) hg g' b hsmall
    have hM := physical_bin_count hκ Q (G.cellPatch C)
    have hB : (0 : ℝ) < Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
      have hMpos : 0 < (PT.tiling.P (G.cellPatch C)).M := by
        rw [← (PT.tiling.P (G.cellPatch C)).cardY]
        exact Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty _).2
      nlinarith [show (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).M by exact_mod_cast hMpos]
    have hMpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).M := by rw [← hM]; positivity
    calc
      _ ≤ 8 * Real.exp (2 * (PT.tiling.kScale (G.cellPatch C) : ℝ) * PT.tiling.tScale (G.cellPatch C)) *
          (PT.tiling.P (G.cellPatch C)).d / (PT.tiling.P (G.cellPatch C)).M := hcap
      _ = 8 * Real.exp (2 * (PT.tiling.kScale (G.cellPatch C) : ℝ) * PT.tiling.tScale (G.cellPatch C)) /
          Fintype.card (Bin PT.tiling (G.cellPatch C)) := by rw [← hM]; field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hB.le
        simpa only [Tiling.kScale, Tiling.tScale, mul_assoc] using
          (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 8))
  · exact (hDirect hc).elim


private theorem group_contribution_minimum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {K16 : ℝ} {hκ : κ.Admissible}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT} {R : CellRawData G}
    {Perm : CellPermissions R} (K : CellRestrictedKernels R Perm) (hR : R.SourceValid)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0)
    (hm : ∀ g, (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) (y : Fin (T.S.N k))
    (hcon : (K.binProblem C pool W).contribution g b y ≠ 0) :
    1 / ((PT.tiling.P (G.cellPatch C)).d : ℝ) ≤
      (K.binProblem C pool W).contribution g b y := by
  classical
  have htarget : (K.qtilde C pool W g).w b ≠ 0 := by
    intro hh
    simp only [CellRestrictedKernels.binProblem, hh, if_true] at hcon
    exact hcon rfl
  have hU : (R.U C W g b).w y ≠ 0 := by
    intro hh
    simp only [CellRestrictedKernels.binProblem, if_neg htarget, hh] at hcon
    simp at hcon
  have hg : ∃ r : OddCellRole G C, R.groupOf C r = g := by
    by_contra hn
    push_neg at hn
    simp only [CellRestrictedKernels.binProblem, if_neg htarget] at hcon
    have hh : ∀ r : OddCellRole G C, (if R.groupOf C r = g then (R.U C W g b).w y else 0) = 0 := by
      intro r
      rw [if_neg (hn r)]
    simp only [hh, Finset.sum_const_zero] at hcon
    exact hcon rfl
  obtain ⟨r, hr⟩ := hg
  have hlow := physical_U_atom_lower R hR hc C W g b
    (positive_pool_bin_raw K C pool W hW hm g b htarget) y hU
  rw [Q.profiled_valid.tiling_valid.bins_card _ _ b.2] at hlow
  apply hlow.trans
  change _ ≤ if (K.qtilde C pool W g).w b = 0 then 0 else _
  rw [if_neg htarget]
  have hsum := Finset.single_le_sum
    (s := (Finset.univ : Finset (OddCellRole G C)))
    (f := fun r => if R.groupOf C r = g then (R.U C W g b).w y else 0)
    (fun r _ => by split_ifs <;> first | exact (R.U C W g b).nonneg y | exact le_rfl)
    (Finset.mem_univ r)
  rwa [if_pos hr] at hsum

private theorem group_atom_estimate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
      (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C),
      R.SourceValid → CellCalibrationScale PT → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      (R.history C).w W ≠ 0 →
      (∀ g, |(∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) /
          ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4)) →
      ∀ g b, (K.qtilde C pool W g).w b ≤
        Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) (-40) := by
  classical
  refine ⟨max 2 ⌈Real.exp 1⌉₊, ?_⟩
  intro T k PT K16 Q H R Perm K C pool W hR hCal hc hn hPerm hW hnorm g b
  let d := (PT.tiling.P (H.geom.cellPatch C)).d
  let B := Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
  let L := H.geom.nslot C
  have hd : 2 ≤ d := le_trans (by norm_num) (hCal.room hc (H.geom.cellPatch C)).2.1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn2 : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast Q.n_large
  have hn1 : (1 : ℝ) ≤ T.S.n k := by linarith
  have heN : Real.exp 1 ≤ (T.S.n k : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (Nat.le_max_right _ _) hn))
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) heN
    simpa only [Real.log_exp] using hh
  have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (T.S.n k : ℝ)),
      sq_nonneg (Real.sqrt (Real.log (T.S.n k : ℝ)) - 1)]
  have hdN : (d : ℝ) ≤ T.S.n k := by
    calc
      _ ≤ Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ))) := Q.bin_count_bound _
      _ ≤ Real.exp (Real.log (T.S.n k : ℝ)) := Real.exp_le_exp.mpr hsqrt
      _ = _ := Real.exp_log (by linarith)
  have hK : 1 ≤ κ.Kcell := by
    apply le_trans _ hκ.Kcell_big
    apply (le_div_iff₀ hκ.bucket.2.2.2.2).mpr
    have hh := thetaStar_slack hκ
    linarith
  have h197 : (32 : ℝ) ≤ (T.S.n k : ℝ) ^ (158 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ (T.S.n k : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hn2 _
      _ ≤ _ := pow_le_pow_right₀ hn1 (by norm_num : (5 : ℕ) ≤ 158)
  have hpower : 32 * (d : ℝ) ^ (42 : ℕ) ≤ (T.S.n k : ℝ) ^ (200 : ℕ) := by
    calc
      _ ≤ (T.S.n k : ℝ) ^ (158 : ℕ) * (T.S.n k : ℝ) ^ (42 : ℕ) :=
        mul_le_mul h197 (pow_le_pow_left₀ hdpos.le hdN _) (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]
  have hslot : 32 * (d : ℝ) ^ (41 : ℕ) ≤ (L : ℝ) := by
    have hceil : κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / d ≤ (L : ℝ) := by
      change _ ≤ (H.data.cells.nslot C : ℝ)
      rw [H.cell_partition.slot_count C]
      exact Nat.le_ceil _
    have hnum : (T.S.n k : ℝ) ^ (200 : ℕ) ≤ κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac := by
      rw [hκ.Ac_eq]
      have hp : Real.rpow (T.S.n k : ℝ) ((200 : ℕ) : ℝ) = (T.S.n k : ℝ) ^ (200 : ℕ) := by
        simpa only [Real.rpow_eq_pow] using Real.rpow_natCast (T.S.n k : ℝ) 200
      rw [hp]
      nlinarith [show 0 ≤ (T.S.n k : ℝ) ^ (200 : ℕ) by positivity]
    apply le_trans _ hceil
    apply (le_div_iff₀ hdpos).mpr
    have hp := hpower.trans hnum
    nlinarith only [hp]
  have hL : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hslot
  have hB : (0 : ℝ) < B := by
    letI := (hPerm C W hW).bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hret := Lane_sol_s16_prod1.permission_retained_half _ _ (hPerm C W hW) g
  have hbar : ∀ b, (K.qbar C W g).w b ≤ 16 * d / (B : ℝ) := by
    intro b
    rw [K.qbar_eq C W g b hW]
    have hnum : (if b ∈ (Perm.table C).permitted g then (R.qin C W g).w b else 0) ≤
        8 * d / (B : ℝ) := by
      split_ifs
      · exact cluster_incoming_cap hκ Q R hR hCal hc C W hW g b
      · positivity
    calc
      _ ≤ (8 * d / (B : ℝ)) / (∑ b ∈ (Perm.table C).permitted g, (R.qin C W g).w b) :=
        div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ (8 * d / (B : ℝ)) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hret
      _ = _ := by ring
  have hlower := Lane_sol_s16_prod1.typical_normalizer_lower (T.S.n k) Q.n_large
    (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) L B hL hB (hnorm g)
  have hm : (∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity) hlower)
  have hcap := Lane_sol_s16_prod1.pool_atom_cap (K.qbar C W g) (K.qtilde C pool W g)
    (Finset.univ.image pool) L B (16 * d) hL hB (by positivity) hbar hlower
    (fun b => K.qtilde_eq C pool W g b hW hm) b
  calc
    _ ≤ 32 * d / (L : ℝ) := by convert hcap using 1 <;> ring
    _ ≤ 1 / (d : ℝ) ^ (40 : ℕ) := by
      apply (div_le_div_iff₀ hL (pow_pos hdpos _)).mpr
      nlinarith only [hslot]
    _ = Real.rpow (d : ℝ) (-40) := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]

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
  · have hStrong := hAtomCutoff Q H R Perm K C pool W hR hCalibration hCluster hn hPerm hW
      (fun g => by
        have h := (D.checks_cover pool ht.2).1 (L.groupProbe g) W
        rw [L.normalizer_eq pool W g hW] at h
        simpa only [Fintype.card_fin] using h)
    intro g b
    exact (hStrong g b).trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ (PT.tiling.P (H.geom.cellPatch C)).d))
      (by norm_num : (-40 : ℝ) ≤ -0.95))
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
  · intro q hq
    let P := K.binProblem C pool W
    letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := (hPerm C W hW).bins_nonempty
    have hLocal : ∀ v, DependsOn (P.failureMass v) (P.participants v : Set (R.Group C)) := by
      intro v a a' haa
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
    have hMean : ∀ v, P.independentFailure v ≤ Real.rpow P.ε (1 / 4 : ℝ) := by
      intro v
      have h := (D.checks_cover pool ht.2).2.1 (L.starProbe v) W
      rw [L.failure_eq pool W v hW, L.epsilon_eq] at h
      exact h
    have hPinMean : ∀ v g b, P.pinnedFailure v g b ≤ Real.rpow P.ε (1 / 4 : ℝ) := by
      intro v g b
      have h := (D.checks_cover pool ht.2).2.2 (L.pinProbe v g b) W
      rw [L.pinned_failure_eq pool W v g b hW, L.epsilon_eq] at h
      exact h
    have hShort : ∀ v, ((P.participants v).card : ℝ) ≤ 2 * Real.rpow (P.d : ℝ) 0.01 := by
      intro v
      have hcard : (P.participants v).card ≤ (PT.tiling.P (H.geom.cellPatch C)).h :=
        Finset.card_image_le.trans (physical_participants_count K C v)
      have hh := hRoom.2.2.2.1
      have hNat : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
          2 * ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ^ 2 := by
        have hi : (PT.tiling.P (H.geom.cellPatch C)).h = 0 ∨
            1 ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by omega
        rcases hi with hi | hi
        · simp [hi]
        · have hi' : (1 : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by exact_mod_cast hi
          nlinarith
      have hb : ((P.participants v).card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.01 :=
        (show ((P.participants v).card : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).h by exact_mod_cast hcard).trans
          (hNat.trans hh)
      have hp : 0 ≤ Real.rpow (P.d : ℝ) 0.01 := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    have hStrong := hAtomCutoff Q H R Perm K C pool W hR hCalibration hCluster hn hPerm hW
      (fun g => by
        have h := (D.checks_cover pool ht.2).1 (L.groupProbe g) W
        rw [L.normalizer_eq pool W g hW] at h
        simpa only [Fintype.card_fin] using h)
    have hStarBounds := Lane_sol_s16_prod1.group_star_event_bounds P hlarge
      (slice_epsilon_range hκ _).1 (by
        intro v a
        change 0 ≤ K.failure C W v a
        simp only [CellRestrictedKernels.failure, hCluster, if_true]
        exact (Lane_sol_s16_prod1.pr_range _ _).1)
      hLocal hMean hPinMean hShort hStrong q hq
    have hContributionLower : ∀ g b y, P.contribution g b y ≠ 0 →
        1 / (P.d : ℝ) ≤ P.contribution g b y := by
      intro g b y hcon
      exact group_contribution_minimum Q K hR hCluster C pool W hW
        (typical_pool_mass_ne_zero hκ Q K C D L pool ht W hW) g b y hcon
    apply Lane_sol_s16_group.dyadic_group_certificates P hlarge
      (slice_epsilon_range hκ _).1 (PT.tiling.P (H.geom.cellPatch C)).h
      hRoom.2.2.2.2.2 (fun b => b.1)
    · intro b
      exact le_of_eq (Q.profiled_valid.tiling_valid.bins_card _ _ b.2)
    · exact physical_bins_disjoint _
    · intro g b y hcon
      by_contra hy
      have hzero : (R.U C W g b).w y = 0 := by
        by_contra hn
        exact hy (R.U_support C W g b y hn)
      simp only [P, CellRestrictedKernels.binProblem, hzero, ite_self, Finset.sum_const_zero] at hcon
      exact hcon rfl
    · intro g b y
      exact group_contribution_nonneg K C pool W g b y
    · exact physical_group_contribution_cap hκ K hR hCalibration hCluster C pool W hW
        (typical_pool_mass_ne_zero hκ Q K C D L pool ht W hW)
    · exact hContributionLower
    · intro y
      rw [nominal_load_eq K C pool W y]
      have h := hload (L.Column.symm y)
      rw [L.load_eq, L.threshold_eq, L.Column.apply_symm_apply] at h
      have hθ : κ.θstar ≤ 1 / 1000 := by
        have hclock := hκ.clock.2.1
        have hb := hκ.bucket
        rw [hclock] at hb
        have hKp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hb.1
        nlinarith [mul_le_mul_of_nonneg_right hKp hb.2.2.2.2.le]
      exact h.trans hθ
    · exact hLocal
    · intro v
      have hcard : (P.participants v).card ≤ (PT.tiling.P (H.geom.cellPatch C)).h :=
        Finset.card_image_le.trans (physical_participants_count K C v)
      have hpow : Real.rpow (P.d : ℝ) 0.025 ≤ P.d := by
        have hbase : (1 : ℝ) ≤ P.d := by
          exact_mod_cast (show 1 ≤ P.d from le_trans (by norm_num) hTwo)
        have hh : Real.rpow (P.d : ℝ) 0.025 ≤ Real.rpow (P.d : ℝ) 1 :=
          Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
        have hone : Real.rpow (P.d : ℝ) 1 = P.d := Real.rpow_one _
        exact hh.trans_eq hone
      have hh := hRoom.2.2.2.2.1
      have hbound : ((P.participants v).card : ℝ) ≤ P.d := by
        have hc : ((P.participants v).card : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by exact_mod_cast hcard
        exact hc.trans (le_trans (by norm_num : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
          (PT.tiling.P (H.geom.cellPatch C)).h + 1) (hh.trans hpow))
      exact_mod_cast hbound
    · intro g
      have hdeg := physical_group_star_degree K hR hCalibration hCluster C g
      have hpow : Real.rpow (P.d : ℝ) 0.01 ≤ P.d := by
        have hbase : (1 : ℝ) ≤ P.d := by
          exact_mod_cast (show 1 ≤ P.d from le_trans (by norm_num) hTwo)
        have hh : Real.rpow (P.d : ℝ) 0.01 ≤ Real.rpow (P.d : ℝ) 1 :=
          Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
        have hone : Real.rpow (P.d : ℝ) 1 = P.d := Real.rpow_one _
        exact hh.trans_eq hone
      exact hdeg.trans hpow
    · exact hq
    · exact hStarBounds.1
    · exact hStarBounds.2

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
    · intro hr q hq seed
      have hc := hRegime.mp hr
      have hRoom := hCalibration.room hc (H.geom.cellPatch C)
      have hd : (10 ^ 100 : ℕ) ≤ L.problem.d := by
        rw [L.scale_eq, if_pos hc]
        exact hRoom.2.1
      have hSize : ∀ v, (L.problem.participants v).card ≤ L.problem.h := by
        intro v
        rw [L.participants_eq, L.height_eq]
        exact physical_participants_count K C v
      have hQuery : (L.problem.h + 1 : ℝ) ≤ Real.rpow (L.problem.d : ℝ) 0.025 := by
        rw [L.height_eq, L.scale_eq, if_pos hc]
        exact hRoom.2.2.2.2.1
      have hShort : (L.problem.h + 1 : ℝ) ≤ 2 * Real.rpow (L.problem.d : ℝ) 0.01 := by
        rw [L.height_eq, L.scale_eq, if_pos hc]
        have hh := hRoom.2.2.2.1
        have hd1 : (1 : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).d := by
          exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 10 ^ 100) hRoom.2.1
        have hp : (1 : ℝ) ≤ Real.rpow ((PT.tiling.P (H.geom.cellPatch C)).d : ℝ) 0.01 :=
          Real.one_le_rpow hd1 (by norm_num)
        have hNat : ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ≤
            2 * ((PT.tiling.P (H.geom.cellPatch C)).h : ℝ) ^ 2 := by
          have hi : (PT.tiling.P (H.geom.cellPatch C)).h = 0 ∨
              1 ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by omega
          rcases hi with hi | hi
          · simp [hi]
          · have hi' : (1 : ℝ) ≤ (PT.tiling.P (H.geom.cellPatch C)).h := by exact_mod_cast hi
            nlinarith
        linarith
      have hLower : ∀ r y, (L.problem.target r).w y ≠ 0 →
          1 / (L.problem.d : ℝ) ≤ (L.problem.target r).w y := by
        intro r y hy
        rw [L.targets_eq, if_pos hc] at hy ⊢
        have h := physical_U_atom_lower R hR hc C W (R.groupOf C r) (a (R.groupOf C r))
          (positive_pool_bin_raw K C pool W hW hm _ _ (hpositive hc _)) y hy
        rw [Q.profiled_valid.tiling_valid.bins_card _ _ (a (R.groupOf C r)).2] at h
        rw [L.scale_eq, if_pos hc]
        exact h
      have hroom : 16 * (L.problem.d : ℝ) ^ 2 * (L.problem.h + 1 : ℝ) ^ 2 *
          Real.rpow (sliceEps κ (PT.tiling.P (H.geom.cellPatch C)).h) (1 / 16 : ℝ) ≤
          Real.rpow (L.problem.d : ℝ) (-20) := by
        rw [L.scale_eq, if_pos hc, L.height_eq]
        exact hRoom.2.2.2.2.2
      obtain ⟨y, _⟩ := (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2
      letI : Nonempty (Fin (T.S.N k)) := ⟨y⟩
      exact Lane_sol_s16_prod1.role_star_certificates L.problem _ (slice_epsilon_range hκ _).1
        hd hr hSize
        (role_block_degree K C pool W a L (role_block_count L.problem (hClusterColumns hr)))
        hQuery hShort hIndependent hLower hroom q hq seed
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

set_option maxHeartbeats 2000000 in
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
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  refine ⟨max nG nR, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds hSource hn hPerm
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left _ _).trans hn
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hLowCluster : PT.tiling.mode.isCluster → PT.tiling.mode = .lowCluster := by
    intro hcl
    cases hmode : PT.tiling.mode with
    | bounded =>
        rw [hmode] at hcl
        simp [Mode.isCluster] at hcl
    | lowDirect =>
        rw [hmode] at hcl
        simp [Mode.isCluster] at hcl
    | highDirect =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | lowCluster => rfl
    | highSmall =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highLarge =>
        have hfalse : False := by
          have hlow := Q.mode_low
          rw [hmode] at hlow
          simpa [Mode.isLow] using hlow
        exact hfalse.elim
  have hGroupInput (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0) :
      GroupBinHypotheses hκ (K.binProblem C pool W) :=
    hG Q H hCalibration R Perm K C (Ds.diagnostic C) hSource (hLowCluster hcl)
      hnG hPerm (Ds.linked C) pool W htyp hload hw
  have hRoleInput (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0)
      (hsafe : PT.tiling.mode.isCluster → (K.binProblem C pool W).safe a)
      (hqpos : PT.tiling.mode.isCluster →
        ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0) :
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem := by
    obtain ⟨L, hL, _hIndependent, _hPinned⟩ :=
      hR Q H hCalibration R Perm K C (Ds.diagnostic C) hSource hnR hPerm
        (Ds.linked C) pool W a htyp hload hw hsafe hqpos
    exact ⟨L, hL⟩
  have hDirectD1 (hnot : ¬ PT.tiling.mode.isCluster) (i : Fin PT.tiling.m) :
      (PT.tiling.P i).d = 1 := by
    cases hmode : PT.tiling.mode with
    | bounded =>
        have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
        exact (hdata.2 i).2.2.1
    | lowDirect =>
        have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode) i
        exact hdata.2.2.2.2.2.1
    | lowCluster =>
        have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
        exact False.elim (hnot hc)
    | highDirect =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highSmall =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
    | highLarge =>
        have hlow := Q.mode_low
        rw [hmode] at hlow
        have hfalse : False := by simpa [Mode.isLow] using hlow
        exact hfalse.elim
  have hBinSingleton (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster)
      (D : Bin PT.tiling (H.geom.cellPatch C)) : D.1.card = 1 := by
    calc
      D.1.card = (PT.tiling.P (H.geom.cellPatch C)).d :=
        Q.profiled_valid.tiling_valid.bins_card (H.geom.cellPatch C) D.1 D.2
      _ = 1 := hDirectD1 hnot (H.geom.cellPatch C)
  let binLabel (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster)
      (D : Bin PT.tiling (H.geom.cellPatch C)) : Fin (T.S.N k) :=
    Classical.choose (Finset.card_eq_one.mp (hBinSingleton C hnot D))
  let defaultBin (C : H.geom.Cell) : Bin PT.tiling (H.geom.cellPatch C) :=
    Classical.choice (by
      have hYne : (PT.tiling.P (H.geom.cellPatch C)).Y ≠ ∅ :=
        (Q.profiled_valid.tiling_valid.patch_nonempty (H.geom.cellPatch C)).2.ne_empty
      have hY : (PT.tiling.P (H.geom.cellPatch C)).Y ≠ ⊥ := by simpa using hYne
      obtain ⟨D, hD⟩ := (PT.tiling.P (H.geom.cellPatch C)).bins.parts_nonempty hY
      exact ⟨⟨D, hD⟩⟩)
  let binOfLabel (C : H.geom.Cell) (pool : CellPool H.geom C)
      (y : Fin (T.S.N k)) : Bin PT.tiling (H.geom.cellPatch C) :=
    if hy : ∃ s : Fin (H.geom.nslot C), y ∈ (pool s).1 then
      pool (Classical.choose hy) else defaultBin C
  let groupBinReadout (C : H.geom.Cell) (pool : CellPool H.geom C)
      (ys : OddCellRole H.geom C → Fin (T.S.N k))
      (a0 : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :
      R.Group C → Bin PT.tiling (H.geom.cellPatch C) := fun g =>
    if hr : ∃ r, R.groupOf C r = g then
      binOfLabel C pool (ys (Classical.choose hr)) else a0 g
  have hDirectRoleData (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      ∃ L : CellRoleProblem K C pool W (fun _ => defaultBin C),
        RoleLabelHypotheses hκ L.problem ∧
        ∃ Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)),
          L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
    have hsafe : PT.tiling.mode.isCluster →
        (K.binProblem C pool W).safe (fun _ => defaultBin C) := fun hc => False.elim (hnot hc)
    have hqpos : PT.tiling.mode.isCluster →
        ∀ g, (K.qtilde C pool W g).w (defaultBin C) ≠ 0 := fun hc => False.elim (hnot hc)
    obtain ⟨L, hL⟩ := hRoleInput C pool W (fun _ => defaultBin C) htyp hload hw hsafe hqpos
    obtain ⟨Qlab, hFeasible, hMarg⟩ := calibrated_role_labels hκ L.problem hL
    exact ⟨L, hL, Qlab, hFeasible, hMarg⟩
  let directRoleLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) :=
    Classical.choose ((Classical.choose_spec (hDirectRoleData C pool W htyp hload hw hnot)).2)
  have hDirectGroupInj (C : H.geom.Cell) (hnot : ¬ PT.tiling.mode.isCluster) :
      Function.Injective (R.groupOf C) := by
    rcases hSource with ⟨hmode, _hUniform, _hData⟩ | ⟨_hnot, hData⟩
    · have hcl : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
      exact False.elim (hnot hcl)
    · exact (hData C).1
  have hDirectRoleSupport (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) (L : CellRoleProblem K C pool W a)
      (Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)))
      (hMarg : ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y)
      (hnot : ¬ PT.tiling.mode.isCluster) (ys : OddCellRole H.geom C → Fin (T.S.N k))
      (hys : Qlab.w ys ≠ 0) (r : OddCellRole H.geom C) :
      poolContainsLabel pool (ys r) := by
    have hweight : 0 < Qlab.w ys :=
      lt_of_le_of_ne (Qlab.nonneg ys) (Ne.symm hys)
    have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr Qlab (fun z => z r = ys r) ys rfl
    have htarget : (L.problem.target r).w (ys r) ≠ 0 := by
      have hpos : 0 < Qlab.pr (fun z => z r = ys r) := lt_of_lt_of_le hweight hAtom
      rw [hMarg r (ys r)] at hpos
      exact ne_of_gt hpos
    have hlabel : ys r ∈ L.problem.blockLabels (L.problem.blockOf r) :=
      L.problem.target_support r (ys r) htarget
    obtain ⟨one, hblock⟩ := L.direct_block hnot
    rw [hblock (L.problem.blockOf r)] at hlabel
    simpa [poolContainsLabel, Finset.mem_biUnion, Finset.mem_image] using hlabel
  have hDirectDecode (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a0 : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) (L : CellRoleProblem K C pool W a0)
      (aOther : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)))
      (hMarg : ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y)
      (hnot : ¬ PT.tiling.mode.isCluster)
      (ys : OddCellRole H.geom C → Fin (T.S.N k)) (hys : Qlab.w ys ≠ 0)
      (r : OddCellRole H.geom C) :
      binLabel C hnot (groupBinReadout C pool ys aOther (R.groupOf C r)) = ys r := by
    have hinj := hDirectGroupInj C hnot
    have hr : ∃ r' : OddCellRole H.geom C, R.groupOf C r' = R.groupOf C r := ⟨r, rfl⟩
    have hchosen : Classical.choose hr = r := by
      apply hinj
      exact Classical.choose_spec hr
    have hpool := hDirectRoleSupport C pool W a0 L Qlab hMarg hnot ys hys r
    rcases hpool with ⟨s, hs⟩
    have hfind : ∃ s : Fin (H.geom.nslot C), ys r ∈ (pool s).1 := ⟨s, hs⟩
    have hy : ys r ∈ (pool (Classical.choose hfind)).1 := Classical.choose_spec hfind
    have hcard := hBinSingleton C hnot (pool (Classical.choose hfind))
    have hsingle : (pool (Classical.choose hfind)).1 =
        {binLabel C hnot (pool (Classical.choose hfind))} :=
      Classical.choose_spec (Finset.card_eq_one.mp hcard)
    have hlabel : ys r = binLabel C hnot (pool (Classical.choose hfind)) := by
      rw [hsingle] at hy
      simpa using hy
    have hread : groupBinReadout C pool ys aOther (R.groupOf C r) = binOfLabel C pool (ys r) := by
      dsimp [groupBinReadout]
      rw [dif_pos hr, hchosen]
    have hread' : binOfLabel C pool (ys r) = pool (Classical.choose hfind) := by
      simp [binOfLabel, hfind]
    rw [hread, hread']
    exact hlabel.symm
  let directBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (htyp : (Ds.diagnostic C).typical pool) (hload : (Ds.diagnostic C).loadGate pool W)
      (hw : (R.history C).w W ≠ 0) (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    FinLaw.map
      (FinLaw.bind (directRoleLaw C pool W htyp hload hw hnot)
        (fun _ => FinLaw.pi fun g => K.qtilde C pool W g))
      (fun ω => groupBinReadout C pool ω.1 ω.2)
  let directLabelLaw (C : H.geom.Cell) (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (hnot : ¬ PT.tiling.mode.isCluster) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) := by
    letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
    exact FinLaw.dirac (fun r => binLabel C hnot (a (R.groupOf C r)))
  let calibratedBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    Classical.choose (calibrated_group_bins hκ (K.binProblem C pool W)
      (hGroupInput C pool W hcl htyp hload hw))
  let productBinLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C) :
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
    FinLaw.pi fun g => K.qtilde C pool W g
  have hDirectU (C : H.geom.Cell) (W : R.Hist C) (g : R.Group C)
      (D : Bin PT.tiling (H.geom.cellPatch C)) (y : Fin (T.S.N k))
      (hnot : ¬ PT.tiling.mode.isCluster) :
      (R.U C W g D).w y = if y ∈ D.1 then 1 else 0 := by
    rcases hSource with ⟨hmode, _hUniform, _hCells⟩ | ⟨_hnot, hCells⟩
    · have hcluster : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
      exact False.elim (hnot hcluster)
    · rcases hCells C with ⟨_hInjective, _hValues, _hPass, _hRaw, _hTrim, hU, _hPrior⟩
      exact hU W g D y
  have hBinUnique (C : H.geom.Cell) (D D' : Bin PT.tiling (H.geom.cellPatch C))
      (y : Fin (T.S.N k)) (hD : y ∈ D.1) (hD' : y ∈ D'.1) : D = D' := by
    by_contra hne
    have hdis := (PT.tiling.P (H.geom.cellPatch C)).bins.disjoint D.2 D'.2 (by
      intro hsets
      apply hne
      exact Subtype.ext hsets)
    exact False.elim ((Finset.disjoint_left.mp hdis) hD hD')
  have hDirectRowPoolSupport (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (L : CellRoleProblem K C pool W a) (r : OddCellRole H.geom C)
      (y : Fin (T.S.N k)) (hnot : ¬ PT.tiling.mode.isCluster)
      (hy : (L.problem.target r).w y ≠ 0) : poolContainsLabel pool y := by
    have hlabels := L.problem.target_support r y hy
    obtain ⟨one, hblock⟩ := L.direct_block hnot
    rw [hblock (L.problem.blockOf r)] at hlabels
    simpa [poolContainsLabel, Finset.mem_biUnion, Finset.mem_image] using hlabels
  have hDirectTargetMap (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (L : CellRoleProblem K C pool W a) (r : OddCellRole H.geom C)
      (hnot : ¬ PT.tiling.mode.isCluster) (D : Bin PT.tiling (H.geom.cellPatch C)) :
      (FinLaw.map (L.problem.target r) (binOfLabel C pool)).pr (fun B => B = D) =
        (K.qtilde C pool W (R.groupOf C r)).w D := by
    rw [Lane_q_s16_prod2.finLaw_map_pr]
    have hevent : ∀ y, (L.problem.target r).w y ≠ 0 →
        (binOfLabel C pool y = D ↔ y ∈ D.1) := by
      intro y hy
      have hp := hDirectRowPoolSupport C pool W a L r y hnot hy
      constructor
      · intro hEq
        have hmem : y ∈ (binOfLabel C pool y).1 := by
          unfold binOfLabel
          split_ifs with hs
          · exact Classical.choose_spec hs
          · exact False.elim (hs hp)
        rw [hEq] at hmem
        exact hmem
      · intro hyD
        obtain ⟨s, hs⟩ := hp
        let hslt : ∃ s : Fin (H.geom.nslot C), y ∈ (pool s).1 := ⟨s, hs⟩
        have hpoolMem : y ∈ (pool (Classical.choose hslt)).1 := Classical.choose_spec hslt
        have huniq := hBinUnique C D (pool (Classical.choose hslt)) y hyD hpoolMem
        have hread : binOfLabel C pool y = pool (Classical.choose hslt) := by
          simp [binOfLabel, hslt]
        exact hread.trans huniq.symm
    rw [Lane_q_s16_prod2.finLaw_pr_congr_of_supported (L.problem.target r)
      (fun y => binOfLabel C pool y = D) (fun y => y ∈ D.1) hevent]
    have htarget : ∀ y, (L.problem.target r).w y =
        ∑ B, (K.qtilde C pool W (R.groupOf C r)).w B * (R.U C W (R.groupOf C r) B).w y := by
      intro y
      simpa [hnot] using L.targets_eq r y
    have hmass : (L.problem.target r).pr (fun y => y ∈ D.1) =
        (K.qtilde C pool W (R.groupOf C r)).w D := by
      letI : DecidablePred (fun y : Fin (T.S.N k) => y ∈ D.1) :=
        fun y => Classical.propDecidable (y ∈ D.1)
      have hmassRaw : (∑ y, if y ∈ D.1 then (L.problem.target r).w y else 0) =
          (K.qtilde C pool W (R.groupOf C r)).w D := by
        calc
          (∑ y, if y ∈ D.1 then (L.problem.target r).w y else 0) =
              ∑ y, ∑ B, if y ∈ D.1 then
                (K.qtilde C pool W (R.groupOf C r)).w B *
                  (if y ∈ B.1 then 1 else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hmem : y ∈ D.1
            · simp only [if_pos hmem]
              rw [htarget y]
              apply Finset.sum_congr rfl
              intro B hB
              rw [hDirectU C W (R.groupOf C r) B y hnot]
            · simp [hmem]
          _ = ∑ B, ∑ y, if y ∈ D.1 then
                (K.qtilde C pool W (R.groupOf C r)).w B *
                  (if y ∈ B.1 then 1 else 0) else 0 := by
            rw [Finset.sum_comm]
          _ = (K.qtilde C pool W (R.groupOf C r)).w D := by
            calc
              (∑ B, ∑ y, if y ∈ D.1 then
                  (K.qtilde C pool W (R.groupOf C r)).w B *
                    (if y ∈ B.1 then 1 else 0) else 0) =
                  ∑ B, if B = D then (K.qtilde C pool W (R.groupOf C r)).w B else 0 := by
                apply Finset.sum_congr rfl
                intro B hB
                by_cases hBD : B = D
                · subst B
                  obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.mp (hBinSingleton C hnot D)
                  simp [hy₀]
                · have hdis : Disjoint B.1 D.1 :=
                    (PT.tiling.P (H.geom.cellPatch C)).bins.disjoint B.2 D.2 (by
                      intro hsets
                      apply hBD
                      exact Subtype.ext hsets)
                  simp only [if_neg hBD]
                  apply Finset.sum_eq_zero
                  intro y hy
                  by_cases hmemD : y ∈ D.1
                  · have hnotB : y ∉ B.1 := fun hmemB =>
                      (Finset.disjoint_left.mp hdis) hmemB hmemD
                    simp [hmemD, hnotB]
                  · simp [hmemD]
              _ = (K.qtilde C pool W (R.groupOf C r)).w D := by simp
      simpa only [FinLaw.pr] using hmassRaw
    exact hmass
  let binLaw : ∀ C (pool : CellPool H.geom C) (W : R.Hist C),
      FinLaw (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) := fun C pool W =>
    if hcl : PT.tiling.mode.isCluster then
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            calibratedBinLaw C pool W hcl htyp hload hw
          else productBinLaw C pool W
        else productBinLaw C pool W
      else productBinLaw C pool W
    else
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            directBinLaw C pool W htyp hload hw hcl
          else productBinLaw C pool W
        else productBinLaw C pool W
      else productBinLaw C pool W
  have hBinMarg : ∀ C pool W g b, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 →
      (binLaw C pool W).pr (fun a => a g = b) = (K.qtilde C pool W g).w b := by
    intro C pool W g b htyp hgate hw
    by_cases hcl : PT.tiling.mode.isCluster
    · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      have hbin := Classical.choose_spec (calibrated_group_bins hκ (K.binProblem C pool W)
        (hGroupInput C pool W hcl htyp hload hw))
      simpa [binLaw, hcl, htyp, hload, hw, calibratedBinLaw,
        CellRestrictedKernels.binProblem] using hbin.2 g b
    · have hnot : ¬ PT.tiling.mode.isCluster := hcl
      have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hDirectRoleData C pool W htyp hload hw hnot
      let L := Classical.choose hData
      let hQexists := (Classical.choose_spec hData).2
      let Qlab := directRoleLaw C pool W htyp hload hw hnot
      have hQspec : L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
        dsimp [Qlab, directRoleLaw, L, hData]
        exact Classical.choose_spec hQexists
      let tailLaw := FinLaw.pi fun g => K.qtilde C pool W g
      let sourceLaw := FinLaw.bind Qlab (fun _ => tailLaw)
      let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
          (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
        groupBinReadout C pool ω.1 ω.2
      have hBinLaw : binLaw C pool W = FinLaw.map sourceLaw readout := by
        simp [binLaw, hnot, htyp, hload, hw, directBinLaw, sourceLaw, readout,
          tailLaw, productBinLaw, directRoleLaw, Qlab, hData]
      have hMapped : (binLaw C pool W).pr (fun a => a g = b) =
          sourceLaw.pr (fun ω => readout ω g = b) := by
        rw [hBinLaw]
        exact Lane_q_s16_prod2.finLaw_map_pr sourceLaw readout (fun a => a g = b)
      by_cases hr : ∃ r : OddCellRole H.geom C, R.groupOf C r = g
      · let r := Classical.choose hr
        have hrEq : R.groupOf C r = g := Classical.choose_spec hr
        have hchoose : Classical.choose hr = r := by
          apply hDirectGroupInj C hnot
          exact (Classical.choose_spec hr).trans hrEq.symm
        have hread (ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C))) :
            readout ω g = binOfLabel C pool (ω.1 r) := by
          dsimp [readout, groupBinReadout]
          rw [dif_pos hr, hchoose]
        have hsource : sourceLaw.pr (fun ω => readout ω g = b) =
            (K.qtilde C pool W g).w b := by
          calc
            sourceLaw.pr (fun ω => readout ω g = b) =
                sourceLaw.pr (fun ω => binOfLabel C pool (ω.1 r) = b) := by
              apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
              intro ω _
              rw [hread ω]
            _ = Qlab.pr (fun ys => binOfLabel C pool (ys r) = b) := by
              simpa [sourceLaw] using
                (Lane_q_s16_prod2.finLaw_bind_pr_fst Qlab (fun _ => tailLaw)
                  (fun ys => binOfLabel C pool (ys r) = b))
            _ = (FinLaw.map (L.problem.target r) (binOfLabel C pool)).pr
                (fun D => D = b) :=
              Lane_q_s16_prod2.finLaw_pr_map_coordinate Qlab
                (fun r => L.problem.target r) hQspec.2 r (binOfLabel C pool)
                (fun D => D = b)
            _ = (K.qtilde C pool W g).w b := by
              rw [hDirectTargetMap C pool W (fun _ => defaultBin C) L r hnot b]
              rw [hrEq]
        exact hMapped.trans hsource
      · have hread (ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C))) :
            readout ω g = ω.2 g := by
          dsimp [readout, groupBinReadout]
          rw [dif_neg hr]
        have hTailMarg : tailLaw.pr (fun a => a g = b) = (K.qtilde C pool W g).w b := by
          dsimp [tailLaw]
          exact Lane_q_s16_prod2.finLaw_pi_coordinate_mass
            (fun g => K.qtilde C pool W g) g b
        have hsource : sourceLaw.pr (fun ω => readout ω g = b) =
            (K.qtilde C pool W g).w b := by
          calc
            sourceLaw.pr (fun ω => readout ω g = b) =
                sourceLaw.pr (fun ω => ω.2 g = b) := by
              apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
              intro ω _
              rw [hread ω]
            _ = tailLaw.pr (fun a => a g = b) := by
              simpa [sourceLaw] using
                (Lane_q_s16_prod2.finLaw_bind_pr_snd Qlab tailLaw (fun a => a g = b))
            _ = (K.qtilde C pool W g).w b := hTailMarg
        exact hMapped.trans hsource
  have hBinFeasible : ∀ C pool W, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → PT.tiling.mode.isCluster →
      (K.binProblem C pool W).feasible (binLaw C pool W) := by
    intro C pool W htyp hgate hw hcl
    have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
    have hbin := Classical.choose_spec (calibrated_group_bins hκ (K.binProblem C pool W)
      (hGroupInput C pool W hcl htyp hload hw))
    simpa [binLaw, hcl, htyp, hload, hw, calibratedBinLaw] using hbin.1
  have hClusterRoleData (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C))
      (hcl : PT.tiling.mode.isCluster) (htyp : (Ds.diagnostic C).typical pool)
      (hload : (Ds.diagnostic C).loadGate pool W) (hw : (R.history C).w W ≠ 0)
      (ha : (binLaw C pool W).w a ≠ 0) :
      ∃ L : CellRoleProblem K C pool W a, RoleLabelHypotheses hκ L.problem ∧
        ∃ Qlab : FinLaw (OddCellRole H.geom C → Fin (T.S.N k)),
          L.problem.feasible Qlab ∧
          ∀ r y, Qlab.pr (fun ys => ys r = y) = (L.problem.target r).w y := by
    have hgateMem : W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hload⟩
    have hbinFeas := hBinFeasible C pool W htyp hgateMem hw hcl
    have hsafe : (K.binProblem C pool W).safe a := hbinFeas.1 a ha
    have hwa : 0 < (binLaw C pool W).w a :=
      lt_of_le_of_ne ((binLaw C pool W).nonneg a) (Ne.symm ha)
    have hqpos : ∀ g, (K.qtilde C pool W g).w (a g) ≠ 0 := by
      intro g
      have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr (binLaw C pool W)
        (fun a' => a' g = a g) a rfl
      have hMarg := hBinMarg C pool W g (a g) htyp hgateMem hw
      have hPos : 0 < (K.qtilde C pool W g).w (a g) := by
        rw [← hMarg]
        exact lt_of_lt_of_le hwa hAtom
      exact ne_of_gt hPos
    obtain ⟨L, hL⟩ := hRoleInput C pool W a htyp hload hw (fun _ => hsafe) (fun _ => hqpos)
    obtain ⟨Qlab, hFeasible, hMarg⟩ := calibrated_role_labels hκ L.problem hL
    exact ⟨L, hL, Qlab, hFeasible, hMarg⟩
  let productLabelLaw (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C)
      (a : R.Group C → Bin PT.tiling (H.geom.cellPatch C)) :
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) :=
    FinLaw.pi fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r))
  let labelLaw : ∀ C (pool : CellPool H.geom C) (W : R.Hist C),
      (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) →
      FinLaw (OddCellRole H.geom C → Fin (T.S.N k)) := fun C pool W a =>
    if hcl : PT.tiling.mode.isCluster then
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then
            if ha : (binLaw C pool W).w a ≠ 0 then
              Classical.choose ((Classical.choose_spec
                (hClusterRoleData C pool W a hcl htyp hload hw ha)).2)
            else productLabelLaw C pool W a
          else productLabelLaw C pool W a
        else productLabelLaw C pool W a
      else productLabelLaw C pool W a
    else
      if htyp : (Ds.diagnostic C).typical pool then
        if hload : (Ds.diagnostic C).loadGate pool W then
          if hw : (R.history C).w W ≠ 0 then directLabelLaw C a hcl
          else productLabelLaw C pool W a
        else productLabelLaw C pool W a
      else productLabelLaw C pool W a
  have hLabelMarg : ∀ C pool W a r y, (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → (binLaw C pool W).w a ≠ 0 →
      (labelLaw C pool W a).pr (fun ys => ys r = y) =
        (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y := by
    intro C pool W a r y htyp hgate hw ha
    by_cases hcl : PT.tiling.mode.isCluster
    · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
      have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
        simp [labelLaw, hcl, htyp, hload, hw, ha]
      rw [hLaw]
      have hQ := Classical.choose_spec ((Classical.choose_spec hData).2)
      have hMarg := hQ.2 r y
      have hTarget : ((Classical.choose hData).problem.target r).w y =
          (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y := by
        simpa [hcl] using (Classical.choose hData).targets_eq r y
      rw [hTarget] at hMarg
      exact hMarg
    · letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
      have hU : (R.U C W (R.groupOf C r) (a (R.groupOf C r))).w y =
          (if y ∈ (a (R.groupOf C r)).1 then 1 else 0) := by
        rcases hSource with ⟨hmode, _hUniform, _hCells⟩ | ⟨_hnot, hCells⟩
        · have hcluster : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
          exact False.elim (hcl hcluster)
        · rcases hCells C with ⟨_hInjective, _hValues, _hPass, _hRaw, _hTrim, hU, _hPrior⟩
          exact hU W (R.groupOf C r) (a (R.groupOf C r)) y
      let D := a (R.groupOf C r)
      have hcard := hBinSingleton C hcl D
      have hBinSet : D.1 = {binLabel C hcl D} :=
        Classical.choose_spec (Finset.card_eq_one.mp hcard)
      have hLaw : labelLaw C pool W a = directLabelLaw C a hcl := by
        simp [labelLaw, hcl, htyp, (Finset.mem_filter.mp hgate).2, hw]
      rw [hLaw]
      dsimp [directLabelLaw]
      rw [Lane_q_s16_prod2.finLaw_dirac_pr, hU]
      simp [D, hBinSet, eq_comm]
  have hDirectJoint : ∀ C (pool : CellPool H.geom C) (W : R.Hist C)
      (Sset : Finset (OddCellRole H.geom C)) (ys : OddCellRole H.geom C → Fin (T.S.N k)),
      (Ds.diagnostic C).typical pool →
      W ∈ Finset.univ.filter ((Ds.diagnostic C).loadGate pool) →
      (R.history C).w W ≠ 0 → ¬ PT.tiling.mode.isCluster →
      (Sset.card : ℝ) ≤ Real.rpow (H.geom.nslot C : ℝ) 0.025 →
      (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr
        (fun ω => ∀ r ∈ Sset, ω.2 r = ys r) ≤
      Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
        ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w (ys r)) := by
    intro C pool W Sset ys htyp hgate hw hnot hsize
    have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
    let hData := hDirectRoleData C pool W htyp hload hw hnot
    let L := Classical.choose hData
    let hQexists := (Classical.choose_spec hData).2
    let Qlab := directRoleLaw C pool W htyp hload hw hnot
    have hQspec : L.problem.feasible Qlab ∧
        ∀ r y, Qlab.pr (fun z => z r = y) = (L.problem.target r).w y := by
      dsimp [Qlab, directRoleLaw, L, hData]
      exact Classical.choose_spec hQexists
    have hRoleLaw : directRoleLaw C pool W htyp hload hw hnot = Qlab := rfl
    let sourceLaw := FinLaw.bind Qlab (fun _ => FinLaw.pi fun g => K.qtilde C pool W g)
    let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
        (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
      groupBinReadout C pool ω.1 ω.2
    let decode := fun a : R.Group C → Bin PT.tiling (H.geom.cellPatch C) =>
      fun r => binLabel C hnot (a (R.groupOf C r))
    let cylinder := fun z : OddCellRole H.geom C → Fin (T.S.N k) =>
      ∀ r ∈ Sset, z r = ys r
    let event : ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
        (OddCellRole H.geom C → Fin (T.S.N k))) → Prop :=
      fun ω => ∀ r ∈ Sset, ω.2 r = ys r
    have hBinLaw : binLaw C pool W = FinLaw.map sourceLaw readout := by
      simp [binLaw, hnot, htyp, hload, hw, directBinLaw, sourceLaw, readout,
        productBinLaw, hRoleLaw]
    have hLabelLaw : labelLaw C pool W = fun a => FinLaw.dirac (decode a) := by
      funext a
      simp [labelLaw, hnot, htyp, hload, hw, directLabelLaw, decode]
    have hStageEvent :
        (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr event =
          sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) := by
      rw [hBinLaw, hLabelLaw]
      letI : DecidableEq (OddCellRole H.geom C → Fin (T.S.N k)) := Fintype.decidablePiFintype
      exact Lane_q_s16_prod2.finLaw_map_bind_dirac_pr sourceLaw readout decode event
    have hDecodeSupport :
        sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) =
          sourceLaw.pr (fun ω => cylinder ω.1) := by
      apply Lane_q_s16_prod2.finLaw_pr_congr_of_supported
      intro ω hω
      have hQpos : Qlab.w ω.1 ≠ 0 := by
        intro hzero
        apply hω
        simp [sourceLaw, FinLaw.bind, hzero]
      constructor
      · intro hEvent r hr
        have hdec := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
          Qlab hQspec.2 hnot ω.1 hQpos r
        exact hdec.symm.trans (hEvent r hr)
      · intro hCylinder r hr
        have hdec := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
          Qlab hQspec.2 hnot ω.1 hQpos r
        exact hdec.trans (hCylinder r hr)
    have hSourceCylinder : sourceLaw.pr (fun ω => cylinder ω.1) = Qlab.pr cylinder := by
      dsimp [sourceLaw]
      rw [Lane_q_s16_prod2.finLaw_bind_pr]
      simp_rw [Lane_q_s16_prod2.finLaw_pr_const]
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hcyl : cylinder z <;> simp [hcyl]
    have hQueries : L.problem.queries Sset := by
      simpa [RoleLabelProblem.queries, L.regime_eq, L.scale_eq, hnot] using hsize
    have hQbound := hQspec.1.2 Sset ys hQueries
    have hTargets : ∀ r y, (L.problem.target r).w y =
        ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w y := by
      intro r y
      simpa [hnot] using L.targets_eq r y
    have hBound : Qlab.pr cylinder ≤
        Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := by
      change Qlab.pr cylinder ≤ Real.exp (L.problem.rate * (Sset.card : ℝ)) *
        ∏ r ∈ Sset, (L.problem.target r).w (ys r) at hQbound
      have hrate : L.problem.rate = Real.rpow (H.geom.nslot C : ℝ) (-0.04 : ℝ) := by
        simp [RoleLabelProblem.rate, L.regime_eq, L.scale_eq, hnot]
      rw [hrate] at hQbound
      have hprod : ∏ r ∈ Sset, (L.problem.target r).w (ys r) =
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact hTargets r (ys r)
      rw [hprod] at hQbound
      exact hQbound
    calc
      (FinLaw.bind (binLaw C pool W) (labelLaw C pool W)).pr event =
          sourceLaw.pr (fun ω => event (readout ω, decode (readout ω))) := hStageEvent
      _ = sourceLaw.pr (fun ω => cylinder ω.1) := hDecodeSupport
      _ = Qlab.pr cylinder := hSourceCylinder
      _ ≤ Real.exp (Real.rpow (H.geom.nslot C : ℝ) (-0.04) * Sset.card) *
          ∏ r ∈ Sset, (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
            (R.U C W (R.groupOf C r) b).w (ys r)) := hBound
  refine ⟨{
    typical := fun C pool => (Ds.diagnostic C).typical pool
    gate := fun C pool => Finset.univ.filter ((Ds.diagnostic C).loadGate pool)
    gate_pos := ?_
    binLaw := binLaw
    bin_marginals := hBinMarg
    bin_feasible := hBinFeasible
    labelLaw := labelLaw
    label_marginals := hLabelMarg
    label_injective := by
      intro C pool W a ys htyp hgate hw ha hys
      by_cases hcl : PT.tiling.mode.isCluster
      · have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
        let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
        have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
          simp [labelLaw, hcl, htyp, hload, hw, ha]
        rw [hLaw] at hys
        have hSafe := (Classical.choose_spec ((Classical.choose_spec hData).2)).1.1 ys hys
        exact hSafe.1
      · have hnot := hcl
        have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
        let hData := hDirectRoleData C pool W htyp hload hw hnot
        let L := Classical.choose hData
        let hQexists := (Classical.choose_spec hData).2
        let Qlab := directRoleLaw C pool W htyp hload hw hnot
        have hQspec := Classical.choose_spec hQexists
        have hMarg : ∀ r y, Qlab.pr (fun z => z r = y) = (L.problem.target r).w y := by
          simpa [Qlab, directRoleLaw, L, hData] using hQspec.2
        let sourceLaw := FinLaw.bind Qlab (fun _ => FinLaw.pi fun g => K.qtilde C pool W g)
        let readout := fun ω : (OddCellRole H.geom C → Fin (T.S.N k)) ×
            (R.Group C → Bin PT.tiling (H.geom.cellPatch C)) =>
          groupBinReadout C pool ω.1 ω.2
        have hBinEq : binLaw C pool W = FinLaw.map sourceLaw readout := by
          simp [binLaw, hnot, htyp, (Finset.mem_filter.mp hgate).2, hw,
            directBinLaw, sourceLaw, readout, productBinLaw, directRoleLaw, Qlab, hData]
        have hpre : ∃ ω, readout ω = a ∧ sourceLaw.w ω ≠ 0 := by
          have ha' : (FinLaw.map sourceLaw readout).w a ≠ 0 := by
            rw [← hBinEq]
            exact ha
          exact Lane_q_s16_prod2.finLaw_map_nonzero_preimage sourceLaw readout a ha'
        obtain ⟨ω, hωa, hωpos⟩ := hpre
        have hQpos : Qlab.w ω.1 ≠ 0 := by
          intro hz
          apply hωpos
          simp [sourceLaw, FinLaw.bind, hz]
        have hysEq : ys = fun r => binLabel C hnot (a (R.groupOf C r)) := by
          by_contra hneq
          have hzero : (labelLaw C pool W a).w ys = 0 := by
            simp [labelLaw, hnot, htyp, (Finset.mem_filter.mp hgate).2, hw,
              directLabelLaw, FinLaw.dirac, hneq]
          exact hys hzero
        have hinj : Function.Injective ω.1 :=
          ((hQspec.1.1 ω.1 hQpos).1)
        have hysToQ (r : OddCellRole H.geom C) : ys r = ω.1 r := by
          have hdecode := hDirectDecode C pool W (fun _ => defaultBin C) L ω.2
            Qlab hMarg hnot ω.1 hQpos r
          have hread : groupBinReadout C pool ω.1 ω.2 = a := by
            simpa [readout] using hωa
          have hdecodeA : binLabel C hnot (a (R.groupOf C r)) = ω.1 r := by
            calc
              binLabel C hnot (a (R.groupOf C r)) =
                  binLabel C hnot (groupBinReadout C pool ω.1 ω.2 (R.groupOf C r)) := by
                rw [hread]
              _ = ω.1 r := hdecode
          have hy := congrFun hysEq r
          exact hy.trans hdecodeA
        intro r r' hrr'
        apply hinj
        calc
          ω.1 r = ys r := (hysToQ r).symm
          _ = ys r' := hrr'
          _ = ω.1 r' := hysToQ r'
    cluster_label_feasible := by
      intro C pool W a htyp hgate hw ha hcl
      have hload : (Ds.diagnostic C).loadGate pool W := (Finset.mem_filter.mp hgate).2
      let hData := hClusterRoleData C pool W a hcl htyp hload hw ha
      refine ⟨Classical.choose hData, ?_⟩
      have hLaw : labelLaw C pool W a = Classical.choose ((Classical.choose_spec hData).2) := by
        simp [labelLaw, hcl, htyp, hload, hw, ha]
      rw [hLaw]
      exact (Classical.choose_spec ((Classical.choose_spec hData).2)).1
    direct_joint := hDirectJoint
  }, ?_, ?_⟩
  · intro C pool ht
    obtain ⟨hgate, _⟩ :=
      ((history_load_gate_concentration (Ds.diagnostic C) (Ds.load C) pool ht).2
        (fun _ => 0) (by intro; norm_num))
    rw [(Ds.linked C).history_eq pool] at hgate
    exact hgate
  · intro C pool
    rfl
  · intro C pool
    rfl

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
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  obtain ⟨nCost, hCost⟩ := Lane_q_s16_prod2.exp_denominator_slack_cutoff
    κ.cperm hκ.cperm_rng.1
  refine ⟨max (max (max nG nR) 2) (max nCost 8), ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S hSource hn hPerm hTypical hGate
  have hnBase : max (max nG nR) 2 ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hn
  have hn0 : max nG nR ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hnBase
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left nG nR).trans hn0
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right nG nR).trans hn0
  have hn2 : 2 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnBase
  have hnCostBase : max nCost 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hnCost : nCost ≤ T.S.n k := (Nat.le_max_left _ _).trans hnCostBase
  have hn8 : 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnCostBase
  have hFallback : ∀ C : H.geom.Cell,
      ∃ ys : OddCellRole H.geom C → Fin (T.S.N k), Function.Injective ys := by
    intro C
    let D := Ds.diagnostic C
    have hPoolHyp : PoolConcentrationHypotheses D := Ds.concentration C
    have hBad := pool_typicality_concentration_after_permission D hPoolHyp
    have hSmall : D.poolLaw.pr (fun pool => ¬ D.typical pool) < 1 := by
      calc
        D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤
            Real.exp (-(T.S.n k : ℝ) ^ c0) / 2 := hBad.1
        _ < 1 := by
          have hc0 : c0 = 1 / 2 := Ds.exponent_half
          rw [hc0]
          have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
          have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
          have hexp : Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) < 1 :=
            Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
          have hexppos : 0 < Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) := Real.exp_pos _
          linarith
    have hTypicalProb : 0 < D.poolLaw.pr (fun pool => D.typical pool) := by
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl D.poolLaw (fun pool => D.typical pool)
      linarith
    obtain ⟨pool, hDtyp, hPoolW⟩ :=
      Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom D.poolLaw
        (fun pool => D.typical pool) hTypicalProb
    have hStyp : S.typical C pool := (hTypical C pool).2 hDtyp
    have hGatePos : 0 < ∑ W ∈ S.gate C pool, (R.history C).w W := S.gate_pos C pool hStyp
    obtain ⟨W, hWgate, hWpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := S.gate C pool)
        (f := fun W => (R.history C).w W)
        (by intro W hW; exact (R.history C).nonneg W)).mp hGatePos
    have hBinProb : 0 < (S.binLaw C pool W).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨a, _haTrue, ha⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.binLaw C pool W) (fun _ => True) hBinProb
    have hLabelProb : 0 < (S.labelLaw C pool W a).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨ys, _hysTrue, hys⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.labelLaw C pool W a) (fun _ => True) hLabelProb
    exact ⟨ys, S.label_injective C pool W a ys hStyp hWgate (ne_of_gt hWpos) ha hys⟩
  let RawState : H.geom.Cell → Type := fun C =>
    R.Hist C × ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
      (OddCellRole H.geom C → Fin (T.S.N k)))
  let encode := fun (C : H.geom.Cell) (z : RawState C) =>
    if hz : Function.Injective z.2.2 then some z else none
  let defaultLabels : ∀ C : H.geom.Cell, OddCellRole H.geom C → Fin (T.S.N k) :=
    fun C => Classical.choose (hFallback C)
  let gatedHistory : ∀ C : H.geom.Cell, CellPool H.geom C → FinLaw (R.Hist C) :=
    fun C pool => if ht : S.typical C pool then
      FinLaw.cond (R.history C) (S.gate C pool) (S.gate_pos C pool ht) else R.history C
  have hGatedSupport {C : H.geom.Cell} (pool : CellPool H.geom C) (W : R.Hist C)
      (ht : S.typical C pool) (hW : (gatedHistory C pool).w W ≠ 0) :
      W ∈ S.gate C pool ∧ (R.history C).w W ≠ 0 := by
    by_cases hmem : W ∈ S.gate C pool
    · refine ⟨hmem, ?_⟩
      by_contra hzero
      have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem, hzero]
      exact hW hz
    · have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem]
      exact False.elim (hW hz)
  let F : FreshCell H.geom := {
    State := fun C => Option (RawState C)
    fresh := fun C pool =>
      if htyp : S.typical C pool then
        FinLaw.map (FinLaw.bind (gatedHistory C pool)
          (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
          (encode C)
      else FinLaw.dirac none
    fallback := fun _ => none
    label := fun C s b =>
      if hb : H.geom.cellOf b = C ∧ ¬ IsEvenRole b then
        match s with
        | none => defaultLabels C ⟨b, hb⟩
        | some z => if hz : Function.Injective z.2.2 then
            z.2.2 ⟨b, hb⟩ else defaultLabels C ⟨b, hb⟩
      else ⟨0, T.S.N_pos k⟩
    prior := fun C s b y =>
      match s with
      | none => 0
      | some z => R.rawPrior C z.1 z.2.2 b y
    typical := S.typical
  }
  let δperm : ℝ := Real.exp (-(κ.cperm * (T.S.n k : ℝ)) / 2)
  let δgate : ℝ := Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ))
  let Cal : FreshLabelCalibration F := {
    Hist := R.Hist
    Group := R.Group
    groupOf := R.groupOf
    history := R.history
    gatedHistory := gatedHistory
    gate := S.gate
    gate_pos := S.gate_pos
    gated_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp only [gatedHistory, dif_pos ht]
    qin := R.qin
    U := R.U
    U_support := R.U_support
    permitted := fun C g => (Perm.table C).permitted g
    qtilde := K.qtilde
    qtilde_eq := by
      intro C pool W g D ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        have hpos : 0 < 1 - Real.exp (-c * (Perm.table C).n) := sub_pos.mpr hexp
        exact lt_of_lt_of_le hpos hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hzBoth : 0 < zBoth := by
        have hratio' : 0 < zBoth / zPerm := by rw [← hzImageEq]; exact hzImage
        have hmul := mul_pos hratio' hzPerm
        have heq : (zBoth / zPerm) * zPerm = zBoth := div_mul_cancel₀ _ (ne_of_gt hzPerm)
        rw [heq] at hmul
        exact hmul
      have hdenEq :
          (∑ D' ∈ (Perm.table C).permitted g ∩ Finset.image pool Finset.univ,
            (R.qin C W g).w D') = zBoth := by
        simp [zBoth, E, I, Finset.inter_comm]
      have hqtilde := K.qtilde_eq C pool W g D hW (ne_of_gt hzImage)
      rw [hqtilde, hqbar D]
      have hsumQbar : (∑ D' ∈ I, (K.qbar C W g).w D') = zImage := rfl
      rw [hsumQbar, hzImageEq, hdenEq]
      by_cases hDperm : D ∈ E <;> by_cases hDimage : D ∈ I
      · simp [E, I, hDperm, hDimage]
        field_simp [ne_of_gt hzPerm, ne_of_gt hzBoth]
      · have hPermD : D ∈ (Perm.table C).permitted g := by simpa [E] using hDperm
        have hNoPre : ¬ ∃ a, pool a = D := by
          intro hpre
          obtain ⟨a, ha⟩ := hpre
          apply hDimage
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
        simp [hDimage, hNoPre, hPermD]
      · simp [E, I, hDperm, hDimage]
      · simp [E, I, hDperm, hDimage]
    binSampler := S.binLaw
    labelSampler := S.labelLaw
    bin_marginals := by
      intro C pool W g D ht hW
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.bin_marginals C pool W g D ht hGateW hHistW
    label_marginals := by
      intro C pool W a r y ht hW ha
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.label_marginals C pool W a r y ht hGateW hHistW ha
    encode := encode
    fresh_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp [F, gatedHistory, ht, encode]
    label_eq := by
      intro C pool W a ys r ht hW ha hys
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hrole : H.geom.cellOf r.1 = C ∧ ¬ IsEvenRole r.1 := r.2
      simp [F, encode, hinj, hrole]
    raw_profile := by
      intro C r y
      rcases hSource with ⟨hmode, _hUniform, hSourceCell⟩ | _hDirect
      · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
          _hgroupOf, hqraw, hpretrim, hU, _hprior⟩ := hSourceCell C
        let gRaw := R.groupOf C r
        let sourcePair := groups.symm gRaw
        let s := sourcePair.1
        let gSol := sourcePair.2
        have hgroups : groups (s, gSol) = gRaw := by
          dsimp [s, gSol, sourcePair]
          exact groups.apply_symm_apply gRaw
        let rowRaw : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W gRaw).w D * (R.U C W gRaw D).w y
        let rowSol : (∀ t, Ssol.Val t) → ℝ := fun W =>
          ∑ D, Ssol.qin W gSol D * Ssol.U gSol W D y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            rowRaw W = rowSol (records s (W s)) := by
          intro W hW
          have hProd :
              (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            simpa [CellRawData.history, FinLaw.pi] using hW
          have hFactor : ∀ t,
              (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t) ≠ 0 := by
            intro t hzero
            apply hProd
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hcond := hFactor t
            have hpass : W t ∈ R.slicePass C t := by
              by_contra hnot
              apply hcond
              simp [FinLaw.cond, hnot]
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              by_contra hzero
              apply hcond
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          have hqin : ∀ D,
              (R.qin C W gRaw).w D = Ssol.qin (records s (W s)) gSol D := by
            intro D
            rw [← hgroups]
            rw [R.qin_eq C W (groups (s, gSol)) D hLocalInput]
            simp only [SliceSolver.qin, hpretrim W s gSol, hqraw W s gSol]
            by_cases hD : D ∈ Ssol.pretrimBins (records s (W s)) gSol <;> simp [hD]
          have hUeq : ∀ D,
              (R.U C W gRaw D).w y = Ssol.U gSol (records s (W s)) D y := by
            intro D
            rw [← hgroups]
            exact hU W s gSol D y
          dsimp [rowRaw, rowSol]
          apply Finset.sum_congr rfl
          intro D hD
          rw [hqin D, hUeq D]
        have hsupportAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) rowRaw (fun W => rowSol (records s (W s))) hrow
        have hcoordAvg :
            (R.history C).E (fun W => rowSol (records s (W s))) =
              (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := by
          simpa [CellRawData.history] using
            (Lane_q_s16_prod2.finLaw_pi_E_coordinate
              (fun t => FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)) s (fun z => rowSol (records s z)))
        have hPassMap : ∀ z,
            ((records s).symm z ∈ R.slicePass C s) ↔ Ssol.AllGood z := by
          intro z
          simpa using hslicePass s ((records s).symm z)
        have hsliceMap : R.sliceLaw C s =
            FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm := hsliceLaw s
        have hden :
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
              (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          calc
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
                (R.sliceLaw C s).pr (fun z => z ∈ R.slicePass C s) :=
              (Lane_q_s16_prod2.finLaw_pr_finset (R.sliceLaw C s)
                (R.slicePass C s)).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).pr
                  (fun z => z ∈ R.slicePass C s) := by rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).pr
                  (fun z => (records s).symm z ∈ R.slicePass C s) :=
              Lane_q_s16_prod2.finLaw_map_pr _ _ _
            _ = (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
              unfold FinLaw.pr
              apply Finset.sum_congr rfl
              intro z hz
              simp [hPassMap z]
        have hrecPos : 0 < (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          rw [← hden]
          exact R.slice_pos C s
        have hnum :
            (∑ z ∈ R.slicePass C s,
              (R.sliceLaw C s).w z * rowSol (records s z)) =
              (Ssol.recLaw PT.parameter).E
                (fun z => if Ssol.AllGood z then rowSol z else 0) := by
          let fVal : R.Value C s → ℝ := fun z =>
            if z ∈ R.slicePass C s then rowSol (records s z) else 0
          calc
            (∑ z ∈ R.slicePass C s,
                (R.sliceLaw C s).w z * rowSol (records s z)) =
              (R.sliceLaw C s).E fVal :=
                (Lane_q_s16_prod2.finLaw_E_finset (R.sliceLaw C s)
                  (R.slicePass C s) (fun z => rowSol (records s z))).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).E fVal := by
              rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => fVal ((records s).symm z)) :=
              Lane_q_s16_prod2.finLaw_map_E _ _ _
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => if Ssol.AllGood z then rowSol z else 0) := by
              congr 1
              funext z
              simp [fVal, hPassMap z]
        have hcondAvg :
            (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
              (R.slice_pos C s)).E (fun z => rowSol (records s z)) =
                Ssol.lowOut PT.parameter gSol y := by
          rw [Lane_q_s16_prod2.finLaw_cond_E]
          rw [hnum, hden]
          simp [SliceSolver.lowOut, rowSol, FinLaw.E]
        have hpi := Q.profiled_valid.low_profile hmode
          (H.geom.cellPatch C) Ssol hsolver gSol y
        calc
          (R.history C).E rowRaw =
              (R.history C).E (fun W => rowSol (records s (W s))) := hsupportAvg
          _ = (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := hcoordAvg
          _ = Ssol.lowOut PT.parameter gSol y := hcondAvg
          _ = (PT.π (H.geom.cellPatch C)).w y := hpi.symm
      · obtain ⟨hnot, hDirectCells⟩ := _hDirect
        let i := H.geom.cellPatch C
        let Y := (PT.tiling.P i).Y
        have hY : Y.Nonempty := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
        have hd : (PT.tiling.P i).d = 1 := by
          cases hmode' : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode'
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode') i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode']; simp [Mode.isCluster]
              exact (hnot hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode'] at hlow
              have hf : False := by simpa [Mode.isLow] using hlow
              exact hf.elim
        obtain ⟨hGroupInjective, _hValues, hSlicePass, hqrawDirect,
          hpretrimDirect, hUDirect, _hPrior⟩ := hDirectCells C
        have hBinSingleton : ∀ D : Bin PT.tiling i, D.1.card = 1 := by
          intro D
          calc
            D.1.card = (PT.tiling.P i).d :=
              Q.profiled_valid.tiling_valid.bins_card i D.1 D.2
            _ = 1 := hd
        let labelOfBin : Bin PT.tiling i → {z : Fin (T.S.N k) // z ∈ Y} := fun D => by
          let z : Fin (T.S.N k) := Classical.choose (Finset.card_eq_one.mp (hBinSingleton D))
          have hset : D.1 = {z} := Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
          have hmemSingleton : z ∈ ({z} : Finset (Fin (T.S.N k))) := Finset.mem_singleton_self z
          have hmem : z ∈ D.1 := by simpa [hset] using hmemSingleton
          exact ⟨z, (PT.tiling.P i).bins.le D.2 hmem⟩
        have hBinSet (D : Bin PT.tiling i) : D.1 = { (labelOfBin D).1 } :=
          Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
        have hlabelInj : Function.Injective labelOfBin := by
          intro D D' hEq
          apply Subtype.ext
          have hval := congrArg Subtype.val hEq
          rw [hBinSet D, hBinSet D']
          simp [hval]
        have hlabelSurj : Function.Surjective labelOfBin := by
          intro z
          have hzCover : z.1 ∈ (PT.tiling.P i).bins.parts.biUnion id := by
            rw [(PT.tiling.P i).bins.biUnion_parts]
            exact z.2
          obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hzCover
          let D : Bin PT.tiling i := ⟨B, hB⟩
          refine ⟨D, ?_⟩
          apply Subtype.ext
          have hzSingle : z.1 ∈ ({ (labelOfBin D).1 } : Finset (Fin (T.S.N k))) := by
            rw [← hBinSet D]
            exact hzB
          exact (Finset.mem_singleton.mp hzSingle).symm
        let binEquiv : Bin PT.tiling i ≃ {z : Fin (T.S.N k) // z ∈ Y} :=
          Equiv.ofBijective labelOfBin ⟨hlabelInj, hlabelSurj⟩
        have hBinCard : (Fintype.card (Bin PT.tiling i) : ℝ) = (Y.card : ℝ) := by
          have hcard : Fintype.card (Bin PT.tiling i) = Y.card := by
            calc
              Fintype.card (Bin PT.tiling i) =
                  Fintype.card {z : Fin (T.S.N k) // z ∈ Y} := Fintype.card_congr binEquiv
              _ = Y.card := by simp [Y]
          exact_mod_cast hcard
        have hlabelCount :
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
              if y ∈ Y then 1 else 0 := by
          calc
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
                ∑ D : Bin PT.tiling i, if y = (labelOfBin D).1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro D hD
              rw [hBinSet D]
              simp [eq_comm]
            _ = ∑ z : {z : Fin (T.S.N k) // z ∈ Y},
                  if y = z.1 then (1 : ℝ) else 0 := by
              exact Fintype.sum_equiv binEquiv
                (fun D => if y = (labelOfBin D).1 then (1 : ℝ) else 0)
                (fun z => if y = z.1 then (1 : ℝ) else 0)
                (by intro D; rfl)
            _ = if y ∈ Y then 1 else 0 := by
              by_cases hy : y ∈ Y
              · simp only [if_pos hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = {⟨y, hy⟩} := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro hz
                    exact Finset.mem_singleton.mpr (Subtype.ext hz.symm)
                  · intro hz
                    exact (congrArg Subtype.val (Finset.mem_singleton.mp hz)).symm
                rw [← Finset.sum_filter, hfilter]
                simp
              · simp only [if_neg hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = ∅ := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro heq
                    exact False.elim (hy (heq.symm ▸ z.2))
                  · intro hfalse
                    cases hfalse
                rw [← Finset.sum_filter, hfilter]
                simp
        have hRawDirect (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
            ∀ D, (R.qin C W (R.groupOf C r)).w D =
              (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ := by
          have hHistoryPos : ∀ t,
              ((FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            intro t hzero
            apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hHistoryPos t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          intro D
          rw [R.qin_eq C W (R.groupOf C r) D hLocalInput]
          rw [hpretrimDirect W (R.groupOf C r)]
          have hsum :
              (∑ D' ∈ (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))),
                (R.qraw C W (R.groupOf C r)).w D') = 1 := by
            simpa using (R.qraw C W (R.groupOf C r)).sum_one
          rw [hsum, hqrawDirect W (R.groupOf C r) D]
          simp [i]
        have hpiLaw : PT.π i = Law.unifCore Y hY :=
          (Q.profiled_valid.law_uniform_direct.resolve_left hnot) i
        rw [hpiLaw]
        let row : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W (R.groupOf C r)).w D * (R.U C W (R.groupOf C r) D).w y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            row W = (Law.unifCore Y hY).w y := by
          intro W hW
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            have hFactor : ∀ t,
                (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t) ≠ 0 := by
              intro t hz
              apply hprod
              exact Finset.prod_eq_zero (Finset.mem_univ t) hz
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hFactor t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          calc
            row W = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) := by
              dsimp [row]
              calc
                (∑ D : Bin PT.tiling (H.geom.cellPatch C), (R.qin C W (R.groupOf C r)).w D *
                    (R.U C W (R.groupOf C r) D).w y) =
                    ∑ D : Bin PT.tiling (H.geom.cellPatch C), (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (if y ∈ D.1 then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro (D : Bin PT.tiling (H.geom.cellPatch C)) hD
                  simpa [hUDirect W (R.groupOf C r) D y] using
                    congrArg (fun q : ℝ => q * (R.U C W (R.groupOf C r) D).w y)
                      (hRawDirect W hW D)
                _ = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (∑ D : Bin PT.tiling (H.geom.cellPatch C),
                        if y ∈ D.1 then (1 : ℝ) else 0) := by
                  rw [← Finset.mul_sum]
            _ = (Law.unifCore Y hY).w y := by
              rw [hlabelCount]
              by_cases hy : y ∈ Y <;> simp [Law.unifCore, hBinCard, hy]
        have hAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) row (fun _ => (Law.unifCore Y hY).w y) hrow
        calc
          (R.history C).E row = (R.history C).E (fun _ => (Law.unifCore Y hY).w y) := hAvg
          _ = (Law.unifCore Y hY).w y := by
            unfold FinLaw.E
            rw [← Finset.sum_mul, (R.history C).sum_one]
            ring
    δperm := δperm
    δgate := δgate
    perm_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
        have hc : 0 < κ.cperm := hκ.cperm_rng.1
        have hprod : 0 < κ.cperm * (T.S.n k : ℝ) := mul_pos hc hnreal
        have harg : -(κ.cperm * (T.S.n k : ℝ)) / 2 < 0 := by linarith
        exact Real.exp_lt_one_iff.mpr harg
    gate_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
        have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
    permission_mass := by
      intro C W g hW
      have h := Lane_q_s16_prod2.permission_mass_explicit_lower
        (Perm.table C) (R.qin C W) (hPerm C W hW) g
      simpa [Perm.rate_eq C, Perm.n_eq C, mul_assoc, mul_comm, mul_left_comm] using h
    pool_normalizer := by
      intro C pool W g ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        exact lt_of_lt_of_le (sub_pos.mpr hexp) hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hnormLower :
          theta * (1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hratioLower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          have habs := abs_le.mp hclose
          linarith
        have hmul := mul_le_mul_of_nonneg_left hratioLower (le_of_lt htheta)
        have heq : theta *
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          field_simp [ne_of_gt htheta]
        rw [heq] at hmul
        exact hmul
      calc
        theta * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          simpa using hnormLower
        _ = zBoth / zPerm := by
          rw [hnormEq]
          exact hzImageEq
        _ = (∑ D' ∈ ((Perm.table C).permitted g ∩ Finset.univ.image pool),
              (R.qin C W g).w D') /
              (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D') := rfl
    gate_mass := by
      intro C pool ht
      have htyp : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let D := Ds.diagnostic C
      have hBad := history_load_gate_concentration D (Ds.load C) pool htyp
      have hfail : (R.history C).pr (fun W => ¬ D.loadGate pool W) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [(Ds.linked C).history_eq pool] at hBad
        simpa [Ds.exponent_half] using hBad.1
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl (R.history C)
        (fun W => D.loadGate pool W)
      have hgateProb : (R.history C).pr (fun W => D.loadGate pool W) =
          ∑ W ∈ S.gate C pool, (R.history C).w W := by
        unfold FinLaw.pr
        rw [← Finset.sum_filter, hGate C pool]
      calc
        1 - Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) ≤
            (R.history C).pr (fun W => D.loadGate pool W) := by
          linarith [hcomp, hfail]
        _ = ∑ W ∈ S.gate C pool, (R.history C).w W := hgateProb
    slot_pos := by
      intro C
      simpa using (Ds.concentration C).slots_pos
    cost_budget := by
      have htails := hCost (T.S.n k) hnCost
      have hnreal : 1 ≤ (T.S.n k : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 8) hn8)
      have hq0 : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
      have hq1 : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnreal (by norm_num)
      simpa [δgate, δperm] using
        (Lane_q_s16_prod2.inverse_three_slacks hq0 hq1
          (by positivity) (by positivity) (by positivity)
          htails.1 htails.2.1 htails.2.2)
  }
  let Link : FreshConstructionLink S F Cal := {
    histories := fun _ => Equiv.refl _
    groups := fun _ => Equiv.refl _
    history_eq := by
      intro C
      change R.history C = FinLaw.map (R.history C) id
      exact (Lane_q_s16_prod2.finLaw_map_id (R.history C)).symm
    group_eq := by intro C r; rfl
    incoming_eq := by intro C W g; rfl
    U_eq := by intro C W g b; rfl
    permission_eq := by intro C g; rfl
    restricted_eq := by intro C pool W g; rfl
    typical_eq := by intro C pool; rfl
    gate_eq := by
      intro C pool
      change S.gate C pool = Finset.image id (S.gate C pool)
      ext W
      simp
    bin_eq := by
      intro C pool W
      change S.binLaw C pool W = FinLaw.map (S.binLaw C pool W) id
      exact (Lane_q_s16_prod2.finLaw_map_id (S.binLaw C pool W)).symm
    label_eq := by
      intro C pool W a
      rfl
    prior_eq := by
      intro C pool W a ys v ht hW ha hys hcell hEven
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hencode : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl, hencode]
      rfl
  }
  exact ⟨F, Cal, ⟨Link⟩⟩

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
  classical
  obtain ⟨nG, hG⟩ := successful_group_bin_hypotheses hκ
  obtain ⟨nR, hR⟩ := successful_role_label_hypotheses hκ
  obtain ⟨nCost, hCost⟩ := Lane_q_s16_prod2.exp_denominator_slack_cutoff
    κ.cperm hκ.cperm_rng.1
  refine ⟨max (max (max nG nR) 2) (max nCost 8), ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S hSource hn hPerm hTypical hGate
  have hnBase : max (max nG nR) 2 ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hn
  have hn0 : max nG nR ≤ T.S.n k :=
    (Nat.le_max_left _ _).trans hnBase
  have hnG : nG ≤ T.S.n k := (Nat.le_max_left nG nR).trans hn0
  have hnR : nR ≤ T.S.n k := (Nat.le_max_right nG nR).trans hn0
  have hn2 : 2 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnBase
  have hnCostBase : max nCost 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hn
  have hnCost : nCost ≤ T.S.n k := (Nat.le_max_left _ _).trans hnCostBase
  have hn8 : 8 ≤ T.S.n k := (Nat.le_max_right _ _).trans hnCostBase
  have hFallback : ∀ C : H.geom.Cell,
      ∃ ys : OddCellRole H.geom C → Fin (T.S.N k), Function.Injective ys := by
    intro C
    let D := Ds.diagnostic C
    have hPoolHyp : PoolConcentrationHypotheses D := Ds.concentration C
    have hBad := pool_typicality_concentration_after_permission D hPoolHyp
    have hSmall : D.poolLaw.pr (fun pool => ¬ D.typical pool) < 1 := by
      calc
        D.poolLaw.pr (fun pool => ¬ D.typical pool) ≤
            Real.exp (-(T.S.n k : ℝ) ^ c0) / 2 := hBad.1
        _ < 1 := by
          have hc0 : c0 = 1 / 2 := Ds.exponent_half
          rw [hc0]
          have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
          have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
          have hexp : Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) < 1 :=
            Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
          have hexppos : 0 < Real.exp (-((T.S.n k : ℝ) ^ (1 / 2 : ℝ))) := Real.exp_pos _
          linarith
    have hTypicalProb : 0 < D.poolLaw.pr (fun pool => D.typical pool) := by
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl D.poolLaw (fun pool => D.typical pool)
      linarith
    obtain ⟨pool, hDtyp, hPoolW⟩ :=
      Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom D.poolLaw
        (fun pool => D.typical pool) hTypicalProb
    have hStyp : S.typical C pool := (hTypical C pool).2 hDtyp
    have hGatePos : 0 < ∑ W ∈ S.gate C pool, (R.history C).w W := S.gate_pos C pool hStyp
    obtain ⟨W, hWgate, hWpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := S.gate C pool)
        (f := fun W => (R.history C).w W)
        (by intro W hW; exact (R.history C).nonneg W)).mp hGatePos
    have hBinProb : 0 < (S.binLaw C pool W).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨a, _haTrue, ha⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.binLaw C pool W) (fun _ => True) hBinProb
    have hLabelProb : 0 < (S.labelLaw C pool W a).pr (fun _ => True) := by
      simpa [Lane_q_s16_prod2.finLaw_pr_const] using
        (show (1 : ℝ) > 0 by norm_num)
    obtain ⟨ys, _hysTrue, hys⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
      (S.labelLaw C pool W a) (fun _ => True) hLabelProb
    exact ⟨ys, S.label_injective C pool W a ys hStyp hWgate (ne_of_gt hWpos) ha hys⟩
  let RawState : H.geom.Cell → Type := fun C =>
    R.Hist C × ((R.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
      (OddCellRole H.geom C → Fin (T.S.N k)))
  let encode := fun (C : H.geom.Cell) (z : RawState C) =>
    if hz : Function.Injective z.2.2 then some z else none
  let defaultLabels : ∀ C : H.geom.Cell, OddCellRole H.geom C → Fin (T.S.N k) :=
    fun C => Classical.choose (hFallback C)
  let gatedHistory : ∀ C : H.geom.Cell, CellPool H.geom C → FinLaw (R.Hist C) :=
    fun C pool => if ht : S.typical C pool then
      FinLaw.cond (R.history C) (S.gate C pool) (S.gate_pos C pool ht) else R.history C
  have hGatedSupport {C : H.geom.Cell} (pool : CellPool H.geom C) (W : R.Hist C)
      (ht : S.typical C pool) (hW : (gatedHistory C pool).w W ≠ 0) :
      W ∈ S.gate C pool ∧ (R.history C).w W ≠ 0 := by
    by_cases hmem : W ∈ S.gate C pool
    · refine ⟨hmem, ?_⟩
      by_contra hzero
      have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem, hzero]
      exact hW hz
    · have hz : (gatedHistory C pool).w W = 0 := by
        simp [gatedHistory, ht, FinLaw.cond, hmem]
      exact False.elim (hW hz)
  let F : FreshCell H.geom := {
    State := fun C => Option (RawState C)
    fresh := fun C pool =>
      if htyp : S.typical C pool then
        FinLaw.map (FinLaw.bind (gatedHistory C pool)
          (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
          (encode C)
      else FinLaw.dirac none
    fallback := fun _ => none
    label := fun C s b =>
      if hb : H.geom.cellOf b = C ∧ ¬ IsEvenRole b then
        match s with
        | none => defaultLabels C ⟨b, hb⟩
        | some z => if hz : Function.Injective z.2.2 then
            z.2.2 ⟨b, hb⟩ else defaultLabels C ⟨b, hb⟩
      else ⟨0, T.S.N_pos k⟩
    prior := fun C s b y =>
      match s with
      | none => 0
      | some z => R.rawPrior C z.1 z.2.2 b y
    typical := S.typical
  }
  let δperm : ℝ := Real.exp (-(κ.cperm * (T.S.n k : ℝ)) / 2)
  let δgate : ℝ := Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ))
  let Cal : FreshLabelCalibration F := {
    Hist := R.Hist
    Group := R.Group
    groupOf := R.groupOf
    history := R.history
    gatedHistory := gatedHistory
    gate := S.gate
    gate_pos := S.gate_pos
    gated_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp only [gatedHistory, dif_pos ht]
    qin := R.qin
    U := R.U
    U_support := R.U_support
    permitted := fun C g => (Perm.table C).permitted g
    qtilde := K.qtilde
    qtilde_eq := by
      intro C pool W g D ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        have hpos : 0 < 1 - Real.exp (-c * (Perm.table C).n) := sub_pos.mpr hexp
        exact lt_of_lt_of_le hpos hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hzBoth : 0 < zBoth := by
        have hratio' : 0 < zBoth / zPerm := by rw [← hzImageEq]; exact hzImage
        have hmul := mul_pos hratio' hzPerm
        have heq : (zBoth / zPerm) * zPerm = zBoth := div_mul_cancel₀ _ (ne_of_gt hzPerm)
        rw [heq] at hmul
        exact hmul
      have hdenEq :
          (∑ D' ∈ (Perm.table C).permitted g ∩ Finset.image pool Finset.univ,
            (R.qin C W g).w D') = zBoth := by
        simp [zBoth, E, I, Finset.inter_comm]
      have hqtilde := K.qtilde_eq C pool W g D hW (ne_of_gt hzImage)
      rw [hqtilde, hqbar D]
      have hsumQbar : (∑ D' ∈ I, (K.qbar C W g).w D') = zImage := rfl
      rw [hsumQbar, hzImageEq, hdenEq]
      by_cases hDperm : D ∈ E <;> by_cases hDimage : D ∈ I
      · simp [E, I, hDperm, hDimage]
        field_simp [ne_of_gt hzPerm, ne_of_gt hzBoth]
      · have hPermD : D ∈ (Perm.table C).permitted g := by simpa [E] using hDperm
        have hNoPre : ¬ ∃ a, pool a = D := by
          intro hpre
          obtain ⟨a, ha⟩ := hpre
          apply hDimage
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
        simp [hDimage, hNoPre, hPermD]
      · simp [E, I, hDperm, hDimage]
      · simp [E, I, hDperm, hDimage]
    binSampler := S.binLaw
    labelSampler := S.labelLaw
    bin_marginals := by
      intro C pool W g D ht hW
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.bin_marginals C pool W g D ht hGateW hHistW
    label_marginals := by
      intro C pool W a r y ht hW ha
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      exact S.label_marginals C pool W a r y ht hGateW hHistW ha
    encode := encode
    fresh_eq := by
      intro C pool ht
      change S.typical C pool at ht
      simp [F, gatedHistory, ht, encode]
    label_eq := by
      intro C pool W a ys r ht hW ha hys
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hrole : H.geom.cellOf r.1 = C ∧ ¬ IsEvenRole r.1 := r.2
      simp [F, encode, hinj, hrole]
    raw_profile := by
      intro C r y
      rcases hSource with ⟨hmode, _hUniform, hSourceCell⟩ | _hDirect
      · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
          _hgroupOf, hqraw, hpretrim, hU, _hprior⟩ := hSourceCell C
        let gRaw := R.groupOf C r
        let sourcePair := groups.symm gRaw
        let s := sourcePair.1
        let gSol := sourcePair.2
        have hgroups : groups (s, gSol) = gRaw := by
          dsimp [s, gSol, sourcePair]
          exact groups.apply_symm_apply gRaw
        let rowRaw : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W gRaw).w D * (R.U C W gRaw D).w y
        let rowSol : (∀ t, Ssol.Val t) → ℝ := fun W =>
          ∑ D, Ssol.qin W gSol D * Ssol.U gSol W D y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            rowRaw W = rowSol (records s (W s)) := by
          intro W hW
          have hProd :
              (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            simpa [CellRawData.history, FinLaw.pi] using hW
          have hFactor : ∀ t,
              (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t) ≠ 0 := by
            intro t hzero
            apply hProd
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hcond := hFactor t
            have hpass : W t ∈ R.slicePass C t := by
              by_contra hnot
              apply hcond
              simp [FinLaw.cond, hnot]
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              by_contra hzero
              apply hcond
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          have hqin : ∀ D,
              (R.qin C W gRaw).w D = Ssol.qin (records s (W s)) gSol D := by
            intro D
            rw [← hgroups]
            rw [R.qin_eq C W (groups (s, gSol)) D hLocalInput]
            simp only [SliceSolver.qin, hpretrim W s gSol, hqraw W s gSol]
            by_cases hD : D ∈ Ssol.pretrimBins (records s (W s)) gSol <;> simp [hD]
          have hUeq : ∀ D,
              (R.U C W gRaw D).w y = Ssol.U gSol (records s (W s)) D y := by
            intro D
            rw [← hgroups]
            exact hU W s gSol D y
          dsimp [rowRaw, rowSol]
          apply Finset.sum_congr rfl
          intro D hD
          rw [hqin D, hUeq D]
        have hsupportAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) rowRaw (fun W => rowSol (records s (W s))) hrow
        have hcoordAvg :
            (R.history C).E (fun W => rowSol (records s (W s))) =
              (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := by
          simpa [CellRawData.history] using
            (Lane_q_s16_prod2.finLaw_pi_E_coordinate
              (fun t => FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)) s (fun z => rowSol (records s z)))
        have hPassMap : ∀ z,
            ((records s).symm z ∈ R.slicePass C s) ↔ Ssol.AllGood z := by
          intro z
          simpa using hslicePass s ((records s).symm z)
        have hsliceMap : R.sliceLaw C s =
            FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm := hsliceLaw s
        have hden :
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
              (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          calc
            (∑ z ∈ R.slicePass C s, (R.sliceLaw C s).w z) =
                (R.sliceLaw C s).pr (fun z => z ∈ R.slicePass C s) :=
              (Lane_q_s16_prod2.finLaw_pr_finset (R.sliceLaw C s)
                (R.slicePass C s)).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).pr
                  (fun z => z ∈ R.slicePass C s) := by rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).pr
                  (fun z => (records s).symm z ∈ R.slicePass C s) :=
              Lane_q_s16_prod2.finLaw_map_pr _ _ _
            _ = (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
              unfold FinLaw.pr
              apply Finset.sum_congr rfl
              intro z hz
              simp [hPassMap z]
        have hrecPos : 0 < (Ssol.recLaw PT.parameter).pr Ssol.AllGood := by
          rw [← hden]
          exact R.slice_pos C s
        have hnum :
            (∑ z ∈ R.slicePass C s,
              (R.sliceLaw C s).w z * rowSol (records s z)) =
              (Ssol.recLaw PT.parameter).E
                (fun z => if Ssol.AllGood z then rowSol z else 0) := by
          let fVal : R.Value C s → ℝ := fun z =>
            if z ∈ R.slicePass C s then rowSol (records s z) else 0
          calc
            (∑ z ∈ R.slicePass C s,
                (R.sliceLaw C s).w z * rowSol (records s z)) =
              (R.sliceLaw C s).E fVal :=
                (Lane_q_s16_prod2.finLaw_E_finset (R.sliceLaw C s)
                  (R.slicePass C s) (fun z => rowSol (records s z))).symm
            _ = (FinLaw.map (Ssol.recLaw PT.parameter) (records s).symm).E fVal := by
              rw [hsliceMap]
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => fVal ((records s).symm z)) :=
              Lane_q_s16_prod2.finLaw_map_E _ _ _
            _ = (Ssol.recLaw PT.parameter).E
                  (fun z => if Ssol.AllGood z then rowSol z else 0) := by
              congr 1
              funext z
              simp [fVal, hPassMap z]
        have hcondAvg :
            (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
              (R.slice_pos C s)).E (fun z => rowSol (records s z)) =
                Ssol.lowOut PT.parameter gSol y := by
          rw [Lane_q_s16_prod2.finLaw_cond_E]
          rw [hnum, hden]
          simp [SliceSolver.lowOut, rowSol, FinLaw.E]
        have hpi := Q.profiled_valid.low_profile hmode
          (H.geom.cellPatch C) Ssol hsolver gSol y
        calc
          (R.history C).E rowRaw =
              (R.history C).E (fun W => rowSol (records s (W s))) := hsupportAvg
          _ = (FinLaw.cond (R.sliceLaw C s) (R.slicePass C s)
                (R.slice_pos C s)).E (fun z => rowSol (records s z)) := hcoordAvg
          _ = Ssol.lowOut PT.parameter gSol y := hcondAvg
          _ = (PT.π (H.geom.cellPatch C)).w y := hpi.symm
      · obtain ⟨hnot, hDirectCells⟩ := _hDirect
        let i := H.geom.cellPatch C
        let Y := (PT.tiling.P i).Y
        have hY : Y.Nonempty := (Q.profiled_valid.tiling_valid.patch_nonempty i).2
        have hd : (PT.tiling.P i).d = 1 := by
          cases hmode' : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode'
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode') i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode']; simp [Mode.isCluster]
              exact (hnot hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode'] at hlow
              have hf : False := by simpa [Mode.isLow] using hlow
              exact hf.elim
        obtain ⟨hGroupInjective, _hValues, hSlicePass, hqrawDirect,
          hpretrimDirect, hUDirect, _hPrior⟩ := hDirectCells C
        have hBinSingleton : ∀ D : Bin PT.tiling i, D.1.card = 1 := by
          intro D
          calc
            D.1.card = (PT.tiling.P i).d :=
              Q.profiled_valid.tiling_valid.bins_card i D.1 D.2
            _ = 1 := hd
        let labelOfBin : Bin PT.tiling i → {z : Fin (T.S.N k) // z ∈ Y} := fun D => by
          let z : Fin (T.S.N k) := Classical.choose (Finset.card_eq_one.mp (hBinSingleton D))
          have hset : D.1 = {z} := Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
          have hmemSingleton : z ∈ ({z} : Finset (Fin (T.S.N k))) := Finset.mem_singleton_self z
          have hmem : z ∈ D.1 := by simpa [hset] using hmemSingleton
          exact ⟨z, (PT.tiling.P i).bins.le D.2 hmem⟩
        have hBinSet (D : Bin PT.tiling i) : D.1 = { (labelOfBin D).1 } :=
          Classical.choose_spec (Finset.card_eq_one.mp (hBinSingleton D))
        have hlabelInj : Function.Injective labelOfBin := by
          intro D D' hEq
          apply Subtype.ext
          have hval := congrArg Subtype.val hEq
          rw [hBinSet D, hBinSet D']
          simp [hval]
        have hlabelSurj : Function.Surjective labelOfBin := by
          intro z
          have hzCover : z.1 ∈ (PT.tiling.P i).bins.parts.biUnion id := by
            rw [(PT.tiling.P i).bins.biUnion_parts]
            exact z.2
          obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hzCover
          let D : Bin PT.tiling i := ⟨B, hB⟩
          refine ⟨D, ?_⟩
          apply Subtype.ext
          have hzSingle : z.1 ∈ ({ (labelOfBin D).1 } : Finset (Fin (T.S.N k))) := by
            rw [← hBinSet D]
            exact hzB
          exact (Finset.mem_singleton.mp hzSingle).symm
        let binEquiv : Bin PT.tiling i ≃ {z : Fin (T.S.N k) // z ∈ Y} :=
          Equiv.ofBijective labelOfBin ⟨hlabelInj, hlabelSurj⟩
        have hBinCard : (Fintype.card (Bin PT.tiling i) : ℝ) = (Y.card : ℝ) := by
          have hcard : Fintype.card (Bin PT.tiling i) = Y.card := by
            calc
              Fintype.card (Bin PT.tiling i) =
                  Fintype.card {z : Fin (T.S.N k) // z ∈ Y} := Fintype.card_congr binEquiv
              _ = Y.card := by simp [Y]
          exact_mod_cast hcard
        have hlabelCount :
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
              if y ∈ Y then 1 else 0 := by
          calc
            (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) =
                ∑ D : Bin PT.tiling i, if y = (labelOfBin D).1 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro D hD
              rw [hBinSet D]
              simp [eq_comm]
            _ = ∑ z : {z : Fin (T.S.N k) // z ∈ Y},
                  if y = z.1 then (1 : ℝ) else 0 := by
              exact Fintype.sum_equiv binEquiv
                (fun D => if y = (labelOfBin D).1 then (1 : ℝ) else 0)
                (fun z => if y = z.1 then (1 : ℝ) else 0)
                (by intro D; rfl)
            _ = if y ∈ Y then 1 else 0 := by
              by_cases hy : y ∈ Y
              · simp only [if_pos hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = {⟨y, hy⟩} := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro hz
                    exact Finset.mem_singleton.mpr (Subtype.ext hz.symm)
                  · intro hz
                    exact (congrArg Subtype.val (Finset.mem_singleton.mp hz)).symm
                rw [← Finset.sum_filter, hfilter]
                simp
              · simp only [if_neg hy]
                have hfilter :
                    (Finset.univ : Finset {z : Fin (T.S.N k) // z ∈ Y}).filter
                      (fun z => y = z.1) = ∅ := by
                  ext z
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  constructor
                  · intro heq
                    exact False.elim (hy (heq.symm ▸ z.2))
                  · intro hfalse
                    cases hfalse
                rw [← Finset.sum_filter, hfilter]
                simp
        have hRawDirect (W : R.Hist C) (hW : (R.history C).w W ≠ 0) :
            ∀ D, (R.qin C W (R.groupOf C r)).w D =
              (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ := by
          have hHistoryPos : ∀ t,
              ((FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                (R.slice_pos C t)).w (W t)) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            intro t hzero
            apply hprod
            exact Finset.prod_eq_zero (Finset.mem_univ t) hzero
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hHistoryPos t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          intro D
          rw [R.qin_eq C W (R.groupOf C r) D hLocalInput]
          rw [hpretrimDirect W (R.groupOf C r)]
          have hsum :
              (∑ D' ∈ (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))),
                (R.qraw C W (R.groupOf C r)).w D') = 1 := by
            simpa using (R.qraw C W (R.groupOf C r)).sum_one
          rw [hsum, hqrawDirect W (R.groupOf C r) D]
          simp [i]
        have hpiLaw : PT.π i = Law.unifCore Y hY :=
          (Q.profiled_valid.law_uniform_direct.resolve_left hnot) i
        rw [hpiLaw]
        let row : R.Hist C → ℝ := fun W =>
          ∑ D, (R.qin C W (R.groupOf C r)).w D * (R.U C W (R.groupOf C r) D).w y
        have hrow : ∀ W, (R.history C).w W ≠ 0 →
            row W = (Law.unifCore Y hY).w y := by
          intro W hW
          have hLocalInput : ∀ t,
              W t ∈ R.slicePass C t ∧ (R.sliceLaw C t).w (W t) ≠ 0 := by
            have hprod :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hW
            have hFactor : ∀ t,
                (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t) ≠ 0 := by
              intro t hz
              apply hprod
              exact Finset.prod_eq_zero (Finset.mem_univ t) hz
            intro t
            have hpass : W t ∈ R.slicePass C t := by rw [hSlicePass t]; simp
            have hraw : (R.sliceLaw C t).w (W t) ≠ 0 := by
              intro hzero
              apply hFactor t
              simp [FinLaw.cond, hpass, hzero]
            exact ⟨hpass, hraw⟩
          calc
            row W = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                (∑ D : Bin PT.tiling i, if y ∈ D.1 then (1 : ℝ) else 0) := by
              dsimp [row]
              calc
                (∑ D : Bin PT.tiling (H.geom.cellPatch C), (R.qin C W (R.groupOf C r)).w D *
                    (R.U C W (R.groupOf C r) D).w y) =
                    ∑ D : Bin PT.tiling (H.geom.cellPatch C), (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (if y ∈ D.1 then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro (D : Bin PT.tiling (H.geom.cellPatch C)) hD
                  simpa [hUDirect W (R.groupOf C r) D y] using
                    congrArg (fun q : ℝ => q * (R.U C W (R.groupOf C r) D).w y)
                      (hRawDirect W hW D)
                _ = (Fintype.card (Bin PT.tiling i) : ℝ)⁻¹ *
                      (∑ D : Bin PT.tiling (H.geom.cellPatch C),
                        if y ∈ D.1 then (1 : ℝ) else 0) := by
                  rw [← Finset.mul_sum]
            _ = (Law.unifCore Y hY).w y := by
              rw [hlabelCount]
              by_cases hy : y ∈ Y <;> simp [Law.unifCore, hBinCard, hy]
        have hAvg := Lane_q_s16_prod2.finLaw_E_congr_of_supported
          (R.history C) row (fun _ => (Law.unifCore Y hY).w y) hrow
        calc
          (R.history C).E row = (R.history C).E (fun _ => (Law.unifCore Y hY).w y) := hAvg
          _ = (Law.unifCore Y hY).w y := by
            unfold FinLaw.E
            rw [← Finset.sum_mul, (R.history C).sum_one]
            ring
    δperm := δperm
    δgate := δgate
    perm_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
        have hc : 0 < κ.cperm := hκ.cperm_rng.1
        have hprod : 0 < κ.cperm * (T.S.n k : ℝ) := mul_pos hc hnreal
        have harg : -(κ.cperm * (T.S.n k : ℝ)) / 2 < 0 := by linarith
        exact Real.exp_lt_one_iff.mpr harg
    gate_range := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · have hnreal : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
        have hpow : 0 < (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by positivity
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpow)
    permission_mass := by
      intro C W g hW
      have h := Lane_q_s16_prod2.permission_mass_explicit_lower
        (Perm.table C) (R.qin C W) (hPerm C W hW) g
      simpa [Perm.rate_eq C, Perm.n_eq C, mul_assoc, mul_comm, mul_left_comm] using h
    pool_normalizer := by
      intro C pool W g ht hW
      let E := (Perm.table C).permitted g
      let I := Finset.univ.image pool
      let zPerm : ℝ := ∑ B ∈ E, (R.qin C W g).w B
      let zImage : ℝ := ∑ B ∈ I, (K.qbar C W g).w B
      let zBoth : ℝ := ∑ B ∈ E ∩ I, (R.qin C W g).w B
      obtain ⟨c, hc, _hcard, hmass⟩ := permission_loss hκ (Perm.table C)
        (R.qin C W) (hPerm C W hW)
      have hcN : 0 < c * ((Perm.table C).n : ℝ) := by
        exact mul_pos hc (by exact_mod_cast (Perm.table C).n_pos)
      have hexp : Real.exp (-c * (Perm.table C).n) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        nlinarith [hcN]
      have hzPerm : 0 < zPerm := by
        have hbound : 1 - Real.exp (-c * (Perm.table C).n) ≤ zPerm := by
          simpa [zPerm] using hmass g
        exact lt_of_lt_of_le (sub_pos.mpr hexp) hbound
      have hqbar : ∀ B, (K.qbar C W g).w B =
          (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
        intro B
        simpa [E, zPerm] using K.qbar_eq C W g B hW
      have hdiagTypical : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let hPoolReq := pool_requirements_realized (Ds.diagnostic C) pool hdiagTypical
      have hslotPos : 0 < H.geom.nslot C := by
        simpa using (Ds.concentration C).slots_pos
      have hqinPr : 0 < (R.qin C W g).pr (fun _ => True) := by
        rw [Lane_q_s16_prod2.finLaw_pr_const]
        norm_num
      obtain ⟨B₀, _hTrue, _hB₀⟩ := Lane_q_s16_prod2.finLaw_pr_pos_has_nonzero_atom
        (R.qin C W g) (fun _ => True) hqinPr
      letI : Nonempty (Bin PT.tiling (H.geom.cellPatch C)) := ⟨B₀⟩
      have hbinCard : 0 < Fintype.card (Bin PT.tiling (H.geom.cellPatch C)) := Fintype.card_pos
      let theta : ℝ := (H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))
      have htheta : 0 < theta := by
        dsimp [theta]
        exact div_pos (by exact_mod_cast hslotPos) (by exact_mod_cast hbinCard)
      have hclose :
          |(Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta - 1| ≤
            Real.rpow (T.S.n k : ℝ) (-4 : ℝ) := by
        simpa [theta] using
          hPoolReq.normalizer_close ((Ds.linked C).groupProbe g) W
      have hnreal : 1 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hpowlt : Real.rpow (T.S.n k : ℝ) (-4 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hnreal (by norm_num)
      have hratio : 0 <
          (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
        have habs := abs_le.mp hclose
        have hlower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          linarith
        exact lt_of_lt_of_le (sub_pos.mpr hpowlt) hlower
      have hnormPos :
          0 < (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hmul := mul_pos hratio htheta
        have heq :
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) * theta =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W :=
          div_mul_cancel₀ _ (ne_of_gt htheta)
        rw [heq] at hmul
        exact hmul
      have hnormEq := (Ds.linked C).normalizer_eq pool W g hW
      have hzImage : 0 < zImage := by
        dsimp [zImage, I]
        rw [← hnormEq]
        exact hnormPos
      have hnum :
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) = zBoth := by
        have hfilter : I.filter (fun B => B ∈ E) = E ∩ I := by
          ext B
          simp [I, E, and_comm]
        calc
          (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) =
              ∑ B ∈ I.filter (fun B => B ∈ E), (R.qin C W g).w B := by
            rw [← Finset.sum_filter]
          _ = ∑ B ∈ E ∩ I, (R.qin C W g).w B := by rw [hfilter]
          _ = zBoth := rfl
      have hzImageEq : zImage = zBoth / zPerm := by
        calc
          zImage = ∑ B ∈ I, (K.qbar C W g).w B := rfl
          _ = ∑ B ∈ I,
                (if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              apply Finset.sum_congr rfl
              intro B hB
              rw [hqbar B]
          _ = (∑ B ∈ I, if B ∈ E then (R.qin C W g).w B else 0) / zPerm := by
              rw [← Finset.sum_div]
          _ = zBoth / zPerm := by rw [hnum]
      have hnormLower :
          theta * (1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
        have hratioLower : 1 - Real.rpow (T.S.n k : ℝ) (-4 : ℝ) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta := by
          have habs := abs_le.mp hclose
          linarith
        have hmul := mul_le_mul_of_nonneg_left hratioLower (le_of_lt htheta)
        have heq : theta *
            ((Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W / theta) =
              (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          field_simp [ne_of_gt htheta]
        rw [heq] at hmul
        exact hmul
      calc
        theta * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ)) ≤
            (Ds.diagnostic C).poolNormalizer pool ((Ds.linked C).groupProbe g) W := by
          simpa using hnormLower
        _ = zBoth / zPerm := by
          rw [hnormEq]
          exact hzImageEq
        _ = (∑ D' ∈ ((Perm.table C).permitted g ∩ Finset.univ.image pool),
              (R.qin C W g).w D') /
              (∑ D' ∈ (Perm.table C).permitted g, (R.qin C W g).w D') := rfl
    gate_mass := by
      intro C pool ht
      have htyp : (Ds.diagnostic C).typical pool := (hTypical C pool).mp ht
      let D := Ds.diagnostic C
      have hBad := history_load_gate_concentration D (Ds.load C) pool htyp
      have hfail : (R.history C).pr (fun W => ¬ D.loadGate pool W) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [(Ds.linked C).history_eq pool] at hBad
        simpa [Ds.exponent_half] using hBad.1
      have hcomp := Lane_q_s16_prod2.finLaw_pr_compl (R.history C)
        (fun W => D.loadGate pool W)
      have hgateProb : (R.history C).pr (fun W => D.loadGate pool W) =
          ∑ W ∈ S.gate C pool, (R.history C).w W := by
        unfold FinLaw.pr
        rw [← Finset.sum_filter, hGate C pool]
      calc
        1 - Real.exp (-(T.S.n k : ℝ) ^ (1 / 2 : ℝ)) ≤
            (R.history C).pr (fun W => D.loadGate pool W) := by
          linarith [hcomp, hfail]
        _ = ∑ W ∈ S.gate C pool, (R.history C).w W := hgateProb
    slot_pos := by
      intro C
      simpa using (Ds.concentration C).slots_pos
    cost_budget := by
      have htails := hCost (T.S.n k) hnCost
      have hnreal : 1 ≤ (T.S.n k : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 8) hn8)
      have hq0 : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
      have hq1 : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnreal (by norm_num)
      simpa [δgate, δperm] using
        (Lane_q_s16_prod2.inverse_three_slacks hq0 hq1
          (by positivity) (by positivity) (by positivity)
          htails.1 htails.2.1 htails.2.2)
  }
  let Link : FreshConstructionLink S F Cal := {
    histories := fun _ => Equiv.refl _
    groups := fun _ => Equiv.refl _
    history_eq := by
      intro C
      change R.history C = FinLaw.map (R.history C) id
      exact (Lane_q_s16_prod2.finLaw_map_id (R.history C)).symm
    group_eq := by intro C r; rfl
    incoming_eq := by intro C W g; rfl
    U_eq := by intro C W g b; rfl
    permission_eq := by intro C g; rfl
    restricted_eq := by intro C pool W g; rfl
    typical_eq := by intro C pool; rfl
    gate_eq := by
      intro C pool
      change S.gate C pool = Finset.image id (S.gate C pool)
      ext W
      simp
    bin_eq := by
      intro C pool W
      change S.binLaw C pool W = FinLaw.map (S.binLaw C pool W) id
      exact (Lane_q_s16_prod2.finLaw_map_id (S.binLaw C pool W)).symm
    label_eq := by
      intro C pool W a
      rfl
    prior_eq := by
      intro C pool W a ys v ht hW ha hys hcell hEven
      change S.typical C pool at ht
      obtain ⟨hGateW, hHistW⟩ := hGatedSupport pool W ht hW
      have hinj := S.label_injective C pool W a ys ht hGateW hHistW ha hys
      have hencode : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl, hencode]
      rfl
  }
  let Spec : FreshCell.Spec F (InternallyValid F Cal) Cal.permittedLabels := {
    fresh_valid := by
      intro C pool s ht hs
      change S.typical C pool at ht
      let sourceLaw := FinLaw.bind (gatedHistory C pool) fun W =>
        FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)
      rw [Cal.fresh_eq C pool ht] at hs
      obtain ⟨src, henc, hsrcPos⟩ :=
        Lane_q_s16_prod2.finLaw_map_nonzero_preimage sourceLaw (encode C) s (ne_of_gt hs)
      rcases src with ⟨W, ab⟩
      rcases ab with ⟨a, ys⟩
      have hGatePos : (gatedHistory C pool).w W ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      have hBinPos : (S.binLaw C pool W).w a ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      have hLabelPos : (S.labelLaw C pool W a).w ys ≠ 0 := by
        intro hz
        apply hsrcPos
        simp [sourceLaw, FinLaw.bind, hz]
      obtain ⟨hGateW, hHistPos⟩ := hGatedSupport pool W ht hGatePos
      have hinj := S.label_injective C pool W a ys ht hGateW hHistPos hBinPos hLabelPos
      have hEncEq : encode C (W, (a, ys)) = some (W, (a, ys)) := by
        simp [encode, hinj]
      have hStateEq : s = some (W, (a, ys)) := henc.symm.trans hEncEq
      subst s
      refine ⟨?_, ?_⟩
      · intro b hcell hodd
        let r : OddCellRole H.geom C := ⟨b, ⟨hcell, hodd⟩⟩
        let g := Cal.groupOf C r
        let D := a g
        have hBinAtomPos : 0 < (S.binLaw C pool W).w a :=
          lt_of_le_of_ne ((S.binLaw C pool W).nonneg a) (Ne.symm hBinPos)
        have hBinEvent := Lane_q_s16_prod2.finLaw_weight_le_pr
          (S.binLaw C pool W) (fun a' => a' g = D) a rfl
        have hQtildePos : 0 < (K.qtilde C pool W g).w D := by
          have hPrPos : 0 < (S.binLaw C pool W).pr (fun a' => a' g = D) :=
            lt_of_lt_of_le hBinAtomPos hBinEvent
          rw [S.bin_marginals C pool W g D ht hGateW hHistPos] at hPrPos
          exact hPrPos
        have hAllowedPool : D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image pool := by
          by_cases hmem : D ∈ Cal.permitted C g ∧ D ∈ Finset.univ.image pool
          · exact hmem
          · have hzero : (K.qtilde C pool W g).w D = 0 := by
              rw [Cal.qtilde_eq C pool W g D ht hHistPos]
              rcases not_and_or.mp hmem with hnotPerm | hnotPool
              · simp [hnotPerm]
              · simp [hnotPool]
            exact False.elim (ne_of_gt hQtildePos hzero)
        have hUPos : (R.U C W g D).w (ys r) ≠ 0 := by
          have hAtom := Lane_q_s16_prod2.finLaw_weight_le_pr
            (S.labelLaw C pool W a) (fun y' => y' r = ys r) ys rfl
          have hLabelAtomPos : 0 < (S.labelLaw C pool W a).w ys :=
            lt_of_le_of_ne ((S.labelLaw C pool W a).nonneg ys) (Ne.symm hLabelPos)
          have hPrPos : 0 < (S.labelLaw C pool W a).pr (fun y' => y' r = ys r) :=
            lt_of_lt_of_le hLabelAtomPos hAtom
          have hMarg := S.label_marginals C pool W a r (ys r)
            ht hGateW hHistPos hBinPos
          rw [hMarg] at hPrPos
          exact ne_of_gt hPrPos
        have hLabelInBin : ys r ∈ D.1 := R.U_support C W g D (ys r) hUPos
        obtain ⟨slot, hslot, hslotEq⟩ := Finset.mem_image.mp hAllowedPool.2
        have hpoolContains : poolContainsLabel pool (ys r) := by
          refine ⟨slot, ?_⟩
          simpa [hslotEq] using hLabelInBin
        have hpermitted : ys r ∈ Cal.permittedLabels C pool b := by
          have hrole : H.geom.cellOf b = C ∧ ¬ IsEvenRole b := ⟨hcell, hodd⟩
          simp only [FreshLabelCalibration.permittedLabels, hrole, dite_true]
          exact Finset.mem_biUnion.mpr ⟨D, hAllowedPool.1, hLabelInBin⟩
        have hFLabel : F.label C (some (W, (a, ys))) b = ys r := by
          simp [F, r, hcell, hodd, hinj]
        rw [hEncEq, hFLabel]
        exact ⟨hpermitted, hpoolContains⟩
      · intro v hcell hEven
        by_cases hcluster : PT.tiling.mode.isCluster
        · rcases hSource with ⟨hsourceMode, _hUniform, hSourceCell⟩ | ⟨hnot, _hDirectCells⟩
          · obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
              _hGroupOf, _hqraw, _hpretrim, _hU, hPriorLink⟩ := hSourceCell C
            let sourcePair := (R.cellWords C).symm ⟨v, hcell⟩
            let sourceSlice := sourcePair.1
            let word := sourcePair.2
            have hCellWord : R.cellWords C (sourceSlice, word) = ⟨v, hcell⟩ := by
              dsimp [sourceSlice, word, sourcePair]
              exact Equiv.apply_symm_apply (R.cellWords C) ⟨v, hcell⟩
            have hCellWordVal : (R.cellWords C (sourceSlice, word)).1 = v :=
              congrArg Subtype.val hCellWord
            have hEvenWord : IsEvenRole word := by
              have hpar := R.word_parity hcluster C sourceSlice word
              rw [hCellWord] at hpar
              exact hpar.mp hEven
            let w : EvenRole PT.tiling (H.geom.cellPatch C) := ⟨word, hEvenWord⟩
            let ev : EvenCellRole H.geom C := ⟨v, ⟨hcell, hEven⟩⟩
            obtain ⟨L, hFeasible⟩ :=
              S.cluster_label_feasible C pool W a ht hGateW hHistPos hBinPos hcluster
            have hSafe : L.problem.safe ys := hFeasible.1 ys hLabelPos
            have hRawRowPos : R.rawPrior C W ys v ≠ 0 := by
              intro hz
              have hbad : L.problem.starBad ev ys :=
                (L.tests_eq ev ys).2 ⟨hcluster, hz⟩
              exact hSafe.2 ev hbad
            let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
            have hPriorEq := hPriorLink W sourceSlice w ys fallback
            rw [hCellWordVal] at hPriorEq
            have hSigmaPos :
                Ssol.σ w (records sourceSlice (W sourceSlice))
                  (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) ≠ 0 := by
              intro hz
              apply hRawRowPos
              rw [hPriorEq]
              exact hz
            have hHistProd :
                (∏ t, (FinLaw.cond (R.sliceLaw C t) (R.slicePass C t)
                  (R.slice_pos C t)).w (W t)) ≠ 0 := by
              simpa [CellRawData.history, FinLaw.pi] using hHistPos
            have hSlicePos : (R.sliceLaw C sourceSlice).w (W sourceSlice) ≠ 0 := by
              have hcond :
                  (FinLaw.cond (R.sliceLaw C sourceSlice) (R.slicePass C sourceSlice)
                    (R.slice_pos C sourceSlice)).w (W sourceSlice) ≠ 0 := by
                intro hz
                apply hHistProd
                exact Finset.prod_eq_zero (Finset.mem_univ sourceSlice) hz
              have hpass : W sourceSlice ∈ R.slicePass C sourceSlice := by
                by_contra hnotPass
                apply hcond
                simp [FinLaw.cond, hnotPass]
              intro hz
              apply hcond
              simp [FinLaw.cond, hpass, hz]
            have hMapPos :
                (FinLaw.map (Ssol.recLaw PT.parameter) (records sourceSlice).symm).w
                  (W sourceSlice) ≠ 0 := by
              rw [← hsliceLaw sourceSlice]
              exact hSlicePos
            obtain ⟨record, hRecordMap, hRecordPos⟩ :=
              Lane_q_s16_prod2.finLaw_map_nonzero_preimage
                (Ssol.recLaw PT.parameter) (records sourceSlice).symm
                (W sourceSlice) hMapPos
            have hRecordEq : record = records sourceSlice (W sourceSlice) := by
              calc
                record = records sourceSlice ((records sourceSlice).symm record) :=
                  (records sourceSlice).apply_symm_apply record |>.symm
                _ = records sourceSlice (W sourceSlice) := by rw [hRecordMap]
            have hRecordPos' :
                (Ssol.recLaw PT.parameter).w (records sourceSlice (W sourceSlice)) ≠ 0 := by
              rw [← hRecordEq]
              exact hRecordPos
            have hRecordPositive :
                0 < (Ssol.recLaw PT.parameter).w (records sourceSlice (W sourceSlice)) :=
              lt_of_le_of_ne
                ((Ssol.recLaw PT.parameter).nonneg (records sourceSlice (W sourceSlice)))
                (Ne.symm hRecordPos')
            obtain ⟨activeVertex, hActive, hSigmaSupport⟩ :=
              Ssol.σ_support w (records sourceSlice (W sourceSlice))
                (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) hSigmaPos
            have hActivePos : 0 < PT.mesh.wt activeVertex PT.parameter :=
              hActive PT.parameter (by simpa [SliceSolver.recLaw] using hRecordPositive)
            have hActiveMem : activeVertex ∈ PT.activeVertices := by
              simp [ProfiledTiling.activeVertices, hActivePos]
            have hPriorEqFun (y : Fin (T.S.N k)) :
                F.prior C (encode C (W, (a, ys))) v y =
                  Ssol.σ w (records sourceSlice (W sourceSlice))
                    (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y := by
              rw [hEncEq]
              change R.rawPrior C W ys v y = _
              exact congrFun hPriorEq y
            constructor
            · calc
                (∑ y, F.prior C (encode C (W, (a, ys))) v y) =
                    ∑ y, Ssol.σ w (records sourceSlice (W sourceSlice))
                      (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  exact hPriorEqFun y
                _ = 1 := Ssol.σ_prob w (records sourceSlice (W sourceSlice))
                  (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) hSigmaPos
            · intro y hy
              have hSigmaY :
                  Ssol.σ w (records sourceSlice (W sourceSlice))
                    (nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback)) y ≠ 0 := by
                rw [← hPriorEqFun y]
                exact hy
              obtain ⟨hCorner, hHits⟩ := hSigmaSupport y hSigmaY
              have hEnvelope : y ∈ PT.envelope (H.geom.cellPatch C) := by
                rw [Q.profiled_valid.envelope_eq (H.geom.cellPatch C)]
                exact Finset.mem_biUnion.mpr ⟨activeVertex, hActiveMem, hCorner⟩
              refine ⟨hEnvelope, ?_⟩
              intro j hj
              have hAxisMem : j ∈ Finset.univ.image (R.axis C) := by
                rw [R.axes_eq C]
                exact hj
              obtain ⟨l, _hl, hAxis⟩ := Finset.mem_image.mp hAxisMem
              have hFlipWord := R.word_flip C sourceSlice word l
              rw [hCellWordVal] at hFlipWord
              rw [hAxis] at hFlipWord
              have hOddInternal : ¬ IsEvenRole (flipPos word l) := by
                intro hflip
                exact (HypercubeRamsey.S15.evenRole_flipPos word l).mp hflip hEvenWord
              have hParityFlip := R.word_parity hcluster C sourceSlice (flipPos word l)
              have hOddCellWord : ¬ IsEvenRole
                  ((R.cellWords C (sourceSlice, flipPos word l)).1) := by
                intro heven
                exact hOddInternal (hParityFlip.mp heven)
              have hCellFlip : H.geom.cellOf (flipPos v j) = C := by
                have hc := (R.cellWords C (sourceSlice, flipPos word l)).2
                rw [hFlipWord] at hc
                exact hc
              have hOddFlip : ¬ IsEvenRole (flipPos v j) := by
                have ho := hOddCellWord
                rw [hFlipWord] at ho
                exact ho
              let roleFlip : OddCellRole H.geom C :=
                ⟨flipPos v j, ⟨hCellFlip, hOddFlip⟩⟩
              have hWordLabel :
                  R.wordLabel C ys sourceSlice fallback (flipPos word l) = ys roleFlip := by
                simp [CellRawData.wordLabel, hOddFlip, hFlipWord, roleFlip]
              have hCalLabel := Cal.label_eq C pool W a ys roleFlip
                ht hGatePos hBinPos hLabelPos
              rw [show Cal.encode C (W, (a, ys)) = encode C (W, (a, ys)) by rfl] at hCalLabel
              have hLabelsEq :
                  F.label C (encode C (W, (a, ys))) (flipPos v j) =
                    R.wordLabel C ys sourceSlice fallback (flipPos word l) := by
                exact hCalLabel.trans hWordLabel.symm
              rw [hLabelsEq]
              exact hHits l
          · exact False.elim (hnot hcluster)
        · rcases hSource with ⟨hmode, _hUniform, _hSourceCell⟩ | ⟨hnot, hDirectData⟩
          · have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
            exact False.elim (hcluster hc)
          · obtain ⟨_, _, _, _, _, _, hEnvExists⟩ := hDirectData C
            obtain ⟨hEnv, hPrior⟩ := hEnvExists
            have hHeightZero : (PT.tiling.P (H.geom.cellPatch C)).h = 0 := by
              cases hmode : PT.tiling.mode with
              | bounded =>
                  have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
                  exact (hdata.2 (H.geom.cellPatch C)).2.1
              | lowDirect =>
                  have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode)
                    (H.geom.cellPatch C)
                  exact hdata.2.2.2.2.1
              | lowCluster =>
                  have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
                  exact (hnot hc).elim
              | highDirect | highSmall | highLarge =>
                  have hlow := Q.mode_low
                  rw [hmode] at hlow
                  have hf : False := by simpa [Mode.isLow] using hlow
                  exact hf.elim
            have hIcoord : PT.tiling.Icoord (H.geom.cellPatch C) = ∅ := by
              ext j
              simp [Tiling.Icoord, topCoordinates, hHeightZero]
            have hPriorFun (y : Fin (T.S.N k)) :
                F.prior C (encode C (W, (a, ys))) v y =
                  (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).w y := by
              rw [hEncEq]
              change R.rawPrior C W ys v y = _
              exact congrFun (hPrior W ys v hcell hEven) y
            constructor
            · calc
                (∑ y, F.prior C (encode C (W, (a, ys))) v y) =
                    ∑ y, (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).w y := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  exact hPriorFun y
                _ = 1 := (Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv).sum_eq_one
            · intro y hy
              have hEnvY : y ∈ PT.envelope (H.geom.cellPatch C) := by
                rw [hPriorFun y] at hy
                by_contra hnotEnv
                apply hy
                simp [Law.unifCore, hnotEnv]
              refine ⟨hEnvY, ?_⟩
              intro j hj
              rw [hIcoord] at hj
              simp at hj
    fresh_atypical := by
      intro C pool hnot
      change ¬ S.typical C pool at hnot
      change (if ht : S.typical C pool then
          FinLaw.map (FinLaw.bind (gatedHistory C pool)
            (fun W => FinLaw.bind (S.binLaw C pool W) (S.labelLaw C pool W)))
            (encode C) else FinLaw.dirac none) = FinLaw.dirac none
      by_cases ht : S.typical C pool
      · exact (hnot ht).elim
      · simp [ht]
    label_permitted := by
      intro C pool s b hvalid hcell hodd
      exact (hvalid.1 b hcell hodd).1
    labels_injective := by
      intro C s b b' hcell hcell' hodd hodd' hne
      let rb : OddCellRole H.geom C := ⟨b, ⟨hcell, hodd⟩⟩
      let rb' : OddCellRole H.geom C := ⟨b', ⟨hcell', hodd'⟩⟩
      intro hlabels
      cases s with
      | none =>
          have hvals : defaultLabels C rb = defaultLabels C rb' := by
            simpa [F, rb, rb', hcell, hodd, hcell', hodd'] using hlabels
          have hinj := Classical.choose_spec (hFallback C)
          exact hne (congrArg Subtype.val (hinj hvals))
      | some z =>
          by_cases hz : Function.Injective z.2.2
          · have hvals : z.2.2 rb = z.2.2 rb' := by
              simpa [F, rb, rb', hcell, hodd, hcell', hodd', hz] using hlabels
            exact hne (congrArg Subtype.val (hz hvals))
          · have hvals : defaultLabels C rb = defaultLabels C rb' := by
              simpa [F, rb, rb', hcell, hodd, hcell', hodd', hz] using hlabels
            have hinj := Classical.choose_spec (hFallback C)
            exact hne (congrArg Subtype.val (hinj hvals))
    prior_nonneg := by
      intro C s b y
      cases s with
      | none => simp [F]
      | some z => exact R.prior_nonneg C z.1 z.2.2 b y
    prior_subprob := by
      intro C s b
      cases s with
      | none => simp [F]
      | some z => exact R.prior_subprob C z.1 z.2.2 b
  }
  exact ⟨F, Cal, ⟨Link⟩, Spec⟩
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
  classical
  refine ⟨2, ?_⟩
  intro T k PT K16 Q H hCalibration R Perm K c0 Ds S F Cal hSource hn hPerm
    hTypical hGate hLink C v hcell hEven
  rcases hSource with hCluster | ⟨hDirect, hDirectData⟩
  · rcases hCluster with ⟨hmode, hUniform, hSourceCell⟩
    obtain ⟨Ssol, hsolver, records, groups, hsliceLaw, hslicePass,
      hgroupReadout, hqraw, hpretrim, hU, hpriorReadout⟩ := hSourceCell C
    let sourcePair := (R.cellWords C).symm ⟨v, hcell⟩
    let sourceSlice := sourcePair.1
    let word := sourcePair.2
    have hCellWord : R.cellWords C (sourceSlice, word) = ⟨v, hcell⟩ := by
      dsimp [sourceSlice, word, sourcePair]
      exact Equiv.apply_symm_apply (R.cellWords C) ⟨v, hcell⟩
    have hCellWordVal : (R.cellWords C (sourceSlice, word)).1 = v :=
      congrArg Subtype.val hCellWord
    have hClusterMode : PT.tiling.mode.isCluster := by
      rw [hmode]
      simp [Mode.isCluster]
    have hEvenWord : IsEvenRole word := by
      have hpar := R.word_parity hClusterMode C sourceSlice word
      rw [hCellWord] at hpar
      exact hpar.mp hEven
    let w : EvenRole PT.tiling (H.geom.cellPatch C) := ⟨word, hEvenWord⟩
    let loc : SliceStarLocation H.geom C v w := {
      axis := R.axis C
      axis_injective := R.axis_injective C
      axes_eq := R.axes_eq C
      embed := fun z => (R.cellWords C (sourceSlice, z)).1
      site_eq := hCellWordVal
      flip_eq := by
        intro z j
        exact R.word_flip C sourceSlice z j
      outer_eq := by
        intro z j hj
        have hout := R.word_outer C sourceSlice z word j hj
        rw [hCellWordVal] at hout
        exact hout
    }
    have hStarCell (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) :
        H.geom.cellOf (flipPos v (R.axis C j)) = C := by
      have hflip := R.word_flip C sourceSlice word j
      rw [hCellWordVal] at hflip
      have hmem := (R.cellWords C (sourceSlice, flipPos word j)).2
      rw [hflip] at hmem
      exact hmem
    have hStarOdd (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) :
        ¬ IsEvenRole (flipPos v (R.axis C j)) := by
      have hInternalOdd : ¬ IsEvenRole (flipPos word j) := by
        intro heven
        exact ((HypercubeRamsey.S15.evenRole_flipPos word j).mp heven) hEvenWord
      have hflip := R.word_flip C sourceSlice word j
      rw [hCellWordVal] at hflip
      have hParity := R.word_parity hClusterMode C sourceSlice (flipPos word j)
      rw [hflip] at hParity
      intro heven
      exact hInternalOdd (hParity.mp heven)
    let starRole (j : Fin (PT.tiling.P (H.geom.cellPatch C)).h) : OddCellRole H.geom C :=
      ⟨flipPos v (R.axis C j), ⟨hStarCell j, hStarOdd j⟩⟩
    let roleScope : Finset (OddCellRole H.geom C) := Finset.univ.image starRole
    let groupScope : Finset (Cal.Group C) := roleScope.image (Cal.groupOf C)
    have hScopesClosed : ∀ r ∈ roleScope, Cal.groupOf C r ∈ groupScope := by
      intro r hr
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    let recordsLocal : R.Hist C → (∀ r, Ssol.Val r) :=
      fun W => records sourceSlice (W sourceSlice)
    have hPriorIdentity (W : R.Hist C) (ys : OddCellRole H.geom C → Fin (T.S.N k)) :
        R.rawPrior C W ys v =
          Ssol.σ w (recordsLocal W) (fun j => ys (starRole j)) := by
      let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
      have hread := hpriorReadout W sourceSlice w ys fallback
      rw [hCellWordVal] at hread
      have hlabels :
          nbrLabels w.1 (R.wordLabel C ys sourceSlice fallback) = fun j => ys (starRole j) := by
        funext j
        have hflip := R.word_flip C sourceSlice word j
        rw [hCellWordVal] at hflip
        have hOddCellWord :
            ¬ IsEvenRole ((R.cellWords C (sourceSlice, flipPos word j)).1) := by
          rw [hflip]
          exact hStarOdd j
        simp only [nbrLabels, w]
        change R.wordLabel C ys sourceSlice fallback (flipPos word j) = ys (starRole j)
        unfold CellRawData.wordLabel
        rw [dif_pos hOddCellWord]
        apply congrArg ys
        apply Subtype.ext
        exact hflip
      rw [hread, hlabels]
    -- The source slice and the `h` star roles now identify the local solver
    -- experiment. Finish the product projection, calibrated-stage bounds,
    -- and denominator budgets using this scope.
    sorry
  · obtain ⟨hGroupInj, hValueUnit, hPassAll, hQUniform, hPretrimAll,
      hUDirect, hEnvExists⟩ := hDirectData C
    obtain ⟨hEnv, hRawPrior⟩ := hEnvExists
    let priorLaw := Law.unifCore (PT.envelope (H.geom.cellPatch C)) hEnv
    let histMap : Cal.Hist C → Cal.Hist C × Unit := fun W => (W, ())
    let histLaw : FinLaw (Cal.Hist C × Unit) := FinLaw.map (Cal.history C) histMap
    let histGate (pool : F.Pool C) : Finset (Cal.Hist C × Unit) :=
      Finset.univ.filter fun z => z.1 ∈ Cal.gate C pool
    have hSlicePos : 0 < ∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
        (Cal.history C).w W := by
      have hsum : (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
          (Cal.history C).w W) = 1 := by simpa using (Cal.history C).sum_one
      rw [hsum]
      norm_num
    have hCalHistSum : ∑ W, (Cal.history C).w W = 1 := (Cal.history C).sum_one
    have hHistWeight (W : Cal.Hist C) : histLaw.w (W, ()) = (Cal.history C).w W := by
      simp [histLaw, histMap, FinLaw.map]
    have hGatedWeight (pool : F.Pool C) (W : Cal.Hist C) :
        (FinLaw.map (Cal.gatedHistory C pool) histMap).w (W, ()) =
          (Cal.gatedHistory C pool).w W := by
      simp [FinLaw.map, histMap]
    have hGateMass (pool : F.Pool C) :
        (∑ z ∈ histGate pool, histLaw.w z) =
          ∑ W ∈ Cal.gate C pool, (Cal.history C).w W := by
      calc
        (∑ z ∈ histGate pool, histLaw.w z) =
            histLaw.pr (fun z => z ∈ histGate pool) :=
          (Lane_q_s16_prod2.finLaw_pr_finset histLaw (histGate pool)).symm
        _ = (Cal.history C).pr (fun W => W ∈ Cal.gate C pool) := by
          rw [Lane_q_s16_prod2.finLaw_map_pr]
          simp [histGate, histMap]
        _ = ∑ W ∈ Cal.gate C pool, (Cal.history C).w W :=
          Lane_q_s16_prod2.finLaw_pr_finset (Cal.history C) (Cal.gate C pool)
    have hGatePos (pool : F.Pool C) (ht : F.typical C pool) :
        0 < ∑ z ∈ histGate pool, histLaw.w z := by
      rw [hGateMass]
      exact Cal.gate_pos C pool ht
    let gatedLaw (pool : F.Pool C) (ht : F.typical C pool) :=
      FinLaw.cond histLaw (histGate pool) (hGatePos pool ht)
    let encodePipe : (Cal.Hist C × Unit) ×
        ((Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
        (OddCellRole H.geom C → Fin (T.S.N k))) → F.State C := fun z =>
      Cal.encode C (z.1.1, z.2.1, z.2.2)
    let binPipe (pool : F.Pool C) (z : Cal.Hist C × Unit) :=
      Cal.binSampler C pool z.1
    let labelPipe (pool : F.Pool C) (z : Cal.Hist C × Unit)
        (a : Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) :=
      Cal.labelSampler C pool z.1 a
    let P : FreshPriorPipeline F C v := {
      LocalHist := Cal.Hist C
      localFin := Cal.histFin C
      localDec := Cal.histDec C
      Aux := Unit
      auxFin := inferInstance
      Group := Cal.Group C
      groupFin := Cal.groupFin C
      groupDec := Cal.groupDec C
      Role := OddCellRole H.geom C
      roleFin := inferInstance
      roleDec := inferInstance
      baseHistory := Cal.history C
      slicePass := Finset.univ
      slice_pos := hSlicePos
      auxHistory := FinLaw.dirac ()
      history := histLaw
      history_eq := by
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        simp [histLaw, histMap, FinLaw.map, FinLaw.bind, FinLaw.cond,
          FinLaw.dirac, hCalHistSum]
      gate := histGate
      gate_pos := hGatePos
      gatedHistory := fun pool => FinLaw.map (Cal.gatedHistory C pool) histMap
      gated_eq := by
        intro pool ht
        apply Lane_q_s16_prod2.finLaw_ext
        intro z
        rcases z with ⟨W, u⟩
        cases u
        rw [hGatedWeight pool W, Cal.gated_eq C pool ht]
        simp only [FinLaw.cond]
        rw [hGateMass pool]
        simp [histGate, hHistWeight]
        by_cases hmem : W ∈ Cal.gate C pool <;> simp [hmem]
      qraw := fun W g => Cal.qin C W g
      U := fun W g D => Cal.U C W g D
      U_support := Cal.U_support C
      groupOf := Cal.groupOf C
      rolePosition := fun r => r.1
      role_cell := fun r => r.2.1
      role_odd := fun r => r.2.2
      groupScope := ∅
      roleScope := ∅
      scopes_closed := by intro r hr; simp at hr
      rawPrior := fun W ys y => priorLaw.w y
      prior_local := by intro W ys ys' hys; rfl
      pretrim := fun _ _ => Finset.univ
      permitted := Cal.permitted C
      qtilde := Cal.qtilde C
      qtilde_eq := by
        intro pool W g D ht hW hbase
        rw [Cal.qtilde_eq C pool W g D ht hbase]
        simp [Finset.univ_inter, Finset.inter_univ]
      binSampler := binPipe
      labelSampler := labelPipe
      groupRate := 0
      labelRate := 0
      rates_nonneg := by norm_num
      bin_joint := by
        intro pool W a ht hW
        simp [Lane_q_s16_prod2.finLaw_pr_const]
      bins_distinct := by
        intro pool W a ht hW ha
        simp
      label_joint := by
        intro pool W a ys ht hW ha
        simp [Lane_q_s16_prod2.finLaw_pr_const]
      encode := encodePipe
      fresh_eq := by
        intro pool ht
        rw [Cal.fresh_eq C pool ht]
        apply Lane_q_s16_prod2.finLaw_ext
        intro s
        simp only [FinLaw.map, FinLaw.bind]
        let StageState := (Cal.Group C → Bin PT.tiling (H.geom.cellPatch C)) ×
          (OddCellRole H.geom C → Fin (T.S.N k))
        let dropUnit : (Cal.Hist C × StageState) ≃ ((Cal.Hist C × Unit) × StageState) := {
          toFun := fun z => ((z.1, ()), z.2)
          invFun := fun z => (z.1.1, z.2)
          left_inv := by intro z; rfl
          right_inv := by intro z; rcases z with ⟨⟨W, u⟩, a⟩; cases u; rfl }
        apply Fintype.sum_equiv dropUnit
        intro z
        rcases z with ⟨W, a⟩
        simp [FinLaw.map, FinLaw.bind, encodePipe, binPipe, labelPipe,
          histMap, dropUnit, hGatedWeight pool W]
      prior_eq := by
        intro pool W a ys ht hW ha hys
        have hMapW : ((Cal.gatedHistory C pool).map histMap).w W =
            (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hMapW]
          exact hW
        have hPrior := hLink.prior_eq C pool W.1 a ys v ht hWCal ha hys hcell hEven
        rw [hPrior]
        exact hRawPrior (hLink.histories C W.1) ys v hcell hEven
      label_eq := by
        intro pool W a ys r ht hW ha hys
        have hMapW : ((Cal.gatedHistory C pool).map histMap).w W =
            (Cal.gatedHistory C pool).w W.1 := by
          rcases W with ⟨W, u⟩
          cases u
          simp [FinLaw.map, histMap]
        have hWCal : (Cal.gatedHistory C pool).w W.1 ≠ 0 := by
          rw [← hMapW]
          exact hW
        exact Cal.label_eq C pool W.1 a ys r ht hWCal ha hys
      δgate := Cal.δgate
      δpre := 0
      δperm := 0
      error_ranges := by
        exact ⟨⟨Cal.gate_range.1, Cal.gate_range.2⟩,
          ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
      gate_mass := by
        intro pool ht
        rw [hGateMass]
        exact Cal.gate_mass C pool ht
      pretrim_mass := by intro W g hW hbase hg; simp at hg
      permission_mass := by intro W g hW hbase hg; simp at hg
      normalizer_mass := by intro pool W g ht hW hbase hg; simp at hg
      slot_pos := by
        change 0 < H.data.cells.nslot C
        have hDirectD1 (i : Fin PT.tiling.m) : (PT.tiling.P i).d = 1 := by
          cases hmode : PT.tiling.mode with
          | bounded =>
              have hdata := Q.profiled_valid.tiling_valid.bounded_data hmode
              exact (hdata.2 i).2.2.1
          | lowDirect =>
              have hdata := Q.profiled_valid.tiling_valid.direct_data (Or.inl hmode) i
              exact hdata.2.2.2.2.2.1
          | lowCluster =>
              have hc : PT.tiling.mode.isCluster := by rw [hmode]; simp [Mode.isCluster]
              exact (hDirect hc).elim
          | highDirect | highSmall | highLarge =>
              have hlow := Q.mode_low
              rw [hmode] at hlow
              have hfalse : False := by simpa [Mode.isLow] using hlow
              exact hfalse.elim
        have hnR : 0 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) Q.n_large)
        have hTheta : 0 < κ.θstar := hκ.bucket.2.2.2.2
        have hKcell : 0 < κ.Kcell :=
          lt_of_lt_of_le (div_pos (by norm_num : (0 : ℝ) < 100) hTheta) hκ.Kcell_big
        rw [H.cell_partition.slot_count C]
        rw [hDirectD1 (H.data.cells.cellPatch C)]
        have hRpow : 0 < Real.rpow (T.S.n k : ℝ) (κ.Ac : ℝ) :=
          Real.rpow_pos_of_pos hnR _
        have hnum : 0 < κ.Kcell * Real.rpow (T.S.n k : ℝ) (κ.Ac : ℝ) / 1 := by
          rw [hκ.Ac_eq]
          exact div_pos (mul_pos hKcell (Real.rpow_pos_of_pos hnR _)) (by norm_num)
        exact Nat.ceil_pos.mpr (by simpa using hnum)
      stage_cost := by
        have hδg := Cal.gate_range
        have hδp := Cal.perm_range
        have hnR : 1 < (T.S.n k : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) Q.n_large)
        have hnNonneg : 0 ≤ (T.S.n k : ℝ) := le_of_lt (lt_trans (by norm_num) hnR)
        have hpow3eq : (T.S.n k : ℝ) ^ (-3 : ℝ) =
            ((T.S.n k : ℝ) ^ 3)⁻¹ := by
          calc
            (T.S.n k : ℝ) ^ (-3 : ℝ) =
                ((T.S.n k : ℝ) ^ (3 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt (by linarith)) 3
            _ = ((T.S.n k : ℝ) ^ 3)⁻¹ :=
              congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (T.S.n k : ℝ) 3)
        have hpow4eq : (T.S.n k : ℝ) ^ (-4 : ℝ) =
            ((T.S.n k : ℝ) ^ 4)⁻¹ := by
          calc
            (T.S.n k : ℝ) ^ (-4 : ℝ) =
                ((T.S.n k : ℝ) ^ (4 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt (by linarith)) 4
            _ = ((T.S.n k : ℝ) ^ 4)⁻¹ :=
              congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (T.S.n k : ℝ) 4)
        have hnR2 : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast Q.n_large
        have hn3 : 1 ≤ (T.S.n k : ℝ) ^ 3 := by
          calc
            1 ≤ (2 : ℝ) ^ 3 := by norm_num
            _ ≤ (T.S.n k : ℝ) ^ 3 := by gcongr
        have hn4 : 1 < (T.S.n k : ℝ) ^ 4 := by
          calc
            1 < (2 : ℝ) ^ 4 := by norm_num
            _ ≤ (T.S.n k : ℝ) ^ 4 := by gcongr
        have hnPow3Le : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 := by
          rw [hpow3eq]
          exact inv_le_one_of_one_le₀ hn3
        have hnPow4Lt : (T.S.n k : ℝ) ^ (-4 : ℝ) < 1 := by
          rw [hpow4eq]
          exact inv_lt_one_of_one_lt₀ hn4
        have hdenG : 0 < 1 - Cal.δgate := by linarith [hδg.2]
        have hdenP : 0 < 1 - Cal.δperm := by linarith [hδp.2]
        have hdenN : 0 < 1 - (T.S.n k : ℝ) ^ (-4 : ℝ) := by linarith
        have hInvP : 1 ≤ (1 - Cal.δperm)⁻¹ :=
          (one_le_inv₀ hdenP).2 (by linarith [hδp.1])
        have hnPow4Nonneg : 0 ≤ (T.S.n k : ℝ) ^ (-4 : ℝ) := by positivity
        have hInvN : 1 ≤ (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ :=
          (one_le_inv₀ hdenN).2 (by linarith [hnPow4Nonneg])
        have hInvGpos : 0 < (1 - Cal.δgate)⁻¹ := inv_pos.mpr hdenG
        have hCost := Cal.cost_budget
        have hBC : 1 ≤ (1 - Cal.δperm)⁻¹ *
            (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ := by
          calc
            1 = (1 : ℝ) * 1 := by ring
            _ ≤ (1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ :=
              mul_le_mul hInvP hInvN (by norm_num) (by positivity)
        have hThree : (1 - Cal.δgate)⁻¹ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
          calc
            (1 - Cal.δgate)⁻¹ = (1 - Cal.δgate)⁻¹ * 1 := by ring
            _ ≤ (1 - Cal.δgate)⁻¹ * ((1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹) :=
              mul_le_mul_of_nonneg_left hBC hInvGpos.le
            _ = (1 - Cal.δgate)⁻¹ * (1 - Cal.δperm)⁻¹ *
                (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ := by ring
            _ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := hCost
        have hGateSmall : (1 - Cal.δgate)⁻¹ ≤ 2 := by linarith [hThree, hnPow3Le]
        rcases hκ.bucket with ⟨hKp, hcp, hKpTheta, hcpTheta, hTheta⟩
        rcases hκ.clock with ⟨_, hTheta0, _⟩
        have hKpR : (40 : ℝ) ≤ (κ.Kp : ℝ) := by exact_mod_cast hKp
        have hProdLo : 40 * κ.θstar ≤ (κ.Kp : ℝ) * κ.θstar := by
          exact mul_le_mul_of_nonneg_right hKpR hTheta.le
        have hThetaBound : κ.θstar ≤ 1 := by
          rw [hTheta0] at hKpTheta
          nlinarith
        have hInvTheta : 1 ≤ κ.θstar⁻¹ := (one_le_inv₀ hTheta).2 hThetaBound
        have hKcell100 : 100 ≤ κ.Kcell := by
          have hBig := hκ.Kcell_big
          rw [div_eq_mul_inv] at hBig
          have hle : 100 ≤ 100 * κ.θstar⁻¹ := by nlinarith
          exact le_trans hle hBig
        have hFinal : (1 - Cal.δgate)⁻¹ ≤ 10 * κ.Kcell := by
          linarith [hGateSmall, hKcell100]
        simpa [Finset.card_empty] using hFinal
      slice_cost := by
        have hKp : (40 : ℝ) ≤ (κ.Kp : ℝ) := by exact_mod_cast hκ.bucket.1
        have hsum : (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)),
            (Cal.history C).w W) = 1 := by simpa using (Cal.history C).sum_one
        calc
          (∑ W ∈ (Finset.univ : Finset (Cal.Hist C)), (Cal.history C).w W)⁻¹ = 1 := by
            rw [hsum]
            norm_num
          _ ≤ 10 * (κ.Kp : ℝ) := by nlinarith
    }
    refine ⟨P, ?_, ?_⟩
    · exact Or.inr ⟨hDirect, hEnv, by intro W ys; simp [P, priorLaw]⟩
    · intro Φ
      have hPprior (z : P.baseExperiment.State) : P.baseExperiment.prior z = priorLaw.w := by
        rfl
      have hRprior (z : (R.baseExperiment C v).State) :
          (R.baseExperiment C v).prior z = priorLaw.w := by
        exact hRawPrior z.1 z.2.2 v hcell hEven
      have hConstP : P.baseExperiment.law.E (fun _ => Φ priorLaw.w) = Φ priorLaw.w := by
        unfold FinLaw.E
        rw [← Finset.sum_mul, P.baseExperiment.law.sum_one]
        ring
      have hConstR : (R.baseExperiment C v).law.E (fun _ => Φ priorLaw.w) = Φ priorLaw.w := by
        unfold FinLaw.E
        rw [← Finset.sum_mul, (R.baseExperiment C v).law.sum_one]
        ring
      calc
        P.baseExperiment.expect Φ = P.baseExperiment.law.E (fun _ => Φ priorLaw.w) := by
          unfold PriorExperiment.expect
          apply Lane_q_s16_prod2.finLaw_E_congr_of_supported
          intro z hz
          simp [hPprior z]
        _ = Φ priorLaw.w := hConstP
        _ = (R.baseExperiment C v).expect Φ := by
          symm
          calc
            (R.baseExperiment C v).expect Φ =
                (R.baseExperiment C v).law.E (fun _ => Φ priorLaw.w) := by
              unfold PriorExperiment.expect
              apply Lane_q_s16_prod2.finLaw_E_congr_of_supported
              intro z hz
              simp [hRprior z]
            _ = Φ priorLaw.w := hConstR

end Lane_sol_fix2_s16
end HypercubeRamsey.S16
