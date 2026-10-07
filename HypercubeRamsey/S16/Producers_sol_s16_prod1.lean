import HypercubeRamsey.S16.Producers_q_s16_prod1
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.S16.Comparisons
import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.FinProbLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

namespace HypercubeRamsey.S16.Lane_sol_s16_prod1

open Classical
open scoped BigOperators
open Filter
open Lane_q_s16_prod1

theorem flip_parity {n : ℕ} (z : CubePos n) (j : Fin n) :
    IsEvenRole (flipPos z j) ↔ ¬ IsEvenRole z := by
  have heq : flipPos z j = cubeFlip z j := by
    funext a
    by_cases ha : a = j <;> simp [flipPos, cubeFlip, ha]
  rw [heq]
  exact cubeFlip_parity z j

theorem shift_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) (a : Fin (PT.tiling.P (G.cellPatch C)).h) :
    clusterShiftWord s (flipPos z a) hp = flipPos (clusterShiftWord s z hp) a := by
  by_cases hs : IsEvenRole s.1
  · simp [clusterShiftWord, hs]
  · simp only [clusterShiftWord, hs, ↓reduceDIte]
    by_cases ha : a = (⟨0, hp⟩ : Fin _)
    · subst a
      rfl
    funext j
    by_cases hj : j = a <;> by_cases hj0 : j = (⟨0, hp⟩ : Fin _) <;>
      simp [flipPos, Function.update_apply, hj, hj0, ha, Ne.symm ha]

theorem combine_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) (a : Fin (PT.tiling.P (G.cellPatch C)).h) :
    clusterCombine hh s (flipPos z a) hp =
      flipPos (clusterCombine hh s z hp) (cellAxis (G.cellPatch C) hh a) := by
  funext j
  by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
  · have hi : cellAxisInv (G.cellPatch C) hh j hj = a ↔
        j = cellAxis (G.cellPatch C) hh a := by
      constructor
      · intro h
        rw [← cellAxisInv_axis (G.cellPatch C) hh j hj, h]
      · intro h
        apply cellAxis_injective (G.cellPatch C) hh
        rw [cellAxisInv_axis, h]
    have hm : cellAxis (G.cellPatch C) hh a ∈ PT.tiling.Icoord (G.cellPatch C) := by
      rw [← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp only [clusterCombine, dif_pos hj]
    rw [shift_flip]
    by_cases hja : j = cellAxis (G.cellPatch C) hh a
    · subst j
      simp [clusterCombine, hm, flipPos, cellAxisInv_cellAxis]
    · have hia := mt hi.mp hja
      simp [clusterCombine, hj, flipPos, hja, hia]
  · have hne : j ≠ cellAxis (G.cellPatch C) hh a := by
      intro h
      apply hj
      rw [h, ← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp [clusterCombine, hj, flipPos, hne]

theorem combine_parity {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {C : G.Cell}
    (hh : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (s : ClusterCellSlice G C) (z : IWord PT.tiling (G.cellPatch C))
    (hp : 0 < (PT.tiling.P (G.cellPatch C)).h) :
    IsEvenRole (clusterCombine hh s z hp) ↔ IsEvenRole z := by
  let A := Finset.univ.filter fun j : Fin (T.S.n k) => s.1 j = true
  let B := Finset.univ.filter fun a : Fin (PT.tiling.P (G.cellPatch C)).h =>
    clusterShiftWord s z hp a = true
  have hdis : Disjoint A (B.image (cellAxis (G.cellPatch C) hh)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have hm : cellAxis (G.cellPatch C) hh a ∈ PT.tiling.Icoord (G.cellPatch C) := by
      rw [← cellAxis_image (G.cellPatch C) hh]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have := s.2.2 _ hm
    simpa [A, this] using hj
  have hset : (Finset.univ.filter fun j => clusterCombine hh s z hp j = true) =
      A ∪ B.image (cellAxis (G.cellPatch C) hh) := by
    ext j
    by_cases hj : j ∈ PT.tiling.Icoord (G.cellPatch C)
    · have hs := s.2.2 j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image]
      simp only [clusterCombine, hj, ↓reduceDIte, A, Finset.mem_filter,
        Finset.mem_univ, true_and, hs, Bool.false_eq_true, false_or]
      constructor
      · intro h
        exact ⟨cellAxisInv (G.cellPatch C) hh j hj, by simpa [B] using h,
          cellAxisInv_axis (G.cellPatch C) hh j hj⟩
      · rintro ⟨a, ha, heq⟩
        have hai : a = cellAxisInv (G.cellPatch C) hh j hj := by
          apply cellAxis_injective (G.cellPatch C) hh
          rw [heq, cellAxisInv_axis]
        simpa [B, hai] using ha
    · have hnot : j ∉ B.image (cellAxis (G.cellPatch C) hh) := by
        intro hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        apply hj
        rw [← cellAxis_image (G.cellPatch C) hh]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hnot,
        or_false]
      simp [clusterCombine, hj, A]
  change Even (Finset.univ.filter fun j => clusterCombine hh s z hp j = true).card ↔ _
  rw [hset, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (cellAxis_injective (G.cellPatch C) hh)]
  by_cases hs : IsEvenRole s.1
  · have hA : Even A.card := hs
    have hB : B = Finset.univ.filter fun a => z a = true := by
      simp [B, clusterShiftWord, hs]
    rw [hB]
    rw [Nat.even_add]
    simp only [hA, true_iff]
    rfl
  · have hA : ¬ Even A.card := hs
    have hB : Even B.card ↔ ¬ IsEvenRole z := by
      change IsEvenRole (clusterShiftWord s z hp) ↔ ¬ IsEvenRole z
      rw [clusterShiftWord, dif_neg hs]
      exact flip_parity z ⟨0, hp⟩
    have hadd : Even (A.card + B.card) ↔ (Even A.card ↔ Even B.card) := Nat.even_add
    rw [hadd, hB]
    tauto

theorem map_refl {α : Type*} [Fintype α] [DecidableEq α] (P : FinLaw α) :
    FinLaw.map P (Equiv.refl α).symm = P := by
  cases P
  unfold FinLaw.map
  congr 1
  funext a
  simp [eq_comm]

theorem solver_good_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hv : PT.Valid) (hm : PT.tiling.mode = .lowCluster)
    {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) :
    0 < (S.recLaw PT.parameter).pr S.AllGood := by
  have hnonneg : 0 ≤ (S.recLaw PT.parameter).pr S.AllGood := by
    apply Finset.sum_nonneg
    intro W hW
    split_ifs <;> first | exact (S.recLaw PT.parameter).nonneg W | exact le_rfl
  by_contra h
  have hz : (S.recLaw PT.parameter).pr S.AllGood = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hzero : ∀ y, (PT.π i).w y = 0 := by
    intro y
    rw [hv.low_profile hm i S hS (S.groupOf (fun _ => false)) y]
    simp [SliceSolver.lowOut, hz]
  have := (PT.π i).sum_eq_one
  simp only [hzero, Finset.sum_const_zero] at this
  norm_num at this

theorem solver_qin_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {i : Fin PT.tiling.m}
    (S : SliceSolver κ PT.tiling i PT.mesh) (W : ∀ r, S.Val r)
    (g : HypercubeRamsey.Group PT.tiling i) :
    (∑ D, S.qin W g D) = if (∑ D ∈ S.pretrimBins W g, S.q g W D) = 0 then 0 else 1 := by
  unfold SliceSolver.qin
  by_cases hz : (∑ D ∈ S.pretrimBins W g, S.q g W D) = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hdiv : ∀ D, (if D ∈ S.pretrimBins W g then S.q g W D / (∑ D' ∈ S.pretrimBins W g, S.q g W D') else 0) =
      (if D ∈ S.pretrimBins W g then S.q g W D else 0) / (∑ D' ∈ S.pretrimBins W g, S.q g W D')
        := by intro D; split_ifs <;> simp
    simp_rw [hdiv]
    rw [← Finset.sum_div]
    simp [Finset.sum_ite_mem, hz]

theorem solver_pretrim_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hv : PT.Valid) (hm : PT.tiling.mode = .lowCluster)
    {i : Fin PT.tiling.m} (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) (W : ∀ r, S.Val r)
    (hW : S.AllGood W) (hpW : (S.recLaw PT.parameter).w W ≠ 0)
    (g : HypercubeRamsey.Group PT.tiling i) :
    0 < ∑ D ∈ S.pretrimBins W g, S.q g W D := by
  let P := S.recLaw PT.parameter
  let mass := fun W' => ∑ D ∈ S.pretrimBins W' g, S.q g W' D
  let f := fun W' => if mass W' = 0 then (0 : ℝ) else 1
  have ha : 0 < P.pr S.AllGood := solver_good_pos hv hm S hS
  have hf : ∀ W', 0 ≤ f W' ∧ f W' ≤ 1 := by
    intro W'
    dsimp [f]
    split_ifs <;> norm_num
  have hnorm : (∑ W', P.w W' * (if S.AllGood W' then f W' else 0)) = P.pr S.AllGood := by
    have hsum := (PT.π i).sum_eq_one
    simp_rw [hv.low_profile hm i S hS g] at hsum
    unfold SliceSolver.lowOut at hsum
    rw [← Finset.sum_div] at hsum
    have heq : (∑ y, ∑ W', P.w W' *
        (if S.AllGood W' then ∑ D, S.qin W' g D * S.U g W' D y else 0)) =
        ∑ W', P.w W' * (if S.AllGood W' then f W' else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W' hW'
      rw [← Finset.mul_sum]
      congr 1
      by_cases hg : S.AllGood W'
      · simp only [hg, ↓reduceIte]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, S.U_sum, mul_one]
        exact solver_qin_sum S W' g
      · simp [hg]
    change (∑ y, ∑ W', P.w W' *
      (if S.AllGood W' then ∑ D, S.qin W' g D * S.U g W' D y else 0)) /
        P.pr S.AllGood = 1 at hsum
    rw [heq] at hsum
    exact (div_eq_one_iff_eq (ne_of_gt ha)).mp hsum
  have hdef : (∑ W', ((if S.AllGood W' then P.w W' else 0) -
      P.w W' * (if S.AllGood W' then f W' else 0))) = 0 := by
    rw [Finset.sum_sub_distrib, hnorm]
    simp [FinLaw.pr]
  have hn : ∀ W', 0 ≤ (if S.AllGood W' then P.w W' else 0) -
      P.w W' * (if S.AllGood W' then f W' else 0) := by
    intro W'
    by_cases hg : S.AllGood W'
    · simp only [hg, ↓reduceIte]
      nlinarith [P.nonneg W', (hf W').2]
    · simp [hg]
  have hterm := Finset.single_le_sum (fun W' _ => hn W') (Finset.mem_univ W)
  rw [hdef] at hterm
  have hnonneg : 0 ≤ mass W := Finset.sum_nonneg fun D _ => S.q_nonneg g W D
  by_contra h
  have hz : mass W = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hpos : 0 < P.w W := lt_of_le_of_ne (P.nonneg W) (Ne.symm hpW)
  simp [hW, f, hz] at hterm
  linarith

theorem pr_range {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ P.pr A ∧ P.pr A ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg fun ω _ => by
      split_ifs <;> first | exact P.nonneg ω | exact le_rfl
  · calc
      P.pr A ≤ ∑ ω, P.w ω := by
        apply Finset.sum_le_sum
        intro ω _
        split_ifs <;> first | exact le_rfl | exact P.nonneg ω
      _ = 1 := P.sum_one

theorem pi_coordinate_E {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinLaw Ω) (i : I) (f : Ω → ℝ) :
    (FinLaw.pi P).E (fun x => f (x i)) = (P i).E f := by
  classical
  let F : I → Ω → ℝ := fun j y => (P j).w y * (if j = i then f y else 1)
  have hprod (x : I → Ω) :
      (∏ j, F j (x j)) = (∏ j, (P j).w (x j)) * f (x i) := by
    dsimp only [F]
    rw [Finset.prod_mul_distrib]
    simp
  have hrow (j : I) : (∑ y, F j y) = if j = i then (P i).E f else 1 := by
    by_cases hji : j = i
    · subst j
      simp [F, FinLaw.E]
    · simp [F, hji, (P j).sum_one]
  calc
    (FinLaw.pi P).E (fun x => f (x i)) = ∑ x : I → Ω, ∏ j, F j (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hprod x).symm
    _ = ∏ j, ∑ y, F j y := (Fintype.prod_sum _).symm
    _ = (P i).E f := by simp [hrow]

theorem pi_support {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (x : ∀ i, Ω i)
    (hx : (FinLaw.pi P).w x ≠ 0) (i : I) : (P i).w (x i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)

theorem cond_support {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A : Finset Ω) (hA : 0 < ∑ ω ∈ A, P.w ω) (ω : Ω)
    (hω : (FinLaw.cond P A hA).w ω ≠ 0) : ω ∈ A ∧ P.w ω ≠ 0 := by
  classical
  constructor
  · by_contra hn
    simp [FinLaw.cond, hn] at hω
  · intro hz
    simp [FinLaw.cond, hz] at hω

theorem flip_twice {n : ℕ} (z : CubePos n) (j : Fin n) :
    flipPos (flipPos z j) j = z := by
  funext a
  by_cases ha : a = j <;> simp [flipPos, ha]

theorem solver_incident_count {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    (g : HypercubeRamsey.Group 𝒯 i) :
    (Finset.univ.filter fun v : EvenRole 𝒯 i => SliceSolver.Incident v g).card ≤
      (𝒯.P i).h ^ 2 := by
  classical
  let V := Finset.univ.filter fun v : EvenRole 𝒯 i => SliceSolver.Incident v g
  let images : Finset (IWord 𝒯 i) :=
    Finset.univ.image fun jl : Fin (𝒯.P i).h × Fin (𝒯.P i).h =>
      flipPos (flipPos g.1 jl.1) jl.2
  have hsub : V.image Subtype.val ⊆ images := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨j, _hj, heq⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨(j, l), Finset.mem_univ _, ?_⟩
    rw [heq, flip_twice]
  calc
    V.card = (V.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ images.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (𝒯.P i).h × Fin (𝒯.P i).h)).card :=
      Finset.card_image_le
    _ = (𝒯.P i).h ^ 2 := by simp [pow_two]

/-- Union/Markov calculation before any physical-cell transport. -/
theorem solver_pretrim_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (hW : S.AllGood W)
    (g : HypercubeRamsey.Group 𝒯 i)
    (heps : 0 < sliceEps κ (𝒯.P i).h) :
    1 - ((𝒯.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
      ∑ D ∈ S.pretrimBins W g, S.q g W D := by
  classical
  let t := Real.sqrt (sliceEps κ (𝒯.P i).h)
  let V := Finset.univ.filter fun v : EvenRole 𝒯 i => SliceSolver.Incident v g
  let m := fun (v : EvenRole 𝒯 i) (D : Bin 𝒯 i) =>
    (S.refLaw W).pr (fun ω => ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0)
  have ht : 0 < t := Real.sqrt_pos.mpr heps
  have hm0 : ∀ v D, 0 ≤ m v D := fun v D => (pr_range _ _).1
  have hmSum : ∀ v, ∑ D, m v D ≤ sliceEps κ (𝒯.P i).h := by
    intro v
    have heq : (∑ D, m v D) =
        (S.refLaw W).pr (fun ω => S.σ v W (nbrLabels v.1 ω.2) = 0) := by
      unfold m FinLaw.pr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hf : S.σ v W (nbrLabels v.1 ω.2) = 0
      · simp [hf, eq_comm]
      · simp [hf]
    rw [heq]
    exact S.Hgood_zero v W (hW v)
  have hbad : ∀ D, D ∉ S.pretrimBins W g →
      S.q g W D ≤ (∑ v ∈ V, m v D) / t := by
    intro D hD
    by_cases hq : 0 < S.q g W D
    · have hfail : ∃ v : EvenRole 𝒯 i, SliceSolver.Incident v g ∧ t * S.q g W D < m v D := by
        simpa [SliceSolver.pretrimBins, t, m, hq, not_forall, not_le] using hD
      obtain ⟨v, hv, hlt⟩ := hfail
      have hvV : v ∈ V := by simp [V, hv]
      have hle := Finset.single_le_sum (s := V) (f := fun v => m v D)
        (fun v _ => hm0 v D) hvV
      exact (le_div_iff₀ ht).mpr (by nlinarith)
    · have hzero : S.q g W D = 0 := le_antisymm (le_of_not_gt hq) (S.q_nonneg g W D)
      rw [hzero]
      exact div_nonneg (Finset.sum_nonneg fun v _ => hm0 v D) ht.le
  have hremoved : (∑ D ∈ Finset.univ \ S.pretrimBins W g, S.q g W D) ≤
      (V.card : ℝ) * t := by
    calc
      (∑ D ∈ Finset.univ \ S.pretrimBins W g, S.q g W D) ≤
          ∑ D ∈ Finset.univ \ S.pretrimBins W g, (∑ v ∈ V, m v D) / t := by
        apply Finset.sum_le_sum
        intro D hD
        exact hbad D (Finset.mem_sdiff.mp hD).2
      _ ≤ ∑ D, (∑ v ∈ V, m v D) / t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        intro D _ _
        exact div_nonneg (Finset.sum_nonneg fun v _ => hm0 v D) ht.le
      _ = (∑ v ∈ V, ∑ D, m v D) / t := by
        rw [← Finset.sum_div, Finset.sum_comm]
      _ ≤ ((V.card : ℝ) * sliceEps κ (𝒯.P i).h) / t := by
        apply div_le_div_of_nonneg_right _ ht.le
        simpa using Finset.sum_le_sum (s := V) (fun v _ => hmSum v)
      _ = (V.card : ℝ) * t := by
        have hs := Real.sq_sqrt heps.le
        change (V.card : ℝ) * sliceEps κ (𝒯.P i).h / t = (V.card : ℝ) * t
        apply (div_eq_iff (ne_of_gt ht)).mpr
        dsimp [t] at *
        nlinarith
  have hcard : (V.card : ℝ) ≤ ((𝒯.P i).h : ℝ) ^ 2 := by
    exact_mod_cast solver_incident_count g
  have hsplit := Finset.sum_sdiff (s₁ := S.pretrimBins W g) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := S.q g W)
  rw [S.q_sum] at hsplit
  have hbound := mul_le_mul_of_nonneg_right hcard ht.le
  dsimp [t] at *
  linarith

theorem calibration_power_bounds (d : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d) :
    Real.rpow (d : ℝ) (-0.1) ≤ 1 / 3 ∧
      Real.rpow (d : ℝ) (-0.02) ≤ 1 / 3 := by
  have hbase : (10 : ℝ) ^ (100 : ℕ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpow : ∀ a : ℝ,
      Real.rpow ((10 : ℝ) ^ (100 : ℕ)) a = Real.rpow 10 (100 * a) := by
    intro a
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 a).symm
  constructor
  · calc
      Real.rpow (d : ℝ) (-0.1) ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
      _ ≤ 1 / 3 := by rw [hpow]; norm_num [Real.rpow_neg, Real.rpow_natCast]
  · calc
      Real.rpow (d : ℝ) (-0.02) ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.02) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
      _ ≤ 1 / 3 := by rw [hpow]; norm_num [Real.rpow_neg, Real.rpow_natCast]

theorem calibration_price_gap (d : ℕ) (hd : 10 ≤ d) (a : ℝ) (ha : a ≤ 1) :
    4 * Real.rpow (d : ℝ) (-2) < Real.rpow (d : ℝ) (-a) := by
  have hdreal : (10 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have heq : Real.rpow (d : ℝ) (-2) =
      Real.rpow (d : ℝ) (-a) * Real.rpow (d : ℝ) (-2 + a) := by
    calc
      Real.rpow (d : ℝ) (-2) = Real.rpow (d : ℝ) ((-a) + (-2 + a)) := by congr 1; ring
      _ = _ := Real.rpow_add hdpos _ _
  have hlt : Real.rpow (d : ℝ) (-2 + a) < 1 / 4 := by
    calc
      Real.rpow (d : ℝ) (-2 + a) ≤ Real.rpow (d : ℝ) (-1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (d : ℝ) := by simpa only [Real.rpow_eq_pow, one_div] using Real.rpow_neg_one (d : ℝ)
      _ < 1 / 4 := (div_lt_iff₀ hdpos).mpr (by linarith)
  have hp : 0 < Real.rpow (d : ℝ) (-a) := Real.rpow_pos_of_pos hdpos (-a)
  rw [heq]
  have hproduct : Real.rpow (d : ℝ) (-a) * Real.rpow (d : ℝ) (-2 + a) <
      Real.rpow (d : ℝ) (-a) * (1 / 4) := mul_lt_mul_of_pos_left hlt hp
  nlinarith

theorem pr_eq_indicator_E {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = P.E (fun ω => if A ω then 1 else 0) := by
  classical
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h]

set_option maxHeartbeats 400000 in
theorem pi_E_local {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (P Q : I → FinLaw Ω) (S : Finset I) (f : (I → Ω) → ℝ)
    (hf : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hPQ : ∀ i ∈ S, P i = Q i) : (FinLaw.pi P).E f = (FinLaw.pi Q).E f := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ : I => Ω)
  let z : {i : I // i ∉ S} → Ω := fun _ => Classical.choice inferInstance
  have hcalc (L : I → FinLaw Ω) : (FinLaw.pi L).E f =
      ∑ x : {i : I // i ∈ S} → Ω,
        (∏ i : {i : I // i ∈ S}, (L i.1).w (x i)) * f (e.symm (x, z)) := by
    have hfactor (xy : ({i : I // i ∈ S} → Ω) × ({i : I // i ∉ S} → Ω)) :
        (FinLaw.pi L).w (e.symm xy) =
          (∏ i : {i : I // i ∈ S}, (L i.1).w (xy.1 i)) *
          (∏ i : {i : I // i ∉ S}, (L i.1).w (xy.2 i)) := by
      change (∏ i, (L i).w ((e.symm xy) i)) = _
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
      congr 1
      · apply Finset.prod_congr (by ext i; simp)
        intro i _
        change (L i.1).w (if h : i.1 ∈ S then xy.1 ⟨i.1, h⟩ else xy.2 ⟨i.1, h⟩) = _
        rw [dif_pos i.2]
      · apply Finset.prod_congr rfl
        intro i _
        change (L i.1).w (if h : i.1 ∈ S then xy.1 ⟨i.1, h⟩ else xy.2 ⟨i.1, h⟩) = _
        rw [dif_neg i.2]
    calc
      (FinLaw.pi L).E f = ∑ xy, (FinLaw.pi L).w (e.symm xy) * f (e.symm xy) := by
        exact (e.symm.sum_comp (fun x => (FinLaw.pi L).w x * f x)).symm
      _ = ∑ x : {i : I // i ∈ S} → Ω, ∑ y : {i : I // i ∉ S} → Ω,
          ((∏ i : {i : I // i ∈ S}, (L i.1).w (x i)) *
          (∏ i : {i : I // i ∉ S}, (L i.1).w (y i))) * f (e.symm (x, z)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [hfactor]
        have heq : f (e.symm (x, y)) = f (e.symm (x, z)) := by
          apply hf
          intro i hi
          change (if h : i ∈ S then x ⟨i, h⟩ else y ⟨i, h⟩) =
            (if h : i ∈ S then x ⟨i, h⟩ else z ⟨i, h⟩)
          rw [dif_pos hi, dif_pos hi]
        rw [heq]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        calc
          (∑ y : {i : I // i ∉ S} → Ω, ((∏ i : {i : I // i ∈ S}, (L i.1).w (x i)) *
              (∏ i : {i : I // i ∉ S}, (L i.1).w (y i))) * f (e.symm (x, z))) =
              ((∏ i : {i : I // i ∈ S}, (L i.1).w (x i)) * f (e.symm (x, z))) *
                (∑ y : {i : I // i ∉ S} → Ω, ∏ i : {i : I // i ∉ S}, (L i.1).w (y i)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          _ = _ := by
            have hnorm := (FinLaw.pi (fun i : {i : I // i ∉ S} => L i.1)).sum_one
            change (∑ y : {i : I // i ∉ S} → Ω, ∏ i : {i : I // i ∉ S}, (L i.1).w (y i)) = 1 at hnorm
            rw [hnorm, mul_one]
  rw [hcalc P, hcalc Q]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hPQ i.1 i.2]

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · simp [ha, hAB ω ha]
  · by_cases hb : B ω <;> simp [ha, hb, P.nonneg]

theorem pi_coordinate_pr {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] (P : I → FinLaw Ω) (i : I) (y : Ω) :
    (FinLaw.pi P).pr (fun x => x i = y) = (P i).w y := by
  classical
  rw [pr_eq_indicator_E]
  calc
    (FinLaw.pi P).E (fun x => if x i = y then 1 else 0) =
        (P i).E (fun z => if z = y then 1 else 0) :=
          pi_coordinate_E P i (fun z => if z = y then (1 : ℝ) else 0)
    _ = (P i).w y := by unfold FinLaw.E; simp [eq_comm]

theorem solver_qin_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (hW : S.AllGood W)
    (g : HypercubeRamsey.Group 𝒯 i) (D : Bin 𝒯 i)
    (hsmall : ((𝒯.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤ 1 / 2) :
    S.qin W g D ≤ 8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) * (𝒯.P i).d / (𝒯.P i).M := by
  let cap := 4 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) * (𝒯.P i).d / (𝒯.P i).M
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  have hmass : (1 / 2 : ℝ) ≤ ∑ b ∈ S.pretrimBins W g, S.q g W b := by
    have h := solver_pretrim_mass S W hW g (Real.exp_pos _)
    linarith
  unfold SliceSolver.qin
  split_ifs with hD
  · calc
      S.q g W D / (∑ b ∈ S.pretrimBins W g, S.q g W b) ≤
          cap / (∑ b ∈ S.pretrimBins W g, S.q g W b) :=
        div_le_div_of_nonneg_right (S.q_cap g W D) (by linarith)
      _ ≤ cap / (1 / 2 : ℝ) := div_le_div_of_nonneg_left hcap (by norm_num) hmass
      _ = _ := by dsimp [cap]; ring
  · positivity

/-- A quantitative permission bound, with the rate fixed by the input table. -/
theorem permission_removed_count {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hP : PermissionLossHypotheses P qin) (g : Group) :
    ((Finset.univ \ P.permitted g).card : ℝ) ≤
      Real.exp (-P.cperm * P.n) * Fintype.card Bin := by
  classical
  let bad := Finset.univ \ P.permitted g
  let pairs := ((permissionIncidences P g).product Finset.univ).filter fun iy =>
    Real.exp (-P.cperm * P.n) < P.badMass iy.1 iy.2
  have witness : ∀ b ∈ bad, ∃ iy : Incidence × Label,
      iy ∈ pairs ∧ iy.2 ∈ P.labels b := by
    intro b hb
    have hn := (Finset.mem_sdiff.mp hb).2
    rw [P.permitted_iff] at hn
    simp only [not_forall, not_le] at hn
    obtain ⟨inc, hg, y, hy, hbad⟩ := hn
    refine ⟨(inc, y), ?_, hy⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp [permissionIncidences, hg], ?_⟩
    exact hbad
  let f : {b // b ∈ bad} → Incidence × Label :=
    fun b => Classical.choose (witness b.1 b.2)
  have hf : ∀ b, f b ∈ pairs ∧ (f b).2 ∈ P.labels b.1 :=
    fun b => Classical.choose_spec (witness b.1 b.2)
  have hinj : Function.Injective f := by
    intro b b' heq
    have hy := (hf b).2
    have hy' : (f b).2 ∈ P.labels b'.1 := by rw [heq]; exact (hf b').2
    apply Subtype.ext
    apply Finset.card_le_one.mp (hP.labels_disjoint (f b).2)
    · simp [binsContainingLabel, hy]
    · simp [binsContainingLabel, hy']
  have hcard : bad.card ≤ pairs.card := by
    have h := Finset.card_le_card (s := Finset.univ.image f) (t := pairs)
      (by intro iy hiy; obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hiy; exact (hf b).1)
    simpa [Finset.card_image_of_injective _ hinj] using h
  have ht : 0 < Real.exp (-P.cperm * P.n) := Real.exp_pos _
  have hmarkov : (pairs.card : ℝ) * Real.exp (-P.cperm * P.n) ≤
      ∑ inc ∈ permissionIncidences P g, ∑ y, P.badMass inc y := by
    calc
      (pairs.card : ℝ) * Real.exp (-P.cperm * P.n) =
          ∑ iy ∈ pairs, Real.exp (-P.cperm * P.n) := by simp
      _ ≤ ∑ iy ∈ pairs, P.badMass iy.1 iy.2 := by
        apply Finset.sum_le_sum
        intro iy hiy
        exact le_of_lt (Finset.mem_filter.mp hiy).2
      _ ≤ ∑ iy ∈ (permissionIncidences P g).product Finset.univ,
          P.badMass iy.1 iy.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro iy _ _
        exact (hP.mean_bad_mass iy.1 iy.2).1
      _ = _ := by exact Finset.sum_product _ _ _
  have hmean : (pairs.card : ℝ) * Real.exp (-P.cperm * P.n) ≤
      ((permissionIncidences P g).card : ℝ) *
        (Real.exp (-3 * P.cperm * P.n) * Fintype.card Label) := by
    exact hmarkov.trans (by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_le_sum (s := permissionIncidences P g)
          (fun inc _ => hP.average_bad_mass inc)))
  have hB : (0 : ℝ) < Fintype.card Bin := by
    letI := hP.bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hr := hP.incidence_label_ratio g
  rw [← mul_div_assoc] at hr
  have hratio := (div_le_iff₀ hB).mp hr
  have hratio' : ((permissionIncidences P g).card : ℝ) * Fintype.card Label ≤
      Real.exp (P.cperm * P.n) * Fintype.card Bin := by
    nlinarith only [hratio]
  have hsum : (pairs.card : ℝ) * Real.exp (-P.cperm * P.n) ≤
      Real.exp (-2 * P.cperm * P.n) * Fintype.card Bin := by
    calc
      _ ≤ Real.exp (-3 * P.cperm * P.n) *
          (((permissionIncidences P g).card : ℝ) * Fintype.card Label) := by
        nlinarith only [hmean]
      _ ≤ Real.exp (-3 * P.cperm * P.n) *
          (Real.exp (P.cperm * P.n) * Fintype.card Bin) :=
        mul_le_mul_of_nonneg_left hratio' (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have hbound : (pairs.card : ℝ) ≤
      Real.exp (-P.cperm * P.n) * Fintype.card Bin := by
    apply (mul_le_mul_iff_left₀ ht).mp
    calc
      _ ≤ Real.exp (-2 * P.cperm * P.n) * Fintype.card Bin := by
        simpa [mul_comm] using hsum
      _ = _ := by
        have he : Real.exp (-2 * P.cperm * P.n) =
            Real.exp (-P.cperm * P.n) * Real.exp (-P.cperm * P.n) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        ring
  exact (by exact_mod_cast hcard : (bad.card : ℝ) ≤ pairs.card).trans hbound

/-- The permission denominator is at least one half at the recorded threshold. -/
theorem permission_retained_half {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hP : PermissionLossHypotheses P qin) (g : Group) :
    (1 / 2 : ℝ) ≤ ∑ b ∈ P.permitted g, (qin g).w b := by
  classical
  have hB : (0 : ℝ) < Fintype.card Bin := by
    letI := hP.bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hremoved : (∑ b ∈ Finset.univ \ P.permitted g, (qin g).w b) ≤
      Real.exp (-P.cperm * P.n / 2) := by
    calc
      _ ≤ ((Finset.univ \ P.permitted g).card : ℝ) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) := by
        simpa using Finset.sum_le_sum (s := Finset.univ \ P.permitted g)
          (fun b _ => hP.incoming_cap g b)
      _ ≤ (Real.exp (-P.cperm * P.n) * Fintype.card Bin) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) :=
        mul_le_mul_of_nonneg_right (permission_removed_count P qin hP g) (by positivity)
      _ = _ := by
        field_simp
        rw [← Real.exp_add]
        congr 1
        ring
  have hexp : Real.exp (-P.cperm * P.n / 2) ≤ 1 / 2 := by
    have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    have hn := hP.threshold_large
    rw [hlog] at hn
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hsplit := Finset.sum_sdiff (s₁ := P.permitted g) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := (qin g).w)
  rw [(qin g).sum_one] at hsplit
  linarith

theorem four_over_atom_cap (d : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d) :
    4 / (d : ℝ) ≤ Real.rpow (d : ℝ) (-0.95) := by
  have hbase : (10 : ℝ) ^ (100 : ℕ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hbase
  have hpow : (4 : ℝ) ≤ Real.rpow (d : ℝ) 0.05 := by
    calc
      4 ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) 0.05 := by
        have he : Real.rpow ((10 : ℝ) ^ (100 : ℕ)) 0.05 =
            Real.rpow 10 (100 * 0.05) := by
          rw [← Real.rpow_natCast]
          exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 0.05).symm
        rw [he]
        norm_num [Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  calc
    4 / (d : ℝ) ≤ Real.rpow (d : ℝ) 0.05 / d :=
      div_le_div_of_nonneg_right hpow hp.le
    _ = _ := by
      have h := Real.rpow_sub_one hp.ne' (0.05 : ℝ)
      rw [show (0.05 - 1 : ℝ) = -0.95 by norm_num] at h
      simpa only [Real.rpow_eq_pow] using h.symm

theorem typical_normalizer_lower (n : ℕ) (hn : 2 ≤ n) (m L B : ℝ)
    (hL : 0 < L) (hB : 0 < B)
    (hm : |m / (L / B) - 1| ≤ Real.rpow (n : ℝ) (-4)) :
    L / (2 * B) ≤ m := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.rpow (n : ℝ) (-4) ≤ 1 / 2 := by
    calc
      _ ≤ Real.rpow (2 : ℝ) (-4) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hn' (by norm_num)
      _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hl := (abs_le.mp hm).1
  have hratio : 1 / 2 ≤ m / (L / B) := by linarith
  have hmul := (le_div_iff₀ (div_pos hL hB)).mp hratio
  calc
    L / (2 * B) = (1 / 2) * (L / B) := by ring
    _ ≤ m := hmul

theorem pool_atom_cap {Bin : Type*} [Fintype Bin]
    (P Q : FinLaw Bin) (A : Finset Bin) (L B c : ℝ)
    (hL : 0 < L) (hB : 0 < B) (hc : 0 ≤ c)
    (hcap : ∀ b, P.w b ≤ c / B)
    (hlower : L / (2 * B) ≤ ∑ b ∈ A, P.w b)
    (hQ : ∀ b, Q.w b = (if b ∈ A then P.w b else 0) / (∑ b' ∈ A, P.w b')) :
    ∀ b, Q.w b ≤ 2 * c / L := by
  intro b
  have hm : 0 < ∑ b ∈ A, P.w b := lt_of_lt_of_le (by positivity) hlower
  rw [hQ]
  by_cases hb : b ∈ A
  · rw [if_pos hb]
    calc
      _ ≤ (c / B) / (∑ b ∈ A, P.w b) :=
        div_le_div_of_nonneg_right (hcap b) hm.le
      _ ≤ (c / B) / (L / (2 * B)) :=
        div_le_div_of_nonneg_left (div_nonneg hc hB.le) (by positivity) hlower
      _ = _ := by field_simp
  · rw [if_neg hb, zero_div]
    positivity

theorem calibration_pretrim_small (d h : ℕ) (ε : ℝ) (hd : 2 ≤ d)
    (hε : 0 < ε ∧ ε ≤ 1)
    (hroom : 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-20)) :
    (h : ℝ) ^ 2 * Real.sqrt ε ≤ 1 / 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hd)
  have hsmall : Real.rpow (d : ℝ) (-20) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd' (by norm_num : (-20 : ℝ) ≤ 0)
  have he : Real.sqrt ε ≤ Real.rpow ε (1 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2 (by norm_num)
  have hheight : (h : ℝ) ^ 2 ≤ (h + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hb : (h : ℝ) ^ 2 * Real.sqrt ε ≤ (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) :=
    mul_le_mul hheight he (Real.sqrt_nonneg _) (sq_nonneg _)
  have hz : 0 ≤ (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hε.1.le _)
  have hfactor : 16 ≤ 16 * (d : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfactor hz
  nlinarith [hroom.trans hsmall]

theorem calibration_exp_cap (d : ℕ) (t : ℝ) (hd : 1 ≤ d) (ht : 0 ≤ t)
    (hroom : 4 * Real.exp (1.5 * t) ≤ Real.rpow (d : ℝ) 0.05) :
    Real.exp (2 * t) ≤ d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := by linarith
  have he : Real.exp (1.5 * t) ≤ Real.rpow (d : ℝ) 0.05 := by
    linarith [Real.exp_pos (1.5 * t)]
  have hs := mul_self_le_mul_self (Real.exp_pos _).le he
  have h3 : Real.exp (3 * t) ≤ Real.rpow (d : ℝ) 0.1 := by
    calc
      Real.exp (3 * t) = Real.exp (1.5 * t) * Real.exp (1.5 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.rpow (d : ℝ) 0.05 * Real.rpow (d : ℝ) 0.05 := hs
      _ = _ := by
        convert (Real.rpow_add hp (0.05 : ℝ) 0.05).symm using 1 <;> norm_num
  calc
    _ ≤ Real.exp (3 * t) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.rpow (d : ℝ) 0.1 := h3
    _ ≤ d := by simpa using Real.rpow_le_rpow_of_exponent_le hd' (by norm_num : (0.1 : ℝ) ≤ 1)

theorem low_cluster_pretrim_power_small {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hm : PT.tiling.mode = .lowCluster)
    (i : Fin PT.tiling.m) (m : ℕ) (hm6 : m ≤ 6) :
    ((PT.tiling.P i).h : ℝ) ^ m * Real.sqrt (sliceEps κ (PT.tiling.P i).h) ≤ Real.rpow 10 (-3) := by
  obtain ⟨hscale, hg, _, _, _, _, _, hLower, hUpper, _, _, _⟩ :=
    Q.profiled_valid.tiling_valid.cluster_data (Or.inl hm) i
  simp only [hm, if_true] at hLower hUpper
  have hMlo : (0 : ℝ) < κ.Mlo := by
    have hh := hκ.Mlo_big
    have hb : (0 : ℝ) ≤ κ.Cb := by
      have hc := hκ.Cb_big
      have hp : 0 < 100 * κ.aC / κ.aB :=
        div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
      linarith
    linarith
  have hq1 : (1 : ℝ) ≤ (PT.tiling.P i).q := by
    have hq : (PT.tiling.P i).q ≠ 0 := by
      intro hz
      have hzpow : Real.rpow (0 : ℝ) (κ.Mlo : ℝ) = 0 := by
        simpa only [Real.rpow_eq_pow] using Real.zero_rpow hMlo.ne'
      rw [hz, Nat.cast_zero, hzpow, mul_zero] at hUpper
      exact not_lt_of_ge (Nat.cast_nonneg _) hUpper
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
    have hh := hκ.Mhi_big.1
    have hp : (0 : ℝ) < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    linarith
  have hmax : max ((PT.tiling.P i).g : ℝ) (PT.tiling.P i).q ≤ κ.M1 * (PT.tiling.P i).q := by
    apply max_le hg
    have hh := hκ.M1_big.1
    nlinarith
  have hq0 : κ.Q0 ≤ (PT.tiling.P i).q := by
    have hh : (κ.M1 : ℝ) * κ.Q0 ≤ κ.M1 * (PT.tiling.P i).q := by
      exact hscale.trans (by exact_mod_cast hmax)
    nlinarith [hκ.M1_big.1]
  have hUpper' : ((PT.tiling.P i).h : ℝ) < 2 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
    hUpper.trans_le (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 hMhi) (by norm_num))
  obtain ⟨_, _, _, _, _, _, _, _, hall⟩ := hκ.Q0_large (PT.tiling.P i).q hq0
  have hs := (hall (PT.tiling.P i).h hLower hUpper').2.2.2.2.2.1
  have hh1 : (1 : ℝ) ≤ (PT.tiling.P i).h :=
    (Real.one_le_rpow hq1 hMlo.le).trans hLower
  have hpow := pow_le_pow_right₀ hh1 hm6
  calc
    _ ≤ ((PT.tiling.P i).h : ℝ) ^ 6 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
    _ ≤ Real.rpow 10 (-3) := hs


theorem low_cluster_pretrim_small {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hm : PT.tiling.mode = .lowCluster)
    (i : Fin PT.tiling.m) :
    ((PT.tiling.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) ≤ 1 / 2 := by
  have hs := low_cluster_pretrim_power_small hκ Q hm i 2 (by norm_num)
  exact hs.trans (by norm_num [Real.rpow_neg, Real.rpow_natCast])

theorem exceptional_count {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err) (c : Colour)
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hw : τ.WidthLE wS)
    (A : Finset (Fin (T.S.N k))) (hA : A.Nonempty) (hAY : A ⊆ T.Y k) :
    (∑ y ∈ A, if err < |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2| then (1 : ℝ) else 0) ≤
      2 * Real.exp (-wL) * T.S.N k := by
  classical
  let ν : Law (T.S.N k) := FinProb.uniform A hA
  have hν : ν.SupportedIn (T.Y k) := by
    intro y hy
    have hn : y ∉ A := fun ha => hy (hAY ha)
    simp [ν, FinProb.uniform, hn]
  have hνw : ν.WidthLE (Real.log ((T.S.N k : ℝ) / A.card)) := Law.uniform_width A hA
  have hN : (0 : ℝ) < T.S.N k := by
    obtain ⟨y, _⟩ := hA
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le y.val) y.isLt)
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have h := S12.exceptional_second hDisc c (Or.inl ⟨le_rfl, le_rfl⟩) τ hτ hw ν hν hνw
  have heq : (∑ y ∈ Finset.univ.filter (fun y => err <
      |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|), ν.w y) =
      (∑ y ∈ A, if err < |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2| then (1 : ℝ) else 0) /
        A.card := by
    simp [ν, FinProb.uniform, Finset.sum_filter, Finset.filter_filter,
      Finset.sum_ite, and_comm, div_eq_mul_inv]
    left
    congr 1
    ext y
    simp [and_comm]
  rw [heq] at h
  have hright : 2 * Real.exp (Real.log ((T.S.N k : ℝ) / A.card) - wL) * A.card =
      2 * Real.exp (-wL) * T.S.N k := by
    rw [Real.exp_sub, Real.exp_log (div_pos hN hcard), Real.exp_neg]
    field_simp
  have hm := (div_le_iff₀ hcard).mp h
  rw [hright] at hm
  exact hm

/-- Fixed logarithmic inflations are absorbed uniformly before choosing a stage. -/
theorem logarithmic_room (r c C a : ℝ) (hr : 0 < r) (hc : 0 < c) (ha : 0 ≤ a) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      C + a * Real.log (n : ℝ) ≤ c * (n : ℝ) ^ r := by
  have hlog := (isLittleO_log_rpow_atTop hr).bound (div_pos hc (by positivity : 0 < 2 * (a + 1)))
  have hpow := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * |C| / c)
  have hgood : ∀ᶠ x : ℝ in Filter.atTop,
      C + a * Real.log x ≤ c * x ^ r := by
    filter_upwards [hlog, hpow, Filter.eventually_ge_atTop (0 : ℝ)] with x hx hp hnonneg
    have hx' : |Real.log x| ≤ c / (2 * (a + 1)) * x ^ r := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnonneg r), Real.rpow_eq_pow] using hx
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self C) (by norm_num : (0 : ℝ) ≤ 2)
    have hcC : 2 * C ≤ c * x ^ r := by
      have hh := (div_le_iff₀ hc).mp hp
      nlinarith
    have hl : a * Real.log x ≤ (c / 2) * x ^ r := by
      have hbound := mul_le_mul_of_nonneg_left hx' ha
      have hfac : a * (c / (2 * (a + 1))) ≤ c / 2 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < 2 * (a + 1))).mpr
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hnonneg r)
      nlinarith [le_abs_self (Real.log x)]
    linarith
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hgood
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge B
  exact ⟨n₀, fun n hn => hB n (hn₀.trans (by exact_mod_cast hn))⟩

theorem omega_le_one {κ : CConsts} (hκ : κ.Admissible) : κ.ω ≤ 1 := by
  have hb : 100 < κ.Cb := by
    have hh := hκ.Cb_big
    have hp : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith
  have hm : (1 : ℝ) ≤ κ.Mhi := by
    have hh := hκ.Mhi_big.1
    have hp : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    have hl := hκ.Mlo_big
    linarith
  have ha : κ.aC < 1 := lt_of_lt_of_le hκ.aC_rng.2 (by
    have hh : min κ.η0 1 ≤ (1 : ℝ) := min_le_right _ _
    nlinarith)
  have hω := hκ.ω_rng.2
  have hprod := mul_nonneg hκ.ω_rng.1.le (sub_nonneg.mpr hm)
  nlinarith

theorem slice_product_bound {κ : CConsts} (hκ : κ.Admissible) (h : ℕ) (hh : 1 ≤ h) :
    (sliceK κ h : ℝ) * sliceT κ h ≤ (h : ℝ) ^ (4 : ℕ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hk : sliceK κ h ≤ h ^ (3 : ℕ) := by
    apply Nat.ceil_le.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hh'
      (show 3 * κ.ω ≤ (3 : ℝ) by linarith [omega_le_one hκ])
    simpa only [Real.rpow_ofNat, Nat.cast_pow, Real.rpow_eq_pow] using hp
  have ht : sliceT κ h ≤ h := by
    apply Nat.ceil_le.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hh' (omega_le_one hκ)
    simpa only [Real.rpow_one, Real.rpow_eq_pow] using hp
  have hk' : (sliceK κ h : ℝ) ≤ (h : ℝ) ^ (3 : ℕ) := by exact_mod_cast hk
  have ht' : (sliceT κ h : ℝ) ≤ h := by exact_mod_cast ht
  calc
    _ ≤ (h : ℝ) ^ (3 : ℕ) * h := mul_le_mul hk' ht' (by positivity) (by positivity)
    _ = _ := by ring

theorem local_product_domination {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Nonempty O] (P Q : I → FinLaw O) (S : Finset I) (c : ℝ)
    (hc : 0 ≤ c) (hQ : ∀ i ∈ S, ∀ y, (Q i).w y ≤ c * (P i).w y)
    (f : (I → O) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hlocal : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) :
    (FinLaw.pi Q).E f ≤ c ^ S.card * (FinLaw.pi P).E f := by
  classical
  let M : I → FinLaw O := fun i => if i ∈ S then Q i else P i
  have hsame : (FinLaw.pi Q).E f = (FinLaw.pi M).E f :=
    pi_E_local Q M S f hlocal (fun i hi => by simp [M, hi])
  have hweight : ∀ x, (FinLaw.pi M).w x ≤ c ^ S.card * (FinLaw.pi P).w x := by
    intro x
    calc
      _ ≤ ∏ i, (if i ∈ S then c else 1) * (P i).w (x i) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact (M i).nonneg _
        · intro i _
          by_cases hi : i ∈ S
          · simpa [M, hi] using hQ i hi (x i)
          · simp [M, hi]
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        congr 1
        simp [Finset.prod_ite_mem]
  rw [hsame]
  calc
    _ ≤ ∑ x, (c ^ S.card * (FinLaw.pi P).w x) * f x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hweight x) (hf x)
    _ = _ := by simp only [FinLaw.E, mul_assoc, Finset.mul_sum]

theorem prior_bad_count {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err) (herr : 0 ≤ err) (c : Colour)
    (P : PriorExperiment (T.S.N k)) (A : Finset (Fin (T.S.N k)))
    (hA : A.Nonempty) (hAY : A ⊆ T.Y k)
    (hrows : ∀ ω, P.law.w ω ≠ 0 → P.prior ω ≠ 0 →
      ∃ τ : Law (T.S.N k), τ.w = P.prior ω ∧ τ.SupportedIn (T.X k) ∧ τ.WidthLE wS) :
    (∑ y ∈ A, P.expect (fun σ => if σ ≠ 0 ∧
      2 * err < |(∑ x, σ x * hit (T.S.E k) c x y) - 1 / 2| then 1 else 0)) ≤
      2 * Real.exp (-wL) * T.S.N k := by
  classical
  have hcount : ∀ ω, P.law.w ω ≠ 0 →
      (∑ y ∈ A, if P.prior ω ≠ 0 ∧
        2 * err < |(∑ x, P.prior ω x * hit (T.S.E k) c x y) - 1 / 2| then (1 : ℝ) else 0) ≤
        2 * Real.exp (-wL) * T.S.N k := by
    intro ω hω
    by_cases hz : P.prior ω = 0
    · simp only [hz, ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
      positivity
    · obtain ⟨τ, hτ, hs, hw⟩ := hrows ω hω hz
      apply le_trans _ (exceptional_count hDisc c τ hs hw A hA hAY)
      apply Finset.sum_le_sum
      intro y _
      by_cases hb : 2 * err < |(∑ x, P.prior ω x * hit (T.S.E k) c x y) - 1 / 2|
      · have hb' : err < |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2| := by
          rw [hτ]
          linarith
        rw [if_pos (And.intro hz hb), if_pos hb']
      · simp only [hb, and_false, if_false]
        split_ifs <;> norm_num
  unfold PriorExperiment.expect FinLaw.E
  rw [Finset.sum_comm]
  calc
    _ = ∑ ω, P.law.w ω * (∑ y ∈ A, if P.prior ω ≠ 0 ∧
        2 * err < |(∑ x, P.prior ω x * hit (T.S.E k) c x y) - 1 / 2| then (1 : ℝ) else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ ω, P.law.w ω * (2 * Real.exp (-wL) * T.S.N k) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hz : P.law.w ω = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hcount ω hz) (P.law.nonneg ω)
    _ = _ := by rw [← Finset.sum_mul, P.law.sum_one, one_mul]

theorem map_equiv_weight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (e : A ≃ B) (b : B) : (FinLaw.map P e).w b = P.w (e.symm b) := by
  classical
  change (∑ a, if e a = b then P.w a else 0) = P.w (e.symm b)
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ hne
    have h : e a ≠ b := by intro he; exact hne (by rw [← he]; simp)
    simp [h]
  · simp

theorem slice_product_log_bound {κ : CConsts} (hκ : κ.Admissible)
    (h : ℕ) (x : ℝ) (hx : 1 ≤ x) (hh : (h : ℝ) ≤ Real.rpow x (1 / 10 : ℝ)) :
    (sliceK κ h : ℝ) * sliceT κ h ≤ x := by
  have hprod : (sliceK κ h : ℝ) * sliceT κ h ≤ (h : ℝ) ^ (4 : ℕ) := by
    by_cases hz : h = 0
    · subst h
      have hk : (0 : ℝ) ^ (3 * κ.ω) = 0 := Real.zero_rpow (by nlinarith [hκ.ω_rng.1])
      have ht : (0 : ℝ) ^ κ.ω = 0 := Real.zero_rpow hκ.ω_rng.1.ne'
      simp only [sliceK, sliceT, Nat.cast_zero, Real.rpow_eq_pow, hk, ht,
        Nat.ceil_zero, zero_mul, zero_pow (by norm_num : (4 : ℕ) ≠ 0), le_refl]
    · exact slice_product_bound hκ h (Nat.one_le_iff_ne_zero.mpr hz)
  change (h : ℝ) ≤ x ^ (1 / 10 : ℝ) at hh
  have hp : (x ^ (1 / 10 : ℝ)) ^ (4 : ℕ) = x ^ (0.4 : ℝ) := by
    have hr : (x ^ (1 / 10 : ℝ)) ^ (4 : ℕ) = (x ^ (1 / 10 : ℝ)) ^ (4 : ℝ) :=
      (Real.rpow_natCast _ 4).symm
    rw [hr, ← Real.rpow_mul (by linarith : 0 ≤ x)]
    norm_num
  calc
    _ ≤ (h : ℝ) ^ (4 : ℕ) := hprod
    _ ≤ (x ^ (1 / 10 : ℝ)) ^ (4 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hh _
    _ = x ^ (0.4 : ℝ) := hp
    _ ≤ x := by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (0.4 : ℝ) ≤ 1)

/-- The diagnostic normalizer agrees with its slot polynomial on distinct pools. -/
theorem distinct_pool_mass {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] (P : FinLaw Bin) (pool : Slot → Bin)
    (hpool : Function.Injective pool) :
    (∑ b ∈ Finset.univ.image pool, P.w b) = ∑ s, P.w (pool s) := by
  exact Finset.sum_image (fun s _ s' _ h => hpool h)

theorem empirical_mass_mean {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] (P : FinLaw Bin) (Q : Slot → FinLaw Bin)
    (hQ : ∀ s b, (Q s).w b = 1 / (Fintype.card Bin : ℝ)) :
    (FinLaw.pi Q).E (fun pool => ∑ s, P.w (pool s)) =
      (Fintype.card Slot : ℝ) / Fintype.card Bin := by
  classical
  calc
    _ = ∑ s, (FinLaw.pi Q).E (fun pool => P.w (pool s)) := by
      unfold FinLaw.E
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ s, (Q s).E P.w := by
      apply Finset.sum_congr rfl
      intro s _
      exact pi_coordinate_E Q s P.w
    _ = ∑ _s : Slot, 1 / (Fintype.card Bin : ℝ) := by
      apply Finset.sum_congr rfl
      intro s _
      unfold FinLaw.E
      simp_rw [hQ]
      rw [← Finset.mul_sum, P.sum_one, mul_one]
    _ = _ := by simp [div_eq_mul_inv]

theorem empirical_mass_one_slot {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] (P : FinLaw Bin) (c : ℝ) (hcap : ∀ b, P.w b ≤ c)
    (s : Slot) (x y : Slot → Bin) (hxy : ∀ t, t ≠ s → x t = y t) :
    |(∑ t, P.w (x t)) - ∑ t, P.w (y t)| ≤ c := by
  classical
  have he : (∑ t, P.w (x t)) - ∑ t, P.w (y t) = P.w (x s) - P.w (y s) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single s]
    · intro t _ hts
      rw [hxy t hts, sub_self]
    · simp
  rw [he, abs_le]
  constructor <;> linarith [P.nonneg (x s), P.nonneg (y s), hcap (x s), hcap (y s)]

noncomputable def role_star_data {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) :
    AvoidanceData P.readout P.blockOf P.safe where
  base := FinLaw.pi seed.laws
  Event := Star
  eventFin := inferInstance
  eventDec := Classical.decEq _
  bad := fun s => Finset.univ.filter fun ω => P.starBad s (P.readout ω)
  scope := fun s => (P.participants s).image P.blockOf
  charge := charge
  pinnedBound := pin
  baseJointRate := Real.rpow (P.d : ℝ) (-0.04)
  touchRate := touch

theorem role_star_data_local {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (s : Star)
    (ω ω' : P.SeedState)
    (hω : ∀ b ∈ (P.participants s).image P.blockOf, ω b = ω' b) :
    ω ∈ (role_star_data P q seed charge pin touch).bad s ↔
      ω' ∈ (role_star_data P q seed charge pin touch).bad s := by
  classical
  simp only [role_star_data, Finset.mem_filter, Finset.mem_univ, true_and]
  apply P.star_local
  intro r hr
  unfold RoleLabelProblem.readout
  rw [hω (P.blockOf r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)]

theorem role_star_data_safe_cover {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (ω : P.SeedState)
    (hω : (FinLaw.pi seed.laws).w ω ≠ 0)
    (havoid : ∀ s, ω ∉ (role_star_data P q seed charge pin touch).bad s) :
    P.safe (P.readout ω) := by
  classical
  have hreadout (r : Role) (b : Block) (hb : P.blockOf r = b) :
      P.readout ω r = (ω b ⟨r, hb⟩).1 := by subst b; rfl
  constructor
  · intro r r' hrr
    have hb : P.blockOf r = P.blockOf r' := by
      by_contra hn
      have hr : P.readout ω r ∈ P.blockLabels (P.blockOf r) := (ω _ ⟨r, rfl⟩).2
      have hr' : P.readout ω r' ∈ P.blockLabels (P.blockOf r') := (ω _ ⟨r', rfl⟩).2
      exact Finset.disjoint_left.mp (P.blocks_disjoint _ _ hn) hr (by rw [hrr]; exact hr')
    have hcoord := pi_support seed.laws ω hω (P.blockOf r)
    have hinj := seed.injective (P.blockOf r) (ω (P.blockOf r)) hcoord
    have hstate : ω (P.blockOf r) ⟨r, rfl⟩ = ω (P.blockOf r) ⟨r', hb.symm⟩ := by
      apply Subtype.ext
      rw [← hreadout r _ rfl, ← hreadout r' _ hb.symm]
      exact hrr
    exact congrArg Subtype.val (hinj hstate)
  · intro s
    simpa only [role_star_data, Finset.mem_filter, Finset.mem_univ, true_and] using havoid s

/-- The calibration room pays the whole-bin star-neighbor and singleton budgets. -/
theorem role_star_charge_budget (d h : ℕ) (ε : ℝ) (hd : 2 ≤ d) (hε : 0 < ε)
    (hroom : 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-20)) :
    (d : ℝ) * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-2) / 16 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hx : 0 ≤ Real.rpow ε (1 / 16 : ℝ) := Real.rpow_nonneg hε.le _
  have hy : 0 ≤ (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) := mul_nonneg (sq_nonneg _) hx
  have hfactor : (16 : ℝ) * d ≤ 16 * (d : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hfactor hy
  have hp := Real.rpow_le_rpow_of_exponent_le hd' (by norm_num : (-20 : ℝ) ≤ -2)
  change Real.rpow (d : ℝ) (-20) ≤ Real.rpow (d : ℝ) (-2) at hp
  nlinarith [hroom.trans hp]

/-- Joint comparisons on a local coordinate set control every event on that set. -/
theorem local_joint_domination {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Nonempty O] (P : I → FinLaw O)
    (Q : FinLaw (I → O)) (S : Finset I) (c : ℝ) (hc : 0 ≤ c)
    (hJoint : ∀ a : I → O, Q.pr (fun x => ∀ i ∈ S, x i = a i) ≤
      c * ∏ i ∈ S, (P i).w (a i))
    (A : (I → O) → Prop)
    (hlocal : ∀ x y, (∀ i ∈ S, x i = y i) → (A x ↔ A y)) :
    Q.pr A ≤ c * (FinLaw.pi P).pr A := by
  classical
  let restrict : (I → O) → ({i // i ∈ S} → O) := fun x i => x i.1
  let extend : ({i // i ∈ S} → O) → I → O := fun z i =>
    if hi : i ∈ S then z ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty O)
  have hback : ∀ x, A x ↔ A (extend (restrict x)) := by
    intro x
    apply hlocal
    intro i hi
    simp [extend, restrict, hi]
  have hmap (R : FinLaw (I → O)) :
      R.pr A = (FinLaw.map R restrict).pr (fun z => A (extend z)) := by
    rw [Lane_q_s16_calib.finLaw_map_pr]
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro x _
    rw [hback x]
  have hcyl (R : FinLaw (I → O)) (z : {i // i ∈ S} → O) :
      (FinLaw.map R restrict).w z = R.pr (fun x => ∀ i ∈ S, x i = extend z i) := by
    have hiff (x : I → O) : restrict x = z ↔ ∀ i ∈ S, x i = extend z i := by
      constructor
      · intro hx i hi
        have hh := congrFun hx ⟨i, hi⟩
        simpa [restrict, extend, hi] using hh
      · intro hx
        funext i
        simpa [restrict, extend, i.2] using hx i.1 i.2
    change (∑ x, if restrict x = z then R.w x else 0) = _
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : restrict x = z
    · rw [if_pos hx, if_pos ((hiff x).mp hx)]
    · have hn : ¬ (∀ i ∈ S, x i = extend z i) := fun hh => hx ((hiff x).mpr hh)
      rw [if_neg hx, if_neg hn]
  have hpi (z : {i // i ∈ S} → O) :
      (FinLaw.pi P).pr (fun x => ∀ i ∈ S, x i = extend z i) =
        ∏ i ∈ S, (P i).w (extend z i) := by
    let C : I → O → Prop := fun i o => i ∈ S → o = extend z i
    have he : (fun x : I → O => ∀ i ∈ S, x i = extend z i) = (fun x => ∀ i, C i (x i)) := rfl
    rw [he, Lane_q_s16_calib.finLaw_pi_pr_forall]
    have hrow : ∀ i, (P i).pr (C i) = if i ∈ S then (P i).w (extend z i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [C, hi, true_implies, if_true]
        exact Lane_q_s16_calib.finLaw_pr_eq_weight (P i) _
      · simp [C, hi, FinLaw.pr, (P i).sum_one]
    simp_rw [hrow]
    simp [Finset.prod_ite_mem]
  have hweights : ∀ z, (FinLaw.map Q restrict).w z ≤
      c * (FinLaw.map (FinLaw.pi P) restrict).w z := by
    intro z
    rw [hcyl, hcyl, hpi]
    exact hJoint (extend z)
  rw [hmap Q, hmap (FinLaw.pi P)]
  unfold FinLaw.pr
  calc
    _ ≤ ∑ z, c * (if A (extend z) then (FinLaw.map (FinLaw.pi P) restrict).w z else 0) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : A (extend z)
      · simp only [if_pos hz]
        exact hweights z
      · simp [hz]
    _ = _ := by rw [← Finset.mul_sum]

theorem role_seed_local_comparison {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (S : Finset Role)
    (hS : ∀ b, ((S.filter fun r => P.blockOf r = b).card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025)
    (A : (Role → Label) → Prop)
    (hlocal : ∀ x y, (∀ r ∈ S, x r = y r) → (A x ↔ A y)) :
    (FinLaw.pi seed.laws).pr (fun ω => A (P.readout ω)) ≤
      Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) * (FinLaw.pi q).pr A := by
  let Q := FinLaw.map (FinLaw.pi seed.laws) P.readout
  have hj : ∀ a : Role → Label, Q.pr (fun x => ∀ r ∈ S, x r = a r) ≤
      Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) * ∏ r ∈ S, (q r).w (a r) := by
    intro a
    rw [Lane_q_s16_calib.finLaw_map_pr]
    exact seed.joint S a hS
  have h := local_joint_domination q Q S _ (Real.exp_pos _).le hj A hlocal
  rw [Lane_q_s16_calib.finLaw_map_pr] at h
  exact h

theorem role_seed_star_comparison {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (s : Star) (c : ℝ) (hc : 0 ≤ c)
    (hq : ∀ r ∈ P.participants s, ∀ y, (q r).w y ≤ c * (P.target r).w y)
    (hS : ∀ b, (((P.participants s).filter fun r => P.blockOf r = b).card : ℝ) ≤
      Real.rpow (P.d : ℝ) 0.025) :
    (FinLaw.pi seed.laws).pr (fun ω => P.starBad s (P.readout ω)) ≤
      (Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (P.participants s).card) *
        c ^ (P.participants s).card) * P.independentStarFailure s := by
  classical
  have hseed := role_seed_local_comparison P q seed (P.participants s) hS
    (P.starBad s) (P.star_local s)
  have hprod : (FinLaw.pi q).pr (P.starBad s) ≤ c ^ (P.participants s).card *
      (FinLaw.pi P.target).pr (P.starBad s) := by
    rw [pr_eq_indicator_E, pr_eq_indicator_E]
    apply local_product_domination P.target q (P.participants s) c hc hq
    · intro x
      split_ifs <;> norm_num
    · intro x y hxy
      rw [(P.star_local s x y hxy)]
  have hh := mul_le_mul_of_nonneg_left hprod
    (Real.exp_pos (Real.rpow (P.d : ℝ) (-0.04) * (P.participants s).card)).le
  exact hseed.trans (by simpa only [RoleLabelProblem.independentStarFailure,
    RoleLabelProblem.productLaw, mul_assoc] using hh)

theorem pi_pr_disjoint {I : Type*} [Fintype I] [DecidableEq I]
    {O : I → Type*} [∀ i, Fintype (O i)] (P : ∀ i, FinLaw (O i))
    (A B : (∀ i, O i) → Prop) (S T : Finset I)
    (hA : ∀ x y, (∀ i ∈ S, x i = y i) → (A x ↔ A y))
    (hB : ∀ x y, (∀ i ∈ T, x i = y i) → (B x ↔ B y))
    (hST : Disjoint S T) :
    (FinLaw.pi P).pr (fun x => A x ∧ B x) = (FinLaw.pi P).pr A * (FinLaw.pi P).pr B := by
  classical
  let R : ∀ i, FinProb (O i) := fun i => finLawToFramework (P i)
  let f : (∀ i, O i) → ℝ := fun x => if A x then 1 else 0
  let g : (∀ i, O i) → ℝ := fun x => if B x then 1 else 0
  have hf : FinProb.DependsOn f S := by
    intro x y hxy
    simp only [f, hA x y hxy]
  have hg : FinProb.DependsOn g T := by
    intro x y hxy
    simp only [g, hB x y hxy]
  have h := FinProb.pi_expect_mul_of_disjoint R f g S T hf hg hST
  have hleft : (FinProb.pi R).expect (fun x => f x * g x) =
      (FinLaw.pi P).pr (fun x => A x ∧ B x) := by
    apply Finset.sum_congr rfl
    intro x _
    change (∏ i, (P i).w (x i)) * ((if A x then (1 : ℝ) else 0) * (if B x then 1 else 0)) = _
    split_ifs <;> simp_all [FinLaw.pi]
  have hfa : (FinProb.pi R).expect f = (FinLaw.pi P).pr A := by
    apply Finset.sum_congr rfl
    intro x _
    change (∏ i, (P i).w (x i)) * (if A x then (1 : ℝ) else 0) = _
    split_ifs <;> simp_all [FinLaw.pi]
  have hgb : (FinProb.pi R).expect g = (FinLaw.pi P).pr B := by
    apply Finset.sum_congr rfl
    intro x _
    change (∏ i, (P i).w (x i)) * (if B x then (1 : ℝ) else 0) = _
    split_ifs <;> simp_all [FinLaw.pi]
  rw [hleft, hfa, hgb] at h
  exact h

theorem disjoint_touching_scopes {I V E : Type*} [Fintype E] [DecidableEq I]
    [DecidableEq V] [DecidableEq E] (varOf : I → V) (scope : E → Finset V)
    (S : Finset I) (R : Finset E)
    (h : Disjoint R (Finset.univ.filter fun e => ∃ i ∈ S, varOf i ∈ scope e)) :
    Disjoint (S.image varOf) (R.biUnion scope) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb hb'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨e, he, hscope⟩ := Finset.mem_biUnion.mp hb'
  exact Finset.disjoint_left.mp h he (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, i, hi, hscope⟩)

theorem role_avoid_local {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (R : Finset Star)
    (ω ω' : P.SeedState)
    (hω : ∀ b ∈ R.biUnion (fun s => (P.participants s).image P.blockOf), ω b = ω' b) :
    ω ∈ (role_star_data P q seed charge pin touch).avoid R ↔
      ω' ∈ (role_star_data P q seed charge pin touch).avoid R := by
  classical
  have he : ∀ s ∈ R, ω ∈ (role_star_data P q seed charge pin touch).bad s ↔
      ω' ∈ (role_star_data P q seed charge pin touch).bad s := by
    intro s hs
    apply role_star_data_local
    intro b hb
    exact hω b (Finset.mem_biUnion.mpr ⟨s, hs, hb⟩)
  simp only [AvoidanceData.avoid, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h s hs hb
    exact h s hs ((he s hs).mpr hb)
  · intro h s hs hb
    exact h s hs ((he s hs).mp hb)

theorem role_query_outside {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (S : Finset Role)
    (ys : Role → Label) (R : Finset Star)
    (hR : Disjoint R ((role_star_data P q seed charge pin touch).touching S)) :
    (FinLaw.pi seed.laws).pr (fun ω =>
      (∀ r ∈ S, P.readout ω r = ys r) ∧ ω ∈ (role_star_data P q seed charge pin touch).avoid R) =
      (FinLaw.pi seed.laws).pr (fun ω => ∀ r ∈ S, P.readout ω r = ys r) *
        (FinLaw.pi seed.laws).pr (fun ω => ω ∈ (role_star_data P q seed charge pin touch).avoid R) := by
  classical
  apply pi_pr_disjoint seed.laws _ _ (S.image P.blockOf)
    (R.biUnion fun s => (P.participants s).image P.blockOf)
  · intro ω ω' hω
    have he : ∀ r ∈ S, P.readout ω r = P.readout ω' r := by
      intro r hr
      unfold RoleLabelProblem.readout
      rw [hω (P.blockOf r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)]
    constructor
    · intro h r hr
      rw [← he r hr]
      exact h r hr
    · intro h r hr
      rw [he r hr]
      exact h r hr
  · exact role_avoid_local P q seed charge pin touch R
  · apply disjoint_touching_scopes P.blockOf (fun s => (P.participants s).image P.blockOf) S R
    exact hR

theorem role_pin_outside {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (r : Role) (y : Label) (R : Finset Star)
    (hR : Disjoint R ((role_star_data P q seed charge pin touch).touching {r})) :
    (FinLaw.pi seed.laws).pr (fun ω => P.readout ω r = y ∧
      ω ∈ (role_star_data P q seed charge pin touch).avoid R) =
      (q r).w y * (FinLaw.pi seed.laws).pr (fun ω =>
        ω ∈ (role_star_data P q seed charge pin touch).avoid R) := by
  classical
  have h := role_query_outside P q seed charge pin touch {r} (fun _ => y) R hR
  simp only [Finset.mem_singleton, forall_eq] at h
  rw [seed.marginal r y] at h
  exact h

theorem avoidance_product_lower {E : Type*} [DecidableEq E]
    (S : Finset E) (x : E → ℝ) (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e ≤ 1) :
    1 - (∑ e ∈ S, x e) ≤ ∏ e ∈ S, (1 - x e) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
    have heX := hx e (Finset.mem_insert_self _ _)
    have hS : ∀ f ∈ S, 0 ≤ x f ∧ x f ≤ 1 := fun f hf => hx f (Finset.mem_insert_of_mem hf)
    have hsum : 0 ≤ ∑ f ∈ S, x f := Finset.sum_nonneg fun f hf => (hS f hf).1
    have hmul := mul_le_mul_of_nonneg_left (ih hS) (sub_nonneg.mpr heX.2)
    rw [Finset.sum_insert he, Finset.prod_insert he]
    nlinarith

theorem avoidance_reciprocal_bound {E : Type*} [DecidableEq E]
    (S : Finset E) (x : E → ℝ) (a : ℝ) (ha : a < 1)
    (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e < 1) (hsum : (∑ e ∈ S, x e) ≤ a) :
    (∏ e ∈ S, (1 - x e)⁻¹) ≤ (1 - a)⁻¹ := by
  have hp : 0 < ∏ e ∈ S, (1 - x e) :=
    Finset.prod_pos fun e he => sub_pos.mpr (hx e he).2
  have hl := avoidance_product_lower S x (fun e he => ⟨(hx e he).1, (hx e he).2.le⟩)
  have hb : 1 - a ≤ ∏ e ∈ S, (1 - x e) := by linarith
  rw [Finset.prod_inv_distrib]
  exact (inv_le_inv₀ hp (sub_pos.mpr ha)).mpr hb

theorem avoidance_singleton_cost {E : Type*} [DecidableEq E]
    (S : Finset E) (x : E → ℝ) (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e < 1) (hsum : (∑ e ∈ S, x e) ≤ η / 2) :
    (∏ e ∈ S, (1 - x e)⁻¹) ≤ 1 + η := by
  have ha : η / 2 < 1 := by linarith
  apply (avoidance_reciprocal_bound S x (η / 2) ha hx hsum).trans
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < 1 - η / 2)).mpr
  nlinarith

theorem reciprocal_exp_bound (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hp : 0 < 1 - x := by linarith
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  have hid : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp [hp.ne'] <;> ring
  rw [hid] at hh
  have hb : x / (1 - x) ≤ 2 * x := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  calc
    _ = Real.exp (Real.log ((1 - x)⁻¹)) := (Real.exp_log (inv_pos.mpr hp)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hh.trans hb)

theorem avoidance_joint_cost {E : Type*} [DecidableEq E]
    (S : Finset E) (x : E → ℝ) (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e ≤ 1 / 2) :
    (∏ e ∈ S, (1 - x e)⁻¹) ≤ Real.exp (2 * ∑ e ∈ S, x e) := by
  calc
    _ ≤ ∏ e ∈ S, Real.exp (2 * x e) := by
      apply Finset.prod_le_prod₀
      · intro e he
        exact inv_nonneg.mpr (by linarith [(hx e he).2])
      · intro e he
        exact reciprocal_exp_bound (x e) (hx e he)
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

theorem empirical_mass_pinned_mean {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] (P : FinLaw Bin) (Q : Slot → FinLaw Bin)
    (hQ : ∀ s b, (Q s).w b = 1 / (Fintype.card Bin : ℝ))
    (c : ℝ) (hc : 0 ≤ c) (hcap : ∀ b, P.w b ≤ c) (s : Slot) (b : Bin) :
    |(FinLaw.pi (fun t => if t = s then FinLaw.dirac b else Q t)).E
      (fun pool => ∑ t, P.w (pool t)) - (Fintype.card Slot : ℝ) / Fintype.card Bin| ≤
        c + 1 / (Fintype.card Bin : ℝ) := by
  classical
  let pinQ : Slot → FinLaw Bin := fun t => if t = s then FinLaw.dirac b else Q t
  have hE (L : Slot → FinLaw Bin) :
      (FinLaw.pi L).E (fun pool => ∑ t, P.w (pool t)) = ∑ t, (L t).E P.w := by
    calc
      _ = ∑ t, (FinLaw.pi L).E (fun pool => P.w (pool t)) := by
        unfold FinLaw.E
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl (fun t _ => pi_coordinate_E L t P.w)
  have hQmean : ∀ t, (Q t).E P.w = 1 / (Fintype.card Bin : ℝ) := by
    intro t
    unfold FinLaw.E
    simp_rw [hQ]
    rw [← Finset.mul_sum, P.sum_one, mul_one]
  have hdiff : (FinLaw.pi pinQ).E (fun pool => ∑ t, P.w (pool t)) -
      (Fintype.card Slot : ℝ) / Fintype.card Bin = P.w b - 1 / (Fintype.card Bin : ℝ) := by
    rw [← empirical_mass_mean P Q hQ, hE, hE, ← Finset.sum_sub_distrib]
    have hterm : ∀ t, (pinQ t).E P.w - (Q t).E P.w =
        if t = s then P.w b - 1 / (Fintype.card Bin : ℝ) else 0 := by
      intro t
      by_cases ht : t = s
      · subst t
        have hp : (FinLaw.dirac b).E P.w = P.w b := by
          unfold FinLaw.E
          change (∑ z, (if z = b then (1 : ℝ) else 0) * P.w z) = P.w b
          simp [eq_comm]
        rw [show pinQ s = FinLaw.dirac b by simp [pinQ], hp, hQmean, if_pos rfl]
      · simp [pinQ, ht]
    simp_rw [hterm]
    simp
  change |(FinLaw.pi pinQ).E (fun pool => ∑ t, P.w (pool t)) - _| ≤ _
  rw [hdiff, abs_le]
  have hB : 0 ≤ 1 / (Fintype.card Bin : ℝ) := by positivity
  constructor <;> linarith [P.nonneg b, hcap b]

theorem calibration_rpow_tenth (d : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d)
    (a : ℝ) (ha : 0.01 ≤ a) : Real.rpow (d : ℝ) (-a) ≤ 1 / 10 := by
  have hb : (10 : ℝ) ^ (100 : ℕ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hb
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hb
  calc
    _ ≤ Real.rpow (d : ℝ) (-0.01) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    _ ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.01) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (by norm_num)
    _ = 1 / 10 := by
      have he : Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.01) = Real.rpow 10 (100 * (-0.01)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 (-0.01)).symm
      rw [he]
      norm_num [Real.rpow_neg_one]

theorem relative_factor_exp (ρ : ℝ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1 / 3) :
    (1 + ρ) / (1 - ρ) ≤ Real.exp (4 * ρ) := by
  have hp : 0 < 1 - ρ := by linarith
  calc
    _ ≤ Real.exp ρ * Real.exp (2 * ρ) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul
      · simpa only [add_comm] using Real.add_one_le_exp ρ
      · exact reciprocal_exp_bound ρ ⟨hρ.1, by linarith⟩
      · exact inv_nonneg.mpr hp.le
      · exact (Real.exp_pos _).le
    _ = Real.exp (3 * ρ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem role_local_inflation (d m : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d)
    (hm : (m : ℝ) ≤ 2 * Real.rpow (d : ℝ) 0.01) :
    Real.exp (Real.rpow (d : ℝ) (-0.04) * m) *
      (((1 + Real.rpow (d : ℝ) (-0.02)) / (1 - Real.rpow (d : ℝ) (-0.02))) ^ m) ≤ 4 := by
  have hp : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 100) hd)
  let ρ := Real.rpow (d : ℝ) (-0.02)
  have hρ : 0 ≤ ρ ∧ ρ ≤ 1 / 3 :=
    ⟨(Real.rpow_pos_of_pos hp _).le, (calibration_power_bounds d hd).2⟩
  have hf := relative_factor_exp ρ hρ
  have hpow : (((1 + ρ) / (1 - ρ)) ^ m) ≤ Real.exp (4 * ρ * m) := by
    have hbase : 0 ≤ (1 + ρ) / (1 - ρ) :=
      div_nonneg (by linarith [hρ.1]) (by linarith [hρ.2])
    calc
      _ ≤ (Real.exp (4 * ρ)) ^ m := pow_le_pow_left₀ hbase hf m
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have ha : 0 ≤ Real.rpow (d : ℝ) (-0.04) + 4 * ρ := by dsimp [ρ]; positivity
  have hb := mul_le_mul_of_nonneg_left hm ha
  have hmul1 : Real.rpow (d : ℝ) (-0.04) * Real.rpow (d : ℝ) 0.01 = Real.rpow (d : ℝ) (-0.03) := by
    convert (Real.rpow_add hp (-0.04) 0.01).symm using 1 <;> norm_num
  have hmul2 : ρ * Real.rpow (d : ℝ) 0.01 = Real.rpow (d : ℝ) (-0.01) := by
    convert (Real.rpow_add hp (-0.02) 0.01).symm using 1 <;> norm_num
  have hexponent : (Real.rpow (d : ℝ) (-0.04) + 4 * ρ) * m ≤ 1 := by
    have h1 := calibration_rpow_tenth d hd 0.03 (by norm_num)
    have h2 := calibration_rpow_tenth d hd 0.01 (by norm_num)
    nlinarith only [hb, hmul1, hmul2, h1, h2]
  calc
    _ ≤ Real.exp (Real.rpow (d : ℝ) (-0.04) * m) * Real.exp (4 * ρ * m) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp ((Real.rpow (d : ℝ) (-0.04) + 4 * ρ) * m) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hexponent
    _ ≤ 4 := le_trans Real.exp_one_lt_three.le (by norm_num)

theorem role_pinned_charge_small (d h : ℕ) (ε : ℝ) (hd : 2 ≤ d) (hε : 0 < ε)
    (hroom : 16 * (d : ℝ) ^ 2 * (h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (d : ℝ) (-20)) :
    8 * d * Real.rpow ε (1 / 8 : ℝ) ≤ Real.rpow ε (1 / 16 : ℝ) / 2 := by
  let x := Real.rpow ε (1 / 16 : ℝ)
  have hx : 0 ≤ x := (Real.rpow_pos_of_pos hε _).le
  have hb := role_star_charge_budget d h ε hd hε hroom
  have hd2 : Real.rpow (d : ℝ) (-2) ≤ 1 / 4 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      _ ≤ Real.rpow (2 : ℝ) (-2) := Real.rpow_le_rpow_of_nonpos (by norm_num) hd' (by norm_num)
      _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have ht : (1 : ℝ) ≤ (h + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hl := mul_le_mul_of_nonneg_left ht (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hx)
  have hdx : 8 * d * x ≤ 1 / 2 := by
    dsimp [x] at *
    nlinarith
  have hsq : x * x = Real.rpow ε (1 / 8 : ℝ) := by
    convert (Real.rpow_add hε (1 / 16 : ℝ) (1 / 16 : ℝ)).symm using 1 <;> norm_num
  have hm := mul_le_mul_of_nonneg_right hdx hx
  rw [← hsq]
  dsimp [x] at *
  nlinarith

theorem nonneighbor_scopes {E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (scope : E → Finset V) (e : E) (R : Finset E) (he : e ∉ R)
    (hR : ∀ f ∈ R, f ∉ Finset.univ.filter fun f => f ≠ e ∧ ¬ Disjoint (scope e) (scope f)) :
    Disjoint (scope e) (R.biUnion scope) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb hb'
  obtain ⟨f, hf, hbf⟩ := Finset.mem_biUnion.mp hb'
  have hfe : f ≠ e := by intro hh; subst f; exact he hf
  have hdis : Disjoint (scope e) (scope f) := by
    by_contra hn
    exact hR f hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfe, hn⟩)
  exact Finset.disjoint_left.mp hdis hb hbf

theorem role_star_nonneighbor {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (e : Star) (R : Finset Star)
    (he : e ∉ R)
    (hR : ∀ f ∈ R, f ∉ (role_star_data P q seed charge pin touch).neighbors e) :
    (FinLaw.pi seed.laws).pr (fun ω => ω ∈ (role_star_data P q seed charge pin touch).bad e ∧
      ω ∈ (role_star_data P q seed charge pin touch).avoid R) =
      (FinLaw.pi seed.laws).pr (fun ω => ω ∈ (role_star_data P q seed charge pin touch).bad e) *
        (FinLaw.pi seed.laws).pr (fun ω => ω ∈ (role_star_data P q seed charge pin touch).avoid R) := by
  classical
  apply pi_pr_disjoint seed.laws _ _ ((P.participants e).image P.blockOf)
    (R.biUnion fun s => (P.participants s).image P.blockOf)
  · exact role_star_data_local P q seed charge pin touch e
  · exact role_avoid_local P q seed charge pin touch R
  · exact nonneighbor_scopes (fun s => (P.participants s).image P.blockOf) e R he hR

theorem role_star_pinned_nonneighbor {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ) (e : Star) (r : Role) (y : Label)
    (R : Finset Star) (he : e ∉ R)
    (hR : ∀ f ∈ R, f ∉ (role_star_data P q seed charge pin touch).neighbors e)
    (hBad : (FinLaw.pi seed.laws).pr (fun ω =>
      ω ∈ (role_star_data P q seed charge pin touch).bad e) ≤ pin e r y)
    (hPin : (FinLaw.pi seed.laws).pr (fun ω => P.readout ω r = y ∧
      ω ∈ (role_star_data P q seed charge pin touch).bad e) ≤ pin e r y * (q r).w y) :
    (FinLaw.pi seed.laws).pr (fun ω => P.readout ω r = y ∧
      ω ∈ (role_star_data P q seed charge pin touch).bad e ∧
      ω ∈ (role_star_data P q seed charge pin touch).avoid R) ≤
      pin e r y * (FinLaw.pi seed.laws).pr (fun ω => P.readout ω r = y ∧
        ω ∈ (role_star_data P q seed charge pin touch).avoid R) := by
  classical
  let A := role_star_data P q seed charge pin touch
  let V := (P.participants e).image P.blockOf
  let U := R.biUnion fun s => (P.participants s).image P.blockOf
  have hVU : Disjoint V U :=
    nonneighbor_scopes (fun s => (P.participants s).image P.blockOf) e R he hR
  by_cases hr : P.blockOf r ∈ V
  · have h1 := pi_pr_disjoint seed.laws
      (fun ω => P.readout ω r = y ∧ ω ∈ A.bad e) (fun ω => ω ∈ A.avoid R) V U
      (by
        intro ω ω' hω
        have hread : P.readout ω r = P.readout ω' r := by
          unfold RoleLabelProblem.readout
          rw [hω (P.blockOf r) hr]
        exact and_congr (by rw [hread]) (role_star_data_local P q seed charge pin touch e ω ω' hω))
      (role_avoid_local P q seed charge pin touch R) hVU
    have h2 := pi_pr_disjoint seed.laws (fun ω => P.readout ω r = y)
      (fun ω => ω ∈ A.avoid R) {P.blockOf r} U
      (by intro ω ω' hω; unfold RoleLabelProblem.readout; rw [hω _ (Finset.mem_singleton_self _)])
      (role_avoid_local P q seed charge pin touch R)
      (Finset.disjoint_left.mpr (by intro b hb hb'; rw [Finset.mem_singleton.mp hb] at hb'; exact Finset.disjoint_left.mp hVU hr hb'))
    rw [seed.marginal r y] at h2
    simp only [and_assoc] at h1
    change _ ≤ pin e r y * _
    rw [h1, h2]
    have hh := mul_le_mul_of_nonneg_right hPin
      (pr_range (FinLaw.pi seed.laws) (fun ω => ω ∈ A.avoid R)).1
    simpa only [mul_assoc] using hh
  · have hdis : Disjoint V (U ∪ {P.blockOf r}) := by
      apply Finset.disjoint_left.mpr
      intro b hb hbu
      rcases Finset.mem_union.mp hbu with hU | hsing
      · exact Finset.disjoint_left.mp hVU hb hU
      · exact hr (by rwa [Finset.mem_singleton.mp hsing] at hb)
    have h1 := pi_pr_disjoint seed.laws (fun ω => ω ∈ A.bad e)
      (fun ω => P.readout ω r = y ∧ ω ∈ A.avoid R) V (U ∪ {P.blockOf r})
      (role_star_data_local P q seed charge pin touch e)
      (by
        intro ω ω' hω
        have hread : P.readout ω r = P.readout ω' r := by
          unfold RoleLabelProblem.readout
          rw [hω (P.blockOf r) (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _)))]
        have hav := role_avoid_local P q seed charge pin touch R ω ω'
          (fun b hb => hω b (Finset.mem_union.mpr (Or.inl hb)))
        exact and_congr (by rw [hread]) hav) hdis
    have heq : (FinLaw.pi seed.laws).pr (fun ω => P.readout ω r = y ∧ ω ∈ A.bad e ∧ ω ∈ A.avoid R) =
        (FinLaw.pi seed.laws).pr (fun ω => ω ∈ A.bad e ∧ (P.readout ω r = y ∧ ω ∈ A.avoid R)) := by
      congr 1
      funext ω
      exact propext (by tauto)
    change _ ≤ pin e r y * _
    rw [heq, h1]
    exact mul_le_mul_of_nonneg_right hBad (pr_range (FinLaw.pi seed.laws) _).1

theorem finLaw_markov {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => t < f ω) ≤ P.E f / t := by
  classical
  have hm : t * P.pr (fun ω => t < f ω) ≤ P.E f := by
    unfold FinLaw.pr FinLaw.E
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : t < f ω
    · rw [if_pos hω]
      exact (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hω.le (P.nonneg ω))
    · rw [if_neg hω, mul_zero]
      exact mul_nonneg (P.nonneg ω) (hf ω)
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hm)

theorem group_star_markov_comparison {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Nonempty Bin]
    [Fintype Star] [Fintype Column] (P : GroupBinProblem Group Bin Star Column)
    (q : Group → FinLaw Bin) (s : Star) (c : ℝ) (hc : 0 ≤ c) (hε : 0 < P.ε)
    (hq : ∀ g ∈ P.participants s, ∀ b, (q g).w b ≤ c * (P.target g).w b)
    (hf : ∀ a, 0 ≤ P.failureMass s a)
    (hlocal : ∀ a a', (∀ g ∈ P.participants s, a g = a' g) → P.failureMass s a = P.failureMass s a')
    (hmean : P.independentFailure s ≤ Real.rpow P.ε (1 / 4 : ℝ)) :
    (FinLaw.pi q).pr (fun a => Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a) ≤
      c ^ (P.participants s).card * Real.rpow P.ε (1 / 8 : ℝ) := by
  have ht : 0 < Real.rpow P.ε (1 / 8 : ℝ) := Real.rpow_pos_of_pos hε _
  have hm := local_product_domination P.target q (P.participants s) c hc hq (P.failureMass s) hf hlocal
  have hMean : (FinLaw.pi q).E (P.failureMass s) ≤
      c ^ (P.participants s).card * Real.rpow P.ε (1 / 4 : ℝ) :=
    hm.trans (mul_le_mul_of_nonneg_left hmean (pow_nonneg hc _))
  have hprod : Real.rpow P.ε (1 / 4 : ℝ) =
      Real.rpow P.ε (1 / 8 : ℝ) * Real.rpow P.ε (1 / 8 : ℝ) := by
    convert Real.rpow_add hε (1 / 8 : ℝ) (1 / 8 : ℝ) using 1 <;> norm_num
  calc
    _ ≤ (FinLaw.pi q).E (P.failureMass s) / Real.rpow P.ε (1 / 8 : ℝ) :=
      finLaw_markov (FinLaw.pi q) (P.failureMass s) hf _ ht
    _ ≤ (c ^ (P.participants s).card * Real.rpow P.ε (1 / 4 : ℝ)) /
        Real.rpow P.ε (1 / 8 : ℝ) := div_le_div_of_nonneg_right hMean ht.le
    _ = _ := by rw [hprod]; field_simp [ht.ne']


/-- Count event scopes through the actual block incidence relation. -/
theorem role_star_scope_counts {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (charge : Star → ℝ)
    (pin : Star → Role → Label → ℝ) (touch : ℝ)
    (hSize : ∀ s, (P.participants s).card ≤ P.h)
    (hDegree : ∀ b, (Finset.univ.filter fun s => ∃ r ∈ P.participants s,
      P.blockOf r = b).card ≤ P.d * P.h) :
    (∀ S, ((role_star_data P q seed charge pin touch).touching S).card ≤
      S.card * (P.d * P.h)) ∧
    (∀ s, ((role_star_data P q seed charge pin touch).neighbors s).card ≤
      P.h * (P.d * P.h)) := by
  classical
  let stars := fun r : Role => Finset.univ.filter fun s : Star =>
    P.blockOf r ∈ (P.participants s).image P.blockOf
  have hc : ∀ r, (stars r).card ≤ P.d * P.h := by
    intro r
    have heq : stars r = Finset.univ.filter (fun s : Star =>
        ∃ r' ∈ P.participants s, P.blockOf r' = P.blockOf r) := by
      apply Finset.ext
      intro s
      change (s ∈ Finset.univ.filter _) ↔ (s ∈ Finset.univ.filter _)
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_image]
    rw [heq]
    exact hDegree (P.blockOf r)
  have hUnion : ∀ S : Finset Role, (S.biUnion stars).card ≤ S.card * (P.d * P.h) := by
    intro S
    calc
      _ ≤ ∑ r ∈ S, (stars r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ S, P.d * P.h := Finset.sum_le_sum fun r _ => hc r
      _ = _ := by simp
  constructor
  · intro S
    have heq : (role_star_data P q seed charge pin touch).touching S = S.biUnion stars := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        obtain ⟨r, hr, hb⟩ := (Finset.mem_filter.mp hs).2
        apply Finset.mem_biUnion.mpr
        refine ⟨r, hr, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
      · intro hs
        obtain ⟨r, hr, hb⟩ := Finset.mem_biUnion.mp hs
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, r, hr, (Finset.mem_filter.mp hb).2⟩
    rw [heq]
    exact hUnion S
  · intro s
    have hsub : (role_star_data P q seed charge pin touch).neighbors s ⊆
        (P.participants s).biUnion stars := by
      intro f hf
      have hnd := (Finset.mem_filter.mp hf).2.2
      obtain ⟨b, hb, hbf⟩ := Finset.not_disjoint_iff.mp hnd
      obtain ⟨r, hr, hrb⟩ := Finset.mem_image.mp hb
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rwa [hrb]⟩
    exact (Finset.card_le_card hsub).trans
      ((hUnion _).trans (Nat.mul_le_mul_right _ (hSize s)))

/-- Seed comparison also applies after adding a singleton pin to a star. -/
theorem role_seed_event_bound {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (hd : (10 ^ 100 : ℕ) ≤ P.d)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.02)))
    (S : Finset Role) (hQuery : (S.card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025)
    (hShort : (S.card : ℝ) ≤ 2 * Real.rpow (P.d : ℝ) 0.01)
    (A : (Role → Label) → Prop)
    (hlocal : ∀ x y, (∀ r ∈ S, x r = y r) → (A x ↔ A y)) :
    (FinLaw.pi seed.laws).pr (fun ω => A (P.readout ω)) ≤
      4 * (FinLaw.pi P.target).pr A := by
  classical
  let c := (1 + Real.rpow (P.d : ℝ) (-0.02)) / (1 - Real.rpow (P.d : ℝ) (-0.02))
  have hρ := (calibration_power_bounds P.d hd).2
  have hc : 0 ≤ c := by
    apply div_nonneg
    · have hh : 0 ≤ Real.rpow (P.d : ℝ) (-0.02) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    · linarith
  have hseed := role_seed_local_comparison P q seed S
    (fun b => le_trans (by exact_mod_cast Finset.card_filter_le S _) hQuery) A hlocal
  have hprod : (FinLaw.pi q).pr A ≤ c ^ S.card * (FinLaw.pi P.target).pr A := by
    rw [pr_eq_indicator_E, pr_eq_indicator_E]
    apply local_product_domination P.target q S c hc
    · intro r _ y
      exact (hq r y).2
    · intro x
      split_ifs <;> norm_num
    · intro x y hxy
      rw [hlocal x y hxy]
  calc
    _ ≤ Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) *
        (c ^ S.card * (FinLaw.pi P.target).pr A) :=
      hseed.trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le)
    _ = (Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) * c ^ S.card) *
        (FinLaw.pi P.target).pr A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (role_local_inflation P.d S.card hd hShort)
      (pr_range _ _).1

/-- Supported pins have enough mass to turn the joint seed comparison into
an unconditional bound on the pinned star. -/
theorem role_seed_failure_bounds {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label)
    (seed : RoleBlockSeed P q) (ε : ℝ) (hε : 0 < ε)
    (hd : (10 ^ 100 : ℕ) ≤ P.d)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.02)))
    (hSize : ∀ s, (P.participants s).card ≤ P.h)
    (hQuery : (P.h + 1 : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025)
    (hShort : (P.h + 1 : ℝ) ≤ 2 * Real.rpow (P.d : ℝ) 0.01)
    (hMean : ∀ s, P.independentStarFailure s ≤ Real.rpow ε (1 / 8 : ℝ))
    (hLower : ∀ r y, (P.target r).w y ≠ 0 → 1 / (P.d : ℝ) ≤ (P.target r).w y)
    (hroom : 16 * (P.d : ℝ) ^ 2 * (P.h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (P.d : ℝ) (-20)) :
    (∀ s, (FinLaw.pi seed.laws).pr (fun ω => P.starBad s (P.readout ω)) ≤
      Real.rpow ε (1 / 16 : ℝ) / 2) ∧
    (∀ s r y, (FinLaw.pi seed.laws).pr
      (fun ω => P.readout ω r = y ∧ P.starBad s (P.readout ω)) ≤
      (Real.rpow ε (1 / 16 : ℝ) / 2) * (q r).w y) := by
  classical
  have hd2 : 2 ≤ P.d := le_trans (by norm_num) hd
  have hdp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  have hρ := (calibration_power_bounds P.d hd).2
  have hfactor : 1 / 2 ≤ (1 - Real.rpow (P.d : ℝ) (-0.02)) /
      (1 + Real.rpow (P.d : ℝ) (-0.02)) := by
    apply (le_div_iff₀ (by
      have hh : 0 ≤ Real.rpow (P.d : ℝ) (-0.02) := Real.rpow_nonneg hdp.le _
      linarith)).mpr
    linarith
  have hsmall := role_pinned_charge_small P.d P.h ε hd2 hε hroom
  have hS : ∀ s, ((P.participants s).card : ℝ) ≤ (P.h + 1 : ℝ) := by
    intro s
    calc
      _ ≤ (P.h : ℝ) := by exact_mod_cast hSize s
      _ ≤ _ := by norm_num
  have hI : ∀ s r, ((insert r (P.participants s)).card : ℝ) ≤ (P.h + 1 : ℝ) := by
    intro s r
    have hs := hSize s
    exact_mod_cast (Finset.card_insert_le r (P.participants s)).trans (by omega)
  have hjoint : ∀ s r y, (FinLaw.pi seed.laws).pr
      (fun ω => P.readout ω r = y ∧ P.starBad s (P.readout ω)) ≤
        4 * Real.rpow ε (1 / 8 : ℝ) := by
    intro s r y
    have hcomp := role_seed_event_bound P q seed hd hq (insert r (P.participants s))
      ((hI s r).trans hQuery) ((hI s r).trans hShort)
      (fun x => x r = y ∧ P.starBad s x) (by
        intro x x' hxx
        exact and_congr (by rw [hxx r (Finset.mem_insert_self _ _)])
          (P.star_local s x x' (fun r' hr' => hxx r' (Finset.mem_insert_of_mem hr'))))
    have hmono := pr_mono (FinLaw.pi P.target) (fun x => x r = y ∧ P.starBad s x)
      (P.starBad s) (fun _ hh => hh.2)
    exact hcomp.trans (mul_le_mul_of_nonneg_left (hmono.trans (hMean s)) (by norm_num))
  constructor
  · intro s
    have hcomp := role_seed_event_bound P q seed hd hq (P.participants s)
      ((hS s).trans hQuery) ((hS s).trans hShort) (P.starBad s) (P.star_local s)
    have hm := hcomp.trans (mul_le_mul_of_nonneg_left (hMean s) (by norm_num))
    have hdreal : (2 : ℝ) ≤ P.d := by exact_mod_cast hd2
    have he : 0 ≤ Real.rpow ε (1 / 8 : ℝ) := Real.rpow_nonneg hε.le _
    nlinarith
  · intro s r y
    by_cases hqy : (q r).w y = 0
    · have hm := pr_mono (FinLaw.pi seed.laws)
        (fun ω => P.readout ω r = y ∧ P.starBad s (P.readout ω))
        (fun ω => P.readout ω r = y) (fun _ hh => hh.1)
      rw [seed.marginal r y, hqy] at hm
      simpa only [hqy, mul_zero] using hm
    · have hpy : (P.target r).w y ≠ 0 := by
        intro hh
        have hb := (hq r y).2
        rw [hh, mul_zero] at hb
        exact hqy (le_antisymm hb ((q r).nonneg y))
      have hlow : 1 / (2 * (P.d : ℝ)) ≤ (q r).w y := by
        have hh := mul_le_mul_of_nonneg_right hfactor ((P.target r).nonneg y)
        have hl := mul_le_mul_of_nonneg_left (hLower r y hpy) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have hle := hl.trans (hh.trans (hq r y).1)
        convert hle using 1 <;> ring
      have hmass : 1 ≤ (2 * (P.d : ℝ)) * (q r).w y := by
        have hh := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * (P.d : ℝ))
        field_simp at hh
        nlinarith
      have he := mul_le_mul_of_nonneg_left hmass
        (show 0 ≤ 4 * Real.rpow ε (1 / 8 : ℝ) from
          mul_nonneg (by norm_num) (Real.rpow_nonneg hε.le _))
      have hh := mul_le_mul_of_nonneg_right hsmall ((q r).nonneg y)
      exact (hjoint s r y).trans (by nlinarith)


theorem role_avoidance_rate_budget (d : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d) :
    Real.rpow (d : ℝ) (-0.04) +
      Real.log ((1 + Real.rpow (d : ℝ) (-0.02)) / (1 - Real.rpow (d : ℝ) (-0.02))) +
      Real.rpow (d : ℝ) (-2) ≤ Real.rpow (d : ℝ) (-0.01) := by
  have hp : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 100) hd
  let ρ := Real.rpow (d : ℝ) (-0.02)
  have hρ : 0 ≤ ρ ∧ ρ ≤ 1 / 3 :=
    ⟨(Real.rpow_pos_of_pos hp _).le, (calibration_power_bounds d hd).2⟩
  have hc : 0 < (1 + ρ) / (1 - ρ) := div_pos (by linarith) (by linarith)
  have hlog : Real.log ((1 + ρ) / (1 - ρ)) ≤ 4 * ρ := by
    have hh := Real.log_le_log hc (relative_factor_exp ρ hρ)
    simpa only [Real.log_exp] using hh
  have h1 := calibration_rpow_tenth d hd 0.03 (by norm_num)
  have h2 := calibration_rpow_tenth d hd 0.01 (by norm_num)
  have h3 := calibration_rpow_tenth d hd 1.99 (by norm_num)
  have hmul (a b : ℝ) : Real.rpow (d : ℝ) a * Real.rpow (d : ℝ) b =
      Real.rpow (d : ℝ) (a + b) := (Real.rpow_add hp a b).symm
  have hh1 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le (-0.01))
  have hh2 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hp.le (-0.01))
  have hh3 := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hp.le (-0.01))
  simp only [← Real.rpow_eq_pow] at hh1 hh2 hh3
  rw [hmul] at hh1 hh2 hh3
  norm_num only at hh1 hh2 hh3
  change Real.log ((1 + Real.rpow (d : ℝ) (-0.02)) /
    (1 - Real.rpow (d : ℝ) (-0.02))) ≤ 4 * Real.rpow (d : ℝ) (-0.02) at hlog
  norm_num only at hlog ⊢
  have hn : 0 ≤ Real.rpow (d : ℝ) (-(1 / 100 : ℝ)) := Real.rpow_nonneg hp.le _
  nlinarith only [hlog, hh1, hh2, hh3, hn]

/-- Complete primitive avoidance certificate for independent whole-bin seeds. -/
theorem role_star_certificates {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label] [Nonempty Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (ε : ℝ) (hε : 0 < ε)
    (hd : (10 ^ 100 : ℕ) ≤ P.d) (hRegime : P.regime = .cluster)
    (hSize : ∀ s, (P.participants s).card ≤ P.h)
    (hDegree : ∀ b, (Finset.univ.filter fun s => ∃ r ∈ P.participants s,
      P.blockOf r = b).card ≤ P.d * P.h)
    (hQuery : (P.h + 1 : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025)
    (hShort : (P.h + 1 : ℝ) ≤ 2 * Real.rpow (P.d : ℝ) 0.01)
    (hMean : ∀ s, P.independentStarFailure s ≤ Real.rpow ε (1 / 8 : ℝ))
    (hLower : ∀ r y, (P.target r).w y ≠ 0 → 1 / (P.d : ℝ) ≤ (P.target r).w y)
    (hroom : 16 * (P.d : ℝ) ^ 2 * (P.h + 1 : ℝ) ^ 2 * Real.rpow ε (1 / 16 : ℝ) ≤
      Real.rpow (P.d : ℝ) (-20))
    (q : Role → FinLaw Label)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.02)))
    (seed : RoleBlockSeed P q) :
    ∃ A : AvoidanceData P.readout P.blockOf P.safe,
      A.base = FinLaw.pi seed.laws ∧
      AvoidanceHypotheses A P.target q P.queries (Real.rpow (P.d : ℝ) (-0.02))
        (Real.rpow (P.d : ℝ) (-2)) P.rate := by
  classical
  let x := Real.rpow ε (1 / 16 : ℝ)
  let η := Real.rpow (P.d : ℝ) (-2)
  let A := role_star_data P q seed (fun _ => x) (fun _ _ _ => x / 2) η
  have hd2 : 2 ≤ P.d := le_trans (by norm_num) hd
  have hdp : (0 : ℝ) < P.d := by exact_mod_cast (by omega : 0 < P.d)
  have hx : 0 < x := Real.rpow_pos_of_pos hε _
  have hη : 0 < η := Real.rpow_pos_of_pos hdp _
  have hηsmall : η ≤ 1 / 4 := by
    calc
      _ ≤ Real.rpow (2 : ℝ) (-2) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hd2) (by norm_num)
      _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hb := role_star_charge_budget P.d P.h ε hd2 hε hroom
  change (P.d : ℝ) * (P.h + 1 : ℝ) ^ 2 * x ≤ η / 16 at hb
  have hh : (0 : ℝ) ≤ P.h := Nat.cast_nonneg _
  have hfactor : (1 : ℝ) ≤ (P.d : ℝ) * (P.h + 1 : ℝ) ^ 2 := by
    have hd' : (2 : ℝ) ≤ P.d := by exact_mod_cast hd2
    nlinarith [sq_nonneg (P.h : ℝ)]
  have hxb : x ≤ η / 16 := by
    have hm := mul_le_mul_of_nonneg_right hfactor hx.le
    nlinarith
  have hxhalf : x ≤ 1 / 2 := by linarith
  have hxone : x < 1 := by linarith
  have hOne : (P.d : ℝ) * P.h * x ≤ η / 16 := by
    have hh' : (P.h : ℝ) ≤ (P.h + 1 : ℝ) ^ 2 := by nlinarith [sq_nonneg (P.h : ℝ)]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh' hdp.le) hx.le).trans hb
  have hNeighbor : (P.h : ℝ) * (P.d * P.h : ℕ) * x ≤ η / 16 := by
    have hh' : (P.h : ℝ) ^ 2 ≤ (P.h + 1 : ℝ) ^ 2 := by nlinarith
    have hm := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh' hdp.le) hx.le).trans hb
    push_cast
    nlinarith only [hm]
  obtain ⟨hTouchCard, hNeighborCard⟩ := role_star_scope_counts P q seed
    (fun _ => x) (fun _ _ _ => x / 2) η hSize hDegree
  have hTouchSum : ∀ S : Finset Role, (∑ e ∈ A.touching S, A.charge e) ≤
      (S.card : ℝ) * (η / 16) := by
    intro S
    have hc : ((A.touching S).card : ℝ) ≤ (S.card : ℝ) * (P.d * P.h : ℕ) := by
      exact_mod_cast hTouchCard S
    change (∑ _e ∈ A.touching S, x) ≤ _
    rw [Finset.sum_const, nsmul_eq_mul]
    have hm := mul_le_mul_of_nonneg_right hc hx.le
    have hh' := mul_le_mul_of_nonneg_left hOne (Nat.cast_nonneg (α := ℝ) S.card)
    push_cast at hm
    nlinarith only [hm, hh']
  have hNeighborSum : ∀ s, (∑ e ∈ A.neighbors s, A.charge e) ≤ η / 16 := by
    intro s
    have hc : ((A.neighbors s).card : ℝ) ≤ (P.h : ℝ) * (P.d * P.h : ℕ) := by
      exact_mod_cast hNeighborCard s
    change (∑ _e ∈ A.neighbors s, x) ≤ _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right hc hx.le).trans hNeighbor
  have hRecip : ∀ s, (∏ e ∈ A.neighbors s, (1 - A.charge e)⁻¹) ≤ 2 := by
    intro s
    have hsum := hNeighborSum s
    have hm := avoidance_reciprocal_bound (A.neighbors s) A.charge (1 / 2)
      (by norm_num) (fun _ _ => ⟨hx.le, hxone⟩) (by linarith)
    norm_num only [inv_div, inv_one, div_one] at hm
    exact hm
  have hBadPin := role_seed_failure_bounds P q seed ε hε hd hq hSize hQuery hShort hMean hLower hroom
  have hBad : ∀ e, A.base.pr (fun ω => ω ∈ A.bad e) ≤ x / 2 := by
    intro e
    simpa only [A, role_star_data, Finset.mem_filter, Finset.mem_univ, true_and] using hBadPin.1 e
  have hPin : ∀ e r y, A.base.pr (fun ω => P.readout ω r = y ∧ ω ∈ A.bad e) ≤
      (x / 2) * (q r).w y := by
    intro e r y
    simpa only [A, role_star_data, Finset.mem_filter, Finset.mem_univ, true_and] using hBadPin.2 e r y
  refine ⟨A, rfl, ?_⟩
  refine {
    rho_range := ⟨Real.rpow_pos_of_pos hdp _, (calibration_power_bounds P.d hd).2⟩
    eta_range := ⟨hη.le, by linarith⟩
    perturbation := hq
    base_marginals := seed.marginal
    safe_cover := role_star_data_safe_cover P q seed _ _ _
    charge_range := fun _ => ⟨hx.le, hxone⟩
    nonneighbor := ?_
    charge_dominates := ?_
    pinned_nonneighbor := ?_
    pinned_outside := role_pin_outside P q seed _ _ _
    pinned_bounds_nonneg := fun _ _ _ => by dsimp [A, role_star_data]; positivity
    pinned_touch_budget := ?_
    singleton_cost := ?_
    base_joint := ?_
    query_outside := ?_
    joint_cost := ?_
    rate_budget := ?_ }
  · intro e S he hS
    exact (role_star_nonneighbor P q seed _ _ _ e S he hS).le
  · intro e
    have hl := avoidance_product_lower (A.neighbors e) A.charge
      (fun _ _ => ⟨hx.le, hxone.le⟩)
    have hsum := hNeighborSum e
    have hp : 1 / 2 ≤ ∏ f ∈ A.neighbors e, (1 - A.charge f) := by linarith
    have hm := mul_le_mul_of_nonneg_left hp hx.le
    change _ ≤ x * _
    exact (hBad e).trans (by nlinarith only [hm])
  · intro e r y S he hS
    exact role_star_pinned_nonneighbor P q seed _ _ _ e r y S he hS (hBad e) (hPin e r y)
  · intro r y
    have hm : (∑ e ∈ A.touching {r}, A.pinnedBound e r y *
        ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) ≤ ∑ e ∈ A.touching {r}, A.charge e := by
      apply Finset.sum_le_sum
      intro e _
      change (x / 2) * _ ≤ x
      have hh' := mul_le_mul_of_nonneg_left (hRecip e) (by positivity : 0 ≤ x / 2)
      nlinarith only [hh']
    have hs := hTouchSum {r}
    simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hs
    exact hm.trans (hs.trans (by linarith))
  · intro r
    apply avoidance_singleton_cost (A.touching {r}) A.charge η ⟨hη.le, by linarith⟩
      (fun _ _ => ⟨hx.le, hxone⟩)
    have hs := hTouchSum {r}
    simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hs
    linarith
  · intro S ys hS
    apply seed.joint
    simp only [RoleLabelProblem.queries, hRegime] at hS
    intro b
    have hh' : ((S.filter fun r => P.blockOf r = b).card : ℝ) ≤ P.h := by
      exact_mod_cast hS b
    exact hh'.trans (le_trans (by norm_num : (P.h : ℝ) ≤ P.h + 1) hQuery)
  · intro S ys R _ hR
    exact role_query_outside P q seed _ _ _ S ys R hR
  · intro S _
    have hm := avoidance_joint_cost (A.touching S) A.charge (fun _ _ => ⟨hx.le, hxhalf⟩)
    apply hm.trans
    apply Real.exp_le_exp.mpr
    have hs := hTouchSum S
    change 2 * _ ≤ η * S.card
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  · simpa only [A, role_star_data, RoleLabelProblem.rate, hRegime] using
      role_avoidance_rate_budget P.d hd


noncomputable def coordinatePin {I O : Type*} [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (i : I) (o : O) : I → FinLaw O :=
  fun j => if j = i then FinLaw.dirac o else P j

theorem coordinate_pin_weight {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (i : I) (o : O) (a : I → O) :
    (if a i = o then (FinLaw.pi P).w a else 0) =
      (P i).w o * (FinLaw.pi (coordinatePin P i o)).w a := by
  classical
  have hprod : (FinLaw.pi (coordinatePin P i o)).w a =
      (if a i = o then 1 else 0) * ∏ j ∈ Finset.univ.erase i, (P j).w (a j) := by
    change (∏ j, (coordinatePin P i o j).w (a j)) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have heq : ∀ j ∈ Finset.univ.erase i, (coordinatePin P i o j).w (a j) = (P j).w (a j) := by
      intro j hj
      simp only [coordinatePin, if_neg (Finset.mem_erase.mp hj).1]
    rw [show (∏ j ∈ Finset.univ.erase i, (coordinatePin P i o j).w (a j)) =
      ∏ j ∈ Finset.univ.erase i, (P j).w (a j) from Finset.prod_congr rfl heq]
    simp [coordinatePin, FinLaw.dirac]
  rw [hprod]
  by_cases hai : a i = o
  · rw [if_pos hai, if_pos hai, one_mul]
    change (∏ j, (P j).w (a j)) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hai]
  · simp [hai]

theorem coordinate_pin_E {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (i : I) (o : O) (f : (I → O) → ℝ) :
    (FinLaw.pi P).E (fun a => if a i = o then f a else 0) =
      (P i).w o * (FinLaw.pi (coordinatePin P i o)).E f := by
  classical
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (FinLaw.pi P).w a * (if a i = o then f a else 0) =
    (P i).w o * ((FinLaw.pi (coordinatePin P i o)).w a * f a)
  have h := coordinate_pin_weight P i o a
  by_cases hai : a i = o
  · rw [if_pos hai] at h ⊢
    rw [h]
    ring
  · rw [if_neg hai] at h ⊢
    rw [mul_zero, ← mul_assoc, ← h, zero_mul]

theorem coordinate_pin_pr {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (i : I) (o : O) (A : (I → O) → Prop) :
    (FinLaw.pi P).pr (fun a => a i = o ∧ A a) =
      (P i).w o * (FinLaw.pi (coordinatePin P i o)).pr A := by
  classical
  have h := coordinate_pin_E P i o (fun a => if A a then 1 else 0)
  rw [pr_eq_indicator_E, pr_eq_indicator_E]
  convert h using 1
  congr 1
  funext a
  by_cases ha : a i = o <;> by_cases hA : A a <;> simp [ha, hA]

theorem finLaw_union_bound {Ω E : Type*} [Fintype Ω] [DecidableEq E]
    (P : FinLaw Ω) (S : Finset E) (A : E → Ω → Prop) :
    P.pr (fun ω => ∃ e ∈ S, A e ω) ≤ ∑ e ∈ S, P.pr (A e) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ e ∈ S, A e ω
  · rw [if_pos h]
    obtain ⟨e, he, hAe⟩ := h
    have hh := Finset.single_le_sum (s := S) (f := fun e => if A e ω then P.w ω else 0)
      (fun e _ => by split_ifs <;> first | exact P.nonneg ω | exact le_rfl) he
    rwa [if_pos hAe] at hh
  · rw [if_neg h]
    exact Finset.sum_nonneg fun e _ => by split_ifs <;> first | exact P.nonneg ω | exact le_rfl

theorem pi_pair_collision {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] (P : I → FinLaw O) (i j : I) (hij : i ≠ j) (α : ℝ)
    (hcap : ∀ o, (P j).w o ≤ α) :
    (FinLaw.pi P).pr (fun a => a i = a j) ≤ α := by
  classical
  have hUnion : (FinLaw.pi P).pr (fun a => a i = a j) ≤
      ∑ o : O, (FinLaw.pi P).pr (fun a => a i = o ∧ a j = o) := by
    apply le_trans (le_of_eq _) (finLaw_union_bound (FinLaw.pi P) (Finset.univ : Finset O)
      (fun o a => a i = o ∧ a j = o))
    congr 1
    funext a
    exact propext (by simp; aesop)
  have hRow : ∀ o, (FinLaw.pi P).pr (fun a => a i = o ∧ a j = o) =
      (P i).w o * (P j).w o := by
    intro o
    have h := pi_pr_disjoint (fun i => P i) (fun a => a i = o) (fun a => a j = o) {i} {j}
      (by intro a b hab; rw [hab i (Finset.mem_singleton_self _)])
      (by intro a b hab; rw [hab j (Finset.mem_singleton_self _)])
      (by simpa using hij)
    rw [pi_coordinate_pr, pi_coordinate_pr] at h
    exact h
  calc
    _ ≤ ∑ o, (P i).w o * (P j).w o := by simpa only [hRow] using hUnion
    _ ≤ ∑ o, (P i).w o * α := Finset.sum_le_sum fun o _ =>
      mul_le_mul_of_nonneg_left (hcap o) ((P i).nonneg o)
    _ = α := by rw [← Finset.sum_mul, (P i).sum_one, one_mul]

/-- The crude ordered-pair union is sufficient once physical atoms are tiny. -/
theorem pi_repeated_bins {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (S : Finset I) (α : ℝ) (hα : 0 ≤ α)
    (hcap : ∀ i ∈ S, ∀ o, (P i).w o ≤ α) :
    (FinLaw.pi P).pr (fun a => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ a i = a j) ≤
      (S.card : ℝ) ^ 2 * α := by
  classical
  let pairs := S ×ˢ S
  have hUnion : (FinLaw.pi P).pr (fun a => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ a i = a j) ≤
      ∑ ij ∈ pairs, (FinLaw.pi P).pr (fun a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) := by
    apply le_trans (le_of_eq _) (finLaw_union_bound (FinLaw.pi P) pairs
      (fun ij a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2))
    congr 1
    funext a
    simp only [pairs, Finset.mem_product]
    exact propext (by aesop)
  have hEach : ∀ ij ∈ pairs, (FinLaw.pi P).pr (fun a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) ≤ α := by
    intro ij hij
    by_cases hne : ij.1 ≠ ij.2
    · have heq : (fun a : I → O => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) =
          (fun a => a ij.1 = a ij.2) := by funext a; exact propext (and_iff_right hne)
      rw [heq]
      exact pi_pair_collision P ij.1 ij.2 hne α (hcap ij.2 (Finset.mem_product.mp hij).2)
    · simpa [hne, FinLaw.pr] using hα
  exact hUnion.trans (by
    calc
      _ ≤ ∑ _ij ∈ pairs, α := Finset.sum_le_sum hEach
      _ = _ := by simp [pairs, pow_two])

theorem group_local_inflation (d m : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d)
    (hm : (m : ℝ) ≤ 2 * Real.rpow (d : ℝ) 0.01) :
    (((1 + Real.rpow (d : ℝ) (-0.1)) / (1 - Real.rpow (d : ℝ) (-0.1))) ^ m) ≤ 4 := by
  have hp : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 100) hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 10 ^ 100) hd
  let ρ := Real.rpow (d : ℝ) (-0.1)
  let σ := Real.rpow (d : ℝ) (-0.02)
  have hρσ : ρ ≤ σ := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have hσ : σ ≤ 1 / 3 := (calibration_power_bounds d hd).2
  have hσpos : 0 ≤ σ := (Real.rpow_pos_of_pos hp _).le
  have hρpos : 0 ≤ ρ := (Real.rpow_pos_of_pos hp _).le
  have hf : (1 + ρ) / (1 - ρ) ≤ (1 + σ) / (1 - σ) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hh := role_local_inflation d m hd hm
  change Real.exp (Real.rpow (d : ℝ) (-0.04) * m) * ((1 + σ) / (1 - σ)) ^ m ≤ 4 at hh
  have he : 1 ≤ Real.exp (Real.rpow (d : ℝ) (-0.04) * m) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (Real.rpow_nonneg hp.le _) (Nat.cast_nonneg _)
  have hpow : 0 ≤ ((1 + σ) / (1 - σ)) ^ m :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hb := mul_le_mul_of_nonneg_right he hpow
  exact (pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hf m).trans (by nlinarith)


theorem pi_repeated_bins_pinned {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinLaw O) (S : Finset I) (g : I) (b : O) (α : ℝ) (hα : 0 ≤ α)
    (hcap : ∀ i ∈ S, ∀ o, (P i).w o ≤ α) :
    (FinLaw.pi (coordinatePin P g b)).pr
      (fun a => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ a i = a j) ≤ (S.card : ℝ) ^ 2 * α := by
  classical
  let Q := coordinatePin P g b
  let pairs := S ×ˢ S
  have hUnion : (FinLaw.pi Q).pr (fun a => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ a i = a j) ≤
      ∑ ij ∈ pairs, (FinLaw.pi Q).pr (fun a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) := by
    apply le_trans (le_of_eq _) (finLaw_union_bound (FinLaw.pi Q) pairs
      (fun ij a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2))
    congr 1
    funext a
    simp only [pairs, Finset.mem_product]
    exact propext (by aesop)
  have hEach : ∀ ij ∈ pairs, (FinLaw.pi Q).pr (fun a => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) ≤ α := by
    intro ij hij
    by_cases hne : ij.1 ≠ ij.2
    · have heq : (fun a : I → O => ij.1 ≠ ij.2 ∧ a ij.1 = a ij.2) =
          (fun a => a ij.1 = a ij.2) := by funext a; exact propext (and_iff_right hne)
      rw [heq]
      by_cases hjg : ij.2 = g
      · have hig : ij.1 ≠ g := by intro hh; exact hne (hh.trans hjg.symm)
        have hh := pi_pair_collision Q ij.2 ij.1 hne.symm α (by
          intro o
          simpa only [Q, coordinatePin, if_neg hig] using hcap ij.1 (Finset.mem_product.mp hij).1 o)
        simpa only [eq_comm] using hh
      · apply pi_pair_collision Q ij.1 ij.2 hne α
        intro o
        simpa only [Q, coordinatePin, if_neg hjg] using hcap ij.2 (Finset.mem_product.mp hij).2 o
    · simpa [hne, FinLaw.pr] using hα
  exact hUnion.trans (by
    calc
      _ ≤ ∑ _ij ∈ pairs, α := Finset.sum_le_sum hEach
      _ = _ := by simp [pairs, pow_two])

/-- Pinning fixes one row in both product laws, so its mass cancels before
comparison across the remaining participating groups. -/
theorem group_star_pinned_markov_comparison {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Nonempty Bin]
    [Fintype Star] [Fintype Column] (P : GroupBinProblem Group Bin Star Column)
    (q : Group → FinLaw Bin) (s : Star) (g : Group) (b : Bin)
    (c : ℝ) (hc : 1 ≤ c) (hε : 0 < P.ε)
    (hq : ∀ g ∈ P.participants s, ∀ b, (q g).w b ≤ c * (P.target g).w b)
    (hf : ∀ a, 0 ≤ P.failureMass s a)
    (hlocal : ∀ a a', (∀ g ∈ P.participants s, a g = a' g) → P.failureMass s a = P.failureMass s a')
    (hmean : P.pinnedFailure s g b ≤ Real.rpow P.ε (1 / 4 : ℝ))
    (hb : (P.target g).w b ≠ 0) :
    (FinLaw.pi (coordinatePin q g b)).pr
      (fun a => Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a) ≤
      c ^ (P.participants s).card * Real.rpow P.ε (1 / 8 : ℝ) := by
  classical
  have hDom : ∀ i ∈ P.participants s, ∀ y,
      (coordinatePin q g b i).w y ≤ c * (coordinatePin P.target g b i).w y := by
    intro i hi y
    by_cases hig : i = g
    · simp only [coordinatePin, if_pos hig]
      exact le_mul_of_one_le_left (FinLaw.nonneg _ _) hc
    · simpa only [coordinatePin, if_neg hig] using hq i hi y
  have hPinMean : (FinLaw.pi (coordinatePin P.target g b)).E (P.failureMass s) ≤
      Real.rpow P.ε (1 / 4 : ℝ) := by
    unfold GroupBinProblem.pinnedFailure GroupBinProblem.independentLaw at hmean
    rw [coordinate_pin_E, pi_coordinate_pr] at hmean
    rwa [mul_div_cancel_left₀ _ hb] at hmean
  have hCompare := local_product_domination (coordinatePin P.target g b) (coordinatePin q g b)
    (P.participants s) c (by linarith) hDom (P.failureMass s) hf hlocal
  have hMean := hCompare.trans
    (mul_le_mul_of_nonneg_left hPinMean (pow_nonneg (by linarith) _))
  have ht : 0 < Real.rpow P.ε (1 / 8 : ℝ) := Real.rpow_pos_of_pos hε _
  have hprod : Real.rpow P.ε (1 / 4 : ℝ) =
      Real.rpow P.ε (1 / 8 : ℝ) * Real.rpow P.ε (1 / 8 : ℝ) := by
    convert Real.rpow_add hε (1 / 8 : ℝ) (1 / 8 : ℝ) using 1 <;> norm_num
  calc
    _ ≤ (FinLaw.pi (coordinatePin q g b)).E (P.failureMass s) /
        Real.rpow P.ε (1 / 8 : ℝ) := finLaw_markov _ _ hf _ ht
    _ ≤ (c ^ (P.participants s).card * Real.rpow P.ε (1 / 4 : ℝ)) /
        Real.rpow P.ε (1 / 8 : ℝ) := div_le_div_of_nonneg_right hMean ht.le
    _ = _ := by rw [hprod]; field_simp [ht.ne']


theorem finLaw_pr_or {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb, P.nonneg ω]

def group_star_bad {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) (s : Star) (a : Group → Bin) : Prop :=
  (∃ g ∈ P.participants s, ∃ g' ∈ P.participants s, g ≠ g' ∧ a g = a g') ∨
    Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a

theorem group_star_bad_local {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column)
    (hlocal : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set Group))
    (s : Star) (a a' : Group → Bin) (haa : ∀ g ∈ P.participants s, a g = a' g) :
    group_star_bad P s a ↔ group_star_bad P s a' := by
  unfold group_star_bad
  rw [hlocal s a a' haa]
  have heq : (∃ g ∈ P.participants s, ∃ g' ∈ P.participants s, g ≠ g' ∧ a g = a g') ↔
      (∃ g ∈ P.participants s, ∃ g' ∈ P.participants s, g ≠ g' ∧ a' g = a' g') := by
    constructor <;> rintro ⟨g, hg, g', hg', hne, heq⟩
    · exact ⟨g, hg, g', hg', hne, by rwa [← haa g hg, ← haa g' hg']⟩
    · exact ⟨g, hg, g', hg', hne, by rwa [haa g hg, haa g' hg']⟩
  exact or_congr heq Iff.rfl

/-- Both constituents of a group star have uniform unconditional and supported
pin estimates before adding capacity-subset events. -/
theorem group_star_event_bounds {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Nonempty Bin]
    [Fintype Star] [Fintype Column] (P : GroupBinProblem Group Bin Star Column)
    (hd : (10 ^ 100 : ℕ) ≤ P.d) (hε : 0 < P.ε)
    (hf : ∀ s a, 0 ≤ P.failureMass s a)
    (hlocal : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set Group))
    (hMean : ∀ s, P.independentFailure s ≤ Real.rpow P.ε (1 / 4 : ℝ))
    (hPinMean : ∀ s g b, P.pinnedFailure s g b ≤ Real.rpow P.ε (1 / 4 : ℝ))
    (hShort : ∀ s, ((P.participants s).card : ℝ) ≤ 2 * Real.rpow (P.d : ℝ) 0.01)
    (hAtom : ∀ g b, (P.target g).w b ≤ Real.rpow (P.d : ℝ) (-40))
    (q : Group → FinLaw Bin)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.1))) :
    (∀ s, (FinLaw.pi q).pr (group_star_bad P s) ≤
      4 * Real.rpow P.ε (1 / 8 : ℝ) +
        2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40)) ∧
    (∀ s g b, (FinLaw.pi q).pr (fun a => a g = b ∧ group_star_bad P s a) ≤
      (4 * Real.rpow P.ε (1 / 8 : ℝ) +
        2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40)) * (q g).w b) := by
  classical
  let c := (1 + Real.rpow (P.d : ℝ) (-0.1)) / (1 - Real.rpow (P.d : ℝ) (-0.1))
  have hρ : Real.rpow (P.d : ℝ) (-0.1) ≤ 1 / 3 := (calibration_power_bounds P.d hd).1
  have hρ0 : 0 ≤ Real.rpow (P.d : ℝ) (-0.1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc1 : 1 ≤ c := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - Real.rpow (P.d : ℝ) (-0.1))).mpr
    linarith
  have hc2 : c ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - Real.rpow (P.d : ℝ) (-0.1))).mpr
    linarith
  have hInflate : ∀ s, c ^ (P.participants s).card ≤ 4 :=
    fun s => group_local_inflation P.d _ hd (hShort s)
  have hqcap : ∀ g b, (q g).w b ≤ 2 * Real.rpow (P.d : ℝ) (-40) := by
    intro g b
    exact ((hq g b).2).trans ((mul_le_mul_of_nonneg_right hc2 ((P.target g).nonneg b)).trans
      (mul_le_mul_of_nonneg_left (hAtom g b) (by norm_num)))
  have hα : 0 ≤ 2 * Real.rpow (P.d : ℝ) (-40) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hStar : ∀ s, (FinLaw.pi q).pr (fun a => Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a) ≤
      4 * Real.rpow P.ε (1 / 8 : ℝ) := by
    intro s
    have hh := group_star_markov_comparison P q s c (by linarith) hε
      (fun g _ b => (hq g b).2) (hf s) (hlocal s) (hMean s)
    exact hh.trans (mul_le_mul_of_nonneg_right (hInflate s) (Real.rpow_nonneg hε.le _))
  constructor
  · intro s
    have hu := finLaw_pr_or (FinLaw.pi q)
      (fun a => ∃ g ∈ P.participants s, ∃ g' ∈ P.participants s, g ≠ g' ∧ a g = a g')
      (fun a => Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a)
    have hc := pi_repeated_bins q (P.participants s) _ hα (fun g _ b => hqcap g b)
    exact hu.trans (by nlinarith [hStar s])
  · intro s g b
    by_cases hqb : (q g).w b = 0
    · rw [coordinate_pin_pr, hqb, zero_mul, mul_zero]
    · have hpb : (P.target g).w b ≠ 0 := by
        intro hh
        have hb := (hq g b).2
        rw [hh, mul_zero] at hb
        exact hqb (le_antisymm hb ((q g).nonneg b))
      have hu := finLaw_pr_or (FinLaw.pi (coordinatePin q g b))
        (fun a => ∃ g ∈ P.participants s, ∃ g' ∈ P.participants s, g ≠ g' ∧ a g = a g')
        (fun a => Real.rpow P.ε (1 / 8 : ℝ) < P.failureMass s a)
      have hStarPin := group_star_pinned_markov_comparison P q s g b c hc1 hε
        (fun g _ b => (hq g b).2) (hf s) (hlocal s) (hPinMean s g b) hpb
      have hc := pi_repeated_bins_pinned q (P.participants s) g b _ hα (fun g _ b => hqcap g b)
      have hbound : (FinLaw.pi (coordinatePin q g b)).pr (group_star_bad P s) ≤
          4 * Real.rpow P.ε (1 / 8 : ℝ) +
            2 * ((P.participants s).card : ℝ) ^ 2 * Real.rpow (P.d : ℝ) (-40) := by
        have hh := hStarPin.trans (mul_le_mul_of_nonneg_right (hInflate s) (Real.rpow_nonneg hε.le _))
        exact hu.trans (by nlinarith)
      rw [coordinate_pin_pr]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound ((q g).nonneg b)


/-- Exponential host room pays the iid birthday budget uniformly in all cells. -/
theorem polynomial_birthday_room (K : ℝ) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (K + 1) * (n : ℝ) ^ (401 : ℕ) / (2 : ℝ) ^ n ≤
        Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n₁, hn₁⟩ := logarithmic_room 1 (Real.log 2 / 4)
    (Real.log (4 * (K + 1))) 401 (by norm_num) (by positivity) (by norm_num)
  refine ⟨max n₁ (max 2 ⌈(4 / Real.log 2) ^ (2 : ℕ)⌉₊), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound := hn₁ n (le_trans (Nat.le_max_left _ _) hn)
  simp only [Real.rpow_one] at hbound
  have hroot : 4 / Real.log 2 ≤ Real.sqrt (n : ℝ) := by
    have hh : (4 / Real.log 2) ^ (2 : ℕ) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_trans
        (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn))
    have hh' := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_sq (by positivity : 0 ≤ 4 / Real.log 2)] at hh'
  have hm : 4 ≤ Real.log 2 * Real.sqrt (n : ℝ) := by
    exact (div_le_iff₀ hc).mp hroot |>.trans_eq (mul_comm _ _)
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.log 2 / 4 * n := by
    have hh := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (n : ℝ))
    rw [mul_assoc, Real.mul_self_sqrt hnp.le] at hh
    nlinarith only [hh]
  have hexp : Real.log (4 * (K + 1)) + (401 : ℝ) * Real.log (n : ℝ) -
      (n : ℝ) * Real.log 2 ≤ -Real.sqrt (n : ℝ) := by
    have hcN : 0 ≤ Real.log 2 * n := mul_nonneg hc.le hnp.le
    nlinarith only [hbound, hsqrt, hcN]
  have he := Real.exp_le_exp.mpr hexp
  have hpow : Real.exp ((401 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (401 : ℕ) := by
    change Real.exp (((401 : ℕ) : ℝ) * Real.log (n : ℝ)) = _
    rw [Real.exp_nat_mul, Real.exp_log hnp]
  have hp2 : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (by linarith : 0 < 4 * (K + 1)), hpow, hp2] at he
  rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
  have htwo : (0 : ℝ) < 2 ^ n := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  convert he using 1 <;> ring

/-- The actual patch-capacity expression controls collisions, unlike the
weaker comparison-room estimate alone. -/
theorem pool_birthday_from_capacity (n ℓ L : ℕ) (B K : ℝ)
    (hn : 2 ≤ n) (hL : 0 < L) (hK : 0 ≤ K) (hℓ : ℓ ≤ n)
    (hprefix : (ℓ : ℝ) ≤ Real.log (n : ℝ))
    (hslots : (L : ℝ) ≤ (K + 1) * (n : ℝ) ^ (200 : ℕ))
    (hcapacity : (Real.rpow 2 ((n - ℓ : ℕ) : ℝ) / (n : ℝ) ^ (200 : ℕ)) * L ≤ B) :
    (L : ℝ) ^ 2 / B ≤ (K + 1) * (n : ℝ) ^ (401 : ℕ) / (2 : ℝ) ^ n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hp : (0 : ℝ) < (2 : ℝ) ^ (n - ℓ) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) ^ (200 : ℕ) := pow_pos hnp _
  have hcap : ((2 : ℝ) ^ (n - ℓ) / (n : ℝ) ^ (200 : ℕ)) * L ≤ B := by
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hcapacity
  have hB : 0 < B := lt_of_lt_of_le (mul_pos (div_pos hp hN) hLp) hcap
  have hsmall : (2 : ℝ) ^ ℓ ≤ n := by
    have he : (ℓ : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have hc : Real.log 2 ≤ 1 := le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) ℓ)
      linarith
    have hh := Real.exp_le_exp.mpr he
    rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hnp] at hh
  have hfactor : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n - ℓ) * n := by
    calc
      _ = (2 : ℝ) ^ (n - ℓ) * (2 : ℝ) ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hℓ]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hp.le
  calc
    _ ≤ (L : ℝ) ^ 2 / (((2 : ℝ) ^ (n - ℓ) / (n : ℝ) ^ (200 : ℕ)) * L) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (div_pos hp hN) hLp) hcap
    _ = (L : ℝ) * (n : ℝ) ^ (200 : ℕ) / (2 : ℝ) ^ (n - ℓ) := by field_simp <;> ring
    _ ≤ ((K + 1) * (n : ℝ) ^ (200 : ℕ)) * (n : ℝ) ^ (200 : ℕ) /
        (2 : ℝ) ^ (n - ℓ) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hslots hN.le) hp.le
    _ ≤ ((K + 1) * (n : ℝ) ^ (200 : ℕ)) * (n : ℝ) ^ (200 : ℕ) * n / (2 : ℝ) ^ n := by
      apply (div_le_div_iff₀ hp (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      have hh := mul_le_mul_of_nonneg_left hfactor
        (by positivity : 0 ≤ ((K + 1) * (n : ℝ) ^ (200 : ℕ)) * (n : ℝ) ^ (200 : ℕ))
      nlinarith only [hh]
    _ = _ := by ring


/-- A generating-function estimate for the sparse capacity subset charges. -/
theorem capacity_subset_product_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℝ) (t : ℕ) (hz : ∀ i ∈ S, 0 ≤ z i)
    (hsum : (∑ i ∈ S, z i) ≤ (t : ℝ) / 5) :
    (∑ A ∈ S.powersetCard t, ∏ i ∈ A, z i) ≤ (3 / 5 : ℝ) ^ t := by
  classical
  have hfamily : S.powersetCard t ⊆ S.powerset := by
    intro A hA
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hA).1
  have hprod : ∀ A ∈ S.powersetCard t, (5 : ℝ) ^ t * (∏ i ∈ A, z i) = ∏ i ∈ A, 5 * z i := by
    intro A hA
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hA).2]
  have hscaled : (5 : ℝ) ^ t * (∑ A ∈ S.powersetCard t, ∏ i ∈ A, z i) ≤ (3 : ℝ) ^ t := by
    calc
      _ = ∑ A ∈ S.powersetCard t, ∏ i ∈ A, 5 * z i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hprod
      _ ≤ ∑ A ∈ S.powerset, ∏ i ∈ A, 5 * z i :=
        Finset.sum_le_sum_of_subset_of_nonneg hfamily (fun A hA _ =>
          Finset.prod_nonneg (fun i hi => mul_nonneg (by norm_num)
            (hz i (Finset.mem_powerset.mp hA hi))))
      _ = ∏ i ∈ S, (1 + 5 * z i) := (Finset.prod_one_add S).symm
      _ ≤ ∏ i ∈ S, Real.exp (5 * z i) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          linarith [hz i hi]
        · intro i _
          simpa only [add_comm] using Real.add_one_le_exp (5 * z i)
      _ = Real.exp (5 * ∑ i ∈ S, z i) := by rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (t : ℝ) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp 1) ^ t := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ t := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le t
  have hp : (0 : ℝ) < 5 ^ t := by positivity
  have hh : (∑ A ∈ S.powersetCard t, ∏ i ∈ A, z i) ≤ (3 : ℝ) ^ t / 5 ^ t :=
    (le_div_iff₀ hp).mpr (by nlinarith only [hscaled])
  simpa only [div_pow] using hh

/-- Erasing the pinned group leaves an ordinary fixed-size subset sum. -/
theorem capacity_pinned_product_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℝ) (g : I) (hg : g ∈ S) (t : ℕ)
    (hz : ∀ i ∈ S, 0 ≤ z i)
    (hsum : (∑ i ∈ S.erase g, z i) ≤ (t : ℝ) / 5) :
    (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => g ∈ A),
      ∏ i ∈ A.erase g, z i) ≤ (3 / 5 : ℝ) ^ t := by
  classical
  have hEq : (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => g ∈ A),
      ∏ i ∈ A.erase g, z i) = ∑ B ∈ (S.erase g).powersetCard t, ∏ i ∈ B, z i := by
    apply Finset.sum_bij (fun A _ => A.erase g)
    · intro A hA
      obtain ⟨hAS, hgA⟩ := Finset.mem_filter.mp hA
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hAS
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro i hi
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, hsub (Finset.mem_erase.mp hi).2⟩
      · rw [Finset.card_erase_of_mem hgA, hcard]
        omega
    · intro A hA B hB hEq
      have hgA := (Finset.mem_filter.mp hA).2
      have hgB := (Finset.mem_filter.mp hB).2
      have hh := congrArg (insert g) hEq
      rwa [Finset.insert_erase hgA, Finset.insert_erase hgB] at hh
    · intro B hB
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
      have hgB : g ∉ B := fun hh => (Finset.mem_erase.mp (hsub hh)).1 rfl
      refine ⟨insert g B, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with hgi | hi
          · simpa only [hgi] using hg
          · exact (Finset.mem_erase.mp (hsub hi)).2
        · rw [Finset.card_insert_of_notMem hgB, hcard]
      · exact Finset.erase_insert hgB
    · intro A hA
      rfl
  rw [hEq]
  exact capacity_subset_product_bound _ z t (fun i hi => hz i (Finset.mem_erase.mp hi).2) hsum

/-- The lower edge of a bucket converts its load mean into a charge sum. -/
theorem capacity_bucket_mean_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (p q u : I → ℝ) (δ μ : ℝ)
    (hδ : 0 < δ) (hp : ∀ i ∈ S, 0 ≤ p i)
    (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 2 * p i)
    (hu : ∀ i ∈ S, δ / 2 ≤ u i)
    (hmean : (∑ i ∈ S, p i * u i) ≤ μ) :
    (∑ i ∈ S, 4 * q i) ≤ 16 * μ / δ := by
  have hh : δ * (∑ i ∈ S, 4 * q i) ≤ 16 * μ := by
    calc
      _ = ∑ i ∈ S, δ * (4 * q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ S, 16 * (p i * u i) := by
        apply Finset.sum_le_sum
        intro i hi
        have h1 := mul_le_mul_of_nonneg_left (hq i hi).2 hδ.le
        have h2 := mul_le_mul_of_nonneg_left (hu i hi) (hp i hi)
        nlinarith only [h1, h2]
      _ = 16 * ∑ i ∈ S, p i * u i := (Finset.mul_sum _ _ _).symm
      _ ≤ 16 * μ := mul_le_mul_of_nonneg_left hmean (by norm_num)
  exact (le_div_iff₀ hδ).mpr (by nlinarith only [hh])


/-- The positive physical atoms fit a finite dyadic family; there is no
infinite event index or summability obligation. -/
theorem capacity_dyadic_bucket_cover (d : ℕ) (δ u : ℝ) (hd : 1 ≤ d)
    (hδ : 0 < δ ∧ δ ≤ 1) (hu : 1 / (d : ℝ) ≤ u ∧ u ≤ δ) :
    ∃ j : ℕ, j < d ∧ δ / (2 : ℝ) ^ (j + 1) < u ∧ u ≤ δ / (2 : ℝ) ^ j := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow : (d : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast d.lt_two_pow_self
  have hsmall : δ / (2 : ℝ) ^ d < u := by
    calc
      _ ≤ 1 / (2 : ℝ) ^ d := div_le_div_of_nonneg_right hδ.2 (by positivity)
      _ < 1 / (d : ℝ) := (div_lt_div_iff₀ (by positivity) hdp).mpr (by simpa using hpow)
      _ ≤ u := hu.1
  have hex : ∃ j : ℕ, δ / (2 : ℝ) ^ j < u := ⟨d, hsmall⟩
  let t := Nat.find hex
  have ht : δ / (2 : ℝ) ^ t < u := Nat.find_spec hex
  have htd : t ≤ d := Nat.find_min' hex hsmall
  have htpos : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    rw [hz, pow_zero, div_one] at ht
    exact not_lt_of_ge hu.2 ht
  have htprev : u ≤ δ / (2 : ℝ) ^ (t - 1) := by
    exact le_of_not_gt (Nat.find_min hex (by omega : t - 1 < t))
  refine ⟨t - 1, by omega, ?_, htprev⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using ht

/-- Avoiding all fixed-size subset certificates enforces the bucket load. -/
theorem capacity_bucket_load_bound {I O : Type*} [DecidableEq I] [DecidableEq O]
    (S : Finset I) (a : I → O) (b : O) (u : I → ℝ) (δ τ : ℝ)
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (hu : ∀ i ∈ S, u i ≤ δ)
    (havoid : ∀ A : Finset I, A ⊆ S → A.card = ⌊τ / δ⌋₊ + 1 →
      ¬ ∀ i ∈ A, a i = b) :
    (∑ i ∈ S, if a i = b then u i else 0) ≤ τ := by
  classical
  let V := S.filter fun i => a i = b
  have hcard : V.card ≤ ⌊τ / δ⌋₊ := by
    by_contra hh
    have ht : ⌊τ / δ⌋₊ + 1 ≤ V.card := by omega
    obtain ⟨A, hAV, hAc⟩ := Finset.exists_subset_card_eq ht
    apply havoid A (hAV.trans (Finset.filter_subset _ _)) hAc
    intro i hi
    exact (Finset.mem_filter.mp (hAV hi)).2
  calc
    _ = ∑ i ∈ V, u i := (Finset.sum_filter _ _).symm
    _ ≤ ∑ _i ∈ V, δ := Finset.sum_le_sum fun i hi => hu i (Finset.mem_filter.mp hi).1
    _ = (V.card : ℝ) * δ := by simp
    _ ≤ (⌊τ / δ⌋₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hδ.le
    _ ≤ (τ / δ) * δ := mul_le_mul_of_nonneg_right
      (Nat.floor_le (div_nonneg hτ hδ.le)) hδ.le
    _ = τ := div_mul_cancel₀ τ hδ.ne'


/-- The double inflation pays both ordinary and reciprocal pinned costs. -/
theorem capacity_pinned_inflated_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → ℝ) (g : I) (hg : g ∈ S) (t : ℕ)
    (hq : ∀ i ∈ S, 0 ≤ q i)
    (hsum : (∑ i ∈ S.erase g, 4 * q i) ≤ (t : ℝ) / 5) :
    (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => g ∈ A),
      (4 : ℝ) ^ A.card * ∏ i ∈ A.erase g, q i) ≤ 4 * (3 / 5 : ℝ) ^ t := by
  classical
  have hh := capacity_pinned_product_bound S (fun i => 4 * q i) g hg t
    (fun i hi => mul_nonneg (by norm_num) (hq i hi)) hsum
  have heq : (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => g ∈ A),
      (4 : ℝ) ^ A.card * ∏ i ∈ A.erase g, q i) =
      4 * (∑ A ∈ (S.powersetCard (t + 1)).filter (fun A => g ∈ A),
        ∏ i ∈ A.erase g, 4 * q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    obtain ⟨hAS, hgA⟩ := Finset.mem_filter.mp hA
    have hc := (Finset.mem_powersetCard.mp hAS).2
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem hgA, hc]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

/-- A fixed large bin scale pays the total capacity charge over d columns
and d finite buckets, including supported singleton pins. -/
theorem capacity_total_charge_small (d m : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d)
    (hm : Real.rpow (d : ℝ) 0.4 ≤ (m : ℝ)) :
    4 * (d : ℝ) ^ 2 * (3 / 5 : ℝ) ^ m ≤ Real.rpow (d : ℝ) (-2) / 16 := by
  have hb : (10 : ℝ) ^ (100 : ℕ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hb
  have hd1 : (1 : ℝ) ≤ d := le_trans (by norm_num) hb
  have hdecay : Real.rpow (d : ℝ) (-0.2) ≤ 1 / 1000 := by
    calc
      _ ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (by norm_num)
      _ = Real.rpow 10 (100 * (-0.2)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 (-0.2)).symm
      _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hsmall : Real.rpow (d : ℝ) 0.2 ≤ (1 / 1000 : ℝ) * Real.rpow (d : ℝ) 0.4 := by
    have hh := mul_le_mul_of_nonneg_right hdecay (Real.rpow_nonneg hp.le 0.4)
    simp only [← Real.rpow_eq_pow] at hh
    have heq : Real.rpow (d : ℝ) (-0.2) * Real.rpow (d : ℝ) 0.4 = Real.rpow (d : ℝ) 0.2 := by
      convert (Real.rpow_add hp (-0.2) 0.4).symm using 1 <;> norm_num
    rw [heq] at hh
    exact hh
  have hlog : Real.log (d : ℝ) ≤ 5 * Real.rpow (d : ℝ) 0.2 := by
    have hh : Real.log (d : ℝ) ≤ Real.rpow (d : ℝ) 0.2 / 0.2 :=
      Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 0.2)
    have hid : Real.rpow (d : ℝ) 0.2 / 0.2 = 5 * Real.rpow (d : ℝ) 0.2 := by ring
    rwa [hid] at hh
  have hlog64 : Real.log (64 : ℝ) ≤ 64 :=
    le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
  have hpow1 : 1 ≤ Real.rpow (d : ℝ) 0.2 := Real.one_le_rpow hd1 (by norm_num)
  have hex : Real.log (64 : ℝ) + 4 * Real.log (d : ℝ) -
      0.4 * Real.rpow (d : ℝ) 0.4 ≤ 0 := by
    nlinarith only [hsmall, hlog, hlog64, hpow1]
  have he := Real.exp_le_exp.mpr hex
  have hd4 : Real.exp ((4 : ℝ) * Real.log (d : ℝ)) = (d : ℝ) ^ (4 : ℕ) := by
    change Real.exp (((4 : ℕ) : ℝ) * Real.log (d : ℝ)) = _
    rw [Real.exp_nat_mul, Real.exp_log hp]
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 64), hd4, Real.exp_zero] at he
  have hgeo : (3 / 5 : ℝ) ^ m ≤ Real.exp (-0.4 * Real.rpow (d : ℝ) 0.4) := by
    have hbase : (3 / 5 : ℝ) ≤ Real.exp (-0.4) := by
      have hh := Real.add_one_le_exp (-0.4)
      norm_num only at hh ⊢
      exact hh
    calc
      _ ≤ (Real.exp (-0.4)) ^ m := pow_le_pow_left₀ (by norm_num) hbase m
      _ = Real.exp (-0.4 * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hm])
  have hbudget : 64 * (d : ℝ) ^ (4 : ℕ) * Real.exp (-0.4 * Real.rpow (d : ℝ) 0.4) ≤ 1 := by
    rw [show -0.4 * Real.rpow (d : ℝ) 0.4 = -(0.4 * Real.rpow (d : ℝ) 0.4) by ring, Real.exp_neg]
    simpa only [div_eq_mul_inv] using he
  have hmul := mul_le_mul_of_nonneg_left hgeo (by positivity : 0 ≤ 64 * (d : ℝ) ^ (4 : ℕ))
  have hh := hmul.trans hbudget
  norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [inv_eq_one_div, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (d : ℝ) ^ 2 * (16 : ℝ))).mpr
  nlinarith only [hh]


/-- Weighted touching costs count each event once, even if several query
variables meet its scope. -/
theorem scope_touching_sum {I E : Type*} [DecidableEq I] [Fintype E] [DecidableEq E]
    (scope : E → Finset I) (x : E → ℝ) (b : ℝ) (hx : ∀ e, 0 ≤ x e)
    (hOne : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => i ∈ scope e), x e) ≤ b)
    (S : Finset I) :
    (∑ e ∈ Finset.univ.filter (fun e => ∃ i ∈ S, i ∈ scope e), x e) ≤ (S.card : ℝ) * b := by
  classical
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ e : E, ∑ i ∈ S, if i ∈ scope e then x e else 0 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : ∃ i ∈ S, i ∈ scope e
      · rw [if_pos he]
        obtain ⟨i, hi, hie⟩ := he
        have hh := Finset.single_le_sum (s := S) (f := fun i => if i ∈ scope e then x e else 0)
          (fun i _ => by split_ifs <;> first | exact hx e | exact le_rfl) hi
        rwa [if_pos hie] at hh
      · rw [if_neg he]
        exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact hx e | exact le_rfl
    _ = ∑ i ∈ S, ∑ e ∈ Finset.univ.filter (fun e => i ∈ scope e), x e := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_filter]
    _ ≤ ∑ _i ∈ S, b := Finset.sum_le_sum fun i _ => hOne i
    _ = _ := by simp

/-- The same incidence estimate controls the weighted neighbor cost. -/
theorem scope_neighbor_sum {I E : Type*} [DecidableEq I] [Fintype E] [DecidableEq E]
    (scope : E → Finset I) (x : E → ℝ) (b : ℝ) (hx : ∀ e, 0 ≤ x e)
    (hOne : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => i ∈ scope e), x e) ≤ b)
    (e : E) :
    (∑ f ∈ Finset.univ.filter (fun f => f ≠ e ∧ ¬ Disjoint (scope e) (scope f)), x f) ≤
      ((scope e).card : ℝ) * b := by
  classical
  have hsub : Finset.univ.filter (fun f => f ≠ e ∧ ¬ Disjoint (scope e) (scope f)) ⊆
      Finset.univ.filter (fun f => ∃ i ∈ scope e, i ∈ scope f) := by
    intro f hf
    obtain ⟨i, hi, hif⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hf).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hif⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hx f)).trans
    (scope_touching_sum scope x b hx hOne (scope e))

theorem group_avoidance_rate_budget (d : ℕ) (hd : (10 ^ 100 : ℕ) ≤ d) :
    Real.log ((1 + Real.rpow (d : ℝ) (-0.1)) / (1 - Real.rpow (d : ℝ) (-0.1))) +
      Real.rpow (d : ℝ) (-2) ≤ Real.rpow (d : ℝ) (-0.05) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 100) hd
  let ρ := Real.rpow (d : ℝ) (-0.1)
  have hρ : 0 ≤ ρ ∧ ρ ≤ 1 / 3 :=
    ⟨(Real.rpow_pos_of_pos hp _).le, (calibration_power_bounds d hd).1⟩
  have hc : 0 < (1 + ρ) / (1 - ρ) := div_pos (by linarith) (by linarith)
  have hlog : Real.log ((1 + ρ) / (1 - ρ)) ≤ 4 * ρ := by
    have hh := Real.log_le_log hc (relative_factor_exp ρ hρ)
    simpa only [Real.log_exp] using hh
  have h1 := calibration_rpow_tenth d hd 0.05 (by norm_num)
  have h2 := calibration_rpow_tenth d hd 1.95 (by norm_num)
  have hh1 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le (-0.05))
  have hh2 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hp.le (-0.05))
  simp only [← Real.rpow_eq_pow] at hh1 hh2
  have hmul (a b : ℝ) : Real.rpow (d : ℝ) a * Real.rpow (d : ℝ) b =
      Real.rpow (d : ℝ) (a + b) := (Real.rpow_add hp a b).symm
  rw [hmul] at hh1 hh2
  norm_num only at hh1 hh2
  change Real.log ((1 + Real.rpow (d : ℝ) (-0.1)) / (1 - Real.rpow (d : ℝ) (-0.1))) ≤
    4 * Real.rpow (d : ℝ) (-0.1) at hlog
  norm_num only at hlog ⊢
  have hn : 0 ≤ Real.rpow (d : ℝ) (-(1 / 20 : ℝ)) := Real.rpow_nonneg hp.le _
  nlinarith only [hlog, hh1, hh2, hn]


/-- The additive bucket slack forces every certificate to have many groups. -/
theorem capacity_size_lower (d : ℕ) (a : ℝ) (hd : (10 ^ 100 : ℕ) ≤ d)
    (ha : (1 / 100 : ℝ) * Real.rpow (d : ℝ) 0.5 ≤ a) :
    Real.rpow (d : ℝ) 0.4 ≤ (⌊a⌋₊ : ℝ) := by
  have hb : (10 : ℝ) ^ (100 : ℕ) ≤ d := by exact_mod_cast hd
  have hp : (0 : ℝ) < d := lt_of_lt_of_le (by positivity) hb
  have hdecay : Real.rpow (d : ℝ) (-0.1) ≤ 1 / 1000 := by
    calc
      _ ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) (-0.1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (by norm_num)
      _ = Real.rpow 10 (100 * (-0.1)) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 (-0.1)).symm
      _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hsmall : Real.rpow (d : ℝ) 0.4 ≤ (1 / 1000 : ℝ) * Real.rpow (d : ℝ) 0.5 := by
    have hh := mul_le_mul_of_nonneg_right hdecay (Real.rpow_nonneg hp.le 0.5)
    simp only [← Real.rpow_eq_pow] at hh
    have heq : Real.rpow (d : ℝ) (-0.1) * Real.rpow (d : ℝ) 0.5 = Real.rpow (d : ℝ) 0.4 := by
      convert (Real.rpow_add hp (-0.1) 0.5).symm using 1 <;> norm_num
    rwa [heq] at hh
  have hbig : 1000 ≤ Real.rpow (d : ℝ) 0.5 := by
    calc
      _ ≤ Real.rpow ((10 : ℝ) ^ (100 : ℕ)) 0.5 := by
        have heq : Real.rpow ((10 : ℝ) ^ (100 : ℕ)) 0.5 = Real.rpow 10 (100 * 0.5) := by
          rw [← Real.rpow_natCast]
          exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) 100 0.5).symm
        rw [heq]
        norm_num [Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hb (by norm_num)
  have hfloor := Nat.sub_one_lt_floor a
  nlinarith only [ha, hsmall, hbig, hfloor]

theorem capacity_size_upper (d : ℕ) (a : ℝ) (hd : 2 ≤ d) (ha : 0 ≤ a)
    (hhalf : a ≤ (d : ℝ) / 2) : ⌊a⌋₊ + 1 ≤ d := by
  have hfloor := Nat.floor_le ha
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hh : (⌊a⌋₊ : ℝ) + 1 ≤ d := by linarith
  exact_mod_cast hh

theorem image_mass_le_slot_mass {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] (P : FinLaw Bin) (pool : Slot → Bin) :
    (∑ b ∈ Finset.univ.image pool, P.w b) ≤ ∑ s, P.w (pool s) := by
  classical
  have hsum : (∑ s, P.w (pool s)) = ∑ b, ∑ s, if pool s = b then P.w b else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp
  rw [hsum]
  calc
    _ ≤ ∑ b ∈ Finset.univ.image pool, ∑ s, if pool s = b then P.w b else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hb
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset Slot))
        (f := fun t => if pool t = b then P.w b else 0)
        (fun t _ => by split_ifs <;> first | exact P.nonneg b | exact le_rfl) (Finset.mem_univ s)
      simpa only [if_pos hs] using hh
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ =>
      Finset.sum_nonneg fun s _ => by split_ifs <;> first | exact P.nonneg b | exact le_rfl)

theorem image_mass_one_slot {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] (P : FinLaw Bin) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ b, P.w b ≤ c) (s : Slot) (x y : Slot → Bin)
    (hxy : ∀ t, t ≠ s → x t = y t) :
    |(∑ b ∈ Finset.univ.image x, P.w b) - ∑ b ∈ Finset.univ.image y, P.w b| ≤ c := by
  classical
  have hupper (a b : Slot → Bin) (hab : ∀ t, t ≠ s → a t = b t) :
      (∑ z ∈ Finset.univ.image a, P.w z) ≤ (∑ z ∈ Finset.univ.image b, P.w z) + c := by
    have hsub : Finset.univ.image a ⊆ insert (a s) (Finset.univ.image b) := by
      intro z hz
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
      by_cases hts : t = s
      · simp [hts]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, (hab t hts).symm⟩
    calc
      _ ≤ ∑ z ∈ insert (a s) (Finset.univ.image b), P.w z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => P.nonneg z)
      _ ≤ P.w (a s) + ∑ z ∈ Finset.univ.image b, P.w z := by
        by_cases hm : a s ∈ Finset.univ.image b
        · rw [Finset.insert_eq_of_mem hm]
          exact le_add_of_nonneg_left (P.nonneg _)
        · rw [Finset.sum_insert hm]
      _ ≤ _ := by linarith [hcap (a s)]
  rw [abs_le]
  constructor <;> linarith [hupper x y hxy, hupper y x (fun t ht => (hxy t ht).symm)]

/-- The image-mass bias is supported on repeated slot images, before or
after an iid pin. This isolates the birthday loss from the pin's mean shift. -/
theorem image_mass_mean_bias {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] [DecidableEq Bin] (P : FinLaw Bin) (Q : FinLaw (Slot → Bin))
    (c : ℝ) (hc : 0 ≤ c) (hcap : ∀ b, P.w b ≤ c) :
    0 ≤ Q.E (fun pool => ∑ s, P.w (pool s)) - Q.E (fun pool => ∑ b ∈ Finset.univ.image pool, P.w b) ∧
    Q.E (fun pool => ∑ s, P.w (pool s)) - Q.E (fun pool => ∑ b ∈ Finset.univ.image pool, P.w b) ≤
      (Fintype.card Slot : ℝ) * c * Q.pr (fun pool => ¬ Function.Injective pool) := by
  classical
  have hpoint (pool : Slot → Bin) :
      0 ≤ (∑ s, P.w (pool s)) - ∑ b ∈ Finset.univ.image pool, P.w b :=
    sub_nonneg.mpr (image_mass_le_slot_mass P pool)
  have hdom (pool : Slot → Bin) :
      (∑ s, P.w (pool s)) - ∑ b ∈ Finset.univ.image pool, P.w b ≤
        if ¬ Function.Injective pool then (Fintype.card Slot : ℝ) * c else 0 := by
    by_cases hi : Function.Injective pool
    · rw [if_neg (not_not.mpr hi), distinct_pool_mass P pool hi, sub_self]
    · rw [if_pos hi]
      have hu : (∑ s, P.w (pool s)) ≤ (Fintype.card Slot : ℝ) * c := by
        simpa using Finset.sum_le_sum (s := Finset.univ) (fun s _ => hcap (pool s))
      have hl : 0 ≤ ∑ b ∈ Finset.univ.image pool, P.w b := Finset.sum_nonneg fun b _ => P.nonneg b
      linarith
  have heq : Q.E (fun pool => ∑ s, P.w (pool s)) -
      Q.E (fun pool => ∑ b ∈ Finset.univ.image pool, P.w b) =
      ∑ pool, Q.w pool * ((∑ s, P.w (pool s)) - ∑ b ∈ Finset.univ.image pool, P.w b) := by
    unfold FinLaw.E
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun pool _ => mul_nonneg (Q.nonneg pool) (hpoint pool)), ?_⟩
  calc
    _ ≤ ∑ pool, Q.w pool * (if ¬ Function.Injective pool then (Fintype.card Slot : ℝ) * c else 0) :=
      Finset.sum_le_sum fun pool _ => mul_le_mul_of_nonneg_left (hdom pool) (Q.nonneg pool)
    _ = _ := by
      unfold FinLaw.pr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro pool _
      by_cases hi : Function.Injective pool <;> simp [hi] <;> ring

theorem iid_collision_probability {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] (Q : Slot → FinLaw Bin)
    (hQ : ∀ s b, (Q s).w b = 1 / (Fintype.card Bin : ℝ)) :
    (FinLaw.pi Q).pr (fun pool => ¬ Function.Injective pool) ≤
      (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin := by
  have hp : (fun pool : Slot → Bin => ¬ Function.Injective pool) =
      (fun pool => ∃ s ∈ (Finset.univ : Finset Slot), ∃ t ∈ Finset.univ, s ≠ t ∧ pool s = pool t) := by
    funext pool
    apply propext
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hex
      apply h
      intro s t heq
      by_contra hst
      exact hex ⟨s, t, hst, heq⟩
    · rintro ⟨s, t, hst, heq⟩ hi
      exact hst (hi heq)
  rw [hp]
  simpa only [Finset.card_univ, div_eq_mul_inv, one_mul] using
    pi_repeated_bins Q Finset.univ (1 / (Fintype.card Bin : ℝ)) (by positivity)
      (fun s _ b => (hQ s b).le)

theorem iid_pinned_collision_probability {Slot Bin : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Bin] (Q : Slot → FinLaw Bin)
    (hQ : ∀ s b, (Q s).w b = 1 / (Fintype.card Bin : ℝ)) (s : Slot) (b : Bin) :
    (FinLaw.pi (coordinatePin Q s b)).pr (fun pool => ¬ Function.Injective pool) ≤
      (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin := by
  have hp : (fun pool : Slot → Bin => ¬ Function.Injective pool) =
      (fun pool => ∃ s ∈ (Finset.univ : Finset Slot), ∃ t ∈ Finset.univ, s ≠ t ∧ pool s = pool t) := by
    funext pool
    apply propext
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hex
      apply h
      intro s t heq
      by_contra hst
      exact hex ⟨s, t, hst, heq⟩
    · rintro ⟨s, t, hst, heq⟩ hi
      exact hst (hi heq)
  rw [hp]
  simpa only [Finset.card_univ, div_eq_mul_inv, one_mul] using
    pi_repeated_bins_pinned Q Finset.univ s b (1 / (Fintype.card Bin : ℝ)) (by positivity)
      (fun s _ b => (hQ s b).le)

/-- Image normalizers concentrate with the same iid pin as the pool
experiment. The two explicit budgets separate bias from bounded differences. -/
theorem image_diagnostic_concentration {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [instB : DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0)
    (P : Check → FinLaw Bin) (c tol : ℝ) (hc : 0 < c) (htol : 0 < tol)
    (hn : 2 ≤ n) (hc0 : 0 < c0) (hslots : 0 < Fintype.card Slot)
    (heps : 0 < D.ε ∧ D.ε ≤ 1)
    (hcap : ∀ a b, (P a).w b ≤ c)
    (hnormal : ∀ pool a, D.normalizer pool a = ∑ b ∈ Finset.univ.image pool, (P a).w b)
    (hcenter : ∀ a, D.center a = (Fintype.card Slot : ℝ) / Fintype.card Bin)
    (htolerance : ∀ a, D.tolerance a = tol)
    (hbias : (Fintype.card Slot : ℝ) * c *
        ((Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin) + (c + 1 / (Fintype.card Bin : ℝ)) ≤ tol / 2)
    (hvariance : (n : ℝ) ^ c0 + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
        2 * (tol / 2) ^ 2 / ((Fintype.card Slot : ℝ) * c ^ 2))
    (hcollision : (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin ≤ Real.exp (-(n : ℝ) ^ c0) / 4) :
    Nonempty (PoolConcentrationHypotheses D) := by
  classical
  cases Subsingleton.elim instB (Classical.decEq Bin)
  let B : ℝ := Fintype.card Bin
  let L : ℝ := Fintype.card Slot
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hslots
  have herror : 0 ≤ c + 1 / B := by positivity
  have hplain (a : Check) :
      |D.poolLaw.E (D.normalizer · a) - D.center a| ≤ tol / 2 := by
    simp_rw [CellPoolDiagnostics.poolLaw, hnormal, hcenter]
    have hb := image_mass_mean_bias (P a) (FinLaw.pi D.iidSlotLaw) c hc.le (hcap a)
    rw [empirical_mass_mean (P a) D.iidSlotLaw D.uniform_slots] at hb
    have hprob := iid_collision_probability D.iidSlotLaw D.uniform_slots
    have hmul := mul_le_mul_of_nonneg_left hprob (mul_nonneg hL.le hc.le)
    have hbound : L / B - (FinLaw.pi D.iidSlotLaw).E
        (fun pool => ∑ b ∈ Finset.univ.image pool, (P a).w b) ≤ tol / 2 := by
      exact (hb.2.trans hmul).trans (by dsimp [L, B] at *; linarith only [hbias, herror])
    apply abs_le.mpr
    dsimp [L, B] at hbound
    constructor <;> linarith [hb.1]
  have hpinned (s : Slot) (b : Bin) (a : Check) :
      |(D.pinLaw s b).E (D.normalizer · a) - D.center a| ≤ tol / 2 := by
    simp_rw [CellPoolDiagnostics.pinLaw, hnormal, hcenter]
    let Q := coordinatePin D.iidSlotLaw s b
    have hb := image_mass_mean_bias (P a) (FinLaw.pi Q) c hc.le (hcap a)
    have hprob := iid_pinned_collision_probability D.iidSlotLaw D.uniform_slots s b
    have hmul := mul_le_mul_of_nonneg_left hprob (mul_nonneg hL.le hc.le)
    have hmean := empirical_mass_pinned_mean (P a) D.iidSlotLaw D.uniform_slots c hc.le (hcap a) s b
    have hshift : |(FinLaw.pi Q).E (fun pool => ∑ s, (P a).w (pool s)) - L / B| ≤ c + 1 / B :=
      by simpa only [Q, coordinatePin, FinLaw.E, FinLaw.pi, FinLaw.dirac, L, B] using hmean
    have hbound : |(FinLaw.pi Q).E (fun pool => ∑ b ∈ Finset.univ.image pool, (P a).w b) -
        (FinLaw.pi Q).E (fun pool => ∑ s, (P a).w (pool s))| ≤ L * c * (L ^ 2 / B) := by
      apply abs_le.mpr
      have hh := hb.2.trans hmul
      constructor <;> linarith [hb.1]
    simpa only [Q, coordinatePin, FinLaw.E, FinLaw.pi, FinLaw.dirac, L, B] using
      (abs_sub_le ((FinLaw.pi Q).E (fun pool => ∑ b ∈ Finset.univ.image pool, (P a).w b))
        ((FinLaw.pi Q).E (fun pool => ∑ s, (P a).w (pool s))) (L / B)).trans
        ((add_le_add hbound hshift).trans hbias)
  refine ⟨{
    n_large := hn
    exponent_pos := hc0
    slots_pos := hslots
    epsilon_pos := heps
    tolerance_pos := fun a => by rw [htolerance]; exact htol
    sensitivity := fun _ _ => c
    sensitivity_nonneg := fun _ _ => hc.le
    mean_close := fun a => by rw [htolerance]; exact hplain a
    pinned_mean_close := fun s b a => by rw [htolerance]; exact hpinned s b a
    one_slot_change := ?_
    variance_budget := ?_
    collision_budget := hcollision }⟩
  · intro a s x y hxy
    rw [hnormal, hnormal]
    exact image_mass_one_slot (P a) c hc.le (hcap a) s x y hxy
  · intro a
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, htolerance]
    exact Or.inr ⟨mul_pos hL (sq_pos_of_pos hc), hvariance⟩

theorem direct_image_budget_room : ∃ n₀ : ℕ, ∀ (n : ℕ) (L B : ℝ),
    n₀ ≤ n → 2 ≤ n → 0 < B → (n : ℝ) ^ (200 : ℕ) ≤ L →
    L ^ 2 / B ≤ Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 →
    (2 * L ^ 2 / B + 3 / L ≤ Real.rpow (n : ℝ) (-4) / 2) ∧
    (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * ((2 ^ n + 1 : ℕ) : ℝ)) ≤
      L * Real.rpow (n : ℝ) (-4) ^ 2 / 8) := by
  obtain ⟨n₀, hroom⟩ := logarithmic_room (1 / 2) 1 (Real.log 2) 4 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n L B hn hn2 hB hL hcollision
  let x : ℝ := n
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hρ : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div] <;> exact hx.le
  have hsmall : Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ Real.rpow x (-4) / 2 := by
    have hr := hroom n hn
    simp only [one_mul] at hr
    have he := Real.exp_le_exp.mpr (show -Real.rpow x (1 / 2 : ℝ) ≤ -(Real.log 2 + 4 * Real.log x) by exact neg_le_neg hr)
    have he4 : Real.exp (4 * Real.log x) = x ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 4
    rw [Real.exp_neg (Real.log 2 + 4 * Real.log x), Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), he4] at he
    rw [hρ]
    convert he using 1 <;> ring
  have h196 : (12 : ℝ) ≤ x ^ (196 : ℕ) := by
    calc
      12 ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ x ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (196 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have h191 : (32 : ℝ) ≤ x ^ (191 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ x ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (191 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hload : 12 * x ^ (4 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (196 : ℕ) * x ^ (4 : ℕ) := mul_le_mul_of_nonneg_right h196 (pow_nonneg hx.le _)
      _ = x ^ (200 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  have hvar : 32 * x ^ (9 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (191 : ℕ) * x ^ (9 : ℕ) := mul_le_mul_of_nonneg_right h191 (pow_nonneg hx.le _)
      _ = x ^ (200 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  refine ⟨?_, ?_⟩
  · have hpin : 3 / L ≤ Real.rpow x (-4) / 4 := by
      calc
        _ ≤ 3 / (12 * x ^ (4 : ℕ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hload
        _ = _ := by rw [hρ]; ring
    have hcoll := mul_le_mul_of_nonneg_left hcollision (by norm_num : (0 : ℝ) ≤ 2)
    have hs := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 1 / 2)
    dsimp [x] at *
    rw [mul_div_assoc]
    nlinarith only [hpin, hcoll, hs]
  · have hlog2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hlog16 : Real.log 16 ≤ 4 := by
      have heq : Real.log 16 = 4 * Real.log 2 := by
        convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
      rw [heq]
      linarith
    have hlog : Real.log (8 * ((2 ^ n + 1 : ℕ) : ℝ)) ≤ 4 + x := by
      have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hh : 8 * ((2 ^ n + 1 : ℕ) : ℝ) ≤ 16 * (2 : ℝ) ^ n := by
        push_cast
        nlinarith only [hp1]
      calc
        _ ≤ Real.log (16 * (2 : ℝ) ^ n) := Real.log_le_log (by positivity) hh
        _ = Real.log 16 + (n : ℝ) * Real.log 2 := by
          rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ n ≠ 0), Real.log_pow]
        _ ≤ 4 + x := by nlinarith [mul_le_mul_of_nonneg_left hlog2 hx.le]
    have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hpoly : 4 * x ≤ L * Real.rpow x (-4) ^ 2 / 8 := by
      calc
        _ = (32 * x ^ (9 : ℕ)) * Real.rpow x (-4) ^ 2 / 8 := by rw [hρ]; field_simp; ring
        _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hvar (sq_nonneg _)) (by norm_num)
    exact (show Real.rpow x (1 / 2 : ℝ) + Real.log (8 * ((2 ^ n + 1 : ℕ) : ℝ)) ≤ 4 * x by linarith).trans hpoly

theorem pi_injective_coordinate_E {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Fintype Bin]
    (Q : Slot → FinLaw Bin) (indices : Index → Slot) (hi : Function.Injective indices)
    (F : (Index → Bin) → ℝ) :
    (FinLaw.pi Q).E (fun pool => F (fun i => pool (indices i))) =
      (FinLaw.pi (fun i => Q (indices i))).E F := by
  classical
  let S := Finset.univ.image indices
  let e : Index ≃ {s : Slot // s ∈ S} := Equiv.ofBijective
    (fun i => ⟨indices i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j hh => hi (congrArg Subtype.val hh), by
      intro s
      obtain ⟨i, _, heq⟩ := Finset.mem_image.mp s.2
      exact ⟨i, Subtype.ext heq⟩⟩
  have heval : ∀ i, (e i).1 = indices i := fun _ => rfl
  let ef : ({s : Slot // s ∈ S} → Bin) ≃ (Index → Bin) := {
    toFun := fun z i => z (e i)
    invFun := fun z s => z (e.symm s)
    left_inv := fun z => funext fun s => by simp
    right_inv := fun z => funext fun i => by simp }
  have hef (z : {s : Slot // s ∈ S} → Bin) : ef z = (fun i => z (e i)) := rfl
  let P : Slot → FinProb Bin := fun s => finLawToFramework (Q s)
  have hm := FinProb.pi_marginal_expect P S (fun z => F (fun i => z (e i)))
  have hm' : (FinLaw.pi Q).E (fun pool => F (fun i => pool (indices i))) =
      (FinLaw.pi (fun s : {s : Slot // s ∈ S} => Q s.1)).E (fun z => F (ef z)) := by
    simpa only [P, FinProb.expect, FinProb.pi, finLawToFramework, FinLaw.E, FinLaw.pi, heval, hef] using hm
  rw [hm']
  have hweights (z : Index → Bin) :
      (FinLaw.pi (fun s : {s : Slot // s ∈ S} => Q s.1)).w (ef.symm z) =
        (FinLaw.pi (fun i => Q (indices i))).w z := by
    change (∏ s : {s : Slot // s ∈ S}, (Q s.1).w (z (e.symm s))) =
      ∏ i, (Q (indices i)).w (z i)
    simpa only [Equiv.symm_apply_apply, heval] using
      (e.prod_comp (fun s : {s : Slot // s ∈ S} => (Q s.1).w (z (e.symm s)))).symm
  calc
    _ = ∑ z : Index → Bin,
        (FinLaw.pi (fun s : {s : Slot // s ∈ S} => Q s.1)).w (ef.symm z) * F z := by
      have hh := (ef.symm.sum_comp (fun z =>
        (FinLaw.pi (fun s : {s : Slot // s ∈ S} => Q s.1)).w z * F (ef z))).symm
      simpa only [Equiv.apply_symm_apply, FinLaw.E] using hh
    _ = _ := by simp only [hweights, FinLaw.E]

/-- Slot expansion of an unnormalized empirical star polynomial. The
kernel can already include the factors `B*qbar` and a fixed group-bin pin. -/
noncomputable def empirical_statistic {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    (F : (Index → Bin) → ℝ) (pool : Slot → Bin) : ℝ :=
  (FinLaw.pi (fun _ : Index => FinLaw.uniform (Finset.univ : Finset Slot) Finset.univ_nonempty)).E
    (fun indices => F (fun i => pool (indices i)))

theorem empirical_statistic_range {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    (F : (Index → Bin) → ℝ) (M : ℝ) (hF : ∀ a, 0 ≤ F a ∧ F a ≤ M) (pool : Slot → Bin) :
    0 ≤ empirical_statistic F pool ∧ empirical_statistic F pool ≤ M := by
  let J := FinLaw.pi (fun _ : Index => FinLaw.uniform (Finset.univ : Finset Slot) Finset.univ_nonempty)
  refine ⟨Finset.sum_nonneg (fun indices _ => mul_nonneg (J.nonneg indices) (hF _).1), ?_⟩
  calc
    _ ≤ ∑ indices, J.w indices * M := Finset.sum_le_sum fun indices _ =>
      mul_le_mul_of_nonneg_left (hF _).2 (J.nonneg indices)
    _ = M := by rw [← Finset.sum_mul, J.sum_one, one_mul]

theorem empirical_statistic_one_slot {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    (F : (Index → Bin) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hF : ∀ a, 0 ≤ F a ∧ F a ≤ M)
    (s : Slot) (x y : Slot → Bin) (hxy : ∀ t, t ≠ s → x t = y t) :
    |empirical_statistic F x - empirical_statistic F y| ≤
      (Fintype.card Index : ℝ) * M / Fintype.card Slot := by
  classical
  let laws : Index → FinLaw Slot := fun _ => FinLaw.uniform Finset.univ Finset.univ_nonempty
  let J := FinLaw.pi laws
  have hprob : J.pr (fun indices => ∃ i : Index, indices i = s) ≤
      (Fintype.card Index : ℝ) / Fintype.card Slot := by
    have hh := finLaw_union_bound J (Finset.univ : Finset Index) (fun i indices => indices i = s)
    have hcoord : ∀ i, J.pr (fun indices => indices i = s) = 1 / (Fintype.card Slot : ℝ) := by
      intro i
      rw [show J = FinLaw.pi laws from rfl, pi_coordinate_pr]
      simp [laws, FinLaw.uniform]
    simpa only [Finset.mem_univ, true_and, hcoord, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, div_eq_mul_inv, one_mul] using hh
  have hdom (indices : Index → Slot) :
      |F (fun i => x (indices i)) - F (fun i => y (indices i))| ≤
        if ∃ i : Index, indices i = s then M else 0 := by
    by_cases hhit : ∃ i : Index, indices i = s
    · rw [if_pos hhit]
      exact abs_le.mpr ⟨by linarith [(hF (fun i => x (indices i))).1, (hF (fun i => y (indices i))).2],
        by linarith [(hF (fun i => y (indices i))).1, (hF (fun i => x (indices i))).2]⟩
    · rw [if_neg hhit]
      have heq : (fun i => x (indices i)) = (fun i => y (indices i)) :=
        funext fun i => hxy (indices i) (fun hi => hhit ⟨i, hi⟩)
      rw [heq, sub_self, abs_zero]
  have heq : empirical_statistic F x - empirical_statistic F y =
      ∑ indices, J.w indices * (F (fun i => x (indices i)) - F (fun i => y (indices i))) := by
    unfold empirical_statistic FinLaw.E
    simp only [J, laws, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ indices, |J.w indices * (F (fun i => x (indices i)) - F (fun i => y (indices i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ indices, J.w indices * |F (fun i => x (indices i)) - F (fun i => y (indices i))| := by
      apply Finset.sum_congr rfl
      intro indices _
      rw [abs_mul, abs_of_nonneg (J.nonneg indices)]
    _ ≤ ∑ indices, J.w indices * (if ∃ i : Index, indices i = s then M else 0) :=
      Finset.sum_le_sum fun indices _ => mul_le_mul_of_nonneg_left (hdom indices) (J.nonneg indices)
    _ = M * J.pr (fun indices => ∃ i : Index, indices i = s) := by
      unfold FinLaw.pr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro indices _
      by_cases hh : ∃ i : Index, indices i = s <;> simp [hh, mul_comm]
    _ ≤ M * ((Fintype.card Index : ℝ) / Fintype.card Slot) := mul_le_mul_of_nonneg_left hprob hM
    _ = _ := by ring

theorem empirical_statistic_mean_exchange {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Bin] (F : (Index → Bin) → ℝ) (P : FinLaw (Slot → Bin)) :
    P.E (empirical_statistic F) =
      (FinLaw.pi (fun _ : Index => FinLaw.uniform (Finset.univ : Finset Slot) Finset.univ_nonempty)).E
        (fun indices => P.E (fun pool => F (fun i => pool (indices i)))) := by
  unfold empirical_statistic FinLaw.E
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro indices _
  apply Finset.sum_congr rfl
  intro pool _
  ring

private theorem finite_expect_range {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (F : Ω → ℝ) (M : ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) :
    0 ≤ P.E F ∧ P.E F ≤ M := by
  refine ⟨Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hF x).1), ?_⟩
  calc
    _ ≤ ∑ x, P.w x * M := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hF x).2 (P.nonneg x)
    _ = M := by rw [← Finset.sum_mul, P.sum_one, one_mul]

/-- Distinct empirical indices reproduce the independent bin integral.
Repeated indices cost at most the ordered-pair birthday estimate. -/
theorem empirical_statistic_mean {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Bin] (F : (Index → Bin) → ℝ) (Q : FinLaw Bin) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ a, 0 ≤ F a ∧ F a ≤ M) :
    (FinLaw.pi (fun _ : Slot => Q)).E (empirical_statistic F) ≤
      (FinLaw.pi (fun _ : Index => Q)).E F +
        M * ((Fintype.card Index : ℝ) ^ 2 / Fintype.card Slot) := by
  classical
  let laws : Index → FinLaw Slot := fun _ => FinLaw.uniform Finset.univ Finset.univ_nonempty
  let J := FinLaw.pi laws
  let μ := (FinLaw.pi (fun _ : Index => Q)).E F
  have hμ : 0 ≤ μ := (finite_expect_range _ F M hF).1
  have hpoint (indices : Index → Slot) :
      (FinLaw.pi (fun _ : Slot => Q)).E (fun pool => F (fun i => pool (indices i))) ≤
        μ + (if ¬ Function.Injective indices then M else 0) := by
    by_cases hi : Function.Injective indices
    · rw [if_neg (not_not.mpr hi), add_zero, pi_injective_coordinate_E _ indices hi]
    · rw [if_pos hi]
      exact ((finite_expect_range _ _ M (fun pool => hF _)).2).trans (le_add_of_nonneg_left hμ)
  have hcollision : J.pr (fun indices => ¬ Function.Injective indices) ≤
      (Fintype.card Index : ℝ) ^ 2 / Fintype.card Slot :=
    iid_collision_probability laws (fun _ _ => by simp [laws, FinLaw.uniform])
  rw [empirical_statistic_mean_exchange F]
  calc
    _ ≤ ∑ indices, J.w indices * (μ + (if ¬ Function.Injective indices then M else 0)) :=
      Finset.sum_le_sum fun indices _ => mul_le_mul_of_nonneg_left (hpoint indices) (J.nonneg indices)
    _ = μ + M * J.pr (fun indices => ¬ Function.Injective indices) := by
      unfold FinLaw.pr
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, J.sum_one, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro indices _
      by_cases hi : Function.Injective indices <;> simp [hi, mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hcollision hM)

theorem finite_pr_or {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A B : Ω → Prop) :
    P.pr (fun x => A x ∨ B x) ≤ P.pr A + P.pr B := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, P.nonneg x]

/-- A fixed pool slot creates an additional exceptional index set. Outside
it and the birthday set, the original independent integral is unchanged. -/
theorem empirical_statistic_pinned_mean {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Bin] (F : (Index → Bin) → ℝ) (Q : FinLaw Bin) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ a, 0 ≤ F a ∧ F a ≤ M) (s : Slot) (b : Bin) :
    (FinLaw.pi (coordinatePin (fun _ : Slot => Q) s b)).E (empirical_statistic F) ≤
      (FinLaw.pi (fun _ : Index => Q)).E F +
        M * (((Fintype.card Index : ℝ) ^ 2 + Fintype.card Index) / Fintype.card Slot) := by
  classical
  let laws : Index → FinLaw Slot := fun _ => FinLaw.uniform Finset.univ Finset.univ_nonempty
  let J := FinLaw.pi laws
  let μ := (FinLaw.pi (fun _ : Index => Q)).E F
  let bad : (Index → Slot) → Prop := fun indices =>
    ¬ Function.Injective indices ∨ ∃ i : Index, indices i = s
  have hμ : 0 ≤ μ := (finite_expect_range _ F M hF).1
  have hgood (indices : Index → Slot) (hi : Function.Injective indices)
      (hmiss : ∀ i, indices i ≠ s) :
      (FinLaw.pi (coordinatePin (fun _ : Slot => Q) s b)).E (fun pool => F (fun i => pool (indices i))) = μ := by
    rw [pi_injective_coordinate_E _ indices hi]
    have heq : (fun i => coordinatePin (fun _ : Slot => Q) s b (indices i)) = (fun _ : Index => Q) := by
      funext i
      simp only [coordinatePin, if_neg (hmiss i)]
    rw [heq]
  have hpoint (indices : Index → Slot) :
      (FinLaw.pi (coordinatePin (fun _ : Slot => Q) s b)).E (fun pool => F (fun i => pool (indices i))) ≤
        μ + (if bad indices then M else 0) := by
    by_cases hb : bad indices
    · rw [if_pos hb]
      exact ((finite_expect_range _ _ M (fun pool => hF _)).2).trans (le_add_of_nonneg_left hμ)
    · rw [if_neg hb, add_zero]
      have hi : Function.Injective indices := by
        by_contra hi
        exact hb (Or.inl hi)
      have hmiss : ∀ i, indices i ≠ s := fun i hh => hb (Or.inr ⟨i, hh⟩)
      rw [hgood indices hi hmiss]
  have hcollision : J.pr (fun indices => ¬ Function.Injective indices) ≤
      (Fintype.card Index : ℝ) ^ 2 / Fintype.card Slot :=
    iid_collision_probability laws (fun _ _ => by simp [laws, FinLaw.uniform])
  have hhit : J.pr (fun indices => ∃ i : Index, indices i = s) ≤
      (Fintype.card Index : ℝ) / Fintype.card Slot := by
    have hh := finLaw_union_bound J (Finset.univ : Finset Index) (fun i indices => indices i = s)
    have hcoord : ∀ i, J.pr (fun indices => indices i = s) = 1 / (Fintype.card Slot : ℝ) := by
      intro i
      rw [show J = FinLaw.pi laws from rfl, pi_coordinate_pr]
      simp [laws, FinLaw.uniform]
    simpa only [Finset.mem_univ, true_and, hcoord, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, div_eq_mul_inv, one_mul] using hh
  have hprob : J.pr bad ≤ ((Fintype.card Index : ℝ) ^ 2 + Fintype.card Index) / Fintype.card Slot := by
    have hh := (finite_pr_or J (fun indices => ¬ Function.Injective indices)
      (fun indices => ∃ i : Index, indices i = s)).trans (add_le_add hcollision hhit)
    simpa only [bad, add_div] using hh
  rw [empirical_statistic_mean_exchange F]
  calc
    _ ≤ ∑ indices, J.w indices * (μ + (if bad indices then M else 0)) :=
      Finset.sum_le_sum fun indices _ => mul_le_mul_of_nonneg_left (hpoint indices) (J.nonneg indices)
    _ = μ + M * J.pr bad := by
      unfold FinLaw.pr
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, J.sum_one, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro indices _
      by_cases hb : bad indices <;> simp [hb, mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hprob hM)

noncomputable def empirical_weighted_kernel {Index Bin : Type*} [Fintype Index] [Fintype Bin]
    (P : Index → FinLaw Bin) (B : ℝ) (F : (Index → Bin) → ℝ) (a : Index → Bin) : ℝ :=
  F a * ∏ i, B * (P i).w (a i)

theorem empirical_weighted_kernel_range {Index Bin : Type*} [Fintype Index] [Fintype Bin]
    (P : Index → FinLaw Bin) (B A : ℝ) (hB : 0 < B) (hA : 0 ≤ A)
    (hcap : ∀ i b, (P i).w b ≤ A / B) (F : (Index → Bin) → ℝ)
    (hF : ∀ a, 0 ≤ F a ∧ F a ≤ 1) :
    ∀ a, 0 ≤ empirical_weighted_kernel P B F a ∧
      empirical_weighted_kernel P B F a ≤ A ^ Fintype.card Index := by
  intro a
  have hprod0 : 0 ≤ ∏ i, B * (P i).w (a i) :=
    Finset.prod_nonneg fun i _ => mul_nonneg hB.le ((P i).nonneg _)
  refine ⟨mul_nonneg (hF a).1 hprod0, ?_⟩
  calc
    _ ≤ ∏ i, B * (P i).w (a i) := mul_le_of_le_one_left hprod0 (hF a).2
    _ ≤ ∏ _i : Index, A := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg hB.le ((P i).nonneg _)
      · intro i _
        have hh := (le_div_iff₀ hB).mp (hcap i (a i))
        simpa only [mul_comm] using hh
    _ = _ := by simp

/-- Uniform-slot expectation cancels the `B*qbar` factors exactly. -/
theorem empirical_weighted_kernel_integral {Index Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (P : Index → FinLaw Bin) (F : (Index → Bin) → ℝ) :
    (FinLaw.pi (fun _ : Index => FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
      (empirical_weighted_kernel P (Fintype.card Bin) F) = (FinLaw.pi P).E F := by
  classical
  have hB : (Fintype.card Bin : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply Finset.sum_congr rfl
  intro a _
  have hprod : (∏ i : Index, (FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty).w (a i)) *
      (∏ i : Index, (Fintype.card Bin : ℝ) * (P i).w (a i)) = ∏ i : Index, (P i).w (a i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [FinLaw.uniform, Finset.mem_univ, if_true, Finset.card_univ]
    field_simp [hB]
  change (∏ i : Index, (FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty).w (a i)) *
    (F a * ∏ i : Index, (Fintype.card Bin : ℝ) * (P i).w (a i)) = (∏ i : Index, (P i).w (a i)) * F a
  rw [mul_left_comm, hprod, mul_comm]

private theorem finLaw_eq_of_weights {Ω : Type*} [Fintype Ω] (P Q : FinLaw Ω)
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P
  cases Q
  congr 1
  exact funext h

/-- Deterministic histories need no further history conditioning. A finite
refinement of the constant summands supplies the analytic range budget. -/
theorem deterministic_history_load_gate {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] [Subsingleton Hist] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (hn : 2 ≤ n)
    (hc0 : 0 < c0) (ht : 0 < D.loadThreshold) (R : ℝ) (hR : 0 ≤ R)
    (hrange : ∀ pool h y, 0 ≤ D.loadValue pool h y ∧ D.loadValue pool h y ≤ R)
    (hsmall : ∀ pool, D.typical pool → ∀ h y,
      D.loadValue pool h y ≤ D.loadThreshold / 2) :
    Nonempty (LoadGateHypotheses D) := by
  classical
  have hHist : Nonempty Hist := by
    by_contra h
    have hzero : Fintype.card Hist = 0 := Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp h)
    have hempty : Finset.univ = (∅ : Finset Hist) :=
      Finset.card_eq_zero.mp (by simpa using hzero)
    have hsum := (D.historyLaw (fun _ => Classical.choice D.bins_nonempty)).sum_one
    rw [hempty, Finset.sum_empty] at hsum
    norm_num at hsum
  let h0 : Hist := Classical.choice hHist
  let A : ℝ := (n : ℝ) ^ c0 + Real.log (max 1 (Fintype.card D.LoadColumn : ℝ))
  have hA : 0 < A := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn
    exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hnp _)
      (Real.log_nonneg (le_max_left _ _))
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * R ^ 2 * A / D.loadThreshold ^ 2)
  let M := m + 1
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.succ_pos m)
  have hroom : 2 * R ^ 2 * A < (M : ℝ) * D.loadThreshold ^ 2 := by
    have hh : 2 * R ^ 2 * A / D.loadThreshold ^ 2 < (M : ℝ) :=
      hm.trans (by dsimp [M]; norm_num)
    exact (div_lt_iff₀ (sq_pos_of_pos ht)).mp hh
  have hbudget : A * (R ^ 2 / (M : ℝ)) ≤ 2 * (D.loadThreshold / 2) ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hM).mpr
    nlinarith only [hroom]
  have hsum : (∑ _s : Fin M, (R / (M : ℝ)) ^ 2) = R ^ 2 / (M : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨{
    n_large := hn
    exponent_pos := hc0
    Slice := Fin M
    Value := fun _ => Unit
    sliceLaw := fun _ _ => FinLaw.dirac ()
    encode := fun _ => h0
    history_eq := ?_
    contribution := fun pool _ _ y => D.loadValue pool h0 y / (M : ℝ)
    range := fun _ => R / (M : ℝ)
    range_nonneg := fun _ => div_nonneg hR hM.le
    contribution_range := ?_
    load_eq := ?_
    threshold_pos := ht
    mean_small := ?_
    variance_budget := ?_ }⟩
  · intro pool
    apply finLaw_eq_of_weights
    intro h
    have heq : h = h0 := Subsingleton.elim _ _
    have huniv : (Finset.univ : Finset Hist) = {h0} := by
      ext x
      simp [Subsingleton.elim x h0]
    have hweight := (D.historyLaw pool).sum_one
    rw [huniv, Finset.sum_singleton] at hweight
    rw [heq, hweight]
    simp only [FinLaw.map, if_true, FinLaw.sum_one]
  · intro pool s z y
    exact ⟨div_nonneg (hrange pool h0 y).1 hM.le,
      div_le_div_of_nonneg_right (hrange pool h0 y).2 hM.le⟩
  · intro pool z y
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro pool hp y
    calc
      _ ≤ (D.historyLaw pool).E (fun _ => D.loadThreshold / 2) := by
        apply Finset.sum_le_sum
        intro h _
        exact mul_le_mul_of_nonneg_left (hsmall pool hp h y) ((D.historyLaw pool).nonneg h)
      _ = _ := by
        unfold FinLaw.E
        rw [← Finset.sum_mul, FinLaw.sum_one, one_mul]
  · rw [hsum]
    by_cases hz : R ^ 2 / (M : ℝ) = 0
    · exact Or.inl hz
    · refine Or.inr ⟨lt_of_le_of_ne (div_nonneg (sq_nonneg R) hM.le) (Ne.symm hz), ?_⟩
      exact (le_div_iff₀ (lt_of_le_of_ne (div_nonneg (sq_nonneg R) hM.le) (Ne.symm hz))).mpr hbudget

private theorem finLaw_E_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (r : ℝ) :
    P.E (fun _ => r) = r := by
  unfold FinLaw.E
  rw [← Finset.sum_mul, P.sum_one, one_mul]

private theorem finLaw_E_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (f : I → Ω → ℝ) :
    P.E (fun z => ∑ i, f i z) = ∑ i, P.E (f i) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem finLaw_E_sub {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f g : Ω → ℝ) : P.E (fun z => f z - g z) = P.E f - P.E g := by
  unfold FinLaw.E
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem finLaw_E_map {Ω Hist : Type*} [Fintype Ω] [Fintype Hist]
    [DecidableEq Hist] (P : FinLaw Ω) (encode : Ω → Hist) (f : Hist → ℝ) :
    (FinLaw.map P encode).E f = P.E (fun z => f (encode z)) := by
  classical
  unfold FinLaw.E
  change (∑ h, (∑ z, if encode z = h then P.w z else 0) * f h) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp

/-- Independence bounds the load variance at every pool when the slice
ranges are required at every pool. This does not use typicality. -/
theorem independent_sum_variance {I : Type*} [Fintype I] [DecidableEq I]
    {Value : I → Type*} [∀ i, Fintype (Value i)]
    (law : ∀ i, FinLaw (Value i)) (f : ∀ i, Value i → ℝ) (R : I → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hf : ∀ i z, 0 ≤ f i z ∧ f i z ≤ R i) :
    let P := FinLaw.pi law
    let F := fun z => ∑ i, f i (z i)
    P.E (fun z => (F z - P.E F) ^ 2) ≤ ∑ i, R i ^ 2 := by
  classical
  dsimp only
  let P := FinLaw.pi law
  let m := fun i => P.E (fun z => f i (z i))
  let g := fun i (z : ∀ i, Value i) => f i (z i) - m i
  have hm : ∀ i, 0 ≤ m i ∧ m i ≤ R i := by
    intro i
    constructor
    · exact Finset.sum_nonneg fun z _ => mul_nonneg (P.nonneg z) (hf i (z i)).1
    · calc
        m i ≤ P.E (fun _ => R i) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hf i (z i)).2 (P.nonneg z)
        _ = R i := finLaw_E_const P _
  have hg : ∀ i, P.E (g i) = 0 := by
    intro i
    change P.E (fun z => f i (z i) - m i) = 0
    rw [finLaw_E_sub, finLaw_E_const]
    exact sub_self _
  let Q : ∀ i, FinProb (Value i) := fun i => ⟨(law i).w, (law i).nonneg, (law i).sum_one⟩
  have hcross : ∀ i j, i ≠ j → P.E (fun z => g i z * g j z) = 0 := by
    intro i j hij
    have h := FinProb.pi_expect_mul_of_disjoint Q (g i) (g j) {i} {j}
      (by intro z z' heq; simp only [g, heq i (by simp)])
      (by intro z z' heq; simp only [g, heq j (by simp)])
      (by simp [hij])
    change P.E (fun z => g i z * g j z) = P.E (g i) * P.E (g j) at h
    rw [h, hg, hg, zero_mul]
  have hcenter : ∀ z,
      (∑ i, f i (z i)) - P.E (fun z => ∑ i, f i (z i)) = ∑ i, g i z := by
    intro z
    rw [finLaw_E_sum, ← Finset.sum_sub_distrib]
  have hexpand : ∀ z, (∑ i, g i z) ^ 2 = ∑ i, ∑ j, g i z * g j z := by
    intro z
    rw [pow_two, Finset.sum_mul_sum]
  calc
    P.E (fun z => ((∑ i, f i (z i)) - P.E (fun z => ∑ i, f i (z i))) ^ 2) =
        P.E (fun z => ∑ i, ∑ j, g i z * g j z) := by
      simp_rw [hcenter, hexpand]
    _ = ∑ i, ∑ j, P.E (fun z => g i z * g j z) := by
      rw [finLaw_E_sum]
      simp_rw [finLaw_E_sum]
    _ = ∑ i, P.E (fun z => (g i z) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j _ hji
        exact hcross i j hji.symm
      · simp
    _ ≤ ∑ i, R i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ P.E (fun _ => R i ^ 2) := by
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left _ (P.nonneg z)
          have ha : 0 ≤ R i - (f i (z i) - m i) := by linarith [(hf i (z i)).2, (hm i).1]
          have hb : 0 ≤ R i + (f i (z i) - m i) := by linarith [(hf i (z i)).1, (hm i).2]
          dsimp only [g]
          nlinarith only [mul_nonneg ha hb]
        _ = _ := finLaw_E_const P _

/-- A necessary consequence of the frozen gate contract, including on
noninjective and otherwise atypical pools. -/
theorem load_gate_global_variance_bound {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (H : LoadGateHypotheses D)
    (pool : Slot → Bin) (y : D.LoadColumn) :
    ((n : ℝ) ^ c0 + Real.log (max 1 (Fintype.card D.LoadColumn : ℝ))) *
      (D.historyLaw pool).E (fun h => (D.loadValue pool h y -
        (D.historyLaw pool).E (fun h => D.loadValue pool h y)) ^ 2) ≤
      2 * (D.loadThreshold / 2) ^ 2 := by
  classical
  letI : Fintype H.Slice := H.sliceFin
  letI : DecidableEq H.Slice := H.sliceDec
  letI : ∀ s, Fintype (H.Value s) := H.valueFin
  let P := FinLaw.pi (H.sliceLaw pool)
  let F := fun z : ∀ s, H.Value s => ∑ s, H.contribution pool s (z s) y
  have hMean : (D.historyLaw pool).E (fun h => D.loadValue pool h y) = P.E F := by
    rw [H.history_eq pool, finLaw_E_map]
    simp_rw [H.load_eq pool]
    rfl
  have hVar : (D.historyLaw pool).E (fun h => (D.loadValue pool h y -
      (D.historyLaw pool).E (fun h => D.loadValue pool h y)) ^ 2) ≤ ∑ s, H.range s ^ 2 := by
    rw [H.history_eq pool, finLaw_E_map]
    simp_rw [H.load_eq pool]
    rw [← H.history_eq pool, hMean]
    exact independent_sum_variance (H.sliceLaw pool) (fun s z => H.contribution pool s z y)
      H.range H.range_nonneg (fun s z => H.contribution_range pool s z y)
  let A := (n : ℝ) ^ c0 + Real.log (max 1 (Fintype.card D.LoadColumn : ℝ))
  have hA : 0 ≤ A := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.log_nonneg (le_max_left _ _))
  have hbudget : A * (∑ s, H.range s ^ 2) ≤ 2 * (D.loadThreshold / 2) ^ 2 := by
    rcases H.variance_budget with hz | ⟨hp, hb⟩
    · rw [hz, mul_zero]
      positivity
    · exact (le_div_iff₀ hp).mp hb
  exact (mul_le_mul_of_nonneg_left hVar hA).trans hbudget

/-- The physical star-kernel amplitude and epsilon have polynomial room
uniformly over every low-cluster slice. -/
theorem cluster_slice_amplitude_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ (n h : ℕ), n₀ ≤ n → 2 ≤ n →
      (h : ℝ) ≤ Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ) →
      (16 * Real.exp (2 * (sliceK κ h : ℝ) * sliceT κ h)) ^ h ≤ (n : ℝ) ∧
      Real.rpow (n : ℝ) (-1) ≤ sliceEps κ h := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  let C := max (Real.log 16 + 2) (0.001 * κ.a)
  have hC : 0 < C := lt_of_lt_of_le (by positivity : (0 : ℝ) < 0.001 * κ.a) (le_max_right _ _)
  let n₀ := ⌈Real.exp (1 + C ^ 2)⌉₊
  refine ⟨n₀, ?_⟩
  intro n h hn hn2 hh
  have hnp : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hn2
  have hx : 1 + C ^ 2 ≤ Real.log (n : ℝ) := by
    have he : Real.exp (1 + C ^ 2) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hx1 : 1 ≤ Real.log (n : ℝ) := by nlinarith only [hx, sq_nonneg C]
  have hx0 : 0 ≤ Real.log (n : ℝ) := hx1.trans' (by norm_num)
  have hroot : C ≤ Real.sqrt (Real.log (n : ℝ)) := by
    apply (Real.le_sqrt hC.le hx0).mpr
    nlinarith only [hx]
  have hroom : C * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    calc
      _ ≤ Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hx0
  by_cases hz : h = 0
  · subst h
    constructor
    · simpa using hn1
    · have he : sliceEps κ 0 = 1 := by simp [sliceEps]
      rw [he]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  · have hh1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hz
    have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    have hkt : (sliceK κ h : ℝ) * sliceT κ h ≤ (h : ℝ) ^ (4 : ℕ) :=
      slice_product_bound hκ h hh1
    have hkt0 : 0 ≤ (sliceK κ h : ℝ) * sliceT κ h := by positivity
    have hhkt : (h : ℝ) * ((sliceK κ h : ℝ) * sliceT κ h) ≤ (h : ℝ) ^ (5 : ℕ) := by
      have hp := mul_le_mul_of_nonneg_left hkt (Nat.cast_nonneg h)
      nlinarith only [hp]
    have h5 : (h : ℝ) ^ (5 : ℕ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
      calc
        _ ≤ (Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)) ^ (5 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg h) hh _
        _ = Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
          norm_num
        _ = _ := (Real.sqrt_eq_rpow _).symm
    have hh5 : (h : ℝ) ≤ (h : ℝ) ^ (5 : ℕ) :=
      le_self_pow₀ hh1r (by norm_num)
    have hlog0 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have hamp : (h : ℝ) * (Real.log 16 +
        2 * (sliceK κ h : ℝ) * sliceT κ h) ≤ Real.log (n : ℝ) := by
      calc
        _ ≤ (Real.log 16 + 2) * (h : ℝ) ^ (5 : ℕ) := by
          nlinarith only [mul_le_mul_of_nonneg_right hh5 hlog0, hhkt]
        _ ≤ (Real.log 16 + 2) * Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
        _ ≤ C * Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
        _ ≤ _ := hroom
    have ht1 : (1 : ℝ) ≤ sliceT κ h := by
      apply le_trans _ (Nat.le_ceil _)
      exact Real.one_le_rpow hh1r hκ.ω_rng.1.le
    have heps : 0.001 * κ.a * (sliceK κ h : ℝ) * h ≤ Real.log (n : ℝ) := by
      have hkT : (sliceK κ h : ℝ) ≤ (sliceK κ h : ℝ) * sliceT κ h :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) ht1
      calc
        _ ≤ (0.001 * κ.a) * (h : ℝ) ^ (5 : ℕ) := by
          have hh := mul_le_mul_of_nonneg_left hkT (Nat.cast_nonneg h)
          have hh' := mul_le_mul_of_nonneg_left (hh.trans hhkt)
            (by positivity : (0 : ℝ) ≤ 0.001 * κ.a)
          nlinarith only [hh']
        _ ≤ (0.001 * κ.a) * Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
        _ ≤ C * Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
        _ ≤ _ := hroom
    constructor
    · calc
        _ = Real.exp ((h : ℝ) * (Real.log 16 +
            2 * (sliceK κ h : ℝ) * sliceT κ h)) := by
          rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hamp
        _ = _ := Real.exp_log hnp
    · change Real.rpow (n : ℝ) (-1) ≤ Real.exp (-0.001 * κ.a * (sliceK κ h : ℝ) * h)
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hnp]
      apply Real.exp_le_exp.mpr
      nlinarith only [heps]

/-- Dimension-only room for all supported slice-history normalizer rows.
The atom bound is n/B and L is at least n^199. -/
theorem cluster_normalizer_budget_room : ∃ n₀ : ℕ, ∀ (n : ℕ) (L B Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → 0 < B → (n : ℝ) ^ (199 : ℕ) ≤ L →
    L ^ 2 / B ≤ Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 →
    Checks ≤ (n : ℝ) ^ (200 : ℕ) * Real.exp ((n : ℝ) ^ (1.01 : ℝ)) →
    ((n : ℝ) * L ^ 2 / B + ((n : ℝ) + 1) / L ≤ Real.rpow (n : ℝ) (-4) / 2) ∧
    (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      L * Real.rpow (n : ℝ) (-4) ^ 2 / (8 * (n : ℝ) ^ (2 : ℕ))) := by
  obtain ⟨n₀, hroom⟩ := logarithmic_room (1 / 2) 1 0 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n L B Checks hn hn2 hB hL hcollision hchecks
  let x : ℝ := n
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hρ : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div] <;> exact hx.le
  have hsmall : Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ 1 / x ^ (5 : ℕ) := by
    have hr := hroom n hn
    simp only [one_mul, zero_add] at hr
    have he := Real.exp_le_exp.mpr (neg_le_neg hr)
    have he5 : Real.exp (5 * Real.log x) = x ^ (5 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 5
    change Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ Real.exp (-(5 * Real.log x)) at he
    rw [Real.exp_neg (5 * Real.log x), he5] at he
    simpa only [one_div] using he
  have h194 : (8 : ℝ) ≤ x ^ (194 : ℕ) := by
    calc
      8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (194 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have h187 : (2048 : ℝ) ≤ x ^ (187 : ℕ) := by
    calc
      2048 = (2 : ℝ) ^ (11 : ℕ) := by norm_num
      _ ≤ x ^ (11 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (187 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hpinL : 8 * x ^ (5 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (194 : ℕ) * x ^ (5 : ℕ) := mul_le_mul_of_nonneg_right h194 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  have hvarL : 2048 * x ^ (12 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (187 : ℕ) * x ^ (12 : ℕ) := mul_le_mul_of_nonneg_right h187 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  refine ⟨?_, ?_⟩
  · have hpin : (x + 1) / L ≤ Real.rpow x (-4) / 4 := by
      calc
        _ ≤ (2 * x) / L := div_le_div_of_nonneg_right (by linarith) hLp.le
        _ ≤ (2 * x) / (8 * x ^ (5 : ℕ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpinL
        _ = _ := by rw [hρ]; field_simp <;> ring
    have hcoll : x * L ^ 2 / B ≤ Real.rpow x (-4) / 4 := by
      calc
        _ = x * (L ^ 2 / B) := by ring
        _ ≤ x * (Real.exp (-Real.rpow x (1 / 2 : ℝ)) / 4) :=
          mul_le_mul_of_nonneg_left hcollision hx.le
        _ ≤ x * ((1 / x ^ (5 : ℕ)) / 4) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsmall (by norm_num)) hx.le
        _ = _ := by rw [hρ]; field_simp <;> ring
    dsimp only [x] at *
    linarith only [hpin, hcoll]
  · have hlogx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx).trans (by linarith)
    have hx200 : 1 ≤ x ^ (200 : ℕ) := one_le_pow₀ hx1
    have hpow101 : Real.rpow x (1.01 : ℝ) ≤ x ^ (2 : ℕ) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1.01 : ℝ) ≤ 2)
    have hmax : max 1 Checks ≤ x ^ (200 : ℕ) * Real.exp (Real.rpow x (1.01 : ℝ)) := by
      refine max_le ?_ hchecks
      exact one_le_mul_of_one_le_of_one_le hx200
        (Real.one_le_exp_iff.mpr (Real.rpow_nonneg hx.le _))
    have hlog : Real.log (8 * max 1 Checks) ≤ 8 + 200 * x + x ^ (2 : ℕ) := by
      calc
        _ ≤ Real.log (8 * (x ^ (200 : ℕ) * Real.exp (Real.rpow x (1.01 : ℝ)))) :=
          Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hmax (by norm_num))
        _ = Real.log 8 + 200 * Real.log x + Real.rpow x (1.01 : ℝ) := by
          rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
            Real.log_mul (by positivity : x ^ (200 : ℕ) ≠ 0) (Real.exp_pos _).ne',
            Real.log_pow, Real.log_exp]
          ring
        _ ≤ _ := by nlinarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8), hlogx, hpow101]
    have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hpoly : 256 * x ^ (2 : ℕ) ≤ L * Real.rpow x (-4) ^ 2 / (8 * x ^ (2 : ℕ)) := by
      calc
        _ = (2048 * x ^ (12 : ℕ)) * Real.rpow x (-4) ^ 2 / (8 * x ^ (2 : ℕ)) := by
          rw [hρ]; field_simp <;> ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hvarL (sq_nonneg _)) (by positivity)
    apply le_trans _ hpoly
    nlinarith only [hlog, hroot, hx2, mul_nonneg (by linarith : 0 ≤ x - 2) (by linarith : 0 ≤ x)]

private theorem finLaw_bind_pr {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (K : A → FinLaw B) (E : A × B → Prop) :
    (FinLaw.bind P K).pr E = P.E (fun a => (K a).pr (fun b => E (a, b))) := by
  classical
  unfold FinLaw.pr FinLaw.E
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (if E (a, b) then P.w a * (K a).w b else 0) =
    P.w a * (if E (a, b) then (K a).w b else 0)
  split_ifs <;> simp

noncomputable def solver_star_bin_failure {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (a : Group 𝒯 i → Bin 𝒯 i) : ℝ :=
  (FinLaw.pi fun z : IWord 𝒯 i =>
    (⟨S.U (S.groupOf z) W (a (S.groupOf z)),
      S.U_nonneg (S.groupOf z) W (a (S.groupOf z)),
      S.U_sum (S.groupOf z) W (a (S.groupOf z))⟩ : FinLaw (Fin (T.S.N k)))).pr
    (fun lab => S.σ v W (nbrLabels v.1 lab) = 0)

theorem solver_star_bin_failure_range {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (a : Group 𝒯 i → Bin 𝒯 i) :
    0 ≤ solver_star_bin_failure S W v a ∧ solver_star_bin_failure S W v a ≤ 1 :=
  pr_range _ _

theorem solver_star_failure_integral {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i) :
    (FinLaw.pi fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))).E
      (solver_star_bin_failure S W v) =
    (S.refLaw W).pr (fun ω => S.σ v W (nbrLabels v.1 ω.2) = 0) := by
  symm
  unfold SliceSolver.refLaw internalRefLaw
  rw [finLaw_bind_pr]
  rfl

theorem solver_star_failure_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (hW : S.Hgood v W) :
    (FinLaw.pi fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))).E
      (solver_star_bin_failure S W v) ≤ sliceEps κ (𝒯.P i).h := by
  rw [solver_star_failure_integral]
  exact S.Hgood_zero v W hW

theorem solver_star_positive_pin_integral {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (g : Group 𝒯 i) (D : Bin 𝒯 i) :
    (S.refLaw W).pr (fun ω => ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) =
      S.q g W D * (FinLaw.pi (coordinatePin
        (fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))) g D)).E
        (solver_star_bin_failure S W v) := by
  classical
  let P : Group 𝒯 i → FinLaw (Bin 𝒯 i) := fun g => ⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩
  let K := fun a : Group 𝒯 i → Bin 𝒯 i => FinLaw.pi fun z : IWord 𝒯 i =>
    (⟨S.U (S.groupOf z) W (a (S.groupOf z)),
      S.U_nonneg (S.groupOf z) W (a (S.groupOf z)),
      S.U_sum (S.groupOf z) W (a (S.groupOf z))⟩ : FinLaw (Fin (T.S.N k)))
  have hInner : ∀ a, (K a).pr (fun lab => a g = D ∧ S.σ v W (nbrLabels v.1 lab) = 0) =
      if a g = D then solver_star_bin_failure S W v a else 0 := by
    intro a
    by_cases ha : a g = D
    · simp only [ha, true_and, ↓reduceIte]
      rfl
    · simp [FinLaw.pr, ha]
  change (FinLaw.bind (FinLaw.pi P) K).pr
    (fun ω => ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) = _
  rw [finLaw_bind_pr]
  simp_rw [hInner]
  exact coordinate_pin_E P g D (solver_star_bin_failure S W v)

theorem solver_pretrim_star_pin_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (g : Group 𝒯 i) (D : Bin 𝒯 i) (hD : D ∈ S.pretrimBins W g) (hvg : SliceSolver.Incident v g) :
    (FinLaw.pi (coordinatePin
      (fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))) g D)).E
      (solver_star_bin_failure S W v) ≤ Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  have hp := (Finset.mem_filter.mp hD).2
  have hb := hp.2 v hvg
  rw [solver_star_positive_pin_integral] at hb
  by_contra hn
  have hb' : S.q g W D * (FinLaw.pi (coordinatePin
      (fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))) g D)).E
      (solver_star_bin_failure S W v) ≤ S.q g W D * Real.sqrt (sliceEps κ (𝒯.P i).h) :=
    by simpa only [mul_comm] using hb
  exact (not_lt_of_ge hb') (mul_lt_mul_of_pos_left (lt_of_not_ge hn) hp.1)

noncomputable def solver_star_group_scope {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (v : EvenRole 𝒯 i) : Finset (Group 𝒯 i) :=
  Finset.univ.image fun j => S.groupOf (flipPos v.1 j)

theorem solver_star_group_scope_count {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (v : EvenRole 𝒯 i) :
    (solver_star_group_scope S v).card ≤ (𝒯.P i).h := by
  simpa only [solver_star_group_scope, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_le (s := (Finset.univ : Finset (Fin (𝒯.P i).h)))
      (f := fun j => S.groupOf (flipPos v.1 j))

theorem solver_star_bin_failure_local {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (a b : Group 𝒯 i → Bin 𝒯 i)
    (hab : ∀ g ∈ solver_star_group_scope S v, a g = b g) :
    solver_star_bin_failure S W v a = solver_star_bin_failure S W v b := by
  classical
  letI : Nonempty (Fin (T.S.N k)) := ⟨⟨0, T.S.N_pos k⟩⟩
  unfold solver_star_bin_failure
  rw [pr_eq_indicator_E, pr_eq_indicator_E]
  apply pi_E_local _ _ (Finset.univ.image (flipPos v.1)) _
  · intro x y hxy
    have heq : nbrLabels v.1 x = nbrLabels v.1 y := by
      funext j
      apply hxy
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [heq]
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    congr 1
    exact congrArg (S.U (S.groupOf (flipPos v.1 j)) W)
      (hab _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))

private theorem solver_bins_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) : Nonempty (Bin 𝒯 i) := by
  classical
  by_contra h
  letI : IsEmpty (Bin 𝒯 i) := not_nonempty_iff.mp h
  have hh := S.q_sum (S.groupOf (fun _ => false)) W
  simp at hh

theorem solver_star_trimmed_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (hW : S.Hgood v W) (P : Group 𝒯 i → FinLaw (Bin 𝒯 i)) (c : ℝ) (hc : 0 ≤ c)
    (hP : ∀ g ∈ solver_star_group_scope S v, ∀ D, (P g).w D ≤ c * S.q g W D) :
    (FinLaw.pi P).E (solver_star_bin_failure S W v) ≤
      c ^ (solver_star_group_scope S v).card * sliceEps κ (𝒯.P i).h := by
  classical
  letI : Nonempty (Bin 𝒯 i) := solver_bins_nonempty S W
  calc
    _ ≤ c ^ (solver_star_group_scope S v).card *
        (FinLaw.pi fun g => (⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ : FinLaw (Bin 𝒯 i))).E
          (solver_star_bin_failure S W v) :=
      local_product_domination _ P (solver_star_group_scope S v) c hc hP
        (solver_star_bin_failure S W v) (fun a => (solver_star_bin_failure_range S W v a).1)
        (solver_star_bin_failure_local S W v)
    _ ≤ _ := mul_le_mul_of_nonneg_left (solver_star_failure_mean S W v hW) (pow_nonneg hc _)

theorem solver_star_trimmed_pin_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i)
    (P : Group 𝒯 i → FinLaw (Bin 𝒯 i)) (c : ℝ) (hc : 1 ≤ c)
    (hP : ∀ g ∈ solver_star_group_scope S v, ∀ D, (P g).w D ≤ c * S.q g W D)
    (g : Group 𝒯 i) (D : Bin 𝒯 i) (hD : D ∈ S.pretrimBins W g)
    (hvg : SliceSolver.Incident v g) :
    (FinLaw.pi (coordinatePin P g D)).E (solver_star_bin_failure S W v) ≤
      c ^ (solver_star_group_scope S v).card * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  classical
  letI : Nonempty (Bin 𝒯 i) := solver_bins_nonempty S W
  let Q : Group 𝒯 i → FinLaw (Bin 𝒯 i) := fun g => ⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hPin : ∀ j ∈ solver_star_group_scope S v, ∀ b,
      ((coordinatePin P g D) j).w b ≤ c * ((coordinatePin Q g D) j).w b := by
    intro j hj b
    by_cases hjg : j = g
    · subst j
      simp only [coordinatePin, if_true]
      exact le_mul_of_one_le_left ((FinLaw.dirac D).nonneg b) hc
    · simpa only [coordinatePin, if_neg hjg, Q] using hP j hj b
  calc
    _ ≤ c ^ (solver_star_group_scope S v).card *
        (FinLaw.pi (coordinatePin Q g D)).E (solver_star_bin_failure S W v) :=
      local_product_domination _ _ (solver_star_group_scope S v) c hc0 hPin
        (solver_star_bin_failure S W v) (fun a => (solver_star_bin_failure_range S W v a).1)
        (solver_star_bin_failure_local S W v)
    _ ≤ _ := mul_le_mul_of_nonneg_left (solver_pretrim_star_pin_mean S W v g D hD hvg)
      (pow_nonneg hc0 _)

theorem permission_retained_sharp {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hP : PermissionLossHypotheses P qin) (g : Group) :
    1 - Real.exp (-P.cperm * P.n / 2) ≤ ∑ b ∈ P.permitted g, (qin g).w b := by
  classical
  have hB : (0 : ℝ) < Fintype.card Bin := by
    letI := hP.bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hremoved : (∑ b ∈ Finset.univ \ P.permitted g, (qin g).w b) ≤
      Real.exp (-P.cperm * P.n / 2) := by
    calc
      _ ≤ ((Finset.univ \ P.permitted g).card : ℝ) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) := by
        simpa using Finset.sum_le_sum (s := Finset.univ \ P.permitted g)
          (fun b _ => hP.incoming_cap g b)
      _ ≤ (Real.exp (-P.cperm * P.n) * Fintype.card Bin) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) :=
        mul_le_mul_of_nonneg_right (permission_removed_count P qin hP g) (by positivity)
      _ = _ := by
        field_simp
        rw [← Real.exp_add]
        congr 1
        ring
  have hsplit := Finset.sum_sdiff (s₁ := P.permitted g) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := (qin g).w)
  rw [(qin g).sum_one] at hsplit
  linarith

/-- Two small normalization losses over at most h groups cost at most two. -/
theorem normalization_product_room (h m : ℕ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u < 1) (hv1 : v < 1)
    (hm : m ≤ h) (hsmall : (h : ℝ) * (u + v) ≤ 1 / 2) :
    1 ≤ ((1 - u) * (1 - v))⁻¹ ∧
      (((1 - u) * (1 - v))⁻¹) ^ m ≤ 2 := by
  have hbpos : 0 < (1 - u) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hbone : (1 - u) * (1 - v) ≤ 1 := by nlinarith [mul_nonneg hu (by linarith : 0 ≤ 1 - v)]
  have hbase : 1 - (u + v) ≤ (1 - u) * (1 - v) := by nlinarith [mul_nonneg hu hv]
  have hBern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ (1 - u) * (1 - v)) m
  have hm' : (m : ℝ) ≤ h := by exact_mod_cast hm
  have hlin : (m : ℝ) * (u + v) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hm' (add_nonneg hu hv)).trans hsmall
  have hpow : (1 / 2 : ℝ) ≤ ((1 - u) * (1 - v)) ^ m := by
    have hb := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg m)
    nlinarith only [hBern, hb, hlin]
  constructor
  · exact (one_le_inv₀ hbpos).mpr hbone
  · rw [inv_pow]
    calc
      _ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
      _ = 2 := by norm_num

theorem cluster_permission_cost_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ n h : ℕ, n₀ ≤ n → 2 ≤ n → h ≤ n →
      (h : ℝ) * Real.exp (-κ.cperm * n / 2) ≤ 1 / 4 := by
  obtain ⟨n₀, hroom⟩ := logarithmic_room 1 (κ.cperm / 2)
    (Real.log 4) 1 (by norm_num) (div_pos hκ.cperm_rng.1 (by norm_num)) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n h hn hn2 hh
  have hnp : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hx := hroom n hn
  simp only [Real.rpow_one, one_mul] at hx
  have he : Real.exp (-κ.cperm * n / 2) ≤ 1 / (4 * (n : ℝ)) := by
    calc
      _ ≤ Real.exp (-(Real.log 4 + Real.log (n : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log hnp]
        simp only [one_div]
  have hh' : (h : ℝ) ≤ n := by exact_mod_cast hh
  calc
    _ ≤ (n : ℝ) * (1 / (4 * (n : ℝ))) :=
      mul_le_mul hh' he (Real.exp_pos _).le (Nat.cast_nonneg n)
    _ = _ := by field_simp

end HypercubeRamsey.S16.Lane_sol_s16_prod1
