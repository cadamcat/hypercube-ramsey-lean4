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

theorem low_cluster_pretrim_small {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hm : PT.tiling.mode = .lowCluster)
    (i : Fin PT.tiling.m) :
    ((PT.tiling.P i).h : ℝ) ^ 2 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) ≤ 1 / 2 := by
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
  have hpow := pow_le_pow_right₀ hh1 (by norm_num : (2 : ℕ) ≤ 6)
  calc
    _ ≤ ((PT.tiling.P i).h : ℝ) ^ 6 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
    _ ≤ Real.rpow 10 (-3) := hs
    _ ≤ _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]

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

end HypercubeRamsey.S16.Lane_sol_s16_prod1
