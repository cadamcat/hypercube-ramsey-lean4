import HypercubeRamsey.S16.Producers_q_s16_prod1
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.S16.Comparisons

namespace HypercubeRamsey.S16.Lane_sol_s16_prod1

open Classical
open scoped BigOperators
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

end HypercubeRamsey.S16.Lane_sol_s16_prod1
