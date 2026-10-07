import HypercubeRamsey.S15.ClusterNodes_q_s15_c1
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S15.Needs

namespace HypercubeRamsey.Lane_sol_s15_load

open HypercubeRamsey HypercubeRamsey.S15 Lane_q_s15_c1 Classical Filter
open scoped BigOperators
open HypercubeRamsey.S15.Needs

set_option maxHeartbeats 1000000

theorem finLaw_map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (g ∘ f) := by
  classical
  simp only [FinLaw.E, FinLaw.map]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem pi_E_prod_injective {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (t : J → ι) (ht : Function.Injective t)
    (f : ∀ j, Ω (t j) → ℝ) :
    (FinLaw.pi P).E (fun ω => ∏ j, f j (ω (t j))) =
      ∏ j, (P (t j)).E (f j) := by
  classical
  have aux (s : Finset J) :
      (FinLaw.pi P).E (fun ω => ∏ j ∈ s, f j (ω (t j))) =
        ∏ j ∈ s, (P (t j)).E (f j) := by
    induction s using Finset.induction_on with
    | empty => simp [FinLaw.E, (FinLaw.pi P).sum_one]
    | @insert j s hj ih =>
      simp only [Finset.prod_insert hj]
      rw [pi_E_mul_of_disjoint P (fun ω => f j (ω (t j)))
        (fun ω => ∏ a ∈ s, f a (ω (t a))) {t j} (s.image t)]
      · rw [pi_E_coordinate, ih]
      · intro ω ω' h
        change f j (ω (t j)) = f j (ω' (t j))
        rw [h (t j) (by simp)]
      · intro ω ω' h
        apply Finset.prod_congr rfl
        intro a ha
        rw [h (t a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
      · simp only [Finset.disjoint_singleton_left, Finset.mem_image]
        rintro ⟨a, ha, h⟩
        exact hj (ht h ▸ ha)
  exact aux Finset.univ

abbrev PatchSlices {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) :=
  {o : OAI.HypercubeRamsey.CubeVertex (T.S.n k - (PT.tiling.P i).h) //
    ∀ j : Fin (T.S.n k - (PT.tiling.P i).h), j.val < (PT.tiling.P i).ℓ →
      o j = PT.tiling.w i ⟨j.val, by have := j.isLt; omega⟩}

abbrev PatchGroups {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) :=
  PatchSlices PT i × Group PT.tiling i

noncomputable def groupMarginal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a : PatchGroups PT i)
    (W : ClusterHistory PT hPT hm) (y : Fin (T.S.N k)) : ℝ :=
  (clusterSolver PT hPT hm i).oddMarginal a.2 (historyOnSlice W ⟨i, a.1⟩) y

theorem groupMarginal_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a : PatchGroups PT i) (W : ClusterHistory PT hPT hm) y :
    0 ≤ groupMarginal PT hPT hm i a W y := by
  unfold groupMarginal SliceSolver.oddMarginal
  exact Finset.sum_nonneg fun D _ => mul_nonneg
    ((clusterSolver PT hPT hm i).q_nonneg _ _ D)
    ((clusterSolver PT hPT hm i).U_nonneg _ _ D y)

theorem groupMarginal_cap {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a : PatchGroups PT i) (W : ClusterHistory PT hPT hm) y :
    groupMarginal PT hPT hm i a W y ≤
      8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) /
        (PT.tiling.P i).M :=
  (clusterSolver PT hPT hm i).marginal_cap _ _ y

theorem groupMarginal_product_mean {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) {m : ℕ} (a : Fin m → PatchGroups PT i)
    (ha : Function.Injective (fun j => (a j).1)) (y : Fin (T.S.N k)) :
    (clusterHistoryLaw PT hPT hm).E
      (fun W => ∏ j, groupMarginal PT hPT hm i (a j) W y) =
        ∏ _j : Fin m, (PT.π i).w y := by
  let t : Fin m → ClusterSlice PT := fun j => ⟨i, (a j).1⟩
  have ht : Function.Injective t := by
    intro j j' h
    apply ha
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hmean (j : Fin m) :
      ((clusterSolver PT hPT hm i).recLaw PT.parameter).E
        (fun W => (clusterSolver PT hPT hm i).oddMarginal (a j).2 W y) =
          (PT.π i).w y := by
    rw [hPT.high_profile hm i]
    exact (hPT.raw_profile (highMode_isCluster PT hm) i _
      (Classical.choose_spec (hPT.cluster_solver (highMode_isCluster PT hm) i))
      (a j).2 y).symm
  calc
    _ = (clusterSlicedHistoryLaw PT hPT hm).E
        (fun X => ∏ j, (clusterSolver PT hPT hm i).oddMarginal (a j).2 (X (t j)) y) := by
      rw [← clusterHistoryLaw_map_curry, finLaw_map_E]
      rfl
    _ = ∏ j, ((clusterSolver PT hPT hm i).recLaw PT.parameter).E
        (fun W => (clusterSolver PT hPT hm i).oddMarginal (a j).2 W y) := by
      exact pi_E_prod_injective
        (fun s : ClusterSlice PT => (clusterSolver PT hPT hm s.1).recLaw PT.parameter)
        t ht (fun j W => (clusterSolver PT hPT hm i).oddMarginal (a j).2 W y)
    _ = _ := Finset.prod_congr rfl fun j _ => hmean j

theorem groupMarginal_product_local {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) {m : ℕ} (a : Fin m → PatchGroups PT i) (y : Fin (T.S.N k)) :
    ClusterHistoryDependsOn (fun W => ∏ j, groupMarginal PT hPT hm i (a j) W y)
      (clusterConsultationScope PT hPT hm
        (Finset.univ.image fun j => (⟨⟨i, (a j).1⟩, (a j).2.1⟩ : ClusterConsultation PT))) := by
  intro W W' h
  apply Finset.prod_congr rfl
  intro j _
  have hs : { (⟨⟨i, (a j).1⟩, (a j).2.1⟩ : ClusterConsultation PT) } ⊆
      Finset.univ.image (fun j => (⟨⟨i, (a j).1⟩, (a j).2.1⟩ : ClusterConsultation PT)) := by
    intro c hc
    rw [Finset.mem_singleton.mp hc]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hlocal := clusterSliceGroupLaws_eq_of_consultation_scope PT hPT hm
    ⟨i, (a j).1⟩ (a j).2 W W' (fun r hr => h r
      (clusterConsultationScope_mono PT hPT hm _ _ hs hr))
  unfold groupMarginal SliceSolver.oddMarginal
  apply Finset.sum_congr rfl
  intro D _
  rw [congrFun hlocal.1 D, congrFun (hlocal.2 D) y]

theorem patchSlices_card {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    Fintype.card (PatchSlices PT i) =
      2 ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) := by
  let n := T.S.n k - (PT.tiling.P i).h
  let ell := (PT.tiling.P i).ℓ
  have hlen : ell ≤ n := by
    have hl := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
      (Finset.mem_univ i)
    have h := hPT.tiling_valid.prefix_internal_length
    dsimp [ell, n]
    omega
  let e : PatchSlices PT i ≃ (Fin (n - ell) → Bool) := {
    toFun := fun o j => o.1 ⟨ell + j.val, by have := j.isLt; omega⟩
    invFun := fun z => ⟨fun j => if hj : j.val < ell then
      PT.tiling.w i ⟨j.val, by have := j.isLt; dsimp [n] at *; omega⟩
      else z ⟨j.val - ell, by have := j.isLt; omega⟩,
      by intro j hj; have hj' : j.val < ell := hj; simp [hj']⟩
    left_inv := by
      intro o
      apply Subtype.ext
      funext j
      dsimp
      split_ifs with hj
      · exact (o.2 j hj).symm
      · exact congrArg o.1 (Fin.ext (by dsimp; omega))
    right_inv := by
      intro z
      funext j
      dsimp
      rw [dif_neg (by omega)]
      exact congrArg z (Fin.ext (by dsimp; omega)) }
  simpa [n, ell] using Fintype.card_congr e

theorem group_roles_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) :
    Fintype.card (Group PT.tiling i) * (PT.tiling.P i).h ≤ 2 ^ (PT.tiling.P i).h := by
  let S := clusterSolver PT hPT hm i
  let f : Group PT.tiling i × Fin (PT.tiling.P i).h → IWord PT.tiling i :=
    fun a => flipPos a.1.1 a.2
  have hf : Function.Injective f := by
    rintro ⟨g, j⟩ ⟨g', j'⟩ h
    have hz : ¬ IsEvenRole (flipPos g.1 j) := by
      intro he
      exact ((evenRole_flipPos g.1 j).mp he) g.2.1
    have hg : flipPos g.1 j ∈ groupFiber g := by
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hg' : flipPos g.1 j ∈ groupFiber g' := by
      rw [show flipPos g.1 j = flipPos g'.1 j' from h]
      exact Finset.mem_image.mpr ⟨j', Finset.mem_univ _, rfl⟩
    have hgg : g = g' := by
      obtain ⟨g0, _, huniq⟩ := S.group_partition _ hz
      exact (huniq g hg).trans (huniq g' hg').symm
    subst g'
    have hjj : j = j' := by
      by_contra hn
      have he := congrFun h j
      simp [f, flipPos, hn] at he
    subst j'
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, IWord, CubePos] using hc

noncomputable def patchColumn {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (W : ClusterHistory PT hPT hm) (y : Fin (T.S.N k)) : ℝ :=
  (PT.tiling.P i).h * ∑ a : PatchGroups PT i, groupMarginal PT hPT hm i a W y

theorem groupMarginal_scaled_product_mean {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) {m : ℕ} (a : Fin m → PatchGroups PT i)
    (ha : Function.Injective (fun j => (a j).1)) (y : Fin (T.S.N k)) :
    (clusterHistoryLaw PT hPT hm).E
      (fun W => ∏ j, ((PT.tiling.P i).M * groupMarginal PT hPT hm i (a j) W y)) =
        ∏ _j : Fin m, ((PT.tiling.P i).M * (PT.π i).w y) := by
  simp only [Finset.prod_mul_distrib]
  unfold FinLaw.E
  rw [show (∑ W, (clusterHistoryLaw PT hPT hm).w W *
    ((∏ _j : Fin m, ((PT.tiling.P i).M : ℝ)) *
      ∏ j, groupMarginal PT hPT hm i (a j) W y)) =
    (∏ _j : Fin m, ((PT.tiling.P i).M : ℝ)) *
      (clusterHistoryLaw PT hPT hm).E (fun W =>
        ∏ j, groupMarginal PT hPT hm i (a j) W y) by
      simp [FinLaw.E, Finset.mul_sum]; congr 1; funext W; ring]
  rw [groupMarginal_product_mean PT hPT hm i a ha y]

theorem patchColumn_moment {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (P : FinLaw (ClusterHistory PT hPT hm))
    (hcompare : ∀ F : ClusterHistory PT hPT hm → ℝ, (∀ W, 0 ≤ F W) →
      ∀ U : Finset (ClusterConsultation PT),
      ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U) →
      (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 →
        P.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterHistoryLaw PT hPT hm).E F)
    (hn : 1 ≤ T.S.n k)
    (hsmall : (T.S.n k : ℝ) *
      (Fintype.card (PatchSlices PT i) : ℝ)⁻¹ *
        (8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)) ≤ 1)
    (y : Fin (T.S.N k)) :
    P.E (fun W => ((Fintype.card (PatchGroups PT i) : ℝ)⁻¹ *
      ∑ a : PatchGroups PT i, (PT.tiling.P i).M * groupMarginal PT hPT hm i a W y)
        ^ (T.S.n k)) ≤ (24 : ℝ) ^ (T.S.n k) := by
  classical
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hS : 0 < Fintype.card (PatchSlices PT i) := by
    rw [patchSlices_card PT hPT i]
    positivity
  letI : Nonempty (PatchSlices PT i) := Fintype.card_pos_iff.mp hS
  letI : Nonempty (Group PT.tiling i) :=
    ⟨(clusterSolver PT hPT hm i).groupOf (fun _ => false)⟩
  let Z : PatchGroups PT i → ClusterHistory PT hPT hm → ℝ :=
    fun a W => (PT.tiling.P i).M * groupMarginal PT hPT hm i a W y
  let near : PatchGroups PT i → Finset (PatchGroups PT i) :=
    fun a => Finset.univ.filter fun b => b.1 = a.1
  let f : ℝ := (Fintype.card (PatchSlices PT i) : ℝ)⁻¹
  let L : ℝ := 8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)
  let d : ℝ := (PT.tiling.P i).M * (PT.π i).w y
  have hZ : ∀ a W, 0 ≤ Z a W := fun a W =>
    mul_nonneg hM.le (groupMarginal_nonneg PT hPT hm i a W y)
  have hd : 0 ≤ d := mul_nonneg hM.le ((PT.π i).nonneg y)
  have hd11 : d ≤ 11 := by
    have h := (mul_le_mul_of_nonneg_left (hPT.law_cap i y) hM.le)
    simpa [d, mul_div_cancel₀, ne_of_gt hM] using h
  have hnear (a : PatchGroups PT i) : ((near a).card : ℝ) ≤
      f * Fintype.card (PatchGroups PT i) := by
    have hc : (near a).card = Fintype.card (Group PT.tiling i) := by
      have heq : near a = {a.1} ×ˢ (Finset.univ : Finset (Group PT.tiling i)) := by
        ext b
        simp only [near, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, Finset.mem_singleton, and_true]
      rw [heq]
      simp
    rw [hc, Fintype.card_prod, Nat.cast_mul]
    dsimp [f]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hS.ne'), one_mul]
  have hjoint : ∀ m ≤ T.S.n k, ∀ a : Fin m → PatchGroups PT i,
      (∀ j l : Fin m, l < j → a j ∉ near (a l)) →
        ∑ W ∈ (Finset.univ : Finset (ClusterHistory PT hPT hm)),
          P.w W * ∏ j, Z (a j) W ≤ (2 : ℝ) ^ m * ∏ _j : Fin m, d := by
    intro m hm' a hsep
    by_cases hm0 : m = 0
    · subst m
      simp [P.sum_one]
    have ha : Function.Injective (fun j => (a j).1) := by
      intro j l h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hsep l j hlt (by simp [near, h])
      · exact hsep j l hgt (by simp [near, h])
    let U : Finset (ClusterConsultation PT) := Finset.univ.image
      fun j => ⟨⟨i, (a j).1⟩, (a j).2.1⟩
    have hdep : ClusterHistoryDependsOn (fun W => ∏ j, Z (a j) W)
        (clusterConsultationScope PT hPT hm U) := by
      intro W W' h
      simp only [Z, Finset.prod_mul_distrib]
      exact congrArg (fun z => (∏ _j : Fin m, ((PT.tiling.P i).M : ℝ)) * z)
        (groupMarginal_product_local PT hPT hm i a y W W' h)
    have hcard : (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 := by
      have hU : U.card ≤ m := (Finset.card_image_le).trans (by simp)
      have hn1 : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
      have hpow : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 5 := by
        simpa using pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 5)
      exact (show (U.card : ℝ) ≤ T.S.n k by exact_mod_cast hU.trans hm').trans hpow
    have hcmp := hcompare (fun W => ∏ j, Z (a j) W)
      (fun W => Finset.prod_nonneg fun j _ => hZ (a j) W) U hdep hcard
    have hmean := groupMarginal_scaled_product_mean PT hPT hm i a ha y
    have hcoeff : 1 + 1 / (T.S.n k : ℝ) ≤ (2 : ℝ) ^ m := by
      have hinv : 1 / (T.S.n k : ℝ) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (show (1 : ℝ) ≤ T.S.n k by exact_mod_cast hn)
      have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (show 1 ≤ m by omega)
      linarith
    simpa only [FinLaw.E] using hcmp.trans (by
      rw [show (clusterHistoryLaw PT hPT hm).E (fun W => ∏ j, Z (a j) W) =
        ∏ _j : Fin m, d from hmean]
      exact mul_le_mul_of_nonneg_right hcoeff (Finset.prod_nonneg fun _ _ => hd))
  have hmoment := scattered_moments P.w P.nonneg Finset.univ Z hZ L
    (by dsimp [L]; positivity)
    (by
      intro a W _
      dsimp [Z, L]
      have h := mul_le_mul_of_nonneg_left (groupMarginal_cap PT hPT hm i a W y) hM.le
      simpa [mul_div_cancel₀, ne_of_gt hM] using h)
    near (by intro a; simp [near]) f hnear (T.S.n k) 2 (by norm_num)
    (fun _ => d) (fun _ => hd) hjoint
  have hG : (Fintype.card (PatchGroups PT i) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (PatchGroups PT i) ≠ 0)
  have havg : (Fintype.card (PatchGroups PT i) : ℝ)⁻¹ *
      ∑ _a : PatchGroups PT i, d = d := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hG, one_mul]
  rw [havg] at hmoment
  have hbase : d + (T.S.n k : ℝ) * f * L ≤ 12 := by
    linarith [hsmall]
  have hbase0 : 0 ≤ d + (T.S.n k : ℝ) * f * L := by dsimp [f, L]; positivity
  calc
    _ ≤ (2 : ℝ) ^ (T.S.n k) * (d + (T.S.n k : ℝ) * f * L) ^ (T.S.n k) := hmoment
    _ ≤ (2 : ℝ) ^ (T.S.n k) * (12 : ℝ) ^ (T.S.n k) := by gcongr
    _ = (24 : ℝ) ^ (T.S.n k) := by rw [← mul_pow]; norm_num

theorem patchColumn_average_conversion {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (W : ClusterHistory PT hPT hm) y :
    patchColumn PT hPT hm i W y ≤ 800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k *
      ((Fintype.card (PatchGroups PT i) : ℝ)⁻¹ *
        ∑ a : PatchGroups PT i, (PT.tiling.P i).M * groupMarginal PT hPT hm i a W y) := by
  have hS : 0 < Fintype.card (PatchSlices PT i) := by
    rw [patchSlices_card PT hPT i]; positivity
  letI : Nonempty (PatchSlices PT i) := Fintype.card_pos_iff.mp hS
  letI : Nonempty (Group PT.tiling i) :=
    ⟨(clusterSolver PT hPT hm i).groupOf (fun _ => false)⟩
  have hU : (Fintype.card (PatchGroups PT i) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hSp : (0 : ℝ) < PT.tiling.S := by nlinarith [hPT.tiling_valid.S_lower]
  have hlen : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ T.S.n k := by
    have hl := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
      (Finset.mem_univ i)
    have h := hPT.tiling_valid.prefix_internal_length
    omega
  have hcount : (Fintype.card (PatchGroups PT i) : ℝ) * (PT.tiling.P i).h ≤
      (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) := by
    rw [Fintype.card_prod, Nat.cast_mul, patchSlices_card PT hPT i, Nat.cast_pow,
      Nat.cast_ofNat]
    calc
      _ = (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) *
          ((Fintype.card (Group PT.tiling i) : ℝ) * (PT.tiling.P i).h) := by ring
      _ ≤ (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) *
          (2 : ℝ) ^ (PT.tiling.P i).h := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast group_roles_card_le PT hPT hm i
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hpow : (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
      (2 : ℝ) ^ (PT.tiling.P i).ℓ = (2 : ℝ) ^ (T.S.n k) := by
    rw [← pow_add]; congr 1; omega
  have hdyad := hPT.tiling_valid.dyadic_mass_upper i
  have hz : (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) =
      1 / (2 : ℝ) ^ (PT.tiling.P i).ℓ := by simp [zpow_neg]
  rw [hz] at hdyad
  have hdyad' : (PT.tiling.S : ℝ) < 2 * (PT.tiling.P i).M *
      (2 : ℝ) ^ (PT.tiling.P i).ℓ := by
    have hh := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (PT.tiling.P i).ℓ) hSp).mp hdyad
    nlinarith [hh]
  have hrecip : 1 / (PT.tiling.P i).M ≤
      2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S := by
    apply (div_le_div_iff₀ hM hSp).2
    nlinarith [hdyad']
  have hratio : (Fintype.card (PatchGroups PT i) : ℝ) * (PT.tiling.P i).h /
      (PT.tiling.P i).M ≤ 800 * (2 : ℝ) ^ (T.S.n k) / T.S.N k := by
    calc
      _ = ((Fintype.card (PatchGroups PT i) : ℝ) * (PT.tiling.P i).h) *
          (1 / (PT.tiling.P i).M) := by ring
      _ ≤ (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ) *
          (2 * (2 : ℝ) ^ (PT.tiling.P i).ℓ / PT.tiling.S) :=
        mul_le_mul hcount hrecip (by positivity) (by positivity)
      _ = 2 * (2 : ℝ) ^ (T.S.n k) / PT.tiling.S := by rw [← hpow]; ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ hSp hN).2
        have h := mul_le_mul_of_nonneg_left hPT.tiling_valid.S_lower
          (by positivity : (0 : ℝ) ≤ 800 * 2 ^ (T.S.n k))
        nlinarith [h]
  have hsum0 : 0 ≤ ∑ a : PatchGroups PT i,
      (PT.tiling.P i).M * groupMarginal PT hPT hm i a W y :=
    Finset.sum_nonneg fun a _ => mul_nonneg hM.le (groupMarginal_nonneg PT hPT hm i a W y)
  calc
    _ = ((Fintype.card (PatchGroups PT i) : ℝ) * (PT.tiling.P i).h /
      (PT.tiling.P i).M) * ((Fintype.card (PatchGroups PT i) : ℝ)⁻¹ *
        ∑ a : PatchGroups PT i, (PT.tiling.P i).M * groupMarginal PT hPT hm i a W y) := by
      unfold patchColumn
      rw [← Finset.mul_sum]
      field_simp [hU, hM.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (mul_nonneg (by positivity) hsum0)

theorem marginal_zero_outside_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a : PatchGroups PT i) (W : ClusterHistory PT hPT hm) y
    (hy : y ∉ (PT.tiling.P i).Y) : groupMarginal PT hPT hm i a W y = 0 := by
  unfold groupMarginal SliceSolver.oddMarginal
  apply Finset.sum_eq_zero
  intro D _
  have hU : (clusterSolver PT hPT hm i).U a.2 (historyOnSlice W ⟨i, a.1⟩) D y = 0 := by
    by_contra h
    have hyD := (clusterSolver PT hPT hm i).U_support _ _ _ y h
    exact hy ((PT.tiling.P i).bins.le D.2 hyD)
  rw [hU, mul_zero]

theorem historyLoad_of_patchColumns {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm)
    (hcol : ∀ i y, patchColumn PT hPT hm i W y < κ.θstar)
    (htheta : 0 < κ.θstar) : clusterHistoryLoad PT hPT hm W := by
  intro y
  have heq : (∑ s : ClusterSlice PT, ∑ g : Group PT.tiling s.1,
      (PT.tiling.P s.1).h * (clusterSolver PT hPT hm s.1).oddMarginal g
        (historyOnSlice W s) y) = ∑ i, patchColumn PT hPT hm i W y := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    simp [patchColumn, Fintype.sum_prod_type, groupMarginal, Finset.mul_sum]
  rw [heq]
  by_cases hex : ∃ i, y ∈ (PT.tiling.P i).Y
  · obtain ⟨i, hi⟩ := hex
    have hz : ∀ j ≠ i, patchColumn PT hPT hm j W y = 0 := by
      intro j hji
      have hj : y ∉ (PT.tiling.P j).Y := by
        intro hj
        exact Finset.disjoint_left.mp (hPT.tiling_valid.patch_Y_disjoint j i hji) hj hi
      simp [patchColumn, marginal_zero_outside_patch PT hPT hm j _ W y hj]
    rw [Finset.sum_eq_single i (by intro j _ hji; exact hz j hji) (by simp)]
    exact hcol i y
  · have hy : ∀ i, y ∉ (PT.tiling.P i).Y := by simpa using hex
    have hz : ∀ i, patchColumn PT hPT hm i W y = 0 := by
      intro i
      simp [patchColumn, marginal_zero_outside_patch PT hPT hm i _ W y (hy i)]
    simp only [hz, Finset.sum_const_zero]
    exact htheta

theorem high_scale_KT_le_height {κ : CConsts} {T : Stage} {k : ℕ}
    (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) :
    2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 8 * (PT.tiling.P i).h := by
  have hAC : κ.aC < 1 := by
    have hmin := min_le_right κ.η0 (1 : ℝ)
    linarith [hκ.aC_rng.2]
  have hMhi0 : 0 < (κ.Mhi : ℝ) := by
    by_contra h
    have hzero : (κ.Mhi : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    have hbig := hκ.Mhi_big.2
    rw [hzero, mul_zero] at hbig
    norm_num at hbig
  have hMhi1 : (1 : ℝ) ≤ κ.Mhi := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hMhi0.ne'))
  have hω : 4 * κ.ω ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hMhi1 (by nlinarith [hκ.ω_rng.1] : 0 ≤ 5 * κ.ω)
    nlinarith [hκ.ω_rng.2]
  have hH : (1 : ℝ) ≤ (PT.tiling.P i).h := by
    exact_mod_cast clusterHeight_pos PT hPT hm i
  have hk : (PT.tiling.kScale i : ℝ) ≤ 2 * (PT.tiling.P i).h ^ (3 * κ.ω) := by
    have hpow : (1 : ℝ) ≤ (PT.tiling.P i).h ^ (3 * κ.ω) :=
      Real.one_le_rpow hH (by nlinarith [hκ.ω_rng.1])
    simpa [Tiling.kScale, sliceK] using Nat.ceil_le_two_mul
      ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hpow)
  have ht : (PT.tiling.tScale i : ℝ) ≤ 2 * (PT.tiling.P i).h ^ κ.ω := by
    have hpow : (1 : ℝ) ≤ (PT.tiling.P i).h ^ κ.ω :=
      Real.one_le_rpow hH hκ.ω_rng.1.le
    simpa [Tiling.tScale, sliceT] using Nat.ceil_le_two_mul
      ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hpow)
  calc
    _ ≤ 2 * (2 * ((PT.tiling.P i).h : ℝ) ^ (3 * κ.ω)) *
        (2 * ((PT.tiling.P i).h : ℝ) ^ κ.ω) := by gcongr
    _ = 8 * ((PT.tiling.P i).h : ℝ) ^ (4 * κ.ω) := by
      rw [show 4 * κ.ω = 3 * κ.ω + κ.ω by ring,
        Real.rpow_add (by positivity : (0 : ℝ) < (PT.tiling.P i).h)]
      ring
    _ ≤ 8 * ((PT.tiling.P i).h : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hH hω
      simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 8)

theorem history_load_small_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, 1 ≤ T.S.n k ∧ ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m,
      (T.S.n k : ℝ) * (Fintype.card (PatchSlices PT i) : ℝ)⁻¹ *
        (8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)) ≤ 1 := by
  let n : ℕ → ℝ := fun k => T.S.n k
  have hn : Tendsto n atTop atTop := (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have hp : Tendsto (fun k => n k ^ (0.1 : ℝ) / n k) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.9)).comp hn
    apply h.congr'
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    change n k ^ (-0.9 : ℝ) = n k ^ (0.1 : ℝ) / n k
    rw [show (-0.9 : ℝ) = 0.1 - 1 by norm_num, Real.rpow_sub hk, Real.rpow_one]
  have hl : Tendsto (fun k => Real.log (n k) / n k) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp' := hp.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.log 2 / 40))
  have hl' := hl.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.log 2 / 4))
  have hconst := hn.eventually_ge_atTop (max 1 (4 * Real.log 8 / Real.log 2))
  have hι : κ.ι ≤ 0.1 := by
    have hmin := (min_le_right κ.xs (min κ.η0 0.01)).trans (min_le_right κ.η0 0.01)
    linarith [hκ.ι_rng.2]
  filter_upwards [hp', hl', hconst] with k hpk hlk hck
  have hn1 : (1 : ℝ) ≤ n k := (le_max_left _ _).trans hck
  have hn0 : 0 < n k := by linarith
  refine ⟨by have hn1' : (1 : ℝ) ≤ T.S.n k := hn1; exact_mod_cast hn1', ?_⟩
  intro PT hPT hm i
  have hH : ((PT.tiling.P i).h : ℝ) ≤ n k ^ (0.1 : ℝ) := by
    have h := (hPT.tiling_valid.allocation_bounds i).1
    exact (le_max_left _ _).trans h.le |>.trans
      (Real.rpow_le_rpow_of_exponent_le hn1 hι)
  have hEll : ((PT.tiling.P i).ℓ : ℝ) ≤ n k ^ (0.1 : ℝ) := by
    have h := (hPT.tiling_valid.allocation_bounds i).1
    exact (le_max_right _ _).trans h.le |>.trans
      (Real.rpow_le_rpow_of_exponent_le hn1 hι)
  have hpBound : 10 * n k ^ (0.1 : ℝ) ≤ n k * Real.log 2 / 4 := by
    have h := (div_lt_iff₀ hn0).mp hpk
    linarith
  have hlBound : Real.log (n k) ≤ n k * Real.log 2 / 4 := by
    have h := (div_lt_iff₀ hn0).mp hlk
    linarith
  have hcBound : Real.log 8 ≤ n k * Real.log 2 / 4 := by
    have h := (le_max_right _ _).trans hck
    have h' := (div_le_iff₀ hlog2).mp h
    linarith
  have hlog2one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlen : (PT.tiling.P i).h + (PT.tiling.P i).ℓ ≤ T.S.n k := by
    have hl := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
      (Finset.mem_univ i)
    have h := hPT.tiling_valid.prefix_internal_length
    omega
  have hcast : ((T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ : ℕ) : ℝ) =
      n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ := by
    dsimp [n]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hKT := high_scale_KT_le_height hκ PT hPT hm i
  have hexp : Real.log (n k) + Real.log 8 +
      2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤
      ((T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ : ℕ) : ℝ) * Real.log 2 := by
    rw [hcast]
    have hHH : ((PT.tiling.P i).h : ℝ) * Real.log 2 ≤ n k ^ (0.1 : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog2one (Nat.cast_nonneg _)).trans (by simpa using hH)
    have hLL : ((PT.tiling.P i).ℓ : ℝ) * Real.log 2 ≤ n k ^ (0.1 : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog2one (Nat.cast_nonneg _)).trans (by simpa using hEll)
    nlinarith [mul_pos hn0 hlog2]
  have hprod : n k * 8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) ≤
      (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) := by
    have h := Real.exp_le_exp.mpr hexp
    simpa [Real.exp_add, Real.exp_log hn0, Real.exp_log (by norm_num : (0 : ℝ) < 8),
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  rw [patchSlices_card PT hPT i, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (0 : ℝ) < 2 ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) := by positivity
  calc
    _ = ((T.S.n k : ℝ) * 8 * Real.exp
        (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)) /
      (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).h - (PT.tiling.P i).ℓ) := by ring
    _ ≤ 1 := (div_le_iff₀ hpow).2 (by simpa [n] using hprod)

theorem finLaw_pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · simp [ha, h ω ha]
  · by_cases hb : B ω <;> simp [ha, hb, P.nonneg ω]

theorem historyLoad_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (P : FinLaw (ClusterHistory PT hPT hm))
    (hcompare : ∀ F : ClusterHistory PT hPT hm → ℝ, (∀ W, 0 ≤ F W) →
      ∀ U : Finset (ClusterConsultation PT),
      ClusterHistoryDependsOn F (clusterConsultationScope PT hPT hm U) →
      (U.card : ℝ) ≤ (T.S.n k : ℝ) ^ 5 →
        P.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterHistoryLaw PT hPT hm).E F)
    (hn : 1 ≤ T.S.n k)
    (hsmall : ∀ i, (T.S.n k : ℝ) * (Fintype.card (PatchSlices PT i) : ℝ)⁻¹ *
      (8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)) ≤ 1)
    (hratio : 800 * 384 * (2 : ℝ) ^ (T.S.n k) / T.S.N k ≤ κ.θstar)
    (hN : (T.S.N k : ℝ) ^ 2 ≤ (8 : ℝ) ^ (T.S.n k))
    (htail : (1 / 2 : ℝ) ^ (T.S.n k) ≤ 1 / 100) :
    (99 / 100 : ℝ) ≤ P.pr (clusterHistoryLoad PT hPT hm) := by
  classical
  let n := T.S.n k
  let c : ℝ := 800 * (2 : ℝ) ^ n / T.S.N k
  let stats : (Fin PT.tiling.m × Fin (T.S.N k)) → ClusterHistory PT hPT hm → ℝ :=
    fun ix W => (Fintype.card (PatchGroups PT ix.1) : ℝ)⁻¹ *
      ∑ a : PatchGroups PT ix.1, (PT.tiling.P ix.1).M *
        groupMarginal PT hPT hm ix.1 a W ix.2
  have hstats : ∀ ix W, 0 ≤ stats ix W := by
    intro ix W
    dsimp [stats]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (Nat.cast_nonneg _) (groupMarginal_nonneg PT hPT hm ix.1 a W ix.2)
  have hc : 0 < c := by
    dsimp [c]
    have hNp : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    positivity
  have hbad : ∀ W, ¬ clusterHistoryLoad PT hPT hm W →
      (384 : ℝ) ^ n ≤ ∑ ix : Fin PT.tiling.m × Fin (T.S.N k), (stats ix W) ^ n := by
    intro W hW
    have hex : ∃ ix, 384 ≤ stats ix W := by
      by_contra h
      have hall : ∀ ix, stats ix W < 384 := by simpa using h
      apply hW
      apply historyLoad_of_patchColumns PT hPT hm W _ hκ.bucket.2.2.2.2
      intro i y
      calc
        patchColumn PT hPT hm i W y ≤ c * stats (i, y) W :=
          patchColumn_average_conversion PT hPT hm i W y
        _ < c * 384 := mul_lt_mul_of_pos_left (hall (i, y)) hc
        _ ≤ κ.θstar := by
          dsimp [c, n]
          convert hratio using 1 <;> ring
    obtain ⟨ix, hix⟩ := hex
    calc
      (384 : ℝ) ^ n ≤ (stats ix W) ^ n :=
        pow_le_pow_left₀ (by norm_num) hix n
      _ ≤ ∑ ix : Fin PT.tiling.m × Fin (T.S.N k), (stats ix W) ^ n :=
        Finset.single_le_sum (fun ix _ => pow_nonneg (hstats ix W) n)
          (Finset.mem_univ ix)
  have hmoment : P.E (fun W => ∑ ix : Fin PT.tiling.m × Fin (T.S.N k),
      (stats ix W) ^ n) ≤ (T.S.N k : ℝ) ^ 2 * (24 : ℝ) ^ n := by
    have heq : P.E (fun W => ∑ ix : Fin PT.tiling.m × Fin (T.S.N k),
        (stats ix W) ^ n) = ∑ ix : Fin PT.tiling.m × Fin (T.S.N k),
        P.E (fun W => (stats ix W) ^ n) := by
      simp only [FinLaw.E, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [heq]
    calc
      _ ≤ ∑ _ix : Fin PT.tiling.m × Fin (T.S.N k), (24 : ℝ) ^ n := by
        apply Finset.sum_le_sum
        intro ix _
        exact patchColumn_moment PT hPT hm ix.1 P hcompare hn (hsmall ix.1) ix.2
      _ = (PT.tiling.m : ℝ) * T.S.N k * (24 : ℝ) ^ n := by simp
      _ ≤ _ := by
        have hmN := Lane_q_s15_direct.tiling_patch_count_le PT hPT
        have h := mul_le_mul_of_nonneg_right (show (PT.tiling.m : ℝ) ≤ T.S.N k by
          exact_mod_cast hmN) (by positivity : (0 : ℝ) ≤ T.S.N k * 24 ^ n)
        nlinarith [h]
  let P' : FinProb (ClusterHistory PT hPT hm) := ⟨P.w, P.nonneg, P.sum_one⟩
  have hmark := FinProb.markov P' (fun W =>
    ∑ ix : Fin PT.tiling.m × Fin (T.S.N k), (stats ix W) ^ n) ((384 : ℝ) ^ n)
    (fun W => Finset.sum_nonneg fun ix _ => pow_nonneg (hstats ix W) n)
    (by positivity)
  have hfail : P.pr (fun W => ¬ clusterHistoryLoad PT hPT hm W) ≤ 1 / 100 := by
    calc
      _ ≤ P.pr (fun W => (384 : ℝ) ^ n ≤
          ∑ ix : Fin PT.tiling.m × Fin (T.S.N k), (stats ix W) ^ n) :=
        finLaw_pr_mono P hbad
      _ ≤ P.E (fun W => ∑ ix : Fin PT.tiling.m × Fin (T.S.N k),
          (stats ix W) ^ n) / (384 : ℝ) ^ n := hmark
      _ ≤ ((T.S.N k : ℝ) ^ 2 * (24 : ℝ) ^ n) / (384 : ℝ) ^ n := by gcongr
      _ ≤ ((8 : ℝ) ^ n * (24 : ℝ) ^ n) / (384 : ℝ) ^ n := by gcongr
      _ = (1 / 2 : ℝ) ^ n := by rw [← mul_pow, ← div_pow]; norm_num
      _ ≤ 1 / 100 := htail
  have hcompl : P.pr (clusterHistoryLoad PT hPT hm) +
      P.pr (fun W => ¬ clusterHistoryLoad PT hPT hm W) = 1 := by
    unfold FinLaw.pr
    rw [← Finset.sum_add_distrib]
    convert P.sum_one using 1
    apply Finset.sum_congr rfl
    intro W _
    by_cases h : clusterHistoryLoad PT hPT hm W <;> simp [h]
  linarith

theorem clusterSigma_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ clusterSigma PT hPT hm W I a x :=
  (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_nonneg _ _ _ x

theorem historyOnSlice_weight_pos {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (s : ClusterSlice PT) :
    0 < ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).w (historyOnSlice W s) := by
  classical
  have heq : (clusterHistoryLaw PT hPT hm).w W =
      ∏ s : ClusterSlice PT,
        ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).w (historyOnSlice W s) := by
    simp [clusterHistoryLaw, FinLaw.pi, SliceSolver.recLaw, recordLaw,
      historyOnSlice, Fintype.prod_sigma]
  have hp : (∏ s : ClusterSlice PT,
      ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).w (historyOnSlice W s)) ≠ 0 := by
    rw [← heq]
    exact hW.ne'
  have hs := Finset.prod_ne_zero_iff.mp hp s (Finset.mem_univ _)
  exact lt_of_le_of_ne (((clusterSolver PT hPT hm s.1).recLaw PT.parameter).nonneg _)
    (Ne.symm hs)

theorem clusterSigma_support_envelope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (I : ClusterInternalData PT) (a : EvenPosition T k) (x : Fin (T.S.N k))
    (hx : clusterSigma PT hPT hm W I a x ≠ 0) :
    x ∈ PT.envelope (patchAt PT hPT a.1) := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  have hrow : S.σ v (historyOnSlice W s) (nbrLabels v.1 (I s).2) ≠ 0 := by
    intro hzero
    apply hx
    exact congrFun hzero x
  obtain ⟨v', hv', hsupport⟩ := S.σ_support v (historyOnSlice W s)
    (nbrLabels v.1 (I s).2) hrow
  have hactive : v' ∈ PT.activeVertices := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hv' PT.parameter (historyOnSlice_weight_pos PT hPT hm W hW s)⟩
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨v', hactive, (hsupport x hx).1⟩

theorem clusterSigma_cap {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    clusterSigma PT hPT hm W I a x ≤
      (2 : ℝ) ^ (PT.tiling.P (patchAt PT hPT a.1)).h *
        Real.exp (-500 * PT.tiling.gain (patchAt PT hPT a.1)) / T.S.N k := by
  have h := (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_cap
    (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
    (nbrLabels (clusterCenterRole PT hPT hm a).1 (I (clusterSliceAt PT hPT a.1)).2) x
  apply (le_div_iff₀ (by exact_mod_cast T.S.N_pos k)).2
  rw [mul_comm]
  exact h

theorem clusterSigma_prob {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (h : clusterSigma PT hPT hm W I a ≠ 0) :
    ∑ x, clusterSigma PT hPT hm W I a x = 1 :=
  (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_prob _ _ _ h

theorem clusterSigma_zero_probability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : clusterAlarmsAvoided PT hPT hm W)
    (a : EvenPosition T k) :
    (clusterInternalKernel PT hPT hm W).pr (fun I => clusterSigma PT hPT hm W I a = 0) ≤
      sliceEps κ (PT.tiling.P (patchAt PT hPT a.1)).h := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm (patchAt PT hPT a.1)
  let v := clusterCenterRole PT hPT hm a
  have hgood : S.Hgood v (historyOnSlice W s) := by
    exact not_not.mp (hW a).2.2
  have hproject : (clusterInternalKernel PT hPT hm W).pr
      (fun I => clusterSigma PT hPT hm W I a = 0) =
      (S.refLaw (historyOnSlice W s)).pr
        (fun ω => S.σ v (historyOnSlice W s) (nbrLabels v.1 ω.2) = 0) := by
    exact pi_pr_coordinate
      (fun s : ClusterSlice PT => (clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s))
      s (fun ω => S.σ v (historyOnSlice W s) (nbrLabels v.1 ω.2) = 0)
  rw [hproject]
  exact S.Hgood_zero v (historyOnSlice W s) hgood

/-- The uniform gate-loss estimates transfer to every charged internal row using its atom cap. -/
theorem clusterSigma_removed_mass_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (havoid : clusterAlarmsAvoided PT hPT hm W) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (δ : ℝ)
    (hcross : (∑ x, if clusterJ0 PT hPT hm W a x ∧
      ∃ b ∈ clusterCrossingNeighbours PT hPT a,
        |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k then
      (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
        (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x else 0) ≤ δ) :
    (∑ x, if clusterJ PT hPT hm W a x then 0 else clusterSigma PT hPT hm W I a x) ≤
      ((PT.tiling.P (patchAt PT hPT a.1)).M *
        ((2 : ℝ) ^ (PT.tiling.P (patchAt PT hPT a.1)).h *
          Real.exp (-500 * PT.tiling.gain (patchAt PT hPT a.1)) / T.S.N k)) *
      (Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) + δ) := by
  classical
  let i := patchAt PT hPT a.1
  let μ := Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
  let B : ℝ := (PT.tiling.P i).M * ((2 : ℝ) ^ (PT.tiling.P i).h *
    Real.exp (-500 * PT.tiling.gain i) / T.S.N k)
  let C : Fin (T.S.N k) → Prop := fun x =>
    ∃ b ∈ clusterCrossingNeighbours PT hPT a,
      |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k
  have hJ (x : Fin (T.S.N k)) : clusterJ PT hPT hm W a x ↔
      clusterJ0 PT hPT hm W a x ∧ ¬ C x := by
    constructor
    · rintro ⟨hj0, hj⟩
      refine ⟨hj0, ?_⟩
      rintro ⟨b, hb, hbad⟩
      exact not_lt_of_ge (hj b hb) hbad
    · rintro ⟨hj0, hn⟩
      refine ⟨hj0, ?_⟩
      intro b hb
      by_contra hbad
      exact hn ⟨b, hb, lt_of_not_ge hbad⟩
  have hsplit : (∑ x, if clusterJ PT hPT hm W a x then 0 else μ.w x) =
      (∑ x, if clusterJ0 PT hPT hm W a x then 0 else μ.w x) +
      ∑ x, if clusterJ0 PT hPT hm W a x ∧ C x then μ.w x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hj0 : clusterJ0 PT hPT hm W a x <;> by_cases hc : C x <;>
      simp [hJ, hj0, hc]
  have halarm : (∑ x, if clusterJ0 PT hPT hm W a x then 0 else μ.w x) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) := le_of_not_gt (havoid a).1
  have hremoved : (∑ x, if clusterJ PT hPT hm W a x then 0 else μ.w x) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) + δ := by
    rw [hsplit]
    exact add_le_add halarm hcross
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (x : Fin (T.S.N k)) : clusterSigma PT hPT hm W I a x ≤ B * μ.w x := by
    by_cases hx : x ∈ (PT.tiling.P i).X
    · have hμ : μ.w x = ((PT.tiling.P i).M : ℝ)⁻¹ := by
        simp [μ, Law.unifCore, hx, (PT.tiling.P i).cardX]
      rw [hμ]
      have hcap := clusterSigma_cap PT hPT hm W I a x
      convert hcap using 1
      dsimp [B]
      field_simp [hM.ne']
      rfl
    · have hzero : clusterSigma PT hPT hm W I a x = 0 := by
        by_contra h
        exact hx (hPT.envelope_subset i (clusterSigma_support_envelope PT hPT hm W hW I a x h))
      rw [hzero]
      exact mul_nonneg hB (μ.nonneg x)
  calc
    _ ≤ B * ∑ x, if clusterJ PT hPT hm W a x then 0 else μ.w x := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      by_cases hj : clusterJ PT hPT hm W a x
      · simp [hj]
      · simpa [hj] using hpoint x
    _ ≤ B * (Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) + δ) :=
      mul_le_mul_of_nonneg_left hremoved hB

theorem positiveTerm_nonneg {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Law N) (I : Finset (Fin u)) (xs : Fin u → Fin N) :
    0 ≤ posTerm E c (fun l => (π l).w) I xs := by
  unfold posTerm
  apply Finset.prod_nonneg
  intro l _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg ((π l).nonneg y)
  apply Finset.prod_nonneg
  intro j _
  dsimp only [acoef]
  split_ifs with hd
  · have hh : 0 ≤ hit E c (xs j) y := by unfold hit; split_ifs <;> norm_num
    have h := div_nonneg hh hd.le
    linarith
  · norm_num

theorem phi_abs_le_positive_envelope {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin d → Law N)
    (xs : Fin u → Fin N) :
    |Phi E c (fun l => (π l).w) xs| ≤
      ∑ I : Finset (Fin u), posTerm E c (fun l => (π l).w) I xs := by
  unfold Phi
  calc
    _ ≤ ∑ I : Finset (Fin u),
        |(-1 : ℝ) ^ (u - I.card) * posTerm E c (fun l => (π l).w) I xs| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      simp [abs_mul, abs_pow, abs_of_nonneg (positiveTerm_nonneg E c π I xs)]

/-- Even-power Markov with the moderate moment and the positive envelope left explicit.
This isolates the final bulk step of the conditional mass argument. -/
theorem heterogeneous_lower_tail_of_moment {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (τ : Law N) (π : Fin d → Law N)
    (hu : Even u) (t B C : ℝ)
    (hmoderate : |∑ xs : Fin u → Fin N,
      if Moderate E c (fun l => (π l).w) t xs then
        prodW τ.w xs * Phi E c (fun l => (π l).w) xs else 0| ≤ B)
    (hlarge : (∑ xs : Fin u → Fin N,
      if ¬ Moderate E c (fun l => (π l).w) t xs then
        prodW τ.w xs * ∑ I : Finset (Fin u),
          posTerm E c (fun l => (π l).w) I xs else 0) ≤ C) :
    (FinLaw.pi (fun l => lawToFinLaw (π l))).pr
      (fun ys => Zmass E c τ.w (fun l => (π l).w) ys < 1 / 2) ≤
        (2 : ℝ) ^ u * (B + C) := by
  classical
  let P : FinLaw (Fin d → Fin N) := FinLaw.pi (fun l => lawToFinLaw (π l))
  let F : (Fin u → Fin N) → ℝ := fun xs =>
    prodW τ.w xs * Phi E c (fun l => (π l).w) xs
  have hidentity : P.E (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) =
      ∑ xs : Fin u → Fin N, F xs := by
    exact centered_moment_identity τ.w τ.sum_eq_one (fun l => (π l).w)
      (fun l => (π l).sum_eq_one) (fun l x y => 1 + acoef E c (π l).w x y)
  have hsplit : (∑ xs : Fin u → Fin N, F xs) =
      (∑ xs : Fin u → Fin N,
        if Moderate E c (fun l => (π l).w) t xs then F xs else 0) +
      (∑ xs : Fin u → Fin N,
        if ¬ Moderate E c (fun l => (π l).w) t xs then F xs else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro xs _
    by_cases h : Moderate E c (fun l => (π l).w) t xs <;> simp [h]
  have hsmall : (∑ xs : Fin u → Fin N,
      if Moderate E c (fun l => (π l).w) t xs then F xs else 0) ≤ B :=
    (le_abs_self _).trans hmoderate
  have hbig : (∑ xs : Fin u → Fin N,
      if ¬ Moderate E c (fun l => (π l).w) t xs then F xs else 0) ≤ C := by
    apply le_trans _ hlarge
    apply Finset.sum_le_sum
    intro xs _
    by_cases h : Moderate E c (fun l => (π l).w) t xs
    · simp [h]
    · simp only [h, not_false_eq_true, if_true]
      have hw : 0 ≤ prodW τ.w xs := Finset.prod_nonneg fun j _ => τ.nonneg (xs j)
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (phi_abs_le_positive_envelope E c π xs)) hw
  have hmoment : P.E (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) ≤ B + C := by
    rw [hidentity, hsplit]
    exact add_le_add hsmall hbig
  have hbad (ys : Fin d → Fin N)
      (hy : Zmass E c τ.w (fun l => (π l).w) ys < 1 / 2) :
      (1 / 2 : ℝ) ^ u ≤ (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u := by
    have habs : (1 / 2 : ℝ) ≤ |Zmass E c τ.w (fun l => (π l).w) ys - 1| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have h := pow_le_pow_left₀ (by norm_num) habs u
    rw [hu.pow_abs] at h
    exact h
  let P' : FinProb (Fin d → Fin N) := ⟨P.w, P.nonneg, P.sum_one⟩
  have hmark := FinProb.markov P'
    (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) ((1 / 2 : ℝ) ^ u)
    (fun ys => hu.pow_nonneg _) (by positivity)
  calc
    _ ≤ P.pr (fun ys => (1 / 2 : ℝ) ^ u ≤
        (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) := finLaw_pr_mono P hbad
    _ ≤ P.E (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) /
        (1 / 2 : ℝ) ^ u := hmark
    _ ≤ (B + C) / (1 / 2 : ℝ) ^ u := by gcongr
    _ = (2 : ℝ) ^ u * (B + C) := by rw [div_eq_mul_inv, ← inv_pow]; norm_num; ring

/-- One crossing ratio preserves mass on a second-side degree success and increases the
normalized atom cap by at most a factor five. -/
theorem ratio_filter_mass_window {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ π : Law N) (b : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ x, 0 < τ.w x → |deg E c π.w x - 1 / 2| ≤ 2 * b)
    (y : Fin N) (hy : |colDeg E c τ y - 1 / 2| ≤ b) :
    let m := ∑ x, τ.w x * normalizedHit E c π x y
    |m - 1| ≤ 20 * b ∧ 0 < m ∧
      ∀ x, τ.w x * normalizedHit E c π x y / m ≤ 5 * τ.w x := by
  classical
  let lo : ℝ := 1 / 2 - 2 * b
  let hi : ℝ := 1 / 2 + 2 * b
  let m : ℝ := ∑ x, τ.w x * normalizedHit E c π x y
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hhi : 0 < hi := by dsimp [hi]; linarith
  have hhit (x : Fin N) : 0 ≤ hit E c x y ∧ hit E c x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  have hpoint (x : Fin N) :
      τ.w x * hit E c x y / hi ≤ τ.w x * normalizedHit E c π x y ∧
      τ.w x * normalizedHit E c π x y ≤ τ.w x * hit E c x y / lo := by
    by_cases hx : τ.w x = 0
    · simp [hx]
    have hxpos : 0 < τ.w x := lt_of_le_of_ne (τ.nonneg x) (Ne.symm hx)
    have hd := abs_le.mp (hdeg x hxpos)
    have hdlo : lo ≤ deg E c π.w x := by dsimp [lo]; linarith
    have hdhi : deg E c π.w x ≤ hi := by dsimp [hi]; linarith
    have hdpos := hlo.trans_le hdlo
    simp only [normalizedHit, if_pos hdpos]
    rw [← mul_div_assoc]
    constructor
    · exact div_le_div_of_nonneg_left (mul_nonneg (τ.nonneg x) (hhit x).1) hdpos hdhi
    · exact div_le_div_of_nonneg_left (mul_nonneg (τ.nonneg x) (hhit x).1) hlo hdlo
  have hcol : (∑ x, τ.w x * hit E c x y) = colDeg E c τ y := by
    simp [colDeg, hit]
  have hmlo : colDeg E c τ y / hi ≤ m := by
    rw [← hcol, Finset.sum_div]
    exact Finset.sum_le_sum fun x _ => (hpoint x).1
  have hmhi : m ≤ colDeg E c τ y / lo := by
    rw [← hcol, Finset.sum_div]
    exact Finset.sum_le_sum fun x _ => (hpoint x).2
  have hc := abs_le.mp hy
  have hlow : 1 - 20 * b ≤ m := by
    have h : (1 - 20 * b) * hi ≤ colDeg E c τ y := by
      dsimp [hi]
      nlinarith [sq_nonneg b]
    exact ((le_div_iff₀ hhi).2 h).trans hmlo
  have hupp : m ≤ 1 + 20 * b := by
    have hs := mul_le_mul_of_nonneg_right hbsmall hb
    have h : colDeg E c τ y ≤ (1 + 20 * b) * lo := by
      dsimp [lo]
      nlinarith [hs]
    exact hmhi.trans ((div_le_iff₀ hlo).2 h)
  have hm08 : (4 / 5 : ℝ) ≤ m := by linarith
  have hmpos : 0 < m := by linarith
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hmpos, ?_⟩
  intro x
  by_cases hx : τ.w x = 0
  · simp [hx]
  have hxpos : 0 < τ.w x := lt_of_le_of_ne (τ.nonneg x) (Ne.symm hx)
  have hd := abs_le.mp (hdeg x hxpos)
  have hd48 : (12 / 25 : ℝ) ≤ deg E c π.w x := by linarith
  have hdpos : 0 < deg E c π.w x := by linarith
  have hdm : (1 : ℝ) ≤ 5 * (deg E c π.w x * m) := by
    have h := mul_le_mul hd48 hm08 (by norm_num : (0 : ℝ) ≤ 4 / 5) hdpos.le
    nlinarith [h]
  simp only [normalizedHit, if_pos hdpos]
  rw [← mul_div_assoc, div_div]
  apply (div_le_iff₀ (mul_pos hdpos hmpos)).2
  have hfirst : τ.w x * hit E c x y ≤ τ.w x := by
    simpa using mul_le_mul_of_nonneg_left (hhit x).2 (τ.nonneg x)
  have hsecond := mul_le_mul_of_nonneg_left hdm (τ.nonneg x)
  nlinarith [hfirst, hsecond]

theorem crossing_ratio_bad_probability {T : Stage} {k : ℕ} {wS wL w : ℝ}
    (hD : TwoBudgetDisc T k wS wL (bstar T k)) (c : Colour)
    (τ π : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE wS)
    (hπ : π.SupportedIn (T.Y k)) (hπw : π.WidthLE w)
    (hb : 0 ≤ bstar T k) (hbsmall : bstar T k ≤ 1 / 100)
    (hdeg : ∀ x, 0 < τ.w x → |deg (T.S.E k) c π.w x - 1 / 2| ≤ 2 * bstar T k) :
    π.pr (fun y => |(∑ x, τ.w x * normalizedHit (T.S.E k) c π x y) - 1| >
      20 * bstar T k) ≤ 2 * Real.exp (w - wL) := by
  classical
  have hbound := exceptional_second hD c (Or.inl ⟨le_rfl, le_rfl⟩) τ π hτ hτw hπ hπw
  have hsub (y : Fin (T.S.N k))
      (hy : |(∑ x, τ.w x * normalizedHit (T.S.E k) c π x y) - 1| > 20 * bstar T k) :
      bstar T k < |colDeg (T.S.E k) c τ y - 1 / 2| := by
    by_contra h
    have hgood := ratio_filter_mass_window (T.S.E k) c τ π (bstar T k) hb hbsmall hdeg y
      (le_of_not_gt h)
    exact not_lt_of_ge hgood.1 hy
  have hmono : π.pr (fun y => |(∑ x, τ.w x * normalizedHit (T.S.E k) c π x y) - 1| >
      20 * bstar T k) ≤ π.pr (fun y => bstar T k < |colDeg (T.S.E k) c τ y - 1 / 2|) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : |(∑ x, τ.w x * normalizedHit (T.S.E k) c π x y) - 1| > 20 * bstar T k
    · rw [if_pos hy, if_pos (hsub y hy)]
    · by_cases hc : bstar T k < |colDeg (T.S.E k) c τ y - 1 / 2|
      · rw [if_neg hy, if_pos hc]
        exact π.nonneg y
      · rw [if_neg hy, if_neg hc]
  apply hmono.trans
  simpa [FinProb.pr, Finset.sum_filter] using hbound

noncomputable def ratioFilter {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ π : Law N) (y : Fin N) : Law N := by
  classical
  let m := ∑ x, τ.w x * normalizedHit E c π x y
  by_cases hm : 0 < m
  · exact {
      w := fun x => τ.w x * normalizedHit E c π x y / m
      nonneg := by
        intro x
        apply div_nonneg _ hm.le
        apply mul_nonneg (τ.nonneg x)
        dsimp only [normalizedHit]
        split_ifs with hd
        · apply div_nonneg _ hd.le
          unfold hit
          split_ifs <;> norm_num
        · exact le_rfl
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self hm.ne' }
  · exact τ

theorem ratioFilter_weight_of_pos {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ π : Law N) (y : Fin N)
    (hm : 0 < ∑ x, τ.w x * normalizedHit E c π x y) (x : Fin N) :
    (ratioFilter E c τ π y).w x = τ.w x * normalizedHit E c π x y /
      (∑ x, τ.w x * normalizedHit E c π x y) := by
  simp [ratioFilter, hm]

noncomputable def crossingState {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) : (m : ℕ) → (Fin m → Fin N) → Law N
  | 0, _ => τ
  | m + 1, ys => ratioFilter E c (crossingState E c τ π m (Fin.init ys))
      (π m) (ys (Fin.last m))

def crossingGood {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (b : ℝ) : (m : ℕ) → (Fin m → Fin N) → Prop
  | 0, _ => True
  | m + 1, ys => crossingGood E c τ π b m (Fin.init ys) ∧
      |colDeg E c (crossingState E c τ π m (Fin.init ys)) (ys (Fin.last m)) - 1 / 2| ≤ b

theorem crossingState_domination {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (b : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ j x, 0 < τ.w x → |deg E c (π j).w x - 1 / 2| ≤ 2 * b) :
    ∀ m (ys : Fin m → Fin N), crossingGood E c τ π b m ys →
      ∀ x, (crossingState E c τ π m ys).w x ≤ (5 : ℝ) ^ m * τ.w x := by
  intro m
  induction m with
  | zero => intro ys _ x; simp [crossingState]
  | succ m ih =>
    intro ys hgood x
    have hprev := ih (Fin.init ys) hgood.1
    have hd : ∀ x, 0 < (crossingState E c τ π m (Fin.init ys)).w x →
        |deg E c (π m).w x - 1 / 2| ≤ 2 * b := by
      intro x hx
      apply hdeg m x
      by_contra h
      have hz : τ.w x = 0 := le_antisymm (le_of_not_gt h) (τ.nonneg x)
      have hh := hprev x
      rw [hz, mul_zero] at hh
      linarith
    have hwindow := ratio_filter_mass_window E c
      (crossingState E c τ π m (Fin.init ys)) (π m) b hb hbsmall hd
      (ys (Fin.last m)) hgood.2
    change (ratioFilter E c (crossingState E c τ π m (Fin.init ys))
      (π m) (ys (Fin.last m))).w x ≤ _
    rw [ratioFilter_weight_of_pos E c _ _ _ hwindow.2.1]
    calc
      _ ≤ 5 * (crossingState E c τ π m (Fin.init ys)).w x := hwindow.2.2 x
      _ ≤ 5 * ((5 : ℝ) ^ m * τ.w x) :=
        mul_le_mul_of_nonneg_left (hprev x) (by norm_num)
      _ = (5 : ℝ) ^ (m + 1) * τ.w x := by rw [pow_succ]; ring

theorem pi_snoc_E {N : ℕ} (π : ℕ → Law N) (m : ℕ)
    (F : (Fin (m + 1) → Fin N) → ℝ) :
    (FinLaw.pi (fun j : Fin (m + 1) => lawToFinLaw (π j))).E F =
      (FinLaw.pi (fun j : Fin m => lawToFinLaw (π j))).E
        (fun ys => (lawToFinLaw (π m)).E (fun y => F (Fin.snoc ys y))) := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (m + 1) => Fin N)
  unfold FinLaw.E
  simp only [FinLaw.pi, lawToFinLaw]
  rw [← Equiv.sum_comp e]
  rw [Fintype.sum_prod_type]
  change (∑ y, ∑ ys : Fin m → Fin N,
    (∏ j : Fin (m + 1), (π j).w ((Fin.snoc ys y) j)) * F (Fin.snoc ys y)) = _
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.coe_castSucc, Fin.val_last]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem finLaw_pr_eq_indicator {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A : Ω → Prop) : P.pr A = P.E (fun ω => if A ω then 1 else 0) := by
  classical
  simp only [FinLaw.pr, FinLaw.E, mul_ite, mul_one, mul_zero]

theorem crossing_failure_probability {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (b γ : ℝ) (hγ : 0 ≤ γ) (ell : ℕ)
    (hstep : ∀ m < ell, ∀ ys : Fin m → Fin N, crossingGood E c τ π b m ys →
      (π m).pr (fun y => b < |colDeg E c (crossingState E c τ π m ys) y - 1 / 2|) ≤ γ) :
    (FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))).pr
      (fun ys => ¬ crossingGood E c τ π b ell ys) ≤ (ell : ℝ) * γ := by
  classical
  have aux : ∀ m ≤ ell,
      (FinLaw.pi (fun j : Fin m => lawToFinLaw (π j))).pr
        (fun ys => ¬ crossingGood E c τ π b m ys) ≤ (m : ℝ) * γ := by
    intro m
    induction m with
    | zero => intro _; simp [crossingGood, FinLaw.pr]
    | succ m ih =>
      intro hm
      let P := FinLaw.pi (fun j : Fin m => lawToFinLaw (π j))
      have hpoint (ys : Fin m → Fin N) :
          (lawToFinLaw (π m)).E (fun y =>
            if ¬ crossingGood E c τ π b (m + 1) (Fin.snoc ys y) then 1 else 0) ≤
          (if ¬ crossingGood E c τ π b m ys then 1 else 0) + γ := by
        by_cases hy : crossingGood E c τ π b m ys
        · have hpr : (lawToFinLaw (π m)).E (fun y =>
              if ¬ crossingGood E c τ π b (m + 1) (Fin.snoc ys y) then 1 else 0) =
              (π m).pr (fun y => b < |colDeg E c (crossingState E c τ π m ys) y - 1 / 2|) := by
            simp only [crossingGood, Fin.init_snoc, Fin.snoc_last, hy, true_and,
              not_le, FinLaw.E, lawToFinLaw, FinProb.pr, mul_ite, mul_one, mul_zero]
          rw [hpr, if_neg (not_not.mpr hy), zero_add]
          exact hstep m (by omega) ys hy
        · have hpr : (lawToFinLaw (π m)).E (fun y =>
              if ¬ crossingGood E c τ π b (m + 1) (Fin.snoc ys y) then 1 else 0) = 1 := by
            simp only [crossingGood, Fin.init_snoc, Fin.snoc_last, hy, false_and,
              not_false_eq_true, ite_true, FinLaw.E, lawToFinLaw, mul_one]
            exact (π m).sum_eq_one
          rw [hpr, if_pos hy]
          linarith
      calc
        _ = P.E (fun ys => (lawToFinLaw (π m)).E (fun y =>
            if ¬ crossingGood E c τ π b (m + 1) (Fin.snoc ys y) then 1 else 0)) := by
          rw [finLaw_pr_eq_indicator, pi_snoc_E]
          congr 1
          funext ys
          congr 1
          funext y
          by_cases h : crossingGood E c τ π b (m + 1) (Fin.snoc ys y) <;> simp [h]
        _ ≤ P.E (fun ys => (if ¬ crossingGood E c τ π b m ys then 1 else 0) + γ) := by
          unfold FinLaw.E
          apply Finset.sum_le_sum
          intro ys _
          exact mul_le_mul_of_nonneg_left (hpoint ys) (P.nonneg ys)
        _ = P.pr (fun ys => ¬ crossingGood E c τ π b m ys) + γ := by
          rw [finLaw_pr_eq_indicator]
          simp only [FinLaw.E, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
            P.sum_one, one_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro ys _
          by_cases h : crossingGood E c τ π b m ys <;> simp [h]
        _ ≤ (m : ℝ) * γ + γ := by
          have h := ih (by omega)
          change (P.pr (fun ys => ¬ crossingGood E c τ π b m ys)) ≤ (m : ℝ) * γ at h
          linarith
        _ = ((m + 1 : ℕ) : ℝ) * γ := by push_cast; ring
  exact aux ell le_rfl

noncomputable def crossingNumerator {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (m : ℕ) (ys : Fin m → Fin N) (x : Fin N) : ℝ :=
  τ.w x * ∏ j : Fin m, normalizedHit E c (π j) x (ys j)

noncomputable def crossingProductMass {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (m : ℕ) (ys : Fin m → Fin N) : ℝ :=
  ∑ x, crossingNumerator E c τ π m ys x

theorem crossingState_mass {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (τ : Law N) (π : ℕ → Law N) (b : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ j x, 0 < τ.w x → |deg E c (π j).w x - 1 / 2| ≤ 2 * b) :
    ∀ m (ys : Fin m → Fin N), crossingGood E c τ π b m ys →
      0 < crossingProductMass E c τ π m ys ∧
      (1 - 20 * b) ^ m ≤ crossingProductMass E c τ π m ys ∧
      ∀ x, (crossingState E c τ π m ys).w x * crossingProductMass E c τ π m ys =
        crossingNumerator E c τ π m ys x := by
  classical
  intro m
  induction m with
  | zero =>
    intro ys _
    simp [crossingProductMass, crossingNumerator, crossingState, τ.sum_eq_one]
  | succ m ih =>
    intro ys hgood
    let z := Fin.init ys
    let S := crossingState E c τ π m z
    let M := crossingProductMass E c τ π m z
    let r := ∑ x, S.w x * normalizedHit E c (π m) x (ys (Fin.last m))
    have hprev := ih z hgood.1
    have hdom := crossingState_domination E c τ π b hb hbsmall hdeg m z hgood.1
    have hd : ∀ x, 0 < S.w x → |deg E c (π m).w x - 1 / 2| ≤ 2 * b := by
      intro x hx
      apply hdeg m x
      by_contra h
      have hz : τ.w x = 0 := le_antisymm (le_of_not_gt h) (τ.nonneg x)
      have hh := hdom x
      rw [hz, mul_zero] at hh
      linarith
    have hwindow := ratio_filter_mass_window E c S (π m) b hb hbsmall hd
      (ys (Fin.last m)) hgood.2
    have hr : 0 < r := hwindow.2.1
    have hrlo : 1 - 20 * b ≤ r := by
      have h := abs_le.mp hwindow.1
      change -(20 * b) ≤ r - 1 ∧ r - 1 ≤ 20 * b at h
      linarith
    have hnum (x : Fin N) : crossingNumerator E c τ π (m + 1) ys x =
        crossingNumerator E c τ π m z x * normalizedHit E c (π m) x (ys (Fin.last m)) := by
      simp only [crossingNumerator, Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      dsimp only [z, Fin.init]
      ring
    have hmass : crossingProductMass E c τ π (m + 1) ys = M * r := by
      unfold crossingProductMass
      simp_rw [hnum, ← hprev.2.2]
      dsimp [M, r, S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hmass]
      exact mul_pos hprev.1 hr
    · rw [hmass, pow_succ]
      exact mul_le_mul hprev.2.1 hrlo (by linarith : 0 ≤ 1 - 20 * b) hprev.1.le
    · intro x
      change (ratioFilter E c S (π m) (ys (Fin.last m))).w x * _ = _
      rw [ratioFilter_weight_of_pos E c S (π m) (ys (Fin.last m)) hr, hmass, hnum]
      change S.w x * normalizedHit E c (π m) x (ys (Fin.last m)) / r * (M * r) = _
      calc
        _ = (S.w x * M) * normalizedHit E c (π m) x (ys (Fin.last m)) := by
          field_simp [hr.ne']
        _ = _ := by rw [hprev.2.2]

theorem finLaw_ext_weight {α : Type*} [Fintype α] {P Q : FinLaw α}
    (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Independent slice outcomes remain a product after distinct slices are projected separately. -/
theorem pi_map_injective {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    {A : J → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (P : ∀ i, FinLaw (Ω i)) (t : J → ι) (ht : Function.Injective t)
    (f : ∀ j, Ω (t j) → A j) :
    FinLaw.map (FinLaw.pi P) (fun ω j => f j (ω (t j))) =
      FinLaw.pi (fun j => FinLaw.map (P (t j)) (f j)) := by
  classical
  apply finLaw_ext_weight
  funext a
  have hind (ω : ∀ i, Ω i) :
      (if (fun j => f j (ω (t j))) = a then (1 : ℝ) else 0) =
        ∏ j, if f j (ω (t j)) = a j then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, f j (ω (t j)) = a j
    · have he : (fun j => f j (ω (t j))) = a := funext h
      simp [he, h]
    · have he : (fun j => f j (ω (t j))) ≠ a := by
        intro he
        exact h (fun j => congrFun he j)
      rw [if_neg he]
      obtain ⟨j, hj⟩ := not_forall.mp h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [if_neg hj]
  have hcoordinate (j : J) : (P (t j)).E
      (fun x => if f j x = a j then (1 : ℝ) else 0) =
      (FinLaw.map (P (t j)) (f j)).w (a j) := by
    unfold FinLaw.E FinLaw.map
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : f j x = a j <;> simp [h]
  calc
    _ = (FinLaw.pi P).E (fun ω => ∏ j,
        if f j (ω (t j)) = a j then (1 : ℝ) else 0) := by
      unfold FinLaw.map FinLaw.E
      apply Finset.sum_congr rfl
      intro ω _
      dsimp only
      rw [← hind ω]
      by_cases h : (fun j => f j (ω (t j))) = a <;> simp [h]
    _ = ∏ j, (P (t j)).E (fun x => if f j x = a j then (1 : ℝ) else 0) :=
      pi_E_prod_injective P t ht (fun j x => if f j x = a j then (1 : ℝ) else 0)
    _ = _ := Finset.prod_congr rfl fun j _ => hcoordinate j

end HypercubeRamsey.Lane_sol_s15_load
