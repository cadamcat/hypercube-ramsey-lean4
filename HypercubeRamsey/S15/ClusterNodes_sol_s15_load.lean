import HypercubeRamsey.S15.ClusterNodes_q_s15_c1
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S15.Needs
import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer

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

theorem heterogeneous_lower_tail_three_quarters {N d u : ℕ}
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
      (fun ys => Zmass E c τ.w (fun l => (π l).w) ys < 3 / 4) ≤
        (4 : ℝ) ^ u * (B + C) := by
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
      (hy : Zmass E c τ.w (fun l => (π l).w) ys < 3 / 4) :
      (1 / 4 : ℝ) ^ u ≤ (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u := by
    have habs : (1 / 4 : ℝ) ≤ |Zmass E c τ.w (fun l => (π l).w) ys - 1| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have h := pow_le_pow_left₀ (by norm_num) habs u
    rw [hu.pow_abs] at h
    exact h
  let P' : FinProb (Fin d → Fin N) := ⟨P.w, P.nonneg, P.sum_one⟩
  have hmark := FinProb.markov P'
    (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) ((1 / 4 : ℝ) ^ u)
    (fun ys => hu.pow_nonneg _) (by positivity)
  calc
    _ ≤ P.pr (fun ys => (1 / 4 : ℝ) ^ u ≤
        (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) := finLaw_pr_mono P hbad
    _ ≤ P.E (fun ys => (Zmass E c τ.w (fun l => (π l).w) ys - 1) ^ u) /
        (1 / 4 : ℝ) ^ u := hmark
    _ ≤ (B + C) / (1 / 4 : ℝ) ^ u := by gcongr
    _ = (4 : ℝ) ^ u * (B + C) := by rw [div_eq_mul_inv, ← inv_pow]; norm_num; ring


noncomputable def clusterMarginalLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) : Law (T.S.N k) := {
  w := clusterMarginal PT hPT hm W b
  nonneg := by
    intro y
    unfold clusterMarginal SliceSolver.oddMarginal
    exact Finset.sum_nonneg fun D _ => mul_nonneg
      ((clusterSolver PT hPT hm _).q_nonneg _ _ D)
      ((clusterSolver PT hPT hm _).U_nonneg _ _ D y)
  sum_eq_one := by
    unfold clusterMarginal SliceSolver.oddMarginal
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (clusterSolver PT hPT hm _).U_sum, mul_one]
    exact (clusterSolver PT hPT hm _).q_sum _ _
}

theorem cluster_slice_label_map {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) :
    FinLaw.map ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).refLaw
      (historyOnSlice W (clusterSliceAt PT hPT b.1)))
      (fun ω => ω.2 (solverWordAt PT hPT hm b.1)) =
        lawToFinLaw (clusterMarginalLaw PT hPT hm W b) := by
  classical
  apply finLaw_ext_weight
  funext y
  have h := Lane_sol_s15_transfer.slice_ref_label_E
    (clusterSolver PT hPT hm (patchAt PT hPT b.1))
    (historyOnSlice W (clusterSliceAt PT hPT b.1))
    (solverWordAt PT hPT hm b.1) (fun z => if z = y then (1 : ℝ) else 0)
  have hmap : (FinLaw.map ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).refLaw
      (historyOnSlice W (clusterSliceAt PT hPT b.1)))
      (fun ω => ω.2 (solverWordAt PT hPT hm b.1))).w y =
    ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).refLaw
      (historyOnSlice W (clusterSliceAt PT hPT b.1))).E
      (fun ω => if ω.2 (solverWordAt PT hPT hm b.1) = y then 1 else 0) := by
    simp only [FinLaw.map, FinLaw.E]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  rw [hmap, h]
  simp [lawToFinLaw, clusterMarginalLaw, clusterMarginal, SliceSolver.oddMarginal,
    clusterSliceAt]
  rfl

theorem pi_E_center_labels {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    {A : J → Type*} [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (t : J → ι) (ht : Function.Injective t)
    (hi : ∀ j, t j ≠ i) (f : ∀ j, Ω (t j) → A j)
    (F : Ω i → (∀ j, A j) → ℝ) :
    (FinLaw.pi P).E (fun ω => F (ω i) (fun j => f j (ω (t j)))) =
      (P i).E (fun a => (FinLaw.pi (fun j => FinLaw.map (P (t j)) (f j))).E
        (F a)) := by
  classical
  let Q := FinLaw.pi P
  have hproj (a : Ω i) : Q.E (fun ω => F a (fun j => f j (ω (t j)))) =
      (FinLaw.pi (fun j => FinLaw.map (P (t j)) (f j))).E (F a) := by
    rw [← pi_map_injective P t ht f, finLaw_map_E]
    rfl
  have hexpand (ω : ∀ i, Ω i) : F (ω i) (fun j => f j (ω (t j))) =
      ∑ a, (if ω i = a then (1 : ℝ) else 0) * F a (fun j => f j (ω (t j))) := by
    simp
  change Q.E _ = _
  simp_rw [hexpand]
  unfold FinLaw.E
  dsimp only
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hfactor := pi_E_mul_of_disjoint P
    (fun ω => if ω i = a then (1 : ℝ) else 0)
    (fun ω => F a (fun j => f j (ω (t j)))) {i} (Finset.univ.image t)
    (by
      intro ω ω' h
      change (if ω i = a then (1 : ℝ) else 0) = (if ω' i = a then 1 else 0)
      rw [h i (by simp)])
    (by
      intro ω ω' h
      change F a (fun j => f j (ω (t j))) = F a (fun j => f j (ω' (t j)))
      apply congrArg (F a)
      funext j
      rw [h (t j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)])
    (by
      simp only [Finset.disjoint_singleton_left, Finset.mem_image]
      rintro ⟨j, _, hj⟩
      exact hi j hj)
  rw [pi_E_coordinate P i (fun x => if x = a then (1 : ℝ) else 0), hproj] at hfactor
  have heq : (P i).E (fun x => if x = a then (1 : ℝ) else 0) = (P i).w a := by
    simp [FinLaw.E, mul_ite]
  rw [heq] at hfactor
  simpa [FinLaw.E, Q, mul_assoc, Finset.mul_sum] using hfactor

private theorem adjacent_eq_flip {T : Stage} {k : ℕ}
    {a : EvenPosition T k} {b : OddPosition T k} (h : Adjacent a b) :
    ∃ j : Fin (T.S.n k), b.1 = flipPos a.1 j := by
  classical
  change hammingDist a.1 b.1 = 1 at h
  unfold hammingDist at h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hdiff : a.1 j ≠ b.1 j := by
    have hm : j ∈ Finset.univ.filter (fun q => a.1 q ≠ b.1 q) := by rw [hj]; simp
    exact (Finset.mem_filter.mp hm).2
  refine ⟨j, ?_⟩
  funext q
  by_cases hq : q = j
  · subst q
    cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [flipPos]
  · have heq : a.1 q = b.1 q := by
      by_contra hn
      have hm : q ∈ Finset.univ.filter (fun r => a.1 r ≠ b.1 r) := by simp [hn]
      rw [hj] at hm
      exact hq (by simpa using hm)
    simp [flipPos, hq, heq]

private def sliceBit {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (s : ClusterSlice PT) (q : Fin (T.S.n k)) : Bool :=
  if h : q.val < T.S.n k - (PT.tiling.P s.1).h then s.2.1 ⟨q.val, h⟩ else false

private theorem sliceBit_at {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v : Position T k)
    (q : Fin (T.S.n k)) (hq : q.val < T.S.n k - (PT.tiling.P (patchAt PT hPT v)).h) :
    sliceBit PT (clusterSliceAt PT hPT v) q = v q := by
  simp [sliceBit, clusterSliceAt, outsideWord, hq]

private theorem dependent_apply_heq {ι : Type*} {A : ι → Type*}
    (f : ∀ i, A i) {i j : ι} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

private theorem clusterSlice_eq_of_outside {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (s t : ClusterSlice PT)
    (h : s.1 = t.1) (hab : HEq s.2.1 t.2.1) : s = t := by
  rcases s with ⟨i, s⟩
  rcases t with ⟨j, t⟩
  dsimp only at h hab
  cases h
  apply congrArg (Sigma.mk i)
  exact Subtype.ext (eq_of_heq hab)

private theorem external_flip_outside {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (b : OddPosition T k)
    (hb : b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a)
    (q : Fin (T.S.n k)) (hflip : b.1 = flipPos a.1 q) :
    q.val < T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h := by
  classical
  rcases Finset.mem_union.mp hb with hb | hb
  · have hp := (Finset.mem_filter.mp hb).2.2.1
    have hs := (Finset.mem_filter.mp hb).2.2.2
    rw [hp]
    by_contra hnot
    apply hs
    have hout : outsideWord PT hPT (patchAt PT hPT a.1) b.1 =
        outsideWord PT hPT (patchAt PT hPT a.1) a.1 := by
      funext t
      let t' : Fin (T.S.n k) := ⟨t.val, by
        have := t.isLt
        have := Nat.sub_le (T.S.n k) (PT.tiling.P (patchAt PT hPT a.1)).h
        omega⟩
      have ht : t' ≠ q := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp [t'] at hv
        have := t.isLt
        omega
      change b.1 t' = a.1 t'
      rw [hflip]
      simp [flipPos, ht]
    have heq : HEq (outsideWord PT hPT (patchAt PT hPT b.1) b.1)
        (outsideWord PT hPT (patchAt PT hPT a.1) a.1) := by
      exact (dependent_apply_heq (fun i => outsideWord PT hPT i b.1) hp).trans
        (heq_of_eq hout)
    exact clusterSlice_eq_of_outside PT _ _ hp heq
  · have hp := (Finset.mem_filter.mp hb).2.2
    have hq : q.val < (PT.tiling.P (patchAt PT hPT a.1)).ℓ := by
      by_contra hnot
      have hleaf : b.1 ∈ PT.tiling.leaf (patchAt PT hPT a.1) := by
        intro t ht
        have hne : t ≠ q := by
          intro heq
          have := congrArg Fin.val heq
          omega
        simpa [hflip, flipPos, hne, patchAt] using
          (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1 t ht
      exact hp (Lane_q_s15_direct.patchAt_eq_of_leaf PT hPT _ b.1 hleaf)
    have hel := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ)
      (Finset.mem_univ (patchAt PT hPT a.1))
    have hh := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h)
      (Finset.mem_univ (patchAt PT hPT b.1))
    have hn := hPT.tiling_valid.prefix_internal_length
    omega

theorem clusterExternalSlices_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Function.Injective (fun b : {b : OddPosition T k //
      b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} =>
        clusterSliceAt PT hPT b.1.1) := by
  classical
  intro b b' hs
  have adjacent (d : {b : OddPosition T k //
      b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a}) :
      Adjacent a d.1 := by
    rcases Finset.mem_union.mp d.2 with hd | hd <;>
      exact (Finset.mem_filter.mp hd).2.1
  obtain ⟨q, hq⟩ := adjacent_eq_flip (adjacent b)
  obtain ⟨r, hr⟩ := adjacent_eq_flip (adjacent b')
  have hqo := external_flip_outside PT hPT a b.1 b.2 q hq
  have hro := external_flip_outside PT hPT a b'.1 b'.2 r hr
  have hp : patchAt PT hPT b.1.1 = patchAt PT hPT b'.1.1 := congrArg Sigma.fst hs
  have hqr : q = r := by
    by_contra hne
    have hqo' : q.val < T.S.n k - (PT.tiling.P (patchAt PT hPT b'.1.1)).h := by
      simpa [← hp] using hqo
    have hbit := congrArg (fun s => sliceBit PT s q) hs
    rw [sliceBit_at PT hPT b.1.1 q hqo, sliceBit_at PT hPT b'.1.1 q hqo', hq, hr] at hbit
    cases hv : a.1 q <;> simp [flipPos, hne, hv] at hbit
  apply Subtype.ext
  apply Subtype.ext
  rw [hq, hr, hqr]

theorem clusterExternalSlices_ne_center {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (b : OddPosition T k)
    (hb : b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a) :
    clusterSliceAt PT hPT b.1 ≠ clusterSliceAt PT hPT a.1 := by
  rcases Finset.mem_union.mp hb with hb | hb
  · exact (Finset.mem_filter.mp hb).2.2.2
  · intro heq
    exact (Finset.mem_filter.mp hb).2.2 (congrArg Sigma.fst heq)

theorem restrict_mass_lower {N : ℕ} (σ : Fin N → ℝ) (J : Fin N → Prop)
    (hσ : ∑ x, σ x = 1) (δ : ℝ)
    (hδ : (∑ x, if J x then 0 else σ x) ≤ δ) :
    1 - δ ≤ ∑ x, if J x then σ x else 0 := by
  classical
  have hsplit : (∑ x, if J x then σ x else 0) +
      (∑ x, if J x then 0 else σ x) = 1 := by
    rw [← Finset.sum_add_distrib, ← hσ]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : J x <;> simp [h]
  linarith

noncomputable def gatedLaw {N : ℕ} (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0) : Law N := by
  classical
  exact {
    w := fun x => (if J x then σ.w x else 0) / (∑ z, if J z then σ.w z else 0)
    nonneg := by
      intro x
      apply div_nonneg _ hm.le
      split_ifs
      · exact σ.nonneg x
      · exact le_rfl
    sum_eq_one := by rw [← Finset.sum_div]; exact div_self hm.ne'
  }

theorem gatedLaw_domination {N : ℕ} (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (hhalf : (1 / 2 : ℝ) ≤ ∑ x, if J x then σ.w x else 0) (x : Fin N) :
    (gatedLaw σ J hm).w x ≤ 2 * σ.w x := by
  classical
  change (if J x then σ.w x else 0) / _ ≤ _
  apply (div_le_iff₀ hm).2
  by_cases hx : J x
  · rw [if_pos hx]
    nlinarith [σ.nonneg x]
  · rw [if_neg hx]
    exact mul_nonneg (mul_nonneg (by norm_num) (σ.nonneg x)) hm.le

theorem crossing_retained_mass_lower {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (hgate : (9 / 10 : ℝ) ≤ ∑ x, if J x then σ.w x else 0)
    (π : ℕ → Law N) (b : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ j x, 0 < (gatedLaw σ J hm).w x →
      |deg E c (π j).w x - 1 / 2| ≤ 2 * b)
    (ell : ℕ) (hell : 20 * (ell : ℝ) * b ≤ 1 / 10)
    (ys : Fin ell → Fin N) (hgood : crossingGood E c (gatedLaw σ J hm) π b ell ys) :
    (2 / 3 : ℝ) ≤ (∑ x, if J x then σ.w x else 0) *
      crossingProductMass E c (gatedLaw σ J hm) π ell ys := by
  have hcross := crossingState_mass E c (gatedLaw σ J hm) π b hb hbsmall hdeg ell ys hgood
  have hBernoulli := one_add_mul_le_pow (a := -(20 * b))
    (by linarith : (-2 : ℝ) ≤ -(20 * b)) ell
  have hpower : (9 / 10 : ℝ) ≤ (1 - 20 * b) ^ ell := by
    have hlin : (9 / 10 : ℝ) ≤ 1 + (ell : ℝ) * -(20 * b) := by linarith
    exact hlin.trans (by simpa [sub_eq_add_neg] using hBernoulli)
  have hmass : (9 / 10 : ℝ) ≤ crossingProductMass E c (gatedLaw σ J hm) π ell ys :=
    hpower.trans hcross.2.1
  nlinarith

theorem positiveTerm_denominator_change {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin d → Law N)
    (xs : Fin u → Fin N) (D : Fin u → ℝ) (I : Finset (Fin u))
    (hD : ∀ j, 0 < D j)
    (hdeg : ∀ l j, 0 < deg E c (π l).w (xs j))
    (hproduct : ∀ j, (1 / 2 : ℝ) ≤
      (∏ l, deg E c (π l).w (xs j)) / (D j) ^ d) :
    posTerm E c (fun l => (π l).w) I xs ≤
      (2 : ℝ) ^ u * ∏ l, ∑ y, (π l).w y * ∏ j ∈ I, hit E c (xs j) y / D j := by
  classical
  let A : Fin d → ℝ := fun l => ∑ y, (π l).w y * ∏ j ∈ I, hit E c (xs j) y / D j
  have hA : ∀ l, 0 ≤ A l := by
    intro l
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg ((π l).nonneg y)
    apply Finset.prod_nonneg
    intro j _
    apply div_nonneg _ (hD j).le
    unfold hit
    split_ifs <;> norm_num
  have hterm (l : Fin d) :
      (∑ y, (π l).w y * ∏ j ∈ I, (1 + acoef E c (π l).w (xs j) y)) =
        (∏ j ∈ I, D j / deg E c (π l).w (xs j)) * A l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [mul_left_comm (∏ j ∈ I, D j / deg E c (π l).w (xs j)) ((π l).w y),
      ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp only [acoef, if_pos (hdeg l j)]
    field_simp [(hD j).ne', (hdeg l j).ne']
    <;> ring
  have hratio (j : Fin u) : (∏ l, D j / deg E c (π l).w (xs j)) ≤ 2 := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpos : 0 < ∏ l, deg E c (π l).w (xs j) :=
      Finset.prod_pos fun l _ => hdeg l j
    apply (div_le_iff₀ hpos).2
    have h := (le_div_iff₀ (pow_pos (hD j) d)).mp (hproduct j)
    linarith
  have hcap : (∏ l, ∏ j ∈ I, D j / deg E c (π l).w (xs j)) ≤ (2 : ℝ) ^ u := by
    rw [Finset.prod_comm]
    calc
      _ ≤ ∏ _j ∈ I, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro j _; apply Finset.prod_nonneg; intro l _; exact div_nonneg (hD j).le (hdeg l j).le
        · intro j _; exact hratio j
      _ = (2 : ℝ) ^ I.card := by simp
      _ ≤ (2 : ℝ) ^ u := pow_le_pow_right₀ (by norm_num)
        (by simpa using Finset.card_le_univ I)
  unfold posTerm
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  exact mul_le_mul_of_nonneg_right hcap (Finset.prod_nonneg fun l _ => hA l)

theorem clusterMarginalLaw_supported {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) :
    (clusterMarginalLaw PT hPT hm W b).SupportedIn (T.Y k) := by
  classical
  intro y hy
  change clusterMarginal PT hPT hm W b y = 0
  unfold clusterMarginal SliceSolver.oddMarginal
  apply Finset.sum_eq_zero
  intro D _
  have hUy : (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U
      ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf (solverWordAt PT hPT hm b.1))
      (historyOnSlice W (clusterSliceAt PT hPT b.1)) D y = 0 := by
    by_contra hne
    have hbin := (clusterSolver PT hPT hm (patchAt PT hPT b.1)).U_support _ _ D y hne
    have hpatch : y ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y :=
      Finpartition.le (PT.tiling.P (patchAt PT hPT b.1)).bins D.2 hbin
    have hres := (hPT.tiling_valid.patch_supports _).2.2.1 hpatch
    exact hy (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports _).2.2.2 hres)).1
  simp only [clusterSliceAt] at hUy ⊢
  rw [hUy, mul_zero]

theorem clusterMarginalLaw_width {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) :
    (clusterMarginalLaw PT hPT hm W b).WidthLE
      (Real.log 8 + 2 * (PT.tiling.kScale (patchAt PT hPT b.1) : ℝ) *
        PT.tiling.tScale (patchAt PT hPT b.1) +
        Real.log ((T.S.N k : ℝ) / (PT.tiling.P (patchAt PT hPT b.1)).M)) := by
  intro y
  let i := patchAt PT hPT b.1
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    have hM' : 0 < (PT.tiling.P i).M := by
      rw [← (PT.tiling.P i).cardY]
      exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).2
    exact_mod_cast hM'
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hcap := (clusterSolver PT hPT hm i).marginal_cap
    ((clusterSolver PT hPT hm i).groupOf (solverWordAt PT hPT hm b.1))
    (historyOnSlice W (clusterSliceAt PT hPT b.1)) y
  change clusterMarginal PT hPT hm W b y ≤ _
  calc
    _ ≤ 8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) /
        (PT.tiling.P i).M := hcap
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8),
        Real.exp_log (div_pos hN hM)]
      dsimp [i]
      field_simp

theorem clusterSigma_supported {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (I : ClusterInternalData PT) (a : EvenPosition T k)
    (τ : Law (T.S.N k)) (C : ℝ)
    (hdom : ∀ x, τ.w x ≤ C * clusterSigma PT hPT hm W I a x) :
    τ.SupportedIn (T.X k) := by
  intro x hx
  have hs : clusterSigma PT hPT hm W I a x = 0 := by
    by_contra hn
    have henv := clusterSigma_support_envelope PT hPT hm W hW I a x hn
    have hpatch := hPT.envelope_subset _ henv
    have hres := (hPT.tiling_valid.patch_supports _).1 hpatch
    exact hx (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports _).2.1 hres)).1
  have h := hdom x
  rw [hs, mul_zero] at h
  exact le_antisymm h (τ.nonneg x)

theorem clusterSigma_dominated_width {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) (a : EvenPosition T k)
    (τ : Law (T.S.N k)) (ell : ℕ)
    (hdom : ∀ x, τ.w x ≤ (5 : ℝ) ^ (ell + 1) * clusterSigma PT hPT hm W I a x) :
    τ.WidthLE (((ell + 1 : ℕ) : ℝ) * Real.log 5 +
      ((PT.tiling.P (patchAt PT hPT a.1)).h : ℝ) * Real.log 2 -
      500 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  intro x
  have hcap := mul_le_mul_of_nonneg_left (clusterSigma_cap PT hPT hm W I a x)
    (by positivity : (0 : ℝ) ≤ 5 ^ (ell + 1))
  apply (hdom x).trans
  apply hcap.trans_eq
  rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 5),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show (-500 : ℝ) * PT.tiling.gain (patchAt PT hPT a.1) =
    -(500 * PT.tiling.gain (patchAt PT hPT a.1)) by ring, Real.exp_neg]
  ring

theorem clusterInternal_E_external {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (F : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1 →
      ({b : OddPosition T k //
        b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} →
          Fin (T.S.N k)) → ℝ) :
    (clusterInternalKernel PT hPT hm W).E (fun I =>
      F (I (clusterSliceAt PT hPT a.1))
        (fun b => (I (clusterSliceAt PT hPT b.1.1)).2 (solverWordAt PT hPT hm b.1.1))) =
    ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw
      (historyOnSlice W (clusterSliceAt PT hPT a.1))).E (fun z =>
        (FinLaw.pi (fun b : {b : OddPosition T k //
          b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} =>
            lawToFinLaw (clusterMarginalLaw PT hPT hm W b.1))).E (F z)) := by
  classical
  have h := pi_E_center_labels
    (fun s : ClusterSlice PT => (clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s))
    (clusterSliceAt PT hPT a.1)
    (fun b : {b : OddPosition T k //
      b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} =>
        clusterSliceAt PT hPT b.1.1)
    (clusterExternalSlices_injective PT hPT a)
    (fun b => clusterExternalSlices_ne_center PT hPT a b.1 b.2)
    (fun b ω => ω.2 (solverWordAt PT hPT hm b.1.1)) F
  apply h.trans
  apply congrArg (((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw
    (historyOnSlice W (clusterSliceAt PT hPT a.1))).E)
  funext z
  apply congrArg (fun (P : FinLaw ({b : OddPosition T k //
    b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} →
      Fin (T.S.N k))) => P.E (F z))
  apply congrArg (fun (P : {b : OddPosition T k //
    b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a} →
      FinLaw (Fin (T.S.N k))) => FinLaw.pi P)
  funext b
  exact cluster_slice_label_map PT hPT hm W b.1

noncomputable def enumerateFinset {α : Type*} [DecidableEq α] (s : Finset α) :
    Fin s.card → {a : α // a ∈ s} :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm

theorem enumerateFinset_surjective {α : Type*} [DecidableEq α] (s : Finset α) :
    Function.Surjective (enumerateFinset s) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm.surjective

theorem enumerateFinset_prod {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (∏ j : Fin s.card, f (enumerateFinset s j).1) = ∏ a ∈ s, f a := by
  classical
  calc
    _ = ∏ a : {a // a ∈ s}, f a.1 :=
      (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm.prod_comp
        (fun a : {a // a ∈ s} => f a.1)
    _ = _ := Finset.prod_coe_sort s f

noncomputable def clusterBulkLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (j : Fin (clusterBulkNeighbours PT hPT a).card) : Law (T.S.N k) :=
  clusterMarginalLaw PT hPT hm W (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1

theorem clusterBulk_moderate_iff {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (xs : Fin κ.u → Fin (T.S.N k)) :
    Moderate (T.S.E k) PT.tiling.c (fun l => (clusterBulkLaw PT hPT hm W a l).w)
      (2 * κ.ξ) xs ↔
    ¬ ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
      2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| := by
  classical
  have heq (l : Fin (clusterBulkNeighbours PT hPT a).card) (J : Finset (Fin κ.u)) :
      inter (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a l).w J xs =
        clusterInteraction PT hPT hm W
          (enumerateFinset (clusterBulkNeighbours PT hPT a) l).1 J xs := rfl
  constructor
  · intro hmod ⟨b, hb, J, hJ, hlarge⟩
    obtain ⟨l, hl⟩ := enumerateFinset_surjective (clusterBulkNeighbours PT hPT a) ⟨b, hb⟩
    have h := hmod l J hJ
    rw [heq, hl] at h
    exact not_lt_of_ge h hlarge
  · intro hnot l J hJ
    rw [heq]
    exact le_of_not_gt (fun h => hnot
      ⟨_, (enumerateFinset (clusterBulkNeighbours PT hPT a) l).2, J, hJ, h⟩)

theorem clusterBulk_positive_envelope_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (xs : Fin κ.u → Fin (T.S.N k))
    (hJ : ∀ j, clusterJ0 PT hPT hm W a (xs j))
    (hbsmall : bstar T k ≤ 1 / 100) :
    (∑ J : Finset (Fin κ.u),
      posTerm (T.S.E k) PT.tiling.c (fun l => (clusterBulkLaw PT hPT hm W a l).w) J xs) ≤
    (2 : ℝ) ^ κ.u * clusterInteractionEnvelope PT hPT hm W a xs := by
  classical
  let D : Fin κ.u → ℝ := fun j =>
    deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j)
  have hD : ∀ j, 0 < D j := fun j => (hJ j).2.2.1
  have hdeg : ∀ l j, 0 < deg (T.S.E k) PT.tiling.c
      (clusterBulkLaw PT hPT hm W a l).w (xs j) := by
    intro l j
    have h := (hJ j).2.1 (enumerateFinset (clusterBulkNeighbours PT hPT a) l).1
      (enumerateFinset (clusterBulkNeighbours PT hPT a) l).2
    have hab := abs_le.mp h
    change -(2 * bstar T k) ≤
      deg (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a l).w (xs j) - 1 / 2 ∧ _ at hab
    linarith
  have hproduct : ∀ j, (1 / 2 : ℝ) ≤
      (∏ l, deg (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a l).w (xs j)) /
        D j ^ (clusterBulkNeighbours PT hPT a).card := by
    intro j
    rw [show (∏ l, deg (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a l).w (xs j)) =
        ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterDegree PT hPT hm W b (xs j) from
      enumerateFinset_prod _ (fun b => clusterDegree PT hPT hm W b (xs j))]
    exact (hJ j).2.2.2.1
  unfold clusterInteractionEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J _
  have h := positiveTerm_denominator_change (T.S.E k) PT.tiling.c
    (clusterBulkLaw PT hPT hm W a) xs D J hD hdeg hproduct
  apply h.trans_eq
  congr 1
  change (∏ l, ∑ y, clusterMarginal PT hPT hm W
    (enumerateFinset (clusterBulkNeighbours PT hPT a) l).1 y *
    ∏ j ∈ J, hit (T.S.E k) PT.tiling.c (xs j) y / D j) = _
  rw [enumerateFinset_prod (clusterBulkNeighbours PT hPT a)
    (fun b => ∑ y, clusterMarginal PT hPT hm W b y *
      ∏ j ∈ J, hit (T.S.E k) PT.tiling.c (xs j) y / D j)]
  apply Finset.prod_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [clusterNominalRatio, hD j, D]

theorem clusterInteractionEnvelope_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (xs : Fin κ.u → Fin (T.S.N k)) :
    0 ≤ clusterInteractionEnvelope PT hPT hm W a xs := by
  unfold clusterInteractionEnvelope
  apply Finset.sum_nonneg
  intro J _
  apply Finset.prod_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg ((clusterMarginalLaw PT hPT hm W b).nonneg y)
  apply Finset.prod_nonneg
  intro j _
  unfold clusterNominalRatio
  dsimp only
  split_ifs with hd
  · apply div_nonneg _ hd.le
    unfold hit
    split_ifs <;> norm_num
  · exact le_rfl

theorem clusterBulk_large_le_integrand {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (σ : Fin (T.S.N k) → ℝ) (hσ : ∀ x, 0 ≤ σ x)
    (τ : Law (T.S.N k)) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ x, τ.w x ≤ C * σ x)
    (hgate : ∀ x, τ.w x ≠ 0 → clusterJ0 PT hPT hm W a x)
    (hbsmall : bstar T k ≤ 1 / 100) :
    (∑ xs : Fin κ.u → Fin (T.S.N k),
      if ¬ Moderate (T.S.E k) PT.tiling.c
          (fun l => (clusterBulkLaw PT hPT hm W a l).w) (2 * κ.ξ) xs then
        prodW τ.w xs * ∑ J : Finset (Fin κ.u),
          posTerm (T.S.E k) PT.tiling.c
            (fun l => (clusterBulkLaw PT hPT hm W a l).w) J xs else 0) ≤
    C ^ κ.u * (2 : ℝ) ^ κ.u *
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        (∏ j, σ (xs j)) *
          (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
              ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
                2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|
            then clusterInteractionEnvelope PT hPT hm W a xs else 0)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro xs _
  have hmod := clusterBulk_moderate_iff PT hPT hm W a xs
  have hnonneg : 0 ≤ (∏ j, σ (xs j)) *
      (if (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
          ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
            2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|
        then clusterInteractionEnvelope PT hPT hm W a xs else 0) := by
    apply mul_nonneg (Finset.prod_nonneg fun j _ => hσ (xs j))
    split_ifs
    · exact clusterInteractionEnvelope_nonneg PT hPT hm W a xs
    · exact le_rfl
  by_cases hlarge : ¬ Moderate (T.S.E k) PT.tiling.c
      (fun l => (clusterBulkLaw PT hPT hm W a l).w) (2 * κ.ξ) xs
  · rw [if_pos hlarge]
    by_cases hp : prodW τ.w xs = 0
    · rw [hp, zero_mul]
      exact mul_nonneg (mul_nonneg (pow_nonneg hC _) (by positivity)) hnonneg
    · have hJ : ∀ j, clusterJ0 PT hPT hm W a (xs j) := by
        intro j
        apply hgate
        intro hz
        exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hz)
      have hbad : ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
          2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| := by
        by_contra hn
        exact hlarge (hmod.mpr hn)
      rw [if_pos ⟨hJ, hbad⟩]
      have hprod : prodW τ.w xs ≤ C ^ κ.u * ∏ j, σ (xs j) := by
        unfold prodW
        calc
          _ ≤ ∏ j, C * σ (xs j) :=
            Finset.prod_le_prod₀ (fun j _ => τ.nonneg (xs j)) (fun j _ => hdom (xs j))
          _ = _ := by rw [Finset.prod_mul_distrib]; simp
      have henv := clusterBulk_positive_envelope_le PT hPT hm W a xs hJ hbsmall
      calc
        _ ≤ (C ^ κ.u * ∏ j, σ (xs j)) *
            ((2 : ℝ) ^ κ.u * clusterInteractionEnvelope PT hPT hm W a xs) :=
          mul_le_mul hprod henv
            (Finset.sum_nonneg fun J _ => positiveTerm_nonneg _ _ _ J xs)
            (mul_nonneg (pow_nonneg hC _) (Finset.prod_nonneg fun j _ => hσ (xs j)))
        _ = _ := by ring
  · rw [if_neg hlarge]
    exact mul_nonneg (mul_nonneg (pow_nonneg hC _) (by positivity)) hnonneg

theorem crossing_failure_of_width {T : Stage} {k : ℕ} {wS wL w : ℝ}
    (hD : TwoBudgetDisc T k wS wL (bstar T k)) (c : Colour)
    (τ : Law (T.S.N k)) (π : ℕ → Law (T.S.N k)) (ell : ℕ)
    (hπ : ∀ j < ell, (π j).SupportedIn (T.Y k))
    (hπw : ∀ j < ell, (π j).WidthLE w)
    (hτ : ∀ m < ell, ∀ ys, crossingGood (T.S.E k) c τ π (bstar T k) m ys →
      (crossingState (T.S.E k) c τ π m ys).SupportedIn (T.X k))
    (hτw : ∀ m < ell, ∀ ys, crossingGood (T.S.E k) c τ π (bstar T k) m ys →
      (crossingState (T.S.E k) c τ π m ys).WidthLE wS) :
    (FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))).pr
      (fun ys => ¬ crossingGood (T.S.E k) c τ π (bstar T k) ell ys) ≤
        (ell : ℝ) * (2 * Real.exp (w - wL)) := by
  apply crossing_failure_probability _ _ _ _ _ _ (by positivity)
  intro m hm ys hy
  have h := exceptional_second hD c (Or.inl ⟨le_rfl, le_rfl⟩)
    (crossingState (T.S.E k) c τ π m ys) (π m) (hτ m hm ys hy)
    (hτw m hm ys hy) (hπ m hm) (hπw m hm)
  simpa [FinProb.pr, Finset.sum_filter] using h

theorem gated_crossing_row_identity {N d : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (π : ℕ → Law N) (ν : Fin d → Law N) (b : ℝ)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ j x, 0 < (gatedLaw σ J hm).w x →
      |deg E c (π j).w x - 1 / 2| ≤ 2 * b)
    (ell : ℕ) (ys : Fin ell → Fin N)
    (hy : crossingGood E c (gatedLaw σ J hm) π b ell ys)
    (zs : Fin d → Fin N) :
    (∑ x, σ.w x * (if J x then 1 else 0) *
      (∏ j : Fin ell, normalizedHit E c (π j) x (ys j)) *
      (∏ l : Fin d, normalizedHit E c (ν l) x (zs l))) =
    (∑ x, if J x then σ.w x else 0) *
      crossingProductMass E c (gatedLaw σ J hm) π ell ys *
      Zmass E c (crossingState E c (gatedLaw σ J hm) π ell ys).w
        (fun l => (ν l).w) zs := by
  classical
  let m := ∑ x, if J x then σ.w x else 0
  have hmass := crossingState_mass E c (gatedLaw σ J hm) π b hb hbsmall hdeg ell ys hy
  have hgate (x : Fin N) : σ.w x * (if J x then 1 else 0) = m * (gatedLaw σ J hm).w x := by
    change σ.w x * (if J x then 1 else 0) = m * ((if J x then σ.w x else 0) / m)
    have hm' : m ≠ 0 := hm.ne'
    by_cases hx : J x <;> simp [hx, hm', mul_div_cancel₀]
  have hfactor (x y : Fin N) (ν : Law N) :
      normalizedHit E c ν x y = 1 + acoef E c ν.w x y := by
    unfold normalizedHit acoef
    dsimp only
    split_ifs <;> ring
  unfold Zmass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hgate]
  have hrow := hmass.2.2 x
  unfold crossingNumerator at hrow
  rw [mul_assoc m, ← hrow]
  simp_rw [hfactor]
  ring

theorem clusterBulk_tail_le_center_budget {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (τ : Law (T.S.N k)) (C B : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ x, τ.w x ≤ C * clusterSigmaAtCenter PT hPT hm W a Y x)
    (hgate : ∀ x, τ.w x ≠ 0 → clusterJ0 PT hPT hm W a x)
    (hbsmall : bstar T k ≤ 1 / 100) (hu : Even κ.u)
    (hmoderate : |∑ xs : Fin κ.u → Fin (T.S.N k),
      if Moderate (T.S.E k) PT.tiling.c
          (fun l => (clusterBulkLaw PT hPT hm W a l).w) (2 * κ.ξ) xs then
        prodW τ.w xs * Phi (T.S.E k) PT.tiling.c
          (fun l => (clusterBulkLaw PT hPT hm W a l).w) xs else 0| ≤ B) :
    (FinLaw.pi (fun l => lawToFinLaw (clusterBulkLaw PT hPT hm W a l))).pr
      (fun ys => Zmass (T.S.E k) PT.tiling.c τ.w
        (fun l => (clusterBulkLaw PT hPT hm W a l).w) ys < 3 / 4) ≤
    (4 : ℝ) ^ κ.u * (B + C ^ κ.u * (2 : ℝ) ^ κ.u *
      clusterInteractionIntegrandAtCenter PT hPT hm W a Y) := by
  apply heterogeneous_lower_tail_three_quarters _ _ _ _ hu (2 * κ.ξ) _ _ hmoderate
  exact clusterBulk_large_le_integrand PT hPT hm W a
    (clusterSigmaAtCenter PT hPT hm W a Y)
    ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).σ_nonneg _ _ _)
    τ C hC hdom hgate hbsmall

theorem clusterBulk_moderate_estimate (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ a : EvenPosition T k, ∀ τ : Law (T.S.N k),
      τ.SupportedIn (T.X k) → τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) →
      (∀ b ∈ clusterBulkNeighbours PT hPT a,
        (clusterMarginalLaw PT hPT hm W b).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
      (∀ x, τ.w x ≠ 0 → clusterJ0 PT hPT hm W a x) →
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if Moderate (T.S.E k) PT.tiling.c
            (fun l => (clusterBulkLaw PT hPT hm W a l).w) (2 * κ.ξ) xs then
          prodW τ.w xs * Phi (T.S.E k) PT.tiling.c
            (fun l => (clusterBulkLaw PT hPT hm W a l).w) xs else 0| ≤
        (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) := by
  have hmoderate := moderate_moment κ hκ T hDeep true 2 (by norm_num)
  have hmoderate' := moderate_moment κ hκ T hDeep false 2 (by norm_num)
  filter_upwards [hmoderate, hmoderate'] with k hk hk'
  intro PT hPT hm W a τ hτ hτw hπw hgate
  have hcard : (clusterBulkNeighbours PT hPT a).card ≤ T.S.n k := by
    apply le_trans (Finset.card_le_card (show clusterBulkNeighbours PT hPT a ⊆
        Lane_q_s15_direct.star a from by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩))
      (Lane_q_s15_direct.star_card_le a)
  let S : InterSetting T k (κ.xs / 4) := {
    d := (clusterBulkNeighbours PT hPT a).card
    d_le := hcard
    τ := τ
    π := clusterBulkLaw PT hPT hm W a
    τ_supported := hτ
    τ_width := hτw
    π_supported := fun l => clusterMarginalLaw_supported PT hPT hm W _
    π_width := fun l => hπw _ (enumerateFinset (clusterBulkNeighbours PT hPT a) l).2
  }
  have hdeg : S.DegOK PT.tiling.c 2 := by
    intro l x hx
    exact (hgate x hx.ne').2.1 _ (enumerateFinset (clusterBulkNeighbours PT hPT a) l).2
  cases hc : PT.tiling.c
  · exact hk' S (by simpa [hc] using hdeg)
  · exact hk S (by simpa [hc] using hdeg)

theorem eventually_const_mul_rpow_le (T : Stage) (C x y : ℝ) (hxy : x < y) :
    ∀ᶠ k in atTop, C * (T.S.n k : ℝ) ^ x ≤ (T.S.n k : ℝ) ^ y := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hp := (tendsto_rpow_atTop (by linarith : 0 < y - x)).comp hn
  filter_upwards [hn.eventually_ge_atTop 1, hp.eventually_ge_atTop C] with k hn1 hk
  change (1 : ℝ) ≤ T.S.n k at hn1
  change C ≤ (T.S.n k : ℝ) ^ (y - x) at hk
  have hn0 : (0 : ℝ) < T.S.n k := by linarith
  rw [show y = (y - x) + x by ring, Real.rpow_add hn0]
  exact mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hn0.le _)

theorem high_cluster_marginal_and_tilted_widths (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm,
      (∀ b : OddPosition T k,
        (clusterMarginalLaw PT hPT hm W b).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) ∧
      (∀ I : ClusterInternalData PT, ∀ a : EvenPosition T k,
        ∀ ell ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ, ∀ τ : Law (T.S.N k),
        (∀ x, τ.w x ≤ (5 : ℝ) ^ (ell + 1) * clusterSigma PT hPT hm W I a x) →
          τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) := by
  have hxy : κ.ι < κ.xs / 4 := by
    have h := min_le_left κ.xs (min κ.η0 (0.01 : ℝ))
    linarith [hκ.ι_rng.2, hκ.xs_rng.1]
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hu : (1 : ℝ) ≤ κ.u := by
    have h := hκ.u_rng.2
    exact_mod_cast (by omega : 1 ≤ κ.u)
  have hsmall := eventually_const_mul_rpow_le T (30 + κ.a) κ.ι (κ.xs / 4) hxy
  have hn := T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hsmall, hn] with k hsmall hn
  intro PT hPT hm W
  let p : ℝ := (T.S.n k : ℝ) ^ κ.ι
  have hn1 : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hp : 1 ≤ p := Real.one_le_rpow hn1 hκ.ι_rng.1.le
  have hH (i : Fin PT.tiling.m) : ((PT.tiling.P i).h : ℝ) ≤ p :=
    (le_max_left _ _).trans (hPT.tiling_valid.allocation_bounds i).1.le
  have hL (i : Fin PT.tiling.m) : ((PT.tiling.P i).ℓ : ℝ) ≤ p :=
    (le_max_right _ _).trans (hPT.tiling_valid.allocation_bounds i).1.le
  have hgain (i : Fin PT.tiling.m) :
      PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
    rcases hm with hm | hm <;> simp [Tiling.gain, hm]
  have hg0 (i : Fin PT.tiling.m) : 0 ≤ PT.tiling.gain i := by rw [hgain]; positivity
  have hg (i : Fin PT.tiling.m) : PT.tiling.gain i ≤ κ.a * p := by
    rw [hgain]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)).2
    nlinarith [hH i]
  have hlog8 : Real.log 8 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlog5 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · intro b
    let i := patchAt PT hPT b.1
    apply Law.WidthLE.mono (clusterMarginalLaw_width PT hPT hm W b)
    apply le_trans _ hsmall
    have halloc : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
        PT.tiling.gain i / (1000 * κ.u) := by
      rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | hbounds
      · rcases hm with hm | hm <;> rw [hm] at hb <;> cases hb
      · exact hbounds.2
    have hlog : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ κ.a * p := by
      apply halloc.trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * κ.u)).2
      have h := hg i
      have hmul := mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1000 * κ.u by linarith) (show 0 ≤ κ.a * p by positivity)
      exact h.trans (by simpa using hmul)
    have hKT := high_scale_KT_le_height hκ PT hPT hm i
    change Real.log 8 + 2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i +
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ (30 + κ.a) * p
    nlinarith [hH i]
  · intro I a ell hell τ hdom
    apply Law.WidthLE.mono (clusterSigma_dominated_width PT hPT hm W I a τ ell hdom)
    apply le_trans _ hsmall
    have hell' : (ell : ℝ) ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ := by exact_mod_cast hell
    have hmul5 := mul_le_mul_of_nonneg_left hlog5 (by positivity : (0 : ℝ) ≤ ell + 1)
    have hmul2 := mul_le_mul_of_nonneg_left hlog2
      (Nat.cast_nonneg (PT.tiling.P (patchAt PT hPT a.1)).h)
    push_cast
    nlinarith [hH (patchAt PT hPT a.1), hL (patchAt PT hPT a.1), hg0 (patchAt PT hPT a.1)]

theorem finLaw_pr_le_one {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A ≤ 1 := by
  classical
  rw [← P.sum_one]
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact P.nonneg x

theorem gated_crossing_bulk_failure_le {N d : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (hgate : (9 / 10 : ℝ) ≤ ∑ x, if J x then σ.w x else 0)
    (π : ℕ → Law N) (ν : Fin d → Law N) (b : ℝ)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100)
    (hdeg : ∀ j x, 0 < (gatedLaw σ J hm).w x → |deg E c (π j).w x - 1 / 2| ≤ 2 * b)
    (ell : ℕ) (hell : 20 * (ell : ℝ) * b ≤ 1 / 10)
    (γ B : ℝ) (hB : 0 ≤ B)
    (hcross : (FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))).pr
      (fun ys => ¬ crossingGood E c (gatedLaw σ J hm) π b ell ys) ≤ γ)
    (hbulk : ∀ ys, crossingGood E c (gatedLaw σ J hm) π b ell ys →
      (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr
        (fun zs => Zmass E c (crossingState E c (gatedLaw σ J hm) π ell ys).w
          (fun l => (ν l).w) zs < 3 / 4) ≤ B) :
    (FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))).E (fun ys =>
      (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr (fun zs =>
        (∑ x, σ.w x * (if J x then 1 else 0) *
          (∏ j : Fin ell, normalizedHit E c (π j) x (ys j)) *
          (∏ l : Fin d, normalizedHit E c (ν l) x (zs l))) < 1 / 2)) ≤ γ + B := by
  classical
  let P := FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))
  let Q := FinLaw.pi (fun l => lawToFinLaw (ν l))
  let Good := crossingGood E c (gatedLaw σ J hm) π b ell
  have hpoint (ys : Fin ell → Fin N) :
      Q.pr (fun zs => (∑ x, σ.w x * (if J x then 1 else 0) *
        (∏ j : Fin ell, normalizedHit E c (π j) x (ys j)) *
        (∏ l : Fin d, normalizedHit E c (ν l) x (zs l))) < 1 / 2) ≤
        (if ¬ Good ys then 1 else 0) + B := by
    by_cases hy : Good ys
    · rw [if_neg (not_not.mpr hy), zero_add]
      apply le_trans _ (hbulk ys hy)
      apply finLaw_pr_mono
      intro zs hz
      rw [gated_crossing_row_identity E c σ J hm π ν b hb hbsmall hdeg ell ys hy zs] at hz
      have hmass := crossing_retained_mass_lower E c σ J hm hgate π b hb hbsmall hdeg ell hell ys hy
      by_contra hnot
      have hZ : (3 / 4 : ℝ) ≤ Zmass E c
          (crossingState E c (gatedLaw σ J hm) π ell ys).w (fun l => (ν l).w) zs :=
        le_of_not_gt hnot
      have hprod := mul_le_mul hmass hZ (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by linarith : 0 ≤ (∑ x, if J x then σ.w x else 0) *
          crossingProductMass E c (gatedLaw σ J hm) π ell ys)
      norm_num at hprod
      linarith
    · rw [if_pos hy]
      exact (finLaw_pr_le_one Q _).trans (by linarith)
  calc
    _ ≤ P.E (fun ys => (if ¬ Good ys then 1 else 0) + B) := by
      unfold FinLaw.E
      apply Finset.sum_le_sum
      intro ys _
      exact mul_le_mul_of_nonneg_left (hpoint ys) (P.nonneg ys)
    _ = P.pr (fun ys => ¬ Good ys) + B := by
      rw [finLaw_pr_eq_indicator]
      simp only [FinLaw.E, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : Good x <;> simp [h]
    _ ≤ γ + B := by
      have hc : P.pr (fun ys => ¬ Good ys) ≤ γ := hcross
      linarith

theorem high_cluster_height_gt_log5 {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hκ : κ.Admissible) (i : Fin PT.tiling.m)
    (hlog : 1 < Real.log (T.S.n k)) :
    Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) < (PT.tiling.P i).h := by
  have hcluster : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
      PT.tiling.mode = .highLarge := by
    rcases hm with hs | hl
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hl)
  rcases hPT.tiling_valid.cluster_data hcluster i with
    ⟨_, _, _, _, _, _, _, hqle, _, _, hsmallReg, hlargeReg⟩
  have hMlo : 100 < (κ.Mlo : ℝ) := by
    have hratio : 0 < 100 * κ.aC / κ.aB := by
      exact div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    have hCb : 100 < κ.Cb := by linarith [hκ.Cb_big]
    linarith [hκ.Mlo_big]
  have hMhi : 5 < (κ.Mhi : ℝ) := by
    have hBound := hκ.Mhi_big.1
    have hterm : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    linarith
  have hMhiPos : 0 < (κ.Mhi : ℝ) := by linarith
  have hresult : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) < (PT.tiling.P i).h := by
    rcases hm with hsmall | hlarge
    · have hReg := hsmallReg.mp hsmall
      have hqLower : Real.rpow (Real.log (T.S.n k)) κ.cq < (PT.tiling.P i).q := hReg.1
      have hqle' : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi ≤ (PT.tiling.P i).h := by
        simpa [hsmall] using hqle
      have hExp : 5 < κ.cq * (κ.Mhi : ℝ) := hκ.Mhi_big.2
      have hpowBase : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
          Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hlog hExp
      have hmul : Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) =
          Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) :=
        Real.rpow_mul (by positivity) κ.cq (κ.Mhi : ℝ)
      have hqPow : Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) <
          Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
        Real.rpow_lt_rpow
          (le_of_lt (Real.rpow_pos_of_pos (by linarith [hlog]) κ.cq)) hqLower hMhiPos
      calc
        Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
            Real.rpow (Real.log (T.S.n k)) (κ.cq * (κ.Mhi : ℝ)) := hpowBase
        _ = Real.rpow (Real.rpow (Real.log (T.S.n k)) κ.cq) (κ.Mhi : ℝ) := hmul
        _ < Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi := hqPow
        _ ≤ (PT.tiling.P i).h := hqle'
    · have hReg := hlargeReg.mp hlarge
      have hqLower : Real.log (T.S.n k) ^ 2 < (PT.tiling.P i).q := hReg
      have hqle' : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi ≤ (PT.tiling.P i).h := by
        simpa [hlarge] using hqle
      have hqgt : Real.log (T.S.n k) < (PT.tiling.P i).q := by
        nlinarith [hlog, hqLower]
      have hLpow : Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
          Real.rpow ((PT.tiling.P i).q : ℝ) ((5 : ℕ) : ℝ) :=
        Real.rpow_lt_rpow (by positivity) hqgt (by norm_num)
      have hqPow : Real.rpow ((PT.tiling.P i).q : ℝ) 5 ≤
          Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hqgt]) (by linarith [hMhi])
      calc
        Real.rpow (Real.log (T.S.n k)) ((5 : ℕ) : ℝ) <
            Real.rpow ((PT.tiling.P i).q : ℝ) 5 := by simpa using hLpow
        _ ≤ Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi := hqPow
        _ ≤ (PT.tiling.P i).h := hqle'
  exact hresult


theorem high_cluster_exp_height_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (c A : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m,
        Real.exp (-c * (PT.tiling.P i).h) ≤ (T.S.n k : ℝ) ^ (-A) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hlog := Real.tendsto_log_atTop.comp hn
  filter_upwards [hn.eventually_ge_atTop 1, hlog.eventually_ge_atTop (max 2 (A / c))]
    with k hn1 hlog
  change (1 : ℝ) ≤ T.S.n k at hn1
  change max 2 (A / c) ≤ Real.log (T.S.n k : ℝ) at hlog
  intro PT hPT hm i
  have hL : 2 ≤ Real.log (T.S.n k : ℝ) := (le_max_left _ _).trans hlog
  have hAc : A ≤ c * Real.log (T.S.n k : ℝ) := by
    have h := (le_max_right _ _).trans hlog
    simpa [mul_comm] using (div_le_iff₀ hc).mp h
  have hheight := high_cluster_height_gt_log5 PT hPT hm hκ i (by linarith)
  have hpow : (Real.log (T.S.n k : ℝ)) ^ 2 ≤ (PT.tiling.P i).h := by
    have h := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ Real.log (T.S.n k : ℝ))
      (show (2 : ℕ) ≤ 5 by omega)
    have hh : (Real.log (T.S.n k : ℝ)) ^ 5 < (PT.tiling.P i).h := by
      have hEq : Real.rpow (Real.log (T.S.n k : ℝ)) (5 : ℝ) =
          (Real.log (T.S.n k : ℝ)) ^ 5 := Real.rpow_natCast _ 5
      norm_num only at hheight
      rw [hEq] at hheight
      exact hheight
    exact h.trans hh.le
  have hmul := mul_le_mul_of_nonneg_right hAc (by linarith : 0 ≤ Real.log (T.S.n k : ℝ))
  have hh := mul_le_mul_of_nonneg_left hpow hc.le
  have hn0 : (0 : ℝ) < T.S.n k := by linarith
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem high_cluster_zero_small_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m,
        sliceEps κ (PT.tiling.P i).h ≤ (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hsmall := high_cluster_exp_height_eventually κ hκ T (0.001 * κ.a)
    (4 * κ.R) (by positivity)
  filter_upwards [hsmall] with k hk
  intro PT hPT hm i
  apply le_trans _ (hk PT hPT hm i)
  unfold sliceEps
  apply Real.exp_le_exp.mpr
  have hH : (1 : ℝ) ≤ (PT.tiling.P i).h := by exact_mod_cast clusterHeight_pos PT hPT hm i
  have hK : (1 : ℝ) ≤ sliceK κ (PT.tiling.P i).h := by
    apply le_trans (Real.one_le_rpow hH (by nlinarith [hκ.ω_rng.1] : 0 ≤ 3 * κ.ω))
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hK
    (show (0 : ℝ) ≤ 0.001 * κ.a * (PT.tiling.P i).h by positivity)
  nlinarith

theorem eventually_polynomial_exponential_small (T : Stage) (C D A c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop, C * (T.S.n k : ℝ) ^ D * Real.exp (-c * T.S.n k) ≤
      (T.S.n k : ℝ) ^ (-A) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hlim : Tendsto (fun k => C * ((T.S.n k : ℝ) ^ (A + D) * Real.exp (-c * T.S.n k)))
      atTop (nhds 0) := by
    simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A + D) c hc).comp hn).const_mul C
  filter_upwards [hn.eventually_gt_atTop 0, hlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k hn0 hk
  change (0 : ℝ) < T.S.n k at hn0
  change C * ((T.S.n k : ℝ) ^ (A + D) * Real.exp (-c * T.S.n k)) ≤ 1 at hk
  have h := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hn0.le (-A))
  rw [Real.rpow_add hn0, one_mul] at h
  have hcancel : (T.S.n k : ℝ) ^ A * (T.S.n k : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hn0]
    simp
  calc
    _ = (C * ((T.S.n k : ℝ) ^ A * (T.S.n k : ℝ) ^ D * Real.exp (-c * T.S.n k))) *
        (T.S.n k : ℝ) ^ (-A) := by rw [show C * (_ * _ * _) * _ =
          C * (T.S.n k : ℝ) ^ D * Real.exp (-c * T.S.n k) *
            ((T.S.n k : ℝ) ^ A * (T.S.n k : ℝ) ^ (-A)) by ring, hcancel, mul_one]
    _ ≤ _ := h

theorem high_cluster_crossing_scales_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, 0 ≤ bstar T k ∧ bstar T k ≤ 1 / 100 ∧
      ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ i : Fin PT.tiling.m,
        20 * ((PT.tiling.P i).ℓ : ℝ) * bstar T k ≤ 1 / 10 := by
  have hι : κ.ι < 0.01 := by
    have h := (min_le_right κ.xs (min κ.η0 (0.01 : ℝ))).trans (min_le_right κ.η0 0.01)
    linarith [hκ.ι_rng.2]
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hb := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn
  have he := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 0.96 - κ.ι by linarith)).comp hn
  have hlim : Tendsto (fun k => (20 : ℝ) * (T.S.n k : ℝ) ^ (-(0.96 - κ.ι)))
      atTop (nhds 0) := by simpa using he.const_mul (20 : ℝ)
  filter_upwards [hn.eventually_ge_atTop 1,
    hb.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    hlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))]
      with k hn1 hbk hek
  change (1 : ℝ) ≤ T.S.n k at hn1
  change (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) ≤ 1 / 100 at hbk
  change 20 * (T.S.n k : ℝ) ^ (-(0.96 - κ.ι)) ≤ 1 / 10 at hek
  have hn0 : (0 : ℝ) < T.S.n k := by linarith
  have hbstar : bstar T k = (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by unfold bstar; norm_num
  refine ⟨by rw [hbstar]; positivity, by rwa [hbstar], ?_⟩
  intro PT hPT i
  have hell : ((PT.tiling.P i).ℓ : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι :=
    (le_max_right _ _).trans (hPT.tiling_valid.allocation_bounds i).1.le
  calc
    _ ≤ 20 * (T.S.n k : ℝ) ^ κ.ι * (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by
      rw [hbstar]
      gcongr
    _ = 20 * (T.S.n k : ℝ) ^ (-(0.96 - κ.ι)) := by
      rw [mul_assoc, ← Real.rpow_add hn0]
      congr 2
      ring
    _ ≤ _ := hek

theorem high_cluster_crossing_failure_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ I : ClusterInternalData PT, ∀ a : EvenPosition T k,
      ∀ τ : Law (T.S.N k), (∀ x, τ.w x ≤ 2 * clusterSigma PT hPT hm W I a x) →
      ∀ ell ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ, ∀ π : ℕ → Law (T.S.N k),
      (∀ j < ell, (π j).SupportedIn (T.Y k)) →
      (∀ j < ell, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
      (∀ j x, 0 < τ.w x → |deg (T.S.E k) PT.tiling.c (π j).w x - 1 / 2| ≤ 2 * bstar T k) →
      (FinLaw.pi (fun j : Fin ell => lawToFinLaw (π j))).pr
        (fun ys => ¬ crossingGood (T.S.E k) PT.tiling.c τ π (bstar T k) ell ys) ≤
        (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) := by
  have hwidths := high_cluster_marginal_and_tilted_widths κ hκ T
  have hscales := high_cluster_crossing_scales_eventually κ hκ T
  have hsmall := eventually_const_mul_rpow_le T (2 / κ.α) (κ.xs / 4) 1
    (by linarith [hκ.xs_rng.2])
  have htail := eventually_polynomial_exponential_small T 2 1 (4 * κ.R) (κ.α / 2)
    (by linarith [hκ.α_rng.1])
  have hn := T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hwidths, hscales, hsmall, htail, hn, hDeep] with
    k hwidths hscales hsmall htail hn hdeep
  intro PT hPT hm W hW I a τ hdom ell hell π hπ hπw hdeg
  have hn1 : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hα : 0 < κ.α := hκ.α_rng.1
  have hsmall' : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ κ.α * T.S.n k / 2 := by
    rw [Real.rpow_one] at hsmall
    have h := (div_le_iff₀ hα).mp (show 2 * (T.S.n k : ℝ) ^ (κ.xs / 4) / κ.α ≤ T.S.n k by
      convert hsmall using 1 <;> ring)
    linarith
  have hfirst (m : ℕ) (hm' : m < ell) (ys : Fin m → Fin (T.S.N k))
      (hy : crossingGood (T.S.E k) PT.tiling.c τ π (bstar T k) m ys) :
      ∀ x, (crossingState (T.S.E k) PT.tiling.c τ π m ys).w x ≤
        (5 : ℝ) ^ (m + 1) * clusterSigma PT hPT hm W I a x := by
    intro x
    have h := crossingState_domination (T.S.E k) PT.tiling.c τ π (bstar T k)
      hscales.1 hscales.2.1 hdeg m ys hy x
    calc
      _ ≤ (5 : ℝ) ^ m * τ.w x := h
      _ ≤ (5 : ℝ) ^ m * (2 * clusterSigma PT hPT hm W I a x) := by
        gcongr
        exact hdom x
      _ ≤ _ := by
        rw [pow_succ]
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 ^ m by positivity)
          (clusterSigma_nonneg PT hPT hm W I a x)]
  have hcross := crossing_failure_of_width hdeep PT.tiling.c τ π ell hπ hπw
    (fun m hm' ys hy => clusterSigma_supported PT hPT hm W hW I a _ _ (hfirst m hm' ys hy))
    (fun m hm' ys hy => Law.WidthLE.mono
      ((hwidths PT hPT hm W).2 I a m (by omega) _ (hfirst m hm' ys hy))
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hκ.xs_rng.1])))
  have helln : ell ≤ T.S.n k := by
    have hL := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ)
      (Finset.mem_univ (patchAt PT hPT a.1))
    have hlen := hPT.tiling_valid.prefix_internal_length
    omega
  have helln' : (ell : ℝ) ≤ T.S.n k := by exact_mod_cast helln
  apply hcross.trans
  apply le_trans _ htail
  rw [Real.rpow_one]
  calc
    _ ≤ (T.S.n k : ℝ) * (2 * Real.exp (-(κ.α / 2) * T.S.n k)) := by
      gcongr
      linarith
    _ = _ := by ring

theorem pi_E_sum {ι J A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
    (P : ι → FinLaw A) (Q : J → FinLaw A) (F : (ι → A) → (J → A) → ℝ) :
    (FinLaw.pi (Sum.elim P Q)).E (fun z => F (fun i => z (.inl i)) (fun j => z (.inr j))) =
      (FinLaw.pi P).E (fun a => (FinLaw.pi Q).E (F a)) := by
  classical
  let e := Equiv.sumArrowEquivProdArrow ι J A
  unfold FinLaw.E FinLaw.pi
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type]
  dsimp only [e, Equiv.sumArrowEquivProdArrow]
  simp only [Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (∏ i, (P i).w (a i)) * (∏ j, (Q j).w (b j)) * F a b = _
  ring

noncomputable def clusterCrossLaw {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (j : Fin (clusterCrossingNeighbours PT hPT a).card) : Law (T.S.N k) :=
  clusterMarginalLaw PT hPT hm W (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1

noncomputable def clusterExternalSumAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Fin (clusterCrossingNeighbours PT hPT a).card ⊕
      Fin (clusterBulkNeighbours PT hPT a).card → OddPosition T k :=
  Sum.elim (fun j => (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1)
    (fun j => (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1)

theorem clusterExternalSumAt_mem {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (j : Fin (clusterCrossingNeighbours PT hPT a).card ⊕
      Fin (clusterBulkNeighbours PT hPT a).card) :
    clusterExternalSumAt PT hPT a j ∈
      clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a := by
  cases j with
  | inl j => exact Finset.mem_union_right _ (enumerateFinset _ j).2
  | inr j => exact Finset.mem_union_left _ (enumerateFinset _ j).2

theorem clusterExternalSumAt_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Function.Injective (clusterExternalSumAt PT hPT a) := by
  classical
  intro j l heq
  cases j with
  | inl j =>
    cases l with
    | inl l =>
      apply congrArg Sum.inl
      apply (Fintype.equivFinOfCardEq (Fintype.card_coe (clusterCrossingNeighbours PT hPT a))).symm.injective
      exact Subtype.ext heq
    | inr l =>
      have hcross := (Finset.mem_filter.mp (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).2).2.2
      have hbulk := (Finset.mem_filter.mp (enumerateFinset (clusterBulkNeighbours PT hPT a) l).2).2.2.1
      change (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1 =
        (enumerateFinset (clusterBulkNeighbours PT hPT a) l).1 at heq
      rw [heq] at hcross
      exact (hcross hbulk).elim
  | inr j =>
    cases l with
    | inl l =>
      have hcross := (Finset.mem_filter.mp (enumerateFinset (clusterCrossingNeighbours PT hPT a) l).2).2.2
      have hbulk := (Finset.mem_filter.mp (enumerateFinset (clusterBulkNeighbours PT hPT a) j).2).2.2.1
      change (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1 =
        (enumerateFinset (clusterCrossingNeighbours PT hPT a) l).1 at heq
      rw [← heq] at hcross
      exact (hcross hbulk).elim
    | inr l =>
      apply congrArg Sum.inr
      apply (Fintype.equivFinOfCardEq (Fintype.card_coe (clusterBulkNeighbours PT hPT a))).symm.injective
      exact Subtype.ext heq

noncomputable def clusterRowAtCenterExternal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (ys : Fin (clusterCrossingNeighbours PT hPT a).card → Fin (T.S.N k))
    (zs : Fin (clusterBulkNeighbours PT hPT a).card → Fin (T.S.N k)) : ℝ :=
  ∑ x, clusterSigmaAtCenter PT hPT hm W a Y x *
    (if clusterJ PT hPT hm W a x then 1 else 0) *
    (∏ j, normalizedHit (T.S.E k) PT.tiling.c (clusterCrossLaw PT hPT hm W a j) x (ys j)) *
    (∏ j, normalizedHit (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a j) x (zs j))

theorem clusterRowMass_eq_center_external {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) (a : EvenPosition T k) :
    clusterRowMass PT hPT hm W I a = clusterRowAtCenterExternal PT hPT hm W a
      (I (clusterSliceAt PT hPT a.1))
      (fun j => (I (clusterSliceAt PT hPT (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1.1)).2
        (solverWordAt PT hPT hm (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1.1))
      (fun j => (I (clusterSliceAt PT hPT (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1.1)).2
        (solverWordAt PT hPT hm (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1.1)) := by
  classical
  have hdis : Disjoint (clusterBulkNeighbours PT hPT a) (clusterCrossingNeighbours PT hPT a) := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    exact (Finset.mem_filter.mp hc).2.2 (Finset.mem_filter.mp hb).2.2.1
  have hfactor (b : OddPosition T k) (x : Fin (T.S.N k)) :
      normalizedHit (T.S.E k) PT.tiling.c (clusterMarginalLaw PT hPT hm W b) x
        ((I (clusterSliceAt PT hPT b.1)).2 (solverWordAt PT hPT hm b.1)) =
      clusterFactor PT hPT hm W I a b x := rfl
  unfold clusterRowMass clusterRowAtCenterExternal clusterRowWeight
  apply Finset.sum_congr rfl
  intro x _
  change clusterSigma PT hPT hm W I a x * _ * _ =
    clusterSigma PT hPT hm W I a x * _ * _ * _
  rw [Finset.prod_union hdis]
  have hcross : (∏ j, normalizedHit (T.S.E k) PT.tiling.c (clusterCrossLaw PT hPT hm W a j) x
      ((I (clusterSliceAt PT hPT (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1.1)).2
        (solverWordAt PT hPT hm (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1.1))) =
      ∏ b ∈ clusterCrossingNeighbours PT hPT a, clusterFactor PT hPT hm W I a b x := by
    change (∏ j, clusterFactor PT hPT hm W I a (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1 x) = _
    exact enumerateFinset_prod _ (fun b => clusterFactor PT hPT hm W I a b x)
  have hbulk : (∏ j, normalizedHit (T.S.E k) PT.tiling.c (clusterBulkLaw PT hPT hm W a j) x
      ((I (clusterSliceAt PT hPT (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1.1)).2
        (solverWordAt PT hPT hm (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1.1))) =
      ∏ b ∈ clusterBulkNeighbours PT hPT a, clusterFactor PT hPT hm W I a b x := by
    change (∏ j, clusterFactor PT hPT hm W I a (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1 x) = _
    exact enumerateFinset_prod _ (fun b => clusterFactor PT hPT hm W I a b x)
  rw [hcross, hbulk]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem clusterRow_failure_probability_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    (clusterInternalKernel PT hPT hm W).pr
      (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) =
    ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw
      (historyOnSlice W (clusterSliceAt PT hPT a.1))).E (fun Y =>
        (FinLaw.pi (fun j => lawToFinLaw (clusterCrossLaw PT hPT hm W a j))).E (fun ys =>
          (FinLaw.pi (fun j => lawToFinLaw (clusterBulkLaw PT hPT hm W a j))).pr
            (fun zs => clusterRowAtCenterExternal PT hPT hm W a Y ys zs < 1 / 2))) := by
  classical
  let J := Fin (clusterCrossingNeighbours PT hPT a).card ⊕ Fin (clusterBulkNeighbours PT hPT a).card
  let t : J → ClusterSlice PT := fun j => clusterSliceAt PT hPT (clusterExternalSumAt PT hPT a j).1
  let f (j : J) (ω : ClusterSliceOutcome PT (t j).1) : Fin (T.S.N k) :=
    ω.2 (solverWordAt PT hPT hm (clusterExternalSumAt PT hPT a j).1)
  let F (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
      (labels : J → Fin (T.S.N k)) : ℝ :=
    if clusterRowAtCenterExternal PT hPT hm W a Y (fun j => labels (.inl j))
      (fun j => labels (.inr j)) < 1 / 2 then 1 else 0
  let P (s : ClusterSlice PT) := (clusterSolver PT hPT hm s.1).refLaw (historyOnSlice W s)
  have ht : Function.Injective t := by
    intro j l h
    have hs := clusterExternalSlices_injective PT hPT a
      (a₁ := ⟨clusterExternalSumAt PT hPT a j, clusterExternalSumAt_mem PT hPT a j⟩)
      (a₂ := ⟨clusterExternalSumAt PT hPT a l, clusterExternalSumAt_mem PT hPT a l⟩) h
    apply clusterExternalSumAt_injective PT hPT a
    exact congrArg Subtype.val hs
  have hi : ∀ j, t j ≠ clusterSliceAt PT hPT a.1 :=
    fun j => clusterExternalSlices_ne_center PT hPT a _ (clusterExternalSumAt_mem PT hPT a j)
  have hproj := pi_E_center_labels P (clusterSliceAt PT hPT a.1) t ht hi f F
  have hlaws : (fun j : J => FinLaw.map (P (t j)) (f j)) =
      Sum.elim (fun j => lawToFinLaw (clusterCrossLaw PT hPT hm W a j))
        (fun j => lawToFinLaw (clusterBulkLaw PT hPT hm W a j)) := by
    funext j
    cases j with
    | inl j => exact cluster_slice_label_map PT hPT hm W (enumerateFinset (clusterCrossingNeighbours PT hPT a) j).1
    | inr j => exact cluster_slice_label_map PT hPT hm W (enumerateFinset (clusterBulkNeighbours PT hPT a) j).1
  have hrow : (clusterInternalKernel PT hPT hm W).pr
      (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) =
      (FinLaw.pi P).E (fun I => F (I (clusterSliceAt PT hPT a.1)) (fun j => f j (I (t j)))) := by
    rw [finLaw_pr_eq_indicator]
    apply congrArg (clusterInternalKernel PT hPT hm W).E
    funext I
    rw [clusterRowMass_eq_center_external]
    rfl
  rw [hrow, hproj]
  apply congrArg (P (clusterSliceAt PT hPT a.1)).E
  funext Y
  rw [hlaws]
  have hsum := pi_E_sum
    (fun j => lawToFinLaw (clusterCrossLaw PT hPT hm W a j))
    (fun j => lawToFinLaw (clusterBulkLaw PT hPT hm W a j))
    (fun ys zs => if clusterRowAtCenterExternal PT hPT hm W a Y ys zs < 1 / 2 then 1 else 0)
  dsimp only [F]
  unfold FinLaw.E FinLaw.pi FinLaw.pr
  unfold FinLaw.E FinLaw.pi at hsum
  dsimp only at hsum ⊢
  simp only [mul_ite, mul_one, mul_zero] at hsum ⊢
  exact hsum

theorem high_cluster_interaction_budget_small_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m,
        (4 : ℝ) ^ κ.u * ((5 : ℝ) ^ ((PT.tiling.P i).ℓ + 1)) ^ κ.u *
          (2 : ℝ) ^ κ.u * Real.exp (-100 * PT.tiling.gain i) ≤
            (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hu : (0 : ℝ) < κ.u := by exact_mod_cast (by have := hκ.u_rng.2; omega : 0 < κ.u)
  have hR : (0 : ℝ) < κ.R := by
    rw [hκ.R_eq]
    have hP := hκ.P_big.2
    rw [hκ.Ac_eq] at hP
    exact_mod_cast (by nlinarith : 0 < κ.P ^ 2)
  have hsmall := high_cluster_exp_height_eventually κ hκ T (90 * κ.a / 10 ^ 6)
    (4 * κ.R) (by positivity)
  have hconst := eventually_const_mul_rpow_le T ((40 : ℝ) ^ κ.u)
    (-(4 * κ.R : ℝ)) (-(3 * κ.R : ℝ)) (by linarith)
  filter_upwards [hsmall, hconst] with k hsmall hconst
  intro PT hPT hm i
  have hgain : PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
    rcases hm with hm | hm <;> simp [Tiling.gain, hm]
  have hg0 : 0 ≤ PT.tiling.gain i := by rw [hgain]; positivity
  have hell : ((PT.tiling.P i).ℓ : ℝ) ≤ PT.tiling.gain i / (1000 * κ.u) := by
    rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | hbounds
    · rcases hm with hm | hm <;> rw [hm] at hb <;> cases hb
    · exact hbounds.1
  have hell' := (le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * κ.u)).mp hell
  have hlog5 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog5
    (show 0 ≤ (κ.u : ℝ) * (PT.tiling.P i).ℓ by positivity)
  have hexponent : (κ.u : ℝ) * (PT.tiling.P i).ℓ * Real.log 5 - 100 * PT.tiling.gain i ≤
      -90 * PT.tiling.gain i := by nlinarith
  have hpow : (5 : ℝ) ^ ((PT.tiling.P i).ℓ * κ.u) =
      Real.exp ((κ.u : ℝ) * (PT.tiling.P i).ℓ * Real.log 5) := by
    rw [show (κ.u : ℝ) * (PT.tiling.P i).ℓ = (((PT.tiling.P i).ℓ * κ.u : ℕ) : ℝ) by
      push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  calc
    _ = (40 : ℝ) ^ κ.u * Real.exp
        ((κ.u : ℝ) * (PT.tiling.P i).ℓ * Real.log 5 - 100 * PT.tiling.gain i) := by
      rw [pow_succ, mul_pow, ← pow_mul, hpow, Real.exp_sub]
      rw [show (-100 : ℝ) * PT.tiling.gain i = -(100 * PT.tiling.gain i) by ring, Real.exp_neg]
      have hconstpow : (4 : ℝ) ^ κ.u * 5 ^ κ.u * 2 ^ κ.u = 40 ^ κ.u := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      rw [← hconstpow]
      ring
    _ ≤ (40 : ℝ) ^ κ.u * Real.exp (-90 * PT.tiling.gain i) := by gcongr
    _ = (40 : ℝ) ^ κ.u * Real.exp (-(90 * κ.a / 10 ^ 6) * (PT.tiling.P i).h) := by
      rw [hgain]
      congr 2
      ring
    _ ≤ (40 : ℝ) ^ κ.u * (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) := by
      gcongr
      exact hsmall PT hPT hm i
    _ ≤ _ := hconst

theorem high_cluster_removed_budget_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i : Fin PT.tiling.m,
      ((PT.tiling.P i).M * ((2 : ℝ) ^ (PT.tiling.P i).h *
        Real.exp (-500 * PT.tiling.gain i) / T.S.N k)) *
      (Real.exp (-Real.rpow (T.S.n k : ℝ) 0.2) + Real.exp (-(κ.α / 2) * T.S.n k)) ≤ 1 / 10 := by
  have hι : κ.ι < 0.2 := by
    have h := (min_le_right κ.xs (min κ.η0 (0.01 : ℝ))).trans (min_le_right κ.η0 0.01)
    linarith [hκ.ι_rng.2]
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.2)).comp hn
  have hfirst := eventually_const_mul_rpow_le T 2 κ.ι 0.2 hι
  have hsecond := eventually_const_mul_rpow_le T (4 / κ.α) κ.ι 1 (by linarith)
  filter_upwards [hfirst, hsecond, hp.eventually_ge_atTop (2 * Real.log 20),
    hn.eventually_ge_atTop (max 1 (4 * Real.log 20 / κ.α))]
    with k hfirst hsecond hp hn1
  change 2 * Real.log 20 ≤ (T.S.n k : ℝ) ^ (0.2 : ℝ) at hp
  change max 1 (4 * Real.log 20 / κ.α) ≤ (T.S.n k : ℝ) at hn1
  intro PT hPT hm i
  have hα := hκ.α_rng.1
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hH : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι :=
    (le_max_left _ _).trans (hPT.tiling_valid.allocation_bounds i).1.le
  have hgain : 0 ≤ PT.tiling.gain i := by
    rcases hm with hm | hm <;> simp only [Tiling.gain, hm] <;> positivity
  have hM : ((PT.tiling.P i).M : ℝ) ≤ T.S.N k := by
    exact_mod_cast (show (PT.tiling.P i).M ≤ T.S.N k from by
      rw [← (PT.tiling.P i).cardX]
      simpa using Finset.card_le_univ (PT.tiling.P i).X)
  have hratio : (PT.tiling.P i).M / (T.S.N k : ℝ) ≤ 1 := by
    exact (div_le_iff₀ hN).2 (by simpa using hM)
  have hpow : (2 : ℝ) ^ (PT.tiling.P i).h ≤ Real.exp (PT.tiling.P i).h := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith [show (0 : ℝ) ≤ (PT.tiling.P i).h by positivity]
  have hgexp : Real.exp (-500 * PT.tiling.gain i) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  have hcap : (PT.tiling.P i).M * ((2 : ℝ) ^ (PT.tiling.P i).h *
      Real.exp (-500 * PT.tiling.gain i) / T.S.N k) ≤ Real.exp (PT.tiling.P i).h := by
    calc
      _ = ((PT.tiling.P i).M / (T.S.N k : ℝ)) * (2 : ℝ) ^ (PT.tiling.P i).h *
          Real.exp (-500 * PT.tiling.gain i) := by ring
      _ ≤ 1 * Real.exp (PT.tiling.P i).h * 1 := by gcongr
      _ = _ := by ring
  have hneg : Real.exp (-Real.log 20) = (1 / 20 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 20)]
    norm_num
  have hsecond' : 4 * (T.S.n k : ℝ) ^ κ.ι ≤ κ.α * T.S.n k := by
    rw [Real.rpow_one] at hsecond
    have h := (div_le_iff₀ hα).mp (show 4 * (T.S.n k : ℝ) ^ κ.ι / κ.α ≤ T.S.n k by
      convert hsecond using 1 <;> ring)
    nlinarith
  have hlogn : 4 * Real.log 20 ≤ κ.α * T.S.n k := by
    have h := (le_max_right _ _).trans hn1
    have h' := (div_le_iff₀ hα).mp h
    nlinarith
  have hb1 : Real.exp ((PT.tiling.P i).h - (T.S.n k : ℝ) ^ (0.2 : ℝ)) ≤ 1 / 20 := by
    rw [← hneg]
    apply Real.exp_le_exp.mpr
    linarith
  have hb2 : Real.exp ((PT.tiling.P i).h - (κ.α / 2) * T.S.n k) ≤ 1 / 20 := by
    rw [← hneg]
    apply Real.exp_le_exp.mpr
    linarith
  apply (mul_le_mul_of_nonneg_right hcap (by positivity)).trans
  rw [mul_add, ← Real.exp_add, ← Real.exp_add]
  have h1 : Real.exp ((PT.tiling.P i).h + -(T.S.n k : ℝ) ^ (0.2 : ℝ)) ≤ 1 / 20 := by
    simpa [sub_eq_add_neg] using hb1
  have h2 : Real.exp ((PT.tiling.P i).h + -(κ.α / 2) * T.S.n k) ≤ 1 / 20 := by
    convert hb2 using 1 <;> ring
  change Real.exp ((PT.tiling.P i).h + -(T.S.n k : ℝ) ^ (0.2 : ℝ)) +
    Real.exp ((PT.tiling.P i).h + -(κ.α / 2) * T.S.n k) ≤ (1 / 10 : ℝ)
  linarith

theorem high_cluster_mass_budget_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop,
      2 * (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) + ((4 : ℝ) ^ κ.u + 1) *
        (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by
  have hR : (0 : ℝ) < κ.R := by
    rw [hκ.R_eq]
    have hP := hκ.P_big.2
    rw [hκ.Ac_eq] at hP
    exact_mod_cast (by nlinarith : 0 < κ.P ^ 2)
  have hsmall := eventually_const_mul_rpow_le T (3 + (4 : ℝ) ^ κ.u)
    (-(3 * κ.R : ℝ)) (-(κ.R : ℝ)) (by linarith)
  have hn := T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hsmall, hn] with k hsmall hn
  have hn1 : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hpow : (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) ≤
      (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  nlinarith

theorem clusterInteractionIntegrandAtCenter_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1) :
    0 ≤ clusterInteractionIntegrandAtCenter PT hPT hm W a Y := by
  unfold clusterInteractionIntegrandAtCenter
  apply Finset.sum_nonneg
  intro xs _
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ =>
      (clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).σ_nonneg _ _ _ (xs j)
  · split_ifs
    · exact clusterInteractionEnvelope_nonneg PT hPT hm W a xs
    · exact le_rfl

theorem gated_bulk_row_identity {N d : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (ν : Fin d → Law N) (zs : Fin d → Fin N) :
    (∑ x, σ.w x * (if J x then 1 else 0) *
      ∏ l, normalizedHit E c (ν l) x (zs l)) =
    (∑ x, if J x then σ.w x else 0) *
      Zmass E c (gatedLaw σ J hm).w (fun l => (ν l).w) zs := by
  classical
  unfold Zmass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hgate : σ.w x * (if J x then 1 else 0) =
      (∑ x, if J x then σ.w x else 0) * (gatedLaw σ J hm).w x := by
    change σ.w x * (if J x then 1 else 0) = _ * ((if J x then σ.w x else 0) / _)
    by_cases hx : J x <;> simp [hx, hm.ne', mul_div_cancel₀]
  have hf (ν : Law N) (x y : Fin N) : normalizedHit E c ν x y = 1 + acoef E c ν.w x y := by
    unfold normalizedHit acoef
    dsimp only
    split_ifs <;> ring
  rw [hgate]
  simp_rw [hf]
  ring

theorem gated_bulk_failure_le {N d : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (σ : Law N) (J : Fin N → Prop)
    (hm : 0 < ∑ x, if J x then σ.w x else 0)
    (hgate : (2 / 3 : ℝ) ≤ ∑ x, if J x then σ.w x else 0)
    (ν : Fin d → Law N) (B : ℝ)
    (hbulk : (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr
      (fun zs => Zmass E c (gatedLaw σ J hm).w (fun l => (ν l).w) zs < 3 / 4) ≤ B) :
    (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr
      (fun zs => (∑ x, σ.w x * (if J x then 1 else 0) *
        ∏ l, normalizedHit E c (ν l) x (zs l)) < 1 / 2) ≤ B := by
  apply le_trans _ hbulk
  apply finLaw_pr_mono
  intro zs hz
  rw [gated_bulk_row_identity E c σ J hm ν zs] at hz
  by_contra hnot
  have hZ : (3 / 4 : ℝ) ≤ Zmass E c (gatedLaw σ J hm).w (fun l => (ν l).w) zs :=
    le_of_not_gt hnot
  have hprod := mul_le_mul hgate hZ (by norm_num : (0 : ℝ) ≤ 3 / 4) hm.le
  norm_num at hprod
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem clusterCenter_mass_bound_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      (∀ I : ClusterInternalData PT,
        (∑ x, if clusterJ PT hPT hm W a x then 0 else clusterSigma PT hPT hm W I a x) ≤ 1 / 10) →
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      clusterSigmaAtCenter PT hPT hm W a Y ≠ 0 →
      (FinLaw.pi (fun j => lawToFinLaw (clusterCrossLaw PT hPT hm W a j))).E (fun ys =>
        (FinLaw.pi (fun j => lawToFinLaw (clusterBulkLaw PT hPT hm W a j))).pr
          (fun zs => clusterRowAtCenterExternal PT hPT hm W a Y ys zs < 1 / 2)) ≤
      (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) + (4 : ℝ) ^ κ.u *
        ((T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) +
          ((5 : ℝ) ^ ((clusterCrossingNeighbours PT hPT a).card + 1)) ^ κ.u * (2 : ℝ) ^ κ.u *
            clusterInteractionIntegrandAtCenter PT hPT hm W a Y) := by
  have hwidth := high_cluster_marginal_and_tilted_widths κ hκ T
  have hmoderate := clusterBulk_moderate_estimate κ hκ T hDeep
  have hcross := high_cluster_crossing_failure_eventually κ hκ T hDeep
  have hscales := high_cluster_crossing_scales_eventually κ hκ T
  filter_upwards [hwidth, hmoderate, hcross, hscales] with k hwidth hmoderate hcross hscales
  intro PT hPT hm W hW a hRemoved Y hY
  let ell := (clusterCrossingNeighbours PT hPT a).card
  let C : ℝ := 5 ^ (ell + 1)
  let J := clusterJ PT hPT hm W a
  let ν := clusterBulkLaw PT hPT hm W a
  let B : ℝ := (4 : ℝ) ^ κ.u * ((T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) +
    C ^ κ.u * (2 : ℝ) ^ κ.u * clusterInteractionIntegrandAtCenter PT hPT hm W a Y)
  have hell : ell ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ :=
    Lane_q_s15_direct.highDirect_crossingNeighbours_card_le_prefix PT hPT a _ rfl
  let I0 := Classical.choice (Lane_sol_s15_transfer.nonempty_of_finLaw
    (clusterInternalKernel PT hPT hm W))
  let I : ClusterInternalData PT := Function.update I0 (clusterSliceAt PT hPT a.1) Y
  have hSigma : clusterSigma PT hPT hm W I a = clusterSigmaAtCenter PT hPT hm W a Y := by
    unfold clusterSigma clusterSigmaAtCenter
    simp only [I, Function.update_self]
  have hI : clusterSigma PT hPT hm W I a ≠ 0 := by rwa [hSigma]
  let σ : Law (T.S.N k) := {
    w := clusterSigma PT hPT hm W I a
    nonneg := clusterSigma_nonneg PT hPT hm W I a
    sum_eq_one := clusterSigma_prob PT hPT hm W I a hI
  }
  have hgate : (9 / 10 : ℝ) ≤ ∑ x, if J x then σ.w x else 0 := by
    have h := restrict_mass_lower σ.w J σ.sum_eq_one (1 / 10) (hRemoved I)
    norm_num at h ⊢
    exact h
  have hmass : 0 < ∑ x, if J x then σ.w x else 0 := by linarith
  let τ0 := gatedLaw σ J hmass
  have hdom0 : ∀ x, τ0.w x ≤ 2 * σ.w x := gatedLaw_domination σ J hmass (by linarith)
  have hC : 0 ≤ C := by positivity
  have hC2 : 2 ≤ C := by
    have hp : (1 : ℝ) ≤ 5 ^ ell := one_le_pow₀ (by norm_num)
    dsimp [C]
    rw [pow_succ]
    linarith
  have hτ0J : ∀ x, τ0.w x ≠ 0 → J x := by
    intro x hx
    by_contra hn
    exact hx (by simp [τ0, gatedLaw, hn])
  have hBulk (τ : Law (T.S.N k)) (hd : ∀ x, τ.w x ≤ C * σ.w x)
      (hJ : ∀ x, τ.w x ≠ 0 → J x) :
      (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr
        (fun zs => Zmass (T.S.E k) PT.tiling.c τ.w (fun l => (ν l).w) zs < 3 / 4) ≤ B := by
    have hs := clusterSigma_supported PT hPT hm W hW I a τ C hd
    have hw := (hwidth PT hPT hm W).2 I a ell hell τ hd
    have hg : ∀ x, τ.w x ≠ 0 → clusterJ0 PT hPT hm W a x := fun x hx => (hJ x hx).1
    have hmom := hmoderate PT hPT hm W a τ hs hw
      (fun b _ => (hwidth PT hPT hm W).1 b) hg
    exact clusterBulk_tail_le_center_budget PT hPT hm W a Y τ C _ hC
      (by intro x; simpa only [σ, hSigma] using hd x) hg hscales.2.1 hκ.u_rng.1 hmom
  have hB : 0 ≤ B := by
    dsimp [B]
    have hc := clusterInteractionIntegrandAtCenter_nonneg PT hPT hm W a Y
    positivity
  by_cases he0 : ell = 0
  · haveI : IsEmpty (Fin ell) := ⟨fun j => by have := j.isLt; omega⟩
    have hbulk0 := hBulk τ0 (fun x => (hdom0 x).trans
      (mul_le_mul_of_nonneg_right hC2 (σ.nonneg x))) hτ0J
    have hraw := gated_bulk_failure_le (T.S.E k) PT.tiling.c σ J hmass (by linarith) ν B hbulk0
    have hrow (ys : Fin ell → Fin (T.S.N k)) (zs : Fin (clusterBulkNeighbours PT hPT a).card → Fin (T.S.N k)) :
        clusterRowAtCenterExternal PT hPT hm W a Y ys zs =
        ∑ x, σ.w x * (if J x then 1 else 0) *
          ∏ l, normalizedHit (T.S.E k) PT.tiling.c (ν l) x (zs l) := by
      have hcp (x : Fin (T.S.N k)) :
          (∏ j : Fin ell, normalizedHit (T.S.E k) PT.tiling.c (clusterCrossLaw PT hPT hm W a j) x (ys j)) = 1 :=
        Finset.prod_eq_one (fun j _ => isEmptyElim j)
      unfold clusterRowAtCenterExternal
      apply Finset.sum_congr rfl
      intro x _
      change clusterSigmaAtCenter PT hPT hm W a Y x * (if J x then 1 else 0) *
        (∏ j : Fin ell, normalizedHit (T.S.E k) PT.tiling.c (clusterCrossLaw PT hPT hm W a j) x (ys j)) *
        (∏ l, normalizedHit (T.S.E k) PT.tiling.c (ν l) x (zs l)) = _
      rw [hcp, mul_one]
      have hx : σ.w x = clusterSigmaAtCenter PT hPT hm W a Y x := congrFun hSigma x
      rw [hx]
    calc
      _ ≤ (FinLaw.pi (fun j => lawToFinLaw (clusterCrossLaw PT hPT hm W a j))).E (fun _ => B) := by
        unfold FinLaw.E
        apply Finset.sum_le_sum
        intro ys _
        apply mul_le_mul_of_nonneg_left _ ((FinLaw.pi _).nonneg ys)
        apply le_trans _ hraw
        apply finLaw_pr_mono
        intro zs hz
        rwa [hrow] at hz
      _ = B := by
        unfold FinLaw.E
        dsimp only
        rw [← Finset.sum_mul, (FinLaw.pi _).sum_one, one_mul]
      _ ≤ _ := by
        change B ≤ (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) + B
        have hγ : 0 ≤ (T.S.n k : ℝ) ^ (-(4 * κ.R : ℝ)) := by positivity
        linarith
  · have hepos : 0 < ell := Nat.pos_of_ne_zero he0
    let π : ℕ → Law (T.S.N k) := fun j => clusterCrossLaw PT hPT hm W a ⟨j % ell, Nat.mod_lt _ hepos⟩
    have hπeq (j : Fin ell) : π j = clusterCrossLaw PT hPT hm W a j := by
      dsimp only [π]
      apply congrArg (clusterCrossLaw PT hPT hm W a)
      apply Fin.ext
      exact Nat.mod_eq_of_lt j.isLt
    have hd : ∀ j x, 0 < τ0.w x →
        |deg (T.S.E k) PT.tiling.c (π j).w x - 1 / 2| ≤ 2 * bstar T k := by
      intro j x hx
      exact (hτ0J x hx.ne').2 _ (enumerateFinset (clusterCrossingNeighbours PT hPT a)
        ⟨j % ell, Nat.mod_lt _ hepos⟩).2
    have hc := hcross PT hPT hm W hW I a τ0 hdom0 ell hell π
      (fun j _ => clusterMarginalLaw_supported PT hPT hm W _)
      (fun j _ => (hwidth PT hPT hm W).1 _) hd
    have hst (ys : Fin ell → Fin (T.S.N k))
        (hy : crossingGood (T.S.E k) PT.tiling.c τ0 π (bstar T k) ell ys) :
        (FinLaw.pi (fun l => lawToFinLaw (ν l))).pr
          (fun zs => Zmass (T.S.E k) PT.tiling.c
            (crossingState (T.S.E k) PT.tiling.c τ0 π ell ys).w (fun l => (ν l).w) zs < 3 / 4) ≤ B := by
      have hdom := crossingState_domination (T.S.E k) PT.tiling.c τ0 π (bstar T k)
        hscales.1 hscales.2.1 hd ell ys hy
      apply hBulk
      · intro x
        apply (hdom x).trans
        have hh := mul_le_mul_of_nonneg_left (hdom0 x) (show (0 : ℝ) ≤ 5 ^ ell by positivity)
        dsimp [C]
        rw [pow_succ]
        nlinarith [σ.nonneg x, show (0 : ℝ) ≤ 5 ^ ell by positivity]
      · intro x hx
        apply hτ0J
        intro hz
        have hh := hdom x
        rw [hz, mul_zero] at hh
        exact hx (le_antisymm hh ((crossingState _ _ _ _ _ _).nonneg x))
    have hscale : 20 * (ell : ℝ) * bstar T k ≤ 1 / 10 := by
      apply le_trans _ (hscales.2.2 PT hPT (patchAt PT hPT a.1))
      have hell' : (ell : ℝ) ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ := by exact_mod_cast hell
      gcongr
      exact hscales.1
    have hraw := gated_crossing_bulk_failure_le (T.S.E k) PT.tiling.c σ J hmass hgate π ν
      (bstar T k) hscales.1 hscales.2.1 hd ell hscale _ B hB hc hst
    simp_rw [hπeq] at hraw
    simpa only [σ, hSigma, ν, J, clusterRowAtCenterExternal, B, C, ell] using hraw

theorem finLaw_E_add {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (F G : Ω → ℝ) :
    P.E (fun x => F x + G x) = P.E F + P.E G := by
  simp [FinLaw.E, mul_add, Finset.sum_add_distrib]

theorem finLaw_E_affine {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (F : Ω → ℝ) (A K : ℝ) :
    P.E (fun x => A + K * F x) = A + K * P.E F := by
  simp only [FinLaw.E, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, P.sum_one, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end HypercubeRamsey.Lane_sol_s15_load
