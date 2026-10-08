import HypercubeRamsey.S15.ClusterBinScales_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelStage_sol_s15_c2
import HypercubeRamsey.S15.ClusterLabelGeometry_sol_s15_c2
import HypercubeRamsey.S15.HighCluster_opus_s15_q_s15_clock_atoms

namespace HypercubeRamsey.S15.Lane_q_s15_clock

open HypercubeRamsey HypercubeRamsey.S15 Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def extendOddLabels {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (z : OddAssignment T k) : ClusterConsultation PT → Fin (T.S.N k) :=
  fun c =>
    if h : ∃ b : OddPosition T k, Lane_sol_s15_transfer.wordAtOdd PT hPT hm b = c then
      z (Classical.choose h)
    else Classical.choose (hPT.tiling_valid.patch_nonempty c.1.1).2

private theorem extendOddLabels_at {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (z : OddAssignment T k) (b : OddPosition T k) :
    extendOddLabels PT hPT hm z (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b) = z b := by
  classical
  unfold extendOddLabels
  split_ifs with h
  · have hchoose : Classical.choose h = b :=
      Lane_sol_s15_c2.wordAtOdd_injective PT hPT hm (Classical.choose_spec h)
    rw [hchoose]
  · exact (h ⟨b, rfl⟩).elim

private theorem internalOfWordLabels_at {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : ClusterConsultation PT → Fin (T.S.N k))
    (b : OddPosition T k) :
    clusterLabelFromInternal (hPT := hPT) hm
        (Lane_sol_s15_transfer.internalOfWordLabels B ys) b =
      ys (Lane_sol_s15_transfer.wordAtOdd PT hPT hm b) := by
  rfl

private theorem oddOutputLabel {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (z : OddAssignment T k) (b : OddPosition T k) :
    clusterLabelFromInternal (hPT := hPT) hm
        (Lane_sol_s15_transfer.internalOfWordLabels B
          (extendOddLabels PT hPT hm z)) b = z b := by
  rw [internalOfWordLabels_at, extendOddLabels_at]

private noncomputable def oddLabelFinProb {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (b : OddPosition T k) : FinProb (Fin (T.S.N k)) :=
  ⟨(Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w,
    (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).nonneg,
    (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).sum_one⟩

private theorem independent_E_eq_odd_product {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (S : Finset (OddPosition T k)) (F : ClusterInternalData PT → ℝ)
    (hF : ClusterLabelDependsOn hPT hm F S) :
    (FinProb.pi (oddLabelFinProb PT hPT hm W B)).expect
        (fun z => F (Lane_sol_s15_transfer.internalOfWordLabels B
          (extendOddLabels PT hPT hm z))) =
      (clusterIndependentLabelKernel PT hPT hm W B).E F := by
  classical
  let w := Lane_sol_s15_transfer.wordAtOdd PT hPT hm
  let p : OddPosition T k → FinProb (Fin (T.S.N k)) :=
    oddLabelFinProb PT hPT hm W B
  let q : ClusterConsultation PT → FinProb (Fin (T.S.N k)) := fun c =>
    ⟨(Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B c).w,
      (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B c).nonneg,
      (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B c).sum_one⟩
  let G : (ClusterConsultation PT → Fin (T.S.N k)) → ℝ :=
    fun ys => F (Lane_sol_s15_transfer.internalOfWordLabels B ys)
  let H : (OddPosition T k → Fin (T.S.N k)) → ℝ :=
    fun z => G (extendOddLabels PT hPT hm z)
  let S' := S.image w
  let defaultOdd : OddPosition T k → Fin (T.S.N k) := fun b =>
    Classical.choose (hPT.tiling_valid.patch_nonempty (patchAt PT hPT b.1)).2
  let defaultWord : ClusterConsultation PT → Fin (T.S.N k) := fun c =>
    if h : ∃ b : OddPosition T k, w b = c then defaultOdd (Classical.choose h)
    else Classical.choose (hPT.tiling_valid.patch_nonempty c.1.1).2
  have hLaw (b : OddPosition T k) :
      (p b).w = (q (w b)).w := by
    rfl
  have hdepH : FinProb.DependsOn H S := by
    intro z z' hz
    apply hF
    intro b hb
    rw [internalOfWordLabels_at, internalOfWordLabels_at]
    rw [extendOddLabels_at, extendOddLabels_at, hz b hb]
  have hdepG : FinProb.DependsOn G S' := by
    intro ys ys' hys
    apply hF
    intro b hb
    have hw : w b ∈ S' := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hval := hys (w b) hw
    rw [internalOfWordLabels_at, internalOfWordLabels_at]
    exact hval
  have hredH := FinProb.pi_expect_depends p S H defaultOdd hdepH
  have hredG := FinProb.pi_expect_depends q S' G defaultWord hdepG
  let eOdd := Equiv.piEquivPiSubtypeProd (fun b : OddPosition T k => b ∈ S)
    (fun _ => Fin (T.S.N k))
  let eWord := Equiv.piEquivPiSubtypeProd (fun c : ClusterConsultation PT => c ∈ S')
    (fun _ => Fin (T.S.N k))
  let f : {b : OddPosition T k // b ∈ S} → {c : ClusterConsultation PT // c ∈ S'} :=
    fun b => ⟨w b.1, Finset.mem_image.mpr ⟨b.1, b.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b b' h
      apply Subtype.ext
      exact Lane_sol_s15_c2.wordAtOdd_injective PT hPT hm (congrArg Subtype.val h)
    · intro c
      obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp c.2
      exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩
  let e := Equiv.ofBijective f hf
  let ePi :
      (∀ b : {b : OddPosition T k // b ∈ S}, Fin (T.S.N k)) ≃
        (∀ c : {c : ClusterConsultation PT // c ∈ S'}, Fin (T.S.N k)) :=
    { toFun := fun a c => a (e.symm c)
      invFun := fun a b => a (e b)
      left_inv := by
        intro a
        funext b
        simp
      right_inv := by
        intro a
        funext c
        simp }
  have hReducedValue (a : ∀ b : {b : OddPosition T k // b ∈ S}, Fin (T.S.N k)) :
      H (eOdd.symm (a, fun b => defaultOdd b.1)) =
        G (eWord.symm ((fun c => a (e.symm c)),
          fun c => defaultWord c.1)) := by
    apply hdepG
    intro c hc
    obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hc
    subst c
    have hcoordOdd :
        eOdd.symm (a, fun b => defaultOdd b.1) b = a ⟨b, hb⟩ := by
      simp only [eOdd, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hb]
    have hcoordWord :
        eWord.symm ((fun c => a (e.symm c)), fun c => defaultWord c.1) (w b) =
          a ⟨b, hb⟩ := by
      have heq : e.symm ⟨w b, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩ =
          ⟨b, hb⟩ := by
        apply e.injective
        simp [e, f]
      simp only [eWord, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hc]
      rw [heq]
    calc
      extendOddLabels PT hPT hm (eOdd.symm (a, fun b => defaultOdd b.1)) (w b) =
          eOdd.symm (a, fun b => defaultOdd b.1) b :=
        extendOddLabels_at PT hPT hm _ b
      _ = a ⟨b, hb⟩ := hcoordOdd
      _ = eWord.symm ((fun c => a (e.symm c)), fun c => defaultWord c.1) (w b) :=
        hcoordWord.symm
  have hReducedWeight
      (a : ∀ b : {b : OddPosition T k // b ∈ S}, Fin (T.S.N k)) :
      (FinProb.pi (fun b : {b : OddPosition T k // b ∈ S} => p b.1)).w a =
        (FinProb.pi (fun c : {c : ClusterConsultation PT // c ∈ S'} => q c.1)).w
          (fun c => a (e.symm c)) := by
    change (∏ b : {b : OddPosition T k // b ∈ S}, (p b.1).w (a b)) =
      ∏ c : {c : ClusterConsultation PT // c ∈ S'}, (q c.1).w (a (e.symm c))
    exact Fintype.prod_equiv e _ _ (by
      intro b
      calc
        (p b.1).w (a b) = (q (w b.1)).w (a b) :=
          congrFun (hLaw b.1) (a b)
        _ = (q (e b).1).w (a (e.symm (e b))) := by
          rw [e.symm_apply_apply]
          rfl)
  have hwordConv :
      (FinProb.pi q).expect G =
        (FinLaw.pi (Lane_sol_s15_transfer.wordLabelLaw PT hPT hm W B)).E G := by
    unfold FinProb.expect FinLaw.E FinProb.pi FinLaw.pi
    rfl
  rw [Lane_sol_s15_transfer.independent_label_E_eq_word_E,
    ← hwordConv, hredH, hredG]
  unfold FinProb.expect
  rw [Fintype.sum_equiv ePi
    (fun a => (FinProb.pi (fun b : {b : OddPosition T k // b ∈ S} => p b.1)).w a *
      H (eOdd.symm (a, fun b => defaultOdd b.1)))
    (fun c => (FinProb.pi (fun c : {c : ClusterConsultation PT // c ∈ S'} => q c.1)).w c *
      G (eWord.symm (c, fun c => defaultWord c.1)))
    (by
      intro a
      change
        (FinProb.pi (fun b : {b : OddPosition T k // b ∈ S} => p b.1)).w a *
          H (eOdd.symm (a, fun b => defaultOdd b.1)) =
        (FinProb.pi (fun c : {c : ClusterConsultation PT // c ∈ S'} => q c.1)).w
            (fun c => a (e.symm c)) *
          G (eWord.symm ((fun c => a (e.symm c)), fun c => defaultWord c.1))
      rw [hReducedWeight a, hReducedValue a])]

/-- High-large mode: the S03 clock sampler applied to the odd-role label laws. -/
theorem label_clock_large (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highLarge →
    ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      clusterAlarmsAvoided PT hPT hm W → clusterHistoryLoad PT hPT hm W →
    ∀ B : ClusterBinAssignment PT, 0 < (clusterIndependentBinKernel PT hPT hm W).w B →
      clusterBinGood PT hPT hm W B →
      (∀ a, (clusterIndependentLabelKernel PT hPT hm W B).pr
        (fun I => clusterRowMass PT hPT hm W I a < 1 / 2) ≤
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2)) →
      ∃ L : FinLaw (ClusterInternalData PT),
        (∀ I, L.w I ≠ 0 → clusterBinsOfInternal I = B) ∧
        (∀ I, L.w I ≠ 0 → ∀ b,
          clusterLabelFromInternal (hPT := hPT) hm I b ∈
            (PT.tiling.P (patchAt PT hPT b.1)).Y) ∧
        (∀ I, L.w I ≠ 0 →
          Function.Injective (clusterLabelFromInternal (hPT := hPT) hm I)) ∧
        (∀ I, L.w I ≠ 0 → ∀ a,
          (1 / 2 : ℝ) ≤ clusterRowMass PT hPT hm W I a) ∧
        ∀ F : ClusterInternalData PT → ℝ, (∀ I, 0 ≤ F I) →
          ∀ S : Finset (OddPosition T k), ClusterLabelDependsOn hPT hm F S →
            (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 →
              L.E F ≤ 2 * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
  classical
  rcases hκ.clock with
    ⟨_, _, A', P', n₀, ε, hA, hP', hA_le, hP_le, hn₀, hε, hClock⟩
  have hAtoms := Lane_q_s15_clock_atoms.highLarge_label_atoms κ hκ T A' hA
  have hHost : ∀ᶠ k in atTop,
      max n₀ 2 ≤ T.S.n k ∧ LargeHost 1 (T.S.n k) (T.S.N k) := by
    exact T.S.eventually_large 1 (max n₀ 2)
  have hEps : ∀ᶠ k in atTop, ε (T.S.n k) ≤ 1 := by
    have hεcomp : Filter.Tendsto (fun k => ε (T.S.n k)) atTop (nhds 0) :=
      hε.comp T.S.n_tendsto
    exact hεcomp.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hAtoms, hHost, hEps] with k hAtoms hhost hεsmall
  intro PT hPT hm hlarge W hW hAvoid hLoad B hB hgood hmass
  let n : ℕ := T.S.n k
  let N : ℕ := T.S.N k
  have hn0 : n₀ ≤ n := by
    dsimp [n]
    exact le_trans (le_max_left _ _) hhost.1
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact le_trans (le_max_right _ _) hhost.1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnRpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hNpos : 0 < (N : ℝ) := by
    dsimp [N]
    exact_mod_cast T.S.N_pos k
  have hNpow : (2 : ℝ) ^ n ≤ (N : ℝ) := by
    have h := hhost.2.1
    dsimp [n, N]
    change (1 : ℝ) * (2 : ℝ) ^ T.S.n k ≤ (T.S.N k : ℝ) at h
    nlinarith
  have hNupper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
    dsimp [n, N]
    exact_mod_cast hhost.2.2
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hnRpos.le
  have hlogN : Real.log (N : ℝ) ≤ 2 * (n : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ) ^ n) :=
        Real.log_le_log hNpos hNupper
      _ = Real.log (n : ℝ) + (n : ℝ) * Real.log (2 : ℝ) := by
        rw [Real.log_mul hnRpos.ne'
          (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
      _ ≤ (n : ℝ) + (n : ℝ) := by
        apply add_le_add hlogn
        calc
          (n : ℝ) * Real.log (2 : ℝ) ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hlog2 hnRpos.le
          _ = (n : ℝ) := by ring
      _ = 2 * (n : ℝ) := by ring
  let Ω : OddPosition T k → Type := fun _ => Fin N
  let laws : ∀ b : OddPosition T k, FinProb (Ω b) := fun b =>
    oddLabelFinProb PT hPT hm W B b
  let lab : ∀ b : OddPosition T k, Ω b → Fin N := fun _ y => y
  have hNnat : 0 < N := T.S.N_pos k
  have hΩnonempty : ∀ b : OddPosition T k, Nonempty (Ω b) :=
    fun _ => ⟨⟨0, hNnat⟩⟩
  letI : ∀ b : OddPosition T k, Nonempty (Ω b) := hΩnonempty
  have hMarg (b : OddPosition T k) (y : Fin N) :
      labMarg (laws b) (lab b) y = (laws b).w y := by
    classical
    unfold labMarg
    simp only [lab]
    rw [Finset.sum_ite_eq']
    simp
  have hcol : ∀ y, ∑ b : OddPosition T k, labMarg (laws b) (lab b) y ≤ κ.θ0 := by
    intro y
    calc
      _ = ∑ b : OddPosition T k, (laws b).w y := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hMarg b y
      _ ≤ clusterGivenBinColumn PT hPT hm W B y :=
        Lane_sol_s15_c2.odd_label_column_le PT hPT hm W B y
      _ ≤ κ.θ0 := hgood.2.1 y
  let Bad : EvenPosition T k → (∀ b : OddPosition T k, Ω b) → Prop :=
    fun a z => clusterRowMass PT hPT hm W
        (Lane_sol_s15_transfer.internalOfWordLabels B
          (extendOddLabels PT hPT hm z)) a < 1 / 2
  let scope : EvenPosition T k → Finset (OddPosition T k) :=
    fun a => Lane_q_s15_direct.star a
  have hdep : ∀ a, FinProb.DependsOn (Bad a) (scope a) := by
    intro a z z' hz
    apply congrArg (fun x : ℝ => x < 1 / 2)
    apply (Lane_sol_s15_c2.row_mass_label_depends PT hPT hm W a)
    intro b hb
    rw [oddOutputLabel, oddOutputLabel, hz b hb]
  have hnPow5 : (n : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 : ℝ) ≤ 5)
  have honePow5 : (1 : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    calc
      (1 : ℝ) = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (0 : ℝ) ≤ 5)
  have honePow5Nat : (1 : ℝ) ≤ (n : ℝ) ^ (5 : ℕ) := by
    simpa [Real.rpow_natCast] using honePow5
  have hscope : ∀ a, ((scope a).card : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    intro a
    have hc : ((scope a).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Lane_q_s15_direct.star_card_le a
    exact hc.trans hnPow5
  have hinc : ∀ b : OddPosition T k,
      ((Finset.univ.filter fun a : EvenPosition T k => b ∈ scope a).card : ℝ) ≤
        (n : ℝ) ^ (5 : ℝ) := by
    intro b
    have hc : ((Finset.univ.filter fun a : EvenPosition T k => b ∈ scope a).card : ℝ) ≤
        (n : ℝ) := by
      change ((Lane_q_s15_direct.starIncidence b).card : ℝ) ≤ (n : ℝ)
      exact_mod_cast Lane_q_s15_direct.star_incidence_card_le b
    exact hc.trans hnPow5
  have hPstar : (κ.Pstar : ℝ) ≤ (κ.P : ℝ) := by exact_mod_cast hκ.P_big.1
  have hPge2 : 2 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hPRhalf : (κ.P : ℝ) ≤ (κ.R : ℝ) / 2 := by
    rw [hκ.R_eq, Nat.cast_pow]
    have hp : 2 ≤ (κ.P : ℝ) := by exact_mod_cast hPge2
    have hp0 : 0 ≤ (κ.P : ℝ) := by linarith
    have hprod : 0 ≤ (κ.P : ℝ) * ((κ.P : ℝ) - 2) :=
      mul_nonneg hp0 (by linarith)
    nlinarith [hprod]
  have hPexp : P' ≤ (κ.R : ℝ) / 2 := hP_le.trans (hPstar.trans hPRhalf)
  have hfail : ∀ a, (FinProb.pi laws).pr (Bad a) ≤
      (n : ℝ) ^ (-P') := by
    intro a
    let massFail : ClusterInternalData PT → Prop :=
      fun I => clusterRowMass PT hPT hm W I a < 1 / 2
    let indicator : ClusterInternalData PT → ℝ :=
      fun I => if massFail I then 1 else 0
    have hFdep : ClusterLabelDependsOn hPT hm indicator (scope a) := by
      intro I I' hI
      simp [indicator, massFail,
        Lane_sol_s15_c2.row_mass_label_depends PT hPT hm W a I I' hI]
    have hbridge := independent_E_eq_odd_product PT hPT hm W B (scope a) indicator hFdep
    have hEq :
        (FinProb.pi laws).pr (Bad a) =
          (clusterIndependentLabelKernel PT hPT hm W B).pr massFail := by
      calc
        _ = (FinProb.pi laws).expect (fun z => if Bad a z then 1 else 0) :=
          by
            classical
            simp [FinProb.pr, FinProb.expect, mul_ite]
        _ = (clusterIndependentLabelKernel PT hPT hm W B).E indicator := by
          simpa [Bad, massFail, indicator] using hbridge
        _ = _ := (Lane_sol_s15_transfer.pr_eq_E_indicator
          (clusterIndependentLabelKernel PT hPT hm W B) massFail).symm
    have hnRpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
    calc
      _ = (clusterIndependentLabelKernel PT hPT hm W B).pr massFail := hEq
      _ ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) := hmass a
      _ ≤ (n : ℝ) ^ (-P') := by
        apply Real.rpow_le_rpow_of_exponent_le hnR
        linarith
  have hRnonempty : Nonempty (OddPosition T k) := by
    let v : Position T k := fun _ => false
    have hv : IsEvenRole v := by simp [IsEvenRole, v]
    let j : Fin n := ⟨0, by omega⟩
    let w := cubeFlip v j
    have hw : ¬ IsEvenRole w := by
      intro hw
      have hnot := (cubeFlip_parity v j).mp hw
      exact hnot hv
    exact ⟨⟨w, hw⟩⟩
  letI : Nonempty (OddPosition T k) := hRnonempty
  obtain ⟨J, hGood, hComp⟩ :=
    hClock n hn0 N hlogN (fun _ y => y) laws Bad scope hcol
      (fun a y => by
        have h := hAtoms PT hPT hm hlarge W B hB a y
        calc
          labMarg (laws a) (lab a) y = (laws a).w y := hMarg a y
          _ ≤ (n : ℝ) ^ (-A') := by
            change (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B a).w y ≤
              (n : ℝ) ^ (-A')
            exact h)
      hdep hscope hinc hfail
  let out : (∀ b : OddPosition T k, Ω b) → ClusterInternalData PT :=
    fun z => Lane_sol_s15_transfer.internalOfWordLabels B
      (extendOddLabels PT hPT hm z)
  let Jlaw : FinLaw (∀ b : OddPosition T k, Ω b) :=
    ⟨J.w, J.nonneg, J.sum_eq_one⟩
  let L : FinLaw (ClusterInternalData PT) := FinLaw.map Jlaw out
  have hLift (I : ClusterInternalData PT) (hI : L.w I ≠ 0) :
      ∃ z, J.w z ≠ 0 ∧ out z = I := by
    by_contra hn
    have hz0 : ∀ z, out z = I → Jlaw.w z = 0 := by
      intro z hz
      change J.w z = 0
      by_contra hne
      exact hn ⟨z, hne, hz⟩
    have hsum : L.w I = 0 := by
      change (∑ z, if out z = I then Jlaw.w z else 0) = 0
      apply Finset.sum_eq_zero
      intro z hz
      by_cases h : out z = I
      · simp [h, hz0 z h]
      · simp [h]
    exact hI hsum
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨z, hz, rfl⟩ := hLift I hI
    rfl
  · intro I hI b
    obtain ⟨z, hz, rfl⟩ := hLift I hI
    have hsingletonCard :
        (({b} : Finset (OddPosition T k)).card : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
      simpa [Real.rpow_natCast] using honePow5Nat
    have hlabelY : z b ∈ (PT.tiling.P (patchAt PT hPT b.1)).Y := by
      by_contra hnotY
      have hzero : (laws b).w (z b) = 0 := by
        change (clusterSolver PT hPT hm (clusterGroupIndexAt PT hPT hm b).1.1).U
          (clusterGroupIndexAt PT hPT hm b).2
          (historyOnSlice W (clusterGroupIndexAt PT hPT hm b).1)
          (B (clusterGroupIndexAt PT hPT hm b)) (z b) = 0
        by_contra hne
        let g := clusterGroupIndexAt PT hPT hm b
        have hbin := (clusterSolver PT hPT hm g.1.1).U_support g.2
          (historyOnSlice W g.1) (B g) (z b) hne
        have hsub : (B g).1 ≤ (PT.tiling.P g.1.1).bins.parts.sup id :=
          Finset.le_sup (f := id) (B g).2
        have hparts :
            (PT.tiling.P g.1.1).bins.parts.sup id = (PT.tiling.P g.1.1).Y :=
          (PT.tiling.P g.1.1).bins.sup_parts
        have hy : z b ∈ (PT.tiling.P g.1.1).Y := by
          rw [← hparts]
          exact hsub hbin
        have hpatch : g.1.1 = patchAt PT hPT b.1 := rfl
        rw [hpatch] at hy
        exact hnotY hy
      have hupper := hComp {b} z hsingletonCard
      have hprob :
          J.pr (fun z' => ∀ c ∈ ({b} : Finset (OddPosition T k)), z' c = z c) ≤ 0 := by
        calc
          _ ≤ (1 + ε n) *
              ∏ c ∈ ({b} : Finset (OddPosition T k)), (laws c).w (z c) := hupper
          _ = 0 := by simp [hzero]
      have hpoint : J.w z ≤
          J.pr (fun z' => ∀ c ∈ ({b} : Finset (OddPosition T k)), z' c = z c) :=
        Lane_q_s15_direct.weight_le_pr J
          (fun z' => ∀ c ∈ ({b} : Finset (OddPosition T k)), z' c = z c) z (by simp)
      have hz0 : J.w z = 0 := le_antisymm (hpoint.trans hprob) (J.nonneg z)
      exact hz hz0
    rw [oddOutputLabel]
    exact hlabelY
  · intro I hI
    obtain ⟨z, hz, rfl⟩ := hLift I hI
    obtain ⟨hinj, _⟩ := hGood z hz
    intro b b' hEq
    rw [oddOutputLabel, oddOutputLabel] at hEq
    exact hinj hEq
  · intro I hI a
    obtain ⟨z, hz, rfl⟩ := hLift I hI
    obtain ⟨_, hAvoid⟩ := hGood z hz
    exact le_of_not_gt (hAvoid a)
  · intro F hF S hdepF hScard
    let F' : (∀ b : OddPosition T k, Ω b) → ℝ := fun z => F (out z)
    have hdepF' : FinProb.DependsOn F' S := by
      intro z z' hsame
      apply hdepF
      intro b hb
      rw [oddOutputLabel, oddOutputLabel, hsame b hb]
    have hSreal : (S.card : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
      have h2 : (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
        have h : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := hScard
        simpa [n] using h
      have h2r : (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
        simpa [Real.rpow_natCast] using h2
      have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (2 : ℝ) ≤ 5)
      exact h2r.trans hpow
    have hFnonneg : ∀ z, 0 ≤ F' z := fun z => hF (out z)
    have hbound : ∀ o : ∀ b : OddPosition T k, Ω b,
        J.pr (fun z => ∀ b ∈ S, z b = o b) ≤
          (1 + ε n) * ∏ b ∈ S, (laws b).w (o b) := by
      intro o
      exact hComp S o hSreal
    have hupper :=
      Lane_q_s15_direct.expect_le_of_cylinder hΩnonempty J laws S F' (1 + ε n)
        hFnonneg hdepF' hbound
    have hbridge := independent_E_eq_odd_product PT hPT hm W B S F hdepF
    have hRawNonneg :
        0 ≤ (clusterIndependentLabelKernel PT hPT hm W B).E F := by
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro I hI
      exact mul_nonneg
        ((clusterIndependentLabelKernel PT hPT hm W B).nonneg I) (hF I)
    have hLexp : L.E F = J.expect F' := by
      rw [Lane_q_s15_c3.finLaw_map_E]
      rfl
    calc
      L.E F = J.expect F' := hLexp
      _ ≤ (1 + ε n) * (FinProb.pi laws).expect F' := hupper
      _ = (1 + ε n) * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
        exact congrArg (fun x => (1 + ε n) * x) hbridge
      _ ≤ 2 * (clusterIndependentLabelKernel PT hPT hm W B).E F :=
        mul_le_mul_of_nonneg_right (by linarith [hεsmall]) hRawNonneg

end HypercubeRamsey.S15.Lane_q_s15_clock
