import HypercubeRamsey.S18.Nodes_sol_s18_2lm_cylinders
import HypercubeRamsey.S18.Nodes_sol_s18_2lm_parameters
import HypercubeRamsey.S18.Nodes_sol_s18_2lm_smallcyl

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.RawExceptions

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

private theorem pr_mono {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ s, A s → B s) : Q.pr A ≤ Q.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s
  · simp [ha, h s ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> simp [Q.nonneg]

private theorem pr_union {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A B : Ω → Prop) :
    Q.pr (fun s => A s ∨ B s) ≤ Q.pr A + Q.pr B := by
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s <;> by_cases hb : B s <;> simp [ha, hb, Q.nonneg s]

theorem profile_supported : (PT.π (D.geom.patchOf X.target)).SupportedIn (T.Y k) := by
  intro y hy
  apply hPT.law_supported _ y
  intro hm
  exact hy (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports _).2.2.2
    ((hPT.tiling_valid.patch_supports _).2.2.1 hm))).1

theorem profile_width (hκ : κ.Admissible) (hP : Parameters.Valid κ T k) :
    (PT.π (D.geom.patchOf X.target)).WidthLE (Parameters.profileWidth κ T k) := by
  let i := D.geom.patchOf X.target
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hbase : (PT.π i).WidthLE (Real.log 11 + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) := by
    intro y
    apply (hPT.law_cap i y).trans
    apply le_of_eq
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 11), Real.exp_log (div_pos hN hM)]
    field_simp
  apply hbase.mono
  unfold Parameters.profileWidth Parameters.patchWidth
  have hh := Lane_sol_fix_outsupp.patch_log_width hκ hPT hP.n_one i
  linarith only [hh]

theorem cylinder_cap (hκ : κ.Admissible) (hP : Parameters.Valid κ T k)
    (m : ℕ) (hm : (m : ℝ) ≤ Parameters.sizeBound κ T k)
    (mass : ℝ) (hmass : Parameters.cutoff κ T k ≤ mass)
    (y : Fin (T.S.N k)) :
    ((1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m / mass) /
      Parameters.cutoff κ T k * (PT.π (D.geom.patchOf X.target)).w y ≤
        Real.exp (κ.α * T.S.n k / 2) / T.S.N k := by
  have hε : 0 < Parameters.cutoff κ T k := Real.exp_pos _
  have hmassPos : 0 < mass := hε.trans_le hmass
  have hnum := div_le_div_of_nonneg_right (hP.tuple_density m hm) hmassPos.le
  have hden := div_le_div_of_nonneg_left (Real.exp_pos (1 : ℝ)).le hε hmass
  have hA : (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ m / mass ≤
      Real.exp 1 / Parameters.cutoff κ T k := hnum.trans hden
  have hAa := div_le_div_of_nonneg_right hA hε.le
  have hπ := profile_width (X := X) hκ hP y
  have hproduct := mul_le_mul hAa hπ ((PT.π _).nonneg y)
    (show 0 ≤ Real.exp 1 / Parameters.cutoff κ T k / Parameters.cutoff κ T k by positivity)
  apply hproduct.trans
  have he : (Real.exp 1 / Parameters.cutoff κ T k / Parameters.cutoff κ T k) *
      Real.exp (Parameters.profileWidth κ T k) =
      Real.exp (1 + Parameters.profileWidth κ T k + κ.α * T.S.n k / 4) := by
    unfold Parameters.cutoff
    rw [← Real.exp_sub, ← Real.exp_sub, ← Real.exp_add]
    congr 1; ring
  calc
    _ = ((Real.exp 1 / Parameters.cutoff κ T k / Parameters.cutoff κ T k) *
        Real.exp (Parameters.profileWidth κ T k)) / T.S.N k := by ring
    _ = Real.exp (1 + Parameters.profileWidth κ T k + κ.α * T.S.n k / 4) / T.S.N k := by rw [he]
    _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hP.width_margin])) (by positivity)

/-- A quantitative window for any selected actual critical block and any
whole-state cylinder with enough mass. -/
theorem selected_window {m : ℕ} (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (a : Fin m → Fin (T.S.n k)) (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (hm : (m : ℝ) ≤ Parameters.sizeBound κ T k)
    (C : Finset X.Raw) (hC : 0 < ∑ s ∈ C, X.rawLaw.w s)
    (hmass : Parameters.cutoff κ T k ≤ ∑ s ∈ C, X.rawLaw.w s) (pair : Bool) :
    (Witnesses.law X pair).pr (fun xz => ¬
      ((Witnesses.baseline pair - Witnesses.tolerance T k pair) ^ m - m * Parameters.additive κ T k ≤
        (FinLaw.cond X.rawLaw C hC).pr (fun s => ∀ i, Witnesses.hit X xz (X.criticalLabel s (a i))) ∧
      (FinLaw.cond X.rawLaw C hC).pr (fun s => ∀ i, Witnesses.hit X xz (X.criticalLabel s (a i))) ≤
        (Witnesses.baseline pair + Witnesses.tolerance T k pair) ^ m + m * Parameters.additive κ T k)) ≤
      Parameters.windowError κ T k := by
  have hb : 0 ≤ bstar T k := by unfold bstar; positivity
  have hp : 0 ≤ Witnesses.baseline pair ∧ Witnesses.baseline pair ≤ 1 := by
    cases pair <;> norm_num [Witnesses.baseline]
  have htol : 0 ≤ Witnesses.tolerance T k pair := by
    cases pair <;> simp [Witnesses.tolerance, hb]
  have hlo : 0 ≤ Witnesses.baseline pair - Witnesses.tolerance T k pair := by
    cases pair <;> simp only [Witnesses.baseline, Witnesses.tolerance, ↓reduceIte, Bool.false_eq_true]
    all_goals linarith [hP.bstar_small]
  have hhi : Witnesses.baseline pair + Witnesses.tolerance T k pair ≤ 1 := by
    cases pair <;> simp only [Witnesses.baseline, Witnesses.tolerance, ↓reduceIte, Bool.false_eq_true]
    all_goals linarith [hP.bstar_small]
  have hwidth : (PT.π (D.geom.patchOf X.target)).WidthLE (κ.α * T.S.n k / 2) := by
    apply (profile_width (X := X) hκ hP).mono
    have hαn : 0 ≤ κ.α * (T.S.n k : ℝ) := mul_nonneg hκ.α_rng.1.le (Nat.cast_nonneg _)
    linarith [hP.width_margin]
  have hwindow := CylinderAdapter.selected_survival_window hκ hD hgeom a ha hinj C hC
    (Witnesses.law X pair) (Witnesses.hit X) (Parameters.cutoff κ T k)
    (Parameters.discrepancyError κ T k) (Parameters.additive κ T k)
    (Witnesses.baseline pair) (Witnesses.tolerance T k pair) (κ.α * T.S.n k / 2)
    (Real.exp_pos _) (by unfold Parameters.discrepancyError; positivity) (Real.exp_pos _)
    hp htol hlo hhi profile_supported hwidth (cylinder_cap hκ hP m hm _ hmass)
    (Witnesses.broad_hit_exception hκ hdisc hP.n_one hP.pair_slack (by linarith [hP.bstar_small]) pair)
  exact hwindow.trans (hP.window_exception m hm)

/-- All relative-survival constants are explicit; the pair case uses 16mb.
The exponentially small additive error costs at most one more mb. -/
theorem selected_relative_exception {m : ℕ} (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (a : Fin m → Fin (T.S.n k)) (ha : ∀ i, a i ∈ X.criticalCoords) (hinj : Function.Injective a)
    (mstar : ℕ) (hm : m ≤ mstar) (hstar : (mstar : ℝ) ≤ Parameters.sizeBound κ T k)
    (hδ : κ.KB * (mstar : ℝ) * bstar T k < 1)
    (C : Finset X.Raw) (hC : 0 < ∑ s ∈ C, X.rawLaw.w s)
    (hmass : Parameters.cutoff κ T k ≤ ∑ s ∈ C, X.rawLaw.w s) (pair : Bool) :
    (Witnesses.law X pair).pr (fun xz => 32 * (mstar : ℝ) * bstar T k <
      |(FinLaw.cond X.rawLaw C hC).pr (fun s => ∀ i, Witnesses.hit X xz (X.criticalLabel s (a i))) /
        Witnesses.baseline pair ^ m - 1|) ≤ Parameters.windowError κ T k := by
  let p := Witnesses.baseline pair
  let b := Witnesses.tolerance T k pair
  let u := Parameters.additive κ T k
  have hp0 : 0 < p := by cases pair <;> norm_num [p, Witnesses.baseline]
  have hpLo : (1 / 4 : ℝ) ≤ p := by cases pair <;> norm_num [p, Witnesses.baseline]
  have hb0 : 0 ≤ bstar T k := by unfold bstar; positivity
  have hb : 0 ≤ b := by cases pair <;> simp [b, Witnesses.tolerance, hb0]
  have hbHi : b ≤ 2 * bstar T k := by
    cases pair <;> simp only [b, Witnesses.tolerance, ↓reduceIte, Bool.false_eq_true] <;> linarith
  have hbP : b ≤ p := by linarith [hP.bstar_small]
  have hmR : (m : ℝ) ≤ mstar := by exact_mod_cast hm
  have hroot := mul_le_mul_of_nonneg_right hmR hb0
  have hKB := mul_le_mul_of_nonneg_right hP.KB_large (show 0 ≤ (mstar : ℝ) * bstar T k by positivity)
  have hsmall : (m : ℝ) * (b / p) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_one hp0).mpr
    have hmul := mul_le_mul_of_nonneg_left hbHi (show 0 ≤ (m : ℝ) by positivity)
    nlinarith only [hmul, hroot, hKB, hδ, hpLo]
  have hms : (m : ℝ) ≤ Parameters.sizeBound κ T k := hmR.trans hstar
  have hwindow := selected_window hκ hD hgeom hP hdisc a ha hinj hms C hC hmass pair
  apply (pr_mono (Witnesses.law X pair) _ _ ?_).trans hwindow
  intro xz hbad hgood
  have hrel := Cylinder.relative_survival_window m p b u _ hp0 hb hbP (Real.exp_pos _).le hsmall hgood
  have hregular : 2 * m * b / p ≤ 16 * m * bstar T k := by
    apply (div_le_iff₀ hp0).mpr
    have h1 := mul_le_mul_of_nonneg_left hbHi (show 0 ≤ 2 * (m : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hpLo (show 0 ≤ 16 * (m : ℝ) * bstar T k by positivity)
    nlinarith only [h1, h2]
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hpLo m
  have hinv := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) m) hpower
  have hquarter : 1 / (1 / 4 : ℝ) ^ m = (4 : ℝ) ^ m := by simp [div_pow, div_div]
  rw [hquarter] at hinv
  have hmul := mul_le_mul_of_nonneg_left hinv (show 0 ≤ (m : ℝ) * u by dsimp [u, Parameters.additive]; positivity)
  have hsmallAdd := mul_le_mul_of_nonneg_left (hP.additive_small m hms) (show 0 ≤ (m : ℝ) by positivity)
  have hadd : (m : ℝ) * u / p ^ m ≤ m * bstar T k := by
    have hmul' : (m : ℝ) * u / p ^ m ≤ (m : ℝ) * u * (4 : ℝ) ^ m := by
      simpa only [div_eq_mul_inv, one_mul] using hmul
    exact hmul'.trans (by simpa only [u, mul_assoc] using hsmallAdd)
  have hroot0 : 0 ≤ (mstar : ℝ) * bstar T k := by positivity
  nlinarith only [hrel, hregular, hadd, hroot, hroot0, hbad]

noncomputable def enumeration (J : Finset (Fin (T.S.n k))) : Fin J.card ≃ J :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card J = J.card)).symm

noncomputable def coordinate (J : Finset (Fin (T.S.n k))) (i : Fin J.card) : Fin (T.S.n k) :=
  (enumeration J i).1

theorem coordinate_mem (J : Finset (Fin (T.S.n k))) (i : Fin J.card) : coordinate J i ∈ J :=
  (enumeration J i).2

theorem coordinate_injective (J : Finset (Fin (T.S.n k))) : Function.Injective (coordinate J) := by
  intro i j he
  exact (enumeration J).injective (Subtype.ext he)

theorem enumeration_all (J : Finset (Fin (T.S.n k))) (A : Fin (T.S.n k) → Prop) :
    (∀ i, A (coordinate J i)) ↔ ∀ a ∈ J, A a := by
  constructor
  · intro h a ha
    have hh := h ((enumeration J).symm ⟨a, ha⟩)
    simpa only [coordinate, Equiv.apply_symm_apply] using hh
  · intro h i
    exact h _ (coordinate_mem J i)

theorem enumerated_block_survival (a : Fin (T.S.n k)) (Q : FinLaw X.Raw)
    (xz : Fin (T.S.N k) × Option (Fin (T.S.N k))) :
    Q.pr (fun s => ∀ i, Witnesses.hit X xz
      (X.criticalLabel s (coordinate (X.criticalCoords.filter (X.sameBlock a)) i))) =
      Q.pr (Blocks.survival X a xz.1 xz.2) := by
  have hevent : (fun s => ∀ i, Witnesses.hit X xz
      (X.criticalLabel s (coordinate (X.criticalCoords.filter (X.sameBlock a)) i))) =
      Blocks.survival X a xz.1 xz.2 := by
    funext s
    apply propext
    unfold Blocks.survival
    simpa only [Witnesses.hit] using enumeration_all (X.criticalCoords.filter (X.sameBlock a))
      (fun b => Witnesses.hit X xz (X.criticalLabel s b))
  rw [hevent]

noncomputable def maxSize (X : CriticalTransferData D) : ℕ :=
  max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r

noncomputable def relativeTolerance (X : CriticalTransferData D) : ℝ :=
  32 * (maxSize X : ℝ) * bstar T k
noncomputable def multiplierTolerance (X : CriticalTransferData D) : ℝ :=
  κ.KB * (maxSize X : ℝ) * bstar T k

theorem size_bound (hκ : κ.Admissible) (hP : Parameters.Valid κ T k) :
    (maxSize X : ℝ) ≤ Parameters.sizeBound κ T k := by
  simpa only [maxSize, Nat.cast_mul, Parameters.sizeBound] using
    block_size_polylog hκ D hP.log_four (D.geom.patchOf X.target)

/-- The no-transcript denominator estimate for each actual block. -/
theorem raw_block_relative_exception (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (hδ : multiplierTolerance X < 1) (a : Fin (T.S.n k)) (pair : Bool) :
    (Witnesses.law X pair).pr (fun xz => relativeTolerance X <
      |X.rawLaw.pr (Blocks.survival X a xz.1 xz.2) /
        Witnesses.baseline pair ^ (X.criticalCoords.filter (X.sameBlock a)).card - 1|) ≤
      Parameters.windowError κ T k := by
  let J := X.criticalCoords.filter (X.sameBlock a)
  have hC : 0 < ∑ s ∈ (Finset.univ : Finset X.Raw), X.rawLaw.w s := by simp [X.rawLaw.sum_one]
  have hε : Parameters.cutoff κ T k ≤ ∑ s ∈ (Finset.univ : Finset X.Raw), X.rawLaw.w s := by
    simp only [X.rawLaw.sum_one]
    unfold Parameters.cutoff
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [hκ.α_rng.1, hP.n_one])
      _ = 1 := Real.exp_zero
  have h := selected_relative_exception hκ hD hgeom hP hdisc (coordinate J)
    (fun i => (Finset.filter_subset _ _) (coordinate_mem J i)) (coordinate_injective J)
    (maxSize X) (hgeom.block_size a) (size_bound hκ hP) hδ Finset.univ hC hε pair
  dsimp only [J] at h
  simp_rw [enumerated_block_survival a] at h
  have hcond : ∀ xz : Fin (T.S.N k) × Option (Fin (T.S.N k)), (FinLaw.cond X.rawLaw Finset.univ hC).pr (Blocks.survival X a xz.1 xz.2) =
      X.rawLaw.pr (Blocks.survival X a xz.1 xz.2) := by
    intro xz
    rw [CylinderAdapter.cond_probability]
    simp [X.rawLaw.sum_one]
  simp_rw [hcond] at h
  exact h

/-- The conditioned numerator estimate for each actual block. -/
theorem conditioned_block_relative_exception (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (hδ : multiplierTolerance X < 1) (a : Fin (T.S.n k)) (C : Finset X.Raw)
    (hC : 0 < ∑ s ∈ C, X.rawLaw.w s)
    (hε : Parameters.cutoff κ T k ≤ ∑ s ∈ C, X.rawLaw.w s) (pair : Bool) :
    (Witnesses.law X pair).pr (fun xz => relativeTolerance X <
      |(FinLaw.cond X.rawLaw C hC).pr (Blocks.survival X a xz.1 xz.2) /
        Witnesses.baseline pair ^ (X.criticalCoords.filter (X.sameBlock a)).card - 1|) ≤
      Parameters.windowError κ T k := by
  let J := X.criticalCoords.filter (X.sameBlock a)
  have h := selected_relative_exception hκ hD hgeom hP hdisc (coordinate J)
    (fun i => (Finset.filter_subset _ _) (coordinate_mem J i)) (coordinate_injective J)
    (maxSize X) (hgeom.block_size a) (size_bound hκ hP) hδ C hC hε pair
  dsimp only [J] at h
  simp_rw [enumerated_block_survival a] at h
  exact h

private theorem pr_le_one {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A : Ω → Prop) : Q.pr A ≤ 1 := by
  unfold FinLaw.pr
  calc
    _ ≤ ∑ s, Q.w s := Finset.sum_le_sum fun s _ => by split_ifs <;> simp [Q.nonneg]
    _ = 1 := Q.sum_one

theorem mean_probability {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (pair : Bool)
    (A : Fin (T.S.N k) → Option (Fin (T.S.N k)) → Ω → Prop) :
    witnessMean X pair (fun x z => if X.allowed x z then Q.pr (A x z) else 0) =
      Q.E (fun s => (Witnesses.law X pair).pr (fun xz => X.allowed xz.1 xz.2 ∧ A xz.1 xz.2 s)) := by
  have hpoint : ∀ x z, (if X.allowed x z then Q.pr (A x z) else 0) =
      Q.E (fun s => if X.allowed x z ∧ A x z s then 1 else 0) := by
    intro x z
    by_cases hx : X.allowed x z <;> simp [hx, FinLaw.E, FinLaw.pr, mul_ite]
  simp_rw [hpoint]
  rw [Witnesses.mean_expect]
  congr 1
  funext s
  have h := (Witnesses.probability_eq_mean (X := X) pair (fun x z => X.allowed x z ∧ A x z s)).symm
  convert h using 1
  congr 1
  funext x z
  by_cases hx : X.allowed x z ∧ A x z s <;> simp [hx]

/-- The raw transcript distribution averages the conditioned exceptions.
Only the small local-cylinder probability and two witness tails are paid. -/
theorem local_factor_raw_bound (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (hδ : multiplierTolerance X < 1) (P : TransferProtocol X) (hR : ReplyRangeBound P)
    (seed : P.Seed) (a : Fin (T.S.n k)) (t : ℕ) (ht : t ≤ P.steps) (pair : Bool) :
    witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
      multiplierTolerance X / 4 < |Blocks.factor P seed s t a x z - 1|) else 0) ≤
        3 * Parameters.windowError κ T k := by
  let γ := Parameters.cutoff κ T k
  let ε := Parameters.windowError κ T k
  let δ := multiplierTolerance X
  let η := relativeTolerance X
  let Small := fun s => X.rawLaw.pr (Blocks.cylinder P seed s t a) < γ
  have hb : 0 ≤ bstar T k := by unfold bstar; positivity
  have hη0 : 0 ≤ η := by dsimp [η, relativeTolerance]; positivity
  have hηδ : 4 * η ≤ δ / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hP.KB_large (show 0 ≤ (maxSize X : ℝ) * bstar T k by positivity)
    dsimp [η, δ, relativeTolerance, multiplierTolerance]
    nlinarith only [hmul]
  have hη1 : η ≤ 1 / 2 := by dsimp [δ] at hηδ; dsimp [η] at *; linarith only [hηδ, hδ]
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hpoint (s : X.Raw) : (Witnesses.law X pair).pr (fun xz => X.allowed xz.1 xz.2 ∧
      δ / 4 < |Blocks.factor P seed s t a xz.1 xz.2 - 1|) ≤
        (if Small s then 1 else 0) + 2 * ε := by
    by_cases hs : Small s
    · rw [if_pos hs]
      exact (pr_le_one _ _).trans (by linarith)
    · rw [if_neg hs, zero_add]
      let C := Finset.univ.filter (Blocks.cylinder P seed s t a)
      have hmass : γ ≤ ∑ u ∈ C, X.rawLaw.w u := by
        have hh := le_of_not_gt hs
        simpa only [Small, C, Finset.sum_filter, FinLaw.pr] using hh
      have hC : 0 < ∑ u ∈ C, X.rawLaw.w u := (Real.exp_pos _).trans_le hmass
      let F := fun (xz : Fin (T.S.N k) × Option (Fin (T.S.N k))) => (FinLaw.cond X.rawLaw C hC).pr (Blocks.survival X a xz.1 xz.2)
      let R := fun (xz : Fin (T.S.N k) × Option (Fin (T.S.N k))) => X.rawLaw.pr (Blocks.survival X a xz.1 xz.2)
      let base := Witnesses.baseline pair ^ (X.criticalCoords.filter (X.sameBlock a)).card
      let badQ := fun xz => η < |F xz / base - 1|
      let badR := fun xz => η < |R xz / base - 1|
      have hF := conditioned_block_relative_exception hκ hD hgeom hP hdisc hδ a C hC hmass pair
      have hRaw := raw_block_relative_exception hκ hD hgeom hP hdisc hδ a pair
      have hcover : ∀ xz, X.allowed xz.1 xz.2 ∧ δ / 4 < |Blocks.factor P seed s t a xz.1 xz.2 - 1| →
          badQ xz ∨ badR xz := by
        intro xz hx
        by_contra hn
        have hQ : |F xz / base - 1| ≤ η := le_of_not_gt (fun h => hn (Or.inl h))
        have hR' : |R xz / base - 1| ≤ η := le_of_not_gt (fun h => hn (Or.inr h))
        have hp : 0 < base := by
          dsimp [base]
          apply pow_pos
          cases pair <;> norm_num [Witnesses.baseline]
        have hratio := Blocks.survival_ratio_close (F xz) (R xz) base η hp hη0 hη1 hQ hR'
        have hf : F xz / R xz = Blocks.factor P seed s t a xz.1 xz.2 := by
          have hmassEq : (∑ u ∈ C, X.rawLaw.w u) = X.rawLaw.pr (Blocks.cylinder P seed s t a) := by
            unfold FinLaw.pr
            simp only [C, Finset.sum_filter]
          have hnumEq : X.rawLaw.pr (fun u => u ∈ C ∧ Blocks.survival X a xz.1 xz.2 u) =
              X.rawLaw.pr (fun u => Blocks.cylinder P seed s t a u ∧ Blocks.survival X a xz.1 xz.2 u) := by
            congr 1
            funext u
            exact propext (by simp only [C, Finset.mem_filter, Finset.mem_univ, true_and])
          dsimp [F, R]
          rw [CylinderAdapter.cond_probability, hmassEq, hnumEq]
          rfl
        rw [hf] at hratio
        linarith only [hx.2, hratio, hηδ]
      calc
        _ ≤ (Witnesses.law X pair).pr (fun xz => badQ xz ∨ badR xz) := pr_mono _ _ _ hcover
        _ ≤ (Witnesses.law X pair).pr badQ + (Witnesses.law X pair).pr badR := pr_union _ _ _
        _ ≤ ε + ε := add_le_add hF hRaw
        _ = 2 * ε := by ring
  rw [mean_probability]
  have hE : X.rawLaw.E (fun s => (Witnesses.law X pair).pr (fun xz => X.allowed xz.1 xz.2 ∧
      δ / 4 < |Blocks.factor P seed s t a xz.1 xz.2 - 1|)) ≤
      X.rawLaw.E (fun s => (if Small s then 1 else 0) + 2 * ε) := by
    unfold FinLaw.E
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpoint s) (X.rawLaw.nonneg s)
  have hEsum : X.rawLaw.E (fun s => (if Small s then 1 else 0) + 2 * ε) = X.rawLaw.pr Small + 2 * ε := by
    simp only [FinLaw.E, FinLaw.pr, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      ← Finset.sum_mul, X.rawLaw.sum_one, one_mul]
  rw [hEsum] at hE
  have hSmall := (SmallCylinder.small_local_cylinder_mass hgeom P hR seed a t ht γ (Real.exp_pos _).le).trans hP.small_cylinder
  exact hE.trans (by linarith only [hSmall])

private theorem pr_exists_finset {Ω I : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (S : Finset I) (A : I → Ω → Prop) :
    Q.pr (fun s => ∃ i ∈ S, A i s) ≤ ∑ i ∈ S, Q.pr (A i) := by
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : ∃ i ∈ S, A i s
  · simp only [if_pos hs]
    obtain ⟨i, hi, ha⟩ := hs
    calc
      _ = (if A i s then Q.w s else 0) := by rw [if_pos ha]
      _ ≤ _ := Finset.single_le_sum (s := S) (f := fun i => if A i s then Q.w s else 0)
        (fun i _ => by split_ifs <;> simp [Q.nonneg]) hi
  · simp only [hs, ↓reduceIte]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Q.nonneg]

/-- The global multiplier event is covered by local factors at two adjacent
prefixes, then averaged over raw states and independent witnesses. -/
theorem raw_exception_bound (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X) (hP : Parameters.Valid κ T k)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (hδ : multiplierTolerance X < 1) (P : TransferProtocol X) (hR : ReplyRangeBound P)
    (seed : P.Seed) (pair : Bool) (t : ℕ) (ht : t < P.steps) :
    witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr
      (fun s => factorException P seed x z s (t + 1)) else 0) ≤ Parameters.rawError κ T k := by
  let δ := multiplierTolerance X
  let F := Blocks.representatives X
  let A := fun a (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) =>
    δ / 4 < |Blocks.factor P seed s t a x z - 1| ∨
    δ / 4 < |Blocks.factor P seed s (t + 1) a x z - 1|
  have hδdef : δ = κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) *
      (D.geom.r : ℝ)) * bstar T k := by simp only [δ, multiplierTolerance, maxSize, Nat.cast_mul, mul_assoc]
  have hδ0 : 0 ≤ δ := by
    have hKB : 0 ≤ κ.KB := (by linarith [hP.KB_large])
    dsimp [δ, multiplierTolerance]
    have hb : 0 ≤ bstar T k := by unfold bstar; positivity
    positivity
  have hpoint (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
      (if X.allowed x z then X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤
      ∑ a ∈ F, if X.allowed x z then X.rawLaw.pr (A a x z) else 0 := by
    by_cases hx : X.allowed x z
    · simp only [hx, ↓reduceIte]
      apply (pr_mono X.rawLaw _ _ (fun s hs => Blocks.factor_exception_cover hgeom hsurv P seed s x z hx
        δ hδdef hδ0 hδ.le t hs)).trans
      exact pr_exists_finset _ F (fun a => A a x z)
    · simp [hx]
  have hmean := witnessMean_mono (X := X) pair _ _ hpoint
  rw [Witnesses.mean_sum] at hmean
  have hlocal (a : Fin (T.S.n k)) : witnessMean X pair (fun x z =>
      if X.allowed x z then X.rawLaw.pr (A a x z) else 0) ≤ 6 * Parameters.windowError κ T k := by
    have hboth : witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (A a x z) else 0) ≤
        witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
          δ / 4 < |Blocks.factor P seed s t a x z - 1|) else 0) +
        witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
          δ / 4 < |Blocks.factor P seed s (t + 1) a x z - 1|) else 0) := by
      rw [← witnessMean_add]
      apply witnessMean_mono
      intro x z
      by_cases hx : X.allowed x z
      · simp only [hx, ↓reduceIte]
        exact pr_union _ _ _
      · simp [hx]
    have hprev := local_factor_raw_bound hκ hD hgeom hP hdisc hδ P hR seed a t (by omega) pair
    have hnext := local_factor_raw_bound hκ hD hgeom hP hdisc hδ P hR seed a (t + 1) (by omega) pair
    linarith only [hboth, hprev, hnext]
  have hcount : F.card ≤ T.S.n k := by
    have hh := Finset.card_le_card (Finset.subset_univ F)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  calc
    _ ≤ ∑ a ∈ F, witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (A a x z) else 0) := hmean
    _ ≤ ∑ a ∈ F, 6 * Parameters.windowError κ T k := Finset.sum_le_sum fun a _ => hlocal a
    _ = (F.card : ℝ) * (6 * Parameters.windowError κ T k) := by simp
    _ ≤ (T.S.n k : ℝ) * (6 * Parameters.windowError κ T k) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (show 0 ≤ 6 * Parameters.windowError κ T k by
        unfold Parameters.windowError; positivity)
    _ = 6 * (T.S.n k : ℝ) * Parameters.windowError κ T k := by ring
    _ ≤ Parameters.rawError κ T k := hP.raw_assembly

end HypercubeRamsey.S18.Lane_sol_s18_2lm.RawExceptions
