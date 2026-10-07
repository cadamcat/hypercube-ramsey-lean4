import HypercubeRamsey.S03.Height.Scale
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.Finner

set_option maxHeartbeats 400000

/-!
# Deterministic height facts for the L3.8 selection estimates

This file contains path-maximality reductions used by the global height estimate.
-/

namespace HypercubeRamsey

namespace Lane_p_height_main

open OAI.HypercubeRamsey
open scoped symmDiff

abbrev HDState (p : HDParams) := CubeVertex p.d × ℕ

/-- One vertical-up or horizontal-down step in the multiscale height path. -/
inductive HDScaleStep {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) : HDState p → HDState p → Prop
  | up {v j} (hv : v ∈ Sites) (hj : j < p.H) (hbad : p.BadN P A E v j) :
      HDScaleStep Sites P A E (v, j) (v, j + 1)
  | down {v v' j} (hj : j < p.H) (hv' : v' ∈ Sites)
      (hstep : _root_.hammingDist v v' ≤ p.D) :
      HDScaleStep Sites P A E (v, j + 1) (v', j)

/-- The metric used to measure a scale path from its fixed starting site-level. -/
def hdScaleDistance {p : HDParams} (D : ℕ) (s t : HDState p) : ℕ :=
  max (Nat.dist s.2 t.2) ((_root_.hammingDist s.1 t.1 + max 1 D - 1) / max 1 D)

/-- A path stopped at the first exit from the metric ball of radius `R` around `origin`. -/
inductive HDScaleWalk {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (origin : HDState p) (R : ℕ) :
    HDState p → HDState p → Type
  | stop {s} (hboundary : R ≤ hdScaleDistance p.D origin s) :
      HDScaleWalk Sites P A E origin R s s
  | up {v j finish} (hinside : hdScaleDistance p.D origin (v, j) < R)
      (hv : v ∈ Sites) (hj : j < p.H) (hbad : p.BadN P A E v j)
      (tail : HDScaleWalk Sites P A E origin R (v, j + 1) finish) :
      HDScaleWalk Sites P A E origin R (v, j) finish
  | down {v v' j finish} (hinside : hdScaleDistance p.D origin (v, j + 1) < R)
      (hv' : v' ∈ Sites) (hj : j < p.H) (hstep : _root_.hammingDist v v' ≤ p.D)
      (tail : HDScaleWalk Sites P A E origin R (v', j) finish) :
      HDScaleWalk Sites P A E origin R (v, j + 1) finish

private theorem hdScaleWalk_finish_outside {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (origin : HDState p) (R : ℕ)
    {start finish : HDState p}
    (hwalk : HDScaleWalk Sites P A E origin R start finish) :
    R ≤ hdScaleDistance p.D origin finish := by
  induction hwalk with
  | stop hb => exact hb
  | up _ _ _ _ _ ih => exact ih
  | down _ _ _ _ _ ih => exact ih

/-- A stopped-path failure at scale radius `R`: the path reaches metric distance `R`
with net rise at least `-ηR`. -/
def hdScaleFailure {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (start : HDState p) (R : ℕ) (η : ℝ) : Prop :=
  ∃ finish : HDState p,
    Nonempty (HDScaleWalk Sites P A E start R start finish) ∧
    -(η * (R : ℝ)) ≤ (finish.2 : ℝ) - start.2

def hdScaleBallSiteLevels {p : HDParams} (Sites : p.Sites)
    (origin : HDState p) (R : ℕ) : Finset (CubeVertex p.d × Fin (p.H + 1)) :=
  Finset.univ.filter (fun x => x.1 ∈ Sites ∧
    hdScaleDistance p.D origin (x.1, x.2.val) < R)

/-- The concrete initial scale used in `topScale`. -/
noncomputable def heightBaseRadius (n : ℕ) : ℕ :=
  max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊

private theorem heightScaleIndex_exists (M R target : ℕ)
    (hM : 2 ≤ M) (hR : 1 ≤ R) : ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hx : 1 ≤ x := by omega
      have hstep : x + 1 ≤ 2 * x := by omega
      have hmult : 2 * x ≤ M * x := Nat.mul_le_mul_right x hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := hstep
        _ ≤ M * x := hmult
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring

/-- The rounded multiplier in the concrete scale sequence. -/
noncomputable def hdScaleMultiplier (n : ℕ) (σ : ℝ) : ℕ :=
  max 2 ⌈(n : ℝ) ^ σ⌉₊

/-- The index of the first concrete scale reaching the target scale. -/
noncomputable def hdScaleIndex (n : ℕ) (σ ζ : ℝ) : ℕ := by
  let R₀ := heightBaseRadius n
  let M := hdScaleMultiplier n σ
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  exact Nat.find (heightScaleIndex_exists M R₀ target (by dsimp [M, hdScaleMultiplier]; omega)
    (by dsimp [R₀, heightBaseRadius]; omega))

/-- The radius at a concrete scale index. -/
noncomputable def hdScaleRadius (n : ℕ) (σ : ℝ) (i : ℕ) : ℕ :=
  (hdScaleMultiplier n σ) ^ i * heightBaseRadius n

theorem topScale_eq_hdScaleRadius (n : ℕ) (σ ζ : ℝ) :
    topScale n σ ζ = hdScaleRadius n σ (hdScaleIndex n σ ζ) := by
  unfold topScale hdScaleRadius hdScaleIndex hdScaleMultiplier heightBaseRadius
  rfl

private theorem hdScaleWalk_up_or_down {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (origin : HDState p) (R : ℕ)
    {start finish : HDState p}
    (hwalk : HDScaleWalk Sites P A E origin R start finish) :
    (∃ v j, v ∈ Sites ∧ p.BadN P A E v j ∧
        hdScaleDistance p.D origin (v, j) < R) ∨
      (finish.2 ≤ start.2 ∧
        _root_.hammingDist start.1 finish.1 ≤ p.D * (start.2 - finish.2)) := by
  induction hwalk with
  | stop hboundary =>
      right
      exact ⟨le_rfl, by simp⟩
  | up hins hv hj hbad tail ih =>
      exact Or.inl ⟨_, _, hv, hbad, hins⟩
  | @down v v' j finish hins hv' hj hstep tail ih =>
      rcases ih with hUp | ⟨hlevel, hspace⟩
      · exact Or.inl hUp
      · right
        constructor
        · omega
        · calc
            _ ≤ _ + _ := _root_.hammingDist_triangle _ _ _
            _ ≤ p.D + p.D * (j - finish.2) := Nat.add_le_add hstep hspace
            _ = p.D * ((j + 1) - finish.2) := by
              have hdiff : (j + 1) - finish.2 = (j - finish.2) + 1 := by omega
              rw [hdiff, Nat.mul_add]
              omega

private theorem hdScaleFailure_has_local_bad {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (start : HDState p) (R : ℕ) (η : ℝ)
    (hD : 0 < p.D) (hR : 0 < R) (hη : η < 1)
    (hfail : hdScaleFailure Sites P A E start R η) :
    ∃ v j, v ∈ Sites ∧ p.BadN P A E v j ∧ hdScaleDistance p.D start (v, j) < R := by
  rcases hfail with ⟨finish, hwalkNonempty, hnet⟩
  let hwalk := Classical.choice hwalkNonempty
  rcases hdScaleWalk_up_or_down Sites P A E start R hwalk with hUp | ⟨hlev, hspace⟩
  · exact hUp
  · let q : ℕ := start.2 - finish.2
    have hmetric : hdScaleDistance p.D start finish ≤ q := by
      apply Nat.max_le.mpr
      constructor
      · simpa [q] using (Nat.dist_eq_sub_of_le_right hlev).le
      · have hnum : _root_.hammingDist start.1 finish.1 + p.D - 1 <
            p.D * (q + 1) := by
          rw [Nat.mul_succ]
          dsimp [q]
          omega
        have hnum' : _root_.hammingDist start.1 finish.1 + p.D - 1 <
            (q + 1) * p.D := by simpa [Nat.mul_comm] using hnum
        have hdiv := (Nat.div_lt_iff_lt_mul hD).2 hnum'
        have hdiv' :
            (_root_.hammingDist start.1 finish.1 + p.D - 1) / p.D < q + 1 := hdiv
        have hceil :
            (_root_.hammingDist start.1 finish.1 + p.D - 1) / p.D ≤ q :=
          Nat.lt_succ_iff.mp hdiv'
        simpa [hdScaleDistance, max_eq_right (Nat.one_le_iff_ne_zero.mpr hD.ne')] using hceil
    have hRfinish : R ≤ hdScaleDistance p.D start finish :=
      hdScaleWalk_finish_outside Sites P A E start R hwalk
    have hRq : R ≤ q := le_trans hRfinish hmetric
    have hnet' : (q : ℝ) ≤ η * R := by
      have hcast : (finish.2 : ℝ) - start.2 = -(q : ℝ) := by
        simp [q, Nat.cast_sub hlev]
      nlinarith [hnet, hcast]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hηR : η * (R : ℝ) < R := by nlinarith [hη, hRreal]
    have hRqReal : (R : ℝ) ≤ q := by exact_mod_cast hRq
    linarith [hnet', hηR, hRqReal]

theorem exists_nat_rpow_ge {e C : ℝ} (he : 0 < e) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → C ≤ (n : ℝ) ^ e := by
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ e) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have hEventually : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ e :=
    (Filter.tendsto_atTop.1 hpow) C
  rcases Filter.eventually_atTop.1 hEventually with ⟨n₀, hn₀⟩
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

theorem hdScaleIndex_le_ceil_inv_sigma {n : ℕ} {σ ζ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hζ : 0 < ζ ∧ ζ < 1) :
    hdScaleIndex n σ ζ ≤ ⌈1 / σ⌉₊ := by
  let k := ⌈1 / σ⌉₊
  let M := hdScaleMultiplier n σ
  let R₀ := heightBaseRadius n
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have htargetReal : (n : ℝ) ^ (1 - ζ) ≤ n := by
    have htargetRpow : (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hζ.1])
    simpa only [Real.rpow_one] using htargetRpow
  have htarget : target ≤ n := by
    dsimp [target]
    exact Nat.ceil_le.2 htargetReal
  have hceilSigma : 1 / σ ≤ (k : ℝ) := by
    dsimp [k]
    exact_mod_cast (Nat.le_ceil (1 / σ))
  have hσk : 1 ≤ σ * (k : ℝ) := by
    calc
      1 = σ * (1 / σ) := by field_simp [hσ.ne']
      _ ≤ σ * (k : ℝ) := mul_le_mul_of_nonneg_left hceilSigma hσ.le
  have hMreal : (n : ℝ) ^ σ ≤ (M : ℝ) := by
    dsimp [M, hdScaleMultiplier]
    have hceil : (n : ℝ) ^ σ ≤ (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := by
      exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ σ))
    exact hceil.trans (by exact_mod_cast (Nat.le_max_right 2 ⌈(n : ℝ) ^ σ⌉₊))
  have hpowM : (n : ℝ) ^ (σ * (k : ℝ)) ≤ (M : ℝ) ^ k := by
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _) hMreal k
    have hpowEq : (n : ℝ) ^ (σ * (k : ℝ)) = ((n : ℝ) ^ σ) ^ k :=
      Real.rpow_mul_natCast hnpos.le σ k
    calc
      (n : ℝ) ^ (σ * (k : ℝ)) = ((n : ℝ) ^ σ) ^ k := hpowEq
      _ ≤ (M : ℝ) ^ k := hpow
  have hnleMpow : (n : ℝ) ≤ (M : ℝ) ^ k := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (σ * (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 hσk
      _ ≤ (M : ℝ) ^ k := hpowM
  have hNatM : n ≤ M ^ k := by exact_mod_cast hnleMpow
  have hR₀ : 1 ≤ R₀ := by dsimp [R₀, heightBaseRadius]; omega
  have htargetScale : target ≤ M ^ k * R₀ :=
    htarget.trans (hNatM.trans (Nat.le_mul_of_pos_right _ (by omega)))
  unfold hdScaleIndex
  apply Nat.find_min'
  simpa [k, M, R₀, target, hdScaleMultiplier] using htargetScale

theorem hdScaleRadius_succ (n : ℕ) (σ : ℝ) (i : ℕ) :
    hdScaleRadius n σ (i + 1) = hdScaleMultiplier n σ * hdScaleRadius n σ i := by
  simp [hdScaleRadius, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem hdScaleIndex_spec (n : ℕ) (σ ζ : ℝ) :
    ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ hdScaleRadius n σ (hdScaleIndex n σ ζ) ∧
      ∀ i, i < hdScaleIndex n σ ζ →
        hdScaleRadius n σ i < ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by
  let R₀ := heightBaseRadius n
  let M := hdScaleMultiplier n σ
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by dsimp [M, hdScaleMultiplier]; omega
  have hR₀ : 1 ≤ R₀ := by dsimp [R₀, heightBaseRadius]; omega
  have hexists := heightScaleIndex_exists M R₀ target hM hR₀
  have hspec : target ≤ M ^ (hdScaleIndex n σ ζ) * R₀ := by
    unfold hdScaleIndex
    exact Nat.find_spec hexists
  have hminimal : ∀ i < hdScaleIndex n σ ζ, ¬ target ≤ M ^ i * R₀ := by
    intro i hi
    unfold hdScaleIndex at hi
    exact Nat.find_min hexists hi
  constructor
  · simpa [hdScaleRadius, M, R₀, target] using hspec
  · intro i hi
    apply Nat.lt_of_not_ge
    simpa [hdScaleRadius, M, R₀, target] using hminimal i hi

noncomputable def hdScaleEligibilityFraction (h i : ℕ) : ℝ :=
  1 / 4 + (i : ℝ) / (20 * ((h + 1 : ℕ) : ℝ))

noncomputable def hdScaleCrowdFraction (h i : ℕ) : ℝ :=
  3 / 5 + (3 / 20) * ((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ)

noncomputable def hdScaleSlope (h i : ℕ) : ℝ :=
  1 / 4 + ((h - i : ℕ) : ℝ) / (4 * ((h + 1 : ℕ) : ℝ))

theorem hdScaleThreshold_fractions_bounds {h i : ℕ} (hi : i ≤ h) :
    1 / 4 ≤ hdScaleEligibilityFraction h i ∧
      hdScaleEligibilityFraction h i ≤ 3 / 10 ∧
    3 / 5 ≤ hdScaleCrowdFraction h i ∧
      hdScaleCrowdFraction h i ≤ 3 / 4 ∧
    1 / 4 ≤ hdScaleSlope h i ∧ hdScaleSlope h i ≤ 1 / 2 := by
  have hden : 0 < ((h + 1 : ℕ) : ℝ) := by positivity
  have hnum : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hnumLe : (i : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_trans hi (Nat.le_succ h))
  have hratio : 0 ≤ (i : ℝ) / ((h + 1 : ℕ) : ℝ) := div_nonneg hnum hden.le
  have hratioLe : (i : ℝ) / ((h + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden).2 hnumLe
  have hnumSucc : 0 ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnumSuccLe : ((i + 1 : ℕ) : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hi
  have hratioSucc : 0 ≤ ((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) :=
    div_nonneg hnumSucc hden.le
  have hratioSuccLe : ((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden).2 hnumSuccLe
  have hremain : 0 ≤ ((h - i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hremainLe : ((h - i : ℕ) : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_trans (Nat.sub_le h i) (Nat.le_succ h))
  have hremainRatio : 0 ≤ ((h - i : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) :=
    div_nonneg hremain hden.le
  have hremainRatioLe : ((h - i : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden).2 hremainLe
  constructor
  · dsimp [hdScaleEligibilityFraction]
    exact le_add_of_nonneg_right (div_nonneg hnum (by positivity))
  constructor
  · dsimp [hdScaleEligibilityFraction]
    have hratio' : (i : ℝ) / (20 * ((h + 1 : ℕ) : ℝ)) ≤ 1 / 20 := by
      calc
        _ = (1 / 20 : ℝ) * ((i : ℝ) / ((h + 1 : ℕ) : ℝ)) := by
              field_simp [hden.ne']
        _ ≤ (1 / 20 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hratioLe (by norm_num)
        _ = 1 / 20 := by norm_num
    linarith
  constructor
  · dsimp [hdScaleCrowdFraction]
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) hnumSucc) hden.le)
  constructor
  · dsimp [hdScaleCrowdFraction]
    have hratio' : (3 / 20 : ℝ) * ((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) ≤ 3 / 20 := by
      calc
        _ = (3 / 20 : ℝ) *
            (((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ)) := by ring
        _ ≤ (3 / 20 : ℝ) * 1 := mul_le_mul_of_nonneg_left hratioSuccLe (by norm_num)
        _ = 3 / 20 := by ring
    linarith
  constructor
  · dsimp [hdScaleSlope]
    exact le_add_of_nonneg_right (div_nonneg hremain (by positivity))
  · dsimp [hdScaleSlope]
    have hratio' : ((h - i : ℕ) : ℝ) / (4 * ((h + 1 : ℕ) : ℝ)) ≤ 1 / 4 := by
      calc
        _ = (1 / 4 : ℝ) *
            (((h - i : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ)) := by ring
        _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hremainRatioLe (by norm_num)
        _ = 1 / 4 := by ring
    linarith

theorem hdScaleThreshold_fractions_strict {h i : ℕ} (hi : i ≤ h) (hi0 : 0 < i) :
    hdScaleEligibilityFraction h (i - 1) < hdScaleEligibilityFraction h i ∧
      hdScaleCrowdFraction h (i - 1) < hdScaleCrowdFraction h i ∧
      hdScaleSlope h i < hdScaleSlope h (i - 1) := by
  have hden : 0 < ((h + 1 : ℕ) : ℝ) := by positivity
  have hIndex : ((i - 1 + 1 : ℕ) : ℝ) = (i : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_of_lt hi0)
  have hIndexSub : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_of_lt hi0)
  have hrem : h - (i - 1) = (h - i) + 1 := by omega
  have hremCast : ((h - (i - 1) : ℕ) : ℝ) = ((h - i : ℕ) : ℝ) + 1 := by
    exact_mod_cast hrem
  have hs : hdScaleEligibilityFraction h (i - 1) < hdScaleEligibilityFraction h i := by
    dsimp [hdScaleEligibilityFraction]
    have hden' : 0 < 20 * ((h + 1 : ℕ) : ℝ) := by positivity
    field_simp [hden'.ne']
    nlinarith [hIndexSub]
  have ht : hdScaleCrowdFraction h (i - 1) < hdScaleCrowdFraction h i := by
    dsimp [hdScaleCrowdFraction]
    rw [hIndex]
    have hden' : 0 < ((h + 1 : ℕ) : ℝ) := hden
    field_simp [hden'.ne']
    have hsucc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by simp
    linarith [hsucc]
  have heta : hdScaleSlope h i < hdScaleSlope h (i - 1) := by
    dsimp [hdScaleSlope]
    rw [hremCast]
    have hden' : 0 < 4 * ((h + 1 : ℕ) : ℝ) := by positivity
    field_simp [hden'.ne']
    nlinarith
  exact ⟨hs, ht, heta⟩

theorem exists_nat_log_ge (C : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → C ≤ Real.log (n : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEventually : ∀ᶠ n : ℕ in Filter.atTop, C ≤ Real.log (n : ℝ) :=
    (Filter.tendsto_atTop.1 hlog) C
  rcases Filter.eventually_atTop.1 hEventually with ⟨n₀, hn₀⟩
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

/-- Every fixed positive power eventually dominates `log n`. -/
theorem log_le_rpow_eventually (e : ℝ) (he : 0 < e) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Real.log (n : ℝ) ≤ (n : ℝ) ^ e := by
  let t : ℝ := e / 2
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge (e := t) (C := t⁻¹) ht
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcoef : t⁻¹ ≤ (n : ℝ) ^ t := hN n hnN
  have hpowpos : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hnpos t
  have hlogpow : Real.log ((n : ℝ) ^ t) ≤ (n : ℝ) ^ t :=
    Real.log_le_self hpowpos.le
  have hlogeq : Real.log ((n : ℝ) ^ t) = t * Real.log (n : ℝ) :=
    Real.log_rpow hnpos t
  have hlogrewrite : Real.log (n : ℝ) = t⁻¹ * Real.log ((n : ℝ) ^ t) := by
    rw [hlogeq]
    field_simp [ht.ne']
  have hpowmul : (n : ℝ) ^ t * (n : ℝ) ^ t = (n : ℝ) ^ e := by
    calc
      (n : ℝ) ^ t * (n : ℝ) ^ t = (n : ℝ) ^ (t + t) :=
        (Real.rpow_add hnpos t t).symm
      _ = (n : ℝ) ^ e := by congr 1; dsimp [t]; ring
  calc
    Real.log (n : ℝ) = t⁻¹ * Real.log ((n : ℝ) ^ t) := hlogrewrite
    _ ≤ t⁻¹ * (n : ℝ) ^ t :=
      mul_le_mul_of_nonneg_left hlogpow (inv_nonneg.mpr ht.le)
    _ ≤ (n : ℝ) ^ t * (n : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnpos.le t)
    _ = (n : ℝ) ^ e := hpowmul

theorem heightBaseRadius_le_logsq :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (heightBaseRadius n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_log_ge 1
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hlog : 1 ≤ Real.log (n : ℝ) := hN n hnN
  have hceil : (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) ≤
      2 * (Real.log (n : ℝ)) ^ 2 :=
    Nat.ceil_le_two_mul (by nlinarith)
  have hone : (1 : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := by nlinarith
  simpa [heightBaseRadius] using (max_le hone hceil)

private theorem heightBaseRadius_times_D_le_dimension_eventually
    (D : ℕ) (c_d : ℝ) (hD : 0 < D) (hcd : 0 < c_d) :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → c_d * (n : ℝ) ≤ (d : ℝ) →
      D * heightBaseRadius n ≤ d := by
  obtain ⟨Nrad, hrad⟩ := heightBaseRadius_le_logsq
  obtain ⟨Nlog, hlog⟩ := log_le_rpow_eventually ((1 : ℝ) / 4) (by norm_num)
  let Croot : ℝ := 2 * (D : ℝ) / c_d
  have hCroot : 0 < Croot := by
    change 0 < 2 * (D : ℝ) / c_d
    exact div_pos (mul_pos (by norm_num) (by exact_mod_cast hD)) hcd
  obtain ⟨Nroot, hroot⟩ := exists_nat_rpow_ge
    (e := (1 : ℝ) / 2) (C := Croot) (by norm_num)
  let Ntail := max Nrad (max Nlog Nroot)
  let n₀ := max 2 Ntail
  refine ⟨n₀, ?_⟩
  intro n d hn hdim
  have hNtail : Ntail ≤ n := le_trans (Nat.le_max_right 2 _) hn
  have hNrad : Nrad ≤ n := le_trans (Nat.le_max_left Nrad _) hNtail
  have hNlogRoot : max Nlog Nroot ≤ n := le_trans (Nat.le_max_right Nrad _) hNtail
  have hNlog : Nlog ≤ n := le_trans (Nat.le_max_left Nlog Nroot) hNlogRoot
  have hNroot : Nroot ≤ n := le_trans (Nat.le_max_right Nlog Nroot) hNlogRoot
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogUpper : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := hlog n hNlog
  have hradUpper : (heightBaseRadius n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hrad n hNrad
  have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hquarterNonneg : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hnpos.le _
    have hpowHalf : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) =
        (n : ℝ) ^ ((1 : ℝ) / 2) := by
      calc
        _ = (n : ℝ) ^ (((1 : ℝ) / 4) + ((1 : ℝ) / 4)) :=
          (Real.rpow_add hnpos _ _).symm
        _ = _ := by congr 1 <;> norm_num
    calc
      (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hlogUpper hlogNonneg
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hlogUpper hquarterNonneg
      _ = (n : ℝ) ^ ((1 : ℝ) / 2) := hpowHalf
  have hrootValue : Croot ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := hroot n hNroot
  have hrootScaled : 2 * (D : ℝ) ≤ c_d * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hrootScaled' : 2 * (D : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * c_d := by
      apply (div_le_iff₀ hcd).1
      simpa [Croot] using hrootValue
    simpa [mul_comm] using hrootScaled'
  have hrootSquare : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
    calc
      _ = (n : ℝ) ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) := (Real.rpow_add hnpos _ _).symm
      _ = n := by norm_num [Real.rpow_one]
  have hradR0 : (heightBaseRadius n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      _ ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hradUpper
      _ ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hlogSq (by norm_num)
  have hradDim : (D : ℝ) * (heightBaseRadius n : ℝ) ≤ c_d * n := by
    calc
      _ ≤ 2 * (D : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        calc
          _ ≤ (D : ℝ) * (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hradR0 (by positivity)
          _ = _ := by ring
      _ ≤ (c_d * (n : ℝ) ^ ((1 : ℝ) / 2)) * (n : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hrootScaled (Real.rpow_nonneg hnpos.le _)
      _ = c_d * n := by
        calc
          _ = c_d * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
          _ = c_d * n := by rw [hrootSquare]
  have hradReal : ((D * heightBaseRadius n : ℕ) : ℝ) ≤ (d : ℝ) := by
    calc
      _ = (D : ℝ) * (heightBaseRadius n : ℝ) := by norm_cast
      _ ≤ c_d * n := hradDim
      _ ≤ d := hdim
  exact_mod_cast hradReal

private theorem linear_regime_hband
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (c_r : ℝ) (hcr : 0 < c_r ∧ c_r ≤ 1 / 4) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.b₀ = b₀ → p.b = b →
      n₀ ≤ p.n → c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n →
      c_r * p.d ≤ p.r ∧ 4 * p.r ≤ p.d →
      0 < p.r ∧ p.r + p.D ≤ p.d ∧
        4 * (p.n : ℝ) ^ p.b₀ *
          (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤ (p.n : ℝ) ^ p.b := by
  have hgap : 0 < b - b₀ := by linarith [hp.hb.2.1]
  let Cpow : ℝ := 4 * (1 + (D : ℝ) * (1 / c_r) ^ D)
  have hCpow : 0 < Cpow := by
    dsimp [Cpow]
    have hInv : 0 < 1 / c_r := one_div_pos.mpr hcr.1
    positivity
  obtain ⟨Npow, hNpow⟩ := exists_nat_rpow_ge (e := b - b₀) (C := Cpow) hgap
  have hcrcd : 0 < c_r * c_d := mul_pos hcr.1 hp.hd.1
  let Crad : ℝ := (D : ℝ) / (c_r * c_d)
  obtain ⟨Nrad, hNrad⟩ := exists_nat_rpow_ge (e := (1 : ℝ)) (C := Crad) (by norm_num)
  let n₀ := max 2 (max Npow Nrad)
  refine ⟨n₀, ?_⟩
  intro p hD hb₀ hb hn hdimLo hdimHi hreg
  have hn2 : 2 ≤ p.n := le_trans (le_max_left _ _) hn
  have hNinner : max Npow Nrad ≤ p.n := le_trans (le_max_right 2 _) hn
  have hNpowle : Npow ≤ p.n := le_trans (le_max_left _ _) hNinner
  have hNradle : Nrad ≤ p.n := le_trans (le_max_right _ _) hNinner
  have hnPow : Cpow ≤ (p.n : ℝ) ^ (b - b₀) := by
    exact hNpow p.n hNpowle
  have hnRad : Crad ≤ (p.n : ℝ) := by
    have h := hNrad p.n hNradle
    simpa [Crad, Real.rpow_one] using h
  have hlowDim : c_d * (p.n : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast hdimLo
  have hhighRad : c_r * (p.d : ℝ) ≤ p.r := hreg.1
  have hradLo : (D : ℝ) ≤ p.r := by
    have h1 : (D : ℝ) ≤ (c_r * c_d) * p.n := by
      dsimp [Crad] at hnRad
      have : c_r * c_d * ((D : ℝ) / (c_r * c_d)) ≤ c_r * c_d * p.n :=
        mul_le_mul_of_nonneg_left hnRad (le_of_lt hcrcd)
      have hcancel : c_r * c_d * ((D : ℝ) / (c_r * c_d)) = D := by
        field_simp [hcr.1.ne', hp.hd.1.ne']
      rw [hcancel] at this
      exact this
    have h2 : (c_r * c_d) * p.n ≤ c_r * (p.d : ℝ) := by
      calc
        (c_r * c_d) * p.n = c_r * (c_d * p.n) := by ring
        _ ≤ c_r * (p.d : ℝ) := mul_le_mul_of_nonneg_left hlowDim hcr.1.le
    exact le_trans (le_trans h1 h2) hhighRad
  have hradLoNat : D ≤ p.r := by exact_mod_cast hradLo
  have hDpos : 1 ≤ D := hp.hD
  have hradPos : 0 < p.r := by omega
  have hRadius : p.r + p.D ≤ p.d := by omega
  have hratio : (p.d : ℝ) / p.r ≤ 1 / c_r := by
    rw [div_le_div_iff₀ (by exact_mod_cast hradPos) hcr.1]
    nlinarith [hhighRad]
  have hfactor : 1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D ≤
      1 + (D : ℝ) * (1 / c_r) ^ D := by
    have hpw : ((p.d : ℝ) / p.r) ^ p.D ≤ (1 / c_r) ^ D := by
      simpa [hD] using (pow_le_pow_left₀ (by positivity) hratio p.D)
    have hDcast : (p.D : ℝ) = D := by exact_mod_cast hD
    rw [hDcast]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpw (Nat.cast_nonneg _))
  have hnpos : 0 < (p.n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (show 1 ≤ p.n by omega)
  have hpowEq : (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀) = (p.n : ℝ) ^ b := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  refine ⟨by omega, hRadius, ?_⟩
  calc
    4 * (p.n : ℝ) ^ p.b₀ *
        (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D)
        ≤ 4 * (p.n : ℝ) ^ b₀ * (1 + (D : ℝ) * (1 / c_r) ^ D) := by
          rw [hb₀]
          exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀) := by
          have h := mul_le_mul_of_nonneg_left hnPow (by positivity : 0 ≤ (p.n : ℝ) ^ b₀)
          dsimp [Cpow] at h
          nlinarith
    _ = (p.n : ℝ) ^ p.b := by simpa [hb] using hpowEq

set_option maxHeartbeats 500000 in
private theorem sublinear_regime_hband
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (ρ : ℝ) (hρ : 0 < ρ ∧ ρ < 1 ∧ b₀ + ((D : ℝ) + 1) * ρ < b) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.b₀ = b₀ → p.b = b →
      n₀ ≤ p.n → c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n →
      p.r = ⌊(p.n : ℝ) ^ (1 - ρ)⌋₊ →
      0 < p.r ∧ p.r + p.D ≤ p.d ∧
        4 * (p.n : ℝ) ^ p.b₀ *
          (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤ (p.n : ℝ) ^ p.b := by
  have hδ : 0 < b - b₀ - ρ * D := by nlinarith [hρ.2.2]
  have hcd : 0 < c_d := hp.hd.1
  have hCd : 0 < C_d := lt_of_lt_of_le hcd hp.hd.2
  let Cρ : ℝ := max (2 / c_d) (2 * (D : ℝ) / c_d)
  have hCρ : 0 < Cρ := by dsimp [Cρ]; positivity
  obtain ⟨Nρ, hNρ⟩ := exists_nat_rpow_ge (e := ρ) (C := Cρ) hρ.1
  obtain ⟨Nfloor, hNfloor⟩ := exists_nat_rpow_ge (e := 1 - ρ) (C := 2) (by linarith [hρ.2.1])
  let A : ℝ := 2 * C_d
  let Cgap : ℝ := 8 * (1 + (D : ℝ) * A ^ D)
  have hCgap : 0 < Cgap := by dsimp [Cgap, A]; positivity
  obtain ⟨Ngap, hNgap⟩ := exists_nat_rpow_ge (e := b - b₀ - ρ * D) (C := Cgap) hδ
  let n₀ := max 2 (max Nρ (max Nfloor Ngap))
  refine ⟨n₀, ?_⟩
  intro p hD hb₀ hb hn hdimLo hdimHi hrEq
  have hn2 : 2 ≤ p.n := le_trans (le_max_left _ _) hn
  have hNinner : max Nρ (max Nfloor Ngap) ≤ p.n := le_trans (le_max_right 2 _) hn
  have hNρle : Nρ ≤ p.n := le_trans (le_max_left _ _) hNinner
  have hNtail : max Nfloor Ngap ≤ p.n := le_trans (le_max_right _ _) hNinner
  have hNfloorle : Nfloor ≤ p.n := le_trans (le_max_left _ _) hNtail
  have hNgaple : Ngap ≤ p.n := le_trans (le_max_right _ _) hNtail
  have hnpos : 0 < (p.n : ℝ) := by positivity
  have hlowDim : c_d * (p.n : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast hdimLo
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (show 1 ≤ p.n by omega)
  have hpowρ : Cρ ≤ (p.n : ℝ) ^ ρ := hNρ p.n hNρle
  have hpowFloor : 2 ≤ (p.n : ℝ) ^ (1 - ρ) := hNfloor p.n hNfloorle
  have hpowGap : Cgap ≤ (p.n : ℝ) ^ (b - b₀ - ρ * D) := hNgap p.n hNgaple
  have hρLeN : (p.n : ℝ) ^ ρ ≤ p.n := by
    calc
      (p.n : ℝ) ^ ρ ≤ (p.n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 hρ.2.1.le
      _ = p.n := by rw [Real.rpow_one]
  have hCρ₁ : 2 / c_d ≤ (p.n : ℝ) ^ ρ := le_trans (le_max_left _ _) hpowρ
  have hCρ₂ : 2 * (D : ℝ) / c_d ≤ (p.n : ℝ) ^ ρ := le_trans (le_max_right _ _) hpowρ
  have hDlin : 2 * (D : ℝ) / c_d ≤ (p.n : ℝ) := le_trans hCρ₂ hρLeN
  have hDlin' : 2 * (D : ℝ) ≤ c_d * p.n := by
    calc
      2 * (D : ℝ) ≤ p.n * c_d := (div_le_iff₀ hcd).1 hDlin
      _ = c_d * p.n := by ring
  have hx : (p.n : ℝ) ^ (1 - ρ) ≤ c_d * p.n / 2 := by
    have hprodPow : (p.n : ℝ) ^ ρ * (p.n : ℝ) ^ (1 - ρ) = p.n := by
      calc
        (p.n : ℝ) ^ ρ * (p.n : ℝ) ^ (1 - ρ) =
            (p.n : ℝ) ^ (ρ + (1 - ρ)) := by rw [← Real.rpow_add hnpos]
        _ = p.n := by rw [show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
    have hmul : (p.n : ℝ) ^ (1 - ρ) * (2 / c_d) ≤ p.n := by
      calc
        (p.n : ℝ) ^ (1 - ρ) * (2 / c_d) ≤
            (p.n : ℝ) ^ (1 - ρ) * (p.n : ℝ) ^ ρ :=
              mul_le_mul_of_nonneg_left hCρ₁ (by positivity)
        _ = p.n := by rw [mul_comm, hprodPow]
    have hdiv : 2 * (p.n : ℝ) ^ (1 - ρ) / c_d ≤ p.n := by
      convert hmul using 1 <;> ring
    have hmul' : 2 * (p.n : ℝ) ^ (1 - ρ) ≤ c_d * p.n :=
      calc
        2 * (p.n : ℝ) ^ (1 - ρ) ≤ (p.n : ℝ) * c_d := (div_le_iff₀ hcd).1 hdiv
        _ = c_d * p.n := by ring
    nlinarith
  have hfloorLe : (p.r : ℝ) ≤ (p.n : ℝ) ^ (1 - ρ) := by
    rw [hrEq]
    exact Nat.floor_le (by positivity)
  have hfloorLt : (p.n : ℝ) ^ (1 - ρ) < (p.r : ℝ) + 1 := by
    rw [hrEq]
    exact Nat.lt_floor_add_one _
  have hfloorLower : (p.n : ℝ) ^ (1 - ρ) / 2 ≤ p.r := by
    nlinarith [hpowFloor, hfloorLt]
  have hradOne : (1 : ℝ) ≤ p.r := by nlinarith [hpowFloor, hfloorLower]
  have hradPos : 0 < p.r := by exact_mod_cast (show (0 : ℝ) < p.r by linarith [hradOne])
  have hRadius : p.r + p.D ≤ p.d := by
    have hsum : (p.r : ℝ) + (p.D : ℝ) ≤ c_d * p.n := by
      rw [hD]
      nlinarith [hfloorLe, hx, hDlin']
    have hsum' : ((p.r + p.D : ℕ) : ℝ) ≤ (p.d : ℝ) := by
      simpa only [Nat.cast_add] using hsum.trans hlowDim
    exact_mod_cast hsum'
  have hnr : (p.n : ℝ) / 2 ≤ (p.n : ℝ) ^ ρ * p.r := by
    have hprodPow : (p.n : ℝ) ^ ρ * (p.n : ℝ) ^ (1 - ρ) = p.n := by
      calc
        (p.n : ℝ) ^ ρ * (p.n : ℝ) ^ (1 - ρ) =
            (p.n : ℝ) ^ (ρ + (1 - ρ)) := by rw [← Real.rpow_add hnpos]
        _ = p.n := by rw [show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_left hfloorLower
      (Real.rpow_nonneg (le_of_lt hnpos) ρ)
    nlinarith [hprodPow]
  have hratio : (p.d : ℝ) / p.r ≤ A * (p.n : ℝ) ^ ρ := by
    apply (div_le_iff₀ (by exact_mod_cast hradPos)).2
    calc
      (p.d : ℝ) ≤ C_d * p.n := hdimHi
      _ ≤ 2 * C_d * ((p.n : ℝ) ^ ρ * p.r) := by nlinarith [hnr, hCd]
      _ = A * (p.n : ℝ) ^ ρ * p.r := by dsimp [A]; ring
  have hfactor : 1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D ≤
      1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) := by
    rw [hD]
    have hpow : ((p.d : ℝ) / p.r) ^ D ≤ (A * (p.n : ℝ) ^ ρ) ^ D := by
      have h := pow_le_pow_left₀ (by positivity) hratio p.D
      simpa [hD] using h
    have hterm : (A * (p.n : ℝ) ^ ρ) ^ D = A ^ D * (p.n : ℝ) ^ (ρ * D) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity) ρ D]
    calc
      1 + (D : ℝ) * ((p.d : ℝ) / p.r) ^ D ≤ 1 + (D : ℝ) *
          (A * (p.n : ℝ) ^ ρ) ^ D := add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
      _ = 1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) := by rw [hterm]; ring
  have hlarge : 1 ≤ (p.n : ℝ) ^ (ρ * D) :=
    Real.one_le_rpow hn1 (mul_nonneg hρ.1.le (Nat.cast_nonneg _))
  have hpowEq : (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀ - ρ * D) *
      (p.n : ℝ) ^ (ρ * D) = (p.n : ℝ) ^ b := by
    calc
      (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀ - ρ * D) *
          (p.n : ℝ) ^ (ρ * D) =
        (p.n : ℝ) ^ (b₀ + (b - b₀ - ρ * D)) * (p.n : ℝ) ^ (ρ * D) := by
          rw [← Real.rpow_add hnpos]
      _ = (p.n : ℝ) ^ ((b₀ + (b - b₀ - ρ * D)) + ρ * D) := by
          rw [← Real.rpow_add hnpos]
      _ = (p.n : ℝ) ^ b := by congr 1 <;> ring
  have hK : 4 * (1 + (D : ℝ) * A ^ D) ≤ (p.n : ℝ) ^ (b - b₀ - ρ * D) := by
    have hsmall : 4 * (1 + (D : ℝ) * A ^ D) ≤ Cgap := by
      dsimp [Cgap]
      nlinarith [show 0 ≤ 1 + (D : ℝ) * A ^ D by positivity]
    exact le_trans hsmall hpowGap
  have hband : 4 * (p.n : ℝ) ^ b₀ *
      (1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D)) ≤ (p.n : ℝ) ^ b := by
    have hinner : 1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) ≤
        (1 + (D : ℝ) * A ^ D) * (p.n : ℝ) ^ (ρ * D) := by
      have hcoeff : 0 ≤ (D : ℝ) * A ^ D := by positivity
      have hlinear : 1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) ≤
          (p.n : ℝ) ^ (ρ * D) + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) :=
        add_le_add hlarge le_rfl
      calc
        1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) ≤
            (p.n : ℝ) ^ (ρ * D) + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D) := hlinear
        _ = (1 + (D : ℝ) * A ^ D) * (p.n : ℝ) ^ (ρ * D) := by ring_nf
    have hscaled : 4 * (p.n : ℝ) ^ b₀ *
        ((1 + (D : ℝ) * A ^ D) * (p.n : ℝ) ^ (ρ * D)) ≤
        (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀ - ρ * D) *
          (p.n : ℝ) ^ (ρ * D) := by
      calc
        _ = (p.n : ℝ) ^ b₀ * (4 * (1 + (D : ℝ) * A ^ D)) *
              (p.n : ℝ) ^ (ρ * D) := by ring
        _ ≤ (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀ - ρ * D) *
              (p.n : ℝ) ^ (ρ * D) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg (by positivity) b₀))
                  (Real.rpow_nonneg (by positivity) (ρ * D))
    calc
      4 * (p.n : ℝ) ^ b₀ *
          (1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D)) ≤
        4 * (p.n : ℝ) ^ b₀ *
          ((1 + (D : ℝ) * A ^ D) * (p.n : ℝ) ^ (ρ * D)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ (p.n : ℝ) ^ b := by
        calc
          _ ≤ (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (b - b₀ - ρ * D) *
              (p.n : ℝ) ^ (ρ * D) := hscaled
          _ = (p.n : ℝ) ^ b := hpowEq
  refine ⟨by exact_mod_cast hradPos, hRadius, ?_⟩
  calc
    4 * (p.n : ℝ) ^ p.b₀ *
        (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤
      4 * (p.n : ℝ) ^ b₀ *
        (1 + (D : ℝ) * A ^ D * (p.n : ℝ) ^ (ρ * D)) := by
          rw [hb₀]
          exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ (p.n : ℝ) ^ p.b := by rw [hb]; exact hband

theorem height_local_geometry_eventually
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      0 < p.r ∧ p.r + p.D ≤ p.d ∧
        4 * (p.n : ℝ) ^ p.b₀ *
          (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤ (p.n : ℝ) ^ p.b := by
  cases reg with
  | lin c_r hcr =>
      obtain ⟨n₀, hlin⟩ := linear_regime_hband J₀ b₀ b σ ζ θ a c_d C_d D hp c_r hcr
      refine ⟨n₀, ?_⟩
      intro p hD hb₀ hb hn hdimLo hdimHi hreg
      apply hlin p hD hb₀ hb hn hdimLo hdimHi
      simpa [HDRegime.ok] using hreg
  | sub ρ hρ =>
      obtain ⟨n₀, hsub⟩ := sublinear_regime_hband J₀ b₀ b σ ζ θ a c_d C_d D hp ρ hρ
      refine ⟨n₀, ?_⟩
      intro p hD hb₀ hb hn hdimLo hdimHi hreg
      apply hsub p hD hb₀ hb hn hdimLo hdimHi
      simpa [HDRegime.ok] using hreg

private theorem finprob_pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · simp only [if_neg hA]
    split_ifs with hB
    · exact P.nonneg ω
    · rfl

private theorem finprob_pr_or_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  simp only [FinProb.pr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB] <;> linarith [P.nonneg ω]

private theorem finprob_pr_finset_exists_le {Ω X : Type*} [Fintype Ω]
    (P : FinProb Ω) (S : Finset X) (F : X → Ω → Prop) :
    P.pr (fun ω => ∃ x ∈ S, F x ω) ≤ ∑ x ∈ S, P.pr (F x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert x S hx ih =>
      have hEq : (fun ω => ∃ y ∈ insert x S, F y ω) =
          (fun ω => F x ω ∨ ∃ y ∈ S, F y ω) := by
        funext ω
        apply propext
        simp [hx]
      rw [hEq]
      calc
        P.pr (fun ω => F x ω ∨ ∃ y ∈ S, F y ω)
            ≤ P.pr (F x) + P.pr (fun ω => ∃ y ∈ S, F y ω) := finprob_pr_or_le _ _ _
        _ ≤ P.pr (F x) + ∑ y ∈ S, P.pr (F y) := add_le_add le_rfl ih
        _ = ∑ y ∈ insert x S, P.pr (F y) := by simp [hx, add_comm]

private theorem finprob_prod_pr_le_of_sections {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) (c : ℝ)
    (hF : ∀ a, Q.pr (F a) ≤ c) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) ≤ c := by
  classical
  have hsum : (P.prod Q).pr (fun ab => F ab.1 ab.2) =
      ∑ a, P.w a * Q.pr (F a) := by
    change (∑ ab : α × β, if F ab.1 ab.2 then P.w ab.1 * Q.w ab.2 else 0) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    change (∑ b, if F a b then P.w a * Q.w b else 0) =
      P.w a * ∑ b, if F a b then Q.w b else 0
    calc
      (∑ b, if F a b then P.w a * Q.w b else 0)
          = ∑ b, P.w a * (if F a b then Q.w b else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases h : F a b <;> simp [h]
      _ = P.w a * ∑ b, if F a b then Q.w b else 0 := by rw [Finset.mul_sum]
  calc
    (P.prod Q).pr (fun ab => F ab.1 ab.2)
        = ∑ a, P.w a * Q.pr (F a) := hsum
    _ ≤ ∑ a, P.w a * c := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hF a) (P.nonneg a)
    _ = c := by
          rw [← Finset.sum_mul, P.sum_eq_one]
          ring

private theorem finprob_pr_le_one {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) : P.pr A ≤ 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, if A ω then P.w ω else 0) ≤ ∑ ω, P.w ω := by
      apply Finset.sum_le_sum
      intro ω hω
      split_ifs <;> simp [P.nonneg ω]
    _ = 1 := P.sum_eq_one

private theorem finprob_prod_pr_eq_sections {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) = ∑ a, P.w a * Q.pr (F a) := by
  classical
  change (∑ ab : α × β, if F ab.1 ab.2 then P.w ab.1 * Q.w ab.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ b, if F a b then P.w a * Q.w b else 0) =
    P.w a * ∑ b, if F a b then Q.w b else 0
  calc
    (∑ b, if F a b then P.w a * Q.w b else 0)
        = ∑ b, P.w a * (if F a b then Q.w b else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases h : F a b <;> simp [h]
    _ = P.w a * ∑ b, if F a b then Q.w b else 0 := by rw [Finset.mul_sum]

private theorem finprob_prod_pr_le_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) (g : α → ℝ)
    (hF : ∀ a, Q.pr (F a) ≤ g a) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) ≤ P.expect g := by
  rw [finprob_prod_pr_eq_sections]
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left (hF a) (P.nonneg a)

private theorem finprob_prod_pr_left {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) :
    (P.prod Q).pr (fun ab => A ab.1) = P.pr A := by
  classical
  rw [finprob_prod_pr_eq_sections P Q (fun a _ => A a)]
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hA : A a
  · simp [hA, Q.sum_eq_one]
  · simp [hA]

private theorem finprob_prod_pr_le_bad_or_small {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (Bad : α → Prop) (F : α → β → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ a, ¬ Bad a → Q.pr (F a) ≤ δ) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) ≤ P.pr Bad + δ := by
  classical
  let g : α → ℝ := fun a => if Bad a then 1 else δ
  have hsections : ∀ a, Q.pr (F a) ≤ g a := by
    intro a
    by_cases hbad : Bad a
    · simpa [g, hbad] using finprob_pr_le_one Q (F a)
    · simpa [g, hbad] using hF a hbad
  have hexpect : P.expect g ≤ P.pr Bad + δ := by
    unfold FinProb.expect
    calc
      (∑ a, P.w a * g a) ≤
          ∑ a, P.w a * ((if Bad a then (1 : ℝ) else 0) + δ) := by
            apply Finset.sum_le_sum
            intro a ha
            by_cases hbad : Bad a
            · simp [g, hbad]
              nlinarith [P.nonneg a, hδ]
            · simp [g, hbad]
      _ = (∑ a, P.w a * (if Bad a then (1 : ℝ) else 0)) +
            ∑ a, P.w a * δ := by
              calc
                (∑ a, P.w a * ((if Bad a then (1 : ℝ) else 0) + δ))
                    = ∑ a, (P.w a * (if Bad a then (1 : ℝ) else 0) + P.w a * δ) := by
                        apply Finset.sum_congr rfl
                        intro a ha
                        rw [mul_add]
                _ = _ := Finset.sum_add_distrib
      _ = P.pr Bad + δ := by
            have hbadPr : P.pr Bad = ∑ a, P.w a * (if Bad a then (1 : ℝ) else 0) := by
              simp [FinProb.pr]
            have hδsum : (∑ a, P.w a * δ) = δ := by
              rw [← Finset.sum_mul, P.sum_eq_one]
              ring
            rw [hbadPr, hδsum]
  exact (finprob_prod_pr_le_expect P Q F g hsections).trans hexpect

private theorem bernoulli_mean_indicator (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (FinProb.bernoulli q).expect (fun b => if b then (1 : ℝ) else 0) = q := by
  have hclamp : max 0 (min q 1) = q := by
    rw [min_eq_left hq1, max_eq_right hq0]
  simp [FinProb.expect, FinProb.bernoulli, hclamp]

private theorem finprob_pi_eval_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i₀ : ι) (X : Ω i₀ → ℝ) :
    (FinProb.pi P).expect (fun ω => X (ω i₀)) = (P i₀).expect X := by
  classical
  let g : ∀ i, Ω i → ℝ := fun i x =>
    (if h : i = i₀ then X (h ▸ x) else 1) * (P i).w x
  have hprod (ω : ∀ i, Ω i) :
      (∏ i, g i (ω i)) = (∏ i, (P i).w (ω i)) * X (ω i₀) := by
    calc
      (∏ i, g i (ω i)) =
          ∏ i, (if i = i₀ then X (ω i₀) else 1) * (P i).w (ω i) := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases h : i = i₀
            · subst i
              simp [g]
            · simp [g, h]
      _ = (∏ i, if i = i₀ then X (ω i₀) else 1) *
            (∏ i, (P i).w (ω i)) := by rw [Finset.prod_mul_distrib]
      _ = _ := by
        rw [Finset.prod_ite_eq']
        simp only [Finset.mem_univ, if_true]
        ring
  have hM :
      (∏ i, ∑ x, g i x) = (∑ x, g i₀ x) := by
    rw [← Finset.insert_erase (Finset.mem_univ i₀)]
    rw [Finset.prod_insert (Finset.notMem_erase _ _)]
    have hrest : ∀ j ∈ (Finset.univ.erase i₀ : Finset ι), ∑ x, g j x = 1 := by
      intro j hj
      have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      simp [g, hjne, (P j).sum_eq_one]
    rw [Finset.prod_eq_one hrest, mul_one]
  calc
    (FinProb.pi P).expect (fun ω => X (ω i₀))
        = ∑ ω : (∀ i, Ω i), (∏ i : ι, (P i).w (ω i)) * X (ω i₀) := by
          rfl
    _ = ∑ ω : (∀ i, Ω i), ∏ i : ι, g i (ω i) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [hprod]
    _ = ∏ i : ι, ∑ x : Ω i, g i x := by rw [← Fintype.prod_sum]
    _ = ∑ x, g i₀ x := hM
    _ = (P i₀).expect X := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro x hx
          simp [g]
          ring

private theorem bernoulli_pi_all_true_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) :
    (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr
      (fun ω => ∀ i ∈ S, ω i = true) ≤ q ^ S.card := by
  classical
  let B := {i : ι // i ∈ S}
  let scope : B → Finset ι := fun b => {b.1}
  let f : B → (∀ i, Bool) → ℝ := fun b ω => if ω b.1 then 1 else 0
  have hcardB : Fintype.card B = S.card := by simp [B]
  have hdegree : ∀ i : ι, (Finset.univ.filter (fun b : B => i ∈ scope b)).card ≤ 1 := by
    intro i
    apply Finset.card_le_one_iff.mpr
    intro b b' hb hb'
    have hbm := (Finset.mem_filter.mp hb).2
    have hbval : i = b.1 := by simpa [scope] using hbm
    have hcm := (Finset.mem_filter.mp hb').2
    have hcval : i = b'.1 := by simpa [scope] using hcm
    exact Subtype.ext (hbval.symm.trans hcval)
  have hnonneg : ∀ b ω, 0 ≤ f b ω := by
    intro b ω
    by_cases h : ω b.1 <;> simp [f, h]
  have hscope : ∀ b : B, FinProb.DependsOn (f b) (scope b) := by
    intro b ω ω' hag
    dsimp [f]
    rw [hag b.1 (by simp [scope])]
  have hmean : ∀ b : B,
      (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).expect
        (fun ω => (f b ω) ^ (1 : ℕ)) = q := by
    intro b
    simp only [pow_one, f]
    rw [finprob_pi_eval_expect (fun _ : ι => FinProb.bernoulli q) b.1
      (fun x => if x then (1 : ℝ) else 0)]
    exact bernoulli_mean_indicator q hq0 hq1
  have hprodEvent : ∀ ω : ∀ i, Bool,
      (∏ b : B, f b ω) = if (∀ i ∈ S, ω i = true) then (1 : ℝ) else 0 := by
    intro ω
    by_cases he : ∀ i ∈ S, ω i = true
    · have hfactor : ∀ b : B, f b ω = 1 := by
        intro b
        simp [f, he b.1 b.2]
      have hprodone : (∏ b : B, f b ω) = 1 := by
        calc
          _ = ∏ b : B, (1 : ℝ) := Finset.prod_congr rfl (fun b _ => hfactor b)
          _ = 1 := by simp
      rw [hprodone]
      rw [if_pos he]
    · have hex : ∃ i ∈ S, ω i = false := by
        push_neg at he
        obtain ⟨i, hi, hnot⟩ := he
        have hfalse : ω i = false := by cases hω : ω i <;> simp_all
        exact ⟨i, hi, hfalse⟩
      obtain ⟨i, hi, hfalse⟩ := hex
      have hzero : f ⟨i, hi⟩ ω = 0 := by simp [f, hfalse]
      have hprodzero : (∏ b : B, f b ω) = 0 := by
        exact Finset.prod_eq_zero (s := Finset.univ) (f := fun b : B => f b ω)
          (Finset.mem_univ ⟨i, hi⟩) hzero
      rw [hprodzero]
      rw [if_neg he]
  have hprob :
      (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr
          (fun ω => ∀ i ∈ S, ω i = true) =
        (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).expect
          (fun ω => ∏ b : B, f b ω) := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    simp only [hprodEvent]
    by_cases he : ∀ i ∈ S, ω i = true <;> simp [he]
  have hmean' : ∀ b : B,
      (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).expect (fun ω => f b ω) = q := by
    intro b
    simpa only [pow_one] using hmean b
  calc
    _ = (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).expect
        (fun ω => ∏ b : B, f b ω) := hprob
    _ ≤ ∏ b : B, Real.rpow
        ((FinProb.pi (fun _ : ι => FinProb.bernoulli q)).expect
          (fun ω => (f b ω) ^ (1 : ℕ))) ((1 : ℝ)⁻¹) := by
        simpa only [Nat.cast_one] using
          (xFinner (fun _ : ι => FinProb.bernoulli q) scope 1 (by norm_num)
            hdegree f hnonneg hscope)
    _ = q ^ S.card := by simp [hmean', hcardB, Real.rpow_one]

private theorem finprob_prod_pr_and_eq_mul {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) (B : β → Prop) :
    (P.prod Q).pr (fun ab => A ab.1 ∧ B ab.2) = P.pr A * Q.pr B := by
  classical
  let qB := Q.pr B
  have hsection := finprob_prod_pr_eq_sections P Q (fun a b => A a ∧ B b)
  calc
    (P.prod Q).pr (fun ab => A ab.1 ∧ B ab.2)
        = ∑ a, P.w a * Q.pr (fun b => A a ∧ B b) := by simpa using hsection
    _
        = ∑ a, (if A a then P.w a else 0) * qB := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hA : A a <;> simp [qB, hA, FinProb.pr]
    _ = (∑ a, if A a then P.w a else 0) * qB := by rw [Finset.sum_mul]
    _ = P.pr A * Q.pr B := by simp [FinProb.pr, qB]

private theorem bernoulli_prod_pair_count_ge_prob
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (qP qA : ℝ) (hqP0 : 0 ≤ qP) (hqP1 : qP ≤ 1)
    (hqA0 : 0 ≤ qA) (hqA1 : qA ≤ 1) (T : Finset ι) (k : ℕ) :
    ((FinProb.pi (fun _ : ι => FinProb.bernoulli qP)).prod
      (FinProb.pi (fun _ : ι => FinProb.bernoulli qA))).pr
        (fun ω => k ≤ (T.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card) ≤
      (T.card : ℝ) ^ k * (qP * qA) ^ k := by
  classical
  let P : FinProb (ι → Bool) := FinProb.pi (fun _ : ι => FinProb.bernoulli qP)
  let A : FinProb (ι → Bool) := FinProb.pi (fun _ : ι => FinProb.bernoulli qA)
  let Pow : Finset (Finset ι) := T.powersetCard k
  have hcover : ∀ ω : (ι → Bool) × (ι → Bool),
      k ≤ (T.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card →
        ∃ U ∈ Pow, (∀ i ∈ U, ω.1 i = true) ∧ (∀ i ∈ U, ω.2 i = true) := by
    intro ω hk
    let C := T.filter (fun i => ω.1 i = true ∧ ω.2 i = true)
    obtain ⟨U, hUC, hUcard⟩ := Finset.exists_subset_card_eq hk
    have hUT : U ⊆ T := by
      intro i hi
      have hiC : i ∈ C := hUC hi
      exact (Finset.mem_filter.mp hiC).1
    have hUPow : U ∈ Pow := by simp [Pow, hUT, hUcard]
    refine ⟨U, hUPow, ?_, ?_⟩
    · intro i hi
      exact ((Finset.mem_filter.mp (hUC hi)).2).1
    · intro i hi
      exact ((Finset.mem_filter.mp (hUC hi)).2).2
  have hsections : ∀ U ∈ Pow,
      (P.prod A).pr (fun ω => (∀ i ∈ U, ω.1 i = true) ∧
        (∀ i ∈ U, ω.2 i = true)) ≤ (qP * qA) ^ k := by
    intro U hU
    have hUk : U.card = k := (Finset.mem_powersetCard.mp hU).2
    have hpos := bernoulli_pi_all_true_prob qP hqP0 hqP1 U
    have hact := bernoulli_pi_all_true_prob qA hqA0 hqA1 U
    have hpair := finprob_prod_pr_and_eq_mul P A
      (fun ω => ∀ i ∈ U, ω i = true) (fun ω => ∀ i ∈ U, ω i = true)
    rw [hpair]
    rw [hUk] at hpos hact
    have hact0 : 0 ≤ A.pr (fun ω => ∀ i ∈ U, ω i = true) := by
      unfold FinProb.pr
      apply Finset.sum_nonneg
      intro ω hω
      split_ifs
      · exact A.nonneg ω
      · exact le_rfl
    calc
      P.pr (fun ω => ∀ i ∈ U, ω i = true) *
          A.pr (fun ω => ∀ i ∈ U, ω i = true)
          ≤ qP ^ k * qA ^ k := mul_le_mul hpos hact hact0 (pow_nonneg hqP0 k)
      _ = (qP * qA) ^ k := by rw [mul_pow]
  have hsubset : ∀ ω : (ι → Bool) × (ι → Bool),
      k ≤ (T.filter (fun i => ω.1 i = true ∧ ω.2 i = true)).card →
        ∃ U ∈ Pow, (∀ i ∈ U, ω.1 i = true) ∧ (∀ i ∈ U, ω.2 i = true) := hcover
  calc
    _ ≤ (P.prod A).pr (fun ω =>
        ∃ U ∈ Pow, (∀ i ∈ U, ω.1 i = true) ∧ (∀ i ∈ U, ω.2 i = true)) :=
      finprob_pr_mono _ _ _ hsubset
    _ ≤ ∑ U ∈ Pow, (P.prod A).pr (fun ω =>
        (∀ i ∈ U, ω.1 i = true) ∧ (∀ i ∈ U, ω.2 i = true)) :=
      finprob_pr_finset_exists_le (P.prod A) Pow
        (fun U ω => (∀ i ∈ U, ω.1 i = true) ∧ (∀ i ∈ U, ω.2 i = true))
    _ ≤ ∑ U ∈ Pow, (qP * qA) ^ k := by
      apply Finset.sum_le_sum
      intro U hU
      exact hsections U hU
    _ = (Pow.card : ℝ) * (qP * qA) ^ k := by simp [Pow]
    _ ≤ (T.card : ℝ) ^ k * (qP * qA) ^ k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (by simpa [Pow] using Nat.choose_le_pow T.card k)

private theorem bernoulli_pi_count_ge_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Finset ι) (k : ℕ) :
    (FinProb.pi (fun _ : ι => FinProb.bernoulli q)).pr
        (fun ω => k ≤ (T.filter (fun i => ω i = true)).card) ≤
      (T.card : ℝ) ^ k * q ^ k := by
  classical
  let Q : FinProb (∀ i : ι, Bool) := FinProb.pi (fun _ : ι => FinProb.bernoulli q)
  let Pow : Finset (Finset ι) := T.powersetCard k
  have hcover : ∀ ω : ι → Bool,
      k ≤ (T.filter (fun i => ω i = true)).card →
        ∃ U ∈ Pow, ∀ i ∈ U, ω i = true := by
    intro ω hk
    let A := T.filter (fun i => ω i = true)
    obtain ⟨U, hUA, hUcard⟩ := Finset.exists_subset_card_eq hk
    have hUT : U ⊆ T := by
      intro i hi
      have hiA : i ∈ A := hUA hi
      exact (Finset.mem_filter.mp hiA).1
    have hUPow : U ∈ Pow := by
      simp [Pow, hUT, hUcard]
    refine ⟨U, hUPow, ?_⟩
    intro i hi
    have hiA : i ∈ A := hUA hi
    exact (Finset.mem_filter.mp hiA).2
  have hsubset : ∀ ω : ι → Bool,
      (k ≤ (T.filter (fun i => ω i = true)).card) →
        ∃ U ∈ Pow, ∀ i ∈ U, ω i = true := hcover
  have hsections : ∀ U ∈ Pow,
      Q.pr (fun ω => ∀ i ∈ U, ω i = true) ≤ q ^ k := by
    intro U hU
    have hUk : U.card = k := (Finset.mem_powersetCard.mp hU).2
    simpa [Q, hUk] using bernoulli_pi_all_true_prob q hq0 hq1 U
  have hpow : Pow.card ≤ T.card ^ k := by
    simpa [Pow] using Nat.choose_le_pow T.card k
  calc
    Q.pr (fun ω => k ≤ (T.filter (fun i => ω i = true)).card)
        ≤ Q.pr (fun ω => ∃ U ∈ Pow, ∀ i ∈ U, ω i = true) :=
          finprob_pr_mono _ _ _ hsubset
    _ ≤ ∑ U ∈ Pow, Q.pr (fun ω => ∀ i ∈ U, ω i = true) :=
          finprob_pr_finset_exists_le Q Pow (fun U ω => ∀ i ∈ U, ω i = true)
    _ ≤ ∑ U ∈ Pow, q ^ k := by
          apply Finset.sum_le_sum
          intro U hU
          exact hsections U hU
    _ = (Pow.card : ℝ) * q ^ k := by simp [Pow]
    _ ≤ (T.card : ℝ) ^ k * q ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hpow

private theorem position_count_ge_prob_bound {p : HDParams}
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1)
    (T : Finset p.Loc) (k : ℕ) :
    p.posLaw.pr (fun P => k ≤ (T.filter (fun ℓ => P ℓ = true)).card) ≤
      (T.card : ℝ) ^ k * (p.lam / (p.V : ℝ)) ^ k := by
  simpa [HDParams.posLaw] using
    bernoulli_pi_count_ge_prob (p.lam / (p.V : ℝ)) hq0 hq1 T k

private theorem activation_count_ge_prob_bound {p : HDParams}
    (hq0 : 0 ≤ (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (T : Finset p.Loc) (k : ℕ) :
    p.actLaw.pr (fun A => k ≤ (T.filter (fun ℓ => A ℓ = true)).card) ≤
      (T.card : ℝ) ^ k * ((p.n : ℝ) ^ p.b₀ / p.lam) ^ k := by
  simpa [HDParams.actLaw] using
    bernoulli_pi_count_ge_prob ((p.n : ℝ) ^ p.b₀ / p.lam) hq0 hq1 T k

private theorem position_overlap_union_bound {p : HDParams}
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1)
    (O : Finset (Finset p.Loc)) (k : ℕ) :
    p.posLaw.pr (fun P => ∃ T ∈ O, k ≤ (T.filter (fun ℓ => P ℓ = true)).card) ≤
      ∑ T ∈ O, (T.card : ℝ) ^ k * (p.lam / (p.V : ℝ)) ^ k := by
  calc
    _ ≤ ∑ T ∈ O, p.posLaw.pr (fun P => k ≤ (T.filter (fun ℓ => P ℓ = true)).card) :=
      finprob_pr_finset_exists_le p.posLaw O
        (fun T P => k ≤ (T.filter (fun ℓ => P ℓ = true)).card)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro T hT
      exact position_count_ge_prob_bound hq0 hq1 T k

private theorem activation_overlap_union_bound {p : HDParams}
    (hq0 : 0 ≤ (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (O : Finset (Finset p.Loc)) (k : ℕ) :
    p.actLaw.pr (fun A => ∃ T ∈ O, k ≤ (T.filter (fun ℓ => A ℓ = true)).card) ≤
      ∑ T ∈ O, (T.card : ℝ) ^ k * ((p.n : ℝ) ^ p.b₀ / p.lam) ^ k := by
  calc
    _ ≤ ∑ T ∈ O, p.actLaw.pr (fun A => k ≤ (T.filter (fun ℓ => A ℓ = true)).card) :=
      finprob_pr_finset_exists_le p.actLaw O
        (fun T A => k ≤ (T.filter (fun ℓ => A ℓ = true)).card)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro T hT
      exact activation_count_ge_prob_bound hq0 hq1 T k

private theorem active_count_ge_prob_bound {p : HDParams}
    (hqP0 : 0 ≤ p.lam / (p.V : ℝ)) (hqP1 : p.lam / (p.V : ℝ) ≤ 1)
    (hqA0 : 0 ≤ (p.n : ℝ) ^ p.b₀ / p.lam)
    (hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (T : Finset p.Loc) (k : ℕ) :
    (p.posLaw.prod p.actLaw).pr (fun ω =>
      k ≤ (T.filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card) ≤
      (T.card : ℝ) ^ k *
        (p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) ^ k := by
  simpa [HDParams.posLaw, HDParams.actLaw] using
    bernoulli_prod_pair_count_ge_prob (p.lam / (p.V : ℝ))
      ((p.n : ℝ) ^ p.b₀ / p.lam) hqP0 hqP1 hqA0 hqA1 T k

private theorem position_overlap_union_bound_of_volume {p : HDParams}
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1)
    (hVpos : 0 < (p.V : ℝ)) (hlam : 0 ≤ p.lam)
    (O : Finset (Finset p.Loc)) (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hvol : ∀ T ∈ O, (T.card : ℝ) ≤ (p.V : ℝ) * ρ) :
    p.posLaw.pr (fun P => ∃ T ∈ O, k ≤ (T.filter (fun ℓ => P ℓ = true)).card) ≤
      (O.card : ℝ) * (p.lam * ρ) ^ k := by
  have hterms : ∀ T ∈ O,
      (T.card : ℝ) ^ k * (p.lam / (p.V : ℝ)) ^ k ≤ (p.lam * ρ) ^ k := by
    intro T hT
    have hmean : (T.card : ℝ) * (p.lam / (p.V : ℝ)) ≤ p.lam * ρ := by
      calc
        (T.card : ℝ) * (p.lam / (p.V : ℝ)) ≤
            ((p.V : ℝ) * ρ) * (p.lam / (p.V : ℝ)) :=
          mul_le_mul_of_nonneg_right (hvol T hT) hq0
        _ = p.lam * ρ := by field_simp [ne_of_gt hVpos] <;> ring
    rw [← mul_pow]
    exact pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) hq0) hmean k
  calc
    _ ≤ ∑ T ∈ O, (T.card : ℝ) ^ k * (p.lam / (p.V : ℝ)) ^ k :=
      position_overlap_union_bound hq0 hq1 O k
    _ ≤ ∑ T ∈ O, (p.lam * ρ) ^ k := by
      apply Finset.sum_le_sum
      intro T hT
      exact hterms T hT
    _ = (O.card : ℝ) * (p.lam * ρ) ^ k := by simp

private theorem active_overlap_union_bound_of_volume {p : HDParams}
    (hqP0 : 0 ≤ p.lam / (p.V : ℝ)) (hqP1 : p.lam / (p.V : ℝ) ≤ 1)
    (hqA0 : 0 ≤ (p.n : ℝ) ^ p.b₀ / p.lam)
    (hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (hVpos : 0 < (p.V : ℝ)) (hlampos : 0 < p.lam)
    (hpow0 : 0 ≤ (p.n : ℝ) ^ p.b₀)
    (O : Finset (Finset p.Loc)) (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hvol : ∀ T ∈ O, (T.card : ℝ) ≤ (p.V : ℝ) * ρ) :
    (p.posLaw.prod p.actLaw).pr (fun ω => ∃ T ∈ O,
      k ≤ (T.filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card) ≤
        (O.card : ℝ) * ((p.n : ℝ) ^ p.b₀ * ρ) ^ k := by
  have hterms : ∀ T ∈ O,
      (T.card : ℝ) ^ k *
          (p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) ^ k ≤
        ((p.n : ℝ) ^ p.b₀ * ρ) ^ k := by
    intro T hT
    have hrate : p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) =
        (p.n : ℝ) ^ p.b₀ / (p.V : ℝ) := by
      field_simp [hlampos.ne', ne_of_gt hVpos]
    have hmean : (T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) ≤
        (p.n : ℝ) ^ p.b₀ * ρ := by
      calc
        (T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) ≤
            ((p.V : ℝ) * ρ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) :=
          mul_le_mul_of_nonneg_right (hvol T hT) (div_nonneg hpow0 hVpos.le)
        _ = (p.n : ℝ) ^ p.b₀ * ρ := by field_simp [ne_of_gt hVpos] <;> ring
    rw [hrate, ← mul_pow]
    exact pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hpow0 hVpos.le)) hmean k
  calc
    _ ≤ ∑ T ∈ O, (p.posLaw.prod p.actLaw).pr (fun ω =>
        k ≤ (T.filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card) :=
          finprob_pr_finset_exists_le (p.posLaw.prod p.actLaw) O
            (fun T ω => k ≤ (T.filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card)
    _ ≤ ∑ T ∈ O, (T.card : ℝ) ^ k *
        (p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) ^ k := by
          apply Finset.sum_le_sum
          intro T hT
          exact active_count_ge_prob_bound hqP0 hqP1 hqA0 hqA1 T k
    _ ≤ ∑ T ∈ O, ((p.n : ℝ) ^ p.b₀ * ρ) ^ k := by
          apply Finset.sum_le_sum
          intro T hT
          exact hterms T hT
    _ = (O.card : ℝ) * ((p.n : ℝ) ^ p.b₀ * ρ) ^ k := by simp

/-- A legal-size set has exponentially small probability of being entirely inactive.
The bound is uniform in the set, so it remains valid after the eligibility map is
chosen from positions and independent auxiliary data. -/
theorem activation_hole_prob {p : HDParams} (E : Finset p.Loc)
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => ∀ ℓ ∈ E, A ℓ = false) ≤
      Real.exp (-((E.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) := by
  classical
  let q : ℝ := (p.n : ℝ) ^ p.b₀ / p.lam
  let X : p.Loc → Bool → ℝ := fun ℓ b =>
    if ℓ ∈ E then if b then 1 else 0 else 0
  have hX : ∀ ℓ b, 0 ≤ X ℓ b ∧ X ℓ b ≤ 1 := by
    intro ℓ b
    by_cases hℓ : ℓ ∈ E <;> cases b <;> simp [X, hℓ]
  have hcoord : ∀ ℓ, (FinProb.bernoulli q).expect (X ℓ) =
      if ℓ ∈ E then q else 0 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ E
    · simpa [X, hℓ] using bernoulli_mean_indicator q hq0.le hq1
    · simp [X, hℓ, FinProb.expect]
  have hμ : (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ)) = (E.card : ℝ) * q := by
    calc
      (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ))
          = ∑ ℓ, if ℓ ∈ E then q else 0 := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact hcoord ℓ
      _ = (E.card : ℝ) * q := by simp
  have htail := xChernoff_lower (fun _ : p.Loc => FinProb.bernoulli q)
    X hX 1 (by norm_num) (by norm_num)
  have hsubset : ∀ A : p.Loc → Bool, (∀ ℓ ∈ E, A ℓ = false) →
      ∑ ℓ, X ℓ (A ℓ) ≤ 0 := by
    intro A hA
    have hsum : ∑ ℓ, X ℓ (A ℓ) = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      by_cases hEℓ : ℓ ∈ E
      · simp [X, hEℓ, hA ℓ hEℓ]
      · simp [X, hEℓ]
    rw [hsum]
  have hbound : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun A => ∀ ℓ ∈ E, A ℓ = false) ≤ Real.exp (-((E.card : ℝ) * q) / 2) := by
    calc
      _ ≤ (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
          (fun A => ∑ ℓ, X ℓ (A ℓ) ≤ 0) := finprob_pr_mono _ _ _ hsubset
      _ ≤ Real.exp (-((E.card : ℝ) * q) / 2) := by
          simpa [hμ] using htail
  simpa [HDParams.actLaw, q] using hbound

/-- Multiplicative Chernoff tail for a fixed set of prospective centers under the
independent activation law. -/
theorem activation_count_upper {p : HDParams} (T : Finset p.Loc) (δ : ℝ)
    (hδ : 0 ≤ δ) (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A =>
      (1 + δ) * (T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
        ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) ≤
      Real.exp (-((T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) * δ ^ 2 / (2 + δ)) := by
  classical
  let q : ℝ := (p.n : ℝ) ^ p.b₀ / p.lam
  let X : p.Loc → Bool → ℝ := fun ℓ b => if ℓ ∈ T ∧ b = true then 1 else 0
  have hX : ∀ ℓ b, 0 ≤ X ℓ b ∧ X ℓ b ≤ 1 := by
    intro ℓ b
    by_cases hℓ : ℓ ∈ T <;> cases b <;> simp [X, hℓ]
  have hcoord : ∀ ℓ, (FinProb.bernoulli q).expect (X ℓ) =
      if ℓ ∈ T then q else 0 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · simpa [X, hℓ] using bernoulli_mean_indicator q hq0.le hq1
    · simp [X, hℓ, FinProb.expect]
  have hμ : (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ)) = (T.card : ℝ) * q := by
    calc
      (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ))
          = ∑ ℓ, if ℓ ∈ T then q else 0 := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact hcoord ℓ
      _ = (T.card : ℝ) * q := by simp
  have htail := xChernoff_upper (fun _ : p.Loc => FinProb.bernoulli q) X hX δ hδ
  have hbound : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun A => (1 + δ) * (T.card : ℝ) * q ≤ ∑ ℓ, X ℓ (A ℓ)) ≤
      Real.exp (-((T.card : ℝ) * q) * δ ^ 2 / (2 + δ)) := by
    simpa [hμ, mul_assoc] using htail
  simpa [HDParams.actLaw, q, X] using hbound

/-- Lower and upper multiplicative tails for the prospective-position count in a
fixed finite region. -/
theorem position_count_tails {p : HDParams} (T : Finset p.Loc)
    (hq0 : 0 < p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1) :
    (p.posLaw.pr (fun P =>
      (∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0) ≤
        (T.card : ℝ) * (p.lam / (p.V : ℝ)) / 2) ≤
        Real.exp (-((T.card : ℝ) * (p.lam / (p.V : ℝ))) / 8)) ∧
    (p.posLaw.pr (fun P =>
      2 * (T.card : ℝ) * (p.lam / (p.V : ℝ)) <
        ∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0) ≤
        Real.exp (-((T.card : ℝ) * (p.lam / (p.V : ℝ))) / 3)) := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let X : p.Loc → Bool → ℝ := fun ℓ b => if ℓ ∈ T ∧ b = true then 1 else 0
  have hX : ∀ ℓ b, 0 ≤ X ℓ b ∧ X ℓ b ≤ 1 := by
    intro ℓ b
    by_cases hℓ : ℓ ∈ T <;> cases b <;> simp [X, hℓ]
  have hcoord : ∀ ℓ, (FinProb.bernoulli q).expect (X ℓ) =
      if ℓ ∈ T then q else 0 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · simpa [X, hℓ] using bernoulli_mean_indicator q hq0.le hq1
    · simp [X, hℓ, FinProb.expect]
  have hμ : (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ)) = (T.card : ℝ) * q := by
    calc
      (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ))
          = ∑ ℓ, if ℓ ∈ T then q else 0 := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact hcoord ℓ
      _ = (T.card : ℝ) * q := by simp
  have hlowRaw := xChernoff_lower (fun _ : p.Loc => FinProb.bernoulli q)
    X hX (1 / 2) (by norm_num) (by norm_num)
  have hhighRaw := xChernoff_upper (fun _ : p.Loc => FinProb.bernoulli q)
    X hX 1 (by norm_num)
  have hlow : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun P => ∑ ℓ, X ℓ (P ℓ) ≤ (T.card : ℝ) * q / 2) ≤
      Real.exp (-((T.card : ℝ) * q) / 8) := by
    norm_num at hlowRaw
    have hEvent : (fun P : p.Loc → Bool =>
        (∑ ℓ, X ℓ (P ℓ)) ≤ (T.card : ℝ) * q / 2) =
        (fun P => (∑ ℓ, X ℓ (P ℓ)) ≤ (1 / 2 : ℝ) * (q * (T.card : ℝ))) := by
      funext P
      apply propext
      constructor <;> intro h <;> nlinarith
    have hExp : -((T.card : ℝ) * q) / 8 =
        -((1 / 4 : ℝ) * (q * (T.card : ℝ))) / 2 := by
      norm_num
      ring
    rw [hEvent, hExp]
    simpa [hμ, mul_assoc, mul_comm, mul_left_comm] using hlowRaw
  have hhigh : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun P => 2 * (T.card : ℝ) * q < ∑ ℓ, X ℓ (P ℓ)) ≤
      Real.exp (-((T.card : ℝ) * q) / 3) := by
    have hsub : ∀ P : p.Loc → Bool,
        (2 * (T.card : ℝ) * q < ∑ ℓ, X ℓ (P ℓ)) →
          (1 + 1) * ((T.card : ℝ) * q) ≤ ∑ ℓ, X ℓ (P ℓ) := by
      intro P hP
      nlinarith
    calc
      _ ≤ (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
          (fun P => (1 + 1) * ((T.card : ℝ) * q) ≤ ∑ ℓ, X ℓ (P ℓ)) :=
            finprob_pr_mono _ _ _ hsub
      _ ≤ Real.exp (-((T.card : ℝ) * q) / 3) := by
            norm_num at hhighRaw ⊢
            simpa [hμ, mul_assoc, mul_comm, mul_left_comm] using hhighRaw
  constructor
  · simpa [HDParams.posLaw, q, X, mul_div_assoc] using hlow
  · simpa [HDParams.posLaw, q, X, mul_div_assoc] using hhigh

/-- A sharper upper tail at the fixed factor `3/2`, used with a `3/4` crowd
threshold in the relaxed scale-zero estimate. -/
theorem position_count_upper_three_halves {p : HDParams} (T : Finset p.Loc)
    (hq0 : 0 < p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => (3 / 2 : ℝ) * (T.card : ℝ) * (p.lam / (p.V : ℝ)) <
      ∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0) ≤
        Real.exp (-((T.card : ℝ) * (p.lam / (p.V : ℝ))) / 10) := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let X : p.Loc → Bool → ℝ := fun ℓ b => if ℓ ∈ T ∧ b = true then 1 else 0
  have hX : ∀ ℓ b, 0 ≤ X ℓ b ∧ X ℓ b ≤ 1 := by
    intro ℓ b
    by_cases hℓ : ℓ ∈ T <;> cases b <;> simp [X, hℓ]
  have hcoord : ∀ ℓ, (FinProb.bernoulli q).expect (X ℓ) =
      if ℓ ∈ T then q else 0 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · simpa [X, hℓ] using bernoulli_mean_indicator q hq0.le hq1
    · simp [X, hℓ, FinProb.expect]
  have hμ : (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ)) = (T.card : ℝ) * q := by
    calc
      (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ))
          = ∑ ℓ, if ℓ ∈ T then q else 0 := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              exact hcoord ℓ
      _ = (T.card : ℝ) * q := by simp
  have hRaw := xChernoff_upper (fun _ : p.Loc => FinProb.bernoulli q)
    X hX (1 / 2) (by norm_num)
  have hBound : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun P => (1 + 1 / 2 : ℝ) * ((T.card : ℝ) * q) ≤
        ∑ ℓ, X ℓ (P ℓ)) ≤ Real.exp (-((T.card : ℝ) * q) / 10) := by
    norm_num at hRaw ⊢
    rw [hμ] at hRaw
    ring_nf at hRaw
    have hmul : (T.card : ℝ) * q * (3 / 2 : ℝ) =
        (3 / 2 : ℝ) * ((T.card : ℝ) * q) := by ring
    have hExp : (T.card : ℝ) * q * (-1 / 10 : ℝ) =
        -((T.card : ℝ) * q) / 10 := by ring
    rw [hmul, hExp] at hRaw
    exact hRaw
  have hsub : ∀ P : p.Loc → Bool,
      ((3 / 2 : ℝ) * (T.card : ℝ) * q < ∑ ℓ, X ℓ (P ℓ)) →
        (1 + 1 / 2 : ℝ) * ((T.card : ℝ) * q) ≤ ∑ ℓ, X ℓ (P ℓ) := by
    intro P hP
    nlinarith
  have hhigh : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun P => (3 / 2 : ℝ) * (T.card : ℝ) * q < ∑ ℓ, X ℓ (P ℓ)) ≤
      Real.exp (-((T.card : ℝ) * q) / 10) :=
    (finprob_pr_mono _ _ _ hsub).trans hBound
  simpa [HDParams.posLaw, q, X, mul_div_assoc] using hhigh

/-- A sharper position-count cutoff at `11/10` of the mean. -/
private theorem position_count_upper_eleven_tenths {p : HDParams} (T : Finset p.Loc)
    (hq0 : 0 < p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => (11 / 10 : ℝ) * (T.card : ℝ) * (p.lam / (p.V : ℝ)) <
      ∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0) ≤
        Real.exp (-((T.card : ℝ) * (p.lam / (p.V : ℝ))) / 210) := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let X : p.Loc → Bool → ℝ := fun ℓ b => if ℓ ∈ T ∧ b = true then 1 else 0
  have hX : ∀ ℓ b, 0 ≤ X ℓ b ∧ X ℓ b ≤ 1 := by
    intro ℓ b
    by_cases hℓ : ℓ ∈ T <;> cases b <;> simp [X, hℓ]
  have hcoord : ∀ ℓ, (FinProb.bernoulli q).expect (X ℓ) =
      if ℓ ∈ T then q else 0 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · simpa [X, hℓ] using bernoulli_mean_indicator q hq0.le hq1
    · simp [X, hℓ, FinProb.expect]
  have hμ : (∑ ℓ, (FinProb.bernoulli q).expect (X ℓ)) = (T.card : ℝ) * q := by
    calc
      _ = ∑ ℓ, if ℓ ∈ T then q else 0 := by
        apply Finset.sum_congr rfl
        intro ℓ _
        exact hcoord ℓ
      _ = (T.card : ℝ) * q := by simp
  have hRaw := xChernoff_upper (fun _ : p.Loc => FinProb.bernoulli q)
    X hX (1 / 10) (by norm_num)
  have hBound : (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
      (fun P => (1 + 1 / 10 : ℝ) * ((T.card : ℝ) * q) ≤
        ∑ ℓ, X ℓ (P ℓ)) ≤ Real.exp (-((T.card : ℝ) * q) / 210) := by
    norm_num at hRaw ⊢
    rw [hμ] at hRaw
    ring_nf at hRaw
    have hmul : (T.card : ℝ) * q * (11 / 10 : ℝ) =
        (11 / 10 : ℝ) * ((T.card : ℝ) * q) := by ring
    rw [hmul] at hRaw
    have hExp : (T.card : ℝ) * q * (-1 / 210 : ℝ) =
        -((T.card : ℝ) * q) / 210 := by ring
    rw [hExp] at hRaw
    exact hRaw
  have hsub : ∀ P : p.Loc → Bool,
      ((11 / 10 : ℝ) * (T.card : ℝ) * q < ∑ ℓ, X ℓ (P ℓ)) →
        (1 + 1 / 10 : ℝ) * ((T.card : ℝ) * q) ≤ ∑ ℓ, X ℓ (P ℓ) := by
    intro P hP
    nlinarith
  calc
    _ ≤ (FinProb.pi (fun _ : p.Loc => FinProb.bernoulli q)).pr
        (fun P => (1 + 1 / 10 : ℝ) * ((T.card : ℝ) * q) ≤
          ∑ ℓ, X ℓ (P ℓ)) := finprob_pr_mono _ _ _ hsub
    _ ≤ Real.exp (-((T.card : ℝ) * q) / 210) := hBound
    _ = _ := by simp [HDParams.posLaw, q, X, mul_div_assoc]

/-- When the mean is at most half a crowd threshold, the event of exceeding that
threshold has an exponential bound in the mean. -/
theorem activation_count_above_threshold {p : HDParams} (T : Finset p.Loc) (τ : ℝ)
    (hmean : 2 * (T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ τ)
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => τ < ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) ≤
      Real.exp (-((T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) := by
  have htail := activation_count_upper T 1 (by norm_num) hq0 hq1
  calc
    p.actLaw.pr (fun A => τ < ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0)
        ≤ p.actLaw.pr (fun A => 2 * (T.card : ℝ) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
            ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) := by
              apply finprob_pr_mono
              intro A hA
              exact le_trans hmean (le_of_lt hA)
    _ ≤ Real.exp (-((T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) := by
          norm_num at htail
          simpa [mul_assoc, mul_comm, mul_left_comm] using htail

/-- A fixed eligible set and a fixed crowd set can be controlled together under the
activation law. -/
theorem activation_hole_or_crowd {p : HDParams} (E T : Finset p.Loc) (τ : ℝ)
    (hmean : 2 * (T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ τ)
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => (∀ ℓ ∈ E, A ℓ = false) ∨
      τ < ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) ≤
      Real.exp (-((E.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) +
        Real.exp (-((T.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) := by
  calc
    _ ≤ p.actLaw.pr (fun A => ∀ ℓ ∈ E, A ℓ = false) +
          p.actLaw.pr (fun A => τ < ∑ ℓ,
            if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) :=
      finprob_pr_or_le _ _ _
    _ ≤ _ := add_le_add
      (activation_hole_prob E hq0 hq1)
      (activation_count_above_threshold T τ hmean hq0 hq1)

private theorem height_crowd_count_eq_sum {p : HDParams} (P A : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    (∑ ℓ : p.Loc, if ℓ.2 = j ∧ P ℓ = true ∧
      _root_.hammingDist ℓ.1 v ≤ p.r + p.D ∧ A ℓ = true then (1 : ℝ) else 0) =
    ((Finset.univ.filter (fun u : CubeVertex p.d =>
      P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D)).card : ℝ) := by
  classical
  calc
    (∑ ℓ : p.Loc, if ℓ.2 = j ∧ P ℓ = true ∧
      _root_.hammingDist ℓ.1 v ≤ p.r + p.D ∧ A ℓ = true then (1 : ℝ) else 0)
        = ∑ u : CubeVertex p.d, if P (u, j) = true ∧ A (u, j) = true ∧
            _root_.hammingDist u v ≤ p.r + p.D then (1 : ℝ) else 0 := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro u hu
              rw [Finset.sum_eq_single j]
              · simp [and_assoc, and_left_comm, and_comm]
              · intro k hk hkj
                simp [hkj]
              · intro hj
                exact False.elim (hj (Finset.mem_univ j))
    _ = _ := by rw [Finset.sum_boole]

private def heightCrowdIDs {p : HDParams} (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Finset p.Loc :=
  Finset.univ.filter (fun ℓ => ℓ.2 = j ∧ P ℓ = true ∧
    _root_.hammingDist ℓ.1 v ≤ p.r + p.D)

private def heightCrowdRegion {p : HDParams} (v : CubeVertex p.d)
    (j : Fin (p.H + 1)) : Finset p.Loc :=
  Finset.univ.filter (fun ℓ => ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r + p.D)

/-- A rectangular over-approximation to the prospective-center domain of a child path:
all levels within `R` and all center locations in the radius-`r + D*R + D` spatial ball. -/
private def hdChildCenterDomain {p : HDParams} (start : HDState p) (R : ℕ) : Finset p.Loc :=
  Finset.univ.filter (fun ℓ =>
    Nat.dist start.2 ℓ.2.val < R ∧
      _root_.hammingDist start.1 ℓ.1 ≤ p.r + p.D * R + p.D)

private theorem hdScaleDistance_hamming_bound {p : HDParams} (hD : 0 < p.D)
    {s t : HDState p} {R : ℕ} (h : hdScaleDistance p.D s t < R) :
    _root_.hammingDist s.1 t.1 ≤ p.D * R := by
  have hD1 : 1 ≤ p.D := by omega
  have hquot :
      (_root_.hammingDist s.1 t.1 + p.D - 1) / p.D < R := by
    have hq := lt_of_le_of_lt (Nat.le_max_right _ _) h
    simpa [hdScaleDistance, max_eq_right hD1] using hq
  have hnum : _root_.hammingDist s.1 t.1 + p.D - 1 < R * p.D :=
    (Nat.div_lt_iff_lt_mul hD).1 hquot
  have hnum' : _root_.hammingDist s.1 t.1 + p.D - 1 < p.D * R := by
    simpa [Nat.mul_comm] using hnum
  omega

private theorem heightCrowdRegion_subset_hdChildCenterDomain {p : HDParams} (hD : 0 < p.D)
    (start : HDState p) (R : ℕ) (v : CubeVertex p.d) (j : Fin (p.H + 1))
    (hstate : hdScaleDistance p.D start (v, j.val) < R) :
    heightCrowdRegion v j ⊆ hdChildCenterDomain start R := by
  intro ℓ hℓ
  have hℓ' := (Finset.mem_filter.mp hℓ).2
  rcases hℓ' with ⟨hlev, hball⟩
  have hlevel : Nat.dist start.2 j.val < R := by
    unfold hdScaleDistance at hstate
    exact lt_of_le_of_lt (Nat.le_max_left _ _) hstate
  have hlevel' : Nat.dist start.2 ℓ.2.val < R := by
    rw [show ℓ.2.val = j.val from congrArg Fin.val hlev]
    exact hlevel
  have hspace := hdScaleDistance_hamming_bound hD hstate
  have hball' : _root_.hammingDist v ℓ.1 ≤ p.r + p.D := by
    simpa [_root_.hammingDist_comm] using hball
  have hspace' : _root_.hammingDist start.1 ℓ.1 ≤ p.r + p.D * R + p.D := by
    calc
      _ ≤ _ + _ := _root_.hammingDist_triangle _ v _
      _ ≤ p.D * R + (p.r + p.D) := Nat.add_le_add hspace hball'
      _ = p.r + p.D * R + p.D := by omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hlevel', hspace'⟩⟩

private theorem hdChildCenterDomain_overlap_card_bound {p : HDParams}
    (start₁ start₂ : HDState p) (R : ℕ) :
    (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
      ((Finset.univ.filter (fun u : CubeVertex p.d =>
        _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
        _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)).card) * (p.H + 1) := by
  classical
  let V : Finset (CubeVertex p.d) := Finset.univ.filter (fun u =>
    _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
    _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)
  have hsubset : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R ⊆
      V ×ˢ (Finset.univ : Finset (Fin (p.H + 1))) := by
    intro ℓ hℓ
    rcases Finset.mem_inter.mp hℓ with ⟨hℓ₁, hℓ₂⟩
    have h₁ := (Finset.mem_filter.mp hℓ₁).2
    have h₂ := (Finset.mem_filter.mp hℓ₂).2
    change ℓ ∈ V ×ˢ (Finset.univ : Finset (Fin (p.H + 1)))
    rw [Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h₁.2, h₂.2⟩⟩,
      Finset.mem_univ _⟩
  calc
    (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
        (V ×ˢ (Finset.univ : Finset (Fin (p.H + 1)))).card := Finset.card_le_card hsubset
    _ = V.card * (p.H + 1) := by simp [Finset.card_product]

private theorem hdChildCenterDomain_overlap_card_bound_sharp {p : HDParams}
    (start₁ start₂ : HDState p) (R : ℕ) :
    (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
      ((Finset.univ.filter (fun u : CubeVertex p.d =>
        _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
        _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)).card) * (2 * R + 1) := by
  classical
  let V : Finset (CubeVertex p.d) := Finset.univ.filter (fun u =>
    _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
    _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)
  let L : Finset (Fin (p.H + 1)) := Finset.univ.filter
    (fun j => Nat.dist start₁.2 j.val < R)
  have hLinterval : L.card ≤ (Finset.Icc (start₁.2 - R) (start₁.2 + R)).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin (p.H + 1) => j.val)
    · intro j hj
      have hdist := (Finset.mem_filter.mp hj).2
      change j.val ∈ Finset.Icc (start₁.2 - R) (start₁.2 + R)
      simp only [Finset.mem_Icc]
      rcases le_total start₁.2 j.val with hle | hge
      · rw [Nat.dist_eq_sub_of_le hle] at hdist
        constructor <;> omega
      · rw [Nat.dist_eq_sub_of_le_right hge] at hdist
        constructor <;> omega
    · intro j hj j' hj' hval
      exact Fin.ext hval
  have hIcc : (Finset.Icc (start₁.2 - R) (start₁.2 + R)).card ≤ 2 * R + 1 := by
    simp
    omega
  have hL : L.card ≤ 2 * R + 1 := hLinterval.trans hIcc
  have hsubset : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R ⊆
      V ×ˢ L := by
    intro ℓ hℓ
    rcases Finset.mem_inter.mp hℓ with ⟨hℓ₁, hℓ₂⟩
    have h₁ := (Finset.mem_filter.mp hℓ₁).2
    have h₂ := (Finset.mem_filter.mp hℓ₂).2
    change ℓ ∈ V ×ˢ L
    rw [Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h₁.2, h₂.2⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁.1⟩⟩
  calc
    (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
        (V ×ˢ L).card := Finset.card_le_card hsubset
    _ = V.card * L.card := by simp [Finset.card_product]
    _ ≤ V.card * (2 * R + 1) := Nat.mul_le_mul_left _ hL

private theorem hdChildCenterDomain_overlap_real_bound {p : HDParams}
    (start₁ start₂ : HDState p) (R : ℕ) (ρ : ℝ)
    (hspatial : (((Finset.univ.filter (fun u : CubeVertex p.d =>
      _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
      _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)).card : ℕ) : ℝ) ≤
        (p.V : ℝ) * ρ) :
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) ≤
      (2 * R + 1 : ℝ) * (p.V : ℝ) * ρ := by
  have hcard := hdChildCenterDomain_overlap_card_bound_sharp start₁ start₂ R
  calc
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ)
        ≤ (((Finset.univ.filter (fun u : CubeVertex p.d =>
          _root_.hammingDist start₁.1 u ≤ p.r + p.D * R + p.D ∧
          _root_.hammingDist start₂.1 u ≤ p.r + p.D * R + p.D)).card : ℕ) : ℝ) *
            (2 * R + 1 : ℝ) := by exact_mod_cast hcard
    _ ≤ (p.V : ℝ) * ρ * (2 * R + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right hspatial (by positivity)
    _ = (2 * R + 1 : ℝ) * (p.V : ℝ) * ρ := by ring

private theorem hdChildCenterDomain_disjoint_levels {p : HDParams}
    (start₁ start₂ : HDState p) (R : ℕ)
    (hsep : 2 * R < Nat.dist start₁.2 start₂.2) :
    Disjoint (hdChildCenterDomain start₁ R) (hdChildCenterDomain start₂ R) := by
  classical
  rw [Finset.disjoint_left]
  intro ℓ hℓ₁ hℓ₂
  have h₁ := (Finset.mem_filter.mp hℓ₁).2
  have h₂ := (Finset.mem_filter.mp hℓ₂).2
  have htri : Nat.dist start₁.2 start₂.2 ≤
      Nat.dist start₁.2 ℓ.2.val + Nat.dist ℓ.2.val start₂.2 := by
    unfold Nat.dist
    omega
  have hsymm : Nat.dist ℓ.2.val start₂.2 = Nat.dist start₂.2 ℓ.2.val := Nat.dist_comm _ _
  rw [hsymm] at htri
  omega

private theorem hdScaleSeparated_spatial_distance_lower {p : HDParams} (hD : 0 < p.D)
    {start₁ start₂ : HDState p} {gap R : ℕ}
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hvertical : Nat.dist start₁.2 start₂.2 ≤ 2 * R)
    (hgap : 2 * R < gap) :
    p.D * (gap - 1) ≤ _root_.hammingDist start₁.1 start₂.1 := by
  have hD1 : 1 ≤ p.D := by omega
  have hquot :
      gap ≤ (_root_.hammingDist start₁.1 start₂.1 + p.D - 1) / p.D := by
    have hsep' : gap ≤ max (Nat.dist start₁.2 start₂.2)
        ((_root_.hammingDist start₁.1 start₂.1 + p.D - 1) / p.D) := by
      simpa [hdScaleDistance, max_eq_right hD1] using hsep
    by_contra hnot
    have hquotLt : (_root_.hammingDist start₁.1 start₂.1 + p.D - 1) / p.D < gap :=
      Nat.lt_of_not_ge hnot
    have hmaxLt : max (Nat.dist start₁.2 start₂.2)
        ((_root_.hammingDist start₁.1 start₂.1 + p.D - 1) / p.D) < gap :=
      max_lt_iff.mpr ⟨lt_of_le_of_lt hvertical hgap, hquotLt⟩
    exact (not_lt_of_ge hsep') hmaxLt
  have hnum : gap * p.D ≤ _root_.hammingDist start₁.1 start₂.1 + p.D - 1 :=
    (Nat.le_div_iff_mul_le hD).1 hquot
  have hdecomp : gap * p.D = (gap - 1) * p.D + p.D := by
    have hgapEq : gap = (gap - 1) + 1 := by omega
    rw [hgapEq, Nat.add_mul]
    simp
  rw [hdecomp] at hnum
  have hnum' : (gap - 1) * p.D + 1 ≤ _root_.hammingDist start₁.1 start₂.1 := by omega
  calc
    p.D * (gap - 1) = (gap - 1) * p.D := Nat.mul_comm _ _
    _ ≤ _ := Nat.le_of_succ_le hnum'

private theorem heightCrowdIDs_card_eq_position_count {p : HDParams}
    (P : p.Loc → Bool) (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    ((heightCrowdIDs P v j).card : ℝ) =
      ∑ ℓ : p.Loc, if ℓ ∈ heightCrowdRegion v j ∧ P ℓ = true then (1 : ℝ) else 0 := by
  classical
  have hIDs : heightCrowdIDs P v j =
      (heightCrowdRegion v j).filter (fun ℓ => P ℓ = true) := by
    ext ℓ
    simp [heightCrowdIDs, heightCrowdRegion, and_assoc, and_left_comm, and_comm]
  have hsets : (Finset.univ.filter
      (fun ℓ : p.Loc => ℓ ∈ heightCrowdRegion v j ∧ P ℓ = true)) =
      (heightCrowdRegion v j).filter (fun ℓ => P ℓ = true) := by
    ext ℓ
    simp
  rw [hIDs, ← hsets]
  symm
  exact Finset.sum_boole
    (fun ℓ : p.Loc => ℓ ∈ heightCrowdRegion v j ∧ P ℓ = true) Finset.univ

private def cubeDiffEquiv {d : ℕ} (v : CubeVertex d) :
    CubeVertex d ≃ Finset (Fin d) where
  toFun u := Finset.univ.filter (fun i => u i ≠ v i)
  invFun s := fun i => if i ∈ s then !v i else v i
  left_inv u := by
    funext i
    cases hu : u i <;> cases hv : v i <;> simp [hu, hv]
  right_inv s := by
    ext i
    cases hv : v i <;> simp [hv]

private theorem hammingDist_eq_cubeDiff_card {d : ℕ} (u v : CubeVertex d) :
    hammingDist u v = (cubeDiffEquiv v u).card := by
  simp [hammingDist, cubeDiffEquiv]

private theorem choose_fixed_lower {d k : ℕ} (h2k : 2 * k ≤ d) :
    ((d : ℝ) / 2) ^ k / (Nat.factorial k : ℝ) ≤ (Nat.choose d k : ℝ) := by
  have hnum : (d : ℝ) / 2 ≤ (d + 1 - k : ℕ) := by
    have hnat : d ≤ 2 * (d + 1 - k) := by omega
    have hnatReal : (d : ℝ) ≤ 2 * (d + 1 - k : ℕ) := by exact_mod_cast hnat
    nlinarith [hnatReal]
  have hpow : ((d : ℝ) / 2) ^ k ≤ (d + 1 - k : ℕ) ^ k :=
    pow_le_pow_left₀ (by positivity) hnum k
  have hdiv : ((d : ℝ) / 2) ^ k / (Nat.factorial k : ℝ) ≤
      ((d + 1 - k : ℕ) ^ k : ℝ) / (Nat.factorial k : ℝ) :=
    div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  exact hdiv.trans (Nat.pow_le_choose k d)

private theorem hdVolume_ge_choose {p : HDParams} (k : ℕ) (hk : k ≤ p.r) :
    Nat.choose p.d k ≤ p.V := by
  unfold HDParams.V
  exact Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

private theorem volume_ge_lambda_from_fixed_layer
    (J₀ c_d : ℝ) (k : ℕ) (hkJ : J₀ < (k : ℝ))
    (hc_d : 0 < c_d)
    (p : HDParams) (hlam : p.lam = (p.n : ℝ) ^ J₀)
    (hn : 1 ≤ p.n)
    (hGrowth : (Nat.factorial k : ℝ) / (c_d / 2) ^ k ≤
      (p.n : ℝ) ^ ((k : ℝ) - J₀))
    (hd : c_d * p.n ≤ p.d)
    (hr : k ≤ p.r) (h2k : 2 * k ≤ p.d) : p.lam ≤ p.V := by
  have hfactPos : 0 < (Nat.factorial k : ℝ) := by positivity
  have hcoeff : (Nat.factorial k : ℝ) ≤ (c_d / 2) ^ k * (p.n : ℝ) ^ ((k : ℝ) - J₀) := by
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0 < (c_d / 2) ^ k)).1 hGrowth
  have hratio : 1 ≤ ((c_d / 2) ^ k * (p.n : ℝ) ^ ((k : ℝ) - J₀)) /
      (Nat.factorial k : ℝ) :=
    (le_div_iff₀ hfactPos).2 (by simpa using hcoeff)
  have hnReal : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hnpos : 0 < (p.n : ℝ) := by positivity
  have hpowEq : (p.n : ℝ) ^ J₀ * (p.n : ℝ) ^ ((k : ℝ) - J₀) =
      (p.n : ℝ) ^ (k : ℝ) := by
    calc
      (p.n : ℝ) ^ J₀ * (p.n : ℝ) ^ ((k : ℝ) - J₀) =
          (p.n : ℝ) ^ (J₀ + ((k : ℝ) - J₀)) := by rw [← Real.rpow_add hnpos]
      _ = (p.n : ℝ) ^ (k : ℝ) := by rw [show J₀ + ((k : ℝ) - J₀) = (k : ℝ) by ring]
  have hbase : c_d * (p.n : ℝ) / 2 ≤ (p.d : ℝ) / 2 := by
    have hdReal : c_d * (p.n : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast hd
    exact div_le_div_of_nonneg_right hdReal (by norm_num)
  have hbasePow : (c_d * (p.n : ℝ) / 2) ^ k ≤ ((p.d : ℝ) / 2) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hchoose : ((c_d * (p.n : ℝ) / 2) ^ k /
      (Nat.factorial k : ℝ)) ≤ (Nat.choose p.d k : ℝ) :=
    (div_le_div_of_nonneg_right hbasePow (Nat.cast_nonneg _)).trans
      (choose_fixed_lower h2k)
  have hbaseEq : c_d * (p.n : ℝ) / 2 = (c_d / 2) * (p.n : ℝ) := by ring
  calc
    p.lam = (p.n : ℝ) ^ J₀ := hlam
    _ ≤ (p.n : ℝ) ^ J₀ *
        (((c_d / 2) ^ k * (p.n : ℝ) ^ ((k : ℝ) - J₀)) /
          (Nat.factorial k : ℝ)) :=
          by simpa using mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hnpos.le J₀)
    _ = ((c_d * (p.n : ℝ) / 2) ^ k / (Nat.factorial k : ℝ)) := by
          rw [hbaseEq, mul_pow]
          field_simp [hfactPos.ne']
          rw [hpowEq]
          simpa only [Real.rpow_natCast]
    _ ≤ (Nat.choose p.d k : ℝ) := hchoose
    _ ≤ (p.V : ℝ) := by exact_mod_cast hdVolume_ge_choose k hr

private theorem height_volume_ge_lambda_eventually
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.lam = (p.n : ℝ) ^ J₀ →
      n₀ ≤ p.n → c_d * p.n ≤ p.d → reg.ok p.n p.d p.r → p.lam ≤ p.V := by
  obtain ⟨k, hkJ⟩ := exists_nat_gt J₀
  have hkExp : 0 < (k : ℝ) - J₀ := by linarith
  have hkPos : 0 < k := by
    have hkReal : (0 : ℝ) < k := by linarith [hp.hJ, hkJ]
    exact_mod_cast hkReal
  have hcd : 0 < c_d := hp.hd.1
  let Cpow : ℝ := (Nat.factorial k : ℝ) / (c_d / 2) ^ k
  have hCpow : 0 < Cpow := by dsimp [Cpow]; positivity
  obtain ⟨Npow, hNpow⟩ := exists_nat_rpow_ge (e := (k : ℝ) - J₀) (C := Cpow) hkExp
  let Cdim : ℝ := (2 * (k : ℝ)) / c_d
  obtain ⟨Ndim, hNdim⟩ := exists_nat_rpow_ge (e := (1 : ℝ)) (C := Cdim) (by positivity)
  cases reg with
  | lin c_r hcr =>
      have hcrcd : 0 < c_r * c_d := mul_pos hcr.1 hcd
      let Krad : ℕ := max k D
      let Crad : ℝ := (Krad : ℝ) / (c_r * c_d)
      obtain ⟨Nrad, hNrad⟩ := exists_nat_rpow_ge (e := (1 : ℝ)) (C := Crad) (by positivity)
      let n₀ := max 2 (max Npow (max Ndim Nrad))
      refine ⟨n₀, ?_⟩
      intro p hD hlam hn hdim hreg
      have hNinner : max Npow (max Ndim Nrad) ≤ p.n := le_trans (Nat.le_max_right 2 _) hn
      have hNpowle : Npow ≤ p.n := le_trans (Nat.le_max_left _ _) hNinner
      have hNdimle : Ndim ≤ p.n := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) hNinner)
      have hNradle : Nrad ≤ p.n := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) hNinner)
      have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left _ _) hn
      have hnpos : 0 < (p.n : ℝ) := by positivity
      have hnReal : 1 ≤ (p.n : ℝ) := by exact_mod_cast (show 1 ≤ p.n by omega)
      have hGrowth : (Nat.factorial k : ℝ) / (c_d / 2) ^ k ≤ (p.n : ℝ) ^ ((k : ℝ) - J₀) := by
        exact hNpow p.n hNpowle
      have hDimN : Cdim ≤ (p.n : ℝ) := by
        simpa [Cdim, Real.rpow_one] using hNdim p.n hNdimle
      have hRadN : Crad ≤ (p.n : ℝ) := by
        simpa [Crad, Real.rpow_one] using hNrad p.n hNradle
      have hDimLower : (2 * (k : ℝ)) ≤ c_d * p.n := by
        have h := (div_le_iff₀ hcd).1 hDimN
        simpa [mul_comm] using h
      have hRadiusReg : c_r * (p.d : ℝ) ≤ p.r ∧ 4 * p.r ≤ p.d := by
        simpa [HDRegime.ok] using hreg
      have hRadLowerAll : (Krad : ℝ) ≤ p.r := by
        have h1 : (Krad : ℝ) ≤ (c_r * c_d) * p.n := by
          have h := (div_le_iff₀ hcrcd).1 hRadN
          simpa [mul_comm] using h
        have h2 : (c_r * c_d) * p.n ≤ c_r * (p.d : ℝ) := by
          calc
            (c_r * c_d) * p.n = c_r * (c_d * p.n) := by ring
            _ ≤ c_r * (p.d : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hdim) hcr.1.le
        exact le_trans (le_trans h1 h2) hRadiusReg.1
      have hRadLower : (k : ℝ) ≤ p.r :=
        le_trans (by exact_mod_cast (Nat.le_max_left k D)) hRadLowerAll
      have hRadLowerNat : k ≤ p.r := by exact_mod_cast hRadLower
      have hDleR : p.D ≤ p.r := by
        rw [hD]
        exact_mod_cast (le_trans (Nat.le_max_right k D) (by exact_mod_cast hRadLowerAll))
      have hRadiusNat : p.r + p.D ≤ p.d := by
        omega
      have hDimNat : 2 * k ≤ p.d := by
        have h := hDimLower.trans (by exact_mod_cast hdim)
        exact_mod_cast h
      exact volume_ge_lambda_from_fixed_layer J₀ c_d k hkJ hcd p hlam (by omega) hGrowth hdim
        hRadLowerNat hDimNat
  | sub ρ hρ =>
      let Cfloor : ℝ := (k : ℝ) + 1
      obtain ⟨Nfloor, hNfloor⟩ := exists_nat_rpow_ge (e := 1 - ρ) (C := Cfloor) (by linarith [hρ.2.1])
      let Crho : ℝ := 2 / c_d
      obtain ⟨Nrho, hNrho⟩ := exists_nat_rpow_ge (e := ρ) (C := Crho) hρ.1
      let n₀ := max 2 (max Npow (max Ndim (max Nfloor Nrho)))
      refine ⟨n₀, ?_⟩
      intro p hD hlam hn hdim hreg
      have hNtail : max Npow (max Ndim (max Nfloor Nrho)) ≤ p.n := le_trans (Nat.le_max_right 2 _) hn
      have hNpowle : Npow ≤ p.n := le_trans (Nat.le_max_left _ _) hNtail
      have hNtail' : max Ndim (max Nfloor Nrho) ≤ p.n := le_trans (Nat.le_max_right _ _) hNtail
      have hNdimle : Ndim ≤ p.n := le_trans (Nat.le_max_left _ _) hNtail'
      have hNtail'' : max Nfloor Nrho ≤ p.n := le_trans (Nat.le_max_right _ _) hNtail'
      have hNfloorle : Nfloor ≤ p.n := le_trans (Nat.le_max_left _ _) hNtail''
      have hNrhole : Nrho ≤ p.n := le_trans (Nat.le_max_right _ _) hNtail''
      have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left _ _) hn
      have hnpos : 0 < (p.n : ℝ) := by positivity
      have hnReal : 1 ≤ (p.n : ℝ) := by exact_mod_cast (show 1 ≤ p.n by omega)
      have hGrowth : (Nat.factorial k : ℝ) / (c_d / 2) ^ k ≤ (p.n : ℝ) ^ ((k : ℝ) - J₀) := hNpow p.n hNpowle
      have hDimN : Cdim ≤ (p.n : ℝ) := by simpa [Cdim, Real.rpow_one] using hNdim p.n hNdimle
      have hfloorN : Cfloor ≤ (p.n : ℝ) ^ (1 - ρ) := hNfloor p.n hNfloorle
      have hrhoN : Crho ≤ (p.n : ℝ) ^ ρ := hNrho p.n hNrhole
      have hDimLower : (2 * (k : ℝ)) ≤ c_d * p.n := by
        have h := (div_le_iff₀ hcd).1 hDimN
        simpa [mul_comm] using h
      have hRadiusEq : p.r = ⌊(p.n : ℝ) ^ (1 - ρ)⌋₊ := by
        simpa [HDRegime.ok] using hreg
      have hRadLower : k ≤ p.r := by
        have hx : (k : ℝ) ≤ (p.n : ℝ) ^ (1 - ρ) := by
          dsimp [Cfloor] at hfloorN
          linarith [hfloorN]
        rw [hRadiusEq]
        exact (Nat.le_floor_iff' hkPos.ne').2 hx
      have hDimNat : 2 * k ≤ p.d := by
        have h := hDimLower.trans (by exact_mod_cast hdim)
        exact_mod_cast h
      exact volume_ge_lambda_from_fixed_layer J₀ c_d k hkJ hcd p hlam (by omega) hGrowth hdim
        hRadLower hDimNat

private theorem cube_ball_card_eq_choose_sum {d r : ℕ} (v : CubeVertex d) (hr : r ≤ d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  let B : CubeVertex d → Prop := fun u => hammingDist u v ≤ r
  let S : Finset (Finset (Fin d)) := Finset.univ.powerset
  have hballSub : Fintype.card {u : CubeVertex d // B u} =
      (Finset.univ.filter B).card := by
    simp [B, Fintype.card_subtype]
  have hsetSub : Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      (S.filter (fun s => s.card ≤ r)).card := by
    simp [S, Fintype.card_subtype]
  let eDiff : CubeVertex d ≃ Finset (Fin d) := cubeDiffEquiv v
  let e : {u : CubeVertex d // B u} ≃ {s : Finset (Fin d) // s.card ≤ r} := {
    toFun := fun u => ⟨eDiff u.1, by
      change (eDiff u.1).card ≤ r
      rw [← hammingDist_eq_cubeDiff_card]
      exact u.2⟩
    invFun := fun s => ⟨eDiff.symm s.1, by
      change hammingDist (eDiff.symm s.1) v ≤ r
      rw [hammingDist_eq_cubeDiff_card]
      simpa [eDiff] using s.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      exact eDiff.left_inv u.1
    right_inv := by
      intro s
      apply Subtype.ext
      exact eDiff.right_inv s.1 }
  have hpowerset : (S.filter (fun s => s.card ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
    calc
      (S.filter (fun s => s.card ≤ r)).card
          = ∑ s ∈ S, if s.card ≤ r then (1 : ℕ) else 0 := by
              symm
              exact Finset.sum_boole (fun s : Finset (Fin d) => s.card ≤ r) S
      _ = ∑ i ∈ Finset.range (d + 1), Nat.choose d i •
            (if i ≤ r then (1 : ℕ) else 0) := by
              simpa [S] using
                (Finset.sum_powerset_apply_card
                  (f := fun k => if k ≤ r then (1 : ℕ) else 0)
                  (x := (Finset.univ : Finset (Fin d))))
      _ = ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
              have hsub : Finset.range (r + 1) ⊆ Finset.range (d + 1) :=
                Finset.range_mono (Nat.succ_le_succ hr)
              have hzero : ∀ i ∈ Finset.range (d + 1), i ∉ Finset.range (r + 1) →
                  Nat.choose d i • (if i ≤ r then (1 : ℕ) else 0) = 0 := by
                intro i hi hnot
                have hir : ¬ i ≤ r := by
                  intro hir
                  exact hnot (Finset.mem_range.mpr (by omega))
                simp [hir]
              rw [(Finset.sum_subset hsub hzero).symm]
              apply Finset.sum_congr rfl
              intro i hi
              have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
              simp [hir]
  calc
    (Finset.univ.filter B).card = Fintype.card {u : CubeVertex d // B u} := hballSub.symm
    _ = Fintype.card {s : Finset (Fin d) // s.card ≤ r} := Fintype.card_congr e
    _ = (S.filter (fun s => s.card ≤ r)).card := hsetSub
    _ = _ := hpowerset

private theorem hdCubeBall_card_power_bound {d s : ℕ} (hs : s ≤ d) (v : CubeVertex d) :
    ((Finset.univ.filter (fun u : CubeVertex d =>
      _root_.hammingDist u v ≤ s)).card : ℝ) ≤
        ((s + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ s := by
  have hball := cube_ball_card_eq_choose_sum v hs
  have hballR : ((Finset.univ.filter (fun u : CubeVertex d =>
      _root_.hammingDist u v ≤ s)).card : ℝ) =
        ∑ i ∈ Finset.range (s + 1), (Nat.choose d i : ℝ) := by
    exact_mod_cast hball
  rw [hballR]
  calc
    (∑ i ∈ Finset.range (s + 1), (Nat.choose d i : ℝ)) ≤
        ∑ i ∈ Finset.range (s + 1), ((d + 1 : ℕ) : ℝ) ^ s := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ≤ s := by simp only [Finset.mem_range] at hi; omega
      have hchoose : Nat.choose d i ≤ (d + 1) ^ s := by
        calc
          Nat.choose d i ≤ d ^ i := Nat.choose_le_pow d i
          _ ≤ (d + 1) ^ i := pow_le_pow_left' (by omega : d ≤ d + 1) i
          _ ≤ (d + 1) ^ s := pow_le_pow_right' (by omega : 1 ≤ d + 1) his
      exact_mod_cast hchoose
    _ = ((s + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ s := by simp

/-- A base-radius path consultation ball contains at most a short-level factor times
the usual small Hamming-ball count. -/
private theorem hdScaleBallSiteLevels_card_bound {p : HDParams} (Sites : p.Sites)
    (start : HDState p) (R : ℕ) (hD : 0 < p.D) (hR : 0 < R)
    (hstart : start.2 = 0) (hRadius : p.D * R ≤ p.d) :
    ((hdScaleBallSiteLevels Sites start R).card : ℝ) ≤
      (R : ℝ) * (p.D * R + 1 : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) := by
  classical
  let B : Finset (CubeVertex p.d) := Finset.univ.filter (fun u =>
    _root_.hammingDist u start.1 ≤ p.D * R)
  let L : Finset (Fin (p.H + 1)) := Finset.univ.filter (fun j => j.val < R)
  have hsubset : hdScaleBallSiteLevels Sites start R ⊆ B.product L := by
    intro x hx
    simp only [hdScaleBallSiteLevels, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change x ∈ B ×ˢ L
    rw [Finset.mem_product]
    rcases hx with ⟨hxSites, hdist⟩
    have hspaceDiv :
        (_root_.hammingDist start.1 x.1 + max 1 p.D - 1) / max 1 p.D < R := by
      exact lt_of_le_of_lt (Nat.le_max_right _ _) hdist
    have hspaceDiv' :
        (_root_.hammingDist start.1 x.1 + p.D - 1) / p.D < R := by
      simpa [max_eq_right (by omega : 1 ≤ p.D)] using hspaceDiv
    have hspaceNum :
        _root_.hammingDist start.1 x.1 + p.D - 1 < R * p.D :=
      (Nat.div_lt_iff_lt_mul hD).1 hspaceDiv'
    have hcomm : _root_.hammingDist x.1 start.1 =
        _root_.hammingDist start.1 x.1 := by exact _root_.hammingDist_comm _ _
    have hspace : _root_.hammingDist x.1 start.1 ≤ p.D * R := by
      rw [hcomm]
      have hspaceNum' :
          _root_.hammingDist start.1 x.1 + p.D - 1 < p.D * R := by
        simpa [Nat.mul_comm] using hspaceNum
      omega
    have hlevel : x.2.val < R := by
      have hlevel' : Nat.dist start.2 x.2.val < R :=
        lt_of_le_of_lt (Nat.le_max_left _ _) hdist
      rw [hstart, Nat.dist_zero_left] at hlevel'
      exact hlevel'
    exact ⟨by simpa [B] using hspace, by simpa [L] using hlevel⟩
  have hball : (B.card : ℝ) ≤
      ((p.D * R + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) := by
    exact hdCubeBall_card_power_bound hRadius start.1
  have hlevels : (L.card : ℝ) ≤ R := by
    let Lv : Finset ℕ := L.image Fin.val
    have hcard : Lv.card = L.card := by
      apply Finset.card_image_iff.mpr
      intro x hx y hy hxy
      exact Fin.ext hxy
    have hsubLv : Lv ⊆ Finset.range R := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hx).2)
    have hLv : Lv.card ≤ R := by
      calc
        Lv.card ≤ (Finset.range R).card := Finset.card_le_card hsubLv
        _ = R := by simp
    rw [← hcard]
    exact_mod_cast hLv
  have hcard := Finset.card_le_card hsubset
  have hprod : (B.product L).card = B.card * L.card := Finset.card_product B L
  rw [hprod] at hcard
  have hcardR : ((hdScaleBallSiteLevels Sites start R).card : ℝ) ≤
      (B.card : ℝ) * (L.card : ℝ) := by exact_mod_cast hcard
  have hfirst := mul_le_mul_of_nonneg_right hball (by positivity : 0 ≤ (L.card : ℝ))
  have hsecond := mul_le_mul_of_nonneg_left hlevels
    (by positivity : 0 ≤ ((p.D * R + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R))
  calc
    ((hdScaleBallSiteLevels Sites start R).card : ℝ)
        ≤ (B.card : ℝ) * (L.card : ℝ) := hcardR
    _ ≤ (((p.D * R + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R)) * R :=
      hfirst.trans hsecond
    _ = (R : ℝ) * (p.D * R + 1 : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) := by
      push_cast
      ring

/-- At the logarithmic initial scale, the number of possible bad site-levels is
subexponential in every fixed positive power of `n`. -/
private theorem hdScaleBallSiteLevels_exp_bound
    (D : ℕ) (C_d e : ℝ) (hD : 0 < D) (hC : 0 < C_d) (he : 0 < e) :
    ∃ n₀ : ℕ, ∀ {p : HDParams} (Sites : p.Sites) (start : HDState p) (R : ℕ),
      n₀ ≤ p.n → p.D = D → (p.d : ℝ) ≤ C_d * p.n →
      (R : ℝ) ≤ 2 * (Real.log (p.n : ℝ)) ^ 2 → 0 < R → start.2 = 0 →
      p.D * R ≤ p.d →
      ((hdScaleBallSiteLevels Sites start R).card : ℝ) ≤
        Real.exp ((p.n : ℝ) ^ e) := by
  obtain ⟨Nroot, hroot⟩ := exists_nat_rpow_ge
    (e := (1 : ℝ) / 2) (C := 2) (by norm_num)
  obtain ⟨NlogLo, hlogLo⟩ := exists_nat_log_ge
    (Real.log ((D + 1 : ℕ) : ℝ) + Real.log (C_d + 1) + 1)
  obtain ⟨NlogQuarter, hlogQuarter⟩ := log_le_rpow_eventually (1 / 4) (by norm_num)
  have heSix : 0 < e / 6 := by positivity
  obtain ⟨NlogE, hlogE⟩ := log_le_rpow_eventually (e / 6) heSix
  obtain ⟨Ncoef, hcoef⟩ := exists_nat_rpow_ge
    (e := e / 2) (C := 3 + 4 * (D : ℝ)) (by positivity)
  let Ntail := max NlogLo (max NlogQuarter (max NlogE Ncoef))
  let Nbody := max Nroot Ntail
  let n₀ := max 2 (max (D + 1) Nbody)
  refine ⟨n₀, ?_⟩
  intro p Sites start R hn hDp hdim hRsmall hR hstart hRadius
  have hNbody : Nbody ≤ p.n := by
    exact le_trans (Nat.le_max_right (D + 1) Nbody)
      (le_trans (Nat.le_max_right 2 _) hn)
  have hNroot : Nroot ≤ p.n := le_trans (Nat.le_max_left Nroot Ntail) hNbody
  have hNtail : Ntail ≤ p.n := le_trans (Nat.le_max_right Nroot Ntail) hNbody
  have hNlogLo : NlogLo ≤ p.n :=
    le_trans (Nat.le_max_left NlogLo _) hNtail
  have hNlogQuarter : NlogQuarter ≤ p.n :=
    le_trans (Nat.le_max_left NlogQuarter _) (le_trans (Nat.le_max_right NlogLo _) hNtail)
  have hNlogE : NlogE ≤ p.n :=
    le_trans (Nat.le_max_left NlogE Ncoef)
      (le_trans (Nat.le_max_right NlogQuarter _) (le_trans (Nat.le_max_right NlogLo _) hNtail))
  have hNcoef : Ncoef ≤ p.n :=
    le_trans (Nat.le_max_right NlogE Ncoef)
      (le_trans (Nat.le_max_right NlogQuarter _) (le_trans (Nat.le_max_right NlogLo _) hNtail))
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left 2 _) hn
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hlogLower :
      Real.log ((D + 1 : ℕ) : ℝ) + Real.log (C_d + 1) + 1 ≤ Real.log (p.n : ℝ) :=
    hlogLo p.n hNlogLo
  have hlogDnonneg : 0 ≤ Real.log ((D + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ D + 1 by omega))
  have hlogCnonneg : 0 ≤ Real.log (C_d + 1) :=
    Real.log_nonneg (by linarith [hC])
  have hlog : 1 ≤ Real.log (p.n : ℝ) := by linarith [hlogLower, hlogDnonneg, hlogCnonneg]
  have hlogD : Real.log ((D + 1 : ℕ) : ℝ) ≤ Real.log (p.n : ℝ) := by
    linarith [hlogLower, hlogCnonneg]
  have hlogC : Real.log (C_d + 1) ≤ Real.log (p.n : ℝ) := by
    linarith [hlogLower, hlogDnonneg]
  have hlogQ : Real.log (p.n : ℝ) ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) :=
    hlogQuarter p.n hNlogQuarter
  have hlogE' : Real.log (p.n : ℝ) ≤ (p.n : ℝ) ^ (e / 6) :=
    hlogE p.n hNlogE
  have hroot' : 2 ≤ (p.n : ℝ) ^ ((1 : ℝ) / 2) := hroot p.n hNroot
  have hpowQuarterSq : (p.n : ℝ) ^ ((1 : ℝ) / 4) * (p.n : ℝ) ^ ((1 : ℝ) / 4) =
      (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      (p.n : ℝ) ^ ((1 : ℝ) / 4) * (p.n : ℝ) ^ ((1 : ℝ) / 4) =
          (p.n : ℝ) ^ (((1 : ℝ) / 4) + ((1 : ℝ) / 4)) := (Real.rpow_add hnpos _ _).symm
      _ = (p.n : ℝ) ^ ((1 : ℝ) / 2) := by congr 1 <;> norm_num
  have hlogNonneg : 0 ≤ Real.log (p.n : ℝ) := by linarith
  have hquarterNonneg : 0 ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hnpos.le _
  have hlogSq : (Real.log (p.n : ℝ)) ^ 2 ≤ (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [pow_two]
    calc
      Real.log (p.n : ℝ) * Real.log (p.n : ℝ) ≤
          (p.n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (p.n : ℝ) :=
        mul_le_mul_of_nonneg_right hlogQ hlogNonneg
      _ ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) * (p.n : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hlogQ hquarterNonneg
      _ = (p.n : ℝ) ^ ((1 : ℝ) / 2) := hpowQuarterSq
  have hrootSquare : (p.n : ℝ) ^ ((1 : ℝ) / 2) * (p.n : ℝ) ^ ((1 : ℝ) / 2) = p.n := by
    calc
      (p.n : ℝ) ^ ((1 : ℝ) / 2) * (p.n : ℝ) ^ ((1 : ℝ) / 2) =
          (p.n : ℝ) ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) := (Real.rpow_add hnpos _ _).symm
      _ = p.n := by norm_num [Real.rpow_one]
  have hrootGrow : 2 * (p.n : ℝ) ^ ((1 : ℝ) / 2) ≤ p.n := by
    have hmul : 0 ≤ ((p.n : ℝ) ^ ((1 : ℝ) / 2) - 2) * (p.n : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (sub_nonneg.mpr hroot') (Real.rpow_nonneg hnpos.le _)
    nlinarith [hmul, hrootSquare]
  have hRreal : (R : ℝ) ≤ p.n := by
    have hRhalf : (R : ℝ) ≤ 2 * (p.n : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith [hRsmall, hlogSq]
    exact hRhalf.trans hrootGrow
  have hRnat : R ≤ p.n := by exact_mod_cast hRreal
  have hDRnat : D * R ≤ D * p.n := Nat.mul_le_mul_left D hRnat
  have hDplusNat : D * R + 1 ≤ (D + 1) * p.n := by
    calc
      D * R + 1 ≤ D * p.n + 1 := Nat.add_le_add_right hDRnat 1
      _ ≤ D * p.n + p.n := by omega
      _ = (D + 1) * p.n := by rw [Nat.add_mul]; simp
  have hDplus : (p.D * R + 1 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * p.n := by
    rw [hDp]
    exact_mod_cast hDplusNat
  have hscale : (p.D * R : ℝ) ≤ (D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2) := by
    rw [hDp]
    exact mul_le_mul_of_nonneg_left hRsmall (by positivity)
  have hpref : (R : ℝ) * (p.D * R + 1 : ℝ) ≤
      p.n * ((D + 1 : ℕ) * p.n : ℝ) := by
    calc
      (R : ℝ) * (p.D * R + 1 : ℝ) ≤ p.n * (p.D * R + 1 : ℝ) :=
        mul_le_mul_of_nonneg_right hRreal (by positivity)
      _ ≤ p.n * ((D + 1 : ℕ) * p.n : ℝ) :=
        mul_le_mul_of_nonneg_left hDplus (by positivity)
  have hdPlusNat : ((p.d + 1 : ℕ) : ℝ) ≤ (C_d + 1) * p.n := by
    push_cast
    have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
    nlinarith [hdim]
  have hpow : ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) ≤
      ((C_d + 1) * p.n) ^ (p.D * R) :=
    pow_le_pow_left₀ (by positivity) hdPlusNat (p.D * R)
  let K : ℝ := ((D + 1 : ℕ) : ℝ) * p.n ^ 2 * ((C_d + 1) * p.n) ^ (p.D * R)
  have hcard := hdScaleBallSiteLevels_card_bound Sites start R
    (by rw [hDp]; exact hD) hR hstart hRadius
  have hcount : ((hdScaleBallSiteLevels Sites start R).card : ℝ) ≤ K := by
    calc
      _ ≤ (R : ℝ) * (p.D * R + 1 : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) := hcard
      _ ≤ (p.n * ((D + 1 : ℕ) * p.n : ℝ)) * ((C_d + 1) * p.n) ^ (p.D * R) :=
        calc
          _ ≤ (p.n * ((D + 1 : ℕ) * p.n : ℝ)) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) :=
            mul_le_mul_of_nonneg_right hpref (by positivity)
          _ ≤ (p.n * ((D + 1 : ℕ) * p.n : ℝ)) * ((C_d + 1) * p.n) ^ (p.D * R) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = K := by dsimp [K]; push_cast; ring
  have hlogK : Real.log K =
      Real.log ((D + 1 : ℕ) : ℝ) + 2 * Real.log (p.n : ℝ) +
        (p.D * R : ℝ) * (Real.log (C_d + 1) + Real.log (p.n : ℝ)) := by
    dsimp [K]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_pow]
    rw [Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have hlogsum : Real.log (C_d + 1) + Real.log (p.n : ℝ) ≤
      2 * Real.log (p.n : ℝ) := by linarith
  have hterm : (p.D * R : ℝ) *
      (Real.log (C_d + 1) + Real.log (p.n : ℝ)) ≤
        ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
          (2 * Real.log (p.n : ℝ)) := by
    calc
      _ ≤ ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
          (Real.log (C_d + 1) + Real.log (p.n : ℝ)) :=
        mul_le_mul_of_nonneg_right hscale (by linarith [hlogC, hlog])
      _ ≤ ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
          (2 * Real.log (p.n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogsum (by positivity)
  have hlogCube : (Real.log (p.n : ℝ)) ^ 3 ≤ (p.n : ℝ) ^ (e / 2) := by
    have hcube : (Real.log (p.n : ℝ)) ^ 3 ≤ ((p.n : ℝ) ^ (e / 6)) ^ 3 :=
      pow_le_pow_left₀ hlogNonneg hlogE' 3
    have hpow : ((p.n : ℝ) ^ (e / 6)) ^ 3 = (p.n : ℝ) ^ (e / 2) := by
      calc
        ((p.n : ℝ) ^ (e / 6)) ^ 3 =
            ((p.n : ℝ) ^ (e / 6)) ^ (3 : ℝ) :=
              (Real.rpow_natCast ((p.n : ℝ) ^ (e / 6)) 3).symm
        _ = (p.n : ℝ) ^ ((e / 6) * 3) := (Real.rpow_mul hnpos.le _ _).symm
        _ = (p.n : ℝ) ^ (e / 2) := by congr 1 <;> ring
    exact hcube.trans_eq hpow
  have hlogKle : Real.log K ≤ (p.n : ℝ) ^ e := by
    rw [hlogK]
    have hlinear : Real.log (p.n : ℝ) ≤ (Real.log (p.n : ℝ)) ^ 3 := by
      have hsq : (1 : ℝ) ≤ (Real.log (p.n : ℝ)) ^ 2 := by nlinarith [sq_nonneg (Real.log (p.n : ℝ) - 1)]
      have hmul : 0 ≤ Real.log (p.n : ℝ) * ((Real.log (p.n : ℝ)) ^ 2 - 1) :=
        mul_nonneg hlogNonneg (sub_nonneg.mpr hsq)
      nlinarith [hmul]
    have hpoly :
        Real.log ((D + 1 : ℕ) : ℝ) + 2 * Real.log (p.n : ℝ) +
          ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
            (2 * Real.log (p.n : ℝ)) ≤
          (3 + 4 * (D : ℝ)) * (Real.log (p.n : ℝ)) ^ 3 := by
      calc
        _ ≤ Real.log (p.n : ℝ) + 2 * Real.log (p.n : ℝ) +
              4 * (D : ℝ) * (Real.log (p.n : ℝ)) ^ 3 := by
          rw [show ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
              (2 * Real.log (p.n : ℝ)) =
                4 * (D : ℝ) * (Real.log (p.n : ℝ)) ^ 3 by ring]
          exact add_le_add (add_le_add hlogD (le_refl _)) (le_refl _)
        _ ≤ (3 + 4 * (D : ℝ)) * (Real.log (p.n : ℝ)) ^ 3 := by
          have hthree := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 3)
          calc
            _ = 3 * Real.log (p.n : ℝ) +
                4 * (D : ℝ) * (Real.log (p.n : ℝ)) ^ 3 := by ring
            _ ≤ 3 * (Real.log (p.n : ℝ)) ^ 3 +
                4 * (D : ℝ) * (Real.log (p.n : ℝ)) ^ 3 :=
              add_le_add hthree (le_refl _)
            _ = _ := by ring
    have hbig := hcoef p.n hNcoef
    have hcoeff : (3 + 4 * (D : ℝ)) *
        (p.n : ℝ) ^ (e / 2) ≤ (p.n : ℝ) ^ (e / 2) * (p.n : ℝ) ^ (e / 2) :=
      mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hnpos.le _)
    have hpow : (p.n : ℝ) ^ (e / 2) * (p.n : ℝ) ^ (e / 2) =
        (p.n : ℝ) ^ e := by
      calc
        _ = (p.n : ℝ) ^ (e / 2 + e / 2) := (Real.rpow_add hnpos _ _).symm
        _ = (p.n : ℝ) ^ e := by congr 1 <;> ring
    calc
      Real.log ((D + 1 : ℕ) : ℝ) + 2 * Real.log (p.n : ℝ) +
          (p.D * R : ℝ) * (Real.log (C_d + 1) + Real.log (p.n : ℝ))
          ≤ Real.log ((D + 1 : ℕ) : ℝ) + 2 * Real.log (p.n : ℝ) +
            ((D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2)) *
              (2 * Real.log (p.n : ℝ)) := by linarith [hterm]
      _ ≤ (3 + 4 * (D : ℝ)) * (Real.log (p.n : ℝ)) ^ 3 := hpoly
      _ ≤ (3 + 4 * (D : ℝ)) * (p.n : ℝ) ^ (e / 2) :=
        mul_le_mul_of_nonneg_left hlogCube (by positivity)
      _ ≤ (p.n : ℝ) ^ (e / 2) * (p.n : ℝ) ^ (e / 2) := hcoeff
      _ = (p.n : ℝ) ^ e := hpow
  have hKexp : K ≤ Real.exp ((p.n : ℝ) ^ e) := Real.le_exp_of_log_le hlogKle
  exact hcount.trans hKexp

private theorem height_base_exp_arithmetic (a b₀ θ : ℝ)
    (ha : 0 < a) (hab : a < b₀) (hθ : 0 < θ ∧ θ < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      4 * Real.exp ((n : ℝ) ^ (b₀ / 2) - (n : ℝ) ^ b₀ / 8) ≤
        Real.exp (-((n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ)) := by
  have hgap : 0 < b₀ - a := by linarith
  have hb₀ : 0 < b₀ := lt_trans ha hab
  have hb₀half : 0 < b₀ / 2 := by positivity
  obtain ⟨Nrad, hrad⟩ := heightBaseRadius_le_logsq
  obtain ⟨Nlog, hlog⟩ := log_le_rpow_eventually ((b₀ - a) / 4) (by positivity)
  obtain ⟨NlogOne, hlogOne⟩ := exists_nat_log_ge 1
  obtain ⟨Nhalf, hhalf⟩ := exists_nat_rpow_ge (e := b₀ / 2) (C := 32) hb₀half
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨Nfull, hfull⟩ := exists_nat_rpow_ge
    (e := b₀) (C := 32 * Real.log 4) hb₀
  obtain ⟨Ngap, hNgapPow⟩ := exists_nat_rpow_ge
    (e := (b₀ - a) / 2) (C := 32) (by positivity)
  let Nleft := max Nlog Nhalf
  let Nright := max Nfull Ngap
  let Ntail := max NlogOne (max Nleft Nright)
  let n₀ := max 2 (max Nrad Ntail)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hNradTail : max Nrad Ntail ≤ n := le_trans (Nat.le_max_right 2 _) hn
  have hNtail : Ntail ≤ n := le_trans (Nat.le_max_right Nrad Ntail) hNradTail
  have hNrest : max Nleft Nright ≤ n := le_trans (Nat.le_max_right NlogOne _) hNtail
  have hNlogOne : NlogOne ≤ n := le_trans (Nat.le_max_left NlogOne _) hNtail
  have hNleft : Nleft ≤ n := le_trans (Nat.le_max_left Nleft Nright) hNrest
  have hNright : Nright ≤ n := le_trans (Nat.le_max_right Nleft Nright) hNrest
  have hNrad : Nrad ≤ n := le_trans (Nat.le_max_left Nrad Ntail) hNradTail
  have hNlog : Nlog ≤ n := le_trans (Nat.le_max_left Nlog Nhalf) hNleft
  have hNhalf : Nhalf ≤ n := le_trans (Nat.le_max_right Nlog Nhalf) hNleft
  have hNfull : Nfull ≤ n := le_trans (Nat.le_max_left Nfull Ngap) hNright
  have hNgap : Ngap ≤ n := le_trans (Nat.le_max_right Nfull Ngap) hNright
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 _) hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hn2)
  have hradUpper : (heightBaseRadius n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hrad n hNrad
  have hlogUpper : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((b₀ - a) / 4) := hlog n hNlog
  have hlogLower : 1 ≤ Real.log (n : ℝ) := hlogOne n hNlogOne
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ ((b₀ - a) / 2) := by
    have hpowNonneg : 0 ≤ (n : ℝ) ^ ((b₀ - a) / 4) := Real.rpow_nonneg hnpos.le _
    let t := (b₀ - a) / 4
    have hsum : t + t = (b₀ - a) / 2 := by dsimp [t]; ring
    calc
      (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ ((b₀ - a) / 4) * (n : ℝ) ^ ((b₀ - a) / 4) :=
        (mul_le_mul_of_nonneg_right hlogUpper hlogNonneg).trans
          (mul_le_mul_of_nonneg_left hlogUpper hpowNonneg)
      _ = (n : ℝ) ^ ((b₀ - a) / 2) := by
        calc
          _ = (n : ℝ) ^ (t + t) := (Real.rpow_add hnpos t t).symm
          _ = (n : ℝ) ^ ((b₀ - a) / 2) := by rw [hsum]
  have hradPow : (heightBaseRadius n : ℝ) ^ θ ≤ heightBaseRadius n := by
    have hRadOne : (1 : ℝ) ≤ heightBaseRadius n := by
      exact_mod_cast Nat.le_max_left 1 _
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hRadOne hθ.2.le
  have hradPowUpper : (n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ ≤
      (n : ℝ) ^ b₀ / 16 := by
    have hlogFactor : (heightBaseRadius n : ℝ) ≤ 2 * (n : ℝ) ^ ((b₀ - a) / 2) := by
      calc
        (heightBaseRadius n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 := hradUpper
        _ ≤ 2 * (n : ℝ) ^ ((b₀ - a) / 2) := mul_le_mul_of_nonneg_left hlogSq (by norm_num)
    have hnGap : 32 ≤ (n : ℝ) ^ ((b₀ - a) / 2) := hNgapPow n hNgap
    have hbase : (n : ℝ) ^ a * (heightBaseRadius n : ℝ) ≤
        2 * (n : ℝ) ^ (a + (b₀ - a) / 2) := by
      calc
        _ ≤ (n : ℝ) ^ a * (2 * (n : ℝ) ^ ((b₀ - a) / 2)) :=
          mul_le_mul_of_nonneg_left hlogFactor (Real.rpow_nonneg hnpos.le _)
        _ = 2 * ((n : ℝ) ^ a * (n : ℝ) ^ ((b₀ - a) / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hnpos]
    have hexp : a + (b₀ - a) / 2 ≤ b₀ := by linarith
    have hmono : (n : ℝ) ^ (a + (b₀ - a) / 2) ≤ (n : ℝ) ^ b₀ :=
      Real.rpow_le_rpow_of_exponent_le hn1 hexp
    have hquarter : 2 * (n : ℝ) ^ (a + (b₀ - a) / 2) ≤ (n : ℝ) ^ b₀ / 16 := by
      let gap : ℝ := (b₀ - a) / 2
      let mid : ℝ := a + gap
      have hmidGap : mid + gap = b₀ := by dsimp [mid, gap]; ring
      have hfactor : (n : ℝ) ^ b₀ = (n : ℝ) ^ mid * (n : ℝ) ^ gap := by
        calc
          (n : ℝ) ^ b₀ = (n : ℝ) ^ (mid + gap) := by rw [hmidGap]
          _ = (n : ℝ) ^ mid * (n : ℝ) ^ gap := Real.rpow_add hnpos mid gap
      have hlarge : 32 * (n : ℝ) ^ mid ≤ (n : ℝ) ^ b₀ := by
        calc
          32 * (n : ℝ) ^ mid ≤
              (n : ℝ) ^ gap * (n : ℝ) ^ mid := by
            exact mul_le_mul_of_nonneg_right hnGap (Real.rpow_nonneg hnpos.le _)
          _ = (n : ℝ) ^ b₀ := by rw [hfactor]; ring
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
      nlinarith [hlarge]
    have hbasePow : (n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ ≤
        2 * (n : ℝ) ^ (a + (b₀ - a) / 2) := by
      calc
        _ ≤ (n : ℝ) ^ a * (heightBaseRadius n : ℝ) :=
          mul_le_mul_of_nonneg_left hradPow (Real.rpow_nonneg hnpos.le _)
        _ ≤ 2 * (n : ℝ) ^ (a + (b₀ - a) / 2) := hbase
    exact hbasePow.trans hquarter
  have hhalfHi : (n : ℝ) ^ (b₀ / 2) ≤ (n : ℝ) ^ b₀ / 32 := by
    have hnHalf : 32 ≤ (n : ℝ) ^ (b₀ / 2) := hhalf n hNhalf
    have hpow : (n : ℝ) ^ (b₀ / 2) * (n : ℝ) ^ (b₀ / 2) = (n : ℝ) ^ b₀ := by
      calc
        _ = (n : ℝ) ^ (b₀ / 2 + b₀ / 2) := (Real.rpow_add hnpos _ _).symm
        _ = _ := by congr 1 <;> ring
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2
    rw [← hpow]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hnHalf (Real.rpow_nonneg hnpos.le (b₀ / 2)))
  have hfullHi : Real.log 4 ≤ (n : ℝ) ^ b₀ / 32 := by
    have h := hfull n hNfull
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2
    simpa [mul_comm] using h
  have hExp :
      4 * Real.exp ((n : ℝ) ^ (b₀ / 2) - (n : ℝ) ^ b₀ / 8) ≤
        Real.exp (-((n : ℝ) ^ b₀ / 16)) := by
    have hmul : 4 * Real.exp ((n : ℝ) ^ (b₀ / 2) - (n : ℝ) ^ b₀ / 8) =
        Real.exp (Real.log 4 + (n : ℝ) ^ (b₀ / 2) - (n : ℝ) ^ b₀ / 8) := by
      calc
        _ = Real.exp (Real.log 4) *
            Real.exp ((n : ℝ) ^ (b₀ / 2) - (n : ℝ) ^ b₀ / 8) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
    rw [hmul]
    apply Real.exp_le_exp.mpr
    linarith [hhalfHi, hfullHi]
  apply hExp.trans (Real.exp_le_exp.mpr ?_)
  exact neg_le_neg hradPowUpper

private theorem choose_layer_step_bound (d r k : ℕ) (hr : 0 < r)
    (hrk : r < k) (hkd : k ≤ d) :
    (Nat.choose d k : ℝ) ≤ (Nat.choose d (k - 1) : ℝ) * ((d : ℝ) / r) := by
  have hratio := hammingLayer_ratio d k (by omega) hkd
  have hratioR : (Nat.choose d (k - 1) : ℝ) * (d - k + 1 : ℕ) =
      (Nat.choose d k : ℝ) * k := by exact_mod_cast hratio
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt hrk)
  have hprevNonneg : 0 ≤ (Nat.choose d (k - 1) : ℝ) := Nat.cast_nonneg _
  have hcurrNonneg : 0 ≤ (Nat.choose d k : ℝ) := Nat.cast_nonneg _
  have hlayer : (d - k + 1 : ℕ) ≤ d := by omega
  have hnum : (Nat.choose d k : ℝ) * r ≤ (Nat.choose d (k - 1) : ℝ) * d := by
    calc
      (Nat.choose d k : ℝ) * r ≤ (Nat.choose d k : ℝ) * k :=
        mul_le_mul_of_nonneg_left hrkR hcurrNonneg
      _ = (Nat.choose d (k - 1) : ℝ) * (d - k + 1 : ℕ) := hratioR.symm
      _ ≤ (Nat.choose d (k - 1) : ℝ) * d :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlayer) hprevNonneg
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    (Nat.choose d k : ℝ) ≤ (Nat.choose d (k - 1) : ℝ) * d / r :=
      (le_div_iff₀ hrR).2 hnum
    _ = (Nat.choose d (k - 1) : ℝ) * ((d : ℝ) / r) := by ring

private theorem choose_growth_bound (d r t : ℕ) (hr : 0 < r)
    (hbound : r + t ≤ d) :
    (Nat.choose d (r + t) : ℝ) ≤ (Nat.choose d r : ℝ) * ((d : ℝ) / r) ^ t := by
  revert hbound
  induction t with
  | zero => intro hbound; simp
  | succ t ih =>
      intro hbound
      have hprev : r + t ≤ d := by omega
      have hih := ih hprev
      have hstep := choose_layer_step_bound d r (r + t + 1) hr (by omega) (by omega)
      calc
        (Nat.choose d (r + (t + 1)) : ℝ) ≤
            (Nat.choose d (r + t) : ℝ) * ((d : ℝ) / r) := by
              simpa [Nat.add_assoc] using hstep
        _ ≤ ((Nat.choose d r : ℝ) * ((d : ℝ) / r) ^ t) * ((d : ℝ) / r) :=
              mul_le_mul_of_nonneg_right hih (by positivity)
        _ = (Nat.choose d r : ℝ) * ((d : ℝ) / r) ^ (t + 1) := by
              rw [pow_succ]
              ring

private theorem hammingBall_volume_add_bound {d r D : ℕ} (hr : 0 < r)
    (hRadius : r + D ≤ d) :
    (∑ i ∈ Finset.range (r + D + 1), (Nat.choose d i : ℝ)) ≤
      (∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ)) *
        (1 + (D : ℝ) * ((d : ℝ) / r) ^ D) := by
  let x : ℝ := (d : ℝ) / r
  let V₀ : ℝ := ∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ)
  let tail : ℝ := ∑ i ∈ Finset.Ico (r + 1) (r + D + 1), (Nat.choose d i : ℝ)
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hrd : (r : ℝ) ≤ d := by exact_mod_cast (Nat.le_trans (Nat.le_add_right r D) hRadius)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hrReal).2 (by nlinarith [hrd])
  have hsplit :
      (∑ i ∈ Finset.range (r + D + 1), (Nat.choose d i : ℝ)) = V₀ + tail := by
    dsimp [V₀, tail]
    simpa [Nat.add_assoc] using
      (Finset.sum_range_add_sum_Ico (fun i => (Nat.choose d i : ℝ))
        (show r + 1 ≤ r + D + 1 by omega)).symm
  have hterm : ∀ i ∈ Finset.Ico (r + 1) (r + D + 1),
      (Nat.choose d i : ℝ) ≤ (Nat.choose d r : ℝ) * x ^ D := by
    intro i hi
    have hir : r < i := by simp only [Finset.mem_Ico] at hi; omega
    have hid : i ≤ d := by
      simp only [Finset.mem_Ico] at hi
      omega
    have hgrowth := choose_growth_bound d r (i - r) hr (by omega)
    have hexp : x ^ (i - r) ≤ x ^ D :=
      pow_le_pow_right₀ hx (by simp only [Finset.mem_Ico] at hi; omega)
    calc
      (Nat.choose d i : ℝ) = (Nat.choose d (r + (i - r)) : ℝ) := by
        have hri : r ≤ i := Nat.le_of_lt hir
        rw [Nat.add_sub_of_le hri]
      _ ≤ (Nat.choose d r : ℝ) * x ^ (i - r) := by simpa [x] using hgrowth
      _ ≤ (Nat.choose d r : ℝ) * x ^ D :=
        mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
  have htail : tail ≤ (D : ℝ) * (Nat.choose d r : ℝ) * x ^ D := by
    dsimp [tail]
    calc
      (∑ i ∈ Finset.Ico (r + 1) (r + D + 1), (Nat.choose d i : ℝ)) ≤
          ∑ i ∈ Finset.Ico (r + 1) (r + D + 1),
            (Nat.choose d r : ℝ) * x ^ D := by
              apply Finset.sum_le_sum
              intro i hi
              exact hterm i hi
      _ = (Finset.Ico (r + 1) (r + D + 1)).card *
            ((Nat.choose d r : ℝ) * x ^ D) := by simp
      _ = (D : ℝ) * (Nat.choose d r : ℝ) * x ^ D := by
            have hcard : (Finset.Ico (r + 1) (r + D + 1)).card = D := by
              rw [Nat.card_Ico]
              omega
            rw [hcard]
            ring
  have hchoose : (Nat.choose d r : ℝ) ≤ V₀ := by
    dsimp [V₀]
    exact Finset.single_le_sum (fun i hi => Nat.cast_nonneg _) (by simp)
  calc
    (∑ i ∈ Finset.range (r + D + 1), (Nat.choose d i : ℝ))
        = V₀ + tail := hsplit
    _ ≤ V₀ + (D : ℝ) * V₀ * x ^ D := by
          have hcoeff : (D : ℝ) * (Nat.choose d r : ℝ) * x ^ D ≤
              (D : ℝ) * V₀ * x ^ D := by
            calc
              (D : ℝ) * (Nat.choose d r : ℝ) * x ^ D =
                  ((D : ℝ) * x ^ D) * (Nat.choose d r : ℝ) := by ring
              _ ≤ ((D : ℝ) * x ^ D) * V₀ :=
                mul_le_mul_of_nonneg_left hchoose (by positivity)
              _ = (D : ℝ) * V₀ * x ^ D := by ring
          nlinarith [htail, hcoeff]
    _ = V₀ * (1 + (D : ℝ) * x ^ D) := by ring

private theorem height_crowd_active_count_eq {p : HDParams} (P A : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    (∑ ℓ : p.Loc, if ℓ ∈ heightCrowdIDs P v j ∧ A ℓ = true then (1 : ℝ) else 0) =
    ((Finset.univ.filter (fun u : CubeVertex p.d =>
      P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D)).card : ℝ) := by
  calc
    (∑ ℓ : p.Loc, if ℓ ∈ heightCrowdIDs P v j ∧ A ℓ = true then (1 : ℝ) else 0)
        = ∑ ℓ : p.Loc, if ℓ.2 = j ∧ P ℓ = true ∧
            _root_.hammingDist ℓ.1 v ≤ p.r + p.D ∧ A ℓ = true then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              simp [heightCrowdIDs, and_assoc, and_left_comm, and_comm]
    _ = _ := height_crowd_count_eq_sum P A v j

private theorem heightCrowdRegion_card_eq_vertex_ball {p : HDParams}
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    ((heightCrowdRegion v j).card : ℝ) =
      ((Finset.univ.filter (fun u : CubeVertex p.d =>
        _root_.hammingDist u v ≤ p.r + p.D)).card : ℝ) := by
  simpa [heightCrowdRegion, Finset.sum_boole, and_assoc, and_left_comm, and_comm] using
    (height_crowd_count_eq_sum (fun _ => true) (fun _ => true) v j)

private theorem heightCrowdRegion_card_eq_choose_sum {p : HDParams}
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (hr : p.r + p.D ≤ p.d) :
    ((heightCrowdRegion v j).card : ℝ) =
      ∑ i ∈ Finset.range (p.r + p.D + 1), (Nat.choose p.d i : ℝ) := by
  have hball := cube_ball_card_eq_choose_sum v hr
  have hregion := heightCrowdRegion_card_eq_vertex_ball v j
  rw [hregion]
  exact_mod_cast hball

theorem heightCrowdRegion_volume_bounds {p : HDParams}
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (hr : 0 < p.r)
    (hRadius : p.r + p.D ≤ p.d) :
    (p.V : ℝ) ≤ (heightCrowdRegion v j).card ∧
      (heightCrowdRegion v j).card ≤ (p.V : ℝ) *
        (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) := by
  have hV : (p.V : ℝ) =
      ∑ i ∈ Finset.range (p.r + 1), (Nat.choose p.d i : ℝ) := by
    simp [HDParams.V, Nat.cast_sum]
  have hRegion : (heightCrowdRegion v j).card =
      ∑ i ∈ Finset.range (p.r + p.D + 1), (Nat.choose p.d i : ℝ) :=
    heightCrowdRegion_card_eq_choose_sum v j hRadius
  have hsubset : Finset.range (p.r + 1) ⊆ Finset.range (p.r + p.D + 1) :=
    Finset.range_mono (by omega)
  constructor
  · rw [hV, hRegion]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro i hi hnot
      positivity)
  · rw [hV, hRegion]
    exact hammingBall_volume_add_bound hr hRadius

/-- The probability of a bad site-level is controlled by the hole bound and a
fixed-set activation crowd tail. -/
theorem height_bad_activation_bound {p : HDParams} (P : p.Loc → Bool)
    (E : p.EligMap) (v : CubeVertex p.d) (j : Fin (p.H + 1))
    (hmean : 2 * (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
      (p.n : ℝ) ^ p.b)
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => p.Bad P A E v j) ≤
      Real.exp (-((E v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) +
        Real.exp (-((heightCrowdIDs P v j).card *
          ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) := by
  apply le_trans (finprob_pr_mono _ _ _ ?_)
  · exact activation_hole_or_crowd (E v j) (heightCrowdIDs P v j)
      ((p.n : ℝ) ^ p.b) hmean hq0 hq1
  · intro A hbad
    unfold HDParams.Bad at hbad
    rcases hbad with hhole | hcrowd
    · exact Or.inl hhole
    · right
      rw [← height_crowd_active_count_eq P A v j] at hcrowd
      exact hcrowd

/-- At a legal site-level, an eligible-set hole has mean at least `n^b₀/3`.
Together with a regular crowd count this gives an `exp(-Ω(n^b₀))` bound. -/
theorem height_bad_activation_bound_rates {p : HDParams} (P : p.Loc → Bool)
    (E : p.EligMap) (v : CubeVertex p.d) (j : Fin (p.H + 1))
    (hlam : 0 < p.lam) (hlegal : p.LegalAt P E v j)
    (hmeanUpper : 2 * (heightCrowdIDs P v j).card *
      ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b)
    (hmeanLower : (p.n : ℝ) ^ p.b₀ / 2 ≤
      (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam))
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => p.Bad P A E v j) ≤
      2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
  have hlamq : p.lam * ((p.n : ℝ) ^ p.b₀ / p.lam) = (p.n : ℝ) ^ p.b₀ := by
    field_simp
  have hholemean : (p.n : ℝ) ^ p.b₀ / 3 ≤
      ((E v j).card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
    calc
      (p.n : ℝ) ^ p.b₀ / 3 = (p.lam / 3) * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
        field_simp [hlam.ne']
      _ ≤ ((E v j).card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) :=
        mul_le_mul_of_nonneg_right hlegal.2 hq0.le
  have hholeExp : Real.exp (-(((E v j).card : ℝ) *
      ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) ≤ Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcrowdExp : Real.exp (-((heightCrowdIDs P v j).card *
      ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) ≤ Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    p.actLaw.pr (fun A => p.Bad P A E v j)
        ≤ Real.exp (-((E v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) +
            Real.exp (-((heightCrowdIDs P v j).card *
              ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) :=
              height_bad_activation_bound P E v j hmeanUpper hq0 hq1
    _ ≤ Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) + Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) :=
      add_le_add hholeExp hcrowdExp
    _ = 2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by ring

/-- Averaging a fixed-site bad event over positions, an auxiliary finite law, and
activations. The eligibility map may depend on positions and auxiliary data; the
only condition is legality before activations are drawn. -/
theorem height_bad_legal_position_average {p : HDParams} {Aux : Type*} [Fintype Aux]
    (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites) (j : Fin (p.H + 1))
    (hLam : 0 < p.lam)
    (hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (hqP0 : 0 < p.lam / (p.V : ℝ)) (hqP1 : p.lam / (p.V : ℝ) ≤ 1)
    (hregionLower : (p.n : ℝ) ^ p.b₀ ≤
      (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
        ((p.n : ℝ) ^ p.b₀ / p.lam))
    (hregionUpper : 4 * (heightCrowdRegion v j).card *
      (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j) ≤
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 8) +
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 3) +
      2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
  classical
  let T := heightCrowdRegion v j
  let μ : ℝ := (T.card : ℝ) * (p.lam / (p.V : ℝ))
  let posCount : (p.Loc → Bool) → ℝ := fun P =>
    ∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0
  let posBad : (p.Loc → Bool) → Prop := fun P =>
    posCount P ≤ μ / 2 ∨ 2 * μ < posCount P
  let outer : FinProb ((p.Loc → Bool) × Aux) := p.posLaw.prod πAux
  let badSite : ((p.Loc → Bool) × Aux) → (p.Loc → Bool) → Prop := fun z A =>
    p.Legal z.1 (Esel z.1 z.2) Sites ∧ p.Bad z.1 A (Esel z.1 z.2) v j
  let δ : ℝ := 2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 6)
  have hposTails := position_count_tails T hqP0 hqP1
  have hposBad : p.posLaw.pr posBad ≤
      Real.exp (-μ / 8) + Real.exp (-μ / 3) := by
    calc
      p.posLaw.pr posBad ≤
          p.posLaw.pr (fun P => posCount P ≤ μ / 2) +
            p.posLaw.pr (fun P => 2 * μ < posCount P) := finprob_pr_or_le _ _ _
      _ ≤ Real.exp (-μ / 8) + Real.exp (-μ / 3) := by
        apply add_le_add
        · simpa [posCount, μ, T] using hposTails.1
        · simpa [posCount, μ, T, mul_assoc] using hposTails.2
  have houterBad : outer.pr (fun z => posBad z.1) = p.posLaw.pr posBad := by
    simpa [outer] using finprob_prod_pr_left p.posLaw πAux posBad
  have hsections : ∀ z, ¬ posBad z.1 → p.actLaw.pr (badSite z) ≤ δ := by
    intro z hz
    let P := z.1
    let E := Esel z.1 z.2
    have hposLow : μ / 2 < (heightCrowdIDs P v j).card := by
      have hcount := heightCrowdIDs_card_eq_position_count P v j
      have hnot : ¬ posCount P ≤ μ / 2 := by
        intro h
        exact hz (Or.inl (by simpa [posCount] using h))
      have hlt : μ / 2 < posCount P := lt_of_not_ge hnot
      rw [hcount]
      simpa [posCount, μ, T] using hlt
    have hposHigh : (heightCrowdIDs P v j).card ≤ 2 * μ := by
      have hcount := heightCrowdIDs_card_eq_position_count P v j
      have hnot : ¬ 2 * μ < posCount P := by
        intro h
        exact hz (Or.inr (by simpa [posCount] using h))
      have hle : posCount P ≤ 2 * μ := le_of_not_gt hnot
      rw [hcount]
      simpa [posCount, μ, T] using hle
    have hmeanLower : (p.n : ℝ) ^ p.b₀ / 2 ≤
        (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
      have hprod : (μ / 2) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
          (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) :=
        mul_le_mul_of_nonneg_right hposLow.le hqA0.le
      dsimp [μ, T] at hprod
      have hnorm : (p.n : ℝ) ^ p.b₀ ≤
          (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
            ((p.n : ℝ) ^ p.b₀ / p.lam) := hregionLower
      nlinarith
    have hmeanUpper : 2 * (heightCrowdIDs P v j).card *
        ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b := by
      have hprod : (heightCrowdIDs P v j).card *
          ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
          (2 * μ) * ((p.n : ℝ) ^ p.b₀ / p.lam) :=
        mul_le_mul_of_nonneg_right hposHigh hqA0.le
      dsimp [μ, T] at hprod
      have hnorm : 4 * (heightCrowdRegion v j).card *
          (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b :=
        hregionUpper
      nlinarith
    by_cases hlegal : p.Legal z.1 E Sites
    · have hAt : p.LegalAt z.1 E v j := hlegal v hv j
      have hlocal := height_bad_activation_bound_rates z.1 E v j hLam hAt
        hmeanUpper hmeanLower hqA0 hqA1
      calc
        p.actLaw.pr (badSite z) ≤ p.actLaw.pr (fun A => p.Bad z.1 A E v j) := by
          apply finprob_pr_mono
          intro A hA
          exact hA.2
        _ ≤ δ := by simpa [δ] using hlocal
    · have hzero : p.actLaw.pr (badSite z) = 0 := by
        simp [badSite, E, hlegal, FinProb.pr]
      rw [hzero]
      positivity
  have hprod := finprob_prod_pr_le_bad_or_small outer p.actLaw
    (fun z => posBad z.1) badSite δ (by positivity) hsections
  calc
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j)
        ≤ outer.pr (fun z => posBad z.1) + δ := by
          simpa [outer, badSite] using hprod
    _ = p.posLaw.pr posBad + δ := by rw [houterBad]
    _ ≤ Real.exp (-μ / 8) + Real.exp (-μ / 3) + δ := by
          linarith [hposBad]
    _ = _ := by simp [δ, μ, T, add_assoc]

/-- A volume-ratio bound supplies the local crowd-mean hypotheses needed by the
position-averaged site-level estimate. -/
theorem height_bad_legal_position_average_of_volume {p : HDParams}
    {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
    (Esel : (p.Loc → Bool) → Aux → p.EligMap) (Sites : p.Sites)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (j : Fin (p.H + 1))
    (hLam : 0 < p.lam) (hV : 0 < (p.V : ℝ))
    (hr : 0 < p.r) (hRadius : p.r + p.D ≤ p.d)
    (hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (hqP1 : p.lam / (p.V : ℝ) ≤ 1)
    (hband : 4 * (p.n : ℝ) ^ p.b₀ *
      (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤ (p.n : ℝ) ^ p.b) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j) ≤
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 8) +
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 3) +
      2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
  have hvolume := heightCrowdRegion_volume_bounds v j hr hRadius
  have hqP0 : 0 < p.lam / (p.V : ℝ) := div_pos hLam hV
  have hproduct : (p.lam / (p.V : ℝ)) *
      ((p.n : ℝ) ^ p.b₀ / p.lam) = (p.n : ℝ) ^ p.b₀ / (p.V : ℝ) := by
    field_simp [hLam.ne', hV.ne']
  have hregionLower : (p.n : ℝ) ^ p.b₀ ≤
      (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
        ((p.n : ℝ) ^ p.b₀ / p.lam) := by
    calc
      (p.n : ℝ) ^ p.b₀ = (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
        field_simp [hV.ne']
      _ ≤ (heightCrowdRegion v j).card * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) :=
        mul_le_mul_of_nonneg_right hvolume.1 (div_nonneg (Real.rpow_nonneg (by positivity) _)
          hV.le)
      _ = (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) := by
            calc
              _ = (heightCrowdRegion v j).card *
                  ((p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by
                    field_simp [hLam.ne', hV.ne']
              _ = _ := by ring
  have hratio : (heightCrowdRegion v j).card / (p.V : ℝ) ≤
      1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D := by
    apply (div_le_iff₀ hV).2
    nlinarith [hvolume.2]
  have hregionUpper : 4 * (heightCrowdRegion v j).card *
      (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b := by
    calc
      4 * (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) =
        4 * (heightCrowdRegion v j).card *
          ((p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by ring
      _ = 4 * (heightCrowdRegion v j).card * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
        rw [hproduct]
      _ = 4 * (p.n : ℝ) ^ p.b₀ *
          ((heightCrowdRegion v j).card / (p.V : ℝ)) := by ring
      _ ≤ 4 * (p.n : ℝ) ^ p.b₀ *
          (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ (p.n : ℝ) ^ p.b := hband
  exact height_bad_legal_position_average πAux Esel Sites v hv j hLam hqA0 hqA1
    hqP0 hqP1 hregionLower hregionUpper

/-- The fixed-site bad-event estimate for every sufficiently large admissible
instance. This is the local probabilistic input to the scale-zero path bound. -/
theorem height_bad_site_average_of_admissible
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites)
        (j : Fin (p.H + 1)) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j) ≤
          Real.exp (-((heightCrowdRegion v j).card : ℝ) *
            (p.lam / (p.V : ℝ)) / 8) +
          Real.exp (-((heightCrowdRegion v j).card : ℝ) *
            (p.lam / (p.V : ℝ)) / 3) +
          2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6) := by
  obtain ⟨nG, hG⟩ := height_local_geometry_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nV, hV⟩ := height_volume_ge_lambda_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  let n₀ := max 2 (max nG nV)
  refine ⟨n₀, ?_⟩
  intro p hD hH hlam hb₀ hb hn hdimLo hdimHi hreg
  have hnG : nG ≤ p.n := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right 2 _) hn)
  have hnV : nV ≤ p.n := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right 2 _) hn)
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left _ _) hn
  have hgeom := hG p hD hb₀ hb hnG hdimLo hdimHi hreg
  have hvolume := hV p hD hlam hnV hdimLo hreg
  have hlamPos : 0 < p.lam := by
    rw [hlam]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p.n)) _
  have hVpos : 0 < (p.V : ℝ) := lt_of_lt_of_le hlamPos hvolume
  have hnPos : 0 < (p.n : ℝ) := by positivity
  have hnOne : (1 : ℝ) ≤ p.n := by exact_mod_cast (show 1 ≤ p.n by omega)
  have hb₀pos : 0 < b₀ := hp.hb.1
  have hqA0 : 0 < (p.n : ℝ) ^ b₀ / p.lam := div_pos (Real.rpow_pos_of_pos hnPos _) hlamPos
  have hJ0b0 : b₀ ≤ J₀ := by linarith [hp.hJ, hp.hb.1, hp.hb.2.1, hp.hb.2.2]
  have hqA1 : (p.n : ℝ) ^ b₀ / p.lam ≤ 1 := by
    rw [hlam]
    have hpow : (p.n : ℝ) ^ b₀ ≤ (p.n : ℝ) ^ J₀ :=
      Real.rpow_le_rpow_of_exponent_le hnOne hJ0b0
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hnPos _)).2 (by simpa using hpow)
  have hqP1 : p.lam / (p.V : ℝ) ≤ 1 := by
    rw [div_le_one hVpos]
    exact_mod_cast hvolume
  have hqA0' : 0 < (p.n : ℝ) ^ p.b₀ / p.lam := by simpa [hb₀] using hqA0
  have hqA1' : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 := by simpa [hb₀] using hqA1
  have hGeom' : 4 * (p.n : ℝ) ^ p.b₀ *
      (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) ≤ (p.n : ℝ) ^ p.b := by
    simpa [hb₀, hb] using hgeom.2.2
  intro Sites v hv j Aux inst πAux Esel
  simpa [hb₀] using
    (height_bad_legal_position_average_of_volume πAux Esel Sites v hv j hlamPos hVpos
      hgeom.1 hgeom.2.1 hqA0' hqA1' hqP1 hGeom')

/-- A finite union of site-level bad events is bounded by the sum of the individual
position-averaged bounds. -/
theorem height_bad_finite_union_bound {p : HDParams} {Aux : Type*} [Fintype Aux]
    (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap)
    (Sites : p.Sites) (T : Finset (CubeVertex p.d × Fin (p.H + 1))) (δ : ℝ)
    (hSites : ∀ x ∈ T, x.1 ∈ Sites)
    (hLocal : ∀ v ∈ Sites, ∀ j : Fin (p.H + 1),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j) ≤ δ) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        ∃ x ∈ T, p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2) ≤
      (T.card : ℝ) * δ := by
  classical
  let law := (p.posLaw.prod πAux).prod p.actLaw
  let F : (CubeVertex p.d × Fin (p.H + 1)) →
      (((p.Loc → Bool) × Aux) × (p.Loc → Bool)) → Prop := fun x ω =>
    p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
      p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2
  have hEq : (fun ω => p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
      ∃ x ∈ T, p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2) =
      (fun ω => ∃ x ∈ T, F x ω) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨hlegal, x, hxT, hbad⟩
      exact ⟨x, hxT, hlegal, hbad⟩
    · rintro ⟨x, hxT, hlegal, hbad⟩
      exact ⟨hlegal, x, hxT, hbad⟩
  rw [hEq]
  calc
    law.pr (fun ω => ∃ x ∈ T, F x ω) ≤ ∑ x ∈ T, law.pr (F x) :=
      finprob_pr_finset_exists_le law T F
    _ ≤ ∑ x ∈ T, δ := by
      apply Finset.sum_le_sum
      intro x hx
      exact hLocal x.1 (hSites x hx) x.2
    _ = (T.card : ℝ) * δ := by simp

/-- The stopped scale-path failure is contained in a finite union of bad site-levels in its
consultation ball, so the local estimate gives a direct probability bound for the base scale. -/
theorem hdScaleFailure_probability_bound
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (start : HDState p) (R : ℕ) (η : ℝ)
        (hR : 0 < R) (hη : η < 1) {Aux : Type*} [Fintype Aux]
        (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) start R η) ≤
          (hdScaleBallSiteLevels Sites start R).card *
            (Real.exp (-p.lam / 8) + Real.exp (-p.lam / 3) +
              2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6)) := by
  classical
  obtain ⟨nG, hG⟩ := height_local_geometry_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nV, hV⟩ := height_volume_ge_lambda_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nLocal, hLocalAll⟩ := height_bad_site_average_of_admissible
    J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  let n₀ := max 2 (max nG (max nV nLocal))
  refine ⟨n₀, ?_⟩
  intro p hD hH hlam hb₀ hb hn hdLo hdHi hreg Sites start R η hR hη Aux inst πAux Esel
  have hNinner : max nG (max nV nLocal) ≤ p.n := le_trans (Nat.le_max_right 2 _) hn
  have hnG : nG ≤ p.n := le_trans (Nat.le_max_left _ _) hNinner
  have hNtail : max nV nLocal ≤ p.n := le_trans (Nat.le_max_right _ _) hNinner
  have hnV : nV ≤ p.n := le_trans (Nat.le_max_left _ _) hNtail
  have hnLocal : nLocal ≤ p.n := le_trans (Nat.le_max_right _ _) hNtail
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left _ _) hn
  have hGeom := hG p hD hb₀ hb hnG hdLo hdHi hreg
  have hVol := hV p hD hlam hnV hdLo hreg
  have hsiteLocal := hLocalAll p hD hH hlam hb₀ hb hnLocal hdLo hdHi hreg
    Sites
  have hDpos : 0 < p.D := by
    rw [hD]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one hp.hD
  have hLamPos : 0 < p.lam := by
    rw [hlam]
    exact Real.rpow_pos_of_pos (by positivity : 0 < (p.n : ℝ)) _
  have hVpos : 0 < (p.V : ℝ) := lt_of_lt_of_le hLamPos hVol
  let T := hdScaleBallSiteLevels Sites start R
  let δ : ℝ := Real.exp (-p.lam / 8) + Real.exp (-p.lam / 3) +
    2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6)
  have hLocal : ∀ v ∈ Sites, ∀ j : Fin (p.H + 1),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j) ≤ δ := by
    intro v hv j
    have hsite := @hsiteLocal v hv j Aux (inferInstance) πAux Esel
    have hgeom := heightCrowdRegion_volume_bounds v j hGeom.1 hGeom.2.1
    have hmu : p.lam ≤ (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) := by
      calc
        p.lam = (p.V : ℝ) * (p.lam / (p.V : ℝ)) := by field_simp [hVpos.ne']
        _ ≤ (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) :=
          mul_le_mul_of_nonneg_right hgeom.1 (div_nonneg hLamPos.le hVpos.le)
    have hterm1 : Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 8) ≤ Real.exp (-p.lam / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hmu]
    have hterm2 : Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 3) ≤ Real.exp (-p.lam / 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hmu]
    dsimp [δ]
    linarith [hsite, hterm1, hterm2]
  have hsubset : ∀ ω : ((p.Loc → Bool) × Aux) × (p.Loc → Bool),
      (p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) start R η) →
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        ∃ x ∈ T, p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 := by
    intro ω hω
    obtain ⟨v, j, hv, hbad, hdist⟩ := hdScaleFailure_has_local_bad
      Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) start R η hDpos hR hη hω.2
    rcases hbad with ⟨hj, hbad⟩
    let jFin : Fin (p.H + 1) := ⟨j, hj⟩
    have hdist' : hdScaleDistance p.D start (v, jFin.val) < R := by simpa [jFin] using hdist
    have hmem : (v, jFin) ∈ T := by
      change (v, jFin) ∈ hdScaleBallSiteLevels Sites start R
      simp [hdScaleBallSiteLevels, hv, hdist']
    exact ⟨hω.1, (v, jFin), hmem, hbad⟩
  have hT : ∀ x ∈ T, x.1 ∈ Sites := by
    intro x hx
    change x ∈ hdScaleBallSiteLevels Sites start R at hx
    exact (Finset.mem_filter.mp hx).2.1
  have hunion := height_bad_finite_union_bound πAux Esel Sites T δ hT hLocal
  calc
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) start R η)
        ≤ ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            ∃ x ∈ T, p.Bad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2) :=
              finprob_pr_mono _ _ _ hsubset
    _ ≤ (T.card : ℝ) * δ := hunion
    _ = _ := by simp [T, δ, hdScaleBallSiteLevels]

/-- The actual bad-path event at the logarithmic initial scale has the required
`exp(-n^a R₀^θ)` bound, uniformly in the finite auxiliary eligibility rule. -/
theorem height_scale_zero_failure_bound
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)
              (v, 0) (heightBaseRadius p.n) ((1 : ℝ) / 2)) ≤
          Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) := by
  classical
  rcases hp.hsz with ⟨hσpos, hσζ, hζone, hθpos, hθone⟩
  rcases hp.hb with ⟨hb₀pos, hb₀b, hbone⟩
  obtain ⟨nFail, hFail⟩ := hdScaleFailure_probability_bound J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  have hCdpos : 0 < C_d := lt_of_lt_of_le hp.hd.1 hp.hd.2
  obtain ⟨nCount, hCount⟩ := hdScaleBallSiteLevels_exp_bound D C_d (b₀ / 2)
    hp.hD hCdpos (by linarith [hb₀pos])
  obtain ⟨nRad, hRad⟩ := heightBaseRadius_le_logsq
  obtain ⟨nLogOne, hLogOne⟩ := exists_nat_log_ge 1
  obtain ⟨nLog, hLog⟩ := log_le_rpow_eventually ((1 : ℝ) / 4) (by norm_num)
  let Croot : ℝ := 2 * (D : ℝ) / c_d
  have hDrealPos : 0 < (D : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hp.hD)
  have hCrootPos : 0 < Croot := by
    change 0 < 2 * (D : ℝ) / c_d
    exact div_pos (mul_pos (by norm_num) hDrealPos) hp.hd.1
  obtain ⟨nRoot, hRoot⟩ := exists_nat_rpow_ge
    (e := (1 : ℝ) / 2) (C := Croot) (by norm_num)
  have haPos : 0 < a := by
    have hζpos : 0 < ζ := lt_trans hσpos hσζ
    have honeθ : 0 < 1 - θ := sub_pos.mpr hθone
    have hsum : 0 < ζ + σ + (1 - θ) := by positivity
    exact lt_trans hsum hp.ha.1
  obtain ⟨nArith, hArith⟩ := height_base_exp_arithmetic a b₀ θ haPos hp.ha.2.1
    ⟨hθpos, hθone⟩
  let NpairA := max nFail nCount
  let Npair := max NpairA 2
  let Nlogs := max nLogOne nLog
  let Ngrowth := max nRoot nRad
  let Ngeom := max Nlogs Ngrowth
  let Nall := max Npair (max Ngeom nArith)
  refine ⟨Nall, ?_⟩
  intro p hD hH hlam hb₀' hb' hn hdLo hdHi hreg Sites v hv Aux inst πAux Esel
  have hNpair : Npair ≤ p.n := le_trans (Nat.le_max_left Npair _) hn
  have hNgeomArith : max Ngeom nArith ≤ p.n :=
    le_trans (Nat.le_max_right Npair _) hn
  have hNgeom : Ngeom ≤ p.n := le_trans (Nat.le_max_left Ngeom nArith) hNgeomArith
  have hnArith : nArith ≤ p.n := le_trans (Nat.le_max_right Ngeom nArith) hNgeomArith
  have hNlogs : Nlogs ≤ p.n := le_trans (Nat.le_max_left Nlogs Ngrowth) hNgeom
  have hNgrowth : Ngrowth ≤ p.n := le_trans (Nat.le_max_right Nlogs Ngrowth) hNgeom
  have hnLogOne : nLogOne ≤ p.n := le_trans (Nat.le_max_left nLogOne nLog) hNlogs
  have hnLog : nLog ≤ p.n := le_trans (Nat.le_max_right nLogOne nLog) hNlogs
  have hnRoot : nRoot ≤ p.n := le_trans (Nat.le_max_left nRoot nRad) hNgrowth
  have hnRad : nRad ≤ p.n := le_trans (Nat.le_max_right nRoot nRad) hNgrowth
  have hNpairA : NpairA ≤ p.n := le_trans (Nat.le_max_left NpairA 2) hNpair
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_right NpairA 2) hNpair
  have hnFail : nFail ≤ p.n := le_trans (Nat.le_max_left nFail nCount) hNpairA
  have hnCount : nCount ≤ p.n := le_trans (Nat.le_max_right nFail nCount) hNpairA
  have hR0 : (heightBaseRadius p.n : ℝ) ≤ 2 * (Real.log (p.n : ℝ)) ^ 2 :=
    hRad p.n hnRad
  have hlogOne : 1 ≤ Real.log (p.n : ℝ) := hLogOne p.n hnLogOne
  have hlogUpper : Real.log (p.n : ℝ) ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) :=
    hLog p.n hnLog
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  have hlogSq : (Real.log (p.n : ℝ)) ^ 2 ≤ (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hlogNonneg : 0 ≤ Real.log (p.n : ℝ) := by linarith
    have hquarterNonneg : 0 ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hnpos.le _
    have hquarterSq : (p.n : ℝ) ^ ((1 : ℝ) / 4) *
        (p.n : ℝ) ^ ((1 : ℝ) / 4) = (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
      calc
        _ = (p.n : ℝ) ^ (((1 : ℝ) / 4) + ((1 : ℝ) / 4)) :=
          (Real.rpow_add hnpos _ _).symm
        _ = _ := by congr 1 <;> norm_num
    calc
      (Real.log (p.n : ℝ)) ^ 2 = Real.log (p.n : ℝ) * Real.log (p.n : ℝ) := by ring
      _ ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (p.n : ℝ) :=
        mul_le_mul_of_nonneg_right hlogUpper hlogNonneg
      _ ≤ (p.n : ℝ) ^ ((1 : ℝ) / 4) * (p.n : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hlogUpper hquarterNonneg
      _ = (p.n : ℝ) ^ ((1 : ℝ) / 2) := hquarterSq
  have hrootSq : (p.n : ℝ) ^ ((1 : ℝ) / 2) * (p.n : ℝ) ^ ((1 : ℝ) / 2) = p.n := by
    calc
      _ = (p.n : ℝ) ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) := (Real.rpow_add hnpos _ _).symm
      _ = p.n := by norm_num [Real.rpow_one]
  have hrootValue : Croot ≤ (p.n : ℝ) ^ ((1 : ℝ) / 2) := hRoot p.n hnRoot
  have hrootScaled : 2 * (D : ℝ) ≤ c_d * (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hrootScaled' : 2 * (D : ℝ) ≤ (p.n : ℝ) ^ ((1 : ℝ) / 2) * c_d := by
      apply (div_le_iff₀ hp.hd.1).1
      simpa [Croot] using hrootValue
    simpa [mul_comm] using hrootScaled'
  have hradDimension : (D : ℝ) * (heightBaseRadius p.n : ℝ) ≤ (p.d : ℝ) := by
    have hradUpper : (D : ℝ) * (heightBaseRadius p.n : ℝ) ≤
        2 * (D : ℝ) * (p.n : ℝ) ^ ((1 : ℝ) / 2) := by
      calc
        _ ≤ (D : ℝ) * (2 * (Real.log (p.n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hR0 (by positivity)
        _ ≤ (D : ℝ) * (2 * (p.n : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlogSq (by norm_num)) (by positivity)
        _ = 2 * (D : ℝ) * (p.n : ℝ) ^ ((1 : ℝ) / 2) := by ring
    have hradFinal : 2 * (D : ℝ) * (p.n : ℝ) ^ ((1 : ℝ) / 2) ≤ c_d * p.n := by
      calc
        _ ≤ (c_d * (p.n : ℝ) ^ ((1 : ℝ) / 2)) * (p.n : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hrootScaled (Real.rpow_nonneg hnpos.le _)
        _ = c_d * p.n := by
          calc
            _ = c_d * ((p.n : ℝ) ^ ((1 : ℝ) / 2) * (p.n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
            _ = c_d * p.n := by rw [hrootSq]
    exact hradUpper.trans (hradFinal.trans hdLo)
  have hRadiusBase : D * heightBaseRadius p.n ≤ p.d := by
    have hRadiusReal : ((D * heightBaseRadius p.n : ℕ) : ℝ) ≤ (p.d : ℝ) := by
      simpa [Nat.cast_mul] using hradDimension
    exact_mod_cast hRadiusReal
  have hRadius : p.D * heightBaseRadius p.n ≤ p.d := by rw [hD]; exact hRadiusBase
  have hRpos : 0 < heightBaseRadius p.n :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hCount' := hCount Sites (v, 0) (heightBaseRadius p.n)
    hnCount hD hdHi hR0 hRpos rfl hRadius
  have hArith' := hArith p.n hnArith
  have hDpos : 0 < p.D := by rw [hD]; exact hp.hD
  have hFail' := hFail p hD hH hlam hb₀' hb' hnFail hdLo hdHi hreg
    Sites (v, 0) (heightBaseRadius p.n) ((1 : ℝ) / 2) hRpos (by norm_num)
      (Aux := Aux) πAux Esel
  have hb₀ltJ : b₀ < J₀ := by linarith [hp.hJ, hb₀b, hbone]
  have hlamLower : (p.n : ℝ) ^ b₀ ≤ p.lam := by
    rw [hlam]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hb₀ltJ.le
  have hbadTail₁ : Real.exp (-p.lam / 8) ≤ Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hlamLower]
  have hbadTail₂ : Real.exp (-p.lam / 3) ≤ Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
    apply Real.exp_le_exp.mpr
    have hfirst : -p.lam / 3 ≤ -((p.n : ℝ) ^ b₀) / 3 := by
      exact div_le_div_of_nonneg_right (neg_le_neg hlamLower) (by norm_num : (0 : ℝ) ≤ 3)
    have hsecond : -((p.n : ℝ) ^ b₀) / 3 ≤ -((p.n : ℝ) ^ b₀) / 8 := by
      have hx : 0 ≤ (p.n : ℝ) ^ b₀ := Real.rpow_nonneg hnpos.le _
      nlinarith [hx]
    exact hfirst.trans hsecond
  have hbadTail₃ : Real.exp (-((p.n : ℝ) ^ b₀) / 6) ≤
      Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg hnpos.le b₀]
  have hδ : Real.exp (-p.lam / 8) + Real.exp (-p.lam / 3) +
      2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6) ≤
      4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
    linarith [hbadTail₁, hbadTail₂, hbadTail₃]
  calc
    _ ≤ ((hdScaleBallSiteLevels Sites (v, 0) (heightBaseRadius p.n)).card : ℝ) *
        (Real.exp (-p.lam / 8) + Real.exp (-p.lam / 3) +
          2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6)) := hFail'
    _ ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
        (4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by
      calc
        _ ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
            (Real.exp (-p.lam / 8) + Real.exp (-p.lam / 3) +
              2 * Real.exp (-((p.n : ℝ) ^ b₀) / 6)) :=
          mul_le_mul_of_nonneg_right hCount' (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hδ (by positivity)
    _ = 4 * Real.exp ((p.n : ℝ) ^ (b₀ / 2) - (p.n : ℝ) ^ b₀ / 8) := by
      calc
        _ = 4 * (Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
              Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) := hArith'

/-- A scale-level site is bad at relaxed eligibility and crowd thresholds. -/
def hdScaleLegalAt {p : HDParams} (P : p.Loc → Bool) (E : p.EligMap)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (s : ℝ) : Prop :=
  (∀ ℓ ∈ E v j, P ℓ = true ∧ ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r) ∧
    s * p.lam ≤ ((E v j).card : ℝ)

def hdScaleLegal {p : HDParams} (P : p.Loc → Bool) (E : p.EligMap)
    (Sites : p.Sites) (s : ℝ) : Prop :=
  ∀ v ∈ Sites, ∀ j, hdScaleLegalAt P E v j s

def hdScaleThresholdBad {p : HDParams} (P A : p.Loc → Bool) (E : p.EligMap)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (s t : ℝ) : Prop :=
  (∀ ℓ ∈ E v j, A ℓ = false) ∨
    t * (p.n : ℝ) ^ p.b <
      ((Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D)).card : ℝ)

def hdScaleThresholdBadN {p : HDParams} (P A : p.Loc → Bool) (E : p.EligMap)
    (v : CubeVertex p.d) (j : ℕ) (s t : ℝ) : Prop :=
  ∃ hj : j < p.H + 1, hdScaleThresholdBad P A E v ⟨j, hj⟩ s t

/-- A fixed relaxed-bad site has an exponentially small activation probability once
its eligibility and crowd means satisfy the supplied threshold bounds. -/
theorem hdScale_bad_activation_bound {p : HDParams} (P : p.Loc → Bool)
    (E : p.EligMap) (v : CubeVertex p.d) (j : Fin (p.H + 1)) (s t : ℝ)
    (hsize : s * p.lam ≤ ((E v j).card : ℝ))
    (hmeanUpper : 2 * (heightCrowdIDs P v j).card *
      ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ t * (p.n : ℝ) ^ p.b)
    (hmeanLower : (p.n : ℝ) ^ p.b₀ / 2 ≤
      (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam))
    (hq0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hq1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1) :
    p.actLaw.pr (fun A => hdScaleThresholdBad P A E v j s t) ≤
      Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) +
        Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
  let T := heightCrowdIDs P v j
  let q : ℝ := (p.n : ℝ) ^ p.b₀ / p.lam
  have hlamNe : p.lam ≠ 0 := by
    intro hzero
    rw [hzero] at hq0
    norm_num at hq0
  have hlamq : p.lam * q = (p.n : ℝ) ^ p.b₀ := by
    dsimp [q]
    field_simp [hlamNe]
  have hHoleMean : s * (p.n : ℝ) ^ p.b₀ ≤ (E v j).card * q := by
    calc
      s * (p.n : ℝ) ^ p.b₀ = s * (p.lam * q) := by rw [hlamq]
      _ = (s * p.lam) * q := by ring
      _ ≤ (E v j).card * q := mul_le_mul_of_nonneg_right hsize hq0.le
  have hHoleExp : Real.exp (-((E v j).card * q) / 2) ≤
      Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hHoleMean]
  have hCrowdExp : Real.exp (-(T.card * q) / 3) ≤
      Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hmeanLower]
  have hsubset : ∀ A : p.Loc → Bool, hdScaleThresholdBad P A E v j s t →
      (∀ ℓ ∈ E v j, A ℓ = false) ∨
        t * (p.n : ℝ) ^ p.b <
          ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0 := by
    intro A hbad
    rcases hbad with hhole | hcrowd
    · exact Or.inl hhole
    · right
      rw [← height_crowd_active_count_eq P A v j] at hcrowd
      exact hcrowd
  calc
    p.actLaw.pr (fun A => hdScaleThresholdBad P A E v j s t) ≤
        p.actLaw.pr (fun A => (∀ ℓ ∈ E v j, A ℓ = false) ∨
          t * (p.n : ℝ) ^ p.b <
            ∑ ℓ, if ℓ ∈ T ∧ A ℓ = true then (1 : ℝ) else 0) :=
      finprob_pr_mono _ _ _ hsubset
    _ ≤ Real.exp (-((E v j).card * q) / 2) + Real.exp (-(T.card * q) / 3) :=
      activation_hole_or_crowd (E v j) T (t * (p.n : ℝ) ^ p.b)
        (by simpa [T, q] using hmeanUpper) hq0 hq1
    _ ≤ Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) +
        Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := add_le_add hHoleExp hCrowdExp

/-- Average the relaxed one-site activation bound over positions and auxiliary data.
The eligibility rule may depend on both, but not on the later activation draw. -/
theorem hdScale_bad_legal_position_average {p : HDParams} {Aux : Type*} [Fintype Aux]
    (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites) (j : Fin (p.H + 1))
    (s t : ℝ) (htLower : 11 / 20 ≤ t) (htUpper : t ≤ 3 / 4)
    (hLam : 0 < p.lam)
    (hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam)
    (hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (hqP0 : 0 < p.lam / (p.V : ℝ)) (hqP1 : p.lam / (p.V : ℝ) ≤ 1)
    (hregionLower : (p.n : ℝ) ^ p.b₀ ≤
      (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
        ((p.n : ℝ) ^ p.b₀ / p.lam))
    (hregionUpper : 4 * (heightCrowdRegion v j).card *
      (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
        hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j s t) ≤
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 8) +
      Real.exp (-((heightCrowdRegion v j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 210) +
      Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) +
      Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
  classical
  let T := heightCrowdRegion v j
  let μ : ℝ := (T.card : ℝ) * (p.lam / (p.V : ℝ))
  let posCount : (p.Loc → Bool) → ℝ := fun P =>
    ∑ ℓ, if ℓ ∈ T ∧ P ℓ = true then (1 : ℝ) else 0
  let posBad : (p.Loc → Bool) → Prop := fun P =>
    posCount P ≤ μ / 2 ∨ (11 / 10 : ℝ) * μ < posCount P
  let outer : FinProb ((p.Loc → Bool) × Aux) := p.posLaw.prod πAux
  let badSite : ((p.Loc → Bool) × Aux) → (p.Loc → Bool) → Prop := fun z A =>
    hdScaleLegal z.1 (Esel z.1 z.2) Sites s ∧
      hdScaleThresholdBad z.1 A (Esel z.1 z.2) v j s t
  let δ : ℝ := Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) +
    Real.exp (-((p.n : ℝ) ^ p.b₀) / 6)
  have hposTails := position_count_tails T hqP0 hqP1
  have hposUpper := position_count_upper_eleven_tenths T hqP0 hqP1
  have hposBad : p.posLaw.pr posBad ≤
      Real.exp (-μ / 8) + Real.exp (-μ / 210) := by
    calc
      p.posLaw.pr posBad ≤
          p.posLaw.pr (fun P => posCount P ≤ μ / 2) +
            p.posLaw.pr (fun P => (11 / 10 : ℝ) * μ < posCount P) := finprob_pr_or_le _ _ _
      _ ≤ Real.exp (-μ / 8) + Real.exp (-μ / 210) := by
        apply add_le_add
        · simpa [posCount, μ, T] using hposTails.1
        · simpa [posCount, μ, T, mul_assoc] using hposUpper
  have houterBad : outer.pr (fun z => posBad z.1) = p.posLaw.pr posBad := by
    simpa [outer] using finprob_prod_pr_left p.posLaw πAux posBad
  have hsections : ∀ z, ¬ posBad z.1 → p.actLaw.pr (badSite z) ≤ δ := by
    intro z hz
    let P := z.1
    let E := Esel z.1 z.2
    have hposLow : μ / 2 < (heightCrowdIDs P v j).card := by
      have hcount := heightCrowdIDs_card_eq_position_count P v j
      have hnot : ¬ posCount P ≤ μ / 2 := by
        intro h
        exact hz (Or.inl (by simpa [posCount] using h))
      have hlt : μ / 2 < posCount P := lt_of_not_ge hnot
      rw [hcount]
      simpa [posCount, μ, T] using hlt
    have hposHigh : (heightCrowdIDs P v j).card ≤ (11 / 10 : ℝ) * μ := by
      have hcount := heightCrowdIDs_card_eq_position_count P v j
      have hnot : ¬ (11 / 10 : ℝ) * μ < posCount P := by
        intro h
        exact hz (Or.inr (by simpa [posCount] using h))
      have hle : posCount P ≤ (11 / 10 : ℝ) * μ := le_of_not_gt hnot
      rw [hcount]
      simpa [posCount, μ, T] using hle
    have hmeanLower : (p.n : ℝ) ^ p.b₀ / 2 ≤
        (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
      have hprod : (μ / 2) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
          (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) :=
        mul_le_mul_of_nonneg_right hposLow.le hqA0.le
      dsimp [μ, T] at hprod
      have hnorm : (p.n : ℝ) ^ p.b₀ ≤
          (heightCrowdRegion v j).card * (p.lam / (p.V : ℝ)) *
            ((p.n : ℝ) ^ p.b₀ / p.lam) := hregionLower
      nlinarith
    have hmeanUpper : 2 * (heightCrowdIDs P v j).card *
        ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ t * (p.n : ℝ) ^ p.b := by
      have hprod : (heightCrowdIDs P v j).card *
          ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
          ((11 / 10 : ℝ) * μ) * ((p.n : ℝ) ^ p.b₀ / p.lam) :=
        mul_le_mul_of_nonneg_right hposHigh hqA0.le
      dsimp [μ, T] at hprod
      have hnorm : 4 * (heightCrowdRegion v j).card *
          (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
            (p.n : ℝ) ^ p.b := hregionUpper
      have hfirst : 2 * (heightCrowdIDs P v j).card *
          ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (11 / 20 : ℝ) * (p.n : ℝ) ^ p.b := by
        nlinarith
      exact hfirst.trans (mul_le_mul_of_nonneg_right htLower
        (Real.rpow_nonneg (by positivity) _))
    by_cases hlegal : hdScaleLegal z.1 E Sites s
    · have hAt : hdScaleLegalAt z.1 E v j s := hlegal v hv j
      have hlocal := hdScale_bad_activation_bound z.1 E v j s t hAt.2
        hmeanUpper hmeanLower hqA0 hqA1
      calc
        p.actLaw.pr (badSite z) ≤ p.actLaw.pr
            (fun A => hdScaleThresholdBad z.1 A E v j s t) := by
          apply finprob_pr_mono
          intro A hA
          exact hA.2
        _ ≤ δ := by simpa [δ] using hlocal
    · have hzero : p.actLaw.pr (badSite z) = 0 := by
        simp [badSite, E, hlegal, FinProb.pr]
      rw [hzero]
      positivity
  have hprod := finprob_prod_pr_le_bad_or_small outer p.actLaw
    (fun z => posBad z.1) badSite δ (by positivity) hsections
  calc
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
          hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j s t)
        ≤ outer.pr (fun z => posBad z.1) + δ := by
          simpa [outer, badSite] using hprod
    _ = p.posLaw.pr posBad + δ := by rw [houterBad]
    _ ≤ Real.exp (-μ / 8) + Real.exp (-μ / 210) + δ := by linarith [hposBad]
    _ = _ := by simp [δ, μ, T, add_assoc]

theorem hdScale_bad_finite_union_bound {p : HDParams} {Aux : Type*} [Fintype Aux]
    (πAux : FinProb Aux) (Esel : (p.Loc → Bool) → Aux → p.EligMap)
    (Sites : p.Sites) (T : Finset (CubeVertex p.d × Fin (p.H + 1)))
    (s t δ : ℝ) (hSites : ∀ x ∈ T, x.1 ∈ Sites)
    (hLocal : ∀ v ∈ Sites, ∀ j : Fin (p.H + 1),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
          hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v j s t) ≤ δ) :
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
      hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
        ∃ x ∈ T, hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 s t) ≤
      (T.card : ℝ) * δ := by
  classical
  let law := (p.posLaw.prod πAux).prod p.actLaw
  let F : (CubeVertex p.d × Fin (p.H + 1)) →
      (((p.Loc → Bool) × Aux) × (p.Loc → Bool)) → Prop := fun x ω =>
    hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
      hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 s t
  have hEq : (fun ω => hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
      ∃ x ∈ T, hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 s t) =
      (fun ω => ∃ x ∈ T, F x ω) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨hlegal, x, hx, hbad⟩
      exact ⟨x, hx, hlegal, hbad⟩
    · rintro ⟨x, hx, hlegal, hbad⟩
      exact ⟨hlegal, x, hx, hbad⟩
  rw [hEq]
  calc
    law.pr (fun ω => ∃ x ∈ T, F x ω) ≤ ∑ x ∈ T, law.pr (F x) :=
      finprob_pr_finset_exists_le law T F
    _ ≤ ∑ x ∈ T, δ := by
      apply Finset.sum_le_sum
      intro x hx
      exact hLocal x.1 (hSites x hx) x.2
    _ = (T.card : ℝ) * δ := by simp

/-- A stopped walk using any supplied relaxed bad-site predicate. -/
inductive HDThresholdWalk {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (origin : HDState p) (R : ℕ) :
    HDState p → HDState p → Type
  | stop {s} (hboundary : R ≤ hdScaleDistance p.D origin s) :
      HDThresholdWalk Sites bad origin R s s
  | up {v j finish} (hinside : hdScaleDistance p.D origin (v, j) < R)
      (hv : v ∈ Sites) (hj : j < p.H) (hbad : bad v j)
      (tail : HDThresholdWalk Sites bad origin R (v, j + 1) finish) :
      HDThresholdWalk Sites bad origin R (v, j) finish
  | down {v v' j finish} (hinside : hdScaleDistance p.D origin (v, j + 1) < R)
      (hv' : v' ∈ Sites) (hj : j < p.H) (hstep : _root_.hammingDist v v' ≤ p.D)
      (tail : HDThresholdWalk Sites bad origin R (v', j) finish) :
      HDThresholdWalk Sites bad origin R (v, j + 1) finish

/- The path-prefix relation certifies that the child walk stops at the first
exit from its radius, with a parent suffix left over. -/
private inductive HDThresholdCutFirstExit {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p) (parentRadius : ℕ)
    (childOrigin : HDState p) (childRadius : ℕ) :
    {start finish : HDState p} →
    HDThresholdWalk Sites bad parentOrigin parentRadius start finish →
    (Σ middle : HDState p,
      HDThresholdWalk Sites bad childOrigin childRadius start middle ×
        HDThresholdWalk Sites bad parentOrigin parentRadius middle finish) → Prop
  | upExit {v j finish} (hparent : hdScaleDistance p.D parentOrigin (v, j) < parentRadius)
      (hv : v ∈ Sites) (hj : j < p.H) (hbad : bad v j)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v, j + 1) finish)
      (hinside : hdScaleDistance p.D childOrigin (v, j) < childRadius)
      (hboundary : childRadius ≤ hdScaleDistance p.D childOrigin (v, j + 1)) :
      HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        (HDThresholdWalk.up hparent hv hj hbad tail)
        ⟨(v, j + 1),
          (HDThresholdWalk.up hinside hv hj hbad (HDThresholdWalk.stop hboundary), tail)⟩
  | upContinue {v j finish middle} {childTail : HDThresholdWalk Sites bad childOrigin childRadius
      (v, j + 1) middle} {parentTail : HDThresholdWalk Sites bad parentOrigin parentRadius
      middle finish}
      (hparent : hdScaleDistance p.D parentOrigin (v, j) < parentRadius)
      (hv : v ∈ Sites) (hj : j < p.H) (hbad : bad v j)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v, j + 1) finish)
      (hinside : hdScaleDistance p.D childOrigin (v, j) < childRadius)
      (hnext : hdScaleDistance p.D childOrigin (v, j + 1) < childRadius)
      (htail : HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        tail ⟨middle, (childTail, parentTail)⟩) :
      HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        (HDThresholdWalk.up hparent hv hj hbad tail)
        ⟨middle, (HDThresholdWalk.up hinside hv hj hbad childTail, parentTail)⟩
  | downExit {v v' j finish} (hparent : hdScaleDistance p.D parentOrigin (v, j + 1) < parentRadius)
      (hv' : v' ∈ Sites) (hj : j < p.H) (hstep : _root_.hammingDist v v' ≤ p.D)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v', j) finish)
      (hinside : hdScaleDistance p.D childOrigin (v, j + 1) < childRadius)
      (hboundary : childRadius ≤ hdScaleDistance p.D childOrigin (v', j)) :
      HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        (HDThresholdWalk.down hparent hv' hj hstep tail)
        ⟨(v', j),
          (HDThresholdWalk.down hinside hv' hj hstep (HDThresholdWalk.stop hboundary), tail)⟩
  | downContinue {v v' j finish middle} {childTail : HDThresholdWalk Sites bad childOrigin childRadius
      (v', j) middle} {parentTail : HDThresholdWalk Sites bad parentOrigin parentRadius
      middle finish}
      (hparent : hdScaleDistance p.D parentOrigin (v, j + 1) < parentRadius)
      (hv' : v' ∈ Sites) (hj : j < p.H) (hstep : _root_.hammingDist v v' ≤ p.D)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v', j) finish)
      (hinside : hdScaleDistance p.D childOrigin (v, j + 1) < childRadius)
      (hnext : hdScaleDistance p.D childOrigin (v', j) < childRadius)
      (htail : HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        tail ⟨middle, (childTail, parentTail)⟩) :
      HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
        (HDThresholdWalk.down hparent hv' hj hstep tail)
        ⟨middle, (HDThresholdWalk.down hinside hv' hj hstep childTail, parentTail)⟩

private theorem hdScaleDistance_self {p : HDParams} (s : HDState p) (hD : 0 < p.D) :
    hdScaleDistance p.D s s = 0 := by
  unfold hdScaleDistance
  have hD1 : 1 ≤ p.D := by omega
  rw [Nat.dist_self]
  have hham : _root_.hammingDist s.1 s.1 = 0 := by simp [_root_.hammingDist]
  rw [hham, max_eq_right hD1]
  have hdiv : (p.D - 1) / p.D = 0 := Nat.div_eq_of_lt (by omega)
  simp [hdiv]

private theorem hdScaleDistance_triangle {p : HDParams} (hD : 0 < p.D)
    (x y z : HDState p) :
    hdScaleDistance p.D x z ≤ hdScaleDistance p.D x y + hdScaleDistance p.D y z := by
  have hD1 : 1 ≤ p.D := by omega
  let qxy := (_root_.hammingDist x.1 y.1 + p.D - 1) / p.D
  let qyz := (_root_.hammingDist y.1 z.1 + p.D - 1) / p.D
  let qxz := (_root_.hammingDist x.1 z.1 + p.D - 1) / p.D
  have hxyNum : _root_.hammingDist x.1 y.1 + p.D - 1 < p.D * (qxy + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hD).1 (Nat.lt_succ_self qxy)
    simpa [qxy, Nat.mul_comm] using h
  have hyzNum : _root_.hammingDist y.1 z.1 + p.D - 1 < p.D * (qyz + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hD).1 (Nat.lt_succ_self qyz)
    simpa [qyz, Nat.mul_comm] using h
  have hxy : _root_.hammingDist x.1 y.1 ≤ p.D * qxy := by
    have h : _root_.hammingDist x.1 y.1 + p.D - 1 < p.D * qxy + p.D := by
      simpa [Nat.mul_succ] using hxyNum
    omega
  have hyz : _root_.hammingDist y.1 z.1 ≤ p.D * qyz := by
    have h : _root_.hammingDist y.1 z.1 + p.D - 1 < p.D * qyz + p.D := by
      simpa [Nat.mul_succ] using hyzNum
    omega
  have hham : _root_.hammingDist x.1 z.1 ≤ p.D * qxy + p.D * qyz := by
    exact (_root_.hammingDist_triangle x.1 y.1 z.1).trans
      (Nat.add_le_add hxy hyz)
  have hprod : p.D * (qxy + qyz + 1) = p.D * qxy + p.D * qyz + p.D := by ring
  have hnum : _root_.hammingDist x.1 z.1 + p.D - 1 <
      p.D * (qxy + qyz + 1) := by
    rw [hprod]
    omega
  have hquot : qxz ≤ qxy + qyz := by
    have hlt : (_root_.hammingDist x.1 z.1 + p.D - 1) / p.D < qxy + qyz + 1 := by
      apply (Nat.div_lt_iff_lt_mul hD).2
      simpa [Nat.mul_comm] using hnum
    simpa [qxz] using (Nat.lt_succ_iff.mp hlt)
  have hlevel : Nat.dist x.2 z.2 ≤ Nat.dist x.2 y.2 + Nat.dist y.2 z.2 := by
    unfold Nat.dist
    omega
  have hform (a b : HDState p) : hdScaleDistance p.D a b =
      max (Nat.dist a.2 b.2) ((_root_.hammingDist a.1 b.1 + p.D - 1) / p.D) := by
    unfold hdScaleDistance
    rw [max_eq_right hD1]
  rw [hform x z, hform x y, hform y z]
  apply Nat.max_le.mpr
  constructor
  · exact hlevel.trans (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  · exact hquot.trans (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _))

private theorem hdScaleDistance_upStep_le_one {p : HDParams} (hD : 0 < p.D)
    (v : CubeVertex p.d) (j : ℕ) :
    hdScaleDistance p.D (v, j) (v, j + 1) ≤ 1 := by
  have hD1 : 1 ≤ p.D := by omega
  have hham : _root_.hammingDist v v = 0 := by simp [_root_.hammingDist]
  have hdiv : (p.D - 1) / p.D = 0 := Nat.div_eq_of_lt (by omega)
  have hlevel : Nat.dist j (j + 1) = 1 := by
    rw [Nat.dist_eq_sub_of_le (Nat.le_succ j)]
    omega
  rw [show hdScaleDistance p.D (v, j) (v, j + 1) =
      max (Nat.dist j (j + 1)) ((_root_.hammingDist v v + p.D - 1) / p.D) by
        simp [hdScaleDistance, max_eq_right hD1]]
  simp [hlevel, hham, hdiv]

private theorem hdScaleDistance_downStep_le_one {p : HDParams} (hD : 0 < p.D)
    (v v' : CubeVertex p.d) (j : ℕ)
    (hstep : _root_.hammingDist v v' ≤ p.D) :
    hdScaleDistance p.D (v, j + 1) (v', j) ≤ 1 := by
  have hD1 : 1 ≤ p.D := by omega
  have hlevel : Nat.dist (j + 1) j = 1 := by
    rw [Nat.dist_eq_sub_of_le_right (Nat.le_succ j)]
    omega
  have hquot : (_root_.hammingDist v v' + p.D - 1) / p.D ≤ 1 := by
    have hnum : _root_.hammingDist v v' + p.D - 1 < 2 * p.D := by omega
    have hlt : (_root_.hammingDist v v' + p.D - 1) / p.D < 2 := by
      apply (Nat.div_lt_iff_lt_mul hD).2
      simpa [Nat.mul_comm] using hnum
    omega
  have hform : hdScaleDistance p.D (v, j + 1) (v', j) =
      max (Nat.dist (j + 1) j) ((_root_.hammingDist v v' + p.D - 1) / p.D) := by
    unfold hdScaleDistance
    rw [max_eq_right hD1]
  rw [hform]
  exact Nat.max_le.mpr ⟨hlevel.le, hquot⟩

private theorem hdScaleLevelRise_le_distance {p : HDParams} (s t : HDState p) :
    (t.2 : ℤ) - s.2 ≤ hdScaleDistance p.D s t := by
  have hdist : (t.2 : ℤ) - s.2 ≤ (Nat.dist s.2 t.2 : ℤ) := by
    by_cases hst : s.2 ≤ t.2
    · rw [Nat.dist_eq_sub_of_le hst]
      have hcast : ((t.2 - s.2 : ℕ) : ℤ) = (t.2 : ℤ) - s.2 := by
        exact Nat.cast_sub hst
      rw [hcast]
    · have hts : t.2 ≤ s.2 := Nat.le_of_not_ge hst
      rw [Nat.dist_eq_sub_of_le_right hts]
      have hcast : ((s.2 - t.2 : ℕ) : ℤ) = (s.2 : ℤ) - t.2 := by
        exact Nat.cast_sub hts
      rw [hcast]
      omega
  have hlevel : Nat.dist s.2 t.2 ≤ hdScaleDistance p.D s t := by
    unfold hdScaleDistance
    exact Nat.le_max_left _ _
  exact hdist.trans (by exact_mod_cast hlevel)

private theorem hdThresholdCutFirstExit_finish_le_radius {p : HDParams}
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin childOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {result : Σ middle : HDState p,
      HDThresholdWalk Sites bad childOrigin childRadius start middle ×
        HDThresholdWalk Sites bad parentOrigin parentRadius middle finish}
    (hD : 0 < p.D)
    (hcut : HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
      walk result) : hdScaleDistance p.D childOrigin result.1 ≤ childRadius := by
  induction hcut with
  | @upExit v j finish hparent hv hj hbad tail hinside hboundary =>
      calc
        hdScaleDistance p.D childOrigin (v, j + 1) ≤
            hdScaleDistance p.D childOrigin (v, j) + hdScaleDistance p.D (v, j) (v, j + 1) :=
              hdScaleDistance_triangle hD childOrigin (v, j) (v, j + 1)
        _ ≤ childRadius := by
          have hstep := hdScaleDistance_upStep_le_one hD v j
          omega
  | upContinue hparent hv hj hbad tail hinside hnext htail ih => exact ih
  | @downExit v v' j finish hparent hv' hj hstep tail hinside hboundary =>
      calc
        hdScaleDistance p.D childOrigin (v', j) ≤
            hdScaleDistance p.D childOrigin (v, j + 1) +
              hdScaleDistance p.D (v, j + 1) (v', j) :=
                hdScaleDistance_triangle hD childOrigin (v, j + 1) (v', j)
        _ ≤ childRadius := by
          have hstep' := hdScaleDistance_downStep_le_one hD v v' j hstep
          omega
  | downContinue hparent hv' hj hstep tail hinside hnext htail ih => exact ih

/-- A parent-walk suffix that never leaves one child ball. -/
private inductive HDThresholdWalkInside {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p) (parentRadius : ℕ)
    (center : HDState p) (childRadius : ℕ) :
    {start finish : HDState p} →
    HDThresholdWalk Sites bad parentOrigin parentRadius start finish → Prop
  | stop {s} (hparent : parentRadius ≤ hdScaleDistance p.D parentOrigin s)
      (hinside : hdScaleDistance p.D center s < childRadius) :
      HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius
        (HDThresholdWalk.stop hparent)
  | up {v j finish} (hparent : hdScaleDistance p.D parentOrigin (v, j) < parentRadius)
      (hv : v ∈ Sites) (hj : j < p.H) (hbad : bad v j)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v, j + 1) finish)
      (hinside : hdScaleDistance p.D center (v, j) < childRadius)
      (hnext : hdScaleDistance p.D center (v, j + 1) < childRadius)
      (htail : HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius tail) :
      HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius
        (HDThresholdWalk.up hparent hv hj hbad tail)
  | down {v v' j finish} (hparent : hdScaleDistance p.D parentOrigin (v, j + 1) < parentRadius)
      (hv' : v' ∈ Sites) (hj : j < p.H) (hstep : _root_.hammingDist v v' ≤ p.D)
      (tail : HDThresholdWalk Sites bad parentOrigin parentRadius (v', j) finish)
      (hinside : hdScaleDistance p.D center (v, j + 1) < childRadius)
      (hnext : hdScaleDistance p.D center (v', j) < childRadius)
      (htail : HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius tail) :
      HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius
        (HDThresholdWalk.down hparent hv' hj hstep tail)

private theorem hdThresholdWalkInside_finish_inside {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p) (parentRadius : ℕ)
    (center : HDState p) (childRadius : ℕ) {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    (hinside : HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius walk) :
    hdScaleDistance p.D center finish < childRadius := by
  induction hinside with
  | stop _ hfinish => exact hfinish
  | up _ _ _ _ _ _ _ _ ih => exact ih
  | down _ _ _ _ _ _ _ _ ih => exact ih

/-- Every parent suffix either reaches the child-radius boundary or stays inside
the child ball all the way to its end. -/
private theorem hdThresholdWalk_cut_or_inside {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p) (parentRadius : ℕ)
    (center : HDState p) (childRadius : ℕ) {start finish : HDState p}
    (walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish)
    (hinside : hdScaleDistance p.D center start < childRadius) :
    (∃ result : Σ middle : HDState p,
      HDThresholdWalk Sites bad center childRadius start middle ×
        HDThresholdWalk Sites bad parentOrigin parentRadius middle finish,
      HDThresholdCutFirstExit Sites bad parentOrigin parentRadius center childRadius walk result) ∨
    HDThresholdWalkInside Sites bad parentOrigin parentRadius center childRadius walk := by
  induction walk with
  | stop hparent => exact Or.inr (HDThresholdWalkInside.stop hparent hinside)
  | @up v j finish hparent hv hj hbad tail ih =>
      by_cases hnext : hdScaleDistance p.D center (v, j + 1) < childRadius
      · rcases ih hnext with hcut | hin
        · rcases hcut with ⟨result, hcert⟩
          rcases result with ⟨middle, childTail, parentTail⟩
          exact Or.inl ⟨⟨middle, (HDThresholdWalk.up hinside hv hj hbad childTail, parentTail)⟩,
            HDThresholdCutFirstExit.upContinue hparent hv hj hbad tail hinside hnext hcert⟩
        · exact Or.inr (HDThresholdWalkInside.up hparent hv hj hbad tail hinside hnext hin)
      · exact Or.inl ⟨⟨(v, j + 1),
          (HDThresholdWalk.up hinside hv hj hbad (HDThresholdWalk.stop (Nat.le_of_not_gt hnext)), tail)⟩,
          HDThresholdCutFirstExit.upExit hparent hv hj hbad tail hinside (Nat.le_of_not_gt hnext)⟩
  | @down v v' j finish hparent hv' hj hstep tail ih =>
      by_cases hnext : hdScaleDistance p.D center (v', j) < childRadius
      · rcases ih hnext with hcut | hin
        · rcases hcut with ⟨result, hcert⟩
          rcases result with ⟨middle, childTail, parentTail⟩
          exact Or.inl ⟨⟨middle, (HDThresholdWalk.down hinside hv' hj hstep childTail, parentTail)⟩,
            HDThresholdCutFirstExit.downContinue hparent hv' hj hstep tail hinside hnext hcert⟩
        · exact Or.inr (HDThresholdWalkInside.down hparent hv' hj hstep tail hinside hnext hin)
      · exact Or.inl ⟨⟨(v', j),
          (HDThresholdWalk.down hinside hv' hj hstep (HDThresholdWalk.stop (Nat.le_of_not_gt hnext)), tail)⟩,
          HDThresholdCutFirstExit.downExit hparent hv' hj hstep tail hinside (Nat.le_of_not_gt hnext)⟩

private def hdThresholdWalkList {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) : List (HDState p) :=
  match hwalk with
  | .stop _ => [start]
  | .up _ _ _ _ tail => start :: hdThresholdWalkList tail
  | .down _ _ _ _ tail => start :: hdThresholdWalkList tail

private theorem hdThresholdWalkList_nonempty {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p} (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    hdThresholdWalkList hwalk ≠ [] := by
  cases hwalk <;> simp [hdThresholdWalkList]

private theorem hdThresholdWalkList_head {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p} (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    (hdThresholdWalkList hwalk).head? = some start := by
  cases hwalk <;> simp [hdThresholdWalkList]

private theorem hdThresholdWalkList_last {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p} (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    (hdThresholdWalkList hwalk).getLast? = some finish := by
  induction hwalk with
  | stop _ => simp [hdThresholdWalkList]
  | @up v j finish _ _ _ _ tail ih =>
      have hne := hdThresholdWalkList_nonempty tail
      change ((v, j) :: hdThresholdWalkList tail).getLast? = some finish
      rw [List.getLast?_cons_of_ne_nil hne]
      exact ih
  | @down v v' j finish _ _ _ _ tail ih =>
      have hne := hdThresholdWalkList_nonempty tail
      change ((v, j + 1) :: hdThresholdWalkList tail).getLast? = some finish
      rw [List.getLast?_cons_of_ne_nil hne]
      exact ih

private noncomputable def hdThresholdWalk_upCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) : ℕ :=
  match hwalk with
  | .stop _ => 0
  | .up _ _ _ _ tail => hdThresholdWalk_upCount tail + 1
  | .down _ _ _ _ tail => hdThresholdWalk_upCount tail

private noncomputable def hdThresholdWalk_downCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) : ℕ :=
  match hwalk with
  | .stop _ => 0
  | .up _ _ _ _ tail => hdThresholdWalk_downCount tail
  | .down _ _ _ _ tail => hdThresholdWalk_downCount tail + 1

private noncomputable def hdThresholdWalk_length {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) : ℕ :=
  hdThresholdWalk_upCount hwalk + hdThresholdWalk_downCount hwalk

private theorem hdThresholdCutFirstExit_remainder_shorter {p : HDParams}
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius : ℕ}
    {childOrigin : HDState p} {childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {result : Σ middle : HDState p,
      HDThresholdWalk Sites bad childOrigin childRadius start middle ×
        HDThresholdWalk Sites bad parentOrigin parentRadius middle finish}
    (hcut : HDThresholdCutFirstExit Sites bad parentOrigin parentRadius childOrigin childRadius
      walk result) : hdThresholdWalk_length result.2.2 < hdThresholdWalk_length walk := by
  induction hcut with
  | upExit hparent hv hj hbad tail hinside hboundary =>
      simp [hdThresholdWalk_length, hdThresholdWalk_upCount, hdThresholdWalk_downCount]
  | upContinue hparent hv hj hbad tail hinside hnext htail ih =>
      simp [hdThresholdWalk_length, hdThresholdWalk_upCount, hdThresholdWalk_downCount] at ih ⊢
      omega
  | downExit hparent hv' hj hstep tail hinside hboundary =>
      simp [hdThresholdWalk_length, hdThresholdWalk_upCount, hdThresholdWalk_downCount]
  | downContinue hparent hv' hj hstep tail hinside hnext htail ih =>
      simp [hdThresholdWalk_length, hdThresholdWalk_upCount, hdThresholdWalk_downCount] at ih ⊢
      omega

private abbrev HDChunk (p : HDParams) (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (childRadius : ℕ) :=
  Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
    HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish

private inductive HDThresholdChunking {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p)
    (parentRadius childRadius : ℕ) :
    {start finish : HDState p} →
    HDThresholdWalk Sites bad parentOrigin parentRadius start finish →
    List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) →
    (Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish) → Prop
  | done {start finish} {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
      (hinside : HDThresholdWalkInside Sites bad parentOrigin parentRadius start childRadius walk) :
      HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk [] ⟨start, walk⟩
  | more {start finish middle chunks suffixStart}
      {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
      {childWalk : HDThresholdWalk Sites bad start childRadius start middle}
      {rest : HDThresholdWalk Sites bad parentOrigin parentRadius middle finish}
      {suffix : HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
      (hcut : HDThresholdCutFirstExit Sites bad parentOrigin parentRadius start childRadius
        walk ⟨middle, (childWalk, rest)⟩)
      (htail : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius rest chunks
        ⟨suffixStart, suffix⟩) :
      HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
        (⟨start, ⟨middle, childWalk⟩⟩ :: chunks) ⟨suffixStart, suffix⟩

private def hdChunkListChain {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ} :
    List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest => first.2.1 = second.1 ∧ hdChunkListChain (second :: rest)

private theorem hdThresholdChunking_headStart {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {parentOrigin : HDState p}
    {parentRadius childRadius : ℕ} {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) : ∀ c, chunks.head? = some c → c.1 = start := by
  induction hchunk with
  | done _ => simp
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      intro c hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      cases hc
      rfl

private theorem hdThresholdChunking_chain {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {parentOrigin : HDState p}
    {parentRadius childRadius : ℕ} {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) : hdChunkListChain chunks := by
  induction hchunk with
  | done _ => simp [hdChunkListChain]
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      cases chunks with
      | nil => simp [hdChunkListChain]
      | cons first restChunks =>
          have hfirst := hdThresholdChunking_headStart htail first (by simp)
          simp [hdChunkListChain, hfirst, ih]

private theorem hdThresholdChunking_lastFinish_eq {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {parentOrigin : HDState p}
    {parentRadius childRadius : ℕ} {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (HDChunk p Sites bad childRadius)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix)
    {last : HDChunk p Sites bad childRadius} (hlast : chunks.getLast? = some last) :
    last.2.1 = suffix.1 := by
  induction hchunk with
  | done hinside => simp at hlast
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      cases chunks with
      | nil =>
          cases htail with
          | done _ =>
              simp at hlast
              subst last
              rfl
      | cons c cs =>
          have hlastTail : (c :: cs).getLast? = some last := by simpa using hlast
          exact ih hlastTail

private def hdThresholdChunkRise {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (chunk : Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) : ℝ :=
  (chunk.2.1.2 : ℝ) - chunk.1.2

private def hdThresholdChunkRiseSum {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ} :
    List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) → ℝ :=
  fun chunks => (chunks.map hdThresholdChunkRise).sum

private theorem hdChunkListChain_riseSum {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish))
    (hchain : hdChunkListChain chunks) :
    ∀ {first last}, chunks.head? = some first → chunks.getLast? = some last →
      hdThresholdChunkRiseSum chunks = (last.2.1.2 : ℝ) - first.1.2 := by
  induction chunks with
  | nil => intro first last hhead; simp at hhead
  | cons c rest ih =>
      intro first last hhead hlast
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      cases rest with
      | nil =>
          simp at hlast
          subst last
          simp [hdThresholdChunkRiseSum, hdThresholdChunkRise]
      | cons d ds =>
          have hpair : c.2.1 = d.1 ∧ hdChunkListChain (d :: ds) := by
            simpa [hdChunkListChain] using hchain
          have htailHead : (d :: ds).head? = some d := by simp
          have hsumTail := ih hpair.2 (first := d) (last := last) htailHead hlast
          change hdThresholdChunkRise c + hdThresholdChunkRiseSum (d :: ds) =
            (last.2.1.2 : ℝ) - c.1.2
          rw [hsumTail]
          simp [hdThresholdChunkRise, hpair.1]

private theorem hdThresholdChunking_suffix_inside {p : HDParams}
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) : hdScaleDistance p.D suffix.1 finish < childRadius := by
  induction hchunk with
  | done hinside => exact hdThresholdWalkInside_finish_inside _ _ _ _ _ _ hinside
  | more hcut htail ih => exact ih

private theorem hdThresholdChunking_chunk_rise_upper {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) : ∀ c ∈ chunks, hdThresholdChunkRise c ≤ (childRadius : ℝ) := by
  induction hchunk with
  | done hinside => simp
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      intro c hc
      rcases List.mem_cons.mp hc with hhead | htailmem
      · subst c
        have hdist := hdThresholdCutFirstExit_finish_le_radius hD hcut
        have hlevel := hdScaleLevelRise_le_distance start middle
        have hlevelReal : (middle.2 : ℝ) - start.2 ≤
            (hdScaleDistance p.D start middle : ℝ) := by exact_mod_cast hlevel
        have hdistReal : (hdScaleDistance p.D start middle : ℝ) ≤ childRadius := by
          exact_mod_cast hdist
        exact hlevelReal.trans hdistReal
      · exact ih c htailmem

private theorem hdThresholdChunking_displacement_bound {p : HDParams}
    (hD : 0 < p.D) {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) :
    hdScaleDistance p.D start finish ≤ (chunks.length + 1) * childRadius := by
  induction hchunk with
  | @done start finish walk hinside =>
      have hfinish := hdThresholdWalkInside_finish_inside Sites bad parentOrigin parentRadius
        start childRadius hinside
      simpa using hfinish.le
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      simp only [List.length_cons]
      calc
        hdScaleDistance p.D start finish ≤
            hdScaleDistance p.D start middle + hdScaleDistance p.D middle finish :=
              hdScaleDistance_triangle hD start middle finish
        _ ≤ childRadius + (chunks.length + 1) * childRadius :=
          Nat.add_le_add (hdThresholdCutFirstExit_finish_le_radius hD hcut) ih
        _ = (chunks.length + 1 + 1) * childRadius := by ring

private theorem hdThresholdChunking_net_decomposition {p : HDParams}
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) :
    (finish.2 : ℝ) - start.2 = hdThresholdChunkRiseSum chunks +
      ((finish.2 : ℝ) - suffix.1.2) := by
  induction hchunk with
  | done hinside =>
      simp [hdThresholdChunkRiseSum]
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      have hsplit : (finish.2 : ℝ) - start.2 =
          ((middle.2 : ℝ) - start.2) + ((finish.2 : ℝ) - middle.2) := by ring
      rw [hsplit, ih]
      simp [hdThresholdChunkRiseSum, hdThresholdChunkRise]
      ring

private theorem hdThresholdChunking_suffix_rise_upper {p : HDParams}
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) : (finish.2 : ℝ) - suffix.1.2 ≤ childRadius := by
  have hinside := hdThresholdChunking_suffix_inside hchunk
  have hlevel := hdScaleLevelRise_le_distance suffix.1 finish
  have hmetric : hdScaleDistance p.D suffix.1 finish ≤ childRadius := Nat.le_of_lt hinside
  have hlevelReal : (finish.2 : ℝ) - suffix.1.2 ≤
      (hdScaleDistance p.D suffix.1 finish : ℝ) := by exact_mod_cast hlevel
  exact hlevelReal.trans (by exact_mod_cast hmetric)

private def hdThresholdChunkFailure {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (η : ℝ) (chunk : Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) : Prop :=
  -(η * (childRadius : ℝ)) ≤ hdThresholdChunkRise chunk

private noncomputable def hdThresholdChunkFailureFlag {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (η : ℝ) : (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) → Bool := by
  classical
  exact fun c => decide (hdThresholdChunkFailure η c)

private noncomputable def hdThresholdChunkFailureCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (η : ℝ) (chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)) : ℕ :=
  (chunks.filter (hdThresholdChunkFailureFlag η)).length

private noncomputable def hdThresholdChunkSuccessCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (η : ℝ) (chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)) : ℕ :=
  (chunks.filter (fun c => !(hdThresholdChunkFailureFlag η c))).length

private theorem list_filter_bool_partition {α : Type*} (P : α → Bool) (xs : List α) :
    (xs.filter P).length + (xs.filter (fun x => !(P x))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hx : P x <;> simp [hx, ih] <;> omega

private theorem list_sum_if_filter_bool {α : Type*} (P : α → Bool) (xs : List α)
    (A B : ℝ) :
    (xs.map (fun x => if P x = true then A else B)).sum =
      ((xs.filter P).length : ℝ) * A +
        ((xs.filter (fun x => !(P x))).length : ℝ) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hx : P x <;> simp [hx, ih] <;> ring

private theorem list_sum_map_le {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h x (by simp)) (ih (by
        intro y hy
        exact h y (by simp [hy])))

private theorem hdThresholdChunking_rise_envelope {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) (η : ℝ) :
    hdThresholdChunkRiseSum chunks ≤
      (hdThresholdChunkFailureCount η chunks : ℝ) * childRadius -
        η * (hdThresholdChunkSuccessCount η chunks : ℝ) * childRadius := by
  classical
  let fails : (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish) → Bool :=
    hdThresholdChunkFailureFlag η
  have hpoint : ∀ c ∈ chunks,
      hdThresholdChunkRise c ≤ if fails c = true then (childRadius : ℝ) else -(η * childRadius) := by
    intro c hc
    by_cases hf : hdThresholdChunkFailure η c
    · have hup := hdThresholdChunking_chunk_rise_upper hD hchunk c hc
      have hflag : fails c = true := by simp [fails, hdThresholdChunkFailureFlag, hf]
      simpa [hflag] using hup
    · have hlt : hdThresholdChunkRise c < -(η * (childRadius : ℝ)) :=
        lt_of_not_ge hf
      have hflag : fails c = false := by simp [fails, hdThresholdChunkFailureFlag, hf]
      simpa [hflag] using hlt.le
  have hsumMap :
      (chunks.map hdThresholdChunkRise).sum ≤
        (chunks.map (fun c => if fails c = true then (childRadius : ℝ) else -(η * childRadius))).sum :=
    list_sum_map_le chunks hdThresholdChunkRise
      (fun c => if fails c = true then (childRadius : ℝ) else -(η * childRadius)) hpoint
  have hsumEq := list_sum_if_filter_bool fails chunks (childRadius : ℝ) (-(η * childRadius))
  have hfailCast : ((chunks.filter fails).length : ℝ) =
      (hdThresholdChunkFailureCount η chunks : ℝ) := by
    rfl
  have hsuccessCast : ((chunks.filter (fun c => !(fails c))).length : ℝ) =
      (hdThresholdChunkSuccessCount η chunks : ℝ) := by
    change ((chunks.filter (fun c => !(hdThresholdChunkFailureFlag η c))).length : ℝ) =
      ((chunks.filter (fun c => !(hdThresholdChunkFailureFlag η c))).length : ℝ)
    rfl
  calc
    hdThresholdChunkRiseSum chunks = (chunks.map hdThresholdChunkRise).sum := rfl
    _ ≤ _ := hsumMap
    _ = _ := by
      rw [hsumEq]
      rw [hfailCast, hsuccessCast]
      ring

private theorem hdThresholdChunking_failure_count_lower {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (Σ chunkStart : HDState p, Σ chunkFinish : HDState p,
      HDThresholdWalk Sites bad chunkStart childRadius chunkStart chunkFinish)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix)
    (M : ℕ) (hscale : parentRadius = M * childRadius) (hR : 0 < childRadius)
    (hboundary : parentRadius ≤ hdScaleDistance p.D start finish)
    (ηParent ηChild : ℝ) (hηParent : 0 ≤ ηParent) (hgap : ηParent < ηChild)
    (hηChild : 0 ≤ ηChild ∧ ηChild ≤ 1)
    (hmargin : 2 * (1 + ηChild) ≤ (ηChild - ηParent) * (M : ℝ))
    (hparent : -(ηParent * (parentRadius : ℝ)) ≤ (finish.2 : ℝ) - start.2) :
    ((ηChild - ηParent) / (2 * (1 + ηChild))) * (M : ℝ) ≤
      (hdThresholdChunkFailureCount ηChild chunks : ℝ) := by
  let q : ℕ := hdThresholdChunkFailureCount ηChild chunks
  let r : ℕ := hdThresholdChunkSuccessCount ηChild chunks
  have hcount : q + r = chunks.length := by
    dsimp [q, r]
    simpa [hdThresholdChunkFailureCount, hdThresholdChunkSuccessCount] using
      (list_filter_bool_partition (hdThresholdChunkFailureFlag ηChild) chunks)
  have hcountReal : (q : ℝ) + r = (chunks.length : ℝ) := by exact_mod_cast hcount
  have hdisp := hdThresholdChunking_displacement_bound hD hchunk
  have hmulBound : M * childRadius ≤ (chunks.length + 1) * childRadius := by
    calc
      M * childRadius = parentRadius := hscale.symm
      _ ≤ hdScaleDistance p.D start finish := hboundary
      _ ≤ _ := hdisp
  have hRreal : 0 < (childRadius : ℝ) := by exact_mod_cast hR
  have hmulBoundReal : (M : ℝ) * childRadius ≤
      ((chunks.length + 1 : ℕ) : ℝ) * childRadius := by exact_mod_cast hmulBound
  have hMbound : (M : ℝ) ≤ (chunks.length : ℝ) + 1 := by
    have h := le_of_mul_le_mul_right hmulBoundReal hRreal
    simpa using h
  have hrLower : (M : ℝ) - 1 - q ≤ r := by nlinarith [hMbound, hcountReal]
  have hnetReal := hdThresholdChunking_net_decomposition hchunk
  have hsuffix := hdThresholdChunking_suffix_rise_upper hchunk
  have hsuffixReal : (finish.2 : ℝ) - suffix.1.2 ≤ childRadius := by
    exact_mod_cast hsuffix
  have henvelope := hdThresholdChunking_rise_envelope hD hchunk ηChild
  have hnetUpper : (finish.2 : ℝ) - start.2 ≤
      q * childRadius - ηChild * r * childRadius + childRadius := by
    calc
      (finish.2 : ℝ) - start.2 =
          hdThresholdChunkRiseSum chunks + ((finish.2 : ℝ) - suffix.1.2) := hnetReal
      _ ≤ _ := add_le_add henvelope hsuffixReal
  have hparent' : -(ηParent * ((M : ℝ) * childRadius)) ≤
      (finish.2 : ℝ) - start.2 := by
    have hscaleReal : (parentRadius : ℝ) = (M : ℝ) * childRadius := by
      exact_mod_cast hscale
    simpa [hscaleReal] using hparent
  have hηProd : ηChild * ((M : ℝ) - 1 - q) * childRadius ≤
      ηChild * r * childRadius := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrLower hηChild.1) hRreal.le
  have hnetUpper' : (finish.2 : ℝ) - start.2 ≤
      ((1 + ηChild) * q + (1 + ηChild) - ηChild * M) * childRadius := by
    calc
      _ ≤ q * childRadius - ηChild * r * childRadius + childRadius := hnetUpper
      _ ≤ q * childRadius - ηChild * ((M : ℝ) - 1 - q) * childRadius + childRadius := by
        nlinarith [hηProd]
      _ = _ := by ring
  have hcoreScaled : ((ηChild - ηParent) * M - (1 + ηChild)) * childRadius ≤
      (1 + ηChild) * q * childRadius := by
    have h := le_trans hparent' hnetUpper'
    nlinarith [h]
  have hcore : (ηChild - ηParent) * M - (1 + ηChild) ≤ (1 + ηChild) * q :=
    le_of_mul_le_mul_right hcoreScaled hRreal
  have hhalf : ((ηChild - ηParent) / 2) * M ≤
      (ηChild - ηParent) * M - (1 + ηChild) := by nlinarith [hmargin]
  have hden : 0 < 2 * (1 + ηChild) := by
    exact mul_pos (by norm_num) (by linarith [hηChild.1])
  have hcoreHalf : (ηChild - ηParent) * M ≤ 2 * (1 + ηChild) * q := by
    nlinarith [hcore, hhalf]
  have hquot : ((ηChild - ηParent) * M) / (2 * (1 + ηChild)) ≤ q := by
    apply (div_le_iff₀ hden).2
    nlinarith [hcoreHalf]
  calc
    ((ηChild - ηParent) / (2 * (1 + ηChild))) * M =
        ((ηChild - ηParent) * M) / (2 * (1 + ηChild)) := by
          field_simp [hden.ne']
    _ ≤ q := hquot

private theorem hdThresholdWalk_exists_chunking {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (parentOrigin : HDState p)
    (parentRadius childRadius : ℕ) (hD : 0 < p.D) (hchild : 0 < childRadius)
    {start finish : HDState p}
    (walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish) :
    ∃ chunks suffix, HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix := by
  have hmain : ∀ n : ℕ, ∀ {x y : HDState p}
      (path : HDThresholdWalk Sites bad parentOrigin parentRadius x y),
      hdThresholdWalk_length path = n →
        ∃ chunks suffix, HDThresholdChunking Sites bad parentOrigin parentRadius childRadius
          path chunks suffix := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x y path hlen
        have hD1 : 1 ≤ p.D := by omega
        have hself : hdScaleDistance p.D x x = 0 := by
          unfold hdScaleDistance
          rw [Nat.dist_self]
          have hham : _root_.hammingDist x.1 x.1 = 0 := by simp [_root_.hammingDist]
          rw [hham, max_eq_right hD1]
          have hdiv : (p.D - 1) / p.D = 0 := Nat.div_eq_of_lt (by omega)
          simp [hdiv]
        have hinside : hdScaleDistance p.D x x < childRadius := by
          rw [hself]
          exact hchild
        rcases hdThresholdWalk_cut_or_inside Sites bad parentOrigin parentRadius x childRadius
          path hinside with hcut | hstay
        · rcases hcut with ⟨result, hcert⟩
          rcases result with ⟨middle, childWalk, rest⟩
          have hlt : hdThresholdWalk_length rest < n := by
            rw [← hlen]
            exact hdThresholdCutFirstExit_remainder_shorter hcert
          obtain ⟨chunks, suffix, htail⟩ :=
            ih (hdThresholdWalk_length rest) hlt rest rfl
          exact ⟨⟨x, ⟨middle, childWalk⟩⟩ :: chunks, suffix,
            HDThresholdChunking.more hcert htail⟩
        · exact ⟨[], ⟨x, path⟩, HDThresholdChunking.done hstay⟩
  exact hmain (hdThresholdWalk_length walk) walk rfl

/-- A relaxed scale failure is a stopped walk with insufficient net descent. -/
def hdScaleThresholdFailure {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (start : HDState p) (R : ℕ) (η : ℝ) : Prop :=
  ∃ finish : HDState p,
    Nonempty (HDThresholdWalk Sites bad start R start finish) ∧
    -(η * (R : ℝ)) ≤ (finish.2 : ℝ) - start.2

private theorem hdThresholdWalk_finish_outside {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (origin : HDState p) (R : ℕ)
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    R ≤ hdScaleDistance p.D origin finish := by
  induction hwalk with
  | stop hb => exact hb
  | up _ _ _ _ _ ih => exact ih
  | down _ _ _ _ _ ih => exact ih

private theorem hdThresholdWalk_net_count {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {origin : HDState p} {R : ℕ}
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    ((hdThresholdWalk_upCount hwalk : ℤ) - (hdThresholdWalk_downCount hwalk : ℤ)) =
      (finish.2 : ℤ) - start.2 := by
  induction hwalk with
  | stop _ => simp [hdThresholdWalk_upCount, hdThresholdWalk_downCount]
  | @up v j finish _ _ _ _ tail ih =>
      simp only [hdThresholdWalk_upCount, hdThresholdWalk_downCount,
        Nat.cast_add, Nat.cast_one]
      omega
  | @down v v' j finish _ _ _ _ tail ih =>
      simp only [hdThresholdWalk_upCount, hdThresholdWalk_downCount,
        Nat.cast_add, Nat.cast_one]
      omega

private theorem hdThresholdWalk_hamming_le_downCount {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (origin : HDState p) (R : ℕ)
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    _root_.hammingDist start.1 finish.1 ≤ p.D * hdThresholdWalk_downCount hwalk := by
  induction hwalk with
  | stop _ => simp [hdThresholdWalk_downCount]
  | up _ _ _ _ _ ih => exact ih
  | @down v v' j finish hins hv' hj hstep tail ih =>
      calc
        _ ≤ _ + _ := _root_.hammingDist_triangle v v' finish.1
        _ ≤ p.D + p.D * hdThresholdWalk_downCount tail := Nat.add_le_add hstep ih
        _ = p.D * hdThresholdWalk_downCount (HDThresholdWalk.down hins hv' hj hstep tail) := by
          simp only [hdThresholdWalk_downCount]
          rw [Nat.mul_succ]
          omega

/-- A scale-failure walk has many upward steps: its net rise and boundary displacement
force at least `(1-η)R` bad steps. -/
private theorem hdThresholdWalk_failure_upCount_lower {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (origin : HDState p) (R : ℕ) (η : ℝ)
    (hD : 0 < p.D) (hR : 0 < R) (hη0 : 0 ≤ η) (hη : η < 1)
    {finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R origin finish)
    (hnet : -(η * (R : ℝ)) ≤ (finish.2 : ℝ) - origin.2) :
    (1 - η) * (R : ℝ) ≤ (hdThresholdWalk_upCount hwalk : ℝ) := by
  have houtside := hdThresholdWalk_finish_outside Sites bad origin R hwalk
  have hD1 : 1 ≤ p.D := by omega
  have hmetric : R ≤ max (Nat.dist origin.2 finish.2)
      ((_root_.hammingDist origin.1 finish.1 + p.D - 1) / p.D) := by
    simpa [hdScaleDistance, max_eq_right hD1] using houtside
  have hnetCount := hdThresholdWalk_net_count hwalk
  have hnetReal : (hdThresholdWalk_upCount hwalk : ℝ) -
      (hdThresholdWalk_downCount hwalk : ℝ) =
        (finish.2 : ℝ) - origin.2 := by exact_mod_cast hnetCount
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hηR : η * (R : ℝ) < R := by
    nlinarith
  by_cases hlevel : R ≤ Nat.dist origin.2 finish.2
  · by_cases horig : origin.2 ≤ finish.2
    · have hrise : R ≤ finish.2 - origin.2 := by
        calc
          R ≤ Nat.dist origin.2 finish.2 := hlevel
          _ = finish.2 - origin.2 := by
            rw [Nat.dist_comm]
            exact Nat.dist_eq_sub_of_le_right horig
      have hriseReal : (R : ℝ) ≤ (finish.2 : ℝ) - origin.2 := by exact_mod_cast hrise
      have hdownNonneg : (0 : ℝ) ≤ (hdThresholdWalk_downCount hwalk : ℝ) := by positivity
      nlinarith [hriseReal, hnetReal, hdownNonneg]
    · have hfinish : finish.2 < origin.2 := by omega
      have hfall : R ≤ origin.2 - finish.2 := by
        simpa [Nat.dist_eq_sub_of_le_right (le_of_lt hfinish)] using hlevel
      have hfallReal : (R : ℝ) ≤ (origin.2 : ℝ) - finish.2 := by
        calc
          (R : ℝ) ≤ ((origin.2 - finish.2 : ℕ) : ℝ) := by exact_mod_cast hfall
          _ = (origin.2 : ℝ) - finish.2 := by
            simp [Nat.cast_sub (le_of_lt hfinish)]
      have hdownNonneg : (0 : ℝ) ≤ (hdThresholdWalk_downCount hwalk : ℝ) := by positivity
      nlinarith [hnetReal, hdownNonneg]
  · have hquot : R ≤
        (_root_.hammingDist origin.1 finish.1 + p.D - 1) / p.D := by
      by_contra hnot
      have hleft : Nat.dist origin.2 finish.2 < R := Nat.lt_of_not_ge hlevel
      have hright :
          (_root_.hammingDist origin.1 finish.1 + p.D - 1) / p.D < R :=
        Nat.lt_of_not_ge hnot
      have hmax : max (Nat.dist origin.2 finish.2)
          ((_root_.hammingDist origin.1 finish.1 + p.D - 1) / p.D) < R :=
        max_lt_iff.mpr ⟨hleft, hright⟩
      omega
    have hham := hdThresholdWalk_hamming_le_downCount Sites bad origin R hwalk
    have hnum : _root_.hammingDist origin.1 finish.1 + p.D - 1 <
        p.D * (hdThresholdWalk_downCount hwalk + 1) := by
      rw [Nat.mul_succ]
      omega
    have hdiv :
        (_root_.hammingDist origin.1 finish.1 + p.D - 1) / p.D <
          hdThresholdWalk_downCount hwalk + 1 := by
      apply (Nat.div_lt_iff_lt_mul hD).2
      simpa [Nat.mul_comm] using hnum
    have hdown : R ≤ hdThresholdWalk_downCount hwalk :=
      le_trans hquot (Nat.lt_succ_iff.mp hdiv)
    have hdownReal : (R : ℝ) ≤ hdThresholdWalk_downCount hwalk := by exact_mod_cast hdown
    have hnet' : -(η * (R : ℝ)) ≤
        (hdThresholdWalk_upCount hwalk : ℝ) - hdThresholdWalk_downCount hwalk := by
      simpa [hnetReal] using hnet
    nlinarith [hnet']

private theorem heightMetric_self {p : HDParams} (x : p.Loc) (hD : 0 < p.D) :
    heightMetric x x = 0 := by
  unfold heightMetric
  have hham : _root_.hammingDist x.1 x.1 = 0 := by simp [_root_.hammingDist]
  have hdiv : (p.D - 1) / p.D = 0 := by
    exact Nat.div_eq_of_lt (by omega)
  simp [Nat.dist_self, hham, hdiv]

private theorem heightMetric_symm {p : HDParams} (x y : p.Loc) :
    heightMetric x y = heightMetric y x := by
  unfold heightMetric
  rw [Nat.dist_comm, _root_.hammingDist_comm]

private def heightMetricSeparated {p : HDParams} (gap : ℕ) (S : Finset p.Loc) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → gap ≤ heightMetric x y

/-- A maximal separated subset of any finite family covers every point by an open
`gap`-ball. This is the packing step used for child-start configurations. -/
private theorem exists_maximal_heightMetricSeparated {p : HDParams}
    (T : Finset p.Loc) (gap : ℕ) (hgap : 0 < gap) (hD : 0 < p.D) :
    ∃ S : Finset p.Loc, S ⊆ T ∧ heightMetricSeparated gap S ∧
      ∀ x ∈ T, ∃ y ∈ S, heightMetric x y < gap := by
  classical
  let candidates : Finset (Finset p.Loc) := T.powerset.filter (heightMetricSeparated gap)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, heightMetricSeparated]
  let cardValues : Finset ℕ := candidates.image Finset.card
  have hcardValues : cardValues.Nonempty := Finset.image_nonempty.mpr hcandidates
  obtain ⟨S, hS, hSmax⟩ := Finset.mem_image.mp (Finset.max'_mem cardValues hcardValues)
  have hSsubset : S ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSsep : heightMetricSeparated gap S := (Finset.mem_filter.mp hS).2
  have hSmax' : ∀ A ∈ candidates, A.card ≤ S.card := by
    intro A hA
    have hAcard : A.card ∈ cardValues := Finset.mem_image.mpr ⟨A, hA, rfl⟩
    have hle := Finset.le_max' cardValues A.card hAcard
    rw [hSmax]
    exact hle
  refine ⟨S, hSsubset, hSsep, ?_⟩
  intro x hxT
  by_contra hcover
  have hNoClose : ∀ y ∈ S, gap ≤ heightMetric x y := by
    intro y hy
    by_contra hnot
    exact hcover ⟨y, hy, Nat.lt_of_not_ge hnot⟩
  have hxnotS : x ∉ S := by
    intro hxS
    have hself := hNoClose x hxS
    rw [heightMetric_self x hD] at hself
    omega
  have hSinsert : heightMetricSeparated gap (insert x S) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        exact False.elim (hab rfl)
      · exact hNoClose b hb
    · rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        calc
          gap ≤ heightMetric x a := hNoClose a ha
          _ = heightMetric a x := heightMetric_symm x a
      · exact hSsep a ha b hb hab
  have hInsertSubset : insert x S ⊆ T := Finset.insert_subset hxT hSsubset
  have hInsertCandidate : insert x S ∈ candidates := by
    change insert x S ∈ T.powerset.filter (heightMetricSeparated gap)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hInsertSubset, hSinsert⟩
  have hcardInsert := hSmax' (insert x S) hInsertCandidate
  have hcardEq : (insert x S).card = S.card + 1 := Finset.card_insert_of_notMem hxnotS
  omega

private def hdScaleSeparated {p : HDParams} (gap : ℕ) (S : Finset (HDState p)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → gap ≤ hdScaleDistance p.D x y

private theorem exists_maximal_hdScaleSeparated {p : HDParams}
    (T : Finset (HDState p)) (gap : ℕ) (hgap : 0 < gap) (hD : 0 < p.D) :
    ∃ S : Finset (HDState p), S ⊆ T ∧ hdScaleSeparated gap S ∧
      ∀ x ∈ T, ∃ y ∈ S, hdScaleDistance p.D x y < gap := by
  classical
  let candidates : Finset (Finset (HDState p)) := T.powerset.filter (hdScaleSeparated gap)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, hdScaleSeparated]
  let cardValues : Finset ℕ := candidates.image Finset.card
  have hcardValues : cardValues.Nonempty := Finset.image_nonempty.mpr hcandidates
  obtain ⟨S, hS, hSmax⟩ := Finset.mem_image.mp (Finset.max'_mem cardValues hcardValues)
  have hSsubset : S ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSsep : hdScaleSeparated gap S := (Finset.mem_filter.mp hS).2
  have hSmax' : ∀ A ∈ candidates, A.card ≤ S.card := by
    intro A hA
    have hAcard : A.card ∈ cardValues := Finset.mem_image.mpr ⟨A, hA, rfl⟩
    have hle := Finset.le_max' cardValues A.card hAcard
    rw [hSmax]
    exact hle
  refine ⟨S, hSsubset, hSsep, ?_⟩
  intro x hxT
  by_contra hcover
  have hNoClose : ∀ y ∈ S, gap ≤ hdScaleDistance p.D x y := by
    intro y hy
    by_contra hnot
    exact hcover ⟨y, hy, Nat.lt_of_not_ge hnot⟩
  have hxnotS : x ∉ S := by
    intro hxS
    have hself := hNoClose x hxS
    rw [hdScaleDistance_self x hD] at hself
    omega
  have hSinsert : hdScaleSeparated gap (insert x S) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        exact False.elim (hab rfl)
      · exact hNoClose b hb
    · rcases Finset.mem_insert.mp hb with hbx | hb
      · subst b
        calc
          gap ≤ hdScaleDistance p.D x a := hNoClose a ha
          _ = hdScaleDistance p.D a x := by
            unfold hdScaleDistance
            rw [Nat.dist_comm, _root_.hammingDist_comm]
      · exact hSsep a ha b hb hab
  have hInsertSubset : insert x S ⊆ T := Finset.insert_subset hxT hSsubset
  have hInsertCandidate : insert x S ∈ candidates := by
    change insert x S ∈ T.powerset.filter (hdScaleSeparated gap)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hInsertSubset, hSinsert⟩
  have hcardInsert := hSmax' (insert x S) hInsertCandidate
  have hcardEq : (insert x S).card = S.card + 1 := Finset.card_insert_of_notMem hxnotS
  omega

private noncomputable def hdFailureStartSet {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (η : ℝ) (chunks : List (HDChunk p Sites bad childRadius)) : Finset (HDState p) := by
  classical
  exact (chunks.toFinset.filter (hdThresholdChunkFailure η)).image (fun c => c.1)

private theorem hdFailureStartSet_mem {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    {η : ℝ} {chunks : List (HDChunk p Sites bad childRadius)}
    {c : HDChunk p Sites bad childRadius} (hc : c ∈ chunks)
    (hf : hdThresholdChunkFailure η c) : c.1 ∈ hdFailureStartSet η chunks := by
  classical
  unfold hdFailureStartSet
  apply Finset.mem_image.mpr
  refine ⟨c, Finset.mem_filter.mpr ⟨?_, hf⟩, rfl⟩
  simpa using hc

private theorem exists_finCoordPerm_mapping {d : ℕ} (A A' : Finset (Fin d))
    (hcard : A.card = A'.card) : ∃ π : Equiv.Perm (Fin d), A.image π = A' := by
  classical
  let p : Fin d → Prop := fun x => x ∈ A
  let q : Fin d → Prop := fun x => x ∈ A'
  let eA : {x // p x} ≃ {x // q x} := Finset.equivOfCardEq hcard
  have hsubcard : Fintype.card {x // p x} = Fintype.card {x // q x} := by
    simpa [p, q] using hcard
  have hcompcard : Fintype.card {x // ¬p x} = Fintype.card {x // ¬q x} :=
    Fintype.card_compl_eq_card_compl p q hsubcard
  let eComp : {x // ¬p x} ≃ {x // ¬q x} := Fintype.equivOfCardEq hcompcard
  let π : Equiv.Perm (Fin d) := Equiv.subtypeCongr eA eComp
  have hπA : ∀ (x : Fin d) (hx : x ∈ A), π x = ((eA ⟨x, by simpa [p] using hx⟩ : {x // q x}) : Fin d) := by
    intro x hx
    simp [π, Equiv.subtypeCongr, p, q, hx]
  refine ⟨π, ?_⟩
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [hπA x hx]
    exact (eA ⟨x, by simpa [p] using hx⟩).property
  · intro hy
    obtain ⟨x, hx⟩ := eA.surjective ⟨y, by simpa [q] using hy⟩
    refine Finset.mem_image.mpr ⟨x.1, by simpa [p] using x.2, ?_⟩
    simpa [hπA x.1 (by simpa [p] using x.2)] using congrArg Subtype.val hx

private noncomputable def hdHypergeometricTail {d : ℕ}
    (k : ℕ) (A : Finset (Fin d)) (t : ℝ) : Finset (Finset (Fin d)) := by
  classical
  exact Finset.univ.filter (fun B : Finset (Fin d) =>
    B.card = k ∧ ((B ∩ A).card : ℝ) ≥ t)

private theorem hdHypergeometricTail_card_eq_of_card_eq {d k : ℕ}
    (A A' : Finset (Fin d)) (t : ℝ) (hAA' : A.card = A'.card) :
    (hdHypergeometricTail k A t).card = (hdHypergeometricTail k A' t).card := by
  classical
  obtain ⟨π, hπA⟩ := exists_finCoordPerm_mapping A A' hAA'
  have hinv : Function.Injective π := π.injective
  let mapSet : Finset (Fin d) → Finset (Fin d) := fun B => B.image π
  have hmapSetInj : Function.Injective mapSet := by
    intro B C hBC
    have h := congrArg (fun S : Finset (Fin d) => S.image π.symm) hBC
    simpa [mapSet, Finset.image_image, Function.comp_def] using h
  have hTailImage : (hdHypergeometricTail k A t).image mapSet = hdHypergeometricTail k A' t := by
    ext B
    constructor
    · intro hB
      rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
      have hC' := Finset.mem_filter.mp hC
      simp only [hdHypergeometricTail, Finset.mem_filter, Finset.mem_univ, true_and] at hC' ⊢
      constructor
      · have hcard : (C.image π).card = C.card := Finset.card_image_of_injective _ hinv
        simpa using hcard.trans hC'.1
      · have hinter : ((C.image π) ∩ A').card = (C ∩ A).card := by
          rw [← hπA, ← Finset.image_inter C A hinv]
          exact Finset.card_image_of_injective _ hinv
        rw [hinter]
        exact hC'.2
    · intro hB
      have hB' : B.card = k ∧ ((B ∩ A').card : ℝ) ≥ t := by
        simpa [hdHypergeometricTail] using hB
      let C := B.image π.symm
      have hCimage : C.image π = B := by
        dsimp [C]
        rw [Finset.image_image]
        simp
      have hCmem : C ∈ hdHypergeometricTail k A t := by
        simp only [hdHypergeometricTail, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · have hcardC : C.card = B.card := Finset.card_image_of_injective _ π.symm.injective
          simpa [C] using hcardC.trans hB'.1
        · have hinter : (C ∩ A).image π = B ∩ A' := by
            rw [Finset.image_inter _ _ hinv, hCimage, hπA]
          have hcardInter : (C ∩ A).card = (B ∩ A').card := by
            calc
              (C ∩ A).card = ((C ∩ A).image π).card := by
                symm
                exact Finset.card_image_of_injective _ hinv
              _ = (B ∩ A').card := by rw [hinter]
          rw [hcardInter]
          exact hB'.2
      exact Finset.mem_image.mpr ⟨C, hCmem, hCimage⟩
  rw [← hTailImage, Finset.card_image_of_injective _ hmapSetInj]

private def hdHypergeomLayer (d k : ℕ) : Finset (Finset (Fin d)) :=
  Finset.univ.filter (fun A : Finset (Fin d) => A.card = k)

private theorem hdHypergeomLayer_card (d k : ℕ) :
    (hdHypergeomLayer d k).card = Nat.choose d k := by
  have hEq : hdHypergeomLayer d k = (Finset.univ : Finset (Fin d)).powersetCard k := by
    ext A
    simp [hdHypergeomLayer, Finset.mem_powersetCard]
  rw [hEq]
  simp [Finset.card_powersetCard]

/-- Transposing a uniform-layer intersection preserves its exact tail probability. -/
private theorem hdHypergeometricTail_ratio_swap {d s i : ℕ}
    (hsd : s ≤ d) (hid : i ≤ d) (A B : Finset (Fin d))
    (hA : A.card = s) (hB : B.card = i) (t : ℝ) :
    ((hdHypergeometricTail i A t).card : ℝ) / Nat.choose d i =
      ((hdHypergeometricTail s B t).card : ℝ) / Nat.choose d s := by
  classical
  let As := hdHypergeomLayer d s
  let Bi := hdHypergeomLayer d i
  let FibA := fun a : Finset (Fin d) =>
    (hdHypergeometricTail i a t).image (fun b => (a, b))
  let FibB := fun b : Finset (Fin d) =>
    (hdHypergeometricTail s b t).image (fun a => (a, b))
  let PairsA := As.biUnion FibA
  let PairsB := Bi.biUnion FibB
  have hPairs : PairsA = PairsB := by
    ext pair
    rcases pair with ⟨a, b⟩
    simp [PairsA, PairsB, As, Bi, FibA, FibB, hdHypergeomLayer,
      hdHypergeometricTail, Finset.mem_biUnion, Finset.mem_image,
      and_assoc, and_left_comm, and_comm, Finset.inter_comm]
  have hdisjA : (As : Set (Finset (Fin d))).PairwiseDisjoint FibA := by
    intro a ha a' ha' hneq
    change Disjoint (FibA a) (FibA a')
    rw [Finset.disjoint_left]
    intro z hz hz'
    rcases Finset.mem_image.mp hz with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨b', hb', heq⟩
    exact hneq (congrArg Prod.fst heq).symm
  have hdisjB : (Bi : Set (Finset (Fin d))).PairwiseDisjoint FibB := by
    intro b hb b' hb' hneq
    change Disjoint (FibB b) (FibB b')
    rw [Finset.disjoint_left]
    intro z hz hz'
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨a', ha', heq⟩
    exact hneq (congrArg Prod.snd heq).symm
  have hcardA : PairsA.card = ∑ a ∈ As, (hdHypergeometricTail i a t).card := by
    dsimp [PairsA]
    rw [Finset.card_biUnion hdisjA]
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.card_image_of_injective _ (by intro b b' heq; exact congrArg Prod.snd heq)
  have hcardB : PairsB.card = ∑ b ∈ Bi, (hdHypergeometricTail s b t).card := by
    dsimp [PairsB]
    rw [Finset.card_biUnion hdisjB]
    apply Finset.sum_congr rfl
    intro b hb
    exact Finset.card_image_of_injective _ (by intro a a' heq; exact congrArg Prod.fst heq)
  have htailA : ∑ a ∈ As, (hdHypergeometricTail i a t).card =
      As.card * (hdHypergeometricTail i A t).card := by
    calc
      _ = ∑ a ∈ As, (hdHypergeometricTail i A t).card := by
            apply Finset.sum_congr rfl
            intro a ha
            apply hdHypergeometricTail_card_eq_of_card_eq
            have haCard : a.card = s := by simpa [As, hdHypergeomLayer] using ha
            exact haCard.trans hA.symm
      _ = _ := by simp
  have htailB : ∑ b ∈ Bi, (hdHypergeometricTail s b t).card =
      Bi.card * (hdHypergeometricTail s B t).card := by
    calc
      _ = ∑ b ∈ Bi, (hdHypergeometricTail s B t).card := by
            apply Finset.sum_congr rfl
            intro b hb
            apply hdHypergeometricTail_card_eq_of_card_eq
            have hbCard : b.card = i := by simpa [Bi, hdHypergeomLayer] using hb
            exact hbCard.trans hB.symm
      _ = _ := by simp
  have hpairCard : As.card * (hdHypergeometricTail i A t).card =
      Bi.card * (hdHypergeometricTail s B t).card := by
    calc
      _ = PairsA.card := htailA.symm.trans hcardA.symm
      _ = PairsB.card := by rw [hPairs]
      _ = _ := hcardB.trans htailB
  have hAsCard : As.card = Nat.choose d s := by simpa [As] using hdHypergeomLayer_card d s
  have hBiCard : Bi.card = Nat.choose d i := by simpa [Bi] using hdHypergeomLayer_card d i
  have hpairCast : (Nat.choose d s : ℝ) * (hdHypergeometricTail i A t).card =
      (Nat.choose d i : ℝ) * (hdHypergeometricTail s B t).card := by
    exact_mod_cast (by simpa [hAsCard, hBiCard] using hpairCard)
  have hspos : 0 < (Nat.choose d s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsd
  have hipos : 0 < (Nat.choose d i : ℝ) := by
    exact_mod_cast Nat.choose_pos hid
  field_simp [hspos.ne', hipos.ne']
  nlinarith [hpairCast]

private theorem hdHypergeometricTail_union_bound {d i s k : ℕ}
    (A : Finset (Fin d)) (hA : A.card = s) (hki : k ≤ i) (hks : k ≤ s)
    (t : ℝ) (ht : (k : ℝ) ≤ t) :
    ((hdHypergeometricTail i A t).card : ℝ) ≤
      (Nat.choose s k : ℝ) * (Nat.choose (d - k) (i - k) : ℝ) := by
  classical
  let Fib : Finset (Fin d) → Finset (Finset (Fin d)) := fun C =>
    (Finset.univ.powersetCard i).filter (C ⊆ ·)
  have hcover : hdHypergeometricTail i A t ⊆ (A.powersetCard k).biUnion Fib := by
    intro B hB
    have hB' : B.card = i ∧ ((B ∩ A).card : ℝ) ≥ t := by
      simpa [hdHypergeometricTail] using hB
    have hInter : k ≤ (B ∩ A).card := by exact_mod_cast (le_trans ht hB'.2)
    obtain ⟨C, hCsubset, hCcard⟩ := Finset.exists_subset_card_eq hInter
    have hCmem : C ∈ A.powersetCard k := by
      exact Finset.mem_powersetCard.mpr ⟨hCsubset.trans Finset.inter_subset_right, hCcard⟩
    have hCtoB : C ⊆ B := hCsubset.trans Finset.inter_subset_left
    have hBmem : B ∈ Fib C := by
      simp only [Fib, Finset.mem_filter]
      exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, hB'.1⟩, hCtoB⟩
    exact Finset.mem_biUnion.mpr ⟨C, hCmem, hBmem⟩
  have hFib : ∀ C ∈ A.powersetCard k, (Fib C).card ≤ Nat.choose (d - k) (i - k) := by
    intro C hC
    have hCcard : C.card = k := (Finset.mem_powersetCard.mp hC).2
    have hCi : C.card ≤ i := by rw [hCcard]; exact hki
    have hcard := Finset.card_filter_powersetCard_subset C Finset.univ i
      (by intro x hx; simp) hCi
    exact le_of_eq (by simpa [Fib, hCcard] using hcard)
  have hcoverCard := Finset.card_biUnion_le_card_mul (A.powersetCard k) Fib
    (Nat.choose (d - k) (i - k)) hFib
  have htailNat : (hdHypergeometricTail i A t).card ≤
      (A.powersetCard k).card * Nat.choose (d - k) (i - k) :=
    le_trans (Finset.card_le_card hcover) hcoverCard
  have hAchoose : (A.powersetCard k).card = Nat.choose s k := by
    rw [Finset.card_powersetCard, hA]
  rw [hAchoose] at htailNat
  exact_mod_cast htailNat

private theorem finset_symmDiff_card_real {α : Type*} [Fintype α] [DecidableEq α]
    (B A : Finset α) :
    ((B ∆ A).card : ℝ) + 2 * ((B ∩ A).card : ℝ) = (B.card : ℝ) + A.card := by
  classical
  have hdis : Disjoint (B \ A) (A \ B) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx.2 hx'.1
  have hsymm : (B ∆ A).card = (B \ A).card + (A \ B).card := by
    rw [Finset.symmDiff_def]
    exact Finset.card_union_of_disjoint hdis
  have hBA : ((B \ A).card : ℝ) + (B ∩ A).card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter B A
  have hAB' : ((A \ B).card : ℝ) + (A ∩ B).card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A B
  have hAB : ((A \ B).card : ℝ) + (B ∩ A).card = A.card := by
    simpa [Finset.inter_comm] using hAB'
  have hsymmReal : ((B ∆ A).card : ℝ) =
      ((B \ A).card : ℝ) + ((A \ B).card : ℝ) := by exact_mod_cast hsymm
  rw [hsymmReal]
  nlinarith [hBA, hAB]

private theorem cubeDiff_symmDiff {d : ℕ} (u v z : CubeVertex d) :
    cubeDiffEquiv v z = cubeDiffEquiv u z ∆ cubeDiffEquiv u v := by
  ext i
  simp only [Finset.mem_symmDiff, cubeDiffEquiv, Equiv.coe_fn_mk,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases hu : u i <;> cases hv : v i <;> cases hz : z i <;>
    decide

private theorem hammingLayer_intersection_count_bound {d i s R q : ℕ}
    (u v : CubeVertex d) (hs : 0 < s) (hsd : s ≤ d)
    (hiR : i ≤ R) (hRD : 3 * R ≤ d) (houter : R ≤ i + q)
    (hq : 10 * q ≤ s) (hs2R : s ≤ 2 * R) (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z = i ∧ hammingDist z v ≤ R)).card : ℝ) ≤
      (Nat.choose d i : ℝ) * Real.exp (-(s : ℝ) / 50) := by
  classical
  have hd : 0 < d := by omega
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hAcard : (cubeDiffEquiv u v).card = s := by
    calc
      (cubeDiffEquiv u v).card = hammingDist v u := by
        symm
        exact hammingDist_eq_cubeDiff_card v u
      _ = s := by
        have hcomm : hammingDist v u = hammingDist u v := _root_.hammingDist_comm _ _
        rw [hcomm]
        exact hsep
  have hlayerPos : 0 < (hdHypergeomLayer d i).card := by
    rw [hdHypergeomLayer_card]
    exact Nat.choose_pos (by omega)
  obtain ⟨B, hBmem⟩ := Finset.card_pos.mp hlayerPos
  have hBcard : B.card = i := by simpa [hdHypergeomLayer] using hBmem
  have h3i : 3 * i ≤ d := by omega
  have hfrac : (i : ℝ) / d ≤ 1 / 3 := by
    apply (div_le_iff₀ hdReal).2
    have h3iReal : 3 * (i : ℝ) ≤ d := by exact_mod_cast h3i
    nlinarith
  have hmean : (i : ℝ) * s / d ≤ s / 3 := by
    calc
      (i : ℝ) * s / d = ((i : ℝ) / d) * s := by field_simp [hdReal.ne']
      _ ≤ (1 / 3) * s := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = s / 3 := by ring
  have hqReal : (q : ℝ) ≤ s / 10 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
    have hqCast : (10 : ℝ) * q ≤ s := by exact_mod_cast hq
    simpa [mul_comm] using hqCast
  have houterReal : (R : ℝ) ≤ (i : ℝ) + q := by exact_mod_cast houter
  have hthreshold : (i : ℝ) * s / d + s / 10 ≤
      ((i : ℝ) + s - R) / 2 := by
    have hreq : 9 * s / 20 ≤ ((i : ℝ) + s - R) / 2 := by
      nlinarith [houterReal, hqReal]
    have hmeanHi : (i : ℝ) * s / d + s / 10 ≤ 13 * s / 30 := by
      nlinarith [hmean]
    have hfracCmp : (13 : ℝ) * s / 30 ≤ (9 : ℝ) * s / 20 := by nlinarith [hsReal]
    exact hmeanHi.trans (hfracCmp.trans hreq)
  let A := cubeDiffEquiv u v
  let badLayer : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z = i ∧ hammingDist z v ≤ R)
  have hbadSubset : badLayer.image (cubeDiffEquiv u) ⊆
      hdHypergeometricTail i A ((i : ℝ) * s / d + s / 10) := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨z, hz, rfl⟩
    have hz' : hammingDist u z = i ∧ hammingDist z v ≤ R := by
      simpa [badLayer] using (Finset.mem_filter.mp hz).2
    have hBzcard : (cubeDiffEquiv u z).card = i := by
      calc
        (cubeDiffEquiv u z).card = hammingDist z u := by
          symm
          exact hammingDist_eq_cubeDiff_card z u
        _ = hammingDist u z := by exact _root_.hammingDist_comm _ _
        _ = i := hz'.1
    have hdiff : cubeDiffEquiv v z = cubeDiffEquiv u z ∆ A := by
      simpa [A] using cubeDiff_symmDiff u v z
    have hdistEq : (hammingDist z v : ℝ) +
        2 * ((cubeDiffEquiv u z ∩ A).card : ℝ) = (i : ℝ) + s := by
      have hcard := finset_symmDiff_card_real (cubeDiffEquiv u z) A
      have hdistCard : hammingDist z v = (cubeDiffEquiv u z ∆ A).card := by
        rw [hammingDist_eq_cubeDiff_card z v, hdiff]
      rw [← hdistCard, hBzcard, hAcard] at hcard
      exact hcard
    have hdistLe : (hammingDist z v : ℝ) ≤ R := by exact_mod_cast hz'.2
    have hinter : (i : ℝ) * s / d + s / 10 ≤
        ((cubeDiffEquiv u z ∩ A).card : ℝ) := by
      nlinarith [hdistEq, hdistLe, hthreshold]
    have htail : cubeDiffEquiv u z ∈
        hdHypergeometricTail i A ((i : ℝ) * s / d + s / 10) := by
      simp only [hdHypergeometricTail, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hBzcard, hinter⟩
    simpa [A] using htail
  have hbadCard : (badLayer.card : ℝ) ≤
      (hdHypergeometricTail i A ((i : ℝ) * s / d + s / 10)).card := by
    have hcardNat := Finset.card_le_card hbadSubset
    rw [Finset.card_image_of_injective _ (cubeDiffEquiv u).injective] at hcardNat
    exact_mod_cast hcardNat
  have htranspose := hdHypergeometricTail_ratio_swap hsd (by omega)
    A B hAcard hBcard ((i : ℝ) * s / d + s / 10)
  have hhyper := hypergeometric_intersection_tail d s hd hs hsd B (s / 10) (by positivity)
  have hhyper' :
      ((hdHypergeometricTail s B ((i : ℝ) * s / d + s / 10)).card : ℝ) /
          Nat.choose d s ≤ Real.exp (-2 * (s / 10) ^ 2 / s) := by
    simpa [hdHypergeometricTail, hBcard, mul_comm, mul_left_comm, mul_assoc] using hhyper
  have hsChoose : 0 < (Nat.choose d s : ℝ) := by exact_mod_cast Nat.choose_pos hsd
  have hiChoose : 0 < (Nat.choose d i : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hratio :
      ((hdHypergeometricTail i A ((i : ℝ) * s / d + s / 10)).card : ℝ) /
          Nat.choose d i ≤ Real.exp (-2 * (s / 10) ^ 2 / s) := by
    calc
      _ = ((hdHypergeometricTail s B ((i : ℝ) * s / d + s / 10)).card : ℝ) /
            Nat.choose d s := htranspose
      _ ≤ _ := hhyper'
  have hratioExp : Real.exp (-2 * (s / 10) ^ 2 / s) = Real.exp (-(s : ℝ) / 50) := by
    congr 1
    field_simp [hsReal.ne']
    ring
  rw [hratioExp] at hratio
  have htailBound : (hdHypergeometricTail i A ((i : ℝ) * s / d + s / 10)).card ≤
      (Nat.choose d i : ℝ) * Real.exp (-(s : ℝ) / 50) := by
    have h := (div_le_iff₀ hiChoose).mp hratio
    simpa [mul_comm] using h
  exact hbadCard.trans htailBound

private theorem hammingLayer_intersection_share_lower {d i s R q : ℕ}
    (u v : CubeVertex d) (hs : 0 < s) (houter : R ≤ i + q)
    (hq : 10 * q ≤ s) (hsep : hammingDist u v = s) :
    ∀ z, hammingDist u z = i → hammingDist z v ≤ R →
      (s : ℝ) / 3 ≤ ((cubeDiffEquiv u z ∩ cubeDiffEquiv u v).card : ℝ) := by
  intro z hzi hzv
  have hAcard : (cubeDiffEquiv u v).card = s := by
    calc
      (cubeDiffEquiv u v).card = hammingDist v u := by
        symm
        exact hammingDist_eq_cubeDiff_card v u
      _ = s := by
        have hcomm : hammingDist v u = hammingDist u v := _root_.hammingDist_comm _ _
        rw [hcomm]
        exact hsep
  have hdiff : cubeDiffEquiv v z = cubeDiffEquiv u z ∆ cubeDiffEquiv u v :=
    cubeDiff_symmDiff u v z
  have hdistEq : (hammingDist z v : ℝ) +
      2 * ((cubeDiffEquiv u z ∩ cubeDiffEquiv u v).card : ℝ) = (i : ℝ) + s := by
    have hcard := finset_symmDiff_card_real (cubeDiffEquiv u z) (cubeDiffEquiv u v)
    have hzcard : (cubeDiffEquiv u z).card = i := by
      calc
        (cubeDiffEquiv u z).card = hammingDist z u := by
          symm
          exact hammingDist_eq_cubeDiff_card z u
        _ = hammingDist u z := _root_.hammingDist_comm _ _
        _ = i := hzi
    have hdistCard : hammingDist z v =
        (cubeDiffEquiv u z ∆ cubeDiffEquiv u v).card := by
      rw [hammingDist_eq_cubeDiff_card z v, hdiff]
    rw [← hdistCard, hzcard, hAcard] at hcard
    exact hcard
  have hqReal : (q : ℝ) ≤ (s : ℝ) / 10 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
    have hqcast : (10 : ℝ) * q ≤ s := by exact_mod_cast hq
    simpa [mul_comm] using hqcast
  have houterReal : (R : ℝ) ≤ (i : ℝ) + q := by exact_mod_cast houter
  have hreq : 9 * (s : ℝ) / 20 ≤ ((i : ℝ) + s - R) / 2 := by
    nlinarith [houterReal, hqReal]
  have hdistLe : (hammingDist z v : ℝ) ≤ R := by exact_mod_cast hzv
  have hinterReal : (s : ℝ) / 3 ≤
      ((cubeDiffEquiv u z ∩ cubeDiffEquiv u v).card : ℝ) := by
    nlinarith [hdistEq, hdistLe, hreq]
  exact hinterReal

private theorem choose_lower_layer_step {d r k : ℕ}
    (hr : 0 < r) (hRD : 3 * r ≤ d) (hkr : k ≤ r) (hk : 0 < k) :
    (Nat.choose d (k - 1) : ℝ) ≤
      (Nat.choose d k : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) := by
  have hratio := hammingLayer_ratio d k (by omega) (by omega)
  have hratioR : (Nat.choose d (k - 1) : ℝ) * ((d - k + 1 : ℕ) : ℝ) =
      (Nat.choose d k : ℝ) * k := by exact_mod_cast hratio
  have hdenK : 0 < ((d - k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - k + 1)
  have hdenR : 0 < ((d - r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - r + 1)
  have hdenKCast : ((d - k + 1 : ℕ) : ℝ) = (d : ℝ) - k + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hdenRCast : ((d - r + 1 : ℕ) : ℝ) = (d : ℝ) - r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hfrac : (k : ℝ) / ((d - k + 1 : ℕ) : ℝ) ≤
      (r : ℝ) / ((d - r + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hdenK hdenR).2
    have hkrReal : (k : ℝ) ≤ r := by exact_mod_cast hkr
    have hprod : 0 ≤ ((r : ℝ) - k) * ((d : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hkrReal) (by positivity)
    rw [hdenKCast, hdenRCast]
    nlinarith [hprod]
  have hratioQuot : (Nat.choose d (k - 1) : ℝ) =
      (Nat.choose d k : ℝ) * ((k : ℝ) / ((d - k + 1 : ℕ) : ℝ)) := by
    calc
      (Nat.choose d (k - 1) : ℝ) =
          (Nat.choose d k : ℝ) * (k : ℝ) / ((d - k + 1 : ℕ) : ℝ) := by
        apply (eq_div_iff hdenK.ne').2
        nlinarith [hratioR]
      _ = _ := by ring
  calc
    (Nat.choose d (k - 1) : ℝ) =
        (Nat.choose d k : ℝ) * ((k : ℝ) / ((d - k + 1 : ℕ) : ℝ)) := hratioQuot
    _ ≤ (Nat.choose d k : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)

private theorem choose_down_layer_bound {d r q : ℕ}
    (hr : 0 < r) (hRD : 3 * r ≤ d) (hq : q ≤ r) :
    (Nat.choose d (r - q) : ℝ) ≤
      (Nat.choose d r : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq' : q ≤ r := by omega
      have hkpos : 0 < r - q := by omega
      have hstep := choose_lower_layer_step hr hRD (by omega) hkpos
      have hprev := ih hq'
      have hsub : r - (q + 1) = (r - q) - 1 := by omega
      rw [hsub]
      calc
        (Nat.choose d ((r - q) - 1) : ℝ) ≤
            (Nat.choose d (r - q) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) := hstep
        _ ≤ ((Nat.choose d r : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) *
              ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right hprev (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = (Nat.choose d r : ℝ) *
              ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (q + 1) := by rw [pow_succ]; ring

private theorem hammingLayer_intersection_sublinear_count_bound {d i s R q : ℕ}
    (u v : CubeVertex d) (hs : 3 ≤ s) (hsd : s ≤ d)
    (hiR : i ≤ R) (hRD : 3 * R ≤ d) (houter : R ≤ i + q)
    (hq : 10 * q ≤ s) (hs2R : s ≤ 2 * R) (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z = i ∧ hammingDist z v ≤ R)).card : ℝ) ≤
      (Nat.choose d i : ℝ) * (2 : ℝ) ^ s *
        ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3) := by
  classical
  have hsPos : 0 < s := by omega
  have hd : 0 < d := by omega
  have hRd : R ≤ d := by omega
  have hiD : i ≤ d := hiR.trans hRd
  let A := cubeDiffEquiv u v
  let badLayer : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z = i ∧ hammingDist z v ≤ R)
  have hbadSubset : badLayer.image (cubeDiffEquiv u) ⊆ hdHypergeometricTail i A (s / 3 : ℝ) := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨z, hz, rfl⟩
    have hz' : hammingDist u z = i ∧ hammingDist z v ≤ R := by
      simpa [badLayer] using (Finset.mem_filter.mp hz).2
    have hshare := hammingLayer_intersection_share_lower u v hsPos houter hq hsep z hz'.1 hz'.2
    have htail : ((cubeDiffEquiv u z).card : ℝ) = (i : ℝ) := by
      exact_mod_cast (by
        calc
          (cubeDiffEquiv u z).card = hammingDist z u := by
            symm
            exact hammingDist_eq_cubeDiff_card z u
          _ = hammingDist u z := _root_.hammingDist_comm _ _
          _ = i := hz'.1)
    have hlow : (s / 3 : ℝ) ≤
        ((cubeDiffEquiv u z ∩ A).card : ℝ) := by
      simpa [A] using hshare
    have htailMem : cubeDiffEquiv u z ∈ hdHypergeometricTail i A (s / 3 : ℝ) := by
      simp only [hdHypergeometricTail, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by exact_mod_cast htail, by simpa [A] using hlow⟩
    simpa [A] using htailMem
  have hbadCard : (badLayer.card : ℝ) ≤
      (hdHypergeometricTail i A (s / 3 : ℝ)).card := by
    have hcardNat := Finset.card_le_card hbadSubset
    rw [Finset.card_image_of_injective _ (cubeDiffEquiv u).injective] at hcardNat
    exact_mod_cast hcardNat
  let k := s / 3
  have hkS : k ≤ s := by dsimp [k]; omega
  have hkI : k ≤ i := by
    dsimp [k]
    omega
  have hkReal : (k : ℝ) ≤ (s : ℝ) / 3 := by
    have hdivNat : k * 3 ≤ s := by dsimp [k]; exact Nat.div_mul_le_self s 3
    have hdivCast : (k : ℝ) * 3 ≤ s := by exact_mod_cast hdivNat
    nlinarith
  have htailUnion := hdHypergeometricTail_union_bound A
    (by simpa [A] using (show (cubeDiffEquiv u v).card = s from by
      calc
        (cubeDiffEquiv u v).card = hammingDist v u := by
          symm
          exact hammingDist_eq_cubeDiff_card v u
        _ = s := by
          have hcomm : hammingDist v u = hammingDist u v := _root_.hammingDist_comm _ _
          rw [hcomm]
          exact hsep)) hkI hkS ((s : ℝ) / 3) hkReal
  have hratioTop : Nat.choose (d - k) (i - k) ≤ Nat.choose d (i - k) :=
    Nat.choose_le_choose (i - k) (by omega)
  have h3i : 3 * i ≤ d := Nat.mul_le_mul_left 3 hiR |>.trans hRD
  have hiPos : 0 < i := by omega
  have hdown := choose_down_layer_bound hiPos h3i hkI
  have hfrac : (i : ℝ) / ((d - i + 1 : ℕ) : ℝ) ≤
      (R : ℝ) / ((d - R + 1 : ℕ) : ℝ) := by
    have hdenI : 0 < ((d - i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - i + 1)
    have hdenR : 0 < ((d - R + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - R + 1)
    have hdenICast : ((d - i + 1 : ℕ) : ℝ) = (d : ℝ) - i + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
    have hdenRCast : ((d - R + 1 : ℕ) : ℝ) = (d : ℝ) - R + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
    apply (div_le_div_iff₀ hdenI hdenR).2
    rw [hdenICast, hdenRCast]
    have hiRReal : (i : ℝ) ≤ R := by exact_mod_cast hiR
    have hprod : 0 ≤ ((R : ℝ) - i) * ((d : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hiRReal) (by positivity)
    nlinarith [hprod]
  have hchooseI : (Nat.choose d (i - k) : ℝ) ≤
      (Nat.choose d i : ℝ) * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k := by
    calc
      (Nat.choose d (i - k) : ℝ) ≤
          (Nat.choose d i : ℝ) * ((i : ℝ) / ((d - i + 1 : ℕ) : ℝ)) ^ k := hdown
      _ ≤ (Nat.choose d i : ℝ) * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k := by
        apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact pow_le_pow_left₀ (by positivity) hfrac _
  have hchooseS : (Nat.choose s k : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast Nat.choose_le_two_pow s k
  have htopReal : (Nat.choose (d - k) (i - k) : ℝ) ≤
      (Nat.choose d i : ℝ) * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k := by
    have hratioTopReal : (Nat.choose (d - k) (i - k) : ℝ) ≤
        (Nat.choose d (i - k) : ℝ) := by exact_mod_cast hratioTop
    exact hratioTopReal.trans hchooseI
  have htailBound : (hdHypergeometricTail i A (s / 3 : ℝ)).card ≤
      (Nat.choose s k : ℝ) * (Nat.choose (d - k) (i - k) : ℝ) := by
    exact htailUnion
  calc
    (badLayer.card : ℝ) ≤ (hdHypergeometricTail i A (s / 3 : ℝ)).card := hbadCard
    _ ≤ (Nat.choose s k : ℝ) * (Nat.choose (d - k) (i - k) : ℝ) := htailBound
    _ ≤ (2 : ℝ) ^ s * ((Nat.choose d i : ℝ) *
          ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k) := by
        calc
          _ ≤ (Nat.choose s k : ℝ) *
                ((Nat.choose d i : ℝ) *
                  ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k) :=
            mul_le_mul_of_nonneg_left htopReal (Nat.cast_nonneg _)
          _ ≤ (2 : ℝ) ^ s *
                ((Nat.choose d i : ℝ) *
                  ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ k) :=
            mul_le_mul_of_nonneg_right hchooseS (by positivity)
    _ = _ := by ring

private theorem hammingBall_intersection_outer_bound {d R s q : ℕ}
    (u v : CubeVertex d) (hs : 0 < s) (hsd : s ≤ d)
    (hRD : 3 * R ≤ d) (hq : 10 * q ≤ s) (hs2R : s ≤ 2 * R)
    (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ R ∧ hammingDist v z ≤ R ∧ R ≤ hammingDist u z + q)).card : ℝ) ≤
      (∑ i ∈ Finset.range (R + 1), (Nat.choose d i : ℝ)) *
        Real.exp (-(s : ℝ) / 50) := by
  classical
  let U : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ R ∧ hammingDist v z ≤ R ∧ R ≤ hammingDist u z + q)
  let I : Finset ℕ := Finset.range (R + 1)
  have hfiberSumNat :
      ∑ i ∈ I, (U.filter (fun z => hammingDist u z = i)).card = U.card := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter U I (fun z => hammingDist u z)
    have hfilter : U.filter (fun z => hammingDist u z ∈ I) = U := by
      ext z
      simp [U, I, Finset.mem_range]
      omega
    rw [hfilter] at hsum
    exact hsum
  have hfiberSum :
      ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast hfiberSumNat
  have hsumBound :
      ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) ≤
        ∑ i ∈ I, (Nat.choose d i : ℝ) * Real.exp (-(s : ℝ) / 50) := by
    apply Finset.sum_le_sum
    intro i hi
    have hiR : i ≤ R := by
      simp only [I, Finset.mem_range] at hi
      omega
    have hsub : U.filter (fun z => hammingDist u z = i) ⊆
        Finset.univ.filter (fun z : CubeVertex d =>
          hammingDist u z = i ∧ hammingDist z v ≤ R) := by
      intro z hz
      have hzi := (Finset.mem_filter.mp hz).2
      have hzU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      have hdistV : hammingDist z v ≤ R := by
        have hsymm : hammingDist z v = hammingDist v z := _root_.hammingDist_comm _ _
        rw [hsymm]
        exact hzU.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hzi, hdistV⟩⟩
    have hsubCard :
        ((U.filter (fun z => hammingDist u z = i)).card : ℝ) ≤
          ((Finset.univ.filter (fun z : CubeVertex d =>
            hammingDist u z = i ∧ hammingDist z v ≤ R)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    by_cases hnonempty : (U.filter (fun z => hammingDist u z = i)).Nonempty
    · obtain ⟨z, hz⟩ := hnonempty
      have hzi := (Finset.mem_filter.mp hz).2
      have hzU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      have houterI : R ≤ i + q := by simpa [hzi] using hzU.2.2
      exact hsubCard.trans (hammingLayer_intersection_count_bound u v hs hsd hiR
        hRD houterI hq hs2R hsep)
    · have hzero : U.filter (fun z => hammingDist u z = i) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hzero]
      positivity
  calc
    (U.card : ℝ) =
        ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) := hfiberSum.symm
    _ ≤ ∑ i ∈ I, (Nat.choose d i : ℝ) * Real.exp (-(s : ℝ) / 50) := hsumBound
    _ = (∑ i ∈ I, (Nat.choose d i : ℝ)) * Real.exp (-(s : ℝ) / 50) := by
          rw [Finset.sum_mul]

private theorem hammingBall_intersection_outer_sublinear_bound {d R s q : ℕ}
    (u v : CubeVertex d) (hs : 3 ≤ s) (hsd : s ≤ d)
    (hRD : 3 * R ≤ d)
    (hq : 10 * q ≤ s) (hs2R : s ≤ 2 * R)
    (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ R ∧ hammingDist v z ≤ R ∧ R ≤ hammingDist u z + q)).card : ℝ) ≤
      (∑ i ∈ Finset.range (R + 1), (Nat.choose d i : ℝ)) *
        ((2 : ℝ) ^ s * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
  classical
  let U : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ R ∧ hammingDist v z ≤ R ∧ R ≤ hammingDist u z + q)
  let I : Finset ℕ := Finset.range (R + 1)
  have hfiberSumNat :
      ∑ i ∈ I, (U.filter (fun z => hammingDist u z = i)).card = U.card := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter U I (fun z => hammingDist u z)
    have hfilter : U.filter (fun z => hammingDist u z ∈ I) = U := by
      ext z
      simp [U, I, Finset.mem_range]
      omega
    rw [hfilter] at hsum
    exact hsum
  have hfiberSum :
      ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast hfiberSumNat
  have hfactor : (2 : ℝ) ^ s *
      ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3) ≥ 0 := by positivity
  have hsumBound :
      ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) ≤
        ∑ i ∈ I, (Nat.choose d i : ℝ) *
          ((2 : ℝ) ^ s * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hiR : i ≤ R := by
      simp only [I, Finset.mem_range] at hi
      omega
    have hsub : U.filter (fun z => hammingDist u z = i) ⊆
        Finset.univ.filter (fun z : CubeVertex d =>
          hammingDist u z = i ∧ hammingDist z v ≤ R) := by
      intro z hz
      have hzi := (Finset.mem_filter.mp hz).2
      have hzU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      have hdistV : hammingDist z v ≤ R := by
        have hsymm : hammingDist z v = hammingDist v z := _root_.hammingDist_comm _ _
        rw [hsymm]
        exact hzU.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hzi, hdistV⟩⟩
    have hsubCard :
        ((U.filter (fun z => hammingDist u z = i)).card : ℝ) ≤
          ((Finset.univ.filter (fun z : CubeVertex d =>
            hammingDist u z = i ∧ hammingDist z v ≤ R)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    by_cases hnonempty : (U.filter (fun z => hammingDist u z = i)).Nonempty
    · obtain ⟨z, hz⟩ := hnonempty
      have hzi := (Finset.mem_filter.mp hz).2
      have hzU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      have houterI : R ≤ i + q := by simpa [hzi] using hzU.2.2
      have hLayer := hammingLayer_intersection_sublinear_count_bound u v hs hsd hiR
        hRD houterI hq hs2R hsep
      exact hsubCard.trans (by simpa [mul_assoc] using hLayer)
    · have hzero : U.filter (fun z => hammingDist u z = i) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hzero]
      positivity
  calc
    (U.card : ℝ) =
        ∑ i ∈ I, ((U.filter (fun z => hammingDist u z = i)).card : ℝ) := hfiberSum.symm
    _ ≤ ∑ i ∈ I, (Nat.choose d i : ℝ) *
          ((2 : ℝ) ^ s * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3)) := hsumBound
    _ = (∑ i ∈ I, (Nat.choose d i : ℝ)) *
          ((2 : ℝ) ^ s * ((R : ℝ) / ((d - R + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
            rw [Finset.sum_mul]

private theorem choose_mono_lower_layers {d r : ℕ} (hRD : 3 * r ≤ d) :
    ∀ i ≤ r, Nat.choose d i ≤ Nat.choose d r := by
  induction r with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      rfl
  | succ r ih =>
      intro i hi
      by_cases hEq : i = r + 1
      · subst i
        rfl
      · have hi' : i ≤ r := by omega
        have hRD' : 3 * r ≤ d := by omega
        have hhalf : r < d / 2 := by omega
        exact (ih hRD' i hi').trans (Nat.choose_le_succ_of_lt_half_left hhalf)

private theorem hammingBall_inner_shell_bound {d r q : ℕ}
    (v : CubeVertex d) (hr : 0 < r) (hRD : 3 * r ≤ d) (hq : q < r) :
    ((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v < r - q)).card : ℝ) ≤
      ((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card : ℝ) *
        ((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := by
  classical
  have hrd : r ≤ d := by omega
  have hlowEq : (Finset.univ.filter (fun u : CubeVertex d =>
      hammingDist u v < r - q)) =
      Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r - q - 1) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hlowCard := cube_ball_card_eq_choose_sum v (by omega : r - q - 1 ≤ d)
  have hhighCard := cube_ball_card_eq_choose_sum v hrd
  have hlowSum :
      (∑ i ∈ Finset.range (r - q), (Nat.choose d i : ℝ)) ≤
        ((r - q : ℕ) : ℝ) * (Nat.choose d (r - q) : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (r - q), (Nat.choose d (r - q) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiR : i ≤ r - q := by simp only [Finset.mem_range] at hi; omega
        exact_mod_cast choose_mono_lower_layers (by omega : 3 * (r - q) ≤ d) i hiR
      _ = _ := by simp
  have hchooseLow : (Nat.choose d (r - q) : ℝ) ≤
      (Nat.choose d r : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q :=
    choose_down_layer_bound hr hRD (by omega)
  have hchooseV : (Nat.choose d r : ℝ) ≤
      ((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card : ℝ) := by
    rw [hhighCard, Nat.cast_sum]
    exact Finset.single_le_sum (f := fun i => (Nat.choose d i : ℝ)) (fun i hi =>
      show (0 : ℝ) ≤ (Nat.choose d i : ℝ) from Nat.cast_nonneg _)
      (show r ∈ Finset.range (r + 1) from Finset.mem_range.mpr (by omega))
  have hlowRad : r - q - 1 + 1 = r - q := by omega
  have hlowBound :
      ((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v < r - q)).card : ℝ) ≤
        ((r - q : ℕ) : ℝ) * (Nat.choose d (r - q) : ℝ) := by
    rw [hlowEq, hlowCard, hlowRad]
    simpa only [Nat.cast_sum] using hlowSum
  calc
    _ ≤ ((r - q : ℕ) : ℝ) * (Nat.choose d (r - q) : ℝ) := hlowBound
    _ ≤ ((r + 1 : ℕ) : ℝ) * (Nat.choose d r : ℝ) *
          ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := by
        calc
          _ ≤ ((r + 1 : ℕ) : ℝ) * (Nat.choose d (r - q) : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show r - q ≤ r + 1 by omega))
              (Nat.cast_nonneg _)
          _ ≤ ((r + 1 : ℕ) : ℝ) *
                ((Nat.choose d r : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) :=
              mul_le_mul_of_nonneg_left hchooseLow (by positivity)
          _ = _ := by ring
    _ ≤ ((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card : ℝ) *
          ((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := by
        have hfactor := mul_le_mul_of_nonneg_right hchooseV (by positivity : 0 ≤ (r + 1 : ℝ))
        have hα : 0 ≤ (r : ℝ) / ((d - r + 1 : ℕ) : ℝ) :=
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hpow : 0 ≤ ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := pow_nonneg hα _
        calc
          _ = ((Nat.choose d r : ℝ) * ((r + 1 : ℕ) : ℝ)) *
                ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q := by ring
          _ ≤ (((Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card : ℝ) *
                ((r + 1 : ℕ) : ℝ)) *
                ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q :=
              mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hfactor) hpow

private theorem hammingBall_intersection_total_bound {d r s q : ℕ}
    (u v : CubeVertex d) (hs : 0 < s) (hsd : s ≤ d)
    (hr : 0 < r) (hRD : 3 * r ≤ d) (hq : 10 * q ≤ s)
    (hqR : q < r) (hs2r : s ≤ 2 * r) (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ r ∧ hammingDist v z ≤ r)).card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (Real.exp (-(s : ℝ) / 50) + ((r + 1 : ℕ) : ℝ) *
          ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) := by
  classical
  let Inter : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ r ∧ hammingDist v z ≤ r)
  let Inner : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist z u < r - q)
  let Outer : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ r ∧ hammingDist v z ≤ r ∧ r ≤ hammingDist u z + q)
  have hsub : Inter ⊆ Inner ∪ Outer := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with ⟨huz, hvz⟩
    by_cases hinner : hammingDist z u < r - q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinner⟩)
    · have hsymm : hammingDist u z = hammingDist z u := _root_.hammingDist_comm _ _
      have hlow : r - q ≤ hammingDist u z := by
        apply Nat.le_of_not_gt
        intro hlt
        exact hinner (by simpa [hsymm] using hlt)
      have houter : r ≤ hammingDist u z + q := by omega
      exact Finset.mem_union_right _ <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨huz, hvz, houter⟩⟩
  have hcardUnion : Inter.card ≤ Inner.card + Outer.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le Inner Outer)
  have hcardUnionR : (Inter.card : ℝ) ≤ (Inner.card : ℝ) + (Outer.card : ℝ) := by
    exact_mod_cast hcardUnion
  have hinner := hammingBall_inner_shell_bound u hr hRD hqR
  have hinner' : (Inner.card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) := by
    simpa [Inner, mul_assoc] using hinner
  have houter := hammingBall_intersection_outer_bound u v hs hsd hRD hq hs2r hsep
  have hvol : ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) =
      ∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ) := by
    have hvolNat : (Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card =
        ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
      exact cube_ball_card_eq_choose_sum (d := d) (r := r) u (by omega)
    exact_mod_cast hvolNat
  have houter' : (Outer.card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        Real.exp (-(s : ℝ) / 50) := by
    calc
      (Outer.card : ℝ) ≤
          (∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ)) *
            Real.exp (-(s : ℝ) / 50) := by simpa [Outer] using houter
      _ = _ := by rw [hvol]
  calc
    (Inter.card : ℝ) ≤ (Inner.card : ℝ) + (Outer.card : ℝ) := hcardUnionR
    _ ≤ ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
          (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) +
        ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
          Real.exp (-(s : ℝ) / 50) := add_le_add hinner' houter'
    _ = ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (Real.exp (-(s : ℝ) / 50) + ((r + 1 : ℕ) : ℝ) *
          ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) := by ring

private theorem hammingBall_intersection_total_sublinear_bound {d r s q : ℕ}
    (u v : CubeVertex d) (hs : 3 ≤ s) (hsd : s ≤ d)
    (hr : 0 < r) (hRD : 3 * r ≤ d) (hq : 10 * q ≤ s)
    (hqR : q < r) (hs2r : s ≤ 2 * r) (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ r ∧ hammingDist v z ≤ r)).card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q +
          (2 : ℝ) ^ s * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
  classical
  let Inter : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ r ∧ hammingDist v z ≤ r)
  let Inner : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist z u < r - q)
  let Outer : Finset (CubeVertex d) := Finset.univ.filter (fun z =>
    hammingDist u z ≤ r ∧ hammingDist v z ≤ r ∧ r ≤ hammingDist u z + q)
  have hsub : Inter ⊆ Inner ∪ Outer := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with ⟨huz, hvz⟩
    by_cases hinner : hammingDist z u < r - q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinner⟩)
    · have hsymm : hammingDist u z = hammingDist z u := _root_.hammingDist_comm _ _
      have hlow : r - q ≤ hammingDist u z := by
        apply Nat.le_of_not_gt
        intro hlt
        exact hinner (by simpa [hsymm] using hlt)
      have houter : r ≤ hammingDist u z + q := by omega
      exact Finset.mem_union_right _ <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨huz, hvz, houter⟩⟩
  have hcardUnion : Inter.card ≤ Inner.card + Outer.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le Inner Outer)
  have hcardUnionR : (Inter.card : ℝ) ≤ (Inner.card : ℝ) + (Outer.card : ℝ) := by
    exact_mod_cast hcardUnion
  have hinner := hammingBall_inner_shell_bound u hr hRD hqR
  have hinner' : (Inner.card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) := by
    simpa [Inner, mul_assoc] using hinner
  have houter := hammingBall_intersection_outer_sublinear_bound u v hs hsd hRD hq hs2r hsep
  have hvol : ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) =
      ∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ) := by
    have hvolNat : (Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card =
        ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
      exact cube_ball_card_eq_choose_sum (d := d) (r := r) u (by omega)
    exact_mod_cast hvolNat
  have houter' : (Outer.card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        ((2 : ℝ) ^ s * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
    calc
      (Outer.card : ℝ) ≤
          (∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ)) *
            ((2 : ℝ) ^ s * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
              simpa [Outer] using houter
      _ = _ := by rw [hvol]
  calc
    (Inter.card : ℝ) ≤ (Inner.card : ℝ) + (Outer.card : ℝ) := hcardUnionR
    _ ≤ ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
          (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q) +
        ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
          ((2 : ℝ) ^ s * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (s / 3)) :=
        add_le_add hinner' houter'
    _ = ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (((r + 1 : ℕ) : ℝ) * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ q +
          (2 : ℝ) ^ s * ((r : ℝ) / ((d - r + 1 : ℕ) : ℝ)) ^ (s / 3)) := by ring

private theorem hammingBall_volume_enlargement_card_bound {d r T : ℕ}
    (v : CubeVertex d) (hr : 0 < r) (hRT : r + T ≤ d) :
    ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z v ≤ r + T)).card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z v ≤ r)).card : ℝ) *
        (1 + (T : ℝ) * ((d : ℝ) / r) ^ T) := by
  have hlarge : ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist z v ≤ r + T)).card : ℝ) =
        ∑ i ∈ Finset.range (r + T + 1), (Nat.choose d i : ℝ) := by
    exact_mod_cast cube_ball_card_eq_choose_sum v (by omega)
  have hsmall : ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist z v ≤ r)).card : ℝ) =
        ∑ i ∈ Finset.range (r + 1), (Nat.choose d i : ℝ) := by
    exact_mod_cast cube_ball_card_eq_choose_sum v (by omega)
  rw [hlarge, hsmall]
  exact hammingBall_volume_add_bound hr hRT

private theorem hammingBall_intersection_enlarged_linear_bound {d r T s q : ℕ}
    (u v : CubeVertex d) (hs : 0 < s) (hsd : s ≤ d)
    (hr : 0 < r) (hRT : r + T ≤ d) (hRD : 3 * (r + T) ≤ d)
    (hq : 10 * q ≤ s) (hqR : q < r + T) (hs2R : s ≤ 2 * (r + T))
    (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ r + T ∧ hammingDist v z ≤ r + T)).card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (1 + (T : ℝ) * ((d : ℝ) / r) ^ T) *
        (Real.exp (-(s : ℝ) / 50) + ((r + T + 1 : ℕ) : ℝ) *
          ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q) := by
  have htotal := hammingBall_intersection_total_bound u v hs hsd (by omega) hRD hq hqR hs2R hsep
  have htotal' :
      ((Finset.univ.filter (fun z : CubeVertex d =>
        hammingDist u z ≤ r + T ∧ hammingDist v z ≤ r + T)).card : ℝ) ≤
        ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r + T)).card : ℝ) *
          (Real.exp (-(s : ℝ) / 50) + ((r + T + 1 : ℕ) : ℝ) *
            (((r : ℝ) + T) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q) := by
    simpa only [Nat.cast_add] using htotal
  have hvolume := hammingBall_volume_enlargement_card_bound u hr hRT
  have herror : 0 ≤ Real.exp (-(s : ℝ) / 50) + ((r + T + 1 : ℕ) : ℝ) *
      ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q := by positivity
  calc
    _ ≤ ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r + T)).card : ℝ) *
          (Real.exp (-(s : ℝ) / 50) + ((r + T + 1 : ℕ) : ℝ) *
            ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q) := htotal'
    _ ≤ _ := mul_le_mul_of_nonneg_right hvolume herror

private theorem hammingBall_intersection_enlarged_sublinear_bound {d r T s q : ℕ}
    (u v : CubeVertex d) (hs : 3 ≤ s) (hsd : s ≤ d)
    (hr : 0 < r) (hRT : r + T ≤ d) (hRD : 3 * (r + T) ≤ d)
    (hq : 10 * q ≤ s) (hqR : q < r + T) (hs2R : s ≤ 2 * (r + T))
    (hsep : hammingDist u v = s) :
    ((Finset.univ.filter (fun z : CubeVertex d =>
      hammingDist u z ≤ r + T ∧ hammingDist v z ≤ r + T)).card : ℝ) ≤
      ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r)).card : ℝ) *
        (1 + (T : ℝ) * ((d : ℝ) / r) ^ T) *
        (((r + T + 1 : ℕ) : ℝ) *
            ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q +
          (2 : ℝ) ^ s *
            ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
  have htotal := hammingBall_intersection_total_sublinear_bound u v hs hsd (by omega)
    hRD hq hqR hs2R hsep
  have htotal' :
      ((Finset.univ.filter (fun z : CubeVertex d =>
        hammingDist u z ≤ r + T ∧ hammingDist v z ≤ r + T)).card : ℝ) ≤
        ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r + T)).card : ℝ) *
          (((r + T + 1 : ℕ) : ℝ) *
              (((r : ℝ) + T) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q +
            (2 : ℝ) ^ s *
              (((r : ℝ) + T) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ (s / 3)) := by
    simpa only [Nat.cast_add] using htotal
  have hvolume := hammingBall_volume_enlargement_card_bound u hr hRT
  have herror : 0 ≤ ((r + T + 1 : ℕ) : ℝ) *
      ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q +
        (2 : ℝ) ^ s *
          ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ (s / 3) := by positivity
  calc
    _ ≤ ((Finset.univ.filter (fun z : CubeVertex d => hammingDist z u ≤ r + T)).card : ℝ) *
          (((r + T + 1 : ℕ) : ℝ) *
              ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ q +
            (2 : ℝ) ^ s *
              ((r + T : ℝ) / ((d - (r + T) + 1 : ℕ) : ℝ)) ^ (s / 3)) := htotal'
    _ ≤ _ := mul_le_mul_of_nonneg_right hvolume herror

private theorem hammingDist_custom_eq_root {d : ℕ} (u v : CubeVertex d) :
    hammingDist u v = _root_.hammingDist u v := by
  classical
  simp [HypercubeRamsey.hammingDist, _root_.hammingDist]

private theorem hdChildSpatial_overlap_linear_bound {p : HDParams}
    (start₁ start₂ : HDState p) (R gap q : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hvertical : Nat.dist start₁.2 start₂.2 ≤ 2 * R)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d)
    (hq : 10 * q ≤ p.D * (gap - 1))
    (hqR : q < p.r + p.D * R + p.D) :
    ((Finset.univ.filter (fun z : CubeVertex p.d =>
      _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
      _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D)).card : ℝ) ≤
      (p.V : ℝ) * (1 + ((p.D * R + p.D : ℕ) : ℝ) *
          ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
        (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
          ((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
            ((p.r + (p.D * R + p.D) : ℝ) /
              ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q) := by
  classical
  let T : ℕ := p.D * R + p.D
  let S : Finset (CubeVertex p.d) := Finset.univ.filter (fun z =>
    hammingDist start₁.1 z ≤ p.r + T ∧
    hammingDist start₂.1 z ≤ p.r + T)
  have hSroot : S = Finset.univ.filter (fun z : CubeVertex p.d =>
      _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
      _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D) := by
    ext z
    simp [S, T, hammingDist_custom_eq_root, Nat.add_assoc]
  have hRT' : p.r + T ≤ p.d := by simpa [T] using hRT
  have hRD' : 3 * (p.r + T) ≤ p.d := by simpa [T] using hRD
  have hqR' : q < p.r + T := by simpa [T, Nat.add_assoc] using hqR
  have hspace := hdScaleSeparated_spatial_distance_lower hD hsep hvertical hgap
  have hsd : hammingDist start₁.1 start₂.1 ≤ p.d := by
    rw [hammingDist_eq_cubeDiff_card]
    exact (Finset.card_le_univ _).trans (by simp)
  have hspaceLocal : p.D * (gap - 1) ≤ hammingDist start₁.1 start₂.1 := by
    rw [hammingDist_custom_eq_root]
    exact hspace
  rw [← hSroot]
  by_cases hSne : S.Nonempty
  · obtain ⟨z, hz⟩ := hSne
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with ⟨hz₁, hz₂⟩
    have hz₂' : hammingDist z start₂.1 ≤ p.r + T := by
      simpa only [hammingDist_custom_eq_root, _root_.hammingDist_comm] using hz₂
    have hsepUpper : hammingDist start₁.1 start₂.1 ≤ 2 * (p.r + T) := by
      calc
        _ ≤ hammingDist start₁.1 z + hammingDist z start₂.1 := hammingDist_triangle _ _ _
        _ ≤ (p.r + T) + (p.r + T) := Nat.add_le_add hz₁ hz₂'
        _ = 2 * (p.r + T) := by omega
    have hgapPos : 0 < gap - 1 := by omega
    have hsepLowerPos : 0 < p.D * (gap - 1) := Nat.mul_pos hD hgapPos
    have hspos : 0 < hammingDist start₁.1 start₂.1 := by omega
    have hq' : 10 * q ≤ hammingDist start₁.1 start₂.1 := hq.trans hspaceLocal
    have hball := hammingBall_intersection_enlarged_linear_bound
      start₁.1 start₂.1 hspos hsd hr hRT' hRD' hq' hqR' hsepUpper rfl
    have hballNat := cube_ball_card_eq_choose_sum start₁.1 (by omega : p.r ≤ p.d)
    have hballReal :
        ((Finset.univ.filter (fun z : CubeVertex p.d =>
          hammingDist z start₁.1 ≤ p.r)).card : ℝ) = (p.V : ℝ) := by
      have hcast := congrArg (fun k : ℕ => (k : ℝ)) hballNat
      simpa [HDParams.V, Nat.cast_sum] using hcast
    have hExp : Real.exp (-(hammingDist start₁.1 start₂.1 : ℝ) / 50) ≤
        Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) := by
      apply Real.exp_le_exp.mpr
      have hcast : ((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) ≤
          (hammingDist start₁.1 start₂.1 : ℝ) := by exact_mod_cast hspaceLocal
      nlinarith
    have hfactor : 0 ≤ ((Finset.univ.filter (fun z : CubeVertex p.d =>
        hammingDist z start₁.1 ≤ p.r)).card : ℝ) *
          (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) := by positivity
    calc
      (S.card : ℝ) ≤ ((Finset.univ.filter (fun z : CubeVertex p.d =>
          hammingDist z start₁.1 ≤ p.r)).card : ℝ) *
            (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
            (Real.exp (-(hammingDist start₁.1 start₂.1 : ℝ) / 50) +
              ((p.r + T + 1 : ℕ) : ℝ) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q) := by
          simpa [S, T] using hball
      _ ≤ ((Finset.univ.filter (fun z : CubeVertex p.d =>
          hammingDist z start₁.1 ≤ p.r)).card : ℝ) *
            (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
            (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
              ((p.r + T + 1 : ℕ) : ℝ) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q) :=
          mul_le_mul_of_nonneg_left (add_le_add hExp (le_refl _)) hfactor
      _ = (p.V : ℝ) * (1 + ((p.D * R + p.D : ℕ) : ℝ) *
            ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
            (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
              ((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
                ((p.r + (p.D * R + p.D) : ℝ) /
                  ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q) := by
          rw [hballReal]
          simp [T, Nat.add_assoc, Nat.cast_add, Nat.cast_mul]
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    have hzero : S.card = 0 := by simp [hSempty]
    change (S.card : ℝ) ≤ _
    rw [hzero]
    norm_num
    positivity

private theorem hdChildSpatial_overlap_sublinear_bound {p : HDParams}
    (start₁ start₂ : HDState p) (R gap q : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hvertical : Nat.dist start₁.2 start₂.2 ≤ 2 * R)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d)
    (hsep3 : 3 ≤ p.D * (gap - 1))
    (hq : 10 * q ≤ p.D * (gap - 1))
    (hqR : q < p.r + p.D * R + p.D) :
    ((Finset.univ.filter (fun z : CubeVertex p.d =>
      _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
      _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D)).card : ℝ) ≤
      (p.V : ℝ) * (1 + ((p.D * R + p.D : ℕ) : ℝ) *
          ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
        (((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
            ((p.r + (p.D * R + p.D) : ℝ) /
              ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q +
          (2 : ℝ) ^ (_root_.hammingDist start₁.1 start₂.1) *
            ((p.r + (p.D * R + p.D) : ℝ) /
              ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                (_root_.hammingDist start₁.1 start₂.1 / 3)) := by
  classical
  let T : ℕ := p.D * R + p.D
  let S : Finset (CubeVertex p.d) := Finset.univ.filter (fun z =>
    hammingDist start₁.1 z ≤ p.r + T ∧
    hammingDist start₂.1 z ≤ p.r + T)
  have hSroot : S = Finset.univ.filter (fun z : CubeVertex p.d =>
      _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
      _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D) := by
    ext z
    simp [S, T, hammingDist_custom_eq_root, Nat.add_assoc]
  have hRT' : p.r + T ≤ p.d := by simpa [T] using hRT
  have hRD' : 3 * (p.r + T) ≤ p.d := by simpa [T] using hRD
  have hqR' : q < p.r + T := by simpa [T, Nat.add_assoc] using hqR
  have hspace := hdScaleSeparated_spatial_distance_lower hD hsep hvertical hgap
  have hsd : hammingDist start₁.1 start₂.1 ≤ p.d := by
    rw [hammingDist_eq_cubeDiff_card]
    exact (Finset.card_le_univ _).trans (by simp)
  have hspaceLocal : p.D * (gap - 1) ≤ hammingDist start₁.1 start₂.1 := by
    rw [hammingDist_custom_eq_root]
    exact hspace
  rw [← hSroot]
  by_cases hSne : S.Nonempty
  · obtain ⟨z, hz⟩ := hSne
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with ⟨hz₁, hz₂⟩
    have hz₂' : hammingDist z start₂.1 ≤ p.r + T := by
      simpa only [hammingDist_custom_eq_root, _root_.hammingDist_comm] using hz₂
    have hsepUpper : hammingDist start₁.1 start₂.1 ≤ 2 * (p.r + T) := by
      calc
        _ ≤ hammingDist start₁.1 z + hammingDist z start₂.1 := hammingDist_triangle _ _ _
        _ ≤ (p.r + T) + (p.r + T) := Nat.add_le_add hz₁ hz₂'
        _ = 2 * (p.r + T) := by omega
    have hs3 : 3 ≤ hammingDist start₁.1 start₂.1 := le_trans hsep3 hspaceLocal
    have hq' : 10 * q ≤ hammingDist start₁.1 start₂.1 := hq.trans hspaceLocal
    have hball := hammingBall_intersection_enlarged_sublinear_bound
      start₁.1 start₂.1 hs3 hsd hr hRT' hRD' hq' hqR' hsepUpper rfl
    have hballNat := cube_ball_card_eq_choose_sum start₁.1 (by omega : p.r ≤ p.d)
    have hballReal :
        ((Finset.univ.filter (fun z : CubeVertex p.d =>
          hammingDist z start₁.1 ≤ p.r)).card : ℝ) = (p.V : ℝ) := by
      have hcast := congrArg (fun k : ℕ => (k : ℝ)) hballNat
      simpa [HDParams.V, Nat.cast_sum] using hcast
    calc
      (S.card : ℝ) ≤ ((Finset.univ.filter (fun z : CubeVertex p.d =>
          hammingDist z start₁.1 ≤ p.r)).card : ℝ) *
            (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
            (((p.r + T + 1 : ℕ) : ℝ) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q +
              (2 : ℝ) ^ (hammingDist start₁.1 start₂.1) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^
                    (hammingDist start₁.1 start₂.1 / 3)) := by
          simpa [S, T] using hball
      _ = (p.V : ℝ) * (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
            (((p.r + T + 1 : ℕ) : ℝ) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q +
              (2 : ℝ) ^ (hammingDist start₁.1 start₂.1) *
                ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^
                    (hammingDist start₁.1 start₂.1 / 3)) := by
          rw [hballReal]
      _ ≤ (p.V : ℝ) * (1 + ((p.D * R + p.D : ℕ) : ℝ) *
            ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
            (((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
                ((p.r + (p.D * R + p.D) : ℝ) /
                  ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q +
              (2 : ℝ) ^ (_root_.hammingDist start₁.1 start₂.1) *
                ((p.r + (p.D * R + p.D) : ℝ) /
                  ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                    (_root_.hammingDist start₁.1 start₂.1 / 3)) := by
          simp [T, hammingDist_custom_eq_root, Nat.add_assoc, Nat.cast_add, Nat.cast_mul]
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    have hzero : S.card = 0 := by simp [hSempty]
    change (S.card : ℝ) ≤ _
    rw [hzero]
    norm_num
    positivity

private theorem hdChildCenterDomain_overlap_linear_bound_of_sep {p : HDParams}
    (start₁ start₂ : HDState p) (R gap q : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d)
    (hq : 10 * q ≤ p.D * (gap - 1))
    (hqR : q < p.r + p.D * R + p.D) :
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) ≤
      (2 * R + 1 : ℝ) * (p.V : ℝ) *
        (1 + ((p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
          (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
            ((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q) := by
  classical
  by_cases hvert : Nat.dist start₁.2 start₂.2 ≤ 2 * R
  · have hspatial := hdChildSpatial_overlap_linear_bound start₁ start₂ R gap q
      hD hsep hvert hgap hR hr hRT hRD hq hqR
    let T : ℕ := p.D * R + p.D
    let ρ : ℝ := (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
      (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
        ((p.r + T + 1 : ℕ) : ℝ) *
          ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q)
    have hspatial' : ((Finset.univ.filter (fun z : CubeVertex p.d =>
        _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
        _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D)).card : ℝ) ≤
          (p.V : ℝ) * ρ := by
      simpa [ρ, T, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, mul_assoc] using hspatial
    have hfull := hdChildCenterDomain_overlap_real_bound start₁ start₂ R ρ hspatial'
    simpa [ρ, T, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, mul_assoc] using hfull
  · have hvert' : 2 * R < Nat.dist start₁.2 start₂.2 := by omega
    have hdisj := hdChildCenterDomain_disjoint_levels start₁ start₂ R hvert'
    have hempty : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
    positivity

private theorem hdChildCenterDomain_overlap_sublinear_bound_of_sep {p : HDParams}
    (start₁ start₂ : HDState p) (R gap q : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d)
    (hsep3 : 3 ≤ p.D * (gap - 1))
    (hq : 10 * q ≤ p.D * (gap - 1))
    (hqR : q < p.r + p.D * R + p.D) :
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) ≤
      (2 * R + 1 : ℝ) * (p.V : ℝ) *
        (1 + ((p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
          (((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^ q +
            (2 : ℝ) ^ (_root_.hammingDist start₁.1 start₂.1) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                  (_root_.hammingDist start₁.1 start₂.1 / 3)) := by
  classical
  by_cases hvert : Nat.dist start₁.2 start₂.2 ≤ 2 * R
  · have hspatial := hdChildSpatial_overlap_sublinear_bound start₁ start₂ R gap q
      hD hsep hvert hgap hR hr hRT hRD hsep3 hq hqR
    let T : ℕ := p.D * R + p.D
    let s : ℕ := _root_.hammingDist start₁.1 start₂.1
    let ρ : ℝ := (1 + (T : ℝ) * ((p.d : ℝ) / p.r) ^ T) *
      (((p.r + T + 1 : ℕ) : ℝ) *
          ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ q +
        (2 : ℝ) ^ s *
          ((p.r + T : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ)) ^ (s / 3))
    have hspatial' : ((Finset.univ.filter (fun z : CubeVertex p.d =>
        _root_.hammingDist start₁.1 z ≤ p.r + p.D * R + p.D ∧
        _root_.hammingDist start₂.1 z ≤ p.r + p.D * R + p.D)).card : ℝ) ≤
          (p.V : ℝ) * ρ := by
      simpa [ρ, T, s, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, mul_assoc] using hspatial
    have hfull := hdChildCenterDomain_overlap_real_bound start₁ start₂ R ρ hspatial'
    simpa [ρ, T, s, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, mul_assoc] using hfull
  · have hvert' : 2 * R < Nat.dist start₁.2 start₂.2 := by omega
    have hdisj := hdChildCenterDomain_disjoint_levels start₁ start₂ R hvert'
    have hempty : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
    positivity

private theorem hdChildCenterDomain_overlap_linear_bound_of_sep_scale {p : HDParams}
    (start₁ start₂ : HDState p) (R gap : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d) :
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) ≤
      (2 * R + 1 : ℝ) * (p.V : ℝ) *
        (1 + ((p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
          (Real.exp (-((p.D * (gap - 1 : ℕ) : ℕ) : ℝ) / 50) +
            ((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                  (p.D * (gap - 1) / 10)) := by
  classical
  let T : ℕ := p.D * R + p.D
  let lower : ℕ := p.D * (gap - 1)
  let q : ℕ := lower / 10
  let S : Finset (CubeVertex p.d) := Finset.univ.filter (fun z =>
    hammingDist start₁.1 z ≤ p.r + T ∧ hammingDist start₂.1 z ≤ p.r + T)
  by_cases hvert : Nat.dist start₁.2 start₂.2 ≤ 2 * R
  · by_cases hSne : S.Nonempty
    · have hRT' : p.r + T ≤ p.d := by simpa [T] using hRT
      obtain ⟨z, hz⟩ := hSne
      have hz' := (Finset.mem_filter.mp hz).2
      rcases hz' with ⟨hz₁, hz₂⟩
      have hz₂' : hammingDist z start₂.1 ≤ p.r + T := by
        simpa only [hammingDist_custom_eq_root, _root_.hammingDist_comm] using hz₂
      have hsepUpper : hammingDist start₁.1 start₂.1 ≤ 2 * (p.r + T) := by
        calc
          _ ≤ hammingDist start₁.1 z + hammingDist z start₂.1 := hammingDist_triangle _ _ _
          _ ≤ (p.r + T) + (p.r + T) := Nat.add_le_add hz₁ hz₂'
          _ = 2 * (p.r + T) := by omega
      have hspaceLocal : lower ≤ hammingDist start₁.1 start₂.1 := by
        have hspace := hdScaleSeparated_spatial_distance_lower hD hsep hvert hgap
        dsimp [lower]
        rw [hammingDist_custom_eq_root]
        exact hspace
      have hq : 10 * q ≤ lower := by dsimp [q, lower]; omega
      have hqR : q < p.r + T := by
        have hqspace : 10 * q ≤ hammingDist start₁.1 start₂.1 := hq.trans hspaceLocal
        dsimp [q]
        omega
      have hbound := hdChildCenterDomain_overlap_linear_bound_of_sep
        start₁ start₂ R gap q hD hsep hgap hR hr hRT hRD hq
          (by simpa [T, Nat.add_assoc] using hqR)
      simpa [T, lower, q, Nat.cast_add, Nat.cast_mul, Nat.add_assoc] using hbound
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      have hS0 : S.card = 0 := by simp [hempty]
      have hsharp := hdChildCenterDomain_overlap_card_bound_sharp start₁ start₂ R
      have hcard : (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤ 0 := by
        have hsharp' :
            (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
              S.card * (2 * R + 1) := by
          simpa [S, T, hammingDist_custom_eq_root, Nat.add_assoc] using hsharp
        simpa [hS0] using hsharp'
      have hzero : (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card = 0 :=
        Nat.eq_zero_of_le_zero hcard
      have hzeroR :
          ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) = 0 := by
        exact_mod_cast hzero
      calc
        _ ≤ 0 := le_of_eq hzeroR
        _ ≤ _ := by positivity
  · have hvert' : 2 * R < Nat.dist start₁.2 start₂.2 := by omega
    have hdisj := hdChildCenterDomain_disjoint_levels start₁ start₂ R hvert'
    have hempty : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
    positivity

private theorem hdChildCenterDomain_overlap_sublinear_bound_of_sep_scale {p : HDParams}
    (start₁ start₂ : HDState p) (R gap : ℕ) (hD : 0 < p.D)
    (hsep : gap ≤ hdScaleDistance p.D start₁ start₂)
    (hgap : 2 * R < gap) (hR : 0 < R) (hr : 0 < p.r)
    (hRT : p.r + (p.D * R + p.D) ≤ p.d)
    (hRD : 3 * (p.r + (p.D * R + p.D)) ≤ p.d)
    (hsep3 : 3 ≤ p.D * (gap - 1)) :
    ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) ≤
      (2 * R + 1 : ℝ) * (p.V : ℝ) *
        (1 + ((p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (p.D * R + p.D)) *
          (((p.r + (p.D * R + p.D) + 1 : ℕ) : ℝ) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                  (p.D * (gap - 1) / 10) +
            (2 : ℝ) ^ (_root_.hammingDist start₁.1 start₂.1) *
              ((p.r + (p.D * R + p.D) : ℝ) /
                ((p.d - (p.r + (p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                  (_root_.hammingDist start₁.1 start₂.1 / 3)) := by
  classical
  let T : ℕ := p.D * R + p.D
  let lower : ℕ := p.D * (gap - 1)
  let q : ℕ := lower / 10
  let S : Finset (CubeVertex p.d) := Finset.univ.filter (fun z =>
    hammingDist start₁.1 z ≤ p.r + T ∧ hammingDist start₂.1 z ≤ p.r + T)
  by_cases hvert : Nat.dist start₁.2 start₂.2 ≤ 2 * R
  · by_cases hSne : S.Nonempty
    · have hRT' : p.r + T ≤ p.d := by simpa [T] using hRT
      obtain ⟨z, hz⟩ := hSne
      have hz' := (Finset.mem_filter.mp hz).2
      rcases hz' with ⟨hz₁, hz₂⟩
      have hz₂' : hammingDist z start₂.1 ≤ p.r + T := by
        simpa only [hammingDist_custom_eq_root, _root_.hammingDist_comm] using hz₂
      have hsepUpper : hammingDist start₁.1 start₂.1 ≤ 2 * (p.r + T) := by
        calc
          _ ≤ hammingDist start₁.1 z + hammingDist z start₂.1 := hammingDist_triangle _ _ _
          _ ≤ (p.r + T) + (p.r + T) := Nat.add_le_add hz₁ hz₂'
          _ = 2 * (p.r + T) := by omega
      have hspaceLocal : lower ≤ hammingDist start₁.1 start₂.1 := by
        have hspace := hdScaleSeparated_spatial_distance_lower hD hsep hvert hgap
        dsimp [lower]
        rw [hammingDist_custom_eq_root]
        exact hspace
      have hq : 10 * q ≤ lower := by dsimp [q, lower]; omega
      have hqR : q < p.r + T := by
        have hqspace : 10 * q ≤ hammingDist start₁.1 start₂.1 := hq.trans hspaceLocal
        dsimp [q]
        omega
      have hbound := hdChildCenterDomain_overlap_sublinear_bound_of_sep
        start₁ start₂ R gap q hD hsep hgap hR hr hRT hRD hsep3 hq
          (by simpa [T, Nat.add_assoc] using hqR)
      simpa [T, lower, q, Nat.cast_add, Nat.cast_mul, Nat.add_assoc] using hbound
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      have hS0 : S.card = 0 := by simp [hempty]
      have hsharp := hdChildCenterDomain_overlap_card_bound_sharp start₁ start₂ R
      have hcard : (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤ 0 := by
        have hsharp' :
            (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card ≤
              S.card * (2 * R + 1) := by
          simpa [S, T, hammingDist_custom_eq_root, Nat.add_assoc] using hsharp
        simpa [hS0] using hsharp'
      have hzero : (hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card = 0 :=
        Nat.eq_zero_of_le_zero hcard
      have hzeroR :
          ((hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R).card : ℝ) = 0 := by
        exact_mod_cast hzero
      calc
        _ ≤ 0 := le_of_eq hzeroR
        _ ≤ _ := by positivity
  · have hvert' : 2 * R < Nat.dist start₁.2 start₂.2 := by omega
    have hdisj := hdChildCenterDomain_disjoint_levels start₁ start₂ R hvert'
    have hempty : hdChildCenterDomain start₁ R ∩ hdChildCenterDomain start₂ R = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hempty]
    positivity

private theorem hdScaleRadius_child_enlargement_le_dimension_eventually
    (D : ℕ) (σ ζ c_d : ℝ) (hD : 0 < D) (hcd : 0 < c_d)
    (hζ : 0 < ζ ∧ ζ < 1) :
    ∃ n₀ : ℕ, ∀ n d i, n₀ ≤ n → c_d * (n : ℝ) ≤ (d : ℝ) →
      i < hdScaleIndex n σ ζ → 12 * (D * hdScaleRadius n σ i + D) ≤ d := by
  have he : 0 < 1 - ζ := sub_pos.mpr hζ.2
  let C : ℝ := 36 * (D : ℝ) / c_d
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨Npow, hNpow⟩ := exists_nat_rpow_ge (e := ζ) (C := C) hζ.1
  let n₀ := max 2 Npow
  refine ⟨n₀, ?_⟩
  intro n d i hn hdim hi
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 _) hn
  have hnPow : Npow ≤ n := le_trans (Nat.le_max_right 2 _) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have htarget := (hdScaleIndex_spec n σ ζ).2 i hi
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hceil : (target : ℝ) < (n : ℝ) ^ (1 - ζ) + 1 := by
    dsimp [target]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le _)
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - ζ) := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (1 - ζ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hζ.2])
  have hscale : (hdScaleRadius n σ i : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
    have hscale' : (hdScaleRadius n σ i : ℝ) < (target : ℝ) := by exact_mod_cast htarget
    linarith
  have hcoef : 36 * (D : ℝ) ≤ c_d * (n : ℝ) ^ ζ := by
    calc
      36 * (D : ℝ) = C * c_d := by dsimp [C]; field_simp [hcd.ne']
      _ ≤ (n : ℝ) ^ ζ * c_d :=
        mul_le_mul_of_nonneg_right (hNpow n hnPow) hcd.le
      _ = c_d * (n : ℝ) ^ ζ := by ring
  have hpower : (n : ℝ) ^ ζ * (n : ℝ) ^ (1 - ζ) = (n : ℝ) := by
    rw [← Real.rpow_add hnpos]
    have hexp : ζ + (1 - ζ) = 1 := by ring
    rw [hexp, Real.rpow_one]
  have hT : ((D * hdScaleRadius n σ i + D : ℕ) : ℝ) ≤
      3 * (D : ℝ) * (n : ℝ) ^ (1 - ζ) := by
    have hDreal : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [hscale, hpow1, hDreal]
  have hboundReal :
      12 * ((D * hdScaleRadius n σ i + D : ℕ) : ℝ) ≤ (d : ℝ) := by
    calc
      _ ≤ 36 * (D : ℝ) * (n : ℝ) ^ (1 - ζ) := by nlinarith [hT]
      _ ≤ c_d * (n : ℝ) ^ ζ * (n : ℝ) ^ (1 - ζ) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnpos.le _)
      _ = c_d * (n : ℝ) := by rw [mul_assoc, hpower]
      _ ≤ _ := hdim
  exact_mod_cast hboundReal

private theorem hdThresholdWalk_up_or_down {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (origin : HDState p) (R : ℕ)
    {start finish : HDState p}
    (hwalk : HDThresholdWalk Sites bad origin R start finish) :
    (∃ v j, v ∈ Sites ∧ bad v j ∧ hdScaleDistance p.D origin (v, j) < R) ∨
      (finish.2 ≤ start.2 ∧
        _root_.hammingDist start.1 finish.1 ≤ p.D * (start.2 - finish.2)) := by
  induction hwalk with
  | stop _ => right; exact ⟨le_rfl, by simp⟩
  | up hins hv _ hbad _ => exact Or.inl ⟨_, _, hv, hbad, hins⟩
  | @down v v' j finish hins hv' hj hstep tail ih =>
      rcases ih with hbad | ⟨hlevel, hspace⟩
      · exact Or.inl hbad
      · right
        constructor
        · omega
        · calc
            _ ≤ _ + _ := _root_.hammingDist_triangle _ _ _
            _ ≤ p.D + p.D * (j - finish.2) := Nat.add_le_add hstep hspace
            _ = p.D * ((j + 1) - finish.2) := by
              have hdiff : (j + 1) - finish.2 = (j - finish.2) + 1 := by omega
              rw [hdiff, Nat.mul_add]
              omega

/-- Split a finite chunk list just after its last start in the ball about `center`.
This is the list-level form of the skip-to-last-visit operation in the scale argument. -/
private noncomputable def hdLastNearSplit {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (gap : ℕ) (center : HDState p) : List (HDChunk p Sites bad childRadius) →
      Option (List (HDChunk p Sites bad childRadius) × List (HDChunk p Sites bad childRadius))
  | [] => none
  | c :: cs =>
      match hdLastNearSplit gap center cs with
      | some (pre, post) => some (c :: pre, post)
      | none => if hdScaleDistance p.D c.1 center < gap then some ([c], cs) else none
termination_by xs => xs.length
decreasing_by simp_wf

private theorem hdLastNearSplit_none_iff {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (gap : ℕ) (center : HDState p) (xs : List (HDChunk p Sites bad childRadius)) :
    hdLastNearSplit gap center xs = none ↔
      ∀ c ∈ xs, gap ≤ hdScaleDistance p.D c.1 center := by
  classical
  induction xs with
  | nil => simp [hdLastNearSplit]
  | cons c cs ih =>
      cases htail : hdLastNearSplit gap center cs with
      | some pair =>
          have hnot : ¬ ∀ a ∈ cs, gap ≤ hdScaleDistance p.D a.1 center := by
            intro hall
            have hnone := ih.mpr hall
            rw [htail] at hnone
            contradiction
          simp [hdLastNearSplit, htail, List.forall_mem_cons, hnot]
      | none =>
          have hfar := ih.mp htail
          simp [hdLastNearSplit, htail, List.forall_mem_cons, hfar]
          all_goals exact fun _ => hfar

private theorem hdLastNearSplit_spec {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (gap : ℕ) (center : HDState p) (xs : List (HDChunk p Sites bad childRadius))
    {pre post : List (HDChunk p Sites bad childRadius)}
    (hsplit : hdLastNearSplit gap center xs = some (pre, post)) :
    xs = pre ++ post ∧ pre ≠ [] ∧
      (∃ c, pre.getLast? = some c ∧ hdScaleDistance p.D c.1 center < gap) ∧
      ∀ c ∈ post, gap ≤ hdScaleDistance p.D c.1 center := by
  classical
  induction xs generalizing pre post with
  | nil => simp [hdLastNearSplit] at hsplit
  | cons c cs ih =>
      cases htail : hdLastNearSplit gap center cs with
      | none =>
          by_cases hnear : hdScaleDistance p.D c.1 center < gap
          · simp only [hdLastNearSplit, htail] at hsplit
            rw [if_pos hnear] at hsplit
            have hpair : ([c], cs) = (pre, post) := Option.some.inj hsplit
            cases hpair
            have hfar := (hdLastNearSplit_none_iff gap center cs).mp htail
            refine ⟨by simp, by simp, ?_, hfar⟩
            exact ⟨c, by simp, hnear⟩
          · simp only [hdLastNearSplit, htail] at hsplit
            rw [if_neg hnear] at hsplit
            simp at hsplit
      | some pair =>
          rcases pair with ⟨pre', post'⟩
          have htail' : hdLastNearSplit gap center cs = some (pre', post') := htail
          have hspec := ih (pre := pre') (post := post') htail'
          simp only [hdLastNearSplit, htail] at hsplit
          have hpair : (c :: pre', post') = (pre, post) := Option.some.inj hsplit
          cases hpair
          obtain ⟨hcat, hne, hlast, hfar⟩ := hspec
          have hpre : pre' ≠ [] := by
            intro he
            subst pre'
            simp at hne
          have hlast' : ∃ d, (c :: pre').getLast? = some d ∧
              hdScaleDistance p.D d.1 center < gap := by
            obtain ⟨d, hd, hdist⟩ := hlast
            refine ⟨d, ?_, hdist⟩
            rw [List.getLast?_cons_of_ne_nil hpre]
            exact hd
          refine ⟨by simp [hcat], by simp [hne], hlast', hfar⟩

private def hdChunkListJoin {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (xs ys : List (HDChunk p Sites bad childRadius)) : Prop :=
  ∀ a b, xs.getLast? = some a → ys.head? = some b → a.2.1 = b.1

private theorem hdChunkListChain_append {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (xs ys : List (HDChunk p Sites bad childRadius)) :
    hdChunkListChain (xs ++ ys) ↔
      hdChunkListChain xs ∧ hdChunkListChain ys ∧ hdChunkListJoin xs ys := by
  induction xs generalizing ys with
  | nil => simp [hdChunkListChain, hdChunkListJoin]
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases ys with
          | nil => simp [hdChunkListChain, hdChunkListJoin]
          | cons d ds => simp [hdChunkListChain, hdChunkListJoin, and_comm]
      | cons d ds =>
          change (c.2.1 = d.1 ∧ hdChunkListChain ((d :: ds) ++ ys)) ↔
            hdChunkListChain (c :: d :: ds) ∧ hdChunkListChain ys ∧
              hdChunkListJoin (c :: d :: ds) ys
          rw [ih]
          simp [hdChunkListChain, hdChunkListJoin, and_assoc, and_left_comm, and_comm]

private theorem hdChunkListChain_tail {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    {c : HDChunk p Sites bad childRadius} {xs : List (HDChunk p Sites bad childRadius)}
    (hchain : hdChunkListChain (c :: xs)) : hdChunkListChain xs := by
  cases xs with
  | nil => simp [hdChunkListChain]
  | cons d ds =>
      have hpair : c.2.1 = d.1 ∧ hdChunkListChain (d :: ds) := by
        simpa [hdChunkListChain] using hchain
      exact hpair.2

private theorem hdThresholdChunkRiseSum_append {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (xs ys : List (HDChunk p Sites bad childRadius)) :
    hdThresholdChunkRiseSum (xs ++ ys) =
      hdThresholdChunkRiseSum xs + hdThresholdChunkRiseSum ys := by
  simp [hdThresholdChunkRiseSum, List.map_append]

private theorem hdScaleDistance_symm {p : HDParams}
    (s t : HDState p) : hdScaleDistance p.D s t = hdScaleDistance p.D t s := by
  unfold hdScaleDistance
  rw [Nat.dist_comm, _root_.hammingDist_comm]

private theorem hdChunkSkipPrefix_rise_upper {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop} {childRadius gap : ℕ}
    {center : HDState p} {pre : List (HDChunk p Sites bad childRadius)}
    (hchain : hdChunkListChain pre)
    (hfirst : ∃ c, pre.head? = some c ∧ hdScaleDistance p.D c.1 center < gap)
    (hlast : ∃ c, pre.getLast? = some c ∧ hdScaleDistance p.D c.1 center < gap)
    (hbound : ∀ c ∈ pre, hdThresholdChunkRise c ≤ (childRadius : ℝ)) :
    hdThresholdChunkRiseSum pre ≤ 2 * (gap : ℝ) + childRadius := by
  rcases hfirst with ⟨first, hhead, hfirstNear⟩
  rcases hlast with ⟨last, hlastEq, hlastNear⟩
  have hsum := hdChunkListChain_riseSum pre hchain hhead hlastEq
  have hlastMem : last ∈ pre := List.mem_of_getLast? hlastEq
  have hlastBound := hbound last hlastMem
  have hsymm := hdScaleDistance_symm center last.1
  have hdist : hdScaleDistance p.D first.1 last.1 ≤ 2 * gap := by
    calc
      hdScaleDistance p.D first.1 last.1 ≤
          hdScaleDistance p.D first.1 center + hdScaleDistance p.D center last.1 :=
            hdScaleDistance_triangle hD first.1 center last.1
      _ ≤ gap + gap := Nat.add_le_add (Nat.le_of_lt hfirstNear)
        (by simpa [hsymm] using (Nat.le_of_lt hlastNear))
      _ = 2 * gap := by omega
  have hlevel : (last.1.2 : ℝ) - first.1.2 ≤
      (hdScaleDistance p.D first.1 last.1 : ℝ) := by
    exact_mod_cast hdScaleLevelRise_le_distance first.1 last.1
  have hdistReal : (hdScaleDistance p.D first.1 last.1 : ℝ) ≤ 2 * (gap : ℝ) := by
    exact_mod_cast hdist
  rw [hsum]
  unfold hdThresholdChunkRise at hlastBound
  nlinarith [hlastBound, hlevel, hdistReal]

private theorem hdChunkSkipPrefix_distance_upper {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop} {childRadius gap : ℕ}
    {center : HDState p} {pre : List (HDChunk p Sites bad childRadius)}
    (hfirst : ∃ c, pre.head? = some c ∧ hdScaleDistance p.D c.1 center < gap)
    (hlastNear : ∃ c, pre.getLast? = some c ∧ hdScaleDistance p.D c.1 center < gap)
    (hbound : ∀ c ∈ pre, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius) :
    ∀ first last, pre.head? = some first → pre.getLast? = some last →
      hdScaleDistance p.D first.1 last.2.1 ≤ 2 * gap + childRadius := by
  intro first last hhead hgetLast
  rcases hfirst with ⟨first', hfirst', hfirstNear⟩
  rcases hlastNear with ⟨last', hlast', hlastNear⟩
  have hfirstEq : first = first' := by simpa [hhead] using hfirst'
  have hlastEq : last = last' := by simpa [hgetLast] using hlast'
  subst first'
  subst last'
  have hlastMem : last ∈ pre := List.mem_of_getLast? hgetLast
  have hlastBound := hbound last hlastMem
  have hsymm := hdScaleDistance_symm center last.1
  have hcenterBound : hdScaleDistance p.D first.1 center +
      hdScaleDistance p.D center last.1 ≤ gap + gap :=
    Nat.add_le_add (Nat.le_of_lt hfirstNear)
      (by simpa [hsymm] using Nat.le_of_lt hlastNear)
  calc
    hdScaleDistance p.D first.1 last.2.1 ≤
        hdScaleDistance p.D first.1 last.1 + hdScaleDistance p.D last.1 last.2.1 :=
          hdScaleDistance_triangle hD first.1 last.1 last.2.1
    _ ≤ (hdScaleDistance p.D first.1 center +
          hdScaleDistance p.D center last.1) + childRadius := by
        exact Nat.add_le_add
          (hdScaleDistance_triangle hD first.1 center last.1) hlastBound
    _ ≤ gap + gap + childRadius := Nat.add_le_add_right hcenterBound childRadius
    _ ≤ 2 * gap + childRadius := by omega

private theorem hdThresholdChunking_chunk_displacement_bound {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius : ℕ}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (HDChunk p Sites bad childRadius)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix) :
    ∀ c ∈ chunks, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius := by
  induction hchunk with
  | done _ => simp
  | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
      intro c hc
      rcases List.mem_cons.mp hc with hhead | htailmem
      · subst c
        exact hdThresholdCutFirstExit_finish_le_radius hD hcut
      · exact ih c htailmem

private inductive HDChunkSkipBlock {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
  | clear (chunk : HDChunk p Sites bad childRadius)
  | skipped (center : HDState p) (chunks : List (HDChunk p Sites bad childRadius))

private inductive HDChunkCoverPartition {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (gap : ℕ) (η : ℝ) :
    Finset (HDState p) → List (HDChunk p Sites bad childRadius) →
      List (HDChunkSkipBlock (Sites := Sites) (bad := bad) (childRadius := childRadius)) → Prop
  | nil (centers : Finset (HDState p)) :
      HDChunkCoverPartition gap η centers [] []
  | clear {centers : Finset (HDState p)} {c : HDChunk p Sites bad childRadius}
      {rest : List (HDChunk p Sites bad childRadius)} {blocks} 
      (hfar : ∀ x ∈ centers, gap ≤ hdScaleDistance p.D c.1 x)
      (hgood : ¬ hdThresholdChunkFailure η c)
      (htail : HDChunkCoverPartition gap η centers rest blocks) :
      HDChunkCoverPartition gap η centers (c :: rest)
        (HDChunkSkipBlock.clear c :: blocks)
  | skip {centers : Finset (HDState p)} {x : HDState p}
      {pre post : List (HDChunk p Sites bad childRadius)} {blocks}
      (hx : x ∈ centers)
      (hfirst : ∃ c, pre.head? = some c ∧ hdScaleDistance p.D c.1 x < gap)
      (hlast : ∃ c, pre.getLast? = some c ∧ hdScaleDistance p.D c.1 x < gap)
      (hfar : ∀ c ∈ post, gap ≤ hdScaleDistance p.D c.1 x)
      (htail : HDChunkCoverPartition gap η (centers.erase x) post blocks) :
      HDChunkCoverPartition gap η centers (pre ++ post)
        (HDChunkSkipBlock.skipped x pre :: blocks)

private theorem hdChunkCoverPartition_empty_blocks {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius gap : ℕ} {η : ℝ}
    {centers : Finset (HDState p)} {chunks : List (HDChunk p Sites bad childRadius)}
    {blocks : List (HDChunkSkipBlock (Sites := Sites) (bad := bad) (childRadius := childRadius))}
    (hpart : HDChunkCoverPartition gap η centers chunks blocks) (hempty : chunks = []) :
    blocks = [] := by
  induction hpart with
  | nil centers => rfl
  | clear hfar hgood htail ih => simp at hempty
  | @skip centers x pre post blocks hx hfirst hlast hfar htail ih =>
      have hsplit : pre ++ post = [] := by simpa using hempty
      rcases List.append_eq_nil_iff.mp hsplit with ⟨hpre, hpost⟩
      subst pre post
      rcases hfirst with ⟨c, hc, _⟩
      simp at hc

private def hdChunkSkipCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ} :
    List (HDChunkSkipBlock (Sites := Sites) (bad := bad) (childRadius := childRadius)) → ℕ
  | [] => 0
  | .clear _ :: blocks => hdChunkSkipCount blocks
  | .skipped _ _ :: blocks => hdChunkSkipCount blocks + 1

private def hdChunkClearCount {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ} :
    List (HDChunkSkipBlock (Sites := Sites) (bad := bad) (childRadius := childRadius)) → ℕ
  | [] => 0
  | .clear _ :: blocks => hdChunkClearCount blocks + 1
  | .skipped _ _ :: blocks => hdChunkClearCount blocks

private def hdChunkCoverBudget {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius : ℕ}
    (gap : ℕ)
    (blocks : List (HDChunkSkipBlock (Sites := Sites) (bad := bad) (childRadius := childRadius))) : ℕ :=
  hdChunkClearCount blocks * childRadius + hdChunkSkipCount blocks * (2 * gap + childRadius)

private theorem hdChunkCoverPartition_span_bound {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {childRadius gap : ℕ} {η : ℝ} {centers : Finset (HDState p)}
    {chunks : List (HDChunk p Sites bad childRadius)} {blocks}
    (hpart : HDChunkCoverPartition gap η centers chunks blocks)
    (hchain : hdChunkListChain chunks)
    (hbound : ∀ c ∈ chunks, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius) :
    ∀ first last, chunks.head? = some first → chunks.getLast? = some last →
      hdScaleDistance p.D first.1 last.2.1 ≤ hdChunkCoverBudget gap blocks := by
  revert hchain hbound
  induction hpart with
  | nil centers =>
      intro hchain hbound
      intro first last hhead hlast
      simp at hhead
  | @clear centers c rest blocks hfar hgood htail ih =>
      intro hchain hbound first last hhead hlast
      cases rest with
      | nil =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst first
          simp at hlast
          subst last
          have hdist := hbound c (by simp)
          have hmul : childRadius ≤ (hdChunkClearCount blocks + 1) * childRadius := by
            calc
              childRadius = 1 * childRadius := by simp
              _ ≤ (hdChunkClearCount blocks + 1) * childRadius :=
                Nat.mul_le_mul_right childRadius (by omega)
          have hbudget : childRadius ≤
              (hdChunkClearCount blocks + 1) * childRadius +
                hdChunkSkipCount blocks * (2 * gap + childRadius) := by
            exact le_trans hmul (Nat.le_add_right _ _)
          exact hdist.trans (by simpa [hdChunkCoverBudget, hdChunkClearCount,
            hdChunkSkipCount] using hbudget)
      | cons d ds =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst first
          have hpair : c.2.1 = d.1 ∧ hdChunkListChain (d :: ds) := by
            simpa [hdChunkListChain] using hchain
          have hlastRest : (d :: ds).getLast? = some last := by simpa using hlast
          have hboundC := hbound c (by simp)
          have hboundRest : ∀ a ∈ d :: ds, hdScaleDistance p.D a.1 a.2.1 ≤ childRadius := by
            intro a ha
            exact hbound a (by simp [ha])
          have htailBound := ih hpair.2 hboundRest d last (by simp) hlastRest
          calc
            hdScaleDistance p.D c.1 last.2.1 ≤
                hdScaleDistance p.D c.1 c.2.1 + hdScaleDistance p.D c.2.1 last.2.1 :=
                  hdScaleDistance_triangle hD c.1 c.2.1 last.2.1
            _ ≤ childRadius + hdChunkCoverBudget gap blocks :=
                  Nat.add_le_add hboundC (by simpa [hpair.1] using htailBound)
            _ = hdChunkCoverBudget gap (HDChunkSkipBlock.clear c :: blocks) := by
                  simp [hdChunkCoverBudget, hdChunkClearCount, hdChunkSkipCount, Nat.add_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

  | @skip centers x pre post blocks hx hfirst hlastNear hfar htail ih =>
      cases post with
      | nil =>
          have hblocks : blocks = [] := hdChunkCoverPartition_empty_blocks htail rfl
          subst blocks
          intro hchain hbound first last hhead hlast
          have hboundPre : ∀ c ∈ pre, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius := by
            intro c hc
            exact hbound c (by simpa using hc)
          have hheadPre : pre.head? = some first := by simpa using hhead
          have hlastPre : pre.getLast? = some last := by simpa using hlast
          have hskip := hdChunkSkipPrefix_distance_upper hD hfirst hlastNear hboundPre
            first last hheadPre hlastPre
          simpa [hdChunkCoverBudget, hdChunkClearCount, hdChunkSkipCount] using hskip
      | cons d ds =>
          intro hchain hbound first last hhead hlast
          have hpreNe : pre ≠ [] := by
            rcases hfirst with ⟨c, hc, _⟩
            intro he
            simp [he] at hc
          have hpostNe : d :: ds ≠ [] := by simp
          have hheadPre : pre.head? = some first := by
            simpa only [List.head?_append_of_ne_nil pre hpreNe] using hhead
          have hlastPost : (d :: ds).getLast? = some last := by
            rw [List.getLast?_append_of_ne_nil pre hpostNe] at hlast
            exact hlast
          have hdecomp := (hdChunkListChain_append pre (d :: ds)).mp hchain
          have hchainPost := hdecomp.2.1
          have hjoin := hdecomp.2.2
          have hboundPre : ∀ c ∈ pre, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius := by
            intro c hc
            exact hbound c (List.mem_append_left (d :: ds) hc)
          have hboundPost : ∀ c ∈ d :: ds, hdScaleDistance p.D c.1 c.2.1 ≤ childRadius := by
            intro c hc
            exact hbound c (List.mem_append_right pre hc)
          have htailBound := ih hchainPost hboundPost d last (by simp) hlastPost
          rcases hfirst with ⟨firstPre, hfirstPre, hfirstNear⟩
          rcases hlastNear with ⟨lastPre, hlastPre, hlastPreNear⟩
          have hfirstEq : first = firstPre := by simpa [hheadPre] using hfirstPre
          subst first
          have hbridge : lastPre.2.1 = d.1 := hjoin lastPre d hlastPre (by simp)
          have hskipBound := hdChunkSkipPrefix_distance_upper hD
            ⟨firstPre, hfirstPre, hfirstNear⟩ ⟨lastPre, hlastPre, hlastPreNear⟩
            hboundPre firstPre lastPre hfirstPre hlastPre
          calc
            hdScaleDistance p.D firstPre.1 last.2.1 ≤
                hdScaleDistance p.D firstPre.1 lastPre.2.1 +
                  hdScaleDistance p.D lastPre.2.1 last.2.1 :=
                    hdScaleDistance_triangle hD firstPre.1 lastPre.2.1 last.2.1
            _ ≤ (2 * gap + childRadius) + hdChunkCoverBudget gap blocks :=
                  Nat.add_le_add hskipBound (by simpa [hbridge] using htailBound)
            _ = hdChunkCoverBudget gap (HDChunkSkipBlock.skipped x pre :: blocks) := by
                  simp [hdChunkCoverBudget, hdChunkClearCount, hdChunkSkipCount, Nat.add_mul,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem hdThresholdChunking_parent_span_bound {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin : HDState p} {parentRadius childRadius gap : ℕ} {η : ℝ}
    {centers : Finset (HDState p)}
    {start finish : HDState p}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (HDChunk p Sites bad childRadius)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix)
    {blocks : List (HDChunkSkipBlock (Sites := Sites) (bad := bad)
      (childRadius := childRadius))}
    (hpart : HDChunkCoverPartition gap η centers chunks blocks)
    {first last : HDChunk p Sites bad childRadius}
    (hhead : chunks.head? = some first) (hlast : chunks.getLast? = some last) :
    hdScaleDistance p.D start finish ≤ hdChunkCoverBudget gap blocks + childRadius := by
  have hspan := hdChunkCoverPartition_span_bound hD hpart
    (hdThresholdChunking_chain hchunk)
    (hdThresholdChunking_chunk_displacement_bound hD hchunk)
    first last hhead hlast
  have hstart := hdThresholdChunking_headStart hchunk first hhead
  have hfinish := hdThresholdChunking_lastFinish_eq hchunk hlast
  have hspan' : hdScaleDistance p.D start suffix.1 ≤ hdChunkCoverBudget gap blocks := by
    simpa [hstart, hfinish] using hspan
  have hsuffix := hdThresholdChunking_suffix_inside hchunk
  calc
    hdScaleDistance p.D start finish ≤
        hdScaleDistance p.D start suffix.1 + hdScaleDistance p.D suffix.1 finish :=
          hdScaleDistance_triangle hD start suffix.1 finish
    _ ≤ hdChunkCoverBudget gap blocks + childRadius :=
          Nat.add_le_add hspan' hsuffix.le

private theorem hdChunkCoverPartition_skipCount_le {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius gap : ℕ} {η : ℝ}
    {centers : Finset (HDState p)}
    {chunks : List (HDChunk p Sites bad childRadius)} {blocks}
    (hpart : HDChunkCoverPartition gap η centers chunks blocks) :
    hdChunkSkipCount blocks ≤ centers.card := by
  induction hpart with
  | nil => simp [hdChunkSkipCount]
  | clear hfar hgood htail ih => simpa [hdChunkSkipCount] using ih
  | @skip centers x pre post blocks hx hfirst hlast hfar htail ih =>
      change hdChunkSkipCount blocks + 1 ≤ centers.card
      have hstep := Nat.add_le_add_right ih 1
      rw [Finset.card_erase_add_one hx] at hstep
      exact hstep

/-- A maximal-cover skip decomposition: failed child starts covered by a finite family
are skipped to the last visit of one center, while every unskipped chunk is a success. -/
private theorem hdChunkCoverPartition_exists {p : HDParams} {Sites : p.Sites}
    {bad : CubeVertex p.d → ℕ → Prop} {childRadius gap : ℕ} {η : ℝ}
    (centers : Finset (HDState p))
    (chunks : List (HDChunk p Sites bad childRadius))
    (hcover : ∀ c ∈ chunks, hdThresholdChunkFailure η c →
      ∃ x ∈ centers, hdScaleDistance p.D c.1 x < gap) :
    ∃ blocks, HDChunkCoverPartition gap η centers chunks blocks := by
  classical
  have hmain : ∀ n : ℕ, ∀ xs : List (HDChunk p Sites bad childRadius),
      xs.length = n → ∀ S : Finset (HDState p),
      (∀ c ∈ xs, hdThresholdChunkFailure η c →
        ∃ x ∈ S, hdScaleDistance p.D c.1 x < gap) →
      ∃ blocks, HDChunkCoverPartition gap η S xs blocks := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs hlen S hcoverXs
        cases xs with
        | nil => exact ⟨[], HDChunkCoverPartition.nil S⟩
        | cons c cs =>
            have hcs : cs.length < n := by simp at hlen; omega
            by_cases hclose : ∃ x ∈ S, hdScaleDistance p.D c.1 x < gap
            · obtain ⟨x, hx, hnear⟩ := hclose
              cases hsplit : hdLastNearSplit gap x (c :: cs) with
              | none =>
                  have hfar := (hdLastNearSplit_none_iff gap x (c :: cs)).mp hsplit
                  exact False.elim (Nat.not_le_of_gt hnear (hfar c (by simp)))
              | some pair =>
                  rcases pair with ⟨pre, post⟩
                  have hspec := hdLastNearSplit_spec gap x (c :: cs) hsplit
                  obtain ⟨hcat, hne, hlast, hpostFar⟩ := hspec
                  have hfirst : ∃ d, pre.head? = some d ∧
                      hdScaleDistance p.D d.1 x < gap := by
                    cases pre with
                    | nil => exact False.elim (hne rfl)
                    | cons d ds =>
                        have hEq : c :: cs = d :: (ds ++ post) := by simpa [hcat]
                        injection hEq with hcd htailEq
                        subst d
                        exact ⟨c, by simp, hnear⟩
                  have hpostLen : post.length < n := by
                    have hpreLen : 0 < pre.length := by
                      cases pre with
                      | nil => exact False.elim (hne rfl)
                      | cons _ _ => simp
                    have hlen' : (c :: cs).length = pre.length + post.length := by
                      rw [hcat, List.length_append]
                    simp only [List.length_cons] at hlen
                    simp only [List.length_cons] at hlen'
                    omega
                  have hpostCover : ∀ a ∈ post, hdThresholdChunkFailure η a →
                      ∃ y ∈ S.erase x, hdScaleDistance p.D a.1 y < gap := by
                    intro a ha hfail
                    have ha' : a ∈ c :: cs := by rw [hcat]; exact List.mem_append.mpr (Or.inr ha)
                    obtain ⟨y, hy, hnearY⟩ := hcoverXs a ha' hfail
                    by_cases hyx : y = x
                    · subst y
                      exact False.elim (Nat.not_le_of_gt hnearY (hpostFar a ha))
                    · exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩, hnearY⟩
                  obtain ⟨blocks, htail⟩ := ih post.length hpostLen post rfl
                    (S.erase x) hpostCover
                  refine ⟨HDChunkSkipBlock.skipped x pre :: blocks, ?_⟩
                  rw [hcat]
                  exact HDChunkCoverPartition.skip hx hfirst hlast hpostFar htail
            · have hfar : ∀ x ∈ S, gap ≤ hdScaleDistance p.D c.1 x := by
                intro x hx
                by_contra hn
                exact hclose ⟨x, hx, Nat.lt_of_not_ge hn⟩
              have hgood : ¬ hdThresholdChunkFailure η c := by
                intro hf
                obtain ⟨x, hx, hnear⟩ := hcoverXs c (by simp) hf
                exact Nat.not_le_of_gt hnear (hfar x hx)
              have hcsCover : ∀ a ∈ cs, hdThresholdChunkFailure η a →
                  ∃ x ∈ S, hdScaleDistance p.D a.1 x < gap := by
                intro a ha hfail
                exact hcoverXs a (by simp [ha]) hfail
              obtain ⟨blocks, htail⟩ := ih cs.length hcs cs rfl S hcsCover
              exact ⟨HDChunkSkipBlock.clear c :: blocks,
                HDChunkCoverPartition.clear hfar hgood htail⟩
  exact hmain chunks.length chunks rfl centers hcover

private theorem hdChunkCoverPartition_rise_upper {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {childRadius gap : ℕ} {η : ℝ} {centers : Finset (HDState p)}
    {chunks : List (HDChunk p Sites bad childRadius)} {blocks}
    (hpart : HDChunkCoverPartition gap η centers chunks blocks)
    (hchain : hdChunkListChain chunks)
    (hbound : ∀ c ∈ chunks, hdThresholdChunkRise c ≤ (childRadius : ℝ)) :
    hdThresholdChunkRiseSum chunks ≤
      -(η * (hdChunkClearCount blocks : ℝ) * childRadius) +
        (2 * (gap : ℝ) + childRadius) * (hdChunkSkipCount blocks : ℝ) := by
  induction hpart with
  | nil centers => simp [hdThresholdChunkRiseSum, hdChunkClearCount, hdChunkSkipCount]
  | @clear centers c rest blocks hfar hgood htail ih =>
      have hchainTail := hdChunkListChain_tail hchain
      have hboundTail : ∀ a ∈ rest, hdThresholdChunkRise a ≤ (childRadius : ℝ) := by
        intro a ha
        exact hbound a (by simp [ha])
      have htailBound := ih hchainTail hboundTail
      have hcBound := hbound c (by simp)
      have hgoodRise : hdThresholdChunkRise c ≤ -(η * (childRadius : ℝ)) := by
        unfold hdThresholdChunkFailure at hgood
        exact le_of_lt (lt_of_not_ge hgood)
      have hsum : hdThresholdChunkRiseSum (c :: rest) =
          hdThresholdChunkRise c + hdThresholdChunkRiseSum rest := by
        simp [hdThresholdChunkRiseSum]
      simp only [hdChunkClearCount, hdChunkSkipCount]
      rw [hsum]
      push_cast
      nlinarith [htailBound, hgoodRise]
  | @skip centers x pre post blocks hx hfirst hlast hfar htail ih =>
      have hdecomp := (hdChunkListChain_append pre post).mp hchain
      have hchainPre := hdecomp.1
      have hchainPost := hdecomp.2.1
      have hboundPre : ∀ c ∈ pre, hdThresholdChunkRise c ≤ (childRadius : ℝ) := by
        intro c hc
        exact hbound c (List.mem_append_left post hc)
      have hboundPost : ∀ c ∈ post, hdThresholdChunkRise c ≤ (childRadius : ℝ) := by
        intro c hc
        exact hbound c (List.mem_append_right pre hc)
      have hskipRise := hdChunkSkipPrefix_rise_upper hD hchainPre hfirst hlast hboundPre
      have htailBound := ih hchainPost hboundPost
      rw [hdThresholdChunkRiseSum_append]
      simp [hdChunkClearCount, hdChunkSkipCount]
      push_cast
      nlinarith [hskipRise, htailBound]

private theorem hdChunkCoverPartition_parent_failure_false {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin start finish : HDState p} {parentRadius childRadius gap M K : ℕ}
    {ηParent ηChild δ : ℝ} {centers : Finset (HDState p)}
    {chunks : List (HDChunk p Sites bad childRadius)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    {blocks : List (HDChunkSkipBlock (Sites := Sites) (bad := bad)
      (childRadius := childRadius))}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix)
    (hpart : HDChunkCoverPartition gap ηChild centers chunks blocks)
    (hM : 2 ≤ M)
    (hR : 0 < childRadius)
    (hbudgetScale : 2 * gap + childRadius = K * childRadius)
    (hηParent : 0 ≤ ηParent) (hηChild : 0 ≤ ηChild)
    (hηgap : ηParent < ηChild)
    (hlarge : (1 + ηChild) * (K : ℝ) * δ * (M : ℝ) + (1 + ηChild) <
      (ηChild - ηParent) * (M : ℝ))
    (hsmall : (centers.card : ℝ) < δ * (M : ℝ))
    (hboundary : M * childRadius ≤ hdScaleDistance p.D start finish)
    (hparentNet : -(ηParent * ((M * childRadius : ℕ) : ℝ)) ≤
      (finish.2 : ℝ) - start.2) : False := by
  have hchunksNe : chunks ≠ [] := by
    intro hnil
    have hdisp := hdThresholdChunking_displacement_bound hD hchunk
    have hdisp' : hdScaleDistance p.D start finish ≤ childRadius := by
      simpa [hnil] using hdisp
    have htwice : 2 * childRadius ≤ M * childRadius := Nat.mul_le_mul_right childRadius hM
    omega
  cases chunks with
  | nil => exact False.elim (hchunksNe rfl)
  | cons first rest =>
      have hhead : (first :: rest).head? = some first := by simp
      cases hlast : (first :: rest).getLast? with
      | none => simp at hlast
      | some last =>
          have hparentSpan := hdThresholdChunking_parent_span_bound hD hchunk hpart
            hhead hlast
          have hspanPieces : M * childRadius ≤
              hdChunkClearCount blocks * childRadius +
                hdChunkSkipCount blocks * (K * childRadius) + childRadius := by
            calc
              M * childRadius ≤ hdScaleDistance p.D start finish := hboundary
              _ ≤ hdChunkCoverBudget gap blocks + childRadius := hparentSpan
              _ = _ := by simp [hdChunkCoverBudget, hbudgetScale]
          have hRReal : 0 < (childRadius : ℝ) := by exact_mod_cast hR
          have hspanReal : (M : ℝ) * childRadius ≤
              (hdChunkClearCount blocks : ℝ) * childRadius +
                (hdChunkSkipCount blocks : ℝ) * ((K : ℝ) * childRadius) + childRadius := by
            exact_mod_cast hspanPieces
          have hspanFactored : (M : ℝ) * childRadius ≤
              ((hdChunkClearCount blocks : ℝ) +
                (K : ℝ) * (hdChunkSkipCount blocks : ℝ) + 1) * childRadius := by
            calc
              _ ≤ _ := hspanReal
              _ = _ := by ring
          have hclear : (M : ℝ) ≤ (hdChunkClearCount blocks : ℝ) +
              (K : ℝ) * (hdChunkSkipCount blocks : ℝ) + 1 :=
            le_of_mul_le_mul_right hspanFactored hRReal
          have hpartRise := hdChunkCoverPartition_rise_upper hD hpart
            (hdThresholdChunking_chain hchunk)
            (hdThresholdChunking_chunk_rise_upper hD hchunk)
          have hnetDecomp := hdThresholdChunking_net_decomposition hchunk
          have hsuffixRise := hdThresholdChunking_suffix_rise_upper hchunk
          have hbudgetScaleReal : ((2 * gap + childRadius : ℕ) : ℝ) =
              (K : ℝ) * childRadius := by exact_mod_cast hbudgetScale
          have hpartRiseCast : hdThresholdChunkRiseSum (first :: rest) ≤
              -(ηChild * (hdChunkClearCount blocks : ℝ) * childRadius) +
                ((2 * gap + childRadius : ℕ) : ℝ) *
                  (hdChunkSkipCount blocks : ℝ) := by
            calc
              _ ≤ _ := hpartRise
              _ = _ := by push_cast; ring
          have hnetUpper : (finish.2 : ℝ) - start.2 ≤
              (-(ηChild * (hdChunkClearCount blocks : ℝ)) +
                (K : ℝ) * (hdChunkSkipCount blocks : ℝ) + 1) * childRadius := by
            rw [hnetDecomp]
            calc
              hdThresholdChunkRiseSum (first :: rest) +
                  ((finish.2 : ℝ) - suffix.1.2) ≤
                  -(ηChild * (hdChunkClearCount blocks : ℝ) * childRadius) +
                    ((2 * gap + childRadius : ℕ) : ℝ) *
                      (hdChunkSkipCount blocks : ℝ) + childRadius :=
                add_le_add hpartRiseCast hsuffixRise
              _ = _ := by rw [hbudgetScaleReal]; ring
          have hparentNetReal : (-(ηParent * (M : ℝ))) * childRadius ≤
              (finish.2 : ℝ) - start.2 := by
            have h : -(ηParent * ((M : ℝ) * childRadius)) ≤
                (finish.2 : ℝ) - start.2 := by
              simpa only [Nat.cast_mul] using hparentNet
            calc
              (-(ηParent * (M : ℝ))) * childRadius =
                  -(ηParent * ((M : ℝ) * childRadius)) := by ring
              _ ≤ _ := h
          have hnetCompare : (-(ηParent * (M : ℝ))) * childRadius ≤
              (-(ηChild * (hdChunkClearCount blocks : ℝ)) +
                (K : ℝ) * (hdChunkSkipCount blocks : ℝ) + 1) * childRadius :=
            le_trans hparentNetReal hnetUpper
          have hnetDiv : -(ηParent * (M : ℝ)) ≤
              -(ηChild * (hdChunkClearCount blocks : ℝ)) +
                (K : ℝ) * (hdChunkSkipCount blocks : ℝ) + 1 :=
            le_of_mul_le_mul_right hnetCompare hRReal
          have hclearLower : (M : ℝ) -
              (K : ℝ) * (hdChunkSkipCount blocks : ℝ) - 1 ≤
                (hdChunkClearCount blocks : ℝ) := by linarith [hclear]
          have hnegEta : -ηChild ≤ 0 := neg_nonpos.mpr hηChild
          have hnegative : -(ηChild * (hdChunkClearCount blocks : ℝ)) ≤
              -(ηChild * ((M : ℝ) - (K : ℝ) *
                (hdChunkSkipCount blocks : ℝ) - 1)) :=
            by
              convert mul_le_mul_of_nonpos_left hclearLower hnegEta using 1 <;> ring
          have hgapIneq : (ηChild - ηParent) * (M : ℝ) ≤
              (1 + ηChild) * (K : ℝ) * (hdChunkSkipCount blocks : ℝ) +
                (1 + ηChild) := by
            nlinarith [hnetDiv, hnegative]
          have hskipCount : hdChunkSkipCount blocks ≤ centers.card :=
            hdChunkCoverPartition_skipCount_le hpart
          have hskipLeReal : (hdChunkSkipCount blocks : ℝ) ≤ (centers.card : ℝ) := by
            exact_mod_cast hskipCount
          have hskipReal : (hdChunkSkipCount blocks : ℝ) < δ * (M : ℝ) := by
            exact lt_of_le_of_lt hskipLeReal hsmall
          have hK : 0 < K := by
            by_contra hnot
            have hzero : K = 0 := by omega
            rw [hzero] at hbudgetScale
            omega
          have hcoeff : 0 < (1 + ηChild) * (K : ℝ) :=
            mul_pos (by linarith [hηChild]) (by exact_mod_cast hK)
          have hskipCoeff := mul_lt_mul_of_pos_left hskipReal hcoeff
          have hupperGap : (1 + ηChild) * (K : ℝ) *
                (hdChunkSkipCount blocks : ℝ) + (1 + ηChild) <
              (ηChild - ηParent) * (M : ℝ) := by
            calc
              _ < (1 + ηChild) * (K : ℝ) * (δ * (M : ℝ)) + (1 + ηChild) :=
                by simpa [add_comm] using add_lt_add_right hskipCoeff (1 + ηChild)
              _ = (1 + ηChild) * (K : ℝ) * δ * (M : ℝ) + (1 + ηChild) := by ring
              _ < _ := hlarge
          exact (not_lt_of_ge hgapIneq hupperGap)

private theorem hdParentFailure_has_many_separated_child_failure_starts
    {p : HDParams} (hD : 0 < p.D)
    {Sites : p.Sites} {bad : CubeVertex p.d → ℕ → Prop}
    {parentOrigin start finish : HDState p} {parentRadius childRadius gap M K : ℕ}
    {ηParent ηChild δ : ℝ}
    {walk : HDThresholdWalk Sites bad parentOrigin parentRadius start finish}
    {chunks : List (HDChunk p Sites bad childRadius)}
    {suffix : Σ suffixStart : HDState p,
      HDThresholdWalk Sites bad parentOrigin parentRadius suffixStart finish}
    (hchunk : HDThresholdChunking Sites bad parentOrigin parentRadius childRadius walk
      chunks suffix)
    (hM : 2 ≤ M) (hR : 0 < childRadius) (hgap : 0 < gap)
    (hbudgetScale : 2 * gap + childRadius = K * childRadius)
    (hηParent : 0 ≤ ηParent) (hηChild : 0 ≤ ηChild)
    (hηgap : ηParent < ηChild)
    (hlarge : (1 + ηChild) * (K : ℝ) * δ * (M : ℝ) + (1 + ηChild) <
      (ηChild - ηParent) * (M : ℝ))
    (hboundary : M * childRadius ≤ hdScaleDistance p.D start finish)
    (hparentNet : -(ηParent * ((M * childRadius : ℕ) : ℝ)) ≤
      (finish.2 : ℝ) - start.2) :
    ∃ S : Finset (HDState p), S ⊆ hdFailureStartSet ηChild chunks ∧
      hdScaleSeparated gap S ∧ δ * (M : ℝ) ≤ (S.card : ℝ) := by
  classical
  let T := hdFailureStartSet ηChild chunks
  obtain ⟨S, hSsubset, hSsep, hcover⟩ :=
    exists_maximal_hdScaleSeparated T gap hgap hD
  refine ⟨S, hSsubset, hSsep, ?_⟩
  by_contra hsmall
  have hsmall' : (S.card : ℝ) < δ * (M : ℝ) := lt_of_not_ge hsmall
  have hcoverFailures : ∀ c ∈ chunks, hdThresholdChunkFailure ηChild c →
      ∃ y ∈ S, hdScaleDistance p.D c.1 y < gap := by
    intro c hc hf
    obtain ⟨y, hy, hnear⟩ := hcover c.1 (by simpa [T] using hdFailureStartSet_mem hc hf)
    exact ⟨y, hy, hnear⟩
  obtain ⟨blocks, hpart⟩ := hdChunkCoverPartition_exists S chunks hcoverFailures
  exact hdChunkCoverPartition_parent_failure_false hD hchunk hpart hM hR hbudgetScale
    hηParent hηChild hηgap hlarge hsmall' hboundary hparentNet

/-- Any relaxed stopped-path failure contains a bad site-level inside its ball. -/
theorem hdScaleThresholdFailure_has_local_bad {p : HDParams} (Sites : p.Sites)
    (bad : CubeVertex p.d → ℕ → Prop) (start : HDState p) (R : ℕ) (η : ℝ)
    (hD : 0 < p.D) (hR : 0 < R) (hη : η < 1)
    (hfail : hdScaleThresholdFailure Sites bad start R η) :
    ∃ v j, v ∈ Sites ∧ bad v j ∧ hdScaleDistance p.D start (v, j) < R := by
  rcases hfail with ⟨finish, hwalkNonempty, hnet⟩
  let hwalk := Classical.choice hwalkNonempty
  rcases hdThresholdWalk_up_or_down Sites bad start R hwalk with hUp | ⟨hlev, hspace⟩
  · exact hUp
  · let q : ℕ := start.2 - finish.2
    have hmetric : hdScaleDistance p.D start finish ≤ q := by
      apply Nat.max_le.mpr
      constructor
      · simpa [q] using (Nat.dist_eq_sub_of_le_right hlev).le
      · have hnum : _root_.hammingDist start.1 finish.1 + p.D - 1 < p.D * (q + 1) := by
          rw [Nat.mul_succ]
          dsimp [q]
          omega
        have hnum' : _root_.hammingDist start.1 finish.1 + p.D - 1 < (q + 1) * p.D := by
          simpa [Nat.mul_comm] using hnum
        have hdiv := (Nat.div_lt_iff_lt_mul hD).2 hnum'
        have hdiv' :
            (_root_.hammingDist start.1 finish.1 + p.D - 1) / p.D < q + 1 := hdiv
        have hceil :
            (_root_.hammingDist start.1 finish.1 + p.D - 1) / p.D ≤ q :=
          Nat.lt_succ_iff.mp hdiv'
        simpa [hdScaleDistance, max_eq_right (Nat.one_le_iff_ne_zero.mpr hD.ne')] using hceil
    have hRfinish := hdThresholdWalk_finish_outside Sites bad start R hwalk
    have hRq : R ≤ q := le_trans hRfinish hmetric
    have hnet' : (q : ℝ) ≤ η * (R : ℝ) := by
      have hcast : (finish.2 : ℝ) - start.2 = -(q : ℝ) := by
        simp [q, Nat.cast_sub hlev]
      nlinarith [hnet, hcast]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hηR : η * (R : ℝ) < R := by nlinarith [hη, hRreal]
    have hRqReal : (R : ℝ) ≤ q := by exact_mod_cast hRq
    linarith [hnet', hηR, hRqReal]

/-- An actually bad site is bad at any relaxed threshold no larger than the
actual crowd threshold, provided eligibility is legally large enough. -/
private theorem hdScaleThresholdBad_of_actual {p : HDParams}
    (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d)
    (j : Fin (p.H + 1)) (s t : ℝ)
    (ht : t ≤ 1) (hn : 0 < p.n)
    (hbad : p.Bad P A E v j) : hdScaleThresholdBad P A E v j s t := by
  rcases hbad with hhole | hcrowd
  · exact Or.inl hhole
  · right
    have hnPow : 0 < (p.n : ℝ) ^ p.b := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have htPow : t * (p.n : ℝ) ^ p.b ≤ (p.n : ℝ) ^ p.b :=
      mul_le_of_le_one_left hnPow.le ht
    exact lt_of_le_of_lt htPow hcrowd

/-- A concrete `HDScaleWalk` can be read as a walk with relaxed threshold
badness whenever its eligibility assignment is legal on the queried domain. -/
private noncomputable def hdThresholdWalk_of_hdScaleWalk {p : HDParams}
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (s t : ℝ) (hlegal : hdScaleLegal P E Sites s)
    (hs : s ≤ 1 / 3) (ht : t ≤ 1) (hn : 0 < p.n) (hb : 0 < p.b)
    {origin start finish : HDState p} {R : ℕ}
    (hwalk : HDScaleWalk Sites P A E origin R start finish) :
    HDThresholdWalk Sites
      (fun v k => hdScaleThresholdBadN P A E v k s t) origin R start finish := by
  induction hwalk with
  | stop hboundary => exact HDThresholdWalk.stop hboundary
  | @up v j finish hinside hv hj hbad tail ih =>
      apply HDThresholdWalk.up hinside hv hj ?_ ih
      rcases hbad with ⟨hjFin, hbad⟩
      exact ⟨hjFin, hdScaleThresholdBad_of_actual P A E v ⟨j, hjFin⟩ s t
        ht hn hbad⟩
  | @down v v' j finish hinside hv' hj hstep tail ih =>
      exact HDThresholdWalk.down hinside hv' hj hstep ih

/-- The concrete stopped-path failure event is contained in the relaxed-scale
failure event on every legally sized configuration. -/
private theorem hdScaleFailure_le_relaxed {p : HDParams}
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (s t : ℝ) (hlegal : hdScaleLegal P E Sites s)
    (hs : s ≤ 1 / 3) (ht : t ≤ 1) (hn : 0 < p.n) (hb : 0 < p.b)
    (start : HDState p) (R : ℕ) (η : ℝ)
    (hfail : hdScaleFailure Sites P A E start R η) :
    hdScaleThresholdFailure Sites
      (fun v k => hdScaleThresholdBadN P A E v k s t) start R η := by
  rcases hfail with ⟨finish, hwalkNonempty, hnet⟩
  rcases hwalkNonempty with ⟨hwalk⟩
  exact ⟨finish, ⟨hdThresholdWalk_of_hdScaleWalk Sites P A E s t hlegal
    hs ht hn hb hwalk⟩, hnet⟩

/-- The relaxed scale-zero stopped-path estimate used to start L3.8's induction. -/
theorem height_scale_zero_relaxed_failure_bound
    (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ((1 : ℝ) / 4) ∧
            hdScaleThresholdFailure Sites
              (fun u k => hdScaleThresholdBadN ω.1.1 ω.2
                (Esel ω.1.1 ω.1.2) u k ((1 : ℝ) / 4)
                (hdScaleCrowdFraction (hdScaleIndex p.n σ ζ) 0))
              (v, 0) (heightBaseRadius p.n) ((1 : ℝ) / 2)) ≤
          Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) := by
  classical
  rcases hp.hsz with ⟨hσpos, hσζ, hζone, hθpos, hθone⟩
  rcases hp.hb with ⟨hb₀pos, hb₀b, hbone⟩
  have hJgap : 1 < J₀ - b₀ := by linarith [hp.hJ, hb₀b, hbone]
  obtain ⟨nGeom, hGeomAll⟩ := height_local_geometry_eventually
    J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nVol, hVolAll⟩ := height_volume_ge_lambda_eventually
    J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nDim, hDimAll⟩ := heightBaseRadius_times_D_le_dimension_eventually
    D c_d hp.hD hp.hd.1
  have hCdpos : 0 < C_d := lt_of_lt_of_le hp.hd.1 hp.hd.2
  obtain ⟨nCount, hCountAll⟩ := hdScaleBallSiteLevels_exp_bound D C_d (b₀ / 2)
    hp.hD hCdpos (by linarith [hb₀pos])
  obtain ⟨nRad, hRadAll⟩ := heightBaseRadius_le_logsq
  have hζpos : 0 < ζ := lt_trans hσpos hσζ
  have honeθ : 0 < 1 - θ := sub_pos.mpr hθone
  have hsumPos : 0 < ζ + σ + (1 - θ) := by positivity
  have haPos : 0 < a := lt_trans hsumPos hp.ha.1
  obtain ⟨nArith, hArithAll⟩ := height_base_exp_arithmetic a b₀ θ haPos hp.ha.2.1
    ⟨hθpos, hθone⟩
  let N1 := max nGeom nVol
  let N2 := max nDim nCount
  let N3 := max nRad nArith
  let Ntail := max N2 N3
  let Nall := max 30 (max 2 (max N1 Ntail))
  refine ⟨Nall, ?_⟩
  intro p hD hH hlam hb₀' hb' hn hdLo hdHi hreg Sites v hv Aux inst πAux Esel
  have hn30 : 30 ≤ p.n := le_trans (Nat.le_max_left 30 _) hn
  have hnCore : max 2 (max N1 Ntail) ≤ p.n := le_trans (Nat.le_max_right 30 _) hn
  have hN1Tail : max N1 Ntail ≤ p.n := le_trans (Nat.le_max_right 2 _) hnCore
  have hN1 : N1 ≤ p.n := le_trans (Nat.le_max_left N1 _) hN1Tail
  have hNtail : Ntail ≤ p.n := le_trans (Nat.le_max_right N1 _) hN1Tail
  have hN2 : N2 ≤ p.n := le_trans (Nat.le_max_left N2 N3) hNtail
  have hN3 : N3 ≤ p.n := le_trans (Nat.le_max_right N2 N3) hNtail
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left 2 _) hnCore
  have hnGeom : nGeom ≤ p.n := le_trans (Nat.le_max_left nGeom nVol) hN1
  have hnVol : nVol ≤ p.n := le_trans (Nat.le_max_right nGeom nVol) hN1
  have hnDim : nDim ≤ p.n := le_trans (Nat.le_max_left nDim nCount) hN2
  have hnCount : nCount ≤ p.n := le_trans (Nat.le_max_right nDim nCount) hN2
  have hnRad : nRad ≤ p.n := le_trans (Nat.le_max_left nRad nArith) hN3
  have hnArith : nArith ≤ p.n := le_trans (Nat.le_max_right nRad nArith) hN3
  have hGeom := hGeomAll p hD hb₀' hb' hnGeom hdLo hdHi hreg
  have hVol := hVolAll p hD hlam hnVol hdLo hreg
  have hR0 : (heightBaseRadius p.n : ℝ) ≤ 2 * (Real.log (p.n : ℝ)) ^ 2 :=
    hRadAll p.n hnRad
  have hRadiusBase := hDimAll p.n p.d hnDim hdLo
  have hRadius : p.D * heightBaseRadius p.n ≤ p.d := by rw [hD]; exact hRadiusBase
  have hRpos : 0 < heightBaseRadius p.n :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hLamPos : 0 < p.lam := by
    rw [hlam]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p.n)) _
  have hVpos : 0 < (p.V : ℝ) := lt_of_lt_of_le hLamPos hVol
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  have hLamLower : (p.n : ℝ) ^ b₀ ≤ p.lam := by
    rw [hlam]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hJgap])
  have hpowGap : (p.n : ℝ) ≤ (p.n : ℝ) ^ (J₀ - b₀) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 : ℝ) ≤ J₀ - b₀ by linarith [hJgap])
    simpa only [Real.rpow_one] using h
  have hpowEq : (p.n : ℝ) ^ J₀ =
      (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (J₀ - b₀) := by
    calc
      _ = (p.n : ℝ) ^ (b₀ + (J₀ - b₀)) := by congr 1 <;> ring
      _ = _ := Real.rpow_add hnpos _ _
  have hLamFactor : 30 * (p.n : ℝ) ^ b₀ ≤ p.lam := by
    rw [hlam, hpowEq]
    calc
      30 * (p.n : ℝ) ^ b₀ ≤ (p.n : ℝ) * (p.n : ℝ) ^ b₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn30) (Real.rpow_nonneg hnpos.le _)
      _ = (p.n : ℝ) ^ b₀ * (p.n : ℝ) := by ring
      _ ≤ (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (J₀ - b₀) :=
        mul_le_mul_of_nonneg_left hpowGap (Real.rpow_nonneg hnpos.le _)
  have hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam := by
    rw [hb₀']
    exact div_pos (Real.rpow_pos_of_pos hnpos _) hLamPos
  have hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 := by
    rw [hb₀', hlam]
    exact (div_le_one (Real.rpow_pos_of_pos hnpos _)).2
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hp.hJ, hb₀b, hbone]))
  have hqP0 : 0 < p.lam / (p.V : ℝ) := div_pos hLamPos hVpos
  have hqP1 : p.lam / (p.V : ℝ) ≤ 1 := by
    rw [div_le_one hVpos]
    exact_mod_cast hVol
  have hDpos : 0 < p.D := by rw [hD]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one hp.hD
  have hlogOne : 0 ≤ Real.log (p.n : ℝ) := by
    exact Real.log_nonneg hn1
  let hScale := hdScaleIndex p.n σ ζ
  let t : ℝ := hdScaleCrowdFraction hScale 0
  have hfrac := hdScaleThreshold_fractions_bounds
    (h := hScale) (i := 0) (Nat.zero_le _)
  have htLower : (11 : ℝ) / 20 ≤ t := by
    dsimp [t]
    linarith [hfrac.2.2.1]
  have htUpper : t ≤ (3 : ℝ) / 4 := by
    dsimp [t]
    exact hfrac.2.2.2.1
  have hLocal : ∀ u ∈ Sites, ∀ j : Fin (p.H + 1),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ((1 : ℝ) / 4) ∧
          hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) u j
            ((1 : ℝ) / 4) t) ≤ 4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
    intro u hu j
    have hVolBall := heightCrowdRegion_volume_bounds u j hGeom.1 hGeom.2.1
    have hproduct : (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) =
        (p.n : ℝ) ^ p.b₀ / (p.V : ℝ) := by
      field_simp [hLamPos.ne', hVpos.ne']
    have hregionLower : (p.n : ℝ) ^ p.b₀ ≤
        (heightCrowdRegion u j).card * (p.lam / (p.V : ℝ)) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) := by
      calc
        (p.n : ℝ) ^ p.b₀ = (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
          field_simp [hVpos.ne']
        _ ≤ (heightCrowdRegion u j).card * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) :=
          mul_le_mul_of_nonneg_right hVolBall.1
            (div_nonneg (Real.rpow_nonneg hnpos.le _) hVpos.le)
        _ = _ := by rw [← hproduct]; ring
    have hratio : (heightCrowdRegion u j).card / (p.V : ℝ) ≤
        1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D := by
      apply (div_le_iff₀ hVpos).2
      nlinarith [hVolBall.2]
    have hregionUpper : 4 * (heightCrowdRegion u j).card *
        (p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b := by
      calc
        _ = 4 * (heightCrowdRegion u j).card *
            ((p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by ring
        _ = 4 * (heightCrowdRegion u j).card * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
          rw [hproduct]
        _ = 4 * (p.n : ℝ) ^ p.b₀ *
            ((heightCrowdRegion u j).card / (p.V : ℝ)) := by
          field_simp [hVpos.ne']
        _ ≤ 4 * (p.n : ℝ) ^ p.b₀ *
            (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ ≤ (p.n : ℝ) ^ p.b := by simpa [hb₀', hb'] using hGeom.2.2
    have hμ : p.lam ≤ (heightCrowdRegion u j).card * (p.lam / (p.V : ℝ)) := by
      calc
        p.lam = (p.V : ℝ) * (p.lam / (p.V : ℝ)) := by field_simp [hVpos.ne']
        _ ≤ (heightCrowdRegion u j).card * (p.lam / (p.V : ℝ)) :=
          mul_le_mul_of_nonneg_right hVolBall.1 (div_nonneg hLamPos.le hVpos.le)
    have hpos1 : Real.exp (-((heightCrowdRegion u j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 8) ≤ Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hμ, hLamLower]
    have hpos2 : Real.exp (-((heightCrowdRegion u j).card : ℝ) *
        (p.lam / (p.V : ℝ)) / 210) ≤ Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
      apply Real.exp_le_exp.mpr
      have hμLarge : 30 * (p.n : ℝ) ^ b₀ ≤
          (heightCrowdRegion u j).card * (p.lam / (p.V : ℝ)) :=
        hLamFactor.trans (by
          calc
            p.lam = (p.V : ℝ) * (p.lam / (p.V : ℝ)) := by field_simp [hVpos.ne']
            _ ≤ (heightCrowdRegion u j).card * (p.lam / (p.V : ℝ)) :=
              mul_le_mul_of_nonneg_right hVolBall.1 (div_nonneg hLamPos.le hVpos.le))
      nlinarith [hμLarge]
    have hhole : Real.exp (-((1 : ℝ) / 4) * (p.n : ℝ) ^ p.b₀ / 2) ≤
        Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
      apply Real.exp_le_exp.mpr
      rw [hb₀']
      ring_nf
      exact le_rfl
    have hcrowd : Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) ≤
        Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by
      apply Real.exp_le_exp.mpr
      rw [hb₀']
      have hnonneg : 0 ≤ (p.n : ℝ) ^ b₀ := Real.rpow_nonneg hnpos.le _
      linarith [hnonneg]
    rw [← hb₀'] at hhole hcrowd
    have hsite := hdScale_bad_legal_position_average πAux Esel Sites u hu j
      ((1 : ℝ) / 4) t htLower htUpper hLamPos hqA0 hqA1 hqP0 hqP1
      hregionLower hregionUpper
    rw [← hb₀'] at hpos1 hpos2
    calc
      _ ≤ _ := hsite
      _ ≤ 4 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
        have hsum :
            (Real.exp (-((heightCrowdRegion u j).card : ℝ) *
                (p.lam / (p.V : ℝ)) / 8) +
              Real.exp (-((heightCrowdRegion u j).card : ℝ) *
                (p.lam / (p.V : ℝ)) / 210)) +
                (Real.exp (-((1 : ℝ) / 4) * (p.n : ℝ) ^ p.b₀ / 2) +
                  Real.exp (-((p.n : ℝ) ^ p.b₀) / 6)) ≤
              (Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) + Real.exp (-((p.n : ℝ) ^ p.b₀) / 8)) +
                (Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) + Real.exp (-((p.n : ℝ) ^ p.b₀) / 8)) := by
          exact add_le_add (add_le_add hpos1 hpos2) (add_le_add hhole hcrowd)
        calc
          _ =
              (Real.exp (-((heightCrowdRegion u j).card : ℝ) *
                  (p.lam / (p.V : ℝ)) / 8) +
                Real.exp (-((heightCrowdRegion u j).card : ℝ) *
                  (p.lam / (p.V : ℝ)) / 210)) +
                  (Real.exp (-((1 : ℝ) / 4) * (p.n : ℝ) ^ p.b₀ / 2) +
                    Real.exp (-((p.n : ℝ) ^ p.b₀) / 6)) := by ring
          _ ≤ _ := hsum
          _ = 4 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by ring
      _ = 4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8) := by rw [hb₀']
  let R₀ := heightBaseRadius p.n
  let T := hdScaleBallSiteLevels Sites (v, 0) R₀
  let s : ℝ := (1 : ℝ) / 4
  let δ : ℝ := 4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8)
  have hLocal' : ∀ u ∈ Sites, ∀ j : Fin (p.H + 1),
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
          hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) u j s t) ≤ δ := by
    intro u hu j
    simpa [s, t, δ] using hLocal u hu j
  have hT : ∀ x ∈ T, x.1 ∈ Sites := by
    intro x hx
    change x ∈ hdScaleBallSiteLevels Sites (v, 0) R₀ at hx
    exact (Finset.mem_filter.mp hx).2.1
  have hsubset : ∀ ω : ((p.Loc → Bool) × Aux) × (p.Loc → Bool),
      (hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
        hdScaleThresholdFailure Sites
          (fun u k => hdScaleThresholdBadN ω.1.1 ω.2
            (Esel ω.1.1 ω.1.2) u k s t) (v, 0) R₀ ((1 : ℝ) / 2)) →
      hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
        ∃ x ∈ T, hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 s t := by
    intro ω hω
    obtain ⟨u, k, hu, hbadN, hdist⟩ := hdScaleThresholdFailure_has_local_bad Sites
      (fun u k => hdScaleThresholdBadN ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) u k s t)
      (v, 0) R₀ ((1 : ℝ) / 2) hDpos hRpos (by norm_num) hω.2
    rcases hbadN with ⟨hk, hbad⟩
    let jFin : Fin (p.H + 1) := ⟨k, hk⟩
    have hdist' : hdScaleDistance p.D (v, 0) (u, jFin.val) < R₀ := by
      simpa [jFin] using hdist
    have hmem : (u, jFin) ∈ T := by
      simp [T, hdScaleBallSiteLevels, hu, hdist']
    exact ⟨hω.1, (u, jFin), hmem, hbad⟩
  have hunion := hdScale_bad_finite_union_bound πAux Esel Sites T s t δ hT hLocal'
  have hFailProb :
      ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
          hdScaleThresholdFailure Sites
            (fun u k => hdScaleThresholdBadN ω.1.1 ω.2
              (Esel ω.1.1 ω.1.2) u k s t) (v, 0) R₀ ((1 : ℝ) / 2)) ≤
        (T.card : ℝ) * δ := by
    calc
      _ ≤ ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          hdScaleLegal ω.1.1 (Esel ω.1.1 ω.1.2) Sites s ∧
            ∃ x ∈ T, hdScaleThresholdBad ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x.1 x.2 s t) :=
              finprob_pr_mono _ _ _ hsubset
      _ ≤ _ := hunion
  have hCount' := hCountAll Sites (v, 0) R₀ hnCount hD hdHi hR0 hRpos rfl hRadius
  have hArith' := hArithAll p.n hnArith
  calc
    _ ≤ (T.card : ℝ) * δ := hFailProb
    _ ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
        (4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by
      dsimp [δ]
      exact mul_le_mul_of_nonneg_right hCount' (by positivity)
    _ = 4 * Real.exp ((p.n : ℝ) ^ (b₀ / 2) - (p.n : ℝ) ^ b₀ / 8) := by
      calc
        _ = 4 * (Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
            Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by ring
        _ = 4 * Real.exp ((p.n : ℝ) ^ (b₀ / 2) +
            (-((p.n : ℝ) ^ b₀) / 8)) := by rw [← Real.exp_add]
        _ = _ := by congr 1 <;> ring
    _ ≤ Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) := hArith'

private theorem sup_id_mem_nat (s : Finset ℕ) (hne : s.Nonempty) : s.sup id ∈ s := by
  classical
  revert hne
  induction s using Finset.induction_on with
  | empty => intro hne; simp at hne
  | @insert a s ha ih =>
      intro hne
      by_cases hs : s.Nonempty
      · have hm := ih hs
        have hsup : (insert a s).sup id = max a (s.sup id) := by simp
        rw [hsup]
        by_cases h : a ≤ s.sup id
        · rw [max_eq_right h]
          exact Finset.mem_insert_of_mem hm
        · rw [max_eq_left (le_of_not_ge h)]
          exact Finset.mem_insert_self a s
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp

private theorem reach_level_le {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    {v : CubeVertex p.d} {j : ℕ}
    (h : p.Reach Sites P A E vq R v j) : j ≤ p.H := by
  induction h with
  | start => omega
  | up v j hj _ _ => omega
  | down v v' j _ _ _ ih => omega

private theorem height_reach_at_height {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    (hvq : vq ∈ Sites) :
    p.Reach Sites P A E vq R vq (p.height Sites P A E R vq) := by
  classical
  let s := (Finset.range (p.H + 1)).filter
    (fun j => p.Reach Sites P A E vq R vq j)
  have hzero : 0 ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    exact HDParams.Reach.start vq hvq (by simp)
  have hmem := sup_id_mem_nat s ⟨0, hzero⟩
  simpa [s, HDParams.height] using (Finset.mem_filter.mp hmem).2

theorem height_le_top {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (R : ℕ) : p.height Sites P A E R v ≤ p.H :=
  reach_level_le Sites P A E v R (height_reach_at_height Sites P A E v R hv)

private theorem height_reach_le {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    {j : ℕ}
    (h : p.Reach Sites P A E vq R vq j) : j ≤ p.height Sites P A E R vq := by
  classical
  unfold HDParams.height
  apply Finset.le_sup (f := id)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, h⟩
  have hj := reach_level_le Sites P A E vq R h
  omega

theorem height_eq_top_iff {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (R : ℕ) :
    p.height Sites P A E R v = p.H ↔ p.Reach Sites P A E v R v p.H := by
  constructor
  · intro h
    simpa [h] using height_reach_at_height Sites P A E v R hv
  · intro hreach
    apply le_antisymm (height_le_top Sites P A E v hv R)
    exact height_reach_le Sites P A E v R hreach

/-- If the maximum reachable level is below the top, it cannot be bad: an upward step
would contradict maximality. -/
theorem height_not_bad_at_max {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (R : ℕ) (hmax : p.height Sites P A E R v < p.H) :
    ¬ p.BadN P A E v (p.height Sites P A E R v) := by
  intro hbad
  rcases hbad with ⟨hlevel, hbad⟩
  have hre := height_reach_at_height Sites P A E v R hv
  have hbadN : p.BadN P A E v (p.height Sites P A E R v) := ⟨hlevel, hbad⟩
  have hup := HDParams.Reach.up v (p.height Sites P A E R v) hmax hre hbadN
  have hle := height_reach_le Sites P A E v R hup
  omega

/-- A downward horizontal step transfers reachability from level `j+1` at one site
to level `j` at a neighboring site, within the same consultation domain. -/
theorem height_neighbor_step {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (vq v v' : CubeVertex p.d) (R j : ℕ)
    (hv' : v' ∈ Sites) (hquery : _root_.hammingDist v' vq ≤ R)
    (hvv' : _root_.hammingDist v v' ≤ p.D)
    (hreach : p.Reach Sites P A E vq R v (j + 1)) :
    p.Reach Sites P A E vq R v' j :=
  HDParams.Reach.down v v' j hreach hv' hquery hvv'

/-- The bad-at-the-maximum clause in `GoodHeights` is automatic once all site heights
are below the top level. -/
theorem goodHeights_of_height_lt {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap)
    (hlow : ∀ v ∈ Sites, p.height Sites P A E p.Rlong v < p.H)
    (hlip : ∀ v ∈ Sites, ∀ v' ∈ Sites, _root_.hammingDist v v' ≤ p.D →
      |(p.height Sites P A E p.Rlong v : ℤ) - p.height Sites P A E p.Rlong v'| ≤ 1) :
    p.GoodHeights Sites P A E := by
  intro v hv
  exact ⟨hlow v hv, height_not_bad_at_max Sites P A E v hv p.Rlong (hlow v hv),
    fun v' hv' hdist => hlip v hv v' hv' hdist⟩

end Lane_p_height_main

end HypercubeRamsey
