import HypercubeRamsey.S12.ModerateMoment
import HypercubeRamsey.S12.CenteredMoment

/-!
# Section 12 homogeneous extension counts and peeling
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.5: the homogeneous support, clique exclusion, and peeling budget. -/
structure HomogeneousInput (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (k : ℕ) (c : Colour) (C0 : ℝ) where
  S : InterSetting T k (κ.xs / 4)
  π : Law (T.S.N k)
  homogeneous : ∀ l, S.π l = π
  Sp : Finset (Fin (T.S.N k))
  Sp_nonempty : Sp.Nonempty
  Sp_subset : Sp ⊆ T.X k
  τ_supported : S.τ.SupportedIn Sp
  π_supported : π.SupportedIn (T.Y k)
  degree_gate : ∀ x ∈ Sp, DegGate (T.S.E k) c π.w C0 (bstar T k) x
  degree_positive : ∀ x ∈ Sp, 0 < deg (T.S.E k) c π.w x
  Q : ℝ
  Q_large : Real.log
      (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ Q ∧ 1 ≤ Q
  noClique : NoClique (T.S.E k) c Sp π.w κ.θ Q
  gamma : ℝ
  gamma_eq : gamma = Real.exp (Cstar κ.u κ.ξ * Q) *
    Sp.sup' Sp_nonempty (fun x => S.τ.w x *
      Real.rpow (deg (T.S.E k) c π.w x) (-(S.d : ℝ)))
  gamma_nonneg : 0 ≤ gamma
  gamma_lt_one : gamma < 1

/-- L12.5(iii): the peeling bound for every valid homogeneous setting at the stage. -/
def HomogeneousPeelingClaim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (c : Colour) (C0 : ℝ) : Prop :=
  ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∑ I : Finset (Fin κ.u),
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if ¬ Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
           then prodW H.S.τ.w xs *
             posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) ≤
            4 ^ (κ.u + 1) * H.gamma

/-- L12.5(i): the number of exceptional one-label extensions is bounded by Ramsey. -/
theorem homogeneous_extension_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0,
        ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
          (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
          ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
            i₀ ∈ J ∧ 2 ≤ J.card ∧
              κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
              Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  sorry

/-- L12.5(ii): every label has few large-correlation partners in the support. -/
theorem homogeneous_conflict_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
        ((H.Sp.filter (fun z =>
          κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  sorry

/-- L12.5(iii): large-interaction tuples have bounded total positive-term mass. -/
theorem homogeneous_peeling (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0) :
    HomogeneousPeelingClaim κ hκ T c C0 := by
  sorry

/-- L12.5(iv): even-moment and peeling bounds give the homogeneous lower-tail estimate. -/
theorem homogeneous_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0)
    (hPeeling : HomogeneousPeelingClaim κ hκ T c C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∑ ys : Fin H.S.d → Fin (T.S.N k),
          if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
          then ∏ l, H.π.w (ys l) else 0) ≤
            (1 - t) ^ (-(κ.u : ℝ)) *
              ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
              4 ^ (κ.u + 1) * H.gamma) := by
  classical
  filter_upwards [hModerate, hPeeling] with k hModerateK hPeelingK
  intro H t ht0 ht1
  have hdegOK : H.S.DegOK c C0 := by
    intro l x hx
    have hxSp : x ∈ H.Sp := by
      by_contra hxSp
      have hzero := H.τ_supported x hxSp
      rw [hzero] at hx
      norm_num at hx
    have hgate := H.degree_gate x hxSp
    simpa [H.homogeneous l] using hgate
  obtain ⟨hmoderateSigned, hmoderatePositive⟩ := hModerateK H.S hdegOK
  have hpeel := hPeelingK H
  have hcenter := centered_moment_identity
    (N := T.S.N k) (d := H.S.d) (u := κ.u) H.S.τ.w H.S.τ.sum_eq_one
    (fun _ : Fin H.S.d => H.π.w) (fun _ => H.π.sum_eq_one)
    (fun _ x y => 1 + acoef (T.S.E k) c H.π.w x y)
  have hcenterEq :
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) *
          (Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys - 1) ^ κ.u) =
      ∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs := by
    simpa [Zmass, prodW, Phi, posTerm] using hcenter
  have hhitNonneg : ∀ x y, 0 ≤ hit (T.S.E k) c x y := by
    intro x y
    unfold hit
    split_ifs <;> norm_num
  have hdegreeNonneg : ∀ x, 0 ≤ deg (T.S.E k) c H.π.w x := by
    intro x
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (H.π.nonneg y) (hhitNonneg x y)
  have hfactorNonneg : ∀ x y, 0 ≤ 1 + acoef (T.S.E k) c H.π.w x y := by
    intro x y
    have hEq : 1 + acoef (T.S.E k) c H.π.w x y =
        hit (T.S.E k) c x y / deg (T.S.E k) c H.π.w x := by
      unfold acoef
      ring
    rw [hEq]
    exact div_nonneg (hhitNonneg x y) (hdegreeNonneg x)
  have hposTermNonneg : ∀ (I : Finset (Fin κ.u))
      (xs : Fin κ.u → Fin (T.S.N k)),
      0 ≤ posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
    intro I xs
    unfold posTerm
    apply Finset.prod_nonneg
    intro l hl
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (H.π.nonneg y)
    apply Finset.prod_nonneg
    intro i hi
    exact hfactorNonneg (xs i) y
  have hprodWNonneg : ∀ xs : Fin κ.u → Fin (T.S.N k),
      0 ≤ prodW H.S.τ.w xs := by
    intro xs
    unfold prodW
    apply Finset.prod_nonneg
    intro i hi
    exact H.S.τ.nonneg (xs i)
  have hPhiBound (xs : Fin κ.u → Fin (T.S.N k)) :
      |Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs| ≤
        ∑ I : Finset (Fin κ.u),
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
    unfold Phi
    calc
      |∑ I : Finset (Fin κ.u), (-1 : ℝ) ^ (κ.u - I.card) *
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs| ≤
        ∑ I : Finset (Fin κ.u),
          |(-1 : ℝ) ^ (κ.u - I.card) *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : Finset (Fin κ.u),
          posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [abs_mul, abs_of_nonneg (hposTermNonneg I xs)]
        simp
  let M2 (xs : Fin κ.u → Fin (T.S.N k)) :=
    Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) (2 * κ.ξ) xs
  let M1 (xs : Fin κ.u → Fin (T.S.N k)) :=
    Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
  let modSum := ∑ xs : Fin κ.u → Fin (T.S.N k),
    if M2 xs then prodW H.S.τ.w xs *
      Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0
  let tailSum := ∑ xs : Fin κ.u → Fin (T.S.N k),
    if ¬ M2 xs then prodW H.S.τ.w xs *
      Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0
  have htermNonneg (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)) :
      0 ≤ prodW H.S.τ.w xs *
        posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs :=
    mul_nonneg (hprodWNonneg xs) (hposTermNonneg I xs)
  have htupleAbs (xs : Fin κ.u → Fin (T.S.N k)) :
      |(if ¬ M2 xs then prodW H.S.τ.w xs *
          Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0)| ≤
        ∑ I : Finset (Fin κ.u),
          if ¬ M1 xs then prodW H.S.τ.w xs *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
    by_cases hM2 : M2 xs
    · by_cases hM1 : M1 xs
      · simp [hM2, hM1]
      · simp [hM2, hM1]
        apply Finset.sum_nonneg
        intro I hI
        exact htermNonneg xs I
    · have hnotM1 : ¬ M1 xs := by
        intro hM1
        apply hM2
        intro l J hJ
        exact le_trans (hM1 l J hJ) (by nlinarith [hκ.ξ_rng.1])
      rw [if_pos hM2]
      calc
        |prodW H.S.τ.w xs * Phi (T.S.E k) c
            (fun _ : Fin H.S.d => H.π.w) xs| =
          prodW H.S.τ.w xs *
            |Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs| := by
              rw [abs_mul, abs_of_nonneg (hprodWNonneg xs)]
        _ ≤ prodW H.S.τ.w xs *
            (∑ I : Finset (Fin κ.u),
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs) :=
          mul_le_mul_of_nonneg_left (hPhiBound xs) (hprodWNonneg xs)
        _ = ∑ I : Finset (Fin κ.u),
              prodW H.S.τ.w xs *
                posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs := by
          rw [Finset.mul_sum]
        _ = ∑ I : Finset (Fin κ.u),
              if ¬ M1 xs then prodW H.S.τ.w xs *
                posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
          simp [hnotM1]
  have hnonmodAbs : |tailSum| ≤ 4 ^ (κ.u + 1) * H.gamma := by
    calc
      |tailSum| ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          |if ¬ M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          ∑ I : Finset (Fin κ.u),
            if ¬ M1 xs then prodW H.S.τ.w xs *
              posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
        apply Finset.sum_le_sum
        intro xs hxs
        exact htupleAbs xs
      _ = ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ M1 xs then prodW H.S.τ.w xs *
            posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0 := by
        rw [Finset.sum_comm]
      _ ≤ 4 ^ (κ.u + 1) * H.gamma := by
        simpa [M1] using hpeel
  have hsplit :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c
          (fun _ : Fin H.S.d => H.π.w) xs) = modSum + tailSum := by
    calc
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
          ((if M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0) +
          (if ¬ M2 xs then prodW H.S.τ.w xs *
            Phi (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) xs else 0)) := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hM2 : M2 xs <;> simp [hM2]
      _ = modSum + tailSum := by
        simp [modSum, tailSum, Finset.sum_add_distrib]
  have htotalAbs :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        prodW H.S.τ.w xs * Phi (T.S.E k) c
          (fun _ : Fin H.S.d => H.π.w) xs| ≤
        (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
    rw [hsplit]
    calc
      |modSum + tailSum| ≤ |modSum| + |tailSum| := abs_add_le _ _
      _ ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
        exact add_le_add (by simpa [modSum, M2, H.homogeneous] using hmoderateSigned) hnonmodAbs
  have hmomentUpper :
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) *
          (Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys - 1) ^ κ.u) ≤
        (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
          4 ^ (κ.u + 1) * H.gamma := by
    rw [hcenterEq]
    exact le_trans (le_abs_self _) htotalAbs
  let z (ys : Fin H.S.d → Fin (T.S.N k)) :=
    Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys
  let badProb := ∑ ys : Fin H.S.d → Fin (T.S.N k),
    if z ys < t then ∏ l, H.π.w (ys l) else 0
  let wp : ℝ := (1 - t) ^ κ.u
  have hwp : 0 < wp := pow_pos (by linarith) _
  have hpiProdNonneg (ys : Fin H.S.d → Fin (T.S.N k)) :
      0 ≤ ∏ l, H.π.w (ys l) := by
    apply Finset.prod_nonneg
    intro l hl
    exact H.π.nonneg (ys l)
  have hEvenPowNonneg (ys : Fin H.S.d → Fin (T.S.N k)) :
      0 ≤ (z ys - 1) ^ κ.u := hκ.u_rng.1.pow_nonneg _
  have hval (ys : Fin H.S.d → Fin (T.S.N k)) (hz : z ys < t) :
      wp ≤ |z ys - 1| ^ κ.u := by
    have hbase : 1 - t ≤ |z ys - 1| := by
      have hZlt1 : z ys < 1 := lt_trans hz ht1
      have hneg : z ys - 1 < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    dsimp [wp]
    exact pow_le_pow_left₀ (by linarith [ht1]) hbase κ.u
  have hmomentLower : wp * badProb ≤
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        (∏ l, H.π.w (ys l)) * (z ys - 1) ^ κ.u) := by
    calc
      wp * badProb = ∑ ys : Fin H.S.d → Fin (T.S.N k),
          (if z ys < t then wp * ∏ l, H.π.w (ys l) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ys hys
        by_cases hz : z ys < t <;> simp [badProb, hz] <;> ring
      _ ≤ ∑ ys : Fin H.S.d → Fin (T.S.N k),
          (∏ l, H.π.w (ys l)) * (z ys - 1) ^ κ.u := by
        apply Finset.sum_le_sum
        intro ys hys
        by_cases hz : z ys < t
        · simp [hz]
          have hval' : wp ≤ (z ys - 1) ^ κ.u := by
            calc
              wp ≤ |z ys - 1| ^ κ.u := hval ys hz
              _ = (z ys - 1) ^ κ.u := hκ.u_rng.1.pow_abs _
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hval' (hpiProdNonneg ys))
        · simp [hz]
          exact mul_nonneg (hpiProdNonneg ys) (hEvenPowNonneg ys)
  have hmassBound : wp * badProb ≤
      (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma := by
    exact le_trans hmomentLower (by simpa [z] using hmomentUpper)
  have hprobBound : badProb ≤ wp⁻¹ *
      ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma) := by
    calc
      badProb = wp⁻¹ * (wp * badProb) := by field_simp [ne_of_gt hwp] <;> ring
      _ ≤ wp⁻¹ *
          ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma) :=
        mul_le_mul_of_nonneg_left hmassBound (inv_nonneg.mpr hwp.le)
  have hwpInv : (1 - t) ^ (-(κ.u : ℝ)) = wp⁻¹ := by
    dsimp [wp]
    rw [Real.rpow_neg (by linarith [ht1]), Real.rpow_natCast]
  simpa [badProb, z, hwpInv] using hprobBound

/-- L12.5: package the extension, conflict, peeling, and lower-tail nodes. -/
structure HomogeneousPeelingResults (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) : Prop where
  extension_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
        (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
        ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
          i₀ ∈ J ∧ 2 ≤ J.card ∧
            κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q)
  conflict_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
      ((H.Sp.filter (fun z => κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
        Real.exp (Cstar κ.u κ.ξ * H.Q)
  peeling : HomogeneousPeelingClaim κ hκ T c C0
  lower_tail : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
        then ∏ l, H.π.w (ys l) else 0) ≤
          (1 - t) ^ (-(κ.u : ℝ)) *
            ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
              4 ^ (κ.u + 1) * H.gamma)

/-- L12.5: the public package assembled from its four theorem nodes. -/
theorem homogeneous_peeling_export (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    HomogeneousPeelingResults κ hκ T hDeep c C0 hC0 := by
  have hm := moderate_moment κ hκ T hDeep c C0 hC0
  have hp := homogeneous_peeling κ hκ T hDeep c C0 hC0 hm
  exact ⟨homogeneous_extension_count κ hκ T hDeep c C0 hC0,
    homogeneous_conflict_count κ hκ T hDeep c C0 hC0, hp,
    homogeneous_lower_tail κ hκ T hDeep c C0 hC0 hm hp⟩

end HypercubeRamsey.S12
