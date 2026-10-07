import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Tools.PToolsMisc_p_tools_misc

/-!
# Signed discrepancy tests

F-SignedTest turns ordinary two-colour discrepancy into tests weighted by any bounded signed function. The
width budget pays for the positive/negative decomposition. The second theorem records the equal-normalizer
tilt pair used in Sections 9 and 11.
-/

namespace HypercubeRamsey

open scoped BigOperators

open Classical in
/-- The signed second test against a finite host colouring. -/
noncomputable def signedHitExpectation {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ π : Law N) (f : Fin N → ℝ) : ℝ :=
  ∑ x, μ.w x * ∑ y, π.w y * ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2) * f y

/-- F-SignedTest: from `DiscOne`, every bounded signed second test is at most
`2(B+1)·err`, after paying `log(2B+2)` in the second width budget. -/
theorem signedTest_of_discrepancy {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {wX wY err B : ℝ} (hB : 0 ≤ B)
    (hdisc : DiscOne E X Y wX wY err)
    (μ π : Law N) (hμX : μ.SupportedIn X) (hπY : π.SupportedIn Y)
    (hμ : μ.WidthLE wX)
    (hπ : π.WidthLE (wY - Real.log (2 * B + 2)))
    (f : Fin N → ℝ) (hf : ∀ y, |f y| ≤ B) (c : Colour) :
    |signedHitExpectation E c μ π f| ≤ 2 * (B + 1) * err := by
  classical
  let scale : ℝ := B + 1
  let uplus : Fin N → ℝ := fun y => 1 + f y / scale
  let uminus : Fin N → ℝ := fun y => 1 - f y / scale
  let zplus : ℝ := ∑ y, uplus y * π.w y
  let zminus : ℝ := ∑ y, uminus y * π.w y
  have hscale : 0 < scale := by dsimp [scale]; linarith
  have hden : 0 < 2 * B + 2 := by linarith
  have hN : 0 < N := by
    by_contra hn
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    have hsum := μ.sum_eq_one
    simp at hsum
  have hflow (y : Fin N) : -B ≤ f y := (abs_le.mp (hf y)).1
  have hfhigh (y : Fin N) : f y ≤ B := (abs_le.mp (hf y)).2
  have hfscale (y : Fin N) : f y / scale * scale = f y :=
    div_mul_cancel₀ (f y) (ne_of_gt hscale)
  have huplusLower (y : Fin N) : 1 / scale ≤ uplus y := by
    dsimp [uplus]
    rw [div_le_iff₀ hscale]
    dsimp [scale]
    nlinarith [hflow y, hfscale y]
  have huplusUpper (y : Fin N) : uplus y ≤ (2 * B + 1) / scale := by
    dsimp [uplus]
    rw [le_div_iff₀ hscale]
    dsimp [scale]
    nlinarith [hfhigh y, hfscale y]
  have huminusLower (y : Fin N) : 1 / scale ≤ uminus y := by
    dsimp [uminus]
    rw [div_le_iff₀ hscale]
    dsimp [scale]
    nlinarith [hfhigh y, hfscale y]
  have huminusUpper (y : Fin N) : uminus y ≤ (2 * B + 1) / scale := by
    dsimp [uminus]
    rw [le_div_iff₀ hscale]
    dsimp [scale]
    nlinarith [hflow y, hfscale y]
  have hzplusLower : 1 / scale ≤ zplus := by
    calc
      1 / scale = (1 / scale) * ∑ y, π.w y := by simp [π.sum_eq_one]
      _ = ∑ y, (1 / scale) * π.w y := by rw [Finset.mul_sum]
      _ ≤ ∑ y, uplus y * π.w y := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right (huplusLower y) (π.nonneg y)
      _ = zplus := by rfl
  have hzminusLower : 1 / scale ≤ zminus := by
    calc
      1 / scale = (1 / scale) * ∑ y, π.w y := by simp [π.sum_eq_one]
      _ = ∑ y, (1 / scale) * π.w y := by rw [Finset.mul_sum]
      _ ≤ ∑ y, uminus y * π.w y := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right (huminusLower y) (π.nonneg y)
      _ = zminus := by rfl
  have hzplus : 0 < zplus := lt_of_lt_of_le (one_div_pos.mpr hscale) hzplusLower
  have hzminus : 0 < zminus := lt_of_lt_of_le (one_div_pos.mpr hscale) hzminusLower
  have hzsum : zplus + zminus = 2 := by
    dsimp [zplus, zminus, uplus, uminus]
    calc
      (∑ y, (1 + f y / scale) * π.w y) +
          ∑ y, (1 - f y / scale) * π.w y =
          ∑ y, ((1 + f y / scale) * π.w y +
            (1 - f y / scale) * π.w y) := by rw [Finset.sum_add_distrib]
      _ = ∑ y, 2 * π.w y := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = 2 := by rw [← Finset.mul_sum, π.sum_eq_one]; ring
  let plusLaw : Law N :=
    { w := fun y => uplus y * π.w y / zplus
      nonneg := by
        intro y
        exact div_nonneg (mul_nonneg (le_trans (one_div_pos.mpr hscale).le
          (huplusLower y)) (π.nonneg y)) hzplus.le
      sum_eq_one := by
        calc
          (∑ y, uplus y * π.w y / zplus) =
              (∑ y, uplus y * π.w y) / zplus := by rw [Finset.sum_div]
          _ = zplus / zplus := rfl
          _ = 1 := div_self hzplus.ne' }
  let minusLaw : Law N :=
    { w := fun y => uminus y * π.w y / zminus
      nonneg := by
        intro y
        exact div_nonneg (mul_nonneg (le_trans (one_div_pos.mpr hscale).le
          (huminusLower y)) (π.nonneg y)) hzminus.le
      sum_eq_one := by
        calc
          (∑ y, uminus y * π.w y / zminus) =
              (∑ y, uminus y * π.w y) / zminus := by rw [Finset.sum_div]
          _ = zminus / zminus := rfl
          _ = 1 := div_self hzminus.ne' }
  have hplusSupport : plusLaw.SupportedIn Y := by
    intro y hy
    change uplus y * π.w y / zplus = 0
    rw [hπY y hy]
    simp
  have hminusSupport : minusLaw.SupportedIn Y := by
    intro y hy
    change uminus y * π.w y / zminus = 0
    rw [hπY y hy]
    simp
  have hscalePlus (y : Fin N) : uplus y / zplus ≤ 2 * B + 2 := by
    apply (div_le_iff₀ hzplus).2
    have hfac : 0 ≤ 2 * B + 2 := by linarith
    have hcomp : (2 * B + 1) / scale ≤ (2 * B + 2) / scale := by
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hscale.le
    have hmul : (2 * B + 2) / scale ≤ (2 * B + 2) * zplus := by
      calc
        (2 * B + 2) / scale = (2 * B + 2) * (1 / scale) := by ring
        _ ≤ (2 * B + 2) * zplus := mul_le_mul_of_nonneg_left hzplusLower hfac
    exact (huplusUpper y).trans (hcomp.trans hmul)
  have hscaleMinus (y : Fin N) : uminus y / zminus ≤ 2 * B + 2 := by
    apply (div_le_iff₀ hzminus).2
    have hfac : 0 ≤ 2 * B + 2 := by linarith
    have hcomp : (2 * B + 1) / scale ≤ (2 * B + 2) / scale := by
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hscale.le
    have hmul : (2 * B + 2) / scale ≤ (2 * B + 2) * zminus := by
      calc
        (2 * B + 2) / scale = (2 * B + 2) * (1 / scale) := by ring
        _ ≤ (2 * B + 2) * zminus := mul_le_mul_of_nonneg_left hzminusLower hfac
    exact (huminusUpper y).trans (hcomp.trans hmul)
  have hplusWidth : plusLaw.WidthLE wY := by
    intro y
    change uplus y * π.w y / zplus ≤ Real.exp wY / N
    calc
      uplus y * π.w y / zplus = (uplus y / zplus) * π.w y := by ring
      _ ≤ (2 * B + 2) * π.w y :=
        mul_le_mul_of_nonneg_right (hscalePlus y) (π.nonneg y)
      _ ≤ (2 * B + 2) * (Real.exp (wY - Real.log (2 * B + 2)) / N) :=
        mul_le_mul_of_nonneg_left (hπ y) (by linarith)
      _ = Real.exp wY / N := by
        rw [Real.exp_sub, Real.exp_log hden]
        field_simp [ne_of_gt hN]
        <;> ring
  have hminusWidth : minusLaw.WidthLE wY := by
    intro y
    change uminus y * π.w y / zminus ≤ Real.exp wY / N
    calc
      uminus y * π.w y / zminus = (uminus y / zminus) * π.w y := by ring
      _ ≤ (2 * B + 2) * π.w y :=
        mul_le_mul_of_nonneg_right (hscaleMinus y) (π.nonneg y)
      _ ≤ (2 * B + 2) * (Real.exp (wY - Real.log (2 * B + 2)) / N) :=
        mul_le_mul_of_nonneg_left (hπ y) (by linarith)
      _ = Real.exp wY / N := by
        rw [Real.exp_sub, Real.exp_log hden]
        field_simp [ne_of_gt hN]
        <;> ring
  have hdiscPlus : |dens E c μ plusLaw - 1 / 2| ≤ err :=
    hdisc μ plusLaw hμX hplusSupport hμ hplusWidth c
  have hdiscMinus : |dens E c μ minusLaw - 1 / 2| ≤ err :=
    hdisc μ minusLaw hμX hminusSupport hμ hminusWidth c
  have hplusWeight (y : Fin N) : zplus * plusLaw.w y = uplus y * π.w y := by
    change zplus * (uplus y * π.w y / zplus) = _
    field_simp [ne_of_gt hzplus]
  have hminusWeight (y : Fin N) : zminus * minusLaw.w y = uminus y * π.w y := by
    change zminus * (uminus y * π.w y / zminus) = _
    field_simp [ne_of_gt hzminus]
  have hweightDiff (y : Fin N) :
      π.w y * f y = scale / 2 * (zplus * plusLaw.w y - zminus * minusLaw.w y) := by
    rw [hplusWeight, hminusWeight]
    dsimp [uplus, uminus]
    field_simp [ne_of_gt hscale]
    <;> ring
  let kernel (x y : Fin N) : ℝ := (if Hits E c x y then (1 : ℝ) else 0) - 1 / 2
  have hinner (x : Fin N) :
      (∑ y, π.w y * kernel x y * f y) =
        scale / 2 * (zplus * (∑ y, plusLaw.w y * kernel x y) -
          zminus * (∑ y, minusLaw.w y * kernel x y)) := by
    calc
      ∑ y, π.w y * kernel x y * f y =
          ∑ y, scale / 2 *
            (zplus * plusLaw.w y * kernel x y - zminus * minusLaw.w y * kernel x y) := by
              apply Finset.sum_congr rfl
              intro y hy
              calc
                π.w y * kernel x y * f y =
                    (π.w y * f y) * kernel x y := by ring
                _ = (scale / 2 *
                    (zplus * plusLaw.w y - zminus * minusLaw.w y)) * kernel x y := by
                      rw [hweightDiff y]
                _ = scale / 2 *
                    (zplus * plusLaw.w y * kernel x y - zminus * minusLaw.w y * kernel x y) := by
                      rw [mul_assoc, sub_mul]
      _ = scale / 2 * (∑ y,
            (zplus * plusLaw.w y * kernel x y - zminus * minusLaw.w y * kernel x y)) := by
              simp only [Finset.mul_sum]
      _ = scale / 2 * (zplus * (∑ y, plusLaw.w y * kernel x y) -
            zminus * (∑ y, minusLaw.w y * kernel x y)) := by
              have hplusSum :
                  (∑ y, zplus * plusLaw.w y * kernel x y) =
                    zplus * (∑ y, plusLaw.w y * kernel x y) := by
                calc
                  _ = ∑ y, zplus * (plusLaw.w y * kernel x y) := by
                    simpa only [mul_assoc]
                  _ = _ := by simp only [Finset.mul_sum]
              have hminusSum :
                  (∑ y, zminus * minusLaw.w y * kernel x y) =
                    zminus * (∑ y, minusLaw.w y * kernel x y) := by
                calc
                  _ = ∑ y, zminus * (minusLaw.w y * kernel x y) := by
                    simpa only [mul_assoc]
                  _ = _ := by simp only [Finset.mul_sum]
              let a : Fin N → ℝ := fun y => zplus * plusLaw.w y * kernel x y
              let b : Fin N → ℝ := fun y => zminus * minusLaw.w y * kernel x y
              have hsumDiff : (∑ y, (a y - b y)) = (∑ y, a y) - ∑ y, b y :=
                PToolsMisc.sum_sub_univ a b
              calc
                scale / 2 * (∑ y,
                    (a y - b y)) = scale / 2 * ((∑ y, a y) - ∑ y, b y) := by
                      rw [hsumDiff]
                _ = scale / 2 * (zplus * (∑ y, plusLaw.w y * kernel x y) -
                      zminus * (∑ y, minusLaw.w y * kernel x y)) := by
                      rw [hplusSum, hminusSum]
  have hdecomp : signedHitExpectation E c μ π f =
      scale / 2 * (zplus * signedHitExpectation E c μ plusLaw (fun _ => 1) -
        zminus * signedHitExpectation E c μ minusLaw (fun _ => 1)) := by
    unfold signedHitExpectation
    calc
      ∑ x, μ.w x * ∑ y, π.w y * kernel x y * f y =
          ∑ x, μ.w x *
            (scale / 2 * (zplus * (∑ y, plusLaw.w y * kernel x y) -
              zminus * (∑ y, minusLaw.w y * kernel x y))) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [hinner x]
      _ = scale / 2 *
            (zplus * (∑ x, μ.w x * ∑ y, plusLaw.w y * kernel x y) -
              zminus * (∑ x, μ.w x * ∑ y, minusLaw.w y * kernel x y)) := by
              calc
                _ = ∑ x,
                    ((scale / 2 * zplus) * (μ.w x * ∑ y, plusLaw.w y * kernel x y) -
                      (scale / 2 * zminus) * (μ.w x * ∑ y, minusLaw.w y * kernel x y)) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        ring
                _ = (∑ x, (scale / 2 * zplus) *
                      (μ.w x * ∑ y, plusLaw.w y * kernel x y)) -
                    ∑ x, (scale / 2 * zminus) *
                      (μ.w x * ∑ y, minusLaw.w y * kernel x y) :=
                        PToolsMisc.sum_sub_univ
                          (fun x => (scale / 2 * zplus) *
                            (μ.w x * ∑ y, plusLaw.w y * kernel x y))
                          (fun x => (scale / 2 * zminus) *
                            (μ.w x * ∑ y, minusLaw.w y * kernel x y))
                _ = (scale / 2 * zplus) *
                      (∑ x, μ.w x * ∑ y, plusLaw.w y * kernel x y) -
                    (scale / 2 * zminus) *
                      (∑ x, μ.w x * ∑ y, minusLaw.w y * kernel x y) := by
                        rw [← Finset.mul_sum, ← Finset.mul_sum]
                _ = _ := by ring
      _ = scale / 2 * (zplus * signedHitExpectation E c μ plusLaw (fun _ => 1) -
            zminus * signedHitExpectation E c μ minusLaw (fun _ => 1)) := by
              simp [signedHitExpectation, kernel]
  have hcenter (ν : Law N) :
      signedHitExpectation E c μ ν (fun _ => 1) = dens E c μ ν - 1 / 2 := by
    unfold signedHitExpectation dens
    simp only [Function.const_apply, mul_one]
    have hinnerCenter (x : Fin N) :
        (∑ y, ν.w y * ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2)) =
          (∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) - 1 / 2 := by
      calc
        ∑ y, ν.w y * ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2) =
            ∑ y, (ν.w y * (if Hits E c x y then (1 : ℝ) else 0) -
              (1 / 2) * ν.w y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
        _ = (∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) -
              ∑ y, (1 / 2) * ν.w y := by
                exact PToolsMisc.sum_sub_univ
                  (fun y => ν.w y * (if Hits E c x y then (1 : ℝ) else 0))
                  (fun y => (1 / 2) * ν.w y)
        _ = (∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) - 1 / 2 := by
              rw [← Finset.mul_sum, ν.sum_eq_one]
              ring
    calc
      ∑ x, μ.w x * ∑ y, ν.w y *
          ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2) =
        ∑ x, μ.w x *
          ((∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) - 1 / 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hinnerCenter x]
      _ = (∑ x, μ.w x * ∑ y, ν.w y *
            (if Hits E c x y then (1 : ℝ) else 0)) -
          ∑ x, μ.w x * (1 / 2) := by
            calc
              _ = ∑ x, (μ.w x *
                    (∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) -
                      μ.w x * (1 / 2)) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        ring
              _ = (∑ x, μ.w x * ∑ y, ν.w y *
                    (if Hits E c x y then (1 : ℝ) else 0)) -
                    ∑ x, μ.w x * (1 / 2) :=
                      PToolsMisc.sum_sub_univ
                        (fun x => μ.w x * ∑ y, ν.w y *
                          (if Hits E c x y then (1 : ℝ) else 0))
                        (fun x => μ.w x * (1 / 2))
      _ = (∑ x, ∑ y, μ.w x * ν.w y *
            (if Hits E c x y then (1 : ℝ) else 0)) - 1 / 2 := by
            have hfirst :
                ∑ x, μ.w x * ∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0) =
                  ∑ x, ∑ y, μ.w x * ν.w y * (if Hits E c x y then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                μ.w x * ∑ y, ν.w y * (if Hits E c x y then (1 : ℝ) else 0) =
                    ∑ y, μ.w x * (ν.w y * (if Hits E c x y then (1 : ℝ) else 0)) := by
                      rw [Finset.mul_sum]
                _ = ∑ y, μ.w x * ν.w y * (if Hits E c x y then (1 : ℝ) else 0) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
            have hsecond : (∑ x, μ.w x * (1 / 2)) = 1 / 2 := by
              calc
                (∑ x, μ.w x * (1 / 2)) = (∑ x, μ.w x) * (1 / 2) := by rw [Finset.sum_mul]
                _ = 1 / 2 := by rw [μ.sum_eq_one]; ring
            rw [hfirst, hsecond]
  rw [hdecomp, hcenter plusLaw, hcenter minusLaw]
  have herr : 0 ≤ err := le_trans (abs_nonneg _) hdiscPlus
  have hsumAbs :
      |zplus * (dens E c μ plusLaw - 1 / 2) -
          zminus * (dens E c μ minusLaw - 1 / 2)| ≤ (zplus + zminus) * err := by
    have hp := mul_le_mul_of_nonneg_left hdiscPlus hzplus.le
    have hm := mul_le_mul_of_nonneg_left hdiscMinus hzminus.le
    calc
      |zplus * (dens E c μ plusLaw - 1 / 2) -
          zminus * (dens E c μ minusLaw - 1 / 2)| ≤
        |zplus * (dens E c μ plusLaw - 1 / 2)| +
          |zminus * (dens E c μ minusLaw - 1 / 2)| := abs_sub _ _
      _ = zplus * |dens E c μ plusLaw - 1 / 2| +
          zminus * |dens E c μ minusLaw - 1 / 2| := by
            rw [abs_mul, abs_of_nonneg hzplus.le, abs_mul, abs_of_nonneg hzminus.le]
      _ ≤ zplus * err + zminus * err := add_le_add hp hm
      _ = (zplus + zminus) * err := by ring
  have hscaleNonneg : 0 ≤ scale / 2 := by positivity
  calc
    |scale / 2 * (zplus * (dens E c μ plusLaw - 1 / 2) -
        zminus * (dens E c μ minusLaw - 1 / 2))| =
      scale / 2 *
        |zplus * (dens E c μ plusLaw - 1 / 2) -
          zminus * (dens E c μ minusLaw - 1 / 2)| := by
            rw [abs_mul, abs_of_nonneg hscaleNonneg]
    _ ≤ scale / 2 * ((zplus + zminus) * err) :=
          mul_le_mul_of_nonneg_left hsumAbs hscaleNonneg
    _ = scale * err := by rw [hzsum]; ring
    _ ≤ 2 * scale * err := by nlinarith [mul_nonneg hscale.le herr]

/-- F-SignedTest, equal-normalizer pair form: two tilts of a common law with the same normalizer are
controlled by the bounded signed test `(S₊-S₋)/Z`. -/
theorem signedTest_equalNormalizer {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {wX wY err B : ℝ} (hB : 0 ≤ B)
    (hdisc : DiscOne E X Y wX wY err)
    (μ baseLaw plusLaw minusLaw : Law N) (hμX : μ.SupportedIn X) (hBaseSupported : baseLaw.SupportedIn Y)
    (hμ : μ.WidthLE wX)
    (hBaseWidth : baseLaw.WidthLE (wY - Real.log (2 * B + 2)))
    (base Z : ℝ) (hZ : 0 < Z) (Splus Sminus : Fin N → ℝ)
    (hplus : ∀ y, plusLaw.w y = ((base + Splus y) / Z) * baseLaw.w y)
    (hminus : ∀ y, minusLaw.w y = ((base + Sminus y) / Z) * baseLaw.w y)
    (hnormPlus : ∑ y, (base + Splus y) * baseLaw.w y = Z)
    (hnormMinus : ∑ y, (base + Sminus y) * baseLaw.w y = Z)
    (hbound : ∀ y, |(Splus y - Sminus y) / Z| ≤ B) (c : Colour)
    [DecidableRel (Hits E c)] :
    |∑ x, μ.w x * ∑ y, (plusLaw.w y - minusLaw.w y) *
      ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2)| ≤ 2 * (B + 1) * err := by
  classical
  let f : Fin N → ℝ := fun y => (Splus y - Sminus y) / Z
  have hsumEq :
      (∑ x, μ.w x * ∑ y, (plusLaw.w y - minusLaw.w y) *
        ((if Hits E c x y then (1 : ℝ) else 0) - 1 / 2)) =
        signedHitExpectation E c μ baseLaw f := by
    unfold signedHitExpectation
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [hplus y, hminus y]
    dsimp [f]
    ring
  have htest := signedTest_of_discrepancy hB hdisc μ baseLaw hμX
    hBaseSupported hμ hBaseWidth f (by intro y; exact hbound y) c
  rw [hsumEq]
  exact htest

end HypercubeRamsey
