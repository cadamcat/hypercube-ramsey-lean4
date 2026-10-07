import HypercubeRamsey.S18.Endpoints
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s18_n6

open Classical
open Filter
open HypercubeRamsey.S18
open scoped BigOperators

lemma pairHitExpansion {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x z : Fin N) :
    corr E c π.w x z =
      4 * (∑ y, π.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) -
        2 * deg E c π.w x - 2 * deg E c π.w z + 1 := by
  classical
  have hpoint (y : Fin N) :
      fv E c x y * fv E c z y =
        4 * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) -
          2 * hit E c x y - 2 * hit E c z y + 1 := by
    by_cases hx : Hits E c x y <;> by_cases hz : Hits E c z y <;>
      simp [fv, hit, hx, hz] <;> ring
  unfold corr deg
  calc
    ∑ y, π.w y * fv E c x y * fv E c z y =
        ∑ y, π.w y * (4 * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) -
          2 * hit E c x y - 2 * hit E c z y + 1) := by
            apply Finset.sum_congr rfl
            intro y _
            calc
              π.w y * fv E c x y * fv E c z y =
                  π.w y * (fv E c x y * fv E c z y) := by ring
              _ = π.w y * (4 * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) -
                    2 * hit E c x y - 2 * hit E c z y + 1) := by rw [hpoint]
    _ = 4 * (∑ y, π.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) -
          2 * (∑ y, π.w y * hit E c x y) -
          2 * (∑ y, π.w y * hit E c z y) + 1 := by
            have hdist (y : Fin N) :
                π.w y * (4 * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) -
                  2 * hit E c x y - 2 * hit E c z y + 1) =
                4 * (π.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) -
                  2 * (π.w y * hit E c x y) - 2 * (π.w y * hit E c z y) + π.w y := by ring
            simp_rw [hdist]
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp_rw [← Finset.mul_sum]
            rw [π.sum_eq_one]

theorem pairHit_le_of_corr_degree {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x z : Fin N) (ξ ε : ℝ)
    (hCorr : |corr E c π.w x z| ≤ ξ)
    (hDx : deg E c π.w x ≤ 1 / 2 + ε)
    (hDz : deg E c π.w z ≤ 1 / 2 + ε) :
    (∑ y, π.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) ≤
      1 / 4 + ε + ξ / 4 := by
  have hid := pairHitExpansion E c π x z
  have hcorr : corr E c π.w x z ≤ ξ := le_trans (le_abs_self _) hCorr
  rw [hid] at hcorr
  linarith

lemma degree_le_of_tv_error {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) (x : Fin N) (e : ℝ)
    (he : e = (1 / 2 : ℝ) * ∑ y, |μ.w y - ν.w y|) :
    deg E c μ.w x ≤ deg E c ν.w x + 2 * e := by
  classical
  have hdiff :
      deg E c μ.w x - deg E c ν.w x = ∑ y, (μ.w y - ν.w y) * hit E c x y := by
    unfold deg
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hsum :
      (∑ y, (μ.w y - ν.w y) * hit E c x y) ≤ ∑ y, |μ.w y - ν.w y| := by
    apply Finset.sum_le_sum
    intro y _
    have hh : 0 ≤ hit E c x y ∧ hit E c x y ≤ 1 := by
      by_cases h : Hits E c x y <;> simp [hit, h]
    calc
      (μ.w y - ν.w y) * hit E c x y ≤
          |μ.w y - ν.w y| * hit E c x y :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hh.1
      _ ≤ |μ.w y - ν.w y| :=
            mul_le_of_le_one_right (abs_nonneg _) hh.2
  rw [← hdiff] at hsum
  linarith

theorem pairQueryBound_from_calibration {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (hκ : κ.Admissible)
    (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D) (Q : PairQueries D A)
    (hCount : Q.count ≤ T.S.n k ^ 2)
    (hOdd : ∀ q, ¬ IsEvenRole (flipPos (Q.row q) (Q.coordinate q)) ∧
      D.geom.classOf (flipPos (Q.row q) (Q.coordinate q)) = none)
    (hInj : Function.Injective (fun q => flipPos (Q.row q) (Q.coordinate q)))
    (hSep : ∀ q q', q ≠ q' →
      D.geom.cellOf (flipPos (Q.row q) (Q.coordinate q)) =
        D.geom.cellOf (flipPos (Q.row q') (Q.coordinate q')) →
      (hammingDist (flipPos (Q.row q) (Q.coordinate q))
        (flipPos (Q.row q') (Q.coordinate q')) : ℝ) >
          50 * κ.ρ * ((PT.tiling.P (D.geom.patchOf
            (flipPos (Q.row q) (Q.coordinate q)))).h))
    (hPairHit : ∀ (assignment : PairAssignment T k) q,
      (∀ v ∈ A.rows, A.validPair v (assignment v).1 (assignment v).2) →
      (∑ y, (PT.πraw (D.geom.patchOf (flipPos (Q.row q) (Q.coordinate q)))).w y *
        (if Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).1 y ∧
            Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).2 y then (1 : ℝ) else 0)) ≤
          1 / 4 + 1 / 2500)
    (hErr : Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)) ≤ 1 / 25000) :
  PairQueryBound D A Q := by
  classical
  intro assignment hValid
  let odd : Fin Q.count → Pos T k := fun q => flipPos (Q.row q) (Q.coordinate q)
  let f : Fin Q.count → Fin (T.S.N k) → ℝ := fun q y =>
    if Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).1 y ∧
        Hits (T.S.E k) PT.tiling.c (assignment (Q.row q)).2 y then 1 else 0
  have hCal := hD.calibration.2 Q.count hCount odd hInj hOdd hSep f (by
    intro q y
    dsimp [f]
    split_ifs <;> norm_num)
  have hCal' : Q.integral assignment ≤
      Real.exp (0.002 * Q.count) *
        ∏ q : Fin Q.count,
          ((∑ y, (PT.πraw (D.geom.patchOf (odd q))).w y * f q y) +
            Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3))) := by
    simpa [PairQueries.integral, LateData.freshQueryIntegral, LateData.freshConfigLaw, odd, f] using hCal
  have hError :
      Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)) ≤ 1 / 25000 := hErr
  have hFactor (q : Fin Q.count) :
      (∑ y, (PT.πraw (D.geom.patchOf (odd q))).w y * f q y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)) ≤ 1 / 4 + 1 / 2000 := by
    have hhit := hPairHit assignment q hValid
    dsimp [odd, f]
    calc
      _ ≤ 1 / 4 + 1 / 2500 + 1 / 25000 := add_le_add hhit hError
      _ ≤ 1 / 4 + 1 / 2000 := by norm_num
  have hFactorNonneg (q : Fin Q.count) :
      0 ≤ (∑ y, (PT.πraw (D.geom.patchOf (odd q))).w y * f q y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)) := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg ((PT.πraw (D.geom.patchOf (odd q))).nonneg y) (by
        dsimp [f]
        split_ifs <;> norm_num)
    · exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (T.S.n k))) _
  have hProdBound :
      (∏ q : Fin Q.count,
        ((∑ y, (PT.πraw (D.geom.patchOf (odd q))).w y * f q y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)))) ≤
        (1 / 4 + 1 / 2000) ^ Q.count := by
    calc
      _ ≤ ∏ _q : Fin Q.count, (1 / 4 + 1 / 2000 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro q hq
          exact hFactorNonneg q
        · intro q hq
          exact hFactor q
      _ = _ := by simp
  have hConst : 1 / 4 + 1 / 2000 ≤ (1 / 4 : ℝ) * Real.exp (3 / 1000) := by
    have hExp := Real.add_one_le_exp (3 / 1000 : ℝ)
    norm_num at hExp ⊢
    nlinarith
  have hExpPow (n : ℕ) : (Real.exp (3 / 1000 : ℝ)) ^ n =
      Real.exp ((3 / 1000 : ℝ) * n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hFourPow : (1 / 4 : ℝ) ^ Q.count = (4 : ℝ) ^ (-(Q.count : ℤ)) := by
    calc
      (1 / 4 : ℝ) ^ Q.count = ((4 : ℝ) ^ Q.count)⁻¹ := by
        simp [one_div, inv_pow]
      _ = (4 : ℝ) ^ (-(Q.count : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
  have hPower : (1 / 4 + 1 / 2000 : ℝ) ^ Q.count ≤
      (4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.003 * Q.count) := by
    calc
      (1 / 4 + 1 / 2000 : ℝ) ^ Q.count ≤
          ((1 / 4 : ℝ) * Real.exp (3 / 1000)) ^ Q.count :=
            pow_le_pow_left₀ (by positivity) hConst _
      _ = (1 / 4 : ℝ) ^ Q.count * Real.exp (0.003 * Q.count) := by
            rw [mul_pow, hExpPow]
            norm_num
      _ = (4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.003 * Q.count) := by rw [hFourPow]
  calc
    Q.integral assignment ≤ Real.exp (0.002 * Q.count) *
        (∏ q : Fin Q.count,
          ((∑ y, (PT.πraw (D.geom.patchOf (odd q))).w y * f q y) +
            Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3)))) := hCal'
    _ ≤ Real.exp (0.002 * Q.count) *
        ((4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.003 * Q.count)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hProdBound hPower) (Real.exp_pos _).le
    _ = (4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.005 * Q.count) := by
      calc
        Real.exp (0.002 * Q.count) *
            ((4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.003 * Q.count)) =
          (4 : ℝ) ^ (-(Q.count : ℤ)) *
            (Real.exp (0.002 * Q.count) * Real.exp (0.003 * Q.count)) := by ring
        _ = (4 : ℝ) ^ (-(Q.count : ℤ)) * Real.exp (0.005 * Q.count) := by
          have hExpAdd :
              Real.exp (0.002 * (Q.count : ℝ)) * Real.exp (0.003 * (Q.count : ℝ)) =
                Real.exp (0.005 * (Q.count : ℝ)) := by
            have hArg : 0.002 * (Q.count : ℝ) + 0.003 * (Q.count : ℝ) =
                0.005 * (Q.count : ℝ) := by ring
            exact (Real.exp_add _ _).symm.trans (congrArg Real.exp hArg)
          rw [hExpAdd]

theorem eventually_endpoint_numeric_bounds {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop,
      κ.Kbd / (T.S.n k : ℝ) < 1 / 10000 ∧
      4 * (T.S.n k : ℝ) ^ (κ.ι / 2 - 1) < 1 / 10000 ∧
      10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) < 1 / 10000 ∧
      Real.rpow (T.S.n k : ℝ) (-197) < 1 / 25000 ∧
      1 ≤ Real.log (T.S.n k : ℝ) ∧ 1 ≤ (T.S.n k : ℝ) := by
  have hnCast : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  have hinv : Tendsto (fun k : ℕ => (T.S.n k : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp hnCast
  have hKlim : Tendsto (fun k : ℕ => κ.Kbd * (T.S.n k : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => κ.Kbd) atTop (nhds κ.Kbd)).mul hinv)
  have hKsmall : ∀ᶠ k : ℕ in atTop,
      κ.Kbd * (T.S.n k : ℝ) ^ (-1 : ℝ) < 1 / 10000 :=
    hKlim.eventually (eventually_lt_nhds (by norm_num))
  have hι : κ.ι / 2 < 1 := by
    have hηbound : min κ.η0 (1 / 100 : ℝ) ≤ 1 / 100 := min_le_right _ _
    have hmin : min κ.xs (min κ.η0 (1 / 100 : ℝ)) ≤ 1 / 100 :=
      le_trans (min_le_right _ _) hηbound
    nlinarith [hκ.ι_rng.2, hmin]
  have hgap : 0 < 1 - κ.ι / 2 := by linarith
  have hpowlim : Tendsto
      (fun k : ℕ => (T.S.n k : ℝ) ^ (κ.ι / 2 - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hgap).comp hnCast
    have hExp : κ.ι / 2 - 1 = -(1 - κ.ι / 2) := by ring
    simpa only [Function.comp_def, hExp] using h
  have hDirectLim : Tendsto
      (fun k : ℕ => 4 * (T.S.n k : ℝ) ^ (κ.ι / 2 - 1)) atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul hpowlim)
  have hDirectSmall : ∀ᶠ k : ℕ in atTop,
      4 * (T.S.n k : ℝ) ^ (κ.ι / 2 - 1) < 1 / 10000 :=
    hDirectLim.eventually (eventually_lt_nhds (by norm_num))
  have hloglim : Tendsto
      (fun k : ℕ => Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
        hnCast
  have hLogSmall : ∀ᶠ k : ℕ in atTop,
      10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) < 1 / 10000 := by
    have h : Tendsto
        (fun k : ℕ => 10 * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (10 : ℝ)) atTop (nhds 10)).mul hloglim)
    filter_upwards [h.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10000))] with k hk
    have hnorm : 10 * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) =
        10 * (Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) := by ring
    simpa [hnorm] using hk
  have hErrLim : Tendsto (fun k : ℕ => Real.rpow (T.S.n k : ℝ) (-197))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 197)).comp hnCast
  have hErrSmall : ∀ᶠ k : ℕ in atTop,
      Real.rpow (T.S.n k : ℝ) (-197) < 1 / 25000 :=
    hErrLim.eventually (eventually_lt_nhds (by norm_num))
  have hLog : ∀ᶠ k : ℕ in atTop, 1 ≤ Real.log (T.S.n k : ℝ) :=
    (Real.tendsto_log_atTop.comp hnCast).eventually_ge_atTop 1
  have hNat : ∀ᶠ k : ℕ in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have h := hnCast.eventually_ge_atTop 1
    filter_upwards [h] with k hk
    exact_mod_cast hk
  filter_upwards [hKsmall, hDirectSmall, hLogSmall, hErrSmall, hLog, hNat]
    with k hkK hkD hkL hkE hklog hkn
  have hkK' : κ.Kbd / (T.S.n k : ℝ) < 1 / 10000 := by
    simpa [div_eq_mul_inv, Real.rpow_neg_one] using hkK
  exact ⟨hkK', hkD, hkL, hkE, hklog, hkn⟩

lemma corr_color_eq {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x z : Fin N) :
    corr E c π.w x z = corr E true π.w x z := by
  cases c with
  | true => rfl
  | false =>
    unfold corr
    apply Finset.sum_congr rfl
    intro y _
    have hx : fv E false x y = -fv E true x y := by
      by_cases h : E x y <;> norm_num [fv, hit, Hits, h]
    have hz : fv E false z y = -fv E true z y := by
      by_cases h : E z y <;> norm_num [fv, hit, Hits, h]
    rw [hx, hz]
    ring

lemma corr_le_of_tv_error {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) (x z : Fin N) (ξ e : ℝ)
    (hCorr : |corr E c ν.w x z| ≤ ξ)
    (he : e = (1 / 2 : ℝ) * ∑ y, |μ.w y - ν.w y|) :
    |corr E c μ.w x z| ≤ ξ + 2 * e := by
  classical
  have hdiff :
      corr E c μ.w x z - corr E c ν.w x z =
        ∑ y, (μ.w y - ν.w y) * (fv E c x y * fv E c z y) := by
    unfold corr
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hprod (y : Fin N) : |fv E c x y * fv E c z y| = 1 := by
    have hx : |fv E c x y| = 1 := by
      unfold fv hit
      split_ifs <;> norm_num
    have hz : |fv E c z y| = 1 := by
      unfold fv hit
      split_ifs <;> norm_num
    norm_num [abs_mul, hx, hz]
  have hsum :
      |∑ y, (μ.w y - ν.w y) * (fv E c x y * fv E c z y)| ≤
        ∑ y, |μ.w y - ν.w y| := by
    calc
      |∑ y, (μ.w y - ν.w y) * (fv E c x y * fv E c z y)| ≤
          ∑ y, |(μ.w y - ν.w y) * (fv E c x y * fv E c z y)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, |μ.w y - ν.w y| := by
            apply Finset.sum_congr rfl
            intro y _
            rw [abs_mul, hprod y, mul_one]
  have hsum' : |corr E c μ.w x z - corr E c ν.w x z| ≤ 2 * e := by
    rw [← hdiff] at hsum
    have hscale : (∑ y, |μ.w y - ν.w y|) = 2 * e := by linarith [he]
    rw [hscale] at hsum
    exact hsum
  have hν : -ξ ≤ corr E c ν.w x z ∧ corr E c ν.w x z ≤ ξ := abs_le.mp hCorr
  have habs := abs_le.mp hsum'
  have hd : corr E c μ.w x z - corr E c ν.w x z ≤ 2 * e := habs.2
  have hnd : -(corr E c μ.w x z - corr E c ν.w x z) ≤ 2 * e := by linarith [habs.1]
  apply abs_le.mpr
  constructor <;> linarith

theorem rawPairHit_le_of_profile_bounds {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (x z : Fin (T.S.N k))
    (hvalid : x ∈ PT.envelope (D.geom.patchOf v) ∧
      z ∈ PT.envelope (D.geom.patchOf v) ∧ D.nonconflict v x z)
    (hOwnX : deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x ≤ 1 / 2 + 1 / 10000)
    (hOwnZ : deg (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w z ≤ 1 / 2 + 1 / 10000)
    (hTV : PT.tvError (D.geom.patchOf v) ≤ 1 / 100000)
    (hξ : κ.ξ ≤ 1 / 1600) :
    (∑ y, (PT.πraw (D.geom.patchOf v)).w y *
      (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y then
        (1 : ℝ) else 0)) ≤ 1 / 4 + 1 / 2500 := by
  have he := hPT.tv_error_eq (D.geom.patchOf v)
  have hCorrTrue :
      |corr (T.S.E k) true (PT.π (D.geom.patchOf v)).w x z| ≤ κ.ξ := by
    rcases hvalid with ⟨_, _, hnc⟩
    change |pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) x z| ≤ κ.ξ at hnc
    simpa [pairCorr] using hnc
  have hCorrPi :
      |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z| ≤ κ.ξ := by
    rw [corr_color_eq]
    exact hCorrTrue
  have hCorrRaw := corr_le_of_tv_error (T.S.E k) PT.tiling.c
    (PT.πraw (D.geom.patchOf v)) (PT.π (D.geom.patchOf v)) x z κ.ξ
    (PT.tvError (D.geom.patchOf v)) hCorrPi he
  have hDxRaw :
      deg (T.S.E k) PT.tiling.c (PT.πraw (D.geom.patchOf v)).w x ≤
        1 / 2 + 1 / 5000 := by
    have h := degree_le_of_tv_error (T.S.E k) PT.tiling.c
      (PT.πraw (D.geom.patchOf v)) (PT.π (D.geom.patchOf v)) x
      (PT.tvError (D.geom.patchOf v)) he
    linarith
  have hDzRaw :
      deg (T.S.E k) PT.tiling.c (PT.πraw (D.geom.patchOf v)).w z ≤
        1 / 2 + 1 / 5000 := by
    have h := degree_le_of_tv_error (T.S.E k) PT.tiling.c
      (PT.πraw (D.geom.patchOf v)) (PT.π (D.geom.patchOf v)) z
      (PT.tvError (D.geom.patchOf v)) he
    linarith
  have hhit := pairHit_le_of_corr_degree (T.S.E k) PT.tiling.c
    (PT.πraw (D.geom.patchOf v)) x z
    (κ.ξ + 2 * PT.tvError (D.geom.patchOf v)) (1 / 5000)
    hCorrRaw hDxRaw hDzRaw
  have hlast : (1 / 5000 : ℝ) +
      (κ.ξ + 2 * PT.tvError (D.geom.patchOf v)) / 4 ≤ 1 / 2500 := by
    nlinarith [hξ, hTV]
  linarith

lemma overlapMoment_exponent_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (δ K Cprime η : ℝ) (hPair : PairInitialFacts D δ K)
    (hCp : 0 ≤ Cprime) (p : ℕ)
    (hp : (p : ℝ) ≤ η * (T.S.n k : ℝ)) (S : Finset (Pos T k)) :
    0.01 * (T.S.n k : ℝ) * (D.nonisolates S).card +
        Cprime * p * D.rank S ≤
      (0.02 + Cprime * η) * (T.S.n k : ℝ) * D.rank S := by
  rcases hPair with ⟨_, _, _, hNonisolates, _⟩
  have hNonisolates' : ((D.nonisolates S).card : ℝ) ≤ 2 * (D.rank S : ℝ) := by
    exact_mod_cast hNonisolates S
  have hn : 0 ≤ (T.S.n k : ℝ) := by positivity
  have hr : 0 ≤ (D.rank S : ℝ) := by positivity
  have hFirst := mul_le_mul_of_nonneg_left hNonisolates' (by positivity : 0 ≤ 0.01 * (T.S.n k : ℝ))
  have hSecond := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hCp) hr
  have h := add_le_add hFirst hSecond
  nlinarith [h]

lemma rank_singleton {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) : D.rank {v} = 0 := by
  simp [LateData.rank, LateData.overlapGraph, LateData.geometricAdj]

lemma nonisolates_singleton {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) : D.nonisolates {v} = ∅ := by
  ext w
  constructor
  · intro hw
    rw [LateData.nonisolates, Finset.mem_filter] at hw
    rcases hw with ⟨hw, x, hx, hadj⟩
    have hwv : w = v := Finset.mem_singleton.mp hw
    have hxv : x = v := Finset.mem_singleton.mp hx
    subst w
    subst x
    exact False.elim (hadj.1 rfl)
  · intro hw
    simp at hw

lemma singleton_overlap_exponent_zero {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (Cprime : ℝ) :
    0.01 * (T.S.n k : ℝ) * (D.nonisolates ({v} : Finset (Pos T k))).card +
        Cprime * D.rank {v} = 0 := by
  simp [rank_singleton, nonisolates_singleton]

end HypercubeRamsey.Lane_q_s18_n6
