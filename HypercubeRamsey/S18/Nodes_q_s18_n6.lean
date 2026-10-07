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

def rootedAdjacencyChain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) : List V → Prop
  | [] => True
  | v :: rest => (∃ u ∈ A, G.Adj u v) ∧ rootedAdjacencyChain G (insert v A) rest

theorem rootedAdjacencyChain_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (A : Finset V) {l : List V} (h : rootedAdjacencyChain G A l) :
    rootedAdjacencyChain H (A.image f) (l.map f) := by
  induction l generalizing A with
  | nil => trivial
  | cons v rest ih =>
    rcases h with ⟨⟨u, hu, huv⟩, hrest⟩
    refine ⟨⟨f u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, hf _ _ huv⟩, ?_⟩
    simpa only [Finset.image_insert, List.map_cons] using ih (A := insert v A) hrest

noncomputable def overlapAmbientGraph {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) :
  SimpleGraph (Pos T k) where
  Adj := D.geometricAdj
  symm := by
    constructor
    intro v w h
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with hd | ⟨b, hb, hv, hw⟩
    · exact Or.inl (fun hd' => hd hd'.symm)
    · exact Or.inr ⟨b, hb, hw, hv⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

noncomputable def adjacencyNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  A.biUnion fun u => Finset.univ.filter fun v => G.Adj u v

lemma mem_adjacencyNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) :
    v ∈ adjacencyNeighborhood G A ↔ ∃ u ∈ A, G.Adj u v := by
  simp [adjacencyNeighborhood]

lemma adjacencyNeighborhood_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (Δ : ℕ)
    (hdeg : ∀ u, (Finset.univ.filter fun v => G.Adj u v).card ≤ Δ) :
    (adjacencyNeighborhood G A).card ≤ A.card * Δ := by
  classical
  unfold adjacencyNeighborhood
  calc
    (A.biUnion fun u => Finset.univ.filter fun v => G.Adj u v).card ≤
        ∑ u ∈ A, (Finset.univ.filter fun v => G.Adj u v).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ A, Δ := Finset.sum_le_sum fun u hu => hdeg u
    _ = A.card * Δ := by simp

noncomputable def adjacencySequences {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ → Finset V → Finset (List V)
  | 0, _ => {[]}
  | n + 1, A =>
      (adjacencyNeighborhood G A).biUnion fun v =>
      (adjacencySequences G n (insert v A)).image fun l => v :: l

noncomputable def rootedSequenceCodeSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (p j : ℕ) :
    Finset (Finset V × List V) :=
  (U.powersetCard (p - j)).biUnion fun roots =>
    (adjacencySequences G j roots).image fun l => (roots, l)

theorem rootedAdjacencyChain_mem_sequences {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {l : List V}
    (hchain : rootedAdjacencyChain G A l) :
    l ∈ adjacencySequences G l.length A := by
  classical
  induction l generalizing A with
  | nil => simp [adjacencySequences]
  | cons v rest ih =>
    rcases hchain with ⟨⟨u, hu, huv⟩, hrest⟩
    have hv : v ∈ adjacencyNeighborhood G A :=
      (mem_adjacencyNeighborhood G A v).2 ⟨u, hu, huv⟩
    have hr := ih (A := insert v A) hrest
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, Finset.mem_image.mpr ?_⟩
    exact ⟨rest, hr, rfl⟩

theorem adjacencySequences_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (n p Δ : ℕ)
    (hdeg : ∀ u, (Finset.univ.filter fun v => G.Adj u v).card ≤ Δ)
    (hsize : A.card + n ≤ p) :
    (adjacencySequences G n A).card ≤ (p * Δ) ^ n := by
  classical
  induction n generalizing A with
  | zero => simp [adjacencySequences]
  | succ n ih =>
    have hA : A.card ≤ p := by omega
    have hneighbors : (adjacencyNeighborhood G A).card ≤ p * Δ := by
      exact (adjacencyNeighborhood_card_le G A Δ hdeg).trans
        (Nat.mul_le_mul_right Δ hA)
    have hnext (v : V) (hv : v ∈ adjacencyNeighborhood G A) :
        (insert v A).card + n ≤ p := by
      have hi : (insert v A).card ≤ A.card + 1 := Finset.card_insert_le v A
      omega
    calc
      (adjacencySequences G (n + 1) A).card ≤
          ∑ v ∈ adjacencyNeighborhood G A,
            ((adjacencySequences G n (insert v A)).image fun l => v :: l).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ v ∈ adjacencyNeighborhood G A, (p * Δ) ^ n := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_image_le.trans (ih (A := insert v A) (hnext v hv)))
      _ = (adjacencyNeighborhood G A).card * (p * Δ) ^ n := by simp
      _ ≤ (p * Δ) * (p * Δ) ^ n := Nat.mul_le_mul_right _ hneighbors
      _ = (p * Δ) ^ (n + 1) := by rw [pow_succ]; ring

theorem rootedSequenceCodeSet_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (p j Δ : ℕ)
    (hj : j ≤ p)
    (hdeg : ∀ u, (Finset.univ.filter fun v => G.Adj u v).card ≤ Δ) :
    (rootedSequenceCodeSet G U p j).card ≤ Nat.choose U.card (p - j) * (p * Δ) ^ j := by
  classical
  unfold rootedSequenceCodeSet
  calc
    _ ≤ ∑ roots ∈ U.powersetCard (p - j),
        ((adjacencySequences G j roots).image fun l => (roots, l)).card := Finset.card_biUnion_le
    _ ≤ ∑ _roots ∈ U.powersetCard (p - j), (p * Δ) ^ j := by
      apply Finset.sum_le_sum
      intro roots hroots
      apply Finset.card_image_le.trans
      apply adjacencySequences_card_le G roots j p Δ hdeg
      have hrootcard := (Finset.mem_powersetCard.mp hroots).2
      omega
    _ = (U.powersetCard (p - j)).card * (p * Δ) ^ j := by simp
    _ = Nat.choose U.card (p - j) * (p * Δ) ^ j := by simp

theorem exists_rootedAdjacencyChain {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A todo : Finset V)
    (hdisj : Disjoint A todo) (hcover : A ∪ todo = Finset.univ)
    (hrep : ∀ v, ∃ u ∈ A, G.Reachable u v) :
    ∃ l : List V, l.Nodup ∧ l.toFinset = todo ∧ rootedAdjacencyChain G A l := by
  classical
  induction todo using Finset.strongInductionOn generalizing A with
  | _ todo ih =>
    by_cases hne : todo.Nonempty
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨r, hr, hreach⟩ := hrep x
      have hxnot : x ∉ A := by
        intro hxa
        exact (Finset.disjoint_left.mp hdisj) hxa hx
      obtain ⟨p⟩ := hreach
      obtain ⟨d, hd, hdu, hdv⟩ := p.exists_boundary_dart (A : Set V) hr hxnot
      rcases d with ⟨⟨u, v⟩, huv⟩
      have hvTodo : v ∈ todo := by
        have hvUnion : v ∈ A ∪ todo := by rw [hcover]; simp
        rcases Finset.mem_union.mp hvUnion with hva | hvt
        · exact False.elim (hdv hva)
        · exact hvt
      have hAerase : A ∪ todo.erase v = (A ∪ todo).erase v := by
        ext w
        simp only [Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (hwa | ⟨hwn, hwt⟩)
          · refine ⟨?_, Or.inl hwa⟩
            intro hwv
            subst w
            exact hdv hwa
          · exact ⟨hwn, Or.inr hwt⟩
        · rintro ⟨hwn, hwa | hwt⟩
          · exact Or.inl hwa
          · exact Or.inr ⟨hwn, hwt⟩
      have hcover' : insert v A ∪ todo.erase v = Finset.univ := by
        rw [Finset.insert_union, hAerase, Finset.insert_erase (Finset.mem_union_right A hvTodo), hcover]
      have hdisj' : Disjoint (insert v A) (todo.erase v) := by
        apply Finset.disjoint_left.mpr
        intro w hwA hwTodo
        rcases Finset.mem_insert.mp hwA with hwv | hwA
        · subst w
          exact Finset.notMem_erase _ _ hwTodo
        · exact (Finset.disjoint_left.mp hdisj) hwA (Finset.mem_of_mem_erase hwTodo)
      have hrep' : ∀ w, ∃ a ∈ insert v A, G.Reachable a w := by
        intro w
        obtain ⟨a, ha, hreach⟩ := hrep w
        exact ⟨a, Finset.mem_insert_of_mem ha, hreach⟩
      obtain ⟨l, hnodup, hto, hchain⟩ :=
        ih (todo.erase v) (Finset.erase_ssubset hvTodo) (insert v A) hdisj' hcover' hrep'
      have hvnotl : v ∉ l := by
        intro hvl
        have hvl' : v ∈ l.toFinset := List.mem_toFinset.mpr hvl
        rw [hto] at hvl'
        exact Finset.notMem_erase _ _ hvl'
      refine ⟨v :: l, List.nodup_cons.mpr ⟨hvnotl, hnodup⟩, ?_, ?_⟩
      · simp only [List.toFinset_cons]
        rw [hto, Finset.insert_erase hvTodo]
      · exact ⟨⟨u, hdu, huv⟩, hchain⟩
    · have htodo : todo = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst todo
      exact ⟨[], by simp, by simp, by simp [rootedAdjacencyChain]⟩

noncomputable def componentRoot {V : Type*} (G : SimpleGraph V)
    (c : G.ConnectedComponent) : V := Classical.choose c.nonempty_supp

lemma componentRoot_mem {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    componentRoot G c ∈ c.supp := Classical.choose_spec c.nonempty_supp

noncomputable def componentRoots {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.image (componentRoot G)

theorem componentRoots_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (componentRoots G).card = Nat.card G.ConnectedComponent := by
  classical
  have hinj : Function.Injective (componentRoot G) := by
    intro c d h
    apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (componentRoot_mem G c)
    rw [h]
    exact componentRoot_mem G d
  rw [componentRoots, Finset.card_image_of_injective _ hinj, Nat.card_eq_fintype_card]
  rfl

theorem componentRoots_reach {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ∃ r ∈ componentRoots G, G.Reachable r v := by
  classical
  let c := G.connectedComponentMk v
  let r := componentRoot G c
  have hr : r ∈ c.supp := componentRoot_mem G c
  have heq : G.connectedComponentMk r = G.connectedComponentMk v := by
    simpa [c, r] using (SimpleGraph.ConnectedComponent.mem_supp_iff c r).mp hr
  refine ⟨r, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
    SimpleGraph.ConnectedComponent.exact heq⟩

theorem exists_overlapRootedChain {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (S : Finset (Pos T k)) :
    ∃ roots : Finset {v : Pos T k // v ∈ S},
      roots.card = Nat.card (D.overlapGraph S).ConnectedComponent ∧
      ∃ l : List {v : Pos T k // v ∈ S}, l.Nodup ∧
        l.toFinset = Finset.univ \ roots ∧
        rootedAdjacencyChain (D.overlapGraph S) roots l := by
  classical
  let G := D.overlapGraph S
  let roots := componentRoots G
  refine ⟨roots, componentRoots_card G, ?_⟩
  apply exists_rootedAdjacencyChain G roots (Finset.univ \ roots)
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset (Finset.subset_univ roots)
  · exact componentRoots_reach G

theorem exists_overlapRootedChain_rank {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (S : Finset (Pos T k)) :
    ∃ roots : Finset {v : Pos T k // v ∈ S},
      ∃ l : List {v : Pos T k // v ∈ S},
        roots.card = Nat.card (D.overlapGraph S).ConnectedComponent ∧
        l.Nodup ∧ l.toFinset = Finset.univ \ roots ∧ l.length = D.rank S ∧
        rootedAdjacencyChain (D.overlapGraph S) roots l := by
  obtain ⟨roots, hroots, l, hnodup, hto, hchain⟩ := exists_overlapRootedChain D S
  refine ⟨roots, l, hroots, hnodup, hto, ?_, hchain⟩
  calc
    l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = (Finset.univ \ roots).card := by rw [hto]
    _ = (Finset.univ : Finset {v : Pos T k // v ∈ S}).card - roots.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ roots)
    _ = S.card - Nat.card (D.overlapGraph S).ConnectedComponent := by
      rw [hroots]
      simp
    _ = D.rank S := rfl

theorem exists_overlapAmbientWitness {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (S : Finset (Pos T k)) :
    ∃ roots : Finset (Pos T k), roots ⊆ S ∧
      roots.card = Nat.card (D.overlapGraph S).ConnectedComponent ∧
      ∃ l : List (Pos T k), l.Nodup ∧ l.toFinset = S \ roots ∧
        l.length = D.rank S ∧ rootedAdjacencyChain (overlapAmbientGraph D) roots l := by
  classical
  obtain ⟨rootsSub, lSub, hroots, hnodup, hto, hlen, hchain⟩ :=
    exists_overlapRootedChain_rank D S
  let roots := rootsSub.image Subtype.val
  let l := lSub.map Subtype.val
  have hrootsSubset : roots ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    exact v.property
  have hrootsCard : roots.card = Nat.card (D.overlapGraph S).ConnectedComponent := by
    dsimp [roots]
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hroots]
  have hImage : (Finset.univ \ rootsSub).image Subtype.val = S \ roots := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨v, hv, hvx⟩
      rcases Finset.mem_sdiff.mp hv with ⟨_, hvnot⟩
      have hxS : x ∈ S := hvx ▸ v.property
      refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
      intro hxroot
      rcases Finset.mem_image.mp hxroot with ⟨w, hw, hwx⟩
      have hvw : v = w := Subtype.ext (hvx.trans hwx.symm)
      exact hvnot (hvw ▸ hw)
    · intro hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxroot⟩
      let v : {v : Pos T k // v ∈ S} := ⟨x, hxS⟩
      have hvnot : v ∉ rootsSub := by
        intro hv
        exact hxroot (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      apply Finset.mem_image.mpr
      exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvnot⟩, rfl⟩
  have hlistSet : l.toFinset = S \ roots := by
    dsimp [l]
    calc
      (lSub.map Subtype.val).toFinset = lSub.toFinset.image Subtype.val := by
        simpa using (Finset.image_toFinset
          (s := (lSub : Multiset {v : Pos T k // v ∈ S})) (f := Subtype.val)).symm
      _ = (Finset.univ \ rootsSub).image Subtype.val := by rw [hto]
      _ = S \ roots := hImage
  have hlistNodup : l.Nodup := hnodup.map Subtype.val_injective
  have hlistLength : l.length = D.rank S := by simpa [l] using hlen
  have hchain' : rootedAdjacencyChain (overlapAmbientGraph D) roots l :=
    rootedAdjacencyChain_map (D.overlapGraph S) (overlapAmbientGraph D) Subtype.val
      (by intro v w h; exact h) rootsSub hchain
  exact ⟨roots, hrootsSubset, hrootsCard, l, hlistNodup, hlistSet, hlistLength, hchain'⟩

theorem exists_overlapWitnessCode {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    {S U : Finset (Pos T k)} (hSU : S ⊆ U) :
    ∃ roots ∈ U.powersetCard (S.card - D.rank S),
      ∃ l ∈ adjacencySequences (overlapAmbientGraph D) (D.rank S) roots,
        roots ∪ l.toFinset = S := by
  classical
  obtain ⟨roots, hrootsSub, hrootsCard, l, hnodup, hlistSet, hlen, hchain⟩ :=
    exists_overlapAmbientWitness D S
  have hrootcard : roots.card = S.card - D.rank S := by
    have hle : Nat.card (D.overlapGraph S).ConnectedComponent ≤ S.card := by
      have := Finset.card_le_card hrootsSub
      simpa [hrootsCard] using this
    rw [hrootsCard]
    have hle' : Fintype.card (D.overlapGraph S).ConnectedComponent ≤ S.card := by
      simpa using hle
    simp only [LateData.rank, Nat.card_eq_fintype_card]
    omega
  have hrootsU : roots ⊆ U := hrootsSub.trans hSU
  have hrootMem : roots ∈ U.powersetCard (S.card - D.rank S) := by
    exact Finset.mem_powersetCard.mpr ⟨hrootsU, hrootcard⟩
  have hseq : l ∈ adjacencySequences (overlapAmbientGraph D) (D.rank S) roots := by
    have h := rootedAdjacencyChain_mem_sequences
      (G := overlapAmbientGraph D) (A := roots) (l := l) hchain
    rw [hlen] at h
    exact h
  refine ⟨roots, hrootMem, l, hseq, ?_⟩
  rw [hlistSet]
  exact Finset.union_sdiff_of_subset hrootsSub

end HypercubeRamsey.Lane_q_s18_n6
