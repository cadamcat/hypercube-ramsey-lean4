import HypercubeRamsey.S13.ResidualBounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace HypercubeRamsey.Lane_sol_s13_allocA
open Filter
open scoped BigOperators

lemma parameters {κ : CConsts} (hκ : κ.Admissible) :
    0 < κ.a ∧ κ.a < 1 ∧ (2000000 : ℝ) ≤ κ.u ∧
      κ.aC < (1 / 10 ^ 6 : ℝ) ∧ κ.aB < (1 / 10 ^ 9 : ℝ) ∧
      10 * κ.u ≤ Real.log (800 / (κ.a * (1 / 400 : ℝ))) := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hu : 2000000 ≤ κ.u := by
    have hP : 100 * (200 + 10) ≤ κ.P := by simpa [hκ.Ac_eq] using hκ.P_big.2
    have hR : 1 ≤ κ.R := by rw [hκ.R_eq]; nlinarith
    have hL : 500 ≤ κ.L := by rw [hκ.L_eq]; omega
    nlinarith [hκ.u_rng.2]
  have huReal : (2000000 : ℝ) ≤ κ.u := by exact_mod_cast hu
  have haC : κ.aC < (1 / 10 ^ 6 : ℝ) := by
    have := (min_le_right κ.η0 (1 : ℝ))
    nlinarith [hκ.aC_rng.2]
  have haB : κ.aB < (1 / 10 ^ 9 : ℝ) := by nlinarith [hκ.aB_rng.2.1]
  have hpow : 1 ≤ (4 : ℝ) ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
  have hθ : κ.θ < κ.ξ ^ 2 := by
    have hden : (1 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith
    have hdiv := div_le_self (sq_nonneg κ.ξ) hden
    exact hκ.θ_rng.2.trans_le hdiv
  have haξ : κ.a < κ.ξ ^ 2 := by rw [hκ.a_eq]; linarith [hκ.θ_rng.1]
  have hξ : κ.ξ < (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) := by
    exact hκ.ξ_rng.2.trans (by
      have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
        (-(10 * (κ.u : ℝ) + 100))
      calc
        κ.α * (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) <
            1 * (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) :=
          mul_lt_mul_of_pos_right (by linarith [hκ.α_rng.2]) hp
        _ = _ := one_mul _)
  have hlogξ := Real.log_lt_log hκ.ξ_rng.1 hξ
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlogξ
  have hloga := Real.log_lt_log ha haξ
  rw [Real.log_pow] at hloga
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogaBound : Real.log κ.a < -10 * (κ.u : ℝ) - 100 := by
    have hm := mul_neg_of_pos_of_neg (by linarith : 0 < 10 * (κ.u : ℝ) + 100)
      (by linarith : 1 / 2 - Real.log 2 < 0)
    norm_num at hloga
    have hlogxBound : 2 * Real.log κ.ξ < -(10 * (κ.u : ℝ) + 100) := by
      have hdouble := mul_lt_mul_of_pos_left hlogξ (by norm_num : (0 : ℝ) < 2)
      nlinarith only [hdouble, hm]
    linarith
  have ha1 : κ.a < 1 := (Real.log_neg_iff ha).mp (by linarith)
  have hquot : 800 / (κ.a * (1 / 400 : ℝ)) = 320000 / κ.a := by field_simp; ring
  rw [hquot, Real.log_div (by norm_num : (320000 : ℝ) ≠ 0) ha.ne']
  have hlog320 : 0 ≤ Real.log (320000 : ℝ) := Real.log_nonneg (by norm_num)
  exact ⟨ha, ha1, huReal, haC, haB, by linarith⟩

lemma threshold {κ : CConsts} (hκ : κ.Admissible) : 1 < κ.Q0 := by
  have hp := parameters hκ
  by_contra h
  have hc := hκ.Q0_large 1 (le_of_not_gt h)
  have hc6 := hc.2.2.2.2.2.1
  norm_num at hc6
  have hr : 0 ≤ (2 * (1 : ℝ)) ^ (4 * κ.ω * κ.Mhi) := Real.rpow_nonneg (by norm_num) _
  norm_num at hr
  have hu := hp.2.2.1
  have hl := hp.2.2.2.2.2
  linarith

lemma direct_budget {κ : CConsts} (hκ : κ.Admissible) {g : ℝ}
    (hg : κ.M1 * κ.Q0 ≤ g) :
    2 * (g ^ κ.aB + 10) ≤ g / (10 ^ 6 * κ.u) := by
  rcases parameters hκ with ⟨ha, ha1, hu, haC, haB, hlog⟩
  have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hg1 : 1 ≤ g := by nlinarith [threshold hκ, hκ.M1_big.1]
  have hg0 : 0 < g := by linarith
  have hbase : 0 < κ.M1 * κ.Q0 := mul_pos hM (by linarith [threshold hκ])
  have hz0 : 0 ≤ Real.log 2 * κ.aB := mul_nonneg (Real.log_nonneg (by norm_num)) hκ.aB_rng.1.le
  have hzUpper : Real.log 2 * κ.aB ≤ 1 / 10 ^ 9 := by
    have hlog1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    exact (mul_le_mul_of_nonneg_right hlog1 hκ.aB_rng.1.le).trans (by simpa using haB.le)
  have hz1 : Real.log 2 * κ.aB ≤ 1 := by linarith
  have hexp := Real.abs_exp_sub_one_le (x := Real.log 2 * κ.aB)
    (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [abs_of_nonneg hz0] at hexp
  have hfactor : (2 : ℝ) ^ κ.aB - 1 ≤ 2 / 10 ^ 9 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := (le_abs_self (Real.exp (Real.log 2 * κ.aB) - 1)).trans hexp
    linarith [hzUpper]
  have hq := (hκ.Q0_large κ.Q0 le_rfl).1
  have hpow : (κ.M1 * κ.Q0) ^ κ.aB ≤ g ^ κ.aB :=
    Real.rpow_le_rpow hbase.le hg hκ.aB_rng.1.le
  have hf0 : 0 ≤ (2 : ℝ) ^ κ.aB - 1 := by
    have := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hκ.aB_rng.1.le
    linarith
  have hbig : (10 ^ 9 : ℝ) * κ.u ≤ g ^ κ.aB := by
    have hm := mul_le_mul_of_nonneg_left hpow hf0
    have hpn := Real.rpow_nonneg hg0.le κ.aB
    have hm2 := mul_le_mul_of_nonneg_right hfactor hpn
    change Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤
      ((2 : ℝ) ^ κ.aB - 1) * (κ.M1 * κ.Q0) ^ κ.aB at hq
    have hc := hlog.trans (hq.trans (hm.trans hm2))
    nlinarith only [hc, hu]
  have hsquare : (g ^ κ.aB) ^ 2 ≤ g := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0.le]
    calc
      g ^ (κ.aB * 2) ≤ g ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
      _ = g := Real.rpow_one _
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 6 * (κ.u : ℝ))).2
  have hpn := Real.rpow_nonneg hg0.le κ.aB
  have hm := mul_nonneg (sub_nonneg.mpr hbig)
    (show 0 ≤ g ^ κ.aB by positivity)
  have hpu : (κ.u : ℝ) ≤ (κ.u : ℝ) * g ^ κ.aB := by
    have hp1 : 1 ≤ g ^ κ.aB := Real.one_le_rpow hg1 hκ.aB_rng.1.le
    nlinarith
  nlinarith

lemma Cstar_large {κ : CConsts} (hκ : κ.Admissible) :
    10000 * (κ.u : ℝ) ≤ Cstar κ.u κ.ξ := by
  have hu := (parameters hκ).2.2.1
  have hξ1 : κ.ξ < 1 := by
    have hp : (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have hu0 : (0 : ℝ) ≤ κ.u := Nat.cast_nonneg κ.u
        linarith)
    have hm := mul_le_mul_of_nonneg_left hp hκ.α_rng.1.le
    have hx := hκ.ξ_rng.2
    simp only [Real.rpow_eq_pow] at hx
    simp only [mul_one] at hm
    exact hx.trans_le (hm.trans (by linarith [hκ.α_rng.2]))
  have hξ2 : κ.ξ ^ 2 ≤ 1 := by nlinarith [hκ.ξ_rng.1]
  have hpow : (κ.u : ℝ) ^ 2 ≤ (4 : ℝ) ^ (κ.u + 3) := by
    have hp : (κ.u : ℝ) ≤ (2 : ℝ) ^ κ.u := by exact_mod_cast S13.nat_le_two_pow κ.u
    calc
      _ ≤ ((2 : ℝ) ^ κ.u) ^ 2 := by gcongr
      _ = (4 : ℝ) ^ κ.u := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (4 : ℝ) ^ (κ.u + 3) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hfrac : (4 : ℝ) ^ (κ.u + 3) ≤ (4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hκ.ξ_rng.1)).2
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (κ.u + 3)]
  have hfloor := Nat.lt_floor_add_one ((4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2)
  unfold Cstar
  nlinarith

lemma cluster_budget {κ : CConsts} (hκ : κ.Admissible) {q h : ℝ}
    (hq : κ.Q0 ≤ q) (hh : q ^ (κ.Mlo : ℝ) ≤ h) :
    2 * (q ^ κ.aC + 10) ≤ (κ.a * h / 10 ^ 6) / (1000 * κ.u) := by
  rcases parameters hκ with ⟨ha, ha1, hu, haC, haB, hlog⟩
  have hq1 : 1 ≤ q := (threshold hκ).le.trans hq
  have hqpow : q ^ κ.aC ≤ q := by
    calc
      _ ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = q := Real.rpow_one _
  have hc := Cstar_large hκ
  have hq7 := (hκ.Q0_large q hq).2.2.2.2.2.2.1
  simp only [Real.rpow_eq_pow] at hq7
  have hmul := mul_le_mul_of_nonneg_left hh ha.le
  have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hpoly : 2 * (q + 10) ≤ 40 * q ^ 2 := by
    nlinarith [sq_nonneg (q - 1)]
  have hprod := mul_le_mul_of_nonneg_right hc (sq_nonneg q)
  have hpolymul := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ (10 ^ 6 : ℝ) * (1000 * (κ.u : ℝ)) by positivity)
  have hqpowmul := mul_le_mul_of_nonneg_right hqpow (show 0 ≤ (2 : ℝ) * (10 ^ 6 * (1000 * (κ.u : ℝ))) by positivity)
  have hden : 0 < (10 ^ 6 : ℝ) * (1000 * (κ.u : ℝ)) := by positivity
  rw [div_div]
  apply (le_div_iff₀ hden).2
  have hnonneg : 0 ≤ (κ.u : ℝ) := by positivity
  nlinarith

lemma Mhi_positive {κ : CConsts} (hκ : κ.Admissible) :
    0 < κ.Mlo ∧ 0 < κ.Mhi ∧ (κ.Mlo : ℝ) ≤ κ.Mhi := by
  have hCb : (100 : ℝ) < κ.Cb := by
    have hr : 0 < 100 * κ.aC / κ.aB := div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith [hκ.Cb_big]
  have hMlo : (0 : ℝ) < κ.Mlo := by linarith [hκ.Mlo_big]
  have hdiv : 0 < (10 : ℝ) / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
  have hhi := hκ.Mhi_big.1
  exact ⟨by exact_mod_cast hMlo, by exact_mod_cast (show (0 : ℝ) < κ.Mhi by linarith), by linarith⟩

lemma cluster_tuple_bound {κ : CConsts} (hκ : κ.Admissible) {q : ℝ} {h : ℕ}
    (hq : κ.Q0 ≤ q) (hh : (h : ℝ) < 2 * q ^ (κ.Mhi : ℝ))
    (hh1 : 1 ≤ h) :
    (sliceK κ h : ℝ) * sliceT κ h ≤ q ^ (κ.aC / 2) := by
  rcases parameters hκ with ⟨ha, ha1, hu, haC, haB, hlog⟩
  have hq1 : 1 ≤ q := (threshold hκ).le.trans hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq1
  have hMhi : 1 ≤ κ.Mhi := by have hp := (Mhi_positive hκ).2.1; omega
  have hhReal : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hωpos := hκ.ω_rng.1
  have haCpos := hκ.aC_rng.1
  have hK : (sliceK κ h : ℝ) ≤ 2 * (h : ℝ) ^ (3 * κ.ω) := by
    unfold sliceK
    simp only [Real.rpow_eq_pow]
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ h) (3 * κ.ω))
    have hone := Real.one_le_rpow hhReal (by positivity : 0 ≤ 3 * κ.ω)
    linarith
  have hT : (sliceT κ h : ℝ) ≤ 2 * (h : ℝ) ^ κ.ω := by
    unfold sliceT
    simp only [Real.rpow_eq_pow]
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ h) κ.ω)
    have hone := Real.one_le_rpow hhReal hκ.ω_rng.1.le
    linarith
  have hprod : (sliceK κ h : ℝ) * sliceT κ h ≤ 4 * (h : ℝ) ^ (4 * κ.ω) := by
    calc
      _ ≤ (2 * (h : ℝ) ^ (3 * κ.ω)) * (2 * (h : ℝ) ^ κ.ω) := by gcongr
      _ = 4 * ((h : ℝ) ^ (3 * κ.ω) * (h : ℝ) ^ κ.ω) := by ring
      _ = 4 * (h : ℝ) ^ (4 * κ.ω) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < h)]
        congr 2
        ring
  have hω : 4 * κ.ω ≤ 1 := by
    have hMhiReal : (1 : ℝ) ≤ κ.Mhi := by exact_mod_cast hMhi
    have hm := mul_le_mul_of_nonneg_left hMhiReal hκ.ω_rng.1.le
    nlinarith [hκ.ω_rng.2]
  have hexp : 4 * κ.ω * (κ.Mhi : ℝ) ≤ κ.aC / 4 := by
    nlinarith [hκ.ω_rng.2, mul_nonneg hωpos.le (Nat.cast_nonneg κ.Mhi)]
  have hTwo : (2 : ℝ) ^ (4 * κ.ω) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hω
      _ = 2 := Real.rpow_one _
  have hUpper : (sliceK κ h : ℝ) * sliceT κ h ≤ 8 * q ^ (κ.aC / 4) := by
    calc
      _ ≤ 4 * (h : ℝ) ^ (4 * κ.ω) := hprod
      _ ≤ 4 * (2 * q ^ (κ.Mhi : ℝ)) ^ (4 * κ.ω) := by gcongr
      _ = 4 * ((2 : ℝ) ^ (4 * κ.ω) * q ^ ((κ.Mhi : ℝ) * (4 * κ.ω))) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hq0.le _),
          ← Real.rpow_mul hq0.le]
      _ ≤ 4 * (2 * q ^ (κ.aC / 4)) := by
        have hqp := Real.rpow_le_rpow_of_exponent_le hq1
          (show (κ.Mhi : ℝ) * (4 * κ.ω) ≤ κ.aC / 4 by nlinarith only [hexp])
        have hm := mul_le_mul hTwo hqp (Real.rpow_nonneg hq0.le _) (by norm_num : (0 : ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = 8 * q ^ (κ.aC / 4) := by ring
  have hq6 := (hκ.Q0_large q hq).2.2.2.2.2.1
  have hsq : q ^ (2 * κ.aC) = (q ^ κ.aC) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  simp only [Real.rpow_eq_pow] at hq6
  rw [hsq] at hq6
  have hx0 := Real.rpow_nonneg hq0.le κ.aC
  have hy0 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * q)
    (4 * κ.ω * (κ.Mhi : ℝ))
  have hx : (4096 : ℝ) ≤ q ^ κ.aC := by nlinarith
  have hroot : (8 : ℝ) ≤ q ^ (κ.aC / 4) := by
    have hr := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4096) hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h8 : (4096 : ℝ) ^ (1 / 4 : ℝ) = 8 := by
      rw [show (4096 : ℝ) = 8 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [h8, ← Real.rpow_mul hq0.le] at hr
    convert hr using 1 <;> congr 1 <;> ring
  calc
    _ ≤ 8 * q ^ (κ.aC / 4) := hUpper
    _ ≤ q ^ (κ.aC / 4) * q ^ (κ.aC / 4) := by gcongr
    _ = q ^ (κ.aC / 2) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring

lemma prefix_loss {N M S ell : ℕ} {r : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hS : 0 < S) (hSN : S ≤ N)
    (hsize : (1 / 400 : ℝ) * N * Real.exp (-r) ≤ M)
    (hdyadic : (M : ℝ) / S ≤ (2 : ℝ) ^ (-(ell : ℤ))) :
    (ell : ℝ) ≤ 2 * (r + 10) ∧ Real.log ((N : ℝ) / M) ≤ r + 10 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hln := Real.log_le_log (by positivity : (0 : ℝ) < (1 / 400 : ℝ) * N * Real.exp (-r)) hsize
  rw [Real.log_mul (by positivity : (1 / 400 : ℝ) * N ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_mul (by norm_num : (1 / 400 : ℝ) ≠ 0) hNr.ne',
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (400 : ℝ) ≠ 0),
    Real.log_one] at hln
  have hlog400 : Real.log (400 : ℝ) < 10 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have hp : (400 : ℝ) < 2 ^ (10 : ℕ) := by norm_num
    exact hp.trans (by
      have h := pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num : (0 : ℝ) ≤ 2) (by decide : (10 : ℕ) ≠ 0)
      simpa [← Real.exp_nat_mul] using h)
  have hmass : Real.log ((N : ℝ) / M) ≤ r + 10 := by
    rw [Real.log_div hNr.ne' hMr.ne']
    linarith
  have hld := Real.log_le_log (div_pos hMr hSr) hdyadic
  rw [Real.log_div hMr.ne' hSr.ne', zpow_neg, zpow_natCast, Real.log_inv,
    Real.log_pow] at hld
  have hSNr : (S : ℝ) ≤ N := by exact_mod_cast hSN
  have hlogs := Real.log_le_log hSr hSNr
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog2 hell0
  refine ⟨?_, hmass⟩
  rw [Real.log_div hNr.ne' hMr.ne'] at hmass
  linarith

lemma qScale_swap (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) :
    qScale κ T.swap k RY RX = qScale κ T k RX RY := by
  classical
  unfold qScale
  apply congrArg (fun J : Finset ℕ => 2 ^ J.sup id)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [S13.clusterWitness_swap_iff]
  rfl

lemma oriented_cluster_bound {κ : CConsts} {T : Stage}
    (hBounds : S13.ResidualScaleBoundFacts κ T) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ o : Bool, ∀ RX RY : Finset (Fin ((T.orient o).S.N k)),
      RX ⊆ (T.orient o).X k → RY ⊆ (T.orient o).Y k →
      (qScale κ (T.orient o) k RX RY : ℝ) < (T.S.n k : ℝ) ^ γ := by
  filter_upwards [(hBounds γ hγ).2] with k hk
  intro o RX RY hRX hRY
  cases o with
  | false => exact (hk RX RY hRX hRY).2
  | true =>
    have h := (hk RY RX hRY hRX).2
    rw [← qScale_swap κ T k RY RX] at h
    exact h

lemma full_bin_log {q : ℝ} (hq : 16 ≤ q) :
    q / 4 < Real.log (⌊Real.exp (q / 2)⌋₊ : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp (q / 2) := by
    have hh : 1 ≤ q / 2 := by linarith
    exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hh)
  have hd : Real.exp (q / 2) / 2 ≤ (⌊Real.exp (q / 2)⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one (Real.exp (q / 2))
    linarith
  have hl := Real.log_le_log (by positivity : 0 < Real.exp (q / 2) / 2) hd
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at hl
  linarith [Real.log_two_lt_d9]

lemma power_lt_quarter {q p : ℝ} (hq : 32 ≤ q) (hp : p < 1 / 2) :
    q ^ p < q / 4 := by
  have hq0 : 0 < q := by linarith
  have h1 : 1 ≤ q := by linarith
  have hr : q ^ p ≤ Real.sqrt q := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le h1 hp.le
  apply hr.trans_lt
  rw [Real.sqrt_lt' (by positivity : 0 < q / 4)]
  have hm := mul_pos (by linarith : 0 < q - 16) hq0
  nlinarith

lemma cluster_scale_large {κ : CConsts} (hκ : κ.Admissible) {q : ℝ}
    (hq : κ.Q0 ≤ q) : 4096 ≤ q ∧ 4096 ≤ q ^ κ.aC := by
  rcases parameters hκ with ⟨ha, ha1, hu, haC, haB, hlog⟩
  have hq1 : 1 ≤ q := (threshold hκ).le.trans hq
  have hq0 : 0 < q := by linarith
  have hq6 := (hκ.Q0_large q hq).2.2.2.2.2.1
  have hsq : q ^ (2 * κ.aC) = (q ^ κ.aC) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  simp only [Real.rpow_eq_pow] at hq6
  rw [hsq] at hq6
  have hx0 := Real.rpow_nonneg hq0.le κ.aC
  have hy0 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * q)
    (4 * κ.ω * (κ.Mhi : ℝ))
  have hx : (4096 : ℝ) ≤ q ^ κ.aC := by nlinarith
  have hpow : q ^ κ.aC ≤ q := by
    calc
      _ ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = q := Real.rpow_one _
  exact ⟨hx.trans hpow, hx⟩

lemma cluster_full_bin {κ : CConsts} (hκ : κ.Admissible) {q : ℝ} {h : ℕ}
    (hq : κ.Q0 ≤ q) (hlo : q ^ (κ.Mlo : ℝ) ≤ h)
    (hhi : (h : ℝ) < 2 * q ^ (κ.Mhi : ℝ)) :
    (sliceK κ h : ℝ) * sliceT κ h < Real.log (⌊Real.exp (q / 2)⌋₊ : ℝ) ∧
      (h : ℝ) < (⌊Real.exp (q / 2)⌋₊ : ℝ) ^ (1 / 40 : ℝ) := by
  have hqLarge := (cluster_scale_large hκ hq).1
  have hq1 : 1 ≤ q := by linarith
  have hh1r : (1 : ℝ) ≤ h := by
    exact (Real.one_le_rpow hq1 (by positivity : 0 ≤ (κ.Mlo : ℝ))).trans hlo
  have hh1 : 1 ≤ h := by exact_mod_cast hh1r
  have htuple := cluster_tuple_bound hκ hq hhi hh1
  have hlog := full_bin_log (q := q) (by linarith)
  have hquarter := power_lt_quarter (q := q) (p := κ.aC / 2)
    (by linarith) (by linarith [(parameters hκ).2.2.2.1])
  refine ⟨htuple.trans_lt (hquarter.trans hlog), ?_⟩
  have hcond := (hκ.Q0_large q hq).2.2.2.2.2.2.2.2 h hlo hhi
  have hsmall := hcond.2.2.2.2.2.2.2.2.2.1
  have hdpos : 0 < Real.log (⌊Real.exp (q / 2)⌋₊ : ℝ) := by linarith
  have hd0 : (0 : ℝ) < ⌊Real.exp (q / 2)⌋₊ := by
    have he : (2 : ℝ) ≤ Real.exp (q / 2) := by
      exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by linarith))
    have hf := Nat.lt_floor_add_one (Real.exp (q / 2))
    linarith
  have hd1 : (1 : ℝ) < ⌊Real.exp (q / 2)⌋₊ := (Real.log_pos_iff hd0.le).mp hdpos
  exact hsmall.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hd1 (by norm_num))

lemma high_small_estimates {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (q : ℝ) (h : ℕ),
      κ.Q0 ≤ q → q ≤ (Real.log (T.S.n k)) ^ 2 →
      q ^ (κ.Mlo : ℝ) ≤ h → (h : ℝ) < 2 * q ^ (κ.Mhi : ℝ) →
      (sliceK κ h : ℝ) * sliceT κ h <
        Real.log (min ⌊Real.exp (q / 2)⌋₊
          ⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℕ) ∧
      (h : ℝ) < (min ⌊Real.exp (q / 2)⌋₊
          ⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℕ) ^ (1 / 40 : ℝ) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hL : Tendsto (fun k => Real.log (T.S.n k)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hn
  have hY : Tendsto (fun k => Real.sqrt (Real.log (T.S.n k))) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hL
  have hpow := hL.eventually (Lane_sol_consts_adm.eventually_power_bound κ.aC (1 / 2) 1 (1 / 4)
    (by linarith [(parameters hκ).2.2.2.1]) (by norm_num))
  have hexp := hY.eventually (Lane_sol_consts_adm.eventually_exp_bound (4 * (κ.Mhi : ℝ)) 8 (1 / 40)
    (by norm_num))
  filter_upwards [hpow, hexp, hL.eventually_ge_atTop 1, hY.eventually_ge_atTop 16]
    with k hp he hL1 hY16
  intro q h hq hqL hlo hhi
  have hq0 : 0 < q := by linarith [threshold hκ]
  have hL0 : 0 < Real.log (T.S.n k) := by linarith
  have hLnonneg : 0 ≤ Real.log (T.S.n k) := hL0.le
  have hY0 : 0 < Real.sqrt (Real.log (T.S.n k)) := by linarith
  have haCpos := hκ.aC_rng.1
  have hfull := cluster_full_bin hκ hq hlo hhi
  have hh1 : 1 ≤ h := by
    have := (Real.one_le_rpow ((threshold hκ).le.trans hq)
      (by positivity : 0 ≤ (κ.Mlo : ℝ))).trans hlo
    exact_mod_cast this
  have ht := cluster_tuple_bound hκ hq hhi hh1
  have htL : (sliceK κ h : ℝ) * sliceT κ h ≤ (Real.log (T.S.n k)) ^ κ.aC := by
    calc
      _ ≤ q ^ (κ.aC / 2) := ht
      _ ≤ ((Real.log (T.S.n k)) ^ 2) ^ (κ.aC / 2) := by gcongr
      _ = (Real.log (T.S.n k)) ^ κ.aC := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLnonneg]
        congr 1
        ring
  have hsmallLog := full_bin_log (q := 2 * Real.sqrt (Real.log (T.S.n k))) (by linarith)
  have hsmallLog' : Real.sqrt (Real.log (T.S.n k)) / 2 <
      Real.log (⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℝ) := by
    rw [show 2 * Real.sqrt (Real.log (T.S.n k)) / 2 = Real.sqrt (Real.log (T.S.n k)) by ring] at hsmallLog
    convert hsmallLog using 1 <;> ring
  have hTupleSmall : (sliceK κ h : ℝ) * sliceT κ h <
      Real.log (⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℝ) := by
    simp only [one_mul, ← Real.sqrt_eq_rpow] at hp
    linarith
  have hExpFloor : Real.exp (Real.sqrt (Real.log (T.S.n k))) / 2 ≤
      (⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℝ) := by
    have hx : (2 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (T.S.n k))) := by
      exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by linarith))
    have hf := Nat.lt_floor_add_one (Real.exp (Real.sqrt (Real.log (T.S.n k))))
    linarith
  have hFloorPow : Real.exp (Real.sqrt (Real.log (T.S.n k)) / 40) / 2 ≤
      (⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℝ) ^ (1 / 40 : ℝ) := by
    have hd := Real.rpow_le_rpow (by positivity : 0 ≤ Real.exp (Real.sqrt (Real.log (T.S.n k))) / 2)
      hExpFloor (by norm_num : (0 : ℝ) ≤ 1 / 40)
    rw [Real.div_rpow (by positivity) (by norm_num),
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hd
    have htwo : (2 : ℝ) ^ (1 / 40 : ℝ) ≤ 2 := by
      calc
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) htwo).trans (by
      simpa [div_eq_mul_inv, mul_comm] using hd)
  have hhL : (h : ℝ) < 2 * (Real.sqrt (Real.log (T.S.n k))) ^ (4 * (κ.Mhi : ℝ)) := by
    apply hhi.trans_le
    have hr : q ^ (κ.Mhi : ℝ) ≤ ((Real.log (T.S.n k)) ^ 2) ^ (κ.Mhi : ℝ) := by gcongr
    have heq : ((Real.log (T.S.n k)) ^ 2) ^ (κ.Mhi : ℝ) =
        (Real.sqrt (Real.log (T.S.n k))) ^ (4 * (κ.Mhi : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hLnonneg, ← Real.rpow_mul hLnonneg]
      congr 1
      ring
    rw [heq] at hr
    linarith
  have hDimSmall : (h : ℝ) <
      (⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊ : ℝ) ^ (1 / 40 : ℝ) := by
    have he' : 8 * (Real.sqrt (Real.log (T.S.n k))) ^ (4 * (κ.Mhi : ℝ)) ≤
        Real.exp (Real.sqrt (Real.log (T.S.n k)) / 40) := by
      simpa [div_eq_mul_inv, mul_comm] using he
    have hp0 := Real.rpow_nonneg hY0.le (4 * (κ.Mhi : ℝ))
    have hx0 := Real.exp_pos (Real.sqrt (Real.log (T.S.n k)) / 40)
    linarith
  by_cases hm : ⌊Real.exp (q / 2)⌋₊ ≤ ⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊
  · simpa only [Nat.min_eq_left hm, one_div] using hfull
  · simpa only [Nat.min_eq_right (le_of_not_ge hm), one_div] using And.intro hTupleSmall hDimSmall

lemma maximal_disjoint_patches {α : Type*} {N : ℕ}
    (X Y : α → Finset (Fin N)) :
    ∃ s : Finset α,
      (s : Set _).Pairwise (fun a b => Disjoint (X a) (X b) ∧ Disjoint (Y a) (Y b)) ∧
      ∀ t : Finset α,
        (t : Set _).Pairwise (fun a b => Disjoint (X a) (X b) ∧ Disjoint (Y a) (Y b)) →
        ∑ a ∈ t, (X a).card ≤ ∑ a ∈ s, (X a).card := by
  classical
  let masses : Finset ℕ := (Finset.range (N + 1)).filter fun m =>
    ∃ s : Finset α,
      (s : Set _).Pairwise (fun a b => Disjoint (X a) (X b) ∧ Disjoint (Y a) (Y b)) ∧
        ∑ a ∈ s, (X a).card = m
  have hzero : 0 ∈ masses := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ∅, ?_, by simp⟩
    simp
  have hne : masses.Nonempty := ⟨0, hzero⟩
  obtain ⟨s, hs, hsum⟩ := (Finset.mem_filter.mp (Finset.max'_mem masses hne)).2
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hcard : (t.biUnion X).card = ∑ a ∈ t, (X a).card := by
    apply Finset.card_biUnion
    intro a ha b hb hab
    exact (ht ha hb hab).1
  have hbound : ∑ a ∈ t, (X a).card ≤ N := by
    rw [← hcard]
    exact (Finset.card_le_univ _).trans (by simp)
  have hmem : (∑ a ∈ t, (X a).card) ∈ masses := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), t, ht, rfl⟩
  rw [hsum]
  exact Finset.le_max' masses _ hmem

end HypercubeRamsey.Lane_sol_s13_allocA
