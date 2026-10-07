import HypercubeRamsey.S07.AnchorStage_q_s07_anchor

namespace HypercubeRamsey.S07

open Filter Real
open scoped Topology

theorem odd_loads_small_q_s07_anchor (d : ℝ) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
        (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) * cellCap d n (gS d n) ≤ 1 := by
  let c : ℝ := 9 * d / 80
  let A : ℝ := 1 / d + 2
  let x : ℕ → ℝ := fun n => (n : ℝ) ^ d
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hXT : Tendsto x atTop atTop := by
    dsimp [x]
    exact (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrootEq : (fun n : ℕ => (n : ℝ) ^ (d / 2) / (n : ℝ) ^ d) =ᶠ[atTop]
      fun n => (n : ℝ) ^ (-(d / 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hnpos), ← Real.rpow_add hnpos]
    congr 1
    ring
  have hrootT : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (d / 2) / (n : ℝ) ^ d) atTop (𝓝 0) := by
    apply (tendsto_congr' hrootEq).mpr
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < d / 2)).comp
      tendsto_natCast_atTop_atTop
  have hinvEq : (fun n : ℕ => 1 / x n) =ᶠ[atTop]
      fun n => (n : ℝ) ^ (-d) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [x]
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hnpos)]
    simp
  have hinvT : Tendsto (fun n : ℕ => 1 / x n) atTop (𝓝 0) := by
    apply (tendsto_congr' hinvEq).mpr
    exact (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
  have hrootSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (d / 2) < (c / 4) * x n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hrootT.eventually (Iio_mem_nhds (by positivity : c / 4 > 0))]
      with n hn hnSmall
    have hx : 0 < x n := by dsimp [x]; positivity
    exact (div_lt_iff₀ hx).mp hnSmall
  have honeSmall : ∀ᶠ n : ℕ in atTop, 1 < (c / 4) * x n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hinvT.eventually (Iio_mem_nhds (by positivity : c / 4 > 0))]
      with n hn hnSmall
    have hx : 0 < x n := by dsimp [x]; positivity
    exact (div_lt_iff₀ hx).mp hnSmall
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    hlogT.eventually (eventually_ge_atTop (1 : ℝ))
  have hlogTwo : ∀ᶠ n : ℕ in atTop,
      (80 / (9 * d) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) :=
    hlogT.eventually (eventually_ge_atTop ((80 / (9 * d : ℝ)) * Real.log 2))
  have hSbounds : ∀ᶠ n : ℕ in atTop,
      x n ≤ (gS d n : ℝ) ∧ (gS d n : ℝ) ≤ 2 * x n ∧ 1 ≤ x n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hpow : 1 < x n := Real.one_lt_rpow hnreal hd
    have hceil : (gS d n : ℝ) < x n + 1 := by
      dsimp [gS, x]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) d)
    have hceilLower : x n ≤ (gS d n : ℝ) := by
      dsimp [gS, x]
      exact_mod_cast Nat.le_ceil ((n : ℝ) ^ d)
    refine ⟨hceilLower, ?_, le_of_lt hpow⟩
    nlinarith
  have hpoly : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 ≤
        25 * (n : ℝ) ^ (1 + 2 * d) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hSbounds] with n hn hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hbase : ((2 * gS d n + 1 : ℕ) : ℝ) ≤ 5 * x n := by
      push_cast
      rcases hs with ⟨_, hsUpper, hsOne⟩
      dsimp [x] at *
      nlinarith [hsUpper, hsOne]
    have hbaseSq : (((2 * gS d n + 1 : ℕ) : ℝ) ^ 2) ≤ (5 * x n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    have hpow2 : ((n : ℝ) ^ d) ^ 2 = (n : ℝ) ^ (2 * d) := by
      calc
        ((n : ℝ) ^ d) ^ 2 = ((n : ℝ) ^ d) ^ (2 : ℝ) :=
          (Real.rpow_natCast ((n : ℝ) ^ d) 2).symm
        _ = (n : ℝ) ^ (d * 2) := (Real.rpow_mul (le_of_lt hnpos) d (2 : ℝ)).symm
        _ = (n : ℝ) ^ (2 * d) := by congr 1 <;> ring
    calc
      (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 ≤
          (n : ℝ) * (5 * x n) ^ 2 := mul_le_mul_of_nonneg_left hbaseSq (by positivity)
      _ = 25 * (n : ℝ) ^ (1 + 2 * d) := by
        calc
          (n : ℝ) * (5 * x n) ^ 2 = 25 * ((n : ℝ) * (x n) ^ 2) := by ring
          _ = 25 * (n : ℝ) ^ (1 + 2 * d) := by
            dsimp [x]
            calc
              25 * ((n : ℝ) * ((n : ℝ) ^ d) ^ 2) =
                  25 * ((n : ℝ) * (n : ℝ) ^ (2 * d)) := by rw [hpow2]
              _ = 25 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 * d)) := by rw [Real.rpow_one]
              _ = 25 * (n : ℝ) ^ (1 + 2 * d) := by rw [← Real.rpow_add hnpos]
  have hcombined (n : ℕ) (hn : 2 ≤ n) :
      (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) *
          Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ)) =
        Real.exp ((gS d n : ℝ) * (Real.log 2 - (9 * d / 40) * Real.log (n : ℝ))) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hbasepos : 0 < 2 * (n : ℝ) ^ (-(d / 4)) := by positivity
    have hpow : (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) =
        Real.exp ((gS d n : ℝ) * Real.log (2 * (n : ℝ) ^ (-(d / 4)))) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbasepos]
      congr 1
      ring
    have hlog : Real.log (2 * (n : ℝ) ^ (-(d / 4))) =
        Real.log 2 + (-(d / 4)) * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hnpos _)),
        Real.log_rpow hnpos]
    rw [hpow, hlog, ← Real.exp_add]
    congr 1
    ring
  have hcombinedSmall : ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) *
          Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ)) ≤
        Real.exp (-c * x n) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hSbounds, hlogOne, hlogTwo]
      with n hn hs hln hlo
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogbound : Real.log 2 ≤ c * Real.log (n : ℝ) := by
      dsimp [c]
      calc
        Real.log 2 = (9 * d / 80) * ((80 / (9 * d)) * Real.log 2) := by
          field_simp [ne_of_gt hd]
        _ ≤ (9 * d / 80) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
    have hsNonneg : 0 ≤ (gS d n : ℝ) := Nat.cast_nonneg _
    have hslog : x n ≤ (gS d n : ℝ) * Real.log (n : ℝ) := by
      rcases hs with ⟨hsLower, _, _⟩
      calc
        x n = x n * 1 := by ring
        _ ≤ (gS d n : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul hsLower hln (by positivity) (by positivity)
    have hexp :
        (gS d n : ℝ) * (Real.log 2 - (9 * d / 40) * Real.log (n : ℝ)) ≤ -c * x n := by
      have hcoeff : Real.log 2 - (9 * d / 40) * Real.log (n : ℝ) ≤
          -c * Real.log (n : ℝ) := by
        calc
          Real.log 2 - (9 * d / 40) * Real.log (n : ℝ) ≤
              (9 * d / 80) * Real.log (n : ℝ) -
                (9 * d / 40) * Real.log (n : ℝ) :=
            sub_le_sub_right hlogbound _
          _ = -(9 * d / 80) * Real.log (n : ℝ) := by ring
          _ = -c * Real.log (n : ℝ) := by dsimp [c]
      calc
        (gS d n : ℝ) * (Real.log 2 - (9 * d / 40) * Real.log (n : ℝ)) ≤
            (gS d n : ℝ) * (-c * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hcoeff hsNonneg
        _ = -c * ((gS d n : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ -c * x n :=
          mul_le_mul_of_nonpos_left hslog (by linarith [hc])
    rw [hcombined n hn]
    exact Real.exp_le_exp.mpr hexp
  have hxA (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ) ^ (1 + 2 * d) = x n ^ A := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpow : d * A = 1 + 2 * d := by
      dsimp [A]
      field_simp [ne_of_gt hd]
    calc
      (n : ℝ) ^ (1 + 2 * d) = (n : ℝ) ^ (d * A) := by rw [hpow]
      _ = ((n : ℝ) ^ d) ^ A := Real.rpow_mul (le_of_lt hnpos) d A
      _ = x n ^ A := by rfl
  have hExpoT : Tendsto (fun n : ℕ => (25 : ℝ) * x n ^ A *
      Real.exp (-(c / 2) * x n)) atTop (𝓝 0) := by
    have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A (c / 2)
      (by positivity : 0 < c / 2)).comp hXT
    have hmult := (tendsto_const_nhds (x := (25 : ℝ))).mul hbase
    simpa [mul_assoc] using hmult
  have hExpoSmall : ∀ᶠ n : ℕ in atTop,
      (25 : ℝ) * x n ^ A * Real.exp (-(c / 2) * x n) < 1 :=
    hExpoT.eventually (Iio_mem_nhds (by norm_num))
  have hAll : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ (n : ℝ) ^ (d / 2) + 1 ≤ (c / 2) * x n ∧
        (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 ≤
          25 * (n : ℝ) ^ (1 + 2 * d) ∧
        (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) *
          Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ)) ≤
            Real.exp (-c * x n) ∧
        (25 : ℝ) * x n ^ A * Real.exp (-(c / 2) * x n) < 1 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hrootSmall, honeSmall, hpoly,
      hcombinedSmall, hExpoSmall] with n hn hr ho hp hcmb he
    refine ⟨hn, ?_, hp, hcmb, he⟩
    dsimp [c] at hr ho ⊢
    nlinarith
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨hn2, hposExp, hpolyN, hcombinedN, hExpoN⟩ := hn₀ n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htargetEq :
      (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
          (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) * cellCap d n (gS d n) =
        (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
          Real.exp ((n : ℝ) ^ (d / 2) + 1) *
            ((2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) *
              Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ))) := by
    dsimp [cellCap]
    have hcoef : 2 * (d / 80) = d / 40 := by ring
    have hexp : Real.exp ((n : ℝ) ^ (d / 2) +
        (d / 40) * (gS d n : ℝ) * Real.log (n : ℝ) + 1) =
        Real.exp ((n : ℝ) ^ (d / 2) + 1) *
          Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcoef, hexp]
    ring_nf
  have hmainExp : Real.exp ((n : ℝ) ^ (d / 2) + 1) * Real.exp (-c * x n) ≤
      Real.exp (-(c / 2) * x n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hposExp]
  have hAeq := hxA n hn2
  rw [htargetEq]
  calc
    (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp ((n : ℝ) ^ (d / 2) + 1) *
          ((2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n) *
            Real.exp ((d / 40) * (gS d n : ℝ) * Real.log (n : ℝ))) ≤
      (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp ((n : ℝ) ^ (d / 2) + 1) * Real.exp (-c * x n) := by
          exact mul_le_mul_of_nonneg_left hcombinedN (by positivity)
    _ ≤ 25 * (n : ℝ) ^ (1 + 2 * d) * Real.exp (-(c / 2) * x n) := by
      calc
        (n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
            Real.exp ((n : ℝ) ^ (d / 2) + 1) * Real.exp (-c * x n) =
            ((n : ℝ) * ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2) *
              (Real.exp ((n : ℝ) ^ (d / 2) + 1) * Real.exp (-c * x n)) := by ring
        _ ≤ 25 * (n : ℝ) ^ (1 + 2 * d) * Real.exp (-(c / 2) * x n) :=
            mul_le_mul hpolyN hmainExp (by positivity) (by positivity)
    _ = (25 : ℝ) * x n ^ A * Real.exp (-(c / 2) * x n) := by rw [hAeq]
    _ ≤ 1 := le_of_lt hExpoN

end HypercubeRamsey.S07
