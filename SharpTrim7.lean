import HypercubeRamsey.S16.Producers_sol_s16_prod1
namespace HypercubeRamsey.S16.Lane_sol_s16_prod1
open Classical
open scoped BigOperators

theorem permission_retained_sharp7 {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hP : PermissionLossHypotheses P qin) (g : Group) :
    1 - Real.exp (-P.cperm * P.n / 2) ≤ ∑ b ∈ P.permitted g, (qin g).w b := by
  classical
  have hB : (0 : ℝ) < Fintype.card Bin := by
    letI := hP.bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hremoved : (∑ b ∈ Finset.univ \ P.permitted g, (qin g).w b) ≤
      Real.exp (-P.cperm * P.n / 2) := by
    calc
      _ ≤ ((Finset.univ \ P.permitted g).card : ℝ) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) := by
        simpa using Finset.sum_le_sum (s := Finset.univ \ P.permitted g)
          (fun b _ => hP.incoming_cap g b)
      _ ≤ (Real.exp (-P.cperm * P.n) * Fintype.card Bin) *
          (Real.exp (P.cperm * P.n / 2) / Fintype.card Bin) :=
        mul_le_mul_of_nonneg_right (permission_removed_count P qin hP g) (by positivity)
      _ = _ := by
        field_simp
        rw [← Real.exp_add]
        congr 1
        ring
  have hsplit := Finset.sum_sdiff (s₁ := P.permitted g) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := (qin g).w)
  rw [(qin g).sum_one] at hsplit
  linarith

/-- Two small normalization losses over at most h groups cost at most two. -/
theorem normalization_product_room7 (h m : ℕ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u < 1) (hv1 : v < 1)
    (hm : m ≤ h) (hsmall : (h : ℝ) * (u + v) ≤ 1 / 2) :
    1 ≤ ((1 - u) * (1 - v))⁻¹ ∧
      (((1 - u) * (1 - v))⁻¹) ^ m ≤ 2 := by
  have hbpos : 0 < (1 - u) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hbone : (1 - u) * (1 - v) ≤ 1 := by nlinarith [mul_nonneg hu (by linarith : 0 ≤ 1 - v)]
  have hbase : 1 - (u + v) ≤ (1 - u) * (1 - v) := by nlinarith [mul_nonneg hu hv]
  have hBern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ (1 - u) * (1 - v)) m
  have hm' : (m : ℝ) ≤ h := by exact_mod_cast hm
  have hlin : (m : ℝ) * (u + v) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hm' (add_nonneg hu hv)).trans hsmall
  have hpow : (1 / 2 : ℝ) ≤ ((1 - u) * (1 - v)) ^ m := by
    have hb := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg m)
    nlinarith only [hBern, hb, hlin]
  constructor
  · exact (one_le_inv₀ hbpos).mpr hbone
  · rw [inv_pow]
    calc
      _ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpow
      _ = 2 := by norm_num

theorem low_cluster_pretrim_power_small7 {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hm : PT.tiling.mode = .lowCluster)
    (i : Fin PT.tiling.m) (m : ℕ) (hm6 : m ≤ 6) :
    ((PT.tiling.P i).h : ℝ) ^ m * Real.sqrt (sliceEps κ (PT.tiling.P i).h) ≤ Real.rpow 10 (-3) := by
  obtain ⟨hscale, hg, _, _, _, _, _, hLower, hUpper, _, _, _⟩ :=
    Q.profiled_valid.tiling_valid.cluster_data (Or.inl hm) i
  simp only [hm, if_true] at hLower hUpper
  have hMlo : (0 : ℝ) < κ.Mlo := by
    have hh := hκ.Mlo_big
    have hb : (0 : ℝ) ≤ κ.Cb := by
      have hc := hκ.Cb_big
      have hp : 0 < 100 * κ.aC / κ.aB :=
        div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
      linarith
    linarith
  have hq1 : (1 : ℝ) ≤ (PT.tiling.P i).q := by
    have hq : (PT.tiling.P i).q ≠ 0 := by
      intro hz
      have hzpow : Real.rpow (0 : ℝ) (κ.Mlo : ℝ) = 0 := by
        simpa only [Real.rpow_eq_pow] using Real.zero_rpow hMlo.ne'
      rw [hz, Nat.cast_zero, hzpow, mul_zero] at hUpper
      exact not_lt_of_ge (Nat.cast_nonneg _) hUpper
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
    have hh := hκ.Mhi_big.1
    have hp : (0 : ℝ) < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    linarith
  have hmax : max ((PT.tiling.P i).g : ℝ) (PT.tiling.P i).q ≤ κ.M1 * (PT.tiling.P i).q := by
    apply max_le hg
    have hh := hκ.M1_big.1
    nlinarith
  have hq0 : κ.Q0 ≤ (PT.tiling.P i).q := by
    have hh : (κ.M1 : ℝ) * κ.Q0 ≤ κ.M1 * (PT.tiling.P i).q := by
      exact hscale.trans (by exact_mod_cast hmax)
    nlinarith [hκ.M1_big.1]
  have hUpper' : ((PT.tiling.P i).h : ℝ) < 2 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mhi :=
    hUpper.trans_le (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 hMhi) (by norm_num))
  obtain ⟨_, _, _, _, _, _, _, _, hall⟩ := hκ.Q0_large (PT.tiling.P i).q hq0
  have hs := (hall (PT.tiling.P i).h hLower hUpper').2.2.2.2.2.1
  have hh1 : (1 : ℝ) ≤ (PT.tiling.P i).h :=
    (Real.one_le_rpow hq1 hMlo.le).trans hLower
  have hpow := pow_le_pow_right₀ hh1 hm6
  calc
    _ ≤ ((PT.tiling.P i).h : ℝ) ^ 6 * Real.sqrt (sliceEps κ (PT.tiling.P i).h) :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
    _ ≤ Real.rpow 10 (-3) := hs


theorem cluster_permission_cost_room7 {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ n h : ℕ, n₀ ≤ n → 2 ≤ n → h ≤ n →
      (h : ℝ) * Real.exp (-κ.cperm * n / 2) ≤ 1 / 4 := by
  obtain ⟨n₀, hroom⟩ := logarithmic_room 1 (κ.cperm / 2)
    (Real.log 4) 1 (by norm_num) (div_pos hκ.cperm_rng.1 (by norm_num)) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n h hn hn2 hh
  have hnp : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hx := hroom n hn
  simp only [Real.rpow_one, one_mul] at hx
  have he : Real.exp (-κ.cperm * n / 2) ≤ 1 / (4 * (n : ℝ)) := by
    calc
      _ ≤ Real.exp (-(Real.log 4 + Real.log (n : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log hnp]
        simp only [one_div]
  have hh' : (h : ℝ) ≤ n := by exact_mod_cast hh
  calc
    _ ≤ (n : ℝ) * (1 / (4 * (n : ℝ))) :=
      mul_le_mul hh' he (Real.exp_pos _).le (Nat.cast_nonneg n)
    _ = _ := by field_simp

end HypercubeRamsey.S16.Lane_sol_s16_prod1

