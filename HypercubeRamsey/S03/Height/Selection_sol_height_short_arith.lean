import HypercubeRamsey.S03.Height.Selection_sol_height_short

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_height_short

open OAI.HypercubeRamsey Lane_p_height_main Lane_opus_height
open scoped BigOperators

theorem power_absorb (C e f : ℝ) (hef : e < f) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ e ≤ (n : ℝ) ^ f := by
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge (e := f - e) (C := C) (sub_pos.mpr hef)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    C * (n : ℝ) ^ e ≤ (n : ℝ) ^ (f - e) * (n : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (hN n (le_of_max_le_right hn))
        (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ f := by rw [← Real.rpow_add hnpos]; congr 1; ring

theorem multiplier_le (n : ℕ) (σ : ℝ) (hn : 1 ≤ n) (hσ : 0 ≤ σ) :
    (hdScaleMultiplier n σ : ℝ) ≤ 3 * (n : ℝ) ^ σ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ σ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hσ
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) σ)).le
  have hm : (max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ 3 * (n : ℝ) ^ σ :=
    max_le (by nlinarith) (by nlinarith)
  simpa [hdScaleMultiplier] using hm

theorem radius_one (n : ℕ) (σ : ℝ) (i : ℕ) : 1 ≤ hdScaleRadius n σ i := by
  apply Nat.one_le_iff_ne_zero.mpr
  unfold hdScaleRadius
  exact Nat.mul_ne_zero (pow_ne_zero _ (by unfold hdScaleMultiplier; omega))
    (by unfold heightBaseRadius; omega)

theorem radius_le_n (n : ℕ) (σ ζ : ℝ) (hn : 1 ≤ n) (hζ : 0 ≤ ζ)
    (i : ℕ) (hi : i < hdScaleIndex n σ ζ) : hdScaleRadius n σ i ≤ n := by
  have ht : ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (show 1 - ζ ≤ 1 by linarith)
  exact ((hdScaleIndex_spec n σ ζ).2 i hi).le.trans ht

theorem top_lower (n : ℕ) (σ ζ : ℝ) :
    (n : ℝ) ^ (1 - ζ) ≤ (topScale n σ ζ : ℝ) := by
  have ht := (hdScaleIndex_spec n σ ζ).1
  rw [← topScale_eq_hdScaleRadius] at ht
  exact (Nat.le_ceil _).trans (by exact_mod_cast ht)

theorem ceil_power_bounds (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (hα : 0 ≤ α) :
    1 ≤ (⌈(n : ℝ) ^ α⌉₊ : ℝ) ∧
    (n : ℝ) ^ α ≤ (⌈(n : ℝ) ^ α⌉₊ : ℝ) ∧
    (⌈(n : ℝ) ^ α⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ α := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ α := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hα
  have hc := Nat.le_ceil ((n : ℝ) ^ α)
  exact ⟨hp.trans hc, hc, Nat.ceil_le_two_mul (by linarith : (2 : ℝ)⁻¹ ≤ (n : ℝ) ^ α)⟩

theorem fifth_le_two_n (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (hα : 0 ≤ α) (hα5 : α ≤ 5) :
    (⌈(n : ℝ) ^ α⌉₊ : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 * n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ) / 5 ≤ 1)
  have hpow : ((n : ℝ) ^ α) ^ ((1 : ℝ) / 5) ≤ n := by
    rw [← Real.rpow_mul hn0]
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (show α * (1 / 5) ≤ 1 by linarith)
  calc
    _ ≤ (2 * (n : ℝ) ^ α) ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (ceil_power_bounds n α hn hα).2.2 (by norm_num)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 5) * ((n : ℝ) ^ α) ^ ((1 : ℝ) / 5) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hn0 α)
    _ ≤ 2 * n := mul_le_mul htwo hpow (by positivity) (by norm_num)

theorem cutoff_fifth (m M R : ℕ) (θ : ℝ) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hθ : (2 : ℝ) / 5 ≤ θ) (hq : Nat.sqrt m < 2 * M * R) :
    (m : ℝ) ^ ((1 : ℝ) / 5) ≤ 2 * M * (R : ℝ) ^ θ := by
  have hq1 : Nat.sqrt m + 1 ≤ 2 * M * R := by omega
  have hm : m ≤ (2 * M * R) ^ 2 :=
    (Nat.lt_succ_sqrt' m).le.trans (Nat.pow_le_pow_left hq1 2)
  have hmR : (m : ℝ) ≤ (2 * (M : ℝ) * (R : ℝ)) ^ 2 := by exact_mod_cast hm
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have htwo : (2 : ℝ) ^ ((2 : ℝ) / 5) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) / 5 ≤ 1)
  have hMp : (M : ℝ) ^ ((2 : ℝ) / 5) ≤ M := by
    simpa using Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num : (2 : ℝ) / 5 ≤ 1)
  have hRp : (R : ℝ) ^ ((2 : ℝ) / 5) ≤ (R : ℝ) ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hR1 hθ
  calc
    _ ≤ ((2 * (M : ℝ) * (R : ℝ)) ^ 2) ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (Nat.cast_nonneg m) hmR (by norm_num)
    _ = (2 * (M : ℝ) * (R : ℝ)) ^ ((2 : ℝ) / 5) := by
      rw [← Real.rpow_natCast_mul (by positivity) 2]
      norm_num
    _ = ((2 : ℝ) ^ ((2 : ℝ) / 5) * (M : ℝ) ^ ((2 : ℝ) / 5)) *
        (R : ℝ) ^ ((2 : ℝ) / 5) := by
      rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg R),
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg M)]
    _ ≤ (2 * (M : ℝ)) * (R : ℝ) ^ θ :=
      mul_le_mul (mul_le_mul htwo hMp (by positivity) (by norm_num)) hRp
        (by positivity) (by positivity)

theorem base_radius_power_eventually (e : ℝ) (he : 0 < e) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (heightBaseRadius n : ℝ) ≤ (n : ℝ) ^ e := by
  obtain ⟨Nb, hb⟩ := heightBaseRadius_le_logsq
  obtain ⟨Nl, hl⟩ := log_le_rpow_eventually (e / 4) (by positivity)
  obtain ⟨Np, hp⟩ := power_absorb 2 (e / 2) e (by linarith)
  refine ⟨max 2 (max Nb (max Nl Np)), ?_⟩
  intro n hn
  have hs := hn
  simp only [max_le_iff] at hs
  obtain ⟨hn2, hNb, hNl, hNp⟩ := hs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc
    (heightBaseRadius n : ℝ) ≤ 2 * Real.log (n : ℝ) ^ 2 := hb n hNb
    _ ≤ 2 * ((n : ℝ) ^ (e / 4)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg hn1) (hl n hNl) 2)
        (by norm_num)
    _ = 2 * (n : ℝ) ^ (e / 2) := by
      rw [← Real.rpow_mul_natCast hn0 (e / 4) 2]
      congr 2
      ring
    _ ≤ (n : ℝ) ^ e := hp n hNp

theorem short_radius_bounds_eventually (σ ζ α : ℝ) (hα : 0 < α ∧ α < 2 * (1 - ζ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nat.sqrt ⌈(n : ℝ) ^ α⌉₊ ≤ 2 * topScale n σ ζ ∧
      2 * heightBaseRadius n ≤ Nat.sqrt ⌈(n : ℝ) ^ α⌉₊ := by
  obtain ⟨Nb, hb⟩ := base_radius_power_eventually (α / 4) (by linarith [hα.1])
  obtain ⟨Np, hp⟩ := power_absorb 4 (α / 2) α (by linarith [hα.1])
  refine ⟨max 2 (max Nb Np), ?_⟩
  intro n hn
  have hs := hn
  simp only [max_le_iff] at hs
  obtain ⟨hn2, hNb, hNp⟩ := hs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let m := ⌈(n : ℝ) ^ α⌉₊
  have hm := ceil_power_bounds n α (by omega) hα.1.le
  have hpow : (n : ℝ) ^ α ≤ ((n : ℝ) ^ (1 - ζ)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hn0 (1 - ζ) 2]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith [hα.2])
  have hsq : (Nat.sqrt m : ℝ) ^ 2 ≤ (m : ℝ) := by
    exact_mod_cast Nat.sqrt_le' m
  have htopSq : ((n : ℝ) ^ (1 - ζ)) ^ 2 ≤ (topScale n σ ζ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) (top_lower n σ ζ) 2
  constructor
  · have hqSq : (Nat.sqrt m : ℝ) ^ 2 ≤ (2 * (topScale n σ ζ : ℝ)) ^ 2 := by
      nlinarith [hm.2.2, sq_nonneg (topScale n σ ζ : ℝ)]
    have hq : (Nat.sqrt m : ℝ) ≤ 2 * (topScale n σ ζ : ℝ) :=
      (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp hqSq
    exact_mod_cast hq
  · have hbSq : (2 * (heightBaseRadius n : ℝ)) ^ 2 ≤ (m : ℝ) := by
      calc
        (2 * (heightBaseRadius n : ℝ)) ^ 2 = 4 * (heightBaseRadius n : ℝ) ^ 2 := by ring
        _ ≤ 4 * ((n : ℝ) ^ (α / 4)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hb n hNb) 2)
            (by norm_num)
        _ = 4 * (n : ℝ) ^ (α / 2) := by
          rw [← Real.rpow_mul_natCast hn0 (α / 4) 2]
          congr 2
          ring
        _ ≤ (n : ℝ) ^ α := hp n hNp
        _ ≤ (m : ℝ) := hm.2.1
    apply Nat.le_sqrt'.mpr
    exact_mod_cast hbSq

theorem power_exp_bound (x : ℝ) (k : ℕ) (A T : ℝ) (hx : 0 < x)
    (h : (k : ℝ) * Real.log x - A ≤ -T) :
    x ^ k * Real.exp (-A) ≤ Real.exp (-T) := by
  have hp : x ^ k = Real.exp ((k : ℝ) * Real.log x) := by
    rw [← Real.log_pow]
    exact (Real.exp_log (pow_pos hx k)).symm
  calc
    _ = Real.exp ((k : ℝ) * Real.log x - A) := by rw [hp, ← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr h

theorem entropy_eventually (D : ℕ) (C_d σ ζ a θ : ℝ)
    (hCd : 0 ≤ C_d) (hσ : 0 ≤ σ) (hζ : 0 ≤ ζ) (hθ : θ ≤ 1)
    (hgap : σ + (1 - θ) < a) :
    ∃ N : ℕ, ∀ n d : ℕ, N ≤ n → (d : ℝ) ≤ C_d * n →
      ∀ i : ℕ, i < hdScaleIndex n σ ζ →
        ((D * hdScaleRadius n σ (i + 1) : ℕ) : ℝ) * Real.log ((d + 1 : ℕ) : ℝ) ≤
          ((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ) / 2 := by
  let δ := (a - σ - (1 - θ)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Nl, hl⟩ := log_le_rpow_eventually δ hδ
  obtain ⟨Nc, hc⟩ := exists_nat_rpow_ge (e := δ) (C := Real.log (C_d + 1)) hδ
  obtain ⟨Np, hp⟩ := power_absorb (12 * (D : ℝ)) (σ + δ + (1 - θ)) a
    (by dsimp [δ]; linarith)
  refine ⟨max 2 (max Nl (max Nc Np)), ?_⟩
  intro n d hn hd i hi
  have hs := hn
  simp only [max_le_iff] at hs
  obtain ⟨hn2, hNl, hNc, hNp⟩ := hs
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let M := hdScaleMultiplier n σ
  let R := hdScaleRadius n σ i
  have hM : (M : ℝ) ≤ 3 * (n : ℝ) ^ σ := multiplier_le n σ hn1 hσ
  have hR : (R : ℝ) ≤ n := by exact_mod_cast radius_le_n n σ ζ hn1 hζ i hi
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (radius_one n σ i)
  have hdp : ((d + 1 : ℕ) : ℝ) ≤ (C_d + 1) * n := by push_cast; nlinarith
  have hlog : Real.log ((d + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ δ := by
    calc
      _ ≤ Real.log ((C_d + 1) * n) := Real.log_le_log (by positivity) hdp
      _ = Real.log (C_d + 1) + Real.log (n : ℝ) := by
        rw [Real.log_mul (by linarith) hnpos.ne']
      _ ≤ _ := by linarith [hl n hNl, hc n hNc]
  have hRp : (R : ℝ) ^ (1 - θ) ≤ (n : ℝ) ^ (1 - θ) :=
    Real.rpow_le_rpow hRpos.le hR (by linarith)
  have hRfac : (R : ℝ) ≤ (n : ℝ) ^ (1 - θ) * (R : ℝ) ^ θ := by
    calc
      (R : ℝ) = (R : ℝ) ^ (1 - θ) * (R : ℝ) ^ θ := by
        rw [← Real.rpow_add hRpos]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hRp (Real.rpow_nonneg hRpos.le _)
  calc
    _ = (D : ℝ) * (M : ℝ) * (R : ℝ) * Real.log ((d + 1 : ℕ) : ℝ) := by
      rw [hdScaleRadius_succ]
      simp only [Nat.cast_mul]
      dsimp [M, R]
      ring
    _ ≤ (D : ℝ) * (3 * (n : ℝ) ^ σ) * (R : ℝ) * (2 * (n : ℝ) ^ δ) := by
      gcongr
    _ = 6 * (D : ℝ) * (n : ℝ) ^ (σ + δ) * (R : ℝ) := by
      rw [Real.rpow_add hnpos]
      ring
    _ ≤ 6 * (D : ℝ) * (n : ℝ) ^ (σ + δ) *
        ((n : ℝ) ^ (1 - θ) * (R : ℝ) ^ θ) :=
      mul_le_mul_of_nonneg_left hRfac (by positivity)
    _ = (12 * (D : ℝ) * (n : ℝ) ^ (σ + δ + (1 - θ))) * (R : ℝ) ^ θ / 2 := by
      simp only [Real.rpow_add hnpos]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hp n hNp) (Real.rpow_nonneg hRpos.le _)) (by norm_num)

theorem intermediate_budget_eventually (D : ℕ) (C_d σ ζ a θ L : ℝ)
    (hCd : 0 ≤ C_d) (hσ : 0 ≤ σ) (hζ : 0 ≤ ζ)
    (hθ : (2 : ℝ) / 5 ≤ θ ∧ θ ≤ 1) (hgap : σ + (1 - θ) < a) (hL : 0 ≤ L) :
    ∃ N : ℕ, ∀ n d m : ℕ, N ≤ n → (d : ℝ) ≤ C_d * n →
      ∀ i : ℕ, i < hdScaleIndex n σ ζ → Nat.sqrt m < 2 * hdScaleRadius n σ (i + 1) →
        ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
          Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) ≤
            Real.exp (-L * (m : ℝ) ^ ((1 : ℝ) / 5)) := by
  obtain ⟨Ne, he⟩ := entropy_eventually D C_d σ ζ a θ hCd hσ hζ hθ.2 hgap
  obtain ⟨Np, hp⟩ := power_absorb (12 * L) σ a (by linarith [hθ.2])
  refine ⟨max 2 (max Ne Np), ?_⟩
  intro n d m hn hd i hi hcut
  have hs := hn
  simp only [max_le_iff] at hs
  obtain ⟨hn2, hNe, hNp⟩ := hs
  let M := hdScaleMultiplier n σ
  let R := hdScaleRadius n σ i
  have hM1 : 1 ≤ M := by dsimp [M, hdScaleMultiplier]; omega
  have hR1 : 1 ≤ R := radius_one n σ i
  have hcut' : Nat.sqrt m < 2 * M * R := by
    simpa only [hdScaleRadius_succ, Nat.mul_assoc] using hcut
  have hM := multiplier_le n σ (by omega : 1 ≤ n) hσ
  have hy : (m : ℝ) ^ ((1 : ℝ) / 5) ≤ 6 * (n : ℝ) ^ σ * (R : ℝ) ^ θ := by
    calc
      _ ≤ 2 * (M : ℝ) * (R : ℝ) ^ θ := cutoff_fifth m M R θ hM1 hR1 hθ.1 hcut'
      _ ≤ 2 * (3 * (n : ℝ) ^ σ) * (R : ℝ) ^ θ := by gcongr
      _ = _ := by ring
  have hbig : 2 * L * (m : ℝ) ^ ((1 : ℝ) / 5) ≤ (n : ℝ) ^ a * (R : ℝ) ^ θ := by
    calc
      _ ≤ 2 * L * (6 * (n : ℝ) ^ σ * (R : ℝ) ^ θ) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ = (12 * L * (n : ℝ) ^ σ) * (R : ℝ) ^ θ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hp n hNp) (by positivity)
  rw [neg_mul]
  apply power_exp_bound _ _ _ (L * (m : ℝ) ^ ((1 : ℝ) / 5)) (by positivity)
  have hent := he n d hNe hd i hi
  change _ ≤ -(L * (m : ℝ) ^ ((1 : ℝ) / 5))
  linarith

theorem top_budget_eventually (C_d σ ζ a θ α L : ℝ) (_hCd : 0 ≤ C_d)
    (hθ : 0 ≤ θ) (hgap : 1 < a + (1 - ζ) * θ)
    (hα : 0 ≤ α ∧ α ≤ 5) (hL : 0 ≤ L) :
    ∃ N : ℕ, ∀ n d : ℕ, N ≤ n → (d : ℝ) ≤ C_d * n →
      (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ)) ≤
        Real.exp (-L * (⌈(n : ℝ) ^ α⌉₊ : ℝ) ^ ((1 : ℝ) / 5)) := by
  obtain ⟨Np, hp⟩ := power_absorb (C_d * Real.log 2 + 2 * L) 1
    (a + (1 - ζ) * θ) hgap
  refine ⟨max 2 Np, ?_⟩
  intro n d hn hd
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hy := fifth_le_two_n n α hn1 hα.1 hα.2
  have hpow : (n : ℝ) ^ (a + (1 - ζ) * θ) ≤
      (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ := by
    calc
      _ = (n : ℝ) ^ a * ((n : ℝ) ^ (1 - ζ)) ^ θ := by
        rw [Real.rpow_add hnpos, Real.rpow_mul hnpos.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) (top_lower n σ ζ) hθ)
        (Real.rpow_nonneg hnpos.le _)
  have hsum : (d : ℝ) * Real.log 2 +
      L * (⌈(n : ℝ) ^ α⌉₊ : ℝ) ^ ((1 : ℝ) / 5) ≤
        (n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ := by
    calc
      _ ≤ (C_d * n) * Real.log 2 + L * (2 * n) :=
        add_le_add (mul_le_mul_of_nonneg_right hd hlog2)
          (mul_le_mul_of_nonneg_left hy hL)
      _ = (C_d * Real.log 2 + 2 * L) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
      _ ≤ (n : ℝ) ^ (a + (1 - ζ) * θ) := hp n (le_of_max_le_right hn)
      _ ≤ _ := hpow
  rw [neg_mul]
  apply power_exp_bound 2 d _ (L * (⌈(n : ℝ) ^ α⌉₊ : ℝ) ^ ((1 : ℝ) / 5)) (by norm_num)
  linarith

/-- The filtered scale sum fits the stretched-exponential error budget. -/
theorem short_error_eventually (J₀ b₀ b σ ζ θ a c_d C_d α : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D)
    (hθ : 0.9 < θ) (hα : 0 < α ∧ α < 2 * (1 - ζ)) :
    ∃ N : ℕ, ∀ n d : ℕ, N ≤ n → (d : ℝ) ≤ C_d * n →
      shortErrorBound n d D ⌈(n : ℝ) ^ α⌉₊ σ ζ a θ ≤
        Real.exp (-3 * (⌈(n : ℝ) ^ α⌉₊ : ℝ) ^ ((1 : ℝ) / 5)) := by
  classical
  have hσ : 0 < σ := hp.hsz.1
  have hζ : 0 < ζ := hσ.trans hp.hsz.2.1
  have hζ1 : ζ < 1 := hp.hsz.2.2.1
  have hθ0 : 0 < θ := hp.hsz.2.2.2.1
  have hθ1 : θ < 1 := hp.hsz.2.2.2.2
  have hCd : 0 ≤ C_d := (hp.hd.1.trans_le hp.hd.2).le
  have hgap : σ + (1 - θ) < a := by linarith [hp.ha.1]
  have hgapTop : 1 < a + (1 - ζ) * θ := by
    have hprod : 0 ≤ ζ * (1 - θ) := mul_nonneg hζ.le (by linarith)
    nlinarith [hp.ha.1]
  let B : ℕ := ⌈1 / σ⌉₊
  let L : ℝ := 3 + Real.log ((B + 1 : ℕ) : ℝ)
  have hB1 : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ B + 1 by omega)
  have hlogB : 0 ≤ Real.log ((B + 1 : ℕ) : ℝ) := Real.log_nonneg hB1
  have hL : 0 ≤ L := by dsimp [L]; linarith
  obtain ⟨Nm, hm⟩ := intermediate_budget_eventually D C_d σ ζ a θ L
    hCd hσ.le hζ.le ⟨by linarith, hθ1.le⟩ hgap hL
  obtain ⟨Nt, ht⟩ := top_budget_eventually C_d σ ζ a θ α L hCd hθ0.le hgapTop
    ⟨hα.1.le, by linarith [hα.2]⟩ hL
  refine ⟨max 2 (max Nm Nt), ?_⟩
  intro n d hn hd
  have hs := hn
  simp only [max_le_iff] at hs
  obtain ⟨hn2, hNm, hNt⟩ := hs
  let m := ⌈(n : ℝ) ^ α⌉₊
  let y := (m : ℝ) ^ ((1 : ℝ) / 5)
  let I := (Finset.range (hdScaleIndex n σ ζ)).filter
    (fun i => Nat.sqrt m < 2 * hdScaleRadius n σ (i + 1))
  have hy : 1 ≤ y := by
    have hm1 := (ceil_power_bounds n α (by omega) hα.1.le).1
    simpa [y, m] using Real.rpow_le_rpow_of_exponent_le hm1
      (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hidx : hdScaleIndex n σ ζ ≤ B :=
    hdScaleIndex_le_ceil_inv_sigma hn2 hσ ⟨hζ, hζ1⟩
  have hcard : I.card ≤ B := by
    calc
      I.card ≤ (Finset.range (hdScaleIndex n σ ζ)).card := Finset.card_filter_le _ _
      _ = hdScaleIndex n σ ζ := Finset.card_range _
      _ ≤ B := hidx
  have hterms : ∀ i ∈ I,
      ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
        Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) ≤ Real.exp (-L * y) := by
    intro i hi
    obtain ⟨hi, hcut⟩ := Finset.mem_filter.mp hi
    exact hm n d m hNm hd i (Finset.mem_range.mp hi) hcut
  have hlast := ht n d hNt hd
  have hco : ((I.card : ℝ) + 1) ≤ ((B + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hcard
  have hlog : Real.log ((B + 1 : ℕ) : ℝ) - L * y ≤ -3 * y := by
    have hb := mul_le_mul_of_nonneg_left hy hlogB
    dsimp [L]
    nlinarith
  calc
    shortErrorBound n d D m σ ζ a θ ≤ (∑ _i ∈ I, Real.exp (-L * y)) + Real.exp (-L * y) :=
      add_le_add (Finset.sum_le_sum hterms) hlast
    _ = ((I.card : ℝ) + 1) * Real.exp (-L * y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((B + 1 : ℕ) : ℝ) * Real.exp (-L * y) :=
      mul_le_mul_of_nonneg_right hco (Real.exp_pos _).le
    _ = Real.exp (Real.log ((B + 1 : ℕ) : ℝ) - L * y) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
      simp only [neg_mul]
    _ ≤ Real.exp (-3 * y) := Real.exp_le_exp.mpr hlog

end HypercubeRamsey.Lane_sol_height_short
