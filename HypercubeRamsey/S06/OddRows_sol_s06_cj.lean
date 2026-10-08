import HypercubeRamsey.S06.EvenRows_q_s06_ev_a

namespace HypercubeRamsey.S06.Lane_sol_s06_cj

open Classical Filter
open scoped BigOperators

theorem proxy_family_rate {n J T H k : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hJ : 20000000 ≤ J)
    (hT : (T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * J)
    (hlogT : Real.log (T + 2) ≤ 2 * α * Real.log n)
    (hH : H ≤ n ^ 4)
    (hk : κ₆ * (J : ℝ) * Real.log n ≤ k)
    (hα0 : 0 ≤ α)
    (hα : α ≤ 1 / 10 ^ 12) :
    (H : ℝ) * Real.exp (10 ^ 4 *
      (T * Real.log (3 * n * (4 * n ^ 10) + 2) +
        (J + 1) * Real.log (T + 2))) ≤ Real.exp ((2 / 100 : ℝ) * k) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have harg : (3 : ℝ) * n * (4 * (n : ℝ) ^ 10) + 2 ≤ 14 * (n : ℝ) ^ 11 := by
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 11 := by
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    nlinarith
  have hlogArg : Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤ 15 * Real.log n := by
    have hmon := Real.log_le_log (by positivity) harg
    have h14 : Real.log (14 : ℝ) ≤ 4 * Real.log 2 := by
      have h := Real.log_le_log (by norm_num) (by norm_num : (14 : ℝ) ≤ 2 ^ 4)
      rw [Real.log_pow] at h
      norm_num at h ⊢
      nlinarith
    have h2n : Real.log (2 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hmon
    have h14n : Real.log (14 : ℝ) ≤ 4 * Real.log n := by nlinarith [h14, h2n]
    have hsum : Real.log (14 : ℝ) + 11 * Real.log n ≤ 15 * Real.log n := by
      nlinarith [h14n]
    exact hmon.trans hsum
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJplus : (J : ℝ) + 1 ≤ 2 * J := by nlinarith
  have hTarg : (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
      (15 / 10 ^ 11 : ℝ) * J * Real.log n := by
    calc
      (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
          (T : ℝ) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_left hlogArg (by exact_mod_cast (Nat.zero_le T))
      _ ≤ ((1 / 10 ^ 11 : ℝ) * J) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_right hT (mul_nonneg (by norm_num) hlogn)
      _ = (15 / 10 ^ 11 : ℝ) * J * Real.log n := by ring
  have hTtail : ((J : ℝ) + 1) * Real.log (T + 2) ≤
      4 * α * J * Real.log n := by
    calc
      ((J : ℝ) + 1) * Real.log (T + 2) ≤ ((J : ℝ) + 1) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
      _ ≤ (2 * J) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_right hJplus
          (mul_nonneg (mul_nonneg (by norm_num) hα0) hlogn)
      _ = 4 * α * J * Real.log n := by ring
  have hS : 10 ^ 4 *
      ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
        ((J : ℝ) + 1) * Real.log (T + 2)) ≤ (18 / 1000 : ℝ) * k := by
    have hα' : 0 ≤ α := hα0
    have hJreal : (20000000 : ℝ) ≤ J := by exact_mod_cast hJ
    have hJlog : (20000000 : ℝ) * Real.log n ≤ J * Real.log n :=
      mul_le_mul_of_nonneg_right hJreal hlogn
    have hcoeff : 10 ^ 4 * (15 / 10 ^ 11 + 4 * α) ≤
        (18 / 1000 : ℝ) * κ₆ := by
      norm_num [κ₆] at hα ⊢
      nlinarith [hα]
    have hsumRate := add_le_add hTarg hTtail
    calc
      10 ^ 4 *
          ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
            ((J : ℝ) + 1) * Real.log (T + 2)) ≤
          10 ^ 4 * (15 / 10 ^ 11 * J * Real.log n + 4 * α * J * Real.log n) :=
            mul_le_mul_of_nonneg_left hsumRate (by norm_num)
      _ = 10 ^ 4 * ((15 / 10 ^ 11 + 4 * α) * J * Real.log n) := by ring
      _ = (10 ^ 4 * (15 / 10 ^ 11 + 4 * α)) * (J * Real.log n) := by ring
      _ ≤ ((18 / 1000 : ℝ) * κ₆) * (J * Real.log n) :=
            mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (by positivity) hlogn)
      _ ≤ (18 / 1000 : ℝ) * k := by
            have hk' := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 18 / 1000)
            nlinarith [hk']
  have hHexp : (H : ℝ) ≤ Real.exp ((2 / 1000 : ℝ) * k) := by
    have hHreal : (H : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hH
    have hexp : (n : ℝ) ^ 4 = Real.exp (4 * Real.log n) := by
      calc
        (n : ℝ) ^ 4 = (Real.exp (Real.log n)) ^ 4 := by rw [Real.exp_log hnpos]
        _ = Real.exp (4 * Real.log n) := by
          rw [← Real.exp_nat_mul (Real.log n) 4]
          norm_num
    have hlarge : 4 * Real.log n ≤ (2 / 1000 : ℝ) * k := by
      have hJreal : (20000000 : ℝ) ≤ J := by exact_mod_cast hJ
      have hJlog : (20000000 : ℝ) * Real.log n ≤ J * Real.log n :=
        mul_le_mul_of_nonneg_right hJreal hlogn
      have hk' := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2 / 1000)
      calc
        4 * Real.log n ≤ 4 * Real.log n := by nlinarith [hlogn]
        _ = ((2 / 1000 : ℝ) * κ₆) * ((20000000 : ℝ) * Real.log n) := by
          norm_num [κ₆]
          ring
        _ ≤ ((2 / 1000 : ℝ) * κ₆) * ((J : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_left hJlog (by norm_num [κ₆])
        _ = (2 / 1000 : ℝ) * (κ₆ * (J : ℝ) * Real.log n) := by ring
        _ ≤ (2 / 1000 : ℝ) * k := by nlinarith [hk']
    calc
      (H : ℝ) ≤ (n : ℝ) ^ 4 := hHreal
      _ = Real.exp (4 * Real.log n) := hexp
      _ ≤ Real.exp ((2 / 1000 : ℝ) * k) := Real.exp_le_exp.mpr hlarge
  calc
    (H : ℝ) * Real.exp (10 ^ 4 *
        ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
          ((J : ℝ) + 1) * Real.log (T + 2))) ≤
        Real.exp ((2 / 1000 : ℝ) * k) * Real.exp ((18 / 1000 : ℝ) * k) := by
      calc
        (H : ℝ) * Real.exp (10 ^ 4 *
            ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
              ((J : ℝ) + 1) * Real.log (T + 2))) ≤
            Real.exp ((2 / 1000 : ℝ) * k) *
              Real.exp (10 ^ 4 *
                ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
                  ((J : ℝ) + 1) * Real.log (T + 2))) :=
          mul_le_mul_of_nonneg_right hHexp (Real.exp_nonneg _)
        _ ≤ Real.exp ((2 / 1000 : ℝ) * k) * Real.exp ((18 / 1000 : ℝ) * k) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS) (Real.exp_nonneg _)
    _ = Real.exp ((2 / 100 : ℝ) * k) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem proxy_growth (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ n₀, ∀ n ≥ n₀, 20000000 ≤ J₆ (m₆ p₀ n) := by
  have hα : 0 < α₆ p₀ := (height_exponents6_admissible p₀ hp₀).1
  have hm : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_
      ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
    filter_upwards [] with n
    exact Nat.le_ceil _
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 25)).comp hm
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hp.eventually_ge_atTop 20000001)
  refine ⟨n₀, fun n hn => ?_⟩
  have hb := hn₀ n hn
  dsimp only [Function.comp_apply] at hb
  have hf : (m₆ p₀ n : ℝ) ^ (1 / 25 : ℝ) < (J₆ (m₆ p₀ n) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  exact_mod_cast (show (20000000 : ℝ) ≤ J₆ (m₆ p₀ n) by linarith)

open OAI.HypercubeRamsey

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}

theorem choice_mem_prosp (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (R : ℕ) (a : X.State) (ℓ : X.Loc)
    (h : X.choice H C R a = some ℓ) : ℓ ∈ X.prosp (X.pos C) (X.site a) ℓ.2 := by
  unfold Ctx6.choice HDParams.selectionAt at h
  dsimp only at h
  split at h
  · split at h
    · simp at h
    · split at h
      · have hm := (Classical.choose_spec (Finset.mem_image.mp (Finset.min'_mem _ ‹_›))).1
        have heq := Option.some.inj h
        rw [heq] at hm
        have hp := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).1
        have hl := (Finset.mem_filter.mp hp).2.2.1
        rw [hl]
        exact hp
      · simp at h
  · simp at h

end HypercubeRamsey.S06.Lane_sol_s06_cj
