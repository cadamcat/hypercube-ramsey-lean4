import HypercubeRamsey.S05.Clock

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000

variable {γ K' χ : ℝ}

theorem m_le_n (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) : p.m n ≤ n := by
  apply Nat.ceil_le.mpr
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [p.halpha.2] : p.alpha ≤ 1)

theorem caps_upper (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ p.m n) :
    p.DL n ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧
      p.DH n ≤ 10 * p.KD * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hmn : (p.m n : ℝ) ≤ n := by exact_mod_cast m_le_n p n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hKD0 := p.hKD.le
  have hpow : (p.m n : ℝ) ^ (3 / 20 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (3 / 20 : ℝ) := Real.rpow_le_rpow (by positivity) hmn (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  constructor
  · simpa only [Params5.DL, show (15 / 100 : ℝ) = 3 / 20 by norm_num] using hpow
  · have hJ : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hlog : Real.log (p.m n : ℝ) ≤ 10 * (p.m n : ℝ) ^ (1 / 10 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using
        Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ p.m n) (by norm_num : (0 : ℝ) < 1 / 10)
    have hlog0 : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg hmR
    calc
      p.DH n ≤ p.KD * ((p.m n : ℝ) ^ (1 / 20 : ℝ)) *
          (10 * (p.m n : ℝ) ^ (1 / 10 : ℝ)) := by
        unfold Params5.DH
        gcongr
      _ = 10 * p.KD * (p.m n : ℝ) ^ (3 / 20 : ℝ) := by
        rw [show (3 / 20 : ℝ) = 1 / 20 + 1 / 10 by norm_num,
          Real.rpow_add (by linarith : (0 : ℝ) < p.m n)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) p.hKD.le)

def capCoeff (p : Params5 γ K' χ) : ℝ := 1 + 10 * p.KD + Real.log 4

theorem capCoeff_pos (p : Params5 γ K' χ) : 0 < capCoeff p := by
  unfold capCoeff
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  linarith [p.hKD]

theorem capCoeff_bounds (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ p.m n) :
    p.DL n ≤ capCoeff p * (n : ℝ) ^ (1 / 4 : ℝ) ∧
      p.DH n + Real.log 4 ≤ capCoeff p * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨hDL, hDH⟩ := caps_upper p n hn hm
  have hlogmul := mul_le_mul_of_nonneg_left hp hlog
  unfold capCoeff
  constructor <;> nlinarith [p.hKD]

theorem eventual_atom_exponent (p : Params5 γ K' χ) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 2 ≤ p.m n ∧
      Real.log 3 + capCoeff p * (n : ℝ) ^ (1 / 4 : ℝ) + A * Real.log (n : ℝ) ≤
        (n : ℝ) * Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    hpow.eventually_ge_atTop ((capCoeff p + 4 * |A| + Real.log 3) / Real.log 2)] with n hn hm hlarge
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogB : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hA : A * Real.log (n : ℝ) ≤ |A| * (4 * (n : ℝ) ^ (1 / 4 : ℝ)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) hlog).trans
      (mul_le_mul_of_nonneg_left hlogB (abs_nonneg A))
  have hb := (div_le_iff₀ hlog2).mp hlarge
  have hh := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ))
  have hproduct : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
    rw [← Real.rpow_add hn0]
    norm_num
  rw [mul_assoc, mul_comm (Real.log 2), ← mul_assoc, hproduct] at hh
  refine ⟨hn, by exact_mod_cast hm, ?_⟩
  have hconst := mul_le_mul_of_nonneg_left hp1 hlog3
  nlinarith

theorem high_lengths_positive (p : Params5 γ K' χ) (n : ℕ) (hm : 2 ≤ p.m n) :
    0 < p.s n ∧ 1 ≤ p.q0 * p.uStarSeg n * p.usedBlocks n := by
  have hmR : (1 : ℝ) < p.m n := by exact_mod_cast (show 1 < p.m n by omega)
  have hlog : 0 < Real.log (p.m n : ℝ) := Real.log_pos hmR
  have hJ : 1 ≤ p.J n := by
    change 1 ≤ ⌊(p.m n : ℝ) ^ (1 / 20 : ℝ)⌋₊
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hmR.le (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hs : 0 < p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) := by
    have hJ0 : (0 : ℝ) < p.J n := by exact_mod_cast (show 0 < p.J n by omega)
    exact mul_pos (mul_pos p.hKs hJ0) hlog
  have hu : 0 < p.uStarSeg n := Lane_sol_s05_h5l.uStarSeg_positive p n (by omega)
  have hd : 0 < (p.q0 : ℝ) * p.uStarSeg n := by exact_mod_cast Nat.mul_pos p.hq0.1 hu
  have hk : 0 < p.usedBlocks n := by
    apply Nat.ceil_pos.mpr
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) hd
  exact ⟨Nat.ceil_pos.mpr hs, Nat.mul_pos (Nat.mul_pos p.hq0.1 hu) hk⟩

theorem eventual_tail_threshold (p : Params5 γ K' χ) (P : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 2 ≤ p.m n ∧
      2 * |P| * (capCoeff p) ^ 2 / (p.a 5 - p.a 4) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    hpow.eventually_ge_atTop (2 * |P| * (capCoeff p) ^ 2 / (p.a 5 - p.a 4) ^ 2)] with n hn hm ht
  exact ⟨hn, by exact_mod_cast hm, ht⟩

theorem tail_bound (p : Params5 γ K' χ) (P : ℝ) (n k : ℕ)
    (hn : 1 ≤ n) (hm : 2 ≤ p.m n) (hk : 1 ≤ k)
    (ht : 2 * |P| * (capCoeff p) ^ 2 / (p.a 5 - p.a 4) ^ 2 ≤
      (n : ℝ) ^ (1 / 4 : ℝ)) :
    Real.exp (-(2 * (p.a 5 * (k : ℝ) * n - p.a 4 * (k : ℝ) * n) ^ 2 /
      ((n : ℝ) * (p.DH n + Real.log 4) ^ 2))) ≤ (n : ℝ) ^ (-P) := by
  let C := capCoeff p
  let d := p.a 5 - p.a 4
  let t := (n : ℝ) ^ (1 / 4 : ℝ)
  let M := p.DH n + Real.log 4
  have hC : 0 < C := capCoeff_pos p
  have hd : 0 < d := sub_pos.mpr (p.ha_order 4 5 (by decide))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have hD0 : 0 ≤ p.DH n := by
    unfold Params5.DH
    exact mul_nonneg (mul_nonneg p.hKD.le (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ p.m n by omega)))
  have hM : 0 < M := add_pos_of_nonneg_of_pos hD0 (Real.log_pos (by norm_num))
  have hMle : M ≤ C * t := (capCoeff_bounds p n hn (by omega)).2
  have hMsq : M ^ 2 ≤ C ^ 2 * t ^ 2 := by nlinarith
  have htlarge : 2 * |P| * C ^ 2 ≤ t * d ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hd)).mp ht
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogB : Real.log (n : ℝ) ≤ 4 * t := by
    simpa [t, div_eq_mul_inv, mul_comm] using
      Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hPlog : P * Real.log (n : ℝ) ≤ |P| * (4 * t) :=
    (mul_le_mul_of_nonneg_right (le_abs_self P) hlog).trans
      (mul_le_mul_of_nonneg_left hlogB (abs_nonneg P))
  have ht4 : t ^ 4 = n := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hden : 0 < (n : ℝ) * M ^ 2 := mul_pos hn0 (sq_pos_of_pos hM)
  have hbound : |P| * (4 * t) ≤ 2 * (d * (k : ℝ) * n) ^ 2 / ((n : ℝ) * M ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have h1 := mul_le_mul_of_nonneg_left hMsq (by positivity : 0 ≤ |P| * (4 * t) * n)
    have h2 := mul_le_mul_of_nonneg_right htlarge (by positivity : 0 ≤ 2 * t ^ 2 * n)
    have h3 : 2 * d ^ 2 * (n : ℝ) ^ 2 ≤ 2 * (d * (k : ℝ) * n) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) - 1)]
    calc
      |P| * (4 * t) * ((n : ℝ) * M ^ 2) ≤
          |P| * (4 * t) * n * (C ^ 2 * t ^ 2) := by nlinarith [h1]
      _ ≤ 2 * d ^ 2 * (n : ℝ) ^ 2 := by
        have htn : t * (2 * t ^ 2 * (n : ℝ)) * d ^ 2 = 2 * d ^ 2 * (n : ℝ) ^ 2 / t := by
          rw [← ht4]
          field_simp
          <;> ring
        have h2' := mul_le_mul_of_nonneg_right htlarge (by positivity : 0 ≤ 2 * t ^ 3 * n)
        nlinarith [ht4, h2']
      _ ≤ _ := h3
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  have heq : p.a 5 * (k : ℝ) * n - p.a 4 * (k : ℝ) * n = d * (k : ℝ) * n := by
    dsimp [d]
    ring
  rw [heq]
  change -(2 * (d * (k : ℝ) * n) ^ 2 / ((n : ℝ) * M ^ 2)) ≤ Real.log (n : ℝ) * -P
  linarith [hPlog.trans hbound]

end
end HypercubeRamsey.Lane_sol_s05_even
