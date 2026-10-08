import HypercubeRamsey.S05.Even_setup_mixtures_sol_s05_even
import HypercubeRamsey.S05.Even_test_scales_sol_s05_even
import HypercubeRamsey.S05.History_sol_s05_h5l_bounds

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem candidatePositions_polynomial (L : X.CentreLayer5) (H : X.KeyHist)
    (ω : X.CΩ L.ht) (b : OddRole5 n) (hb : L.valid H ω b) (hn : 7 ≤ n) :
    ((candidatePositions X L ω b).card : ℝ) ≤ (n : ℝ) ^ 15 := by
  have hh : ((L.ht.hp.H + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast height_levels_bound X L.ht hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hl : L.ht.hp.lam = (n : ℝ) ^ (10 : ℕ) := by
    change (n : ℝ) ^ (10 : ℝ) = _
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (n : ℝ) (10 : ℕ)
  calc
    _ ≤ (n : ℝ) * ((L.ht.hp.H + 1 : ℕ) : ℝ) * (2 * L.ht.hp.lam) :=
      candidatePositions_card X L H ω b hb
    _ ≤ (n : ℝ) * (n : ℝ) ^ 3 * (2 * (n : ℝ) ^ 10) := by
      rw [hl]
      gcongr
    _ = 2 * (n : ℝ) ^ 14 := by ring
    _ ≤ (n : ℝ) ^ 15 := by
      have h := mul_le_mul_of_nonneg_right hnR (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 14)
      convert h using 1 <;> ring

theorem T_le_n (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) : p.T n ≤ n := by
  apply Nat.ceil_le.mpr
  have hm : (p.m n : ℝ) ≤ n := by exact_mod_cast m_le_n p n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (n : ℝ) ^ (1 / 1000 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hm (by norm_num)
    _ ≤ (n : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 / 1000 : ℝ) ≤ 1)

theorem T_positive (p : Params5 γ K' χ) (n : ℕ) (hm : 1 ≤ p.m n) : 0 < p.T n := by
  have hmR : (0 : ℝ) < p.m n := by exact_mod_cast (show 0 < p.m n by omega)
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hmR _)

theorem placement_cost {h : X.HeightChoice5} (D : Finset h.hp.Loc) (hn : 1 ≤ n)
    (hD : (D.card : ℝ) ≤ (n : ℝ) ^ 15) :
    (D.card ^ X.p.T n : ℝ) ≤ Real.exp (15 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ((n : ℝ) ^ 15) ^ X.p.T n := pow_le_pow_left₀ (Nat.cast_nonneg _) hD _
    _ = Real.exp (15 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
      rw [← pow_mul]
      have hp := Real.exp_nat_mul (Real.log (n : ℝ)) (15 * X.p.T n)
      rw [Real.exp_log hnR] at hp
      rw [← hp]
      congr 1
      push_cast
      ring

def lowRecordCost (C : ℝ) (b : OddRole5 n) : ℝ :=
  C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
    (((X.g.roleKey (X.p.J n) b.1).level : ℝ) + 1) * Real.log (X.p.m n) +
    (if (X.g.roleKey (X.p.J n) b.1).isLeft ∧ (X.g.roleKey (X.p.J n) b.1).level = X.p.J n then
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))

theorem lowConfig_cost (C : ℝ) (hC : X.RecordCount C) (L : X.CentreLayer5)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n) (hb : L.valid H ω b) (hn : 7 ≤ n) :
    ((lowConfigSet X b (candidatePositions X L ω b)).card : ℝ) ≤
      Real.exp (lowRecordCost X C b + 15 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
  rw [lowConfigSet_card, Nat.cast_mul, Nat.cast_pow, Real.exp_add]
  exact mul_le_mul (lowRecordSet_card X C hC b)
    (placement_cost X _ (by omega) (candidatePositions_polynomial X L H ω b hb hn))
    (by positivity) (Real.exp_pos _).le

theorem highConfig_cost (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (hbl : ¬ X.g.low (X.p.J n) b.1)
    (hn : 7 ≤ n) (hm : 1 ≤ X.p.m n) :
    ((highConfigSet X b (candidatePositions X L ω b)).card : ℝ) ≤
      Real.exp (617 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
  have hT := T_positive X.p n hm
  have hTn : (X.p.T n : ℝ) ≤ n := by exact_mod_cast T_le_n X.p n (by omega)
  have hT1 : (1 : ℝ) ≤ X.p.T n := by exact_mod_cast hT
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
  have hlogT : Real.log (X.p.T n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) hTn
  have hprod : ((highConfigSet X b (candidatePositions X L ω b)).card : ℝ) ≤
      ((2 : ℝ) ^ X.p.T n * (X.p.T n : ℝ) ^ 601) *
        ((candidatePositions X L ω b).card : ℝ) ^ X.p.T n := by
    exact_mod_cast highConfigSet_card X b _ hbl hT
  have heq : (2 : ℝ) ^ X.p.T n * (X.p.T n : ℝ) ^ 601 =
      Real.exp ((X.p.T n : ℝ) * Real.log 2 + 601 * Real.log (X.p.T n : ℝ)) := by
    have h2 := Real.exp_nat_mul (Real.log (2 : ℝ)) (X.p.T n)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2
    have h601 := Real.exp_nat_mul (Real.log (X.p.T n : ℝ)) 601
    rw [Real.exp_log (by linarith : (0 : ℝ) < X.p.T n)] at h601
    norm_num only [Nat.cast_ofNat] at h601
    rw [Real.exp_add, h2, h601]
  calc
    _ ≤ Real.exp ((X.p.T n : ℝ) * Real.log 2 + 601 * Real.log (X.p.T n : ℝ)) *
        Real.exp (15 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
      rw [← heq]
      exact hprod.trans (mul_le_mul_of_nonneg_left
        (placement_cost X _ (by omega) (candidatePositions_polynomial X L H ω b hb hn)) (by positivity))
    _ ≤ Real.exp (617 * (X.p.T n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (X.p.T n))
      have h2 := mul_le_mul_of_nonneg_left hlogT (by norm_num : (0 : ℝ) ≤ 601)
      have h3 := mul_le_mul_of_nonneg_right hT1 hlogn
      nlinarith

end
end HypercubeRamsey.Lane_sol_s05_even
