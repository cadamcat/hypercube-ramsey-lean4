import HypercubeRamsey.S05.Even_test_sol_s05_even
import HypercubeRamsey.S05.History_sol_s05_1f_scales

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ}

theorem smallest_scale_upper (M R target : ℕ) (h : ∃ i : ℕ, target ≤ M ^ i * R) :
    M ^ Nat.find h * R ≤ R + M * target := by
  cases hi : Nat.find h with
  | zero => simp [hi]
  | succ i =>
    have hprev : ¬ target ≤ M ^ i * R := Nat.find_min h (by omega)
    have hlt : M ^ i * R < target := Nat.lt_of_not_ge hprev
    calc
      M ^ (i + 1) * R = M * (M ^ i * R) := by rw [pow_succ]; ring
      _ ≤ M * target := Nat.mul_le_mul_left M hlt.le
      _ ≤ _ := by omega

theorem topScale_upper (n : ℕ) (σ ζ : ℝ) (hn : 1 ≤ n) (hσ : σ ≤ 1) (hζ : 0 ≤ ζ) :
    (topScale n σ ζ : ℝ) ≤ 6 * (n : ℝ) ^ 2 := by
  let R := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hraw : topScale n σ ζ ≤ R + M * target := by
    unfold topScale
    exact smallest_scale_upper _ _ _ _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM : (M : ℝ) ≤ 2 * n := by
    dsimp [M]
    push_cast
    apply max_le
    · linarith
    · have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le σ)
      have hp : (n : ℝ) ^ σ ≤ n := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR hσ
      linarith
  have ht : (target : ℝ) ≤ 2 * n := by
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le (1 - ζ))
    have hp : (n : ℝ) ^ (1 - ζ) ≤ n := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ζ ≤ 1)
    exact (by dsimp [target] at ⊢; linarith)
  have hR : (R : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    dsimp [R]
    push_cast
    apply max_le
    · nlinarith
    · have hc := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
      have hlog := Real.log_le_self hn0.le
      have hlog0 := Real.log_nonneg hnR
      nlinarith
  have hrawR : (topScale n σ ζ : ℝ) ≤ (R : ℝ) + (M : ℝ) * target := by exact_mod_cast hraw
  have hmult := mul_le_mul hM ht (Nat.cast_nonneg target) (by linarith : (0 : ℝ) ≤ 2 * n)
  nlinarith

def blockBoundCoeff (p : Params5 γ K' χ) : ℝ := 51 * p.K2 + 2 * Real.exp (p.Kh * p.q0) + 2

theorem lowBlocks_upper (p : Params5 γ K' χ) (n j : ℕ) (hn : 1 ≤ n) (hm : 2 ≤ p.m n)
    (hj : j ≤ p.J n) :
    (p.lowBlocks n j : ℝ) ≤ (51 * p.K2 + 1) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hmR : (1 : ℝ) ≤ p.m n := by exact_mod_cast (show 1 ≤ p.m n by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 0 < p.uSeg n j := Lane_sol_s05_h5l.uSeg_positive p n j (by omega)
  have hd : (1 : ℝ) ≤ (p.q0 : ℝ) * p.uSeg n j := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos p.hq0.1 hu)
  have hlog0 := Real.log_nonneg hmR
  have hnum0 : 0 ≤ p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) :=
    mul_nonneg p.hK2.le (add_nonneg (mul_nonneg (by positivity) hlog0) (Real.rpow_nonneg (by positivity) _))
  have hc : (p.lowBlocks n j : ℝ) <
      p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
        ((p.q0 : ℝ) * p.uSeg n j) + 1 := Nat.ceil_lt_add_one (div_nonneg hnum0 (by linarith))
  have hdiv : p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
      ((p.q0 : ℝ) * p.uSeg n j) ≤
        p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) :=
    div_le_self hnum0 hd
  have hjR : (j : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := by
    have hJ : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hcast : (j : ℝ) ≤ p.J n := by exact_mod_cast hj
    exact hcast.trans hJ
  have hpow1 := Real.one_le_rpow hmR (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hlog : Real.log (p.m n : ℝ) ≤ 10 * (p.m n : ℝ) ^ (1 / 10 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ p.m n)
      (by norm_num : (0 : ℝ) < 1 / 10)
  have hbase : ((j : ℝ) + 4) * Real.log (p.m n : ℝ) ≤ 50 * (p.m n : ℝ) ^ (3 / 20 : ℝ) := by
    calc
      _ ≤ (5 * (p.m n : ℝ) ^ (1 / 20 : ℝ)) * (10 * (p.m n : ℝ) ^ (1 / 10 : ℝ)) := by
        apply mul_le_mul (by linarith) hlog hlog0 (by positivity)
      _ = _ := by
        rw [show (3 / 20 : ℝ) = 1 / 20 + 1 / 10 by norm_num, Real.rpow_add (by linarith)]
        ring
  have hsmall : (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (p.m n : ℝ) ^ (3 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  have hmn : (p.m n : ℝ) ≤ n := by exact_mod_cast m_le_n p n hn
  have hp : (p.m n : ℝ) ^ (3 / 20 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    (Real.rpow_le_rpow (by positivity) hmn (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have ht := Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hmul := mul_le_mul_of_nonneg_left (add_le_add hbase hsmall) p.hK2.le
  have hmul2 := mul_le_mul_of_nonneg_left hp (by linarith [p.hK2] : 0 ≤ 51 * p.K2)
  nlinarith

theorem blockBound_upper {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (hn : 1 ≤ n) (hm : 2 ≤ X.p.m n) :
    (X.blockBound : ℝ) ≤ blockBoundCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ) := by
  let B := blockBoundCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ)
  have hpool : (X.p.poolBlocks n : ℝ) ≤ B := by
    have hh := Lane_sol_s05_1f.poolBlocks_power_upper X.p n (by omega)
    have hmR : (1 : ℝ) ≤ X.p.m n := by exact_mod_cast (show 1 ≤ X.p.m n by omega)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmn : (X.p.m n : ℝ) ≤ n := by exact_mod_cast m_le_n X.p n hn
    have hp : (X.p.m n : ℝ) ^ (3 / 100 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      (Real.rpow_le_rpow (by positivity) hmn (by norm_num)).trans
        (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
    have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Real.exp (X.p.Kh * X.p.q0) + 1)
    dsimp [B, blockBoundCoeff]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ), X.p.hK2]
  have hlow (j : Fin (X.p.J n + 1)) : (X.p.lowBlocks n j : ℝ) ≤ B := by
    have hh := lowBlocks_upper X.p n j hn hm (by omega)
    dsimp [B, blockBoundCoeff]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ), Real.exp_pos (X.p.Kh * X.p.q0)]
  have hmax : X.blockBound ≤ ⌊B⌋₊ := by
    unfold Setup5.blockBound
    apply max_le
    · exact Nat.le_floor hpool
    · apply Finset.sup_le
      intro j _
      exact Nat.le_floor (hlow j)
  have hB0 : 0 ≤ B := by
    dsimp [B, blockBoundCoeff]
    have := X.p.hK2
    positivity
  have hcast : (X.blockBound : ℝ) ≤ (⌊B⌋₊ : ℕ) := by exact_mod_cast hmax
  exact hcast.trans (Nat.floor_le hB0)

theorem eventual_blockBound_threshold (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 2 ≤ p.m n ∧ blockBoundCoeff p ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    hp.eventually_ge_atTop (blockBoundCoeff p)] with n hn hm hb
  exact ⟨hn, by exact_mod_cast hm, hb⟩

theorem blockBound_le_dimension {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (hn : 1 ≤ n) (hm : 2 ≤ X.p.m n)
    (hcoef : blockBoundCoeff X.p ≤ (n : ℝ) ^ (3 / 4 : ℝ)) : X.blockBound ≤ n := by
  have hh := blockBound_upper X hn hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnR.le (1 / 4 : ℝ))
  rw [← Real.rpow_add hnR] at hmul
  norm_num at hmul
  exact_mod_cast hh.trans hmul

theorem evenRole_card_le (n : ℕ) : Fintype.card (EvenRole5 n) ≤ 2 ^ n := by
  have hh := Fintype.card_subtype_le (fun v : CubeVertex n => IsEvenRole v)
  simpa [EvenRole5, Fintype.card_fun] using hh

theorem center_dimension_bound {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (hn : 301 ≤ n) : X.St.d ≤ 5 * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : (n : ℝ) ^ (1 / 2 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hlarge : (301 : ℝ) ≤ n := by exact_mod_cast hn
  have hd := X.St.dimension_upper
  have hh : (X.St.d : ℝ) ≤ 5 * n := by linarith
  exact_mod_cast hh

theorem height_levels_bound {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (h : X.HeightChoice5) (hn : 7 ≤ n) : h.hp.H + 1 ≤ n ^ 3 := by
  have hσ : h.σ ≤ 1 := (h.adm.hsz.2.1.trans h.adm.hsz.2.2.1).le
  have hζ : 0 ≤ h.ζ := (h.adm.hsz.1.trans h.adm.hsz.2.1).le
  have hh := topScale_upper n h.σ h.ζ (by omega) hσ hζ
  change (h.hp.H : ℝ) ≤ 6 * (n : ℝ) ^ 2 at hh
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : ((h.hp.H + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
    push_cast
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hnR (sq_nonneg (n : ℝ))
    nlinarith
  exact_mod_cast hH

theorem reference_count_bound {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (h : X.HeightChoice5) (hn : 301 ≤ n) (hblock : X.blockBound ≤ n) :
    (Fintype.card (EvenRole5 n) * Fintype.card (X.CRef h) : ℕ) ≤ n ^ 3 * 2 ^ (7 * n) := by
  have hd := center_dimension_bound X hn
  have hH := height_levels_bound X h (by omega)
  have hrole := evenRole_card_le n
  have hcref : Fintype.card (X.CRef h) = (2 ^ X.St.d * (h.hp.H + 1)) * 2 ^ X.blockBound := by
    simp [Setup5.CRef, HDParams.Loc, CubeVertex, Setup5.HeightChoice5.hp]
  rw [hcref]
  have hdPow : 2 ^ X.St.d ≤ 2 ^ (5 * n) := Nat.pow_le_pow_right (by decide) hd
  have hblockPow : 2 ^ X.blockBound ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hblock
  calc
    _ ≤ (2 ^ n) * (((2 ^ (5 * n)) * n ^ 3) * 2 ^ n) :=
      Nat.mul_le_mul hrole (Nat.mul_le_mul (Nat.mul_le_mul hdPow hH) hblockPow)
    _ = n ^ 3 * 2 ^ (7 * n) := by
      rw [show 7 * n = n + 5 * n + n by omega, pow_add, pow_add]
      ring

theorem test_union_tail (n : ℕ) (hn : 301 ≤ n) (δ k : ℝ) (hδk : 12 ≤ δ * k) :
    (n : ℝ) ^ 3 * (2 : ℝ) ^ (7 * n) * (2 * Real.exp (-(δ * k * n))) ≤ 1 / 100 := by
  have hnR : (301 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hlogn : Real.log (n : ℝ) ≤ n := Real.log_le_self hn0.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcount : (n : ℝ) ^ 3 * (2 : ℝ) ^ (7 * n) ≤ Real.exp (10 * n) := by
    have hpN : (n : ℝ) ^ 3 = Real.exp (3 * Real.log (n : ℝ)) := by
      have hh := Real.exp_nat_mul (Real.log (n : ℝ)) 3
      rw [Real.exp_log hn0] at hh
      simpa only [Nat.cast_ofNat] using hh.symm
    have hp2 : (2 : ℝ) ^ (7 * n) = Real.exp ((7 * n : ℕ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hpN, hp2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have htail : Real.exp (-(δ * k * n)) ≤ Real.exp (-((12 : ℝ) * n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (10 * n) * (2 * Real.exp (-((12 : ℝ) * n))) :=
      mul_le_mul hcount (mul_le_mul_of_nonneg_left htail (by norm_num)) (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-((2 : ℝ) * n)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ 1 / 100 := by
      rw [Real.exp_neg]
      have hh : 1 + 2 * (n : ℝ) ≤ Real.exp (2 * n) := by
        simpa only [add_comm] using Real.add_one_le_exp (2 * n)
      have hpos := Real.exp_pos (2 * (n : ℝ))
      rw [mul_inv_le_iff₀ hpos]
      nlinarith

end
end HypercubeRamsey.Lane_sol_s05_even
