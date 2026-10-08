import HypercubeRamsey.S11.Core.Assignment_q_s11_tags
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_s11_raw

open HypercubeRamsey.S11.Core HypercubeRamsey OAI.HypercubeRamsey
open Classical Filter Real
open scoped BigOperators Topology

private theorem poly_exp_decay (R : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 3 * (n : ℝ)^2 * Real.exp (-(1/5 : ℝ) * (n : ℝ)^((19 : ℝ)/100)) ≤
      (n : ℝ)^(-R) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(R+2) *
      Real.exp (-(1/5 : ℝ) * (n : ℝ)^((19 : ℝ)/100))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((R+2)/((19 : ℝ)/100)) (1/5) (by norm_num)).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 19/100)).comp tendsto_natCast_atTop_atTop)
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change ((n : ℝ)^(19/100))^((R+2)/(19/100)) *
      Real.exp (-(1/5 : ℝ) * (n : ℝ)^(19/100)) = _
    rw [← Real.rpow_mul hn0]
    congr 2
    ring
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/3)))
  refine ⟨max 1 n₁, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ht := hn₁ n (le_trans (le_max_right _ _) hn)
  have hr : (n : ℝ)^(R+2) = (n : ℝ)^R * (n : ℝ)^2 := by
    rw [Real.rpow_add hnpos, Real.rpow_two]
  have hinv : (n : ℝ)^(-R) = ((n : ℝ)^R)⁻¹ := Real.rpow_neg hnpos.le _
  rw [hinv]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hnpos R)).2
  rw [hr] at ht
  nlinarith

theorem sigma_polynomial_bound (R : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N), SliceFacts M y₀ →
      ∀ i, sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) ≤
        (n : ℝ)^(-R) := by
  obtain ⟨n₁, hn₁⟩ := poly_exp_decay R
  refine ⟨max 4 n₁, ?_⟩
  intro n hn N E X Y κ M y₀ hS i
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  let h := Fintype.card (InnerCoord n)
  have hcard : h = hIn n := HypercubeRamsey.Lane_q_s11_tags.innerCoord_card
    (le_trans (HypercubeRamsey.Lane_q_s11_tags.hIn_le_half hn4) (Nat.div_le_self n 2))
  have hh1 : (1 : ℝ) ≤ h := by
    rw [hcard]
    exact_mod_cast (Nat.one_le_floor_iff _).2
      (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/10))
  have hhN : (h : ℝ) ≤ n := by
    rw [hcard]
    exact_mod_cast le_trans (HypercubeRamsey.Lane_q_s11_tags.hIn_le_half hn4) (Nat.div_le_self n 2)
  have hk : (n : ℝ)^((1 : ℝ)/5) ≤ kTup n := Nat.le_ceil _
  have hg0 : 0 ≤ gS n := Real.rpow_nonneg hnpos.le _
  have hg1 : gS n ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hgk : (n : ℝ)^((19 : ℝ)/100) ≤ gS n * kTup n := by
    calc
      _ = gS n * (n : ℝ)^((1 : ℝ)/5) := by
        unfold gS
        rw [← Real.rpow_add hnpos]
        congr 1
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hg0
  have hk0 : (0 : ℝ) ≤ kTup n := Nat.cast_nonneg _
  have hgh : gS n * kTup n ≤ gS n * kTup n * h := by
    nlinarith [mul_nonneg hg0 hk0]
  have hkh : gS n * kTup n ≤ (kTup n : ℝ) * h := by
    nlinarith
  let B := Real.exp (-(1/5 : ℝ) * (n : ℝ)^((19 : ℝ)/100))
  have hb0 : 0 ≤ B := (Real.exp_pos _).le
  have hfirst : Real.exp (-(1/2 : ℝ) * gS n * kTup n * h) ≤ B := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg hnpos.le ((19 : ℝ)/100)]
  have htest1 : Real.exp (-((kTup n : ℝ) * h)) ≤ B := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg hnpos.le ((19 : ℝ)/100)]
  have htest2 : Real.exp (-(1/5 : ℝ) * gS n * kTup n) ≤ B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (-(1/2 : ℝ) * gS n * kTup n * h) +
        (h : ℝ) * (Real.exp (-((kTup n : ℝ) * h)) +
          (h : ℝ) * Real.exp (-(1/5 : ℝ) * gS n * kTup n)) := by
      exact (hS.sigma i).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hS.test i) (Nat.cast_nonneg h)))
    _ ≤ B + (n : ℝ) * (B + (n : ℝ) * B) := by
      gcongr
    _ ≤ 3 * (n : ℝ)^2 * B := by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hb0]
    _ ≤ _ := hn₁ n (le_trans (le_max_right _ _) hn)

end HypercubeRamsey.Lane_sol_s11_raw
