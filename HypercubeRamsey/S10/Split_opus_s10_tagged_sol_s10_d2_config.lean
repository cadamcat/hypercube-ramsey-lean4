import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_disjoint_numeric

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

theorem envelope_size_polynomial (n m : ℕ) (hm : m ≤ n) (hn : 2 ≤ n) :
    m + (n - m + 1) ^ 3 ≤ 9 * n ^ 3 := by
  have hp : (n - m + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hn3 : n ≤ n ^ 3 := by
    have hh := Nat.mul_le_mul_left n hn2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
  have hh := Nat.add_le_add hm hp
  nlinarith

/-- The deterministic marking loss is a small fraction of lambda eventually. -/
theorem marking_budget_eventually (δ : ℝ) (hδ : 0 < δ) (hs : δ < (1 : ℝ) / 2000) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n →
      (((m + (n - m + 1) ^ 3 : ℕ) : ℝ) *
        ((n * p10_1kFixedListBlockCount n δ : ℕ) : ℝ)) ≤
        (8 / 1000 : ℝ) * (n : ℝ) ^ 10 := by
  have hg := power_gap (a := 4 + 200 * δ) (b := 10) (c := 3375)
    (by linarith) (by norm_num)
  filter_upwards [hg, Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩] with n hg hn
  intro m hm
  have hx : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have he : ((m + (n - m + 1) ^ 3 : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 := by
    exact_mod_cast envelope_size_polynomial n m hm hn
  have hr := (p10_1kFixedListScale_rounding_bounds n δ hn hδ).2.2
  have hdom : ((m + (n - m + 1) ^ 3 : ℕ) : ℝ) *
      ((n * p10_1kFixedListBlockCount n δ : ℕ) : ℝ) ≤ 27 * (n : ℝ) ^ (4 + 200 * δ) := by
    push_cast at he ⊢
    calc
      _ ≤ (9 * (n : ℝ) ^ 3) * ((n : ℝ) * (3 * (n : ℝ) ^ (200 * δ))) := by gcongr
      _ = 27 * (n : ℝ) ^ (4 + 200 * δ) := by
        have hp4 : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_num
        rw [Real.rpow_add hx, hp4]
        ring
  have hg' : 27 * (n : ℝ) ^ (4 + 200 * δ) ≤ (8 / 1000 : ℝ) * (n : ℝ) ^ 10 := by
    have hp10 : (n : ℝ) ^ (10 : ℝ) = (n : ℝ) ^ 10 := by norm_num
    rw [hp10] at hg
    linarith
  exact hdom.trans hg'

/-- The global position union bound is less than the allotted budget eventually. -/
theorem position_error_small (δ ε : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n →
      (2 : ℝ) ^ m * (2 * (2 : ℝ) ^ (n - m) *
        (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) *
          Real.exp (-(p10_1kHeightParams n m δ).lam / 2000000)) ≤ ε := by
  have hs := cube_exp_error_small 10 3 (1 / 2000000) 4 ε
    (by norm_num) (by norm_num) (by norm_num) hε
  filter_upwards [hs, Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩] with n hs hn
  intro m hm
  have hH : ((p10_1kHeightParams n m δ).H : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast height_scale_le_cube n δ hn hδ1 hδ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have hH' : (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by
    push_cast
    linarith
  have hp : (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m) = (2 : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have hlam : (p10_1kHeightParams n m δ).lam = (n : ℝ) ^ 10 := rfl
  calc
    (2 : ℝ) ^ m * (2 * (2 : ℝ) ^ (n - m) *
        (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) *
          Real.exp (-(p10_1kHeightParams n m δ).lam / 2000000)) =
      (2 : ℝ) ^ n * 2 * (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) *
        Real.exp (-(n : ℝ) ^ 10 / 2000000) := by
      rw [hlam]
      calc
        _ = ((2 : ℝ) ^ m * (2 : ℝ) ^ (n - m)) * 2 *
          (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) * Real.exp (-(n : ℝ) ^ 10 / 2000000) := by ring
        _ = _ := by rw [hp]
    _ ≤ 4 * (n : ℝ) ^ 3 * (2 : ℝ) ^ n * Real.exp (-(n : ℝ) ^ 10 / 2000000) := by
      calc
        _ ≤ (2 : ℝ) ^ n * 2 * (2 * (n : ℝ) ^ 3) * Real.exp (-(n : ℝ) ^ 10 / 2000000) := by gcongr
        _ = _ := by ring
    _ ≤ ε := by simpa [Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs

end HypercubeRamsey.Lane_sol_s10_d2
