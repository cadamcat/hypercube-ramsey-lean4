import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_tilt

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

private theorem scale_exists (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
    obtain ⟨i, hi⟩ := ih
    have hx : 1 ≤ M ^ i * R := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (pow_ne_zero _ (by omega : M ≠ 0)) (by omega))
    refine ⟨i + 1, ?_⟩
    rw [pow_succ]
    nlinarith

private theorem least_scale_le (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R)
    (h : ∃ i : ℕ, target ≤ M ^ i * R) :
    M ^ Nat.find h * R ≤ M * max R target := by
  cases he : Nat.find h with
  | zero =>
    simp only [he, pow_zero, one_mul]
    calc
      R ≤ max R target := le_max_left _ _
      _ ≤ M * max R target := by
        simpa using Nat.mul_le_mul_right (max R target) (show 1 ≤ M by omega)
  | succ i =>
    have hi : i < Nat.find h := by omega
    have hprev : M ^ i * R < target := lt_of_not_ge (Nat.find_min h hi)
    rw [pow_succ]
    calc
      M ^ i * M * R = M * (M ^ i * R) := by ring
      _ ≤ M * target := Nat.mul_le_mul_left M hprev.le
      _ ≤ M * max R target := Nat.mul_le_mul_left M (le_max_right _ _)

/-- A coarse polynomial bound suffices for all position and list enumerations. -/
theorem height_scale_le_cube (n : ℕ) (δ : ℝ) (hn : 2 ≤ n) (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) :
    topScale n δ (8 * δ) ≤ n ^ 3 := by
  let R : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ δ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - 8 * δ)⌉₊
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ^ δ ≤ n := by
    calc
      (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hδ
      _ = n := Real.rpow_one _
  have htarget : (n : ℝ) ^ (1 - 8 * δ) ≤ n := by
    calc
      (n : ℝ) ^ (1 - 8 * δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
      _ = n := Real.rpow_one _
  have hM : M ≤ n := max_le hn (Nat.ceil_le.mpr hpow)
  have ht : target ≤ n := Nat.ceil_le.mpr htarget
  have hlog : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlog2 : Real.log (n : ℝ) ^ 2 ≤ ((n ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hR : R ≤ n ^ 2 := max_le (by nlinarith) (Nat.ceil_le.mpr hlog2)
  have hmax : max R target ≤ n ^ 2 := max_le hR (ht.trans (by nlinarith))
  have hM2 : 2 ≤ M := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_left _ _
  have hleast := least_scale_le M R target hM2 hR1 (scale_exists M R target hM2 hR1)
  have hbound : M * max R target ≤ n ^ 3 := by nlinarith [Nat.mul_le_mul hM hmax]
  apply le_trans _ hbound
  change M ^ Nat.find (scale_exists M R target hM2 hR1) * R ≤ _
  exact hleast

/-- Fixed constant multiples of a smaller power are eventually below a larger one. -/
theorem power_gap {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop c,
    Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hn hn1
  have hp : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hp _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hp]; congr 1; ring

end HypercubeRamsey.Lane_sol_s10_d2
