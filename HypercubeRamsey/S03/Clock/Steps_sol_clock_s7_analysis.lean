import HypercubeRamsey.S03.Clock.Inputs

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open scoped BigOperators

/-- A relative lower bound for one small Euler survival factor. -/
theorem exp_neg_le_euler_factor {δ r : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.exp (-δ * r) ≤ Real.exp (2 * δ ^ 2) * (1 - δ * r) := by
  let x := δ * r
  have hx0 : 0 ≤ x := mul_nonneg hδ0 hr0
  have hxδ : x ≤ δ := by simpa [x] using mul_le_mul_of_nonneg_left hr1 hδ0
  have hxhalf : x ≤ 1 / 2 := hxδ.trans hδ1
  have hb : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
  rw [Real.log_inv] at hlog
  have hinv : (1 - x)⁻¹ - 1 ≤ x + 2 * δ ^ 2 := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hb).mpr
    have hsq : x ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hx0 hxδ 2
    have hprod := mul_nonneg (sq_nonneg δ) (show 0 ≤ 1 - 2 * x by linarith)
    nlinarith
  have hexp : Real.exp (-x - 2 * δ ^ 2) ≤ 1 - x := by
    rw [← Real.exp_log hb]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Real.exp (-δ * r) = Real.exp (2 * δ ^ 2) * Real.exp (-x - 2 * δ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [x]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)

/-- The Euler background remains in the unit square. -/
theorem euler_background_bounds (q z : ℕ → ℝ) (δ θ : ℝ)
    (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq : ∀ t, q (t + 1) = q t * (1 - δ * θ * z t))
    (hz : ∀ t, z (t + 1) = z t * (1 - δ * q t)) :
    ∀ t, 0 ≤ q t ∧ q t ≤ 1 ∧ 0 ≤ z t ∧ z t ≤ 1 := by
  intro t
  induction t with
  | zero => simp [hq0, hz0]
  | succ t ih =>
    obtain ⟨hqt0, hqt1, hzt0, hzt1⟩ := ih
    have hδθ0 : 0 ≤ δ * θ := mul_nonneg hδ0 hθ0
    have hδθ1 : δ * θ ≤ 1 := mul_le_one₀ hδ1 hθ0 hθ1
    have hqfac0 : 0 ≤ 1 - δ * θ * z t :=
      sub_nonneg.mpr (mul_le_one₀ hδθ1 hzt0 hzt1)
    have hzfac0 : 0 ≤ 1 - δ * q t := sub_nonneg.mpr (mul_le_one₀ hδ1 hqt0 hqt1)
    have hqfac1 : 1 - δ * θ * z t ≤ 1 := sub_le_self _ (mul_nonneg hδθ0 hzt0)
    have hzfac1 : 1 - δ * q t ≤ 1 := sub_le_self _ (mul_nonneg hδ0 hqt0)
    rw [hq t, hz t]
    exact ⟨mul_nonneg hqt0 hqfac0,
      (mul_le_mul_of_nonneg_left hqfac1 hqt0).trans (by simpa using hqt1),
      mul_nonneg hzt0 hzfac0,
      (mul_le_mul_of_nonneg_left hzfac1 hzt0).trans (by simpa using hzt1)⟩

/-- The finite-mesh target-time integral telescopes exactly. -/
theorem euler_target_integral (q z : ℕ → ℝ) (δ : ℝ) (T : ℕ)
    (hz0 : z 0 = 1) (hz : ∀ t, z (t + 1) = z t * (1 - δ * q t)) :
    δ * (∑ t ∈ Finset.range T, q t * z t) = 1 - z T := by
  induction T with
  | zero => simp [hz0]
  | succ T ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hz T]
    ring

/-- Summed ordinary hazards compare relatively to the Euler product `q(t)z(t)`. -/
theorem euler_hazard_product_bound (q z : ℕ → ℝ) (δ θ : ℝ)
    (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq : ∀ t, q (t + 1) = q t * (1 - δ * θ * z t))
    (hz : ∀ t, z (t + 1) = z t * (1 - δ * q t)) :
    ∀ t, Real.exp (-δ * (∑ i ∈ Finset.range t, (q i + θ * z i))) ≤
      Real.exp (4 * δ ^ 2 * (t : ℝ)) * (q t * z t) := by
  have hb := euler_background_bounds q z δ θ hq0 hz0 hδ0 (by linarith) hθ0 hθ1 hq hz
  intro t
  induction t with
  | zero => simp [hq0, hz0]
  | succ t ih =>
    obtain ⟨hqt0, hqt1, hzt0, hzt1⟩ := hb t
    have hθz0 : 0 ≤ θ * z t := mul_nonneg hθ0 hzt0
    have hθz1 : θ * z t ≤ 1 := mul_le_one₀ hθ1 hzt0 hzt1
    have hfq := exp_neg_le_euler_factor hδ0 hδ1 hqt0 hqt1
    have hfz := exp_neg_le_euler_factor hδ0 hδ1 hθz0 hθz1
    have hqfac0 : 0 ≤ 1 - δ * q t :=
      sub_nonneg.mpr (mul_le_one₀ (by linarith : δ ≤ 1) hqt0 hqt1)
    have hstep : Real.exp (-δ * (q t + θ * z t)) ≤
        Real.exp (4 * δ ^ 2) * ((1 - δ * q t) * (1 - δ * θ * z t)) := by
      calc
        _ = Real.exp (-δ * q t) * Real.exp (-δ * (θ * z t)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ (Real.exp (2 * δ ^ 2) * (1 - δ * q t)) *
            (Real.exp (2 * δ ^ 2) * (1 - δ * (θ * z t))) :=
          mul_le_mul hfq hfz (Real.exp_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) hqfac0)
        _ = _ := by
          rw [show Real.exp (4 * δ ^ 2) = Real.exp (2 * δ ^ 2) * Real.exp (2 * δ ^ 2) by
            rw [← Real.exp_add]; congr 1; ring]
          ring
    rw [Finset.sum_range_succ, mul_add, Real.exp_add]
    calc
      _ ≤ (Real.exp (4 * δ ^ 2 * (t : ℝ)) * (q t * z t)) *
          (Real.exp (4 * δ ^ 2) * ((1 - δ * q t) * (1 - δ * θ * z t))) :=
        mul_le_mul ih hstep (Real.exp_nonneg _) (by positivity)
      _ = Real.exp (4 * δ ^ 2 * ((t + 1 : ℕ) : ℝ)) * (q (t + 1) * z (t + 1)) := by
        rw [Nat.cast_succ, hq t, hz t]
        rw [show Real.exp (4 * δ ^ 2 * ((t : ℝ) + 1)) =
            Real.exp (4 * δ ^ 2 * (t : ℝ)) * Real.exp (4 * δ ^ 2) by
          rw [← Real.exp_add]; congr 1; ring]
        ring

end HypercubeRamsey.Lane_sol_clock_s7
