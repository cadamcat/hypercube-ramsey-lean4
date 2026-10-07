import Mathlib

namespace HypercubeRamsey.S11.Core

/-- Fixed independence threshold, kept opaque while used as an exponent. -/
@[irreducible] def q_s11_compat_t₀ : ℕ := 1000000000000

/-- Monotonicity of natural powers, kept generic so large fixed exponents remain symbolic. -/
theorem q_s11_compat_pow_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    a ^ k ≤ b ^ k :=
  pow_le_pow_left₀ ha hab k

/-- Cast a natural power bound to `ℝ` without reducing its exponent. -/
theorem q_s11_compat_cast_pow_bound (a b k : ℕ) (h : a ≤ b ^ k) :
    (a : ℝ) ≤ (b : ℝ) ^ k := by
  exact_mod_cast h

theorem q_s11_compat_pred_exists (n : ℕ) : ∃ k : ℕ, k = n - 1 :=
  ⟨n - 1, rfl⟩

theorem q_s11_compat_exp_pow_le (k : ℕ) (x y : ℝ)
    (h : (k : ℝ) * x ≤ y) : (Real.exp x) ^ k ≤ Real.exp y := by
  rw [← Real.exp_nat_mul x k]
  exact Real.exp_le_exp.mpr h

end HypercubeRamsey.S11.Core
