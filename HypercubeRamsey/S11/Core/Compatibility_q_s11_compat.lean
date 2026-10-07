import Mathlib
import HypercubeRamsey.Framework.FinProbLemmas

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

theorem q_s11_compat_expect_single {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (P : FinProb Ω) (y : Ω) :
    P.expect (fun x => if x = y then (1 : ℝ) else 0) = P.w y := by
  classical
  unfold FinProb.expect
  rw [Fintype.sum_eq_single y]
  · simp
  · intro x hxy
    simp [hxy]

theorem q_s11_compat_cond_expect_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A]
    (hA : 0 < P.pr A) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (P.cond A hA).expect f ≤ P.expect f / P.pr A := by
  classical
  have hNum : P.expect (fun x => if A x then f x else 0) ≤ P.expect f := by
    apply FinProb.expect_mono
    intro x
    by_cases h : A x <;> simp [h, hf x]
  have hEq : (P.cond A hA).expect f =
      P.expect (fun x => if A x then f x else 0) / P.pr A := by
    dsimp [FinProb.expect, FinProb.cond]
    rw [Finset.sum_div (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : A x <;> simp [h] <;> ring
  calc
    (P.cond A hA).expect f =
        P.expect (fun x => if A x then f x else 0) / P.pr A := hEq
    _ ≤ P.expect f / P.pr A := div_le_div_of_nonneg_right hNum hA.le

end HypercubeRamsey.S11.Core
