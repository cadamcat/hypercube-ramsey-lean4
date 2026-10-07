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

theorem q_s11_compat_uniformWeight_sum {β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset β) (hs : s.Nonempty) :
    (∑ b : β, if b ∈ s then (s.card : ℝ)⁻¹ else 0) = 1 := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hs)
  rw [Finset.sum_ite_mem_eq, Finset.sum_const]
  simp only [nsmul_eq_mul]
  field_simp [ne_of_gt hcard]
  <;> ring

theorem q_s11_compat_sum_unique_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hunique : ∀ a ∈ s, ∀ b ∈ s, P a → P b → a = b) :
    (∑ a : α, if a ∈ s then if P a then (1 : ℝ) else 0 else 0) ≤ 1 := by
  classical
  let t := s.filter P
  have hcard : t.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply hunique a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hsum :
      (∑ a : α, if a ∈ s then if P a then (1 : ℝ) else 0 else 0) = (t.card : ℝ) := by
    simp [t, Finset.sum_ite_mem_eq, Finset.sum_filter]
  rw [hsum]
  exact_mod_cast hcard

noncomputable def q_s11_compat_uniformIndexLaw {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinProb α) (S : α → Finset β)
    (hS : ∀ a, P.w a ≠ 0 → (S a).Nonempty) : FinProb (α × β) where
  w ab := P.w ab.1 * (if ab.2 ∈ S ab.1 then ((S ab.1).card : ℝ)⁻¹ else 0)
  nonneg ab := mul_nonneg (P.nonneg ab.1) (by split_ifs <;> positivity)
  sum_eq_one := by
    classical
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, P.w a * (if b ∈ S a then ((S a).card : ℝ)⁻¹ else 0)) =
          ∑ a, P.w a * (∑ b, if b ∈ S a then ((S a).card : ℝ)⁻¹ else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
      _ = ∑ a, P.w a := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hzero : P.w a = 0
            · simp [hzero]
            · rw [q_s11_compat_uniformWeight_sum (S a) (hS a hzero)]
              ring
      _ = 1 := P.sum_eq_one

end HypercubeRamsey.S11.Core
