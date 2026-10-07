import HypercubeRamsey.S08.L81.EvenNodes

namespace HypercubeRamsey.Lane_q_s08_asm

open Classical
open scoped BigOperators

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hB : B ω
  · by_cases hA : A ω <;> simp [hA, hB, P.nonneg ω]
  · have hA : ¬ A ω := fun hA => hB (hAB ω hA)
    simp [hA, hB]

theorem pr_mono_support {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, P.w ω ≠ 0 → A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hw : P.w ω = 0
  · simp [hw]
  · by_cases hB : B ω
    · by_cases hA : A ω <;> simp [hA, hB, P.nonneg ω]
    · have hA : ¬ A ω := fun hA => hB (hAB ω hw hA)
      simp [hA, hB]

theorem pr_eq_one_of_support {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (hA : ∀ ω, P.w ω ≠ 0 → A ω) : P.pr A = 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, if A ω then P.w ω else 0) = ∑ ω, P.w ω := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hw : P.w ω = 0
      · simp [hw]
      · simp [hA ω hw]
    _ = 1 := P.sum_eq_one

theorem pr_compl {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr (fun ω => ¬ A ω) + P.pr A = 1 := by
  classical
  unfold FinProb.pr
  calc
    _ = ∑ ω, P.w ω := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hA : A ω <;> simp [hA]
    _ = 1 := P.sum_eq_one

theorem exists_support_of_pos {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (h : 0 < P.pr A) : ∃ ω, P.w ω ≠ 0 ∧ A ω := by
  classical
  by_contra hno
  push Not at hno
  have hz : P.pr A = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hA : A ω
    · have hw : P.w ω = 0 := by
        by_contra hw
        exact hno ω hw hA
      simp [hA, hw]
    · simp [hA]
  linarith

theorem bind_pr {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (K : α → FinProb β)
    (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      ∑ a, P.w a * (K a).pr (A a) := by
  classical
  change (∑ ab : α × β, if A ab.1 ab.2 then P.w ab.1 * (K ab.1).w ab.2 else 0) =
    ∑ a, P.w a * ∑ b, if A a b then (K a).w b else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ b, if A a b then P.w a * (K a).w b else 0) =
        ∑ b, P.w a * (if A a b then (K a).w b else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hA : A a b <;> simp [hA]
    _ = P.w a * ∑ b, if A a b then (K a).w b else 0 := by rw [Finset.mul_sum]

theorem bind_pr_fst {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (K : α → FinProb β)
    (A : α → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1) = P.pr A := by
  classical
  rw [bind_pr P K (fun a _ => A a)]
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro a _
  by_cases hA : A a <;> simp [hA, (K a).sum_eq_one]

theorem exp_tail_bound (n : ℕ) (hn : 8 ≤ n) :
    Real.exp (-(n : ℝ)) ≤ 1 / ((n : ℝ) + 1) := by
  rw [Real.exp_neg]
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hexp : 0 < Real.exp (n : ℝ) := Real.exp_pos _
  have hle : (n : ℝ) + 1 ≤ Real.exp (n : ℝ) := Real.add_one_le_exp _
  calc
    (Real.exp (n : ℝ))⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := (inv_le_inv₀ hexp hden).2 hle
    _ = 1 / ((n : ℝ) + 1) := by ring

theorem half_pow_bound (n : ℕ) (hn : 8 ≤ n) :
    4 * (n : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
  have hpow : 8 * (n : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : ∀ m : ℕ, 8 ≤ m → 8 * (m : ℝ) ≤ (2 : ℝ) ^ m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | @succ m hm ih =>
          rw [Nat.cast_succ, pow_succ]
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
          nlinarith [ih]
    exact h n hn
  have hdiv : 4 * (n : ℝ) / (2 : ℝ) ^ n ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2
    nlinarith [hpow]
  calc
    4 * (n : ℝ) * (1 / 2 : ℝ) ^ n = 4 * (n : ℝ) / (2 : ℝ) ^ n := by
      rw [div_pow]
      norm_num
      ring
    _ ≤ 1 / 2 := hdiv

theorem tails_small :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      3 * Real.exp (-(n : ℝ)) + 4 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1 := by
  refine ⟨8, ?_⟩
  intro n hn
  have hn8 : 8 ≤ n := hn
  have hn9 : 9 ≤ (n : ℝ) + 1 := by exact_mod_cast (show 9 ≤ n + 1 by omega)
  have hexp := exp_tail_bound n hn8
  have hhalf := half_pow_bound n hn8
  have hgeom : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hsecond : 4 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) ≤ 1 / 2 := by
    calc
      4 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) =
          4 * (n : ℝ) * (2 ^ n * (1 / 4 : ℝ) ^ n) := by ring
      _ = 4 * (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hgeom]
      _ ≤ 1 / 2 := hhalf
  have hfirst : 3 * Real.exp (-(n : ℝ)) ≤ 1 / 3 := by
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / 9 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hn9
    nlinarith [hexp, hdiv]
  nlinarith [hfirst, hsecond]

end HypercubeRamsey.Lane_q_s08_asm
