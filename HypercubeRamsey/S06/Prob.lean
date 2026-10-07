import HypercubeRamsey.S06.Defs

/-!
# Finite-probability utilities for the Section 6 assembly

Stagewise laws are `FinProb.bind` chains (06:452–455, 06:883–884): a bad event of the composite law is bounded by
the bad mass of the first stage plus a bound for the second stage at every good first-stage outcome in the support.
-/

namespace HypercubeRamsey
namespace S06

open Classical
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem pr_nonneg6 (P : FinProb Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact P.nonneg ω; exact le_rfl]

theorem pr_le_one6 (P : FinProb Ω) (A : Ω → Prop) : P.pr A ≤ 1 := by
  unfold FinProb.pr
  calc (∑ ω, if A ω then P.w ω else 0) ≤ ∑ ω, P.w ω :=
        Finset.sum_le_sum fun ω _ => by split_ifs <;> [exact le_rfl; exact P.nonneg ω]
    _ = 1 := P.sum_eq_one

/-- Monotonicity on the support. -/
theorem pr_mono_supp6 (P : FinProb Ω) {A B : Ω → Prop} (h : ∀ ω, P.w ω ≠ 0 → A ω → B ω) :
    P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hw : P.w ω = 0
  · simp [hw]
  · by_cases hA : A ω
    · simp [hA, h ω hw hA]
    · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

theorem pr_mono6 (P : FinProb Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B :=
  pr_mono_supp6 P fun ω _ => h ω

theorem pr_or_le6 (P : FinProb Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

/-- An event without supported outcomes has probability zero. -/
theorem pr_zero_of_supp6 (P : FinProb Ω) {A : Ω → Prop} (h : ∀ ω, P.w ω ≠ 0 → ¬ A ω) : P.pr A = 0 := by
  unfold FinProb.pr
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases hA : A ω
  · by_cases hw : P.w ω = 0
    · simp [hA, hw]
    · exact absurd hA (h ω hw)
  · simp [hA]

/-- An event of probability less than one has a supported outcome outside it. -/
theorem exists_of_pr_lt_one6 (P : FinProb Ω) (A : Ω → Prop)
    (h : P.pr (fun ω => ¬ A ω) < 1) : ∃ ω, P.w ω ≠ 0 ∧ A ω := by
  by_contra hne
  push_neg at hne
  have hall : P.pr (fun ω => ¬ A ω) = 1 := by
    unfold FinProb.pr
    rw [← P.sum_eq_one]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hw : P.w ω = 0
    · simp [hw]
    · have := hne ω hw
      simp [this]
  linarith

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Support of a bind. -/
theorem bind_w_ne_zero6 (P : FinProb α) (K : α → FinProb β) (ab : α × β)
    (h : (P.bind K).w ab ≠ 0) : P.w ab.1 ≠ 0 ∧ (K ab.1).w ab.2 ≠ 0 := by
  have h' : P.w ab.1 * (K ab.1).w ab.2 ≠ 0 := h
  exact ⟨left_ne_zero_of_mul h', right_ne_zero_of_mul h'⟩

theorem pr_bind_eq6 (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) :
    (P.bind K).pr B = ∑ a, P.w a * (K a).pr (fun b => B (a, b)) := by
  unfold FinProb.pr
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  change (if B (a, b) then P.w a * (K a).w b else 0) = P.w a * if B (a, b) then (K a).w b else 0
  split_ifs <;> simp

/-- Events of the first stage. -/
theorem pr_bind_fst6 (P : FinProb α) (K : α → FinProb β) (A : α → Prop) :
    (P.bind K).pr (fun ab => A ab.1) = P.pr A := by
  rw [pr_bind_eq6]
  unfold FinProb.pr
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hA : A a
  · simp [hA, (K a).sum_eq_one]
  · simp [hA]

/-- Two-stage union bound. -/
theorem pr_bind_le6 (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) (A : α → Prop) (c : ℝ)
    (h : ∀ a, P.w a ≠ 0 → ¬ A a → (K a).pr (fun b => B (a, b)) ≤ c) (hc : 0 ≤ c) :
    (P.bind K).pr B ≤ P.pr A + c := by
  rw [pr_bind_eq6]
  have hpt : ∀ a, P.w a * (K a).pr (fun b => B (a, b)) ≤ (if A a then P.w a else 0) + P.w a * c := by
    intro a
    have hw := P.nonneg a
    have hc' : 0 ≤ P.w a * c := mul_nonneg hw hc
    by_cases hA : A a
    · simp only [hA, if_true]
      have := mul_le_mul_of_nonneg_left (pr_le_one6 (K a) fun b => B (a, b)) hw
      linarith
    · simp only [hA, if_false, zero_add]
      by_cases hw0 : P.w a = 0
      · simp [hw0]
      · exact mul_le_mul_of_nonneg_left (h a hw0 hA) hw
  calc (∑ a, P.w a * (K a).pr (fun b => B (a, b)))
      ≤ ∑ a, ((if A a then P.w a else 0) + P.w a * c) := Finset.sum_le_sum fun a _ => hpt a
    _ = P.pr A + c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_eq_one, one_mul]
      rfl

/-- The support of a restricted law lies in the restricting event. -/
theorem restrictOr6_supp {P : FinProb Ω} {A : Ω → Prop} {ω₀ ω : Ω} (hA : 0 < P.pr A)
    (h : (restrictOr6 P A ω₀).w ω ≠ 0) : A ω ∧ P.w ω ≠ 0 := by
  have hmax : ∀ ω', max 0 (if A ω' then P.w ω' else 0) = if A ω' then P.w ω' else 0 := fun ω' =>
    max_eq_right (by split_ifs <;> [exact P.nonneg ω'; exact le_rfl])
  have hsum : 0 < ∑ ω', max 0 (if A ω' then P.w ω' else 0) := by
    simp only [hmax]
    exact hA
  unfold restrictOr6 normalize6 at h
  rw [dif_pos hsum] at h
  simp only at h
  have hnum : max 0 (if A ω then P.w ω else 0) ≠ 0 := by
    intro h0
    exact h (by rw [h0, zero_div])
  rw [hmax] at hnum
  by_cases hAω : A ω
  · simp only [hAω, if_true] at hnum
    exact ⟨hAω, hnum⟩
  · simp [hAω] at hnum

end S06
end HypercubeRamsey
