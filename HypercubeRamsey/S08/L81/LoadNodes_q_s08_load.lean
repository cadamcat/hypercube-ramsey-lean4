import HypercubeRamsey.S08.L81.PosteriorNodes

/-!
Private helpers for lane q-s08-load.
-/

noncomputable section

namespace HypercubeRamsey.S08.Lane_q_s08_load

open Classical
open scoped BigOperators

private theorem pr_bind_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) :
    (FinProb.bind P K).pr B = ∑ a, P.w a * (K a).pr (fun b => B (a, b)) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : B (a, b) <;> simp [h, mul_assoc]

private theorem pr_le_one {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A ≤ 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ a, if A a then P.w a else 0) ≤ ∑ a, P.w a :=
      Finset.sum_le_sum fun a _ => by split_ifs <;> simp [P.nonneg a]
    _ = 1 := P.sum_eq_one

private theorem pr_bind_le {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) (A : α → Prop) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ a, P.w a ≠ 0 → ¬ A a → (K a).pr (fun b => B (a, b)) ≤ c) :
    (FinProb.bind P K).pr B ≤ P.pr A + c := by
  rw [pr_bind_eq]
  have hpt (a : α) : P.w a * (K a).pr (fun b => B (a, b)) ≤
      (if A a then P.w a else 0) + P.w a * c := by
    have hw := P.nonneg a
    by_cases hA : A a
    · simp only [hA, if_true]
      have hle := mul_le_mul_of_nonneg_left (pr_le_one (K a) fun b => B (a, b)) hw
      have htail : 0 ≤ P.w a * c := mul_nonneg hw hc
      nlinarith
    · simp only [hA, if_false, zero_add]
      by_cases hw0 : P.w a = 0
      · simp [hw0]
      · exact mul_le_mul_of_nonneg_left (h a hw0 hA) hw
  calc
    (∑ a, P.w a * (K a).pr (fun b => B (a, b))) ≤
        ∑ a, ((if A a then P.w a else 0) + P.w a * c) :=
      Finset.sum_le_sum fun a _ => hpt a
    _ = P.pr A + c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_eq_one]
      simp [FinProb.pr]

private theorem pre_pr_reassoc {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (E : D.Hist → D.Pos × D.TAT → Prop) :
    D.preLaw.pr (fun q => E q.1.1 (q.1.2, q.2)) =
      (FinProb.bind D.hiddenLaw (fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ))).pr
        (fun q => E q.1 q.2) := by
  classical
  have hleft : D.preLaw.pr (fun q => E q.1.1 (q.1.2, q.2)) =
      ∑ Θ, D.hiddenLaw.w Θ *
        (FinProb.bind D.posLaw (fun P => D.rawTAT Θ)).pr (fun z => E Θ z) := by
    unfold Ctx.preLaw
    rw [pr_bind_eq]
    calc
      (∑ q : D.Hist × D.Pos,
          (FinProb.bind D.hiddenLaw (fun _ => D.posLaw)).w q *
            (D.rawTAT q.1).pr (fun ω => E q.1 (q.2, ω))) =
        ∑ Θ, ∑ P, (D.hiddenLaw.w Θ * D.posLaw.w P) *
            (D.rawTAT Θ).pr (fun ω => E Θ (P, ω)) := by
          simp only [FinProb.bind]
          rw [Fintype.sum_prod_type]
      _ = ∑ Θ, D.hiddenLaw.w Θ *
            (FinProb.bind D.posLaw (fun P => D.rawTAT Θ)).pr (fun z => E Θ z) := by
          apply Finset.sum_congr rfl
          intro Θ _
          rw [pr_bind_eq]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro P _
          ring
  have hright :
      (FinProb.bind D.hiddenLaw (fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ))).pr
        (fun q => E q.1 q.2) =
      ∑ Θ, D.hiddenLaw.w Θ *
        (FinProb.bind D.posLaw (fun _ => D.rawTAT Θ)).pr (fun z => E Θ z) := by
    rw [pr_bind_eq]
  rw [hleft, hright]

theorem load_tail {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (C₁ C₂ a b : ℝ) (hb : 0 ≤ b)
    (hpos : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g))
    (hcomp : D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) ≤ a)
    (hcenter : ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → D.CompOK C₁ Θ →
      (FinProb.bind D.posLaw fun _ => D.rawTAT Θ).pr
        (fun z => D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK C₂ ((Θ, z.1), z.2)) ≤ b) :
    D.preLaw.pr (fun q => D.SelOK q ∧ ¬ D.LoadOK C₂ q) ≤ a + b := by
  classical
  let Good : D.Hist → Prop := fun Θ => ∀ g, ¬ D.HBad Θ g
  let E : D.Hist → D.Pos × D.TAT → Prop := fun Θ z =>
    D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK C₂ ((Θ, z.1), z.2)
  let K : D.Hist → FinProb (D.Pos × D.TAT) :=
    fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ)
  have hform (Θ : D.Hist) : D.hiddenLaw.w Θ =
      (if Good Θ then D.rawHidden.w Θ else 0) / D.rawHidden.pr Good := by
    change (condOr D.rawHidden Good).w Θ = _
    unfold condOr
    rw [dif_pos hpos]
    by_cases hg : Good Θ <;> simp [FinProb.cond, hg]
  have hsupp (Θ : D.Hist) (hw : D.hiddenLaw.w Θ ≠ 0) : Good Θ := by
    by_contra hbad
    have hzero : D.hiddenLaw.w Θ = 0 := by
      rw [hform]
      simp [hbad]
    exact hw hzero
  have hpoint : ∀ Θ, D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤
      (if ¬ D.CompOK C₁ Θ then D.hiddenLaw.w Θ else 0) + D.hiddenLaw.w Θ * b := by
    intro Θ
    by_cases hC : D.CompOK C₁ Θ
    · by_cases hw : D.hiddenLaw.w Θ = 0
      · simp [hw]
      · have hraw : (K Θ).pr (fun z => E Θ z) ≤ b := by
          simpa [K, E] using hcenter Θ (hsupp Θ hw) hC
        simpa [hC] using mul_le_mul_of_nonneg_left hraw (D.hiddenLaw.nonneg Θ)
    · have hle := pr_le_one (K Θ) (fun z => E Θ z)
      have hw := D.hiddenLaw.nonneg Θ
      have hwb : 0 ≤ D.hiddenLaw.w Θ * b := mul_nonneg hw hb
      have hle' : D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤ D.hiddenLaw.w Θ := by
        simpa using mul_le_mul_of_nonneg_left hle hw
      have hsum : D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤
          D.hiddenLaw.w Θ + D.hiddenLaw.w Θ * b :=
        hle'.trans (le_add_of_nonneg_right hwb)
      simpa [hC] using hsum
  have hbound :
      (FinProb.bind D.hiddenLaw K).pr (fun q => E q.1 q.2) ≤
        D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := by
    rw [pr_bind_eq]
    calc
      (∑ Θ, D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z)) ≤
        ∑ Θ, ((if ¬ D.CompOK C₁ Θ then D.hiddenLaw.w Θ else 0) + D.hiddenLaw.w Θ * b) :=
          Finset.sum_le_sum fun Θ _ => hpoint Θ
      _ = D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, D.hiddenLaw.sum_eq_one]
          rw [FinProb.pr]
          ring
  have heq := pre_pr_reassoc D E
  rw [heq]
  calc
    (FinProb.bind D.hiddenLaw K).pr (fun q => E q.1 q.2) ≤
        D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := hbound
    _ ≤ a + b := by linarith [hcomp]

end HypercubeRamsey.S08.Lane_q_s08_load

end
