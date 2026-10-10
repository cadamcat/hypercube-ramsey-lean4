import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.S03.Injection.Nodes

/-!
# Lemma 3.9: calibrated near-product injections

Source: `sections/03-…tex`, Lemma 3.9 (`lem:near-product-injection`, lines 586–769). Rows `i : R` carry full
outputs `Ω i` with labels `lab i : Ω i → Fin d`; the injection assigns distinct labels, keeps every row's
marginal exactly, and bounds joint probabilities of at most `d^{0.025}` specified outputs by the product of their
probabilities times `exp (d^{-0.04} · #rows)`.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- Label marginal of a row law. -/
noncomputable def labMarg {Ω : Type*} [Fintype Ω] {d : ℕ} (p : FinProb Ω) (lab : Ω → Fin d)
    (y : Fin d) : ℝ := by
  classical exact ∑ o, if lab o = y then p.w o else 0

/-- Label masses are nonnegative. -/
theorem labMarg_nonneg {Ω : Type*} [Fintype Ω] {d : ℕ}
    (p : FinProb Ω) (lab : Ω → Fin d) (y : Fin d) : 0 ≤ labMarg p lab y := by
  classical
  unfold labMarg
  exact Finset.sum_nonneg fun o _ => by
    split_ifs
    · exact p.nonneg o
    · exact le_rfl

/-- The label masses of a probability law sum to one. -/
theorem labMarg_sum_one {Ω : Type*} [Fintype Ω] {d : ℕ}
    (p : FinProb Ω) (lab : Ω → Fin d) : ∑ y, labMarg p lab y = 1 := by
  classical
  calc
    ∑ y, labMarg p lab y = ∑ o, ∑ y, (if lab o = y then p.w o else 0) := by
      simp only [labMarg]
      rw [Finset.sum_comm]
    _ = ∑ o, p.w o := by
      apply Finset.sum_congr rfl
      intro o ho
      simp
    _ = 1 := p.sum_eq_one

theorem near_product_injection : ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ {R : Type} [Fintype R] [DecidableEq R]
    {Ω : R → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (lab : ∀ i, Ω i → Fin d) (p : ∀ i, FinProb (Ω i)),
    (∀ i y, labMarg (p i) (lab i) y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) →
    (∀ y, ∑ i, labMarg (p i) (lab i) y ≤ 0.4) →
    ∃ J : FinProb (∀ i, Ω i),
      (∀ ω, J.w ω ≠ 0 → Function.Injective (fun i => lab i (ω i))) ∧
      (∀ i o, J.pr (fun ω => ω i = o) = (p i).w o) ∧
      (∀ (S : Finset R) (o : ∀ i, Ω i), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
          Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, (p i).w (o i)) := by
  obtain ⟨d₀, hd₀, hpriceAll⟩ := price_directed_label_sampler
  refine ⟨d₀, ?_⟩
  intro d hd R instR instDecR Ω instΩ instDecΩ lab p hcap hload
  let q : R → Fin d → ℝ := fun i y => labMarg (p i) (lab i) y
  have hq_nonneg : ∀ i y, 0 ≤ q i y := by
    intro i y
    exact labMarg_nonneg (p i) (lab i) y
  have hq_sum : ∀ i, ∑ y, q i y = 1 := by
    intro i
    exact labMarg_sum_one (p i) (lab i)
  have hprice : ∀ c : R → Fin d → ℝ, ∃ Q : FinProb (R → Fin d),
      LabelInjectionSupported Q ∧ LabelNearProductBound d q Q ∧
      injectionTargetPrice q c ≤ injectionLabelPrice Q c :=
    hpriceAll d hd q hq_nonneg hq_sum hcap hload
  obtain ⟨Q, hQinj, hQjoint, hQmarg⟩ :=
    calibrate_label_marginals d q hprice
  have hq : ∀ i y, q i y = injectionLabelMass (p i) (lab i) y := by
    intro i y
    rfl
  exact lift_side_data d lab p q Q hq hQinj hQmarg hQjoint

end HypercubeRamsey
