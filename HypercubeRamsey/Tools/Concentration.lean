import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Tools.Concentration_p_tools_conc

/-!
# Finite concentration tools

Finite-weight forms of Hoeffding's lemma, Hoeffding/Chernoff tails, Azuma, Freedman, and bounded differences.
The corresponding measure-theoretic Mathlib routes are `hasSubgaussianMGF_of_mem_Icc`,
`measure_sum_ge_le_of_iIndepFun`, and `measure_sum_ge_le_of_HasCondSubgaussianMGF` in
`Mathlib/Probability/Moments/SubGaussian.lean`; these statements keep the interfaces on `FinProb`.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- X-HoeffdingLemma: a bounded finite random variable has a sub-Gaussian centered moment generating function. -/
theorem xHoeffdingLemma {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (X : Ω → ℝ)
    (a b t : ℝ) (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b) :
    P.expect (fun ω => Real.exp (t * (X ω - P.expect X))) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  have hmeas : Measurable X := fun _ _ => by simp
  have hbound : ∀ᵐ ω ∂(P.toPMF.toMeasure), X ω ∈ Set.Icc a b :=
    Filter.Eventually.of_forall fun ω => hX ω
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := P.toPMF.toMeasure) hmeas.aemeasurable hbound
  have hsub' : ProbabilityTheory.HasSubgaussianMGF
      (fun ω => X ω - P.expect X) ((‖b - a‖₊ / 2) ^ 2) (P.toPMF.toMeasure) := by
    simpa only [FinProb.integral_toPMF_eq_expect] using hsub
  calc
    P.expect (fun ω => Real.exp (t * (X ω - P.expect X))) =
        ∫ ω, Real.exp (t * (X ω - P.expect X)) ∂(P.toPMF.toMeasure) :=
      (FinProb.integral_toPMF_eq_expect P _).symm
    _ = ProbabilityTheory.mgf (fun ω => X ω - P.expect X) (P.toPMF.toMeasure) t := rfl
    _ ≤ Real.exp (((‖b - a‖₊ / 2) ^ 2) * t ^ 2 / 2) := hsub'.mgf_le t
    _ = Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
      congr 1
      norm_num [Real.nnnorm_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- X-Chernoff: two-sided Hoeffding tails for independent finite bounded summands. -/
theorem xChernoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ) (a b : ι → ℝ)
    (hX : ∀ i ω, a i ≤ X i ω ∧ X i ω ≤ b i)
    (hwidth : 0 < ∑ i, (b i - a i) ^ 2) (t : ℝ) (ht : 0 < t) :
    (FinProb.pi P).pr (fun ω =>
      t ≤ |(∑ i, X i (ω i)) - ∑ i, (P i).expect (X i)|) ≤
        2 * Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  classical
  let m : ι → ℝ := fun i => (P i).expect (X i)
  let Z : (∀ i, Ω i) → ℝ := fun ω => (∑ i, X i (ω i)) - ∑ i, m i
  let S : ℝ := ∑ i, (b i - a i) ^ 2
  have hab : ∀ i, a i ≤ b i := by
    intro i
    have hne : Nonempty (Ω i) := by
      by_contra hn
      haveI : IsEmpty (Ω i) := not_nonempty_iff.mp hn
      have hs := (P i).sum_eq_one
      simp at hs
    obtain ⟨ω⟩ := hne
    exact le_trans (hX i ω).1 (hX i ω).2
  have hS : 0 < S := by simpa [S] using hwidth
  have hmgf : ∀ r : ℝ,
      (FinProb.pi P).expect (fun ω => Real.exp (r * Z ω)) ≤ Real.exp (r ^ 2 * S / 8) := by
    intro r
    have hlocal (i : ι) :
        (P i).expect (fun ω => Real.exp (r * (X i ω - m i))) ≤
          Real.exp (r ^ 2 * (b i - a i) ^ 2 / 8) := by
      simpa [m] using xHoeffdingLemma (P i) (X i) (a i) (b i) r (hab i) (hX i)
    have hsum (ω : ∀ i, Ω i) : Z ω = ∑ i, (X i (ω i) - m i) := by
      dsimp [Z, m]
      rw [Finset.sum_sub_distrib]
    calc
      (FinProb.pi P).expect (fun ω => Real.exp (r * Z ω)) =
          (FinProb.pi P).expect
            (fun ω => Real.exp (r * ∑ i, (X i (ω i) - m i))) := by
        congr 1
        funext ω
        rw [hsum]
      _ = ∏ i, (P i).expect
            (fun ω => Real.exp (r * (X i ω - m i))) :=
          FinProb.expect_exp_sum_pi P (fun i ω => X i ω - m i) r
      _ ≤ ∏ i, Real.exp (r ^ 2 * (b i - a i) ^ 2 / 8) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          unfold FinProb.expect
          apply Finset.sum_nonneg
          intro ω hω
          exact mul_nonneg ((P i).nonneg ω) (Real.exp_nonneg _)
        · intro i hi
          exact hlocal i
      _ = Real.exp (r ^ 2 * S / 8) := by
        rw [← Real.exp_sum]
        congr 1
        dsimp [S]
        rw [← Finset.sum_div, ← Finset.mul_sum]
  let r : ℝ := 4 * t / S
  have hr : 0 < r := by dsimp [r]; positivity
  have hupper : (FinProb.pi P).pr (fun ω => t ≤ Z ω) ≤ Real.exp (-2 * t ^ 2 / S) := by
    calc
      _ ≤ Real.exp (-r * t) * (FinProb.pi P).expect (fun ω => Real.exp (r * Z ω)) :=
        FinProb.pr_exp_markov (FinProb.pi P) Z r t hr.le
      _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) :=
        mul_le_mul_of_nonneg_left (hmgf r) (Real.exp_nonneg _)
      _ = Real.exp (-2 * t ^ 2 / S) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        field_simp [ne_of_gt hS]
        ring
  have hlower : (FinProb.pi P).pr (fun ω => t ≤ -Z ω) ≤ Real.exp (-2 * t ^ 2 / S) := by
    calc
      _ ≤ Real.exp (-r * t) *
          (FinProb.pi P).expect (fun ω => Real.exp (r * -Z ω)) :=
        FinProb.pr_exp_markov (FinProb.pi P) (fun ω => -Z ω) r t hr.le
      _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        simpa [mul_neg, pow_two] using hmgf (-r)
      _ = Real.exp (-2 * t ^ 2 / S) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        field_simp [ne_of_gt hS]
        ring
  have hsplit : ∀ ω, t ≤ |Z ω| → t ≤ Z ω ∨ t ≤ -Z ω := by
    intro ω h
    by_cases hz : 0 ≤ Z ω
    · rw [abs_of_nonneg hz] at h
      exact Or.inl h
    · have hz' : Z ω ≤ 0 := le_of_not_ge hz
      rw [abs_of_nonpos hz'] at h
      exact Or.inr (by linarith)
  calc
    (FinProb.pi P).pr (fun ω => t ≤ |Z ω|) ≤
        (FinProb.pi P).pr (fun ω => t ≤ Z ω ∨ t ≤ -Z ω) :=
      FinProb.pr_mono _ _ _ hsplit
    _ ≤ (FinProb.pi P).pr (fun ω => t ≤ Z ω) +
        (FinProb.pi P).pr (fun ω => t ≤ -Z ω) := FinProb.pr_union_le _ _ _
    _ ≤ Real.exp (-2 * t ^ 2 / S) + Real.exp (-2 * t ^ 2 / S) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-2 * t ^ 2 / S) := by ring

/-- X-Chernoff: multiplicative upper tail for independent `[0,1]` finite summands. -/
theorem xChernoff_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    let μ : ℝ := ∑ i, (P i).expect (X i)
    (FinProb.pi P).pr (fun ω => (1 + δ) * μ ≤ ∑ i, X i (ω i)) ≤
      Real.exp (-μ * δ ^ 2 / (2 + δ)) := by
  classical
  let μ : ℝ := ∑ i, (P i).expect (X i)
  change (FinProb.pi P).pr (fun ω => (1 + δ) * μ ≤ ∑ i, X i (ω i)) ≤
    Real.exp (-μ * δ ^ 2 / (2 + δ))
  have hμ : 0 ≤ μ := by
    dsimp [μ]
    apply Finset.sum_nonneg
    intro i hi
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg ((P i).nonneg ω) (hX i ω).1
  let s : ℝ := Real.log (1 + δ)
  have hs : 0 ≤ s := by
    dsimp [s]
    apply Real.log_nonneg
    linarith
  have hexps : Real.exp s = 1 + δ := by
    dsimp [s]
    rw [Real.exp_log (by positivity)]
  have hlog := Real.le_log_one_add_of_nonneg hδ
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + δ)
  have hcalc : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    have hden : δ + 2 ≠ 0 := by linarith
    field_simp
    <;> ring
  have hrate : δ ^ 2 / (2 + δ) ≤ (1 + δ) * s - δ := by
    calc
      δ ^ 2 / (2 + δ) = (1 + δ) * (2 * δ / (δ + 2)) - δ := by
        rw [add_comm 2 δ]
        exact hcalc.symm
      _ ≤ (1 + δ) * s - δ := by
        have hmul' : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * s := by
          simpa [s] using hmul
        linarith
  have hrate' : -((1 + δ) * s - δ) ≤ -(δ ^ 2 / (2 + δ)) := by
    linarith
  have hexponent : -s * ((1 + δ) * μ) + (Real.exp s - 1) * μ ≤
      -μ * δ ^ 2 / (2 + δ) := by
    have hm := mul_le_mul_of_nonneg_left hrate' hμ
    rw [hexps]
    calc
      -s * ((1 + δ) * μ) + ((1 + δ) - 1) * μ =
          μ * -((1 + δ) * s - δ) := by ring
      _ ≤ μ * -(δ ^ 2 / (2 + δ)) := hm
      _ = -μ * δ ^ 2 / (2 + δ) := by ring
  calc
    (FinProb.pi P).pr (fun ω => (1 + δ) * μ ≤ ∑ i, X i (ω i)) ≤
        Real.exp (-s * ((1 + δ) * μ)) *
          (FinProb.pi P).expect (fun ω => Real.exp (s * ∑ i, X i (ω i))) :=
      FinProb.pr_exp_markov (FinProb.pi P) (fun ω => ∑ i, X i (ω i)) s
        ((1 + δ) * μ) hs
    _ ≤ Real.exp (-s * ((1 + δ) * μ)) *
          Real.exp ((Real.exp s - 1) * μ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa [μ] using FinProb.expect_exp_sum_le_of_mem_Icc P X hX s
    _ ≤ Real.exp (-μ * δ ^ 2 / (2 + δ)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexponent

/-- X-Chernoff: multiplicative lower tail for independent `[0,1]` finite summands. -/
theorem xChernoff_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let μ : ℝ := ∑ i, (P i).expect (X i)
    (FinProb.pi P).pr (fun ω => ∑ i, X i (ω i) ≤ (1 - δ) * μ) ≤
      Real.exp (-μ * δ ^ 2 / 2) := by
  classical
  let μ : ℝ := ∑ i, (P i).expect (X i)
  change (FinProb.pi P).pr (fun ω => ∑ i, X i (ω i) ≤ (1 - δ) * μ) ≤
    Real.exp (-μ * δ ^ 2 / 2)
  have hμ : 0 ≤ μ := by
    dsimp [μ]
    apply Finset.sum_nonneg
    intro i hi
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg ((P i).nonneg ω) (hX i ω).1
  have hexpneg : Real.exp (-δ) ≤ 1 - δ + δ ^ 2 / 2 := by
    have hquad := Real.quadratic_le_exp_of_nonneg hδ
    have hqpos : 0 < 1 + δ + δ ^ 2 / 2 := by positivity
    have htarget : 0 ≤ 1 - δ + δ ^ 2 / 2 := by nlinarith [sq_nonneg (1 - δ)]
    have hrecip : (Real.exp δ)⁻¹ ≤ (1 + δ + δ ^ 2 / 2)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos δ) hqpos).2 hquad
    have hsimple : (1 + δ + δ ^ 2 / 2)⁻¹ ≤ 1 - δ + δ ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀' hqpos]
      nlinarith [sq_nonneg (δ ^ 2)]
    calc
      Real.exp (-δ) = (Real.exp δ)⁻¹ := by rw [Real.exp_neg]
      _ ≤ (1 + δ + δ ^ 2 / 2)⁻¹ := hrecip
      _ ≤ 1 - δ + δ ^ 2 / 2 := hsimple
  have hterm : Real.exp (-δ) - 1 ≤ -δ + δ ^ 2 / 2 := by linarith
  have hexponent : δ * ((1 - δ) * μ) + (Real.exp (-δ) - 1) * μ ≤
      -μ * δ ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hterm hμ
    nlinarith [hm]
  calc
    (FinProb.pi P).pr (fun ω => ∑ i, X i (ω i) ≤ (1 - δ) * μ) ≤
        Real.exp (δ * ((1 - δ) * μ)) *
          (FinProb.pi P).expect (fun ω => Real.exp (-δ * ∑ i, X i (ω i))) := by
      have hev (ω : ∀ i, Ω i) :
          (∑ i, X i (ω i) ≤ (1 - δ) * μ) ↔
            -(1 - δ) * μ ≤ -(∑ i, X i (ω i)) := by
        rw [neg_mul, neg_le_neg_iff]
      have hmark := FinProb.pr_exp_markov (FinProb.pi P)
        (fun ω => -(∑ i, X i (ω i))) δ (-(1 - δ) * μ) hδ
      calc
        (FinProb.pi P).pr (fun ω => ∑ i, X i (ω i) ≤ (1 - δ) * μ) =
            (FinProb.pi P).pr (fun ω => -(1 - δ) * μ ≤ -(∑ i, X i (ω i))) := by
          congr 1
          funext ω
          exact propext (hev ω)
        _ ≤ Real.exp (-δ * (-(1 - δ) * μ)) *
            (FinProb.pi P).expect
              (fun ω => Real.exp (δ * (-(∑ i, X i (ω i))))) := hmark
        _ = Real.exp (δ * ((1 - δ) * μ)) *
            (FinProb.pi P).expect
              (fun ω => Real.exp (-δ * ∑ i, X i (ω i))) := by
          congr 1
          · congr 1 <;> ring
          · congr 1
            funext ω
            congr 1 <;> ring
    _ ≤ Real.exp (δ * ((1 - δ) * μ)) *
          Real.exp ((Real.exp (-δ) - 1) * μ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa [μ, mul_comm] using
        FinProb.expect_exp_sum_le_of_mem_Icc P X hX (-δ)
    _ ≤ Real.exp (-μ * δ ^ 2 / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexponent

/-- X-Azuma: lower-tail Azuma--Hoeffding for a finite filtration and increments with conditional mean at
least `μ i`. A fiber of `history i.castSucc` is the information available before increment `i`; `project`
states that consecutive histories form a filtration. -/
theorem xAzuma {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ) (μ lo hi : Fin k → ℝ)
    (hbound : ∀ i ω, lo i ≤ Δ i ω ∧ Δ i ω ≤ hi i)
    (hmean : ∀ i (h : H i.castSucc),
      P.pr (fun ω => history i.castSucc ω = h) = 0 ∨
        μ i * P.pr (fun ω => history i.castSucc ω = h) ≤
          (∑ ω, if history i.castSucc ω = h then P.w ω * Δ i ω else 0))
    (hwidth : 0 < ∑ i, (hi i - lo i) ^ 2) (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (hi i - lo i) ^ 2) := by
  classical
  sorry

/-- X-Freedman: finite Freedman tail for conditionally centered, bounded martingale differences with a
deterministic bound on their total predictable variance. -/
theorem xFreedman {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hbound : ∀ i ω, |Δ i ω| ≤ c)
    (hmean : ∀ i (h : H i.castSucc),
      (∑ ω, (if history i.castSucc ω = h then P.w ω * Δ i ω else 0)) = 0)
    (hvariance : ∀ i (h : H i.castSucc),
      (∑ ω, if history i.castSucc ω = h then P.w ω * (Δ i ω) ^ 2 else 0) ≤
        v i * P.pr (fun ω => history i.castSucc ω = h))
    (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => t ≤ ∑ i, Δ i ω) ≤
      Real.exp (-t ^ 2 / (2 * (∑ i, v i + c * t / 3))) := by
  classical
  sorry

/-- X-McDiarmid: bounded differences for a real-valued function of independent finite coordinates with
arbitrary coordinate laws. -/
theorem xMcDiarmid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ i (ω ω' : ∀ j, Ω j), (∀ j, j ≠ i → ω j = ω' j) → |f ω - f ω'| ≤ c i)
    (hwidth : 0 < ∑ i, c i ^ 2) (t : ℝ) (ht : 0 < t) :
    (FinProb.pi P).pr (fun ω => t ≤ |f ω - (FinProb.pi P).expect f|) ≤
      2 * Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by
  sorry

end HypercubeRamsey
