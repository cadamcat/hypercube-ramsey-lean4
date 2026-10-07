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
open Classical

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

/-- Expectation under a law conditioned on an event, written as an unnormalised fiber sum. -/
theorem FinProb.expect_cond_eq_sum {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (f : Ω → ℝ) :
    (P.cond A hA).expect f =
      (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
  classical
  simp only [FinProb.expect, FinProb.cond]
  calc
    _ = ∑ ω, (if A ω then P.w ω * f ω else 0) / P.pr A := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : A ω <;> simp [h] <;> field_simp [ne_of_gt hA] <;> ring
    _ = (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
      rw [Finset.sum_div]

/-- Conditional Hoeffding bound on one history fiber, when its conditional mean is at least `μ`. -/
theorem FinProb.expect_exp_neg_centered_cond_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (X : Ω → ℝ)
    (a b μ s : ℝ) (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b)
    (hs : 0 ≤ s)
    (hmean : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0) :
    (P.cond A hA).expect (fun ω => Real.exp (-s * (X ω - μ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  let Q := P.cond A hA
  have hμ : μ ≤ Q.expect X := by
    rw [FinProb.expect_cond_eq_sum]
    exact (le_div_iff₀ hA).2 hmean
  let mQ : ℝ := Q.expect X
  have hhoeffding := xHoeffdingLemma Q X a b (-s) hab hX
  have hhoeffding' : Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
    simpa [mQ, pow_two] using hhoeffding
  have hfactor : Q.expect (fun ω => Real.exp (-s * (X ω - μ))) =
      Real.exp (s * (μ - mQ)) *
        Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    change Q.w ω * Real.exp (-s * (X ω - μ)) =
      Real.exp (s * (μ - mQ)) * (Q.w ω * Real.exp (-s * (X ω - mQ)))
    have he : -s * (X ω - μ) = s * (μ - mQ) + -s * (X ω - mQ) := by ring
    rw [he, Real.exp_add]
    ring_nf
  have hscalar : Real.exp (s * (μ - mQ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    dsimp [mQ]
    nlinarith
  have hcenter_nonneg : 0 ≤ Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (Q.nonneg ω) (Real.exp_nonneg _)
  rw [hfactor]
  calc
    _ ≤ 1 * Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) :=
      mul_le_mul_of_nonneg_right hscalar hcenter_nonneg
    _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
      simpa using hhoeffding'

/-- A point's weight is bounded by the mass of any event containing it. -/
theorem FinProb.pr_fiber_single_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω : Ω) (hω : A ω) :
    P.w ω ≤ P.pr A := by
  classical
  unfold FinProb.pr
  calc
    P.w ω = if A ω then P.w ω else 0 := by simp [hω]
    _ ≤ ∑ x, if A x then P.w x else 0 :=
      Finset.single_le_sum
        (f := fun x => if A x then P.w x else 0)
        (fun x hx => by
          split_ifs with hAx
          · exact P.nonneg x
          · exact le_rfl)
        (Finset.mem_univ ω)

/-- The unnormalised exponential moment on a history fiber has the conditional Hoeffding bound. -/
theorem FinProb.fiber_exp_neg_centered_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (X : Ω → ℝ) (a b μ s : ℝ)
    (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b) (hs : 0 ≤ s)
    (hmean : P.pr A = 0 ∨ μ * P.pr A ≤
      ∑ ω, if A ω then P.w ω * X ω else 0) :
    (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
      P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  have hqnonneg : 0 ≤ P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    by_cases hA : A ω
    · simp [hA, P.nonneg ω]
    · simp [hA]
  by_cases hq : P.pr A = 0
  · have hzero (ω : Ω) (hω : A ω) : P.w ω = 0 := by
      have hle := FinProb.pr_fiber_single_le P A ω hω
      rw [hq] at hle
      exact le_antisymm hle (P.nonneg ω)
    have hsum :
        (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hA : A ω
      · simp [hA, hzero ω hA]
      · simp [hA]
    rw [hsum, hq]
    simp
  · have hqpos : 0 < P.pr A := lt_of_le_of_ne hqnonneg (Ne.symm hq)
    have hmean' : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0 := by
      rcases hmean with hz | hmean'
      · exact (hq hz).elim
      · exact hmean'
    have hcond := FinProb.expect_exp_neg_centered_cond_le
      P A hqpos X a b μ s hab hX hs hmean'
    rw [FinProb.expect_cond_eq_sum] at hcond
    have hmul := (div_le_iff₀ hqpos).mp hcond
    calc
      _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) * P.pr A := hmul
      _ = P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by ring

/-- A nonnegative factor measurable on history fibers can be carried through a conditional
Hoeffding bound. -/
theorem FinProb.expect_mul_fiber_exp_neg_centered_le
    {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]
    (P : FinProb Ω) (history : Ω → H) (F X : Ω → ℝ) (μ s E : ℝ)
    (hFfiber : ∀ ω ω', history ω = history ω' → F ω = F ω')
    (hFnonneg : ∀ ω, 0 ≤ F ω)
    (hlocal : ∀ h : H,
      (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
        (∑ ω, if history ω = h then P.w ω else 0) * E) :
    P.expect (fun ω => F ω * Real.exp (-s * (X ω - μ))) ≤ E * P.expect F := by
  classical
  have hfiber (h : H) :
      (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) ≤
        E * (∑ ω, if history ω = h then P.w ω * F ω else 0) := by
    by_cases hex : ∃ ω, history ω = h
    · obtain ⟨ω₀, hω₀⟩ := hex
      have hleft :
          (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) *
              (F ω₀ * Real.exp (-s * (X ω - μ))) := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then
                P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh] <;> ring
      have hright :
          (∑ ω, if history ω = h then P.w ω * F ω else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) * F ω₀ := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF, mul_comm]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh, mul_comm]
      rw [hleft, hright]
      calc
        F ω₀ * (∑ ω, if history ω = h then
            P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
            F ω₀ * ((∑ ω, if history ω = h then P.w ω else 0) * E) :=
          mul_le_mul_of_nonneg_left (hlocal h) (hFnonneg ω₀)
        _ = E * (F ω₀ * ∑ ω, if history ω = h then P.w ω else 0) := by ring
    · have hnone (ω : Ω) : history ω ≠ h := by
        intro heq
        exact hex ⟨ω, heq⟩
      simp [hnone]
  have hpartition (ω : Ω) :
      P.w ω * (F ω * Real.exp (-s * (X ω - μ))) =
        ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  have hsumF :
      (∑ h : H, ∑ ω, if history ω = h then P.w ω * F ω else 0) = P.expect F := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * (F ω * Real.exp (-s * (X ω - μ)))) =
        ∑ ω, ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact hpartition ω
    _ = ∑ h : H, ∑ ω, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := Finset.sum_comm
    _ ≤ ∑ h : H, E * (∑ ω, if history ω = h then P.w ω * F ω else 0) :=
      Finset.sum_le_sum fun h hh => hfiber h
    _ = E * P.expect F := by
      rw [← Finset.mul_sum, hsumF]

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
least `μ i`. Every earlier increment is determined by the current history; `project` states that
consecutive histories form a filtration. -/
theorem xAzuma {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ ω ω', history ⟨m, Nat.lt_succ_of_le hm⟩ ω = history ⟨m, Nat.lt_succ_of_le hm⟩ ω' →
        Δ i ω = Δ i ω')
    (μ lo hi : Fin k → ℝ)
    (hbound : ∀ i ω, lo i ≤ Δ i ω ∧ Δ i ω ≤ hi i)
    (hmean : ∀ i (h : H i.castSucc),
      P.pr (fun ω => history i.castSucc ω = h) = 0 ∨
        μ i * P.pr (fun ω => history i.castSucc ω = h) ≤
          (∑ ω, if history i.castSucc ω = h then P.w ω * Δ i ω else 0))
    (hwidth : 0 < ∑ i, (hi i - lo i) ^ 2) (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (hi i - lo i) ^ 2) := by
  classical
  let yNat : ℕ → Ω → ℝ := fun j ω =>
    if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0
  let widthNat : ℕ → ℝ := fun j =>
    if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0
  let S : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ Finset.range m, yNat j ω
  let W : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, widthNat j
  let U : ℝ := ∑ i, (hi i - lo i) ^ 2
  have hU : 0 < U := by simpa [U] using hwidth
  let s : ℝ := 4 * t / U
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hΩ : Nonempty Ω := by
    by_contra hne
    haveI : IsEmpty Ω := not_nonempty_iff.mp hne
    have hsum : (∑ ω, P.w ω) = 0 := by simp
    rw [P.sum_eq_one] at hsum
    norm_num at hsum
  have hmgf : ∀ m, m ≤ k →
      P.expect (fun ω => Real.exp (-s * S m ω)) ≤
        Real.exp (s ^ 2 * W m / 8) := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp [S, W, FinProb.expect, P.sum_eq_one]
    | succ m ih =>
      intro hm
      have hm_lt : m < k := by omega
      have hm_le : m ≤ k := by omega
      let i : Fin k := ⟨m, hm_lt⟩
      have hstep (ω : Ω) : S (m + 1) ω = S m ω + (Δ i ω - μ i) := by
        simp [S, yNat, Finset.sum_range_succ, i, hm_lt]
      have hwidthStep : W (m + 1) = W m + (hi i - lo i) ^ 2 := by
        simp [W, widthNat, Finset.sum_range_succ, i, hm_lt]
      have hab : lo i ≤ hi i := by
        obtain ⟨ω⟩ := hΩ
        exact (hbound i ω).1.trans (hbound i ω).2
      have hlocal (g : H i.castSucc) :
          (∑ ω, if history i.castSucc ω = g then
            P.w ω * Real.exp (-s * (Δ i ω - μ i)) else 0) ≤
          (∑ ω, if history i.castSucc ω = g then P.w ω else 0) *
            Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) := by
        have hlocal' := FinProb.fiber_exp_neg_centered_le P
          (fun ω => history i.castSucc ω = g) (Δ i) (lo i) (hi i) (μ i) s
          hab (fun ω => hbound i ω) hs (hmean i g)
        have hprob : P.pr (fun ω => history i.castSucc ω = g) =
            ∑ ω, if history i.castSucc ω = g then P.w ω else 0 := by
          unfold FinProb.pr
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hEq : history i.castSucc ω = g <;> simp [hEq]
        rw [hprob] at hlocal'
        exact hlocal'
      have hSfiber (ω ω' : Ω)
          (hh : history i.castSucc ω = history i.castSucc ω') : S m ω = S m ω' := by
        unfold S
        apply Finset.sum_congr rfl
        intro j hj
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hj_k : j < k := lt_of_lt_of_le hj_lt (Nat.le_of_lt i.isLt)
        have hΔ := hadapted m hm_le ⟨j, hj_k⟩ hj_lt ω ω' hh
        simp [yNat, hj_k, hΔ]
      have hstepMgf :
          P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro ω hω
        change P.w ω * Real.exp (-s * S (m + 1) ω) =
          P.w ω * (Real.exp (-s * S m ω) * Real.exp (-s * (Δ i ω - μ i)))
        have he : -s * S (m + 1) ω =
            (-s * S m ω) + (-s * (Δ i ω - μ i)) := by
          rw [hstep ω]
          ring
        rw [he, Real.exp_add]
      have htail := FinProb.expect_mul_fiber_exp_neg_centered_le P
        (history i.castSucc) (fun ω => Real.exp (-s * S m ω)) (Δ i) (μ i) s
        (Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8))
        (fun ω ω' hh => by rw [hSfiber ω ω' hh])
        (fun ω => Real.exp_nonneg _)
        hlocal
      calc
        P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := hstepMgf
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              P.expect (fun ω => Real.exp (-s * S m ω)) := htail
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              Real.exp (s ^ 2 * W m / 8) :=
            mul_le_mul_of_nonneg_left (ih hm_le) (Real.exp_nonneg _)
        _ = Real.exp (s ^ 2 * W (m + 1) / 8) := by
          rw [hwidthStep, ← Real.exp_add]
          congr 1
          ring
  have hWfull : W k = ∑ i, (hi i - lo i) ^ 2 := by
    dsimp [W, widthNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0)]
    simp
  have hsumY (ω : Ω) : S k ω = ∑ i, (Δ i ω - μ i) := by
    dsimp [S, yNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0)]
    simp
  have hsumCentered (ω : Ω) :
      (∑ i, Δ i ω) - ∑ i, μ i = S k ω := by
    calc
      (∑ i, Δ i ω) - ∑ i, μ i = ∑ i, (Δ i ω - μ i) := by
        rw [Finset.sum_sub_distrib]
      _ = S k ω := (hsumY ω).symm
  have hevent (ω : Ω) :
      (∑ i, Δ i ω < (∑ i, μ i) - t) →
        t ≤ -((∑ i, Δ i ω) - ∑ i, μ i) := by
    intro h
    linarith
  have hmark := FinProb.pr_exp_markov P
    (fun ω => -((∑ i, Δ i ω) - ∑ i, μ i)) s t hs
  have hmgfMark :
      P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) ≤
        Real.exp (s ^ 2 * U / 8) := by
    have hfun : (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) =
        (fun ω => Real.exp (-s * S k ω)) := by
      funext ω
      rw [hsumCentered]
      congr 1
      ring
    rw [hfun]
    simpa [hWfull, U] using hmgf k le_rfl
  calc
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
        P.pr (fun ω => t ≤ -((∑ i, Δ i ω) - ∑ i, μ i)) :=
      FinProb.pr_mono P _ _ hevent
    _ ≤ Real.exp (-s * t) *
          P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) := hmark
    _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * U / 8) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact hmgfMark
    _ = Real.exp (-2 * t ^ 2 / U) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp [ne_of_gt hU]
      ring

/-- The scalar exponential bound used in Freedman's conditional MGF estimate. -/
private theorem real_exp_le_freedman_quadratic {x r : ℝ}
    (hr0 : 0 ≤ r) (hr3 : r < 3) (hx : |x| ≤ r) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r / 3)) := by
  by_cases hxneg : x ≤ 0
  · let q : ℝ := -x
    have hq : 0 ≤ q := by dsimp [q]; linarith
    have hquad := Real.quadratic_le_exp_of_nonneg hq
    have hden : 0 < 1 + q + q ^ 2 / 2 := by positivity
    have hinv : (Real.exp q)⁻¹ ≤ (1 + q + q ^ 2 / 2)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos q) hden).2 hquad
    have hsimple : (1 + q + q ^ 2 / 2)⁻¹ ≤ 1 - q + q ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hden]
      nlinarith [sq_nonneg (q ^ 2)]
    have hxexp : Real.exp x = (Real.exp q)⁻¹ := by
      rw [show x = -q by dsimp [q]; ring, Real.exp_neg]
    have hcoeff : (1 / 2 : ℝ) ≤ 1 / (2 * (1 - r / 3)) := by
      have hdenr : 0 < 2 * (1 - r / 3) := by linarith
      have hdenle : 2 * (1 - r / 3) ≤ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (by norm_num) hdenr hdenle
    rw [hxexp]
    have hqeq : q = -x := by dsimp [q]
    calc
      (Real.exp q)⁻¹ ≤ (1 + q + q ^ 2 / 2)⁻¹ := hinv
      _ ≤ 1 - q + q ^ 2 / 2 := hsimple
      _ ≤ 1 + x + x ^ 2 / 2 := by
        rw [hqeq]
        ring_nf
        exact le_rfl
      _ ≤ 1 + x + x ^ 2 / (2 * (1 - r / 3)) := by
        calc
          1 + x + x ^ 2 / 2 = 1 + x + x ^ 2 * (1 / 2) := by ring
          _ ≤ 1 + x + x ^ 2 * (1 / (2 * (1 - r / 3))) := by
            gcongr
          _ = 1 + x + x ^ 2 / (2 * (1 - r / 3)) := by ring
  · have hxpos : 0 < x := lt_of_not_ge hxneg
    have hxle : x ≤ r := by simpa [abs_of_nonneg hxpos.le] using hx
    have hx3 : x / 3 < 1 := by linarith [hxle, hr3]
    let u : ℝ := x / 3
    let p : ℝ → ℝ := fun z => 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + 5 * z ^ 4 / 96
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have happrox := Real.exp_bound' hu0 hu1 (by norm_num : 0 < 4)
    have hpexp : Real.exp u ≤ p u := by
      calc
        Real.exp u ≤
            (∑ m ∈ Finset.range 4, u ^ m / m.factorial) +
              u ^ 4 * (4 + 1) / (Nat.factorial 4 * 4) := happrox
        _ = p u := by
          simp [p, Finset.sum_range_succ, Nat.factorial]
          ring
    have hpdiff : 0 ≤ 1 + 2 * u + (3 / 2 : ℝ) * u ^ 2 -
        (1 - u) * (p u) ^ 3 := by
      dsimp [p]
      ring_nf
      positivity
    have hdenu : 0 < 1 - u := by dsimp [u]; linarith [hx3]
    have hpoly : (p u) ^ 3 ≤ 1 + 3 * u + 9 * u ^ 2 / (2 * (1 - u)) := by
      have hquot : (p u) ^ 3 ≤
          (1 + 2 * u + (3 / 2 : ℝ) * u ^ 2) / (1 - u) := by
        rw [le_div_iff₀ hdenu]
        nlinarith
      calc
        (p u) ^ 3 ≤ (1 + 2 * u + (3 / 2 : ℝ) * u ^ 2) / (1 - u) := hquot
        _ = 1 + 3 * u + 9 * u ^ 2 / (2 * (1 - u)) := by
          field_simp [ne_of_gt hdenu]
          ring
    have hthree : 3 * u = x := by dsimp [u]; ring
    have hexp_small : Real.exp x ≤
        1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
      calc
        Real.exp x = Real.exp (3 * u) := by rw [hthree]
        _ = (Real.exp u) ^ 3 := Real.exp_nat_mul u 3
        _ ≤ (p u) ^ 3 := by gcongr
        _ ≤ 1 + 3 * u + 9 * u ^ 2 / (2 * (1 - u)) := hpoly
        _ = 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by rw [hthree]; dsimp [u]; ring
    have hdenr : 0 < 2 * (1 - r / 3) := by linarith
    have hdenx : 0 < 2 * (1 - x / 3) := by linarith
    have hdenle : 2 * (1 - r / 3) ≤ 2 * (1 - x / 3) := by nlinarith [hxle]
    have hfrac := div_le_div_of_nonneg_left (sq_nonneg x) hdenr hdenle
    exact hexp_small.trans (by nlinarith)

/-- A centered bounded increment with controlled second moment has the Freedman MGF bound
on one history fiber. -/
private theorem FinProb.fiber_exp_bounded_variance_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (X : Ω → ℝ)
    (c s v : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (hv : 0 ≤ v) (hsc : s * c < 3)
    (hX : ∀ ω, |X ω| ≤ c)
    (hmean : (∑ ω, if A ω then P.w ω * X ω else 0) = 0)
    (hvariance : (∑ ω, if A ω then P.w ω * X ω ^ 2 else 0) ≤ v * P.pr A) :
    (∑ ω, if A ω then P.w ω * Real.exp (s * X ω) else 0) ≤
      P.pr A * Real.exp ((s ^ 2 / (2 * (1 - s * c / 3))) * v) := by
  classical
  let C : ℝ := s ^ 2 / (2 * (1 - s * c / 3))
  have hden : 0 < 2 * (1 - s * c / 3) := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : 0 ≤ P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    by_cases hA : A ω <;> simp [hA, P.nonneg ω]
  have hmass : (∑ ω, if A ω then P.w ω else 0) = P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hA : A ω <;> simp [hA]
  have hmeanFactor :
      (∑ ω, if A ω then P.w ω * (s * X ω) else 0) =
        s * (∑ ω, if A ω then P.w ω * X ω else 0) := by
    calc
      _ = ∑ ω, (if A ω then P.w ω * X ω else 0) * s := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA, mul_comm] <;> ring
      _ = (∑ ω, if A ω then P.w ω * X ω else 0) * s := (Finset.sum_mul ..).symm
      _ = _ := by ring
  have hvarFactor :
      (∑ ω, if A ω then P.w ω * (C * X ω ^ 2) else 0) =
        C * (∑ ω, if A ω then P.w ω * X ω ^ 2 else 0) := by
    calc
      _ = ∑ ω, (if A ω then P.w ω * X ω ^ 2 else 0) * C := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA, mul_comm, mul_left_comm, mul_assoc]
      _ = (∑ ω, if A ω then P.w ω * X ω ^ 2 else 0) * C := (Finset.sum_mul ..).symm
      _ = _ := by ring
  have hpolySum :
      (∑ ω, if A ω then P.w ω * (1 + s * X ω + C * X ω ^ 2) else 0) =
        P.pr A + s * (∑ ω, if A ω then P.w ω * X ω else 0) +
          C * (∑ ω, if A ω then P.w ω * X ω ^ 2 else 0) := by
    calc
      _ = ∑ ω, ((if A ω then P.w ω else 0) +
          (if A ω then P.w ω * (s * X ω) else 0) +
          (if A ω then P.w ω * (C * X ω ^ 2) else 0)) := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA] <;> ring
      _ = (∑ ω, if A ω then P.w ω else 0) +
          (∑ ω, if A ω then P.w ω * (s * X ω) else 0) +
          (∑ ω, if A ω then P.w ω * (C * X ω ^ 2) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by rw [hmass, hmeanFactor, hvarFactor]
  have hpoint (ω : Ω) :
      Real.exp (s * X ω) ≤ 1 + s * X ω + C * X ω ^ 2 := by
    have harg : |s * X ω| ≤ s * c := by
      rw [abs_mul, abs_of_nonneg hs]
      exact mul_le_mul_of_nonneg_left (hX ω) hs
    have hex := real_exp_le_freedman_quadratic (mul_nonneg hs hc) hsc harg
    calc
      Real.exp (s * X ω) ≤
          1 + s * X ω + (s * X ω) ^ 2 / (2 * (1 - s * c / 3)) := hex
      _ = 1 + s * X ω + C * X ω ^ 2 := by dsimp [C]; ring
  have hsum :
      (∑ ω, if A ω then P.w ω * Real.exp (s * X ω) else 0) ≤
        P.pr A * Real.exp (C * v) := by
    calc
      _ ≤ ∑ ω, if A ω then
            P.w ω * (1 + s * X ω + C * X ω ^ 2) else 0 := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hA : A ω
        · simp [hA]
          exact mul_le_mul_of_nonneg_left (hpoint ω) (P.nonneg ω)
        · simp [hA]
      _ = P.pr A + s * 0 + C * (∑ ω, if A ω then P.w ω * X ω ^ 2 else 0) := by
        rw [hpolySum, hmean]
      _ ≤ P.pr A * (1 + C * v) := by
        have hcv := mul_le_mul_of_nonneg_left hvariance hC
        dsimp [C] at hcv ⊢
        nlinarith
      _ ≤ P.pr A * Real.exp (C * v) := by
        apply mul_le_mul_of_nonneg_left _ hq
        simpa [add_comm] using Real.add_one_le_exp (C * v)
  simpa [C] using hsum

/-- X-Freedman: finite Freedman tail for conditionally centered, bounded martingale differences with a
deterministic bound on their total predictable variance. Every earlier increment is determined by the
current history. -/
theorem xFreedman {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ ω ω', history ⟨m, Nat.lt_succ_of_le hm⟩ ω = history ⟨m, Nat.lt_succ_of_le hm⟩ ω' →
        Δ i ω = Δ i ω')
    (c : ℝ) (hc : 0 < c)
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
  let Vtot : ℝ := ∑ i, v i
  have hVnonneg : 0 ≤ Vtot := by
    dsimp [Vtot]
    exact Finset.sum_nonneg fun i hi => hv i
  by_cases hVzero : Vtot = 0
  · have hvzero (i : Fin k) : v i = 0 := by
      have hle : v i ≤ Vtot := by
        dsimp [Vtot]
        exact Finset.single_le_sum (f := v) (fun j hj => hv j) (Finset.mem_univ i)
      rw [hVzero] at hle
      exact le_antisymm hle (hv i)
    have hzeroΔ (ω : Ω) (hweight : 0 < P.w ω) (i : Fin k) : Δ i ω = 0 := by
      let g : H i.castSucc := history i.castSucc ω
      have hsingle : P.w ω * (Δ i ω) ^ 2 ≤
          ∑ ω', if history i.castSucc ω' = g then
            P.w ω' * (Δ i ω') ^ 2 else 0 := by
        have hs := Finset.single_le_sum
          (f := fun ω' => if history i.castSucc ω' = g then
            P.w ω' * (Δ i ω') ^ 2 else 0)
          (fun ω' hω' => by
            by_cases hEq : history i.castSucc ω' = g
            · simp [hEq]
              exact mul_nonneg (P.nonneg ω') (sq_nonneg _)
            · simp [hEq])
          (Finset.mem_univ ω)
        simpa [g] using hs
      have hsecond := hvariance i g
      have hle := hsingle.trans (by simpa [hvzero i] using hsecond)
      have hnonneg : 0 ≤ P.w ω * (Δ i ω) ^ 2 :=
        mul_nonneg (P.nonneg ω) (sq_nonneg _)
      have hprod : P.w ω * (Δ i ω) ^ 2 = 0 := le_antisymm hle hnonneg
      rcases mul_eq_zero.mp hprod with hW | hsq
      · exact (ne_of_gt hweight hW).elim
      · nlinarith
    have hbad : P.pr (fun ω => t ≤ ∑ i, Δ i ω) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hE : t ≤ ∑ i, Δ i ω
      · have hw : P.w ω = 0 := by
          by_contra hn
          have hwpos : 0 < P.w ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hn)
          have hsum : (∑ i, Δ i ω) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            exact hzeroΔ ω hwpos i
          linarith
        simp [hE, hw]
      · simp [hE]
    rw [hbad]
    exact Real.exp_nonneg _
  · have hVpos : 0 < Vtot := lt_of_le_of_ne hVnonneg (Ne.symm hVzero)
    let D : ℝ := Vtot + c * t / 3
    have hD : 0 < D := by dsimp [D]; positivity
    let s : ℝ := t / D
    have hs : 0 < s := by dsimp [s]; positivity
    have hnum : t * c < 3 * D := by
      dsimp [D]
      nlinarith
    have hsc3 : s * c / 3 < 1 := by
      have hsEq : s * c / 3 = (t * c) / (3 * D) := by
        dsimp [s]
        field_simp
      rw [hsEq]
      apply (div_lt_iff₀ (by positivity : 0 < 3 * D)).2
      nlinarith [hnum]
    have hsc : s * c < 3 := by nlinarith [hsc3]
    let C : ℝ := s ^ 2 / (2 * (1 - s * c / 3))
    have hdenC : 0 < 2 * (1 - s * c / 3) := by linarith [hsc3]
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let xNat : ℕ → Ω → ℝ := fun j ω =>
      if hj : j < k then Δ ⟨j, hj⟩ ω else 0
    let vNat : ℕ → ℝ := fun j =>
      if hj : j < k then v ⟨j, hj⟩ else 0
    let S : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ Finset.range m, xNat j ω
    let Vprefix : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, vNat j
    let M : ℕ → Ω → ℝ := fun m ω => Real.exp (s * S m ω - C * Vprefix m)
    have hlocal (i : Fin k) (g : H i.castSucc) :
        (∑ ω, if history i.castSucc ω = g then
          P.w ω * Real.exp (s * Δ i ω) else 0) ≤
          (∑ ω, if history i.castSucc ω = g then P.w ω else 0) *
            Real.exp (C * v i) := by
      have hlocal' := FinProb.fiber_exp_bounded_variance_le P
        (fun ω => history i.castSucc ω = g) (Δ i) c s (v i) hc.le hs.le (hv i) hsc
        (hbound i) (hmean i g) (hvariance i g)
      have hprob : P.pr (fun ω => history i.castSucc ω = g) =
          ∑ ω, if history i.castSucc ω = g then P.w ω else 0 := by
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hEq : history i.castSucc ω = g <;> simp [hEq]
      rw [hprob] at hlocal'
      exact hlocal'
    have hlocalNeg (i : Fin k) (g : H i.castSucc) :
        (∑ ω, if history i.castSucc ω = g then
          P.w ω * Real.exp (-s * (-Δ i ω - 0)) else 0) ≤
          (∑ ω, if history i.castSucc ω = g then P.w ω else 0) *
            Real.exp (C * v i) := by
      simpa [mul_neg, neg_mul] using hlocal i g
    have hmgf : ∀ m, m ≤ k → P.expect (M m) ≤ 1 := by
      intro m
      induction m with
      | zero =>
        intro hm
        simp [M, S, Vprefix, FinProb.expect, P.sum_eq_one]
      | succ m ih =>
        intro hm
        have hm_lt : m < k := by omega
        have hm_le : m ≤ k := by omega
        let i : Fin k := ⟨m, hm_lt⟩
        have hSstep (ω : Ω) : S (m + 1) ω = S m ω + Δ i ω := by
          simp [S, xNat, Finset.sum_range_succ, i, hm_lt]
        have hVstep : Vprefix (m + 1) = Vprefix m + v i := by
          simp [Vprefix, vNat, Finset.sum_range_succ, i, hm_lt]
        have hSfiber (ω ω' : Ω)
            (hh : history i.castSucc ω = history i.castSucc ω') : S m ω = S m ω' := by
          unfold S
          apply Finset.sum_congr rfl
          intro j hj
          have hj_lt : j < m := Finset.mem_range.mp hj
          have hj_k : j < k := lt_of_lt_of_le hj_lt (Nat.le_of_lt i.isLt)
          have hΔ := hadapted m hm_le ⟨j, hj_k⟩ hj_lt ω ω' hh
          simp [xNat, hj_k, hΔ]
        have htail := FinProb.expect_mul_fiber_exp_neg_centered_le P
          (history i.castSucc) (M m) (fun ω => -Δ i ω) 0 s (Real.exp (C * v i))
          (fun ω ω' hh => by
            unfold M
            rw [hSfiber ω ω' hh])
          (fun ω => Real.exp_nonneg _)
          (by
            intro g
            exact hlocalNeg i g)
        have htail' : P.expect (fun ω => M m ω * Real.exp (s * Δ i ω)) ≤
            Real.exp (C * v i) * P.expect (M m) := by
          convert htail using 1
          congr 1
          funext ω
          congr 1
          ring
        have hstepM (ω : Ω) :
            M (m + 1) ω = Real.exp (-C * v i) *
              (M m ω * Real.exp (s * Δ i ω)) := by
          unfold M
          rw [hSstep ω, hVstep]
          have he : s * (S m ω + Δ i ω) - C * (Vprefix m + v i) =
              (-C * v i) + (s * S m ω - C * Vprefix m) + s * Δ i ω := by ring_nf
          rw [he, Real.exp_add, Real.exp_add]
          ring
        have hstepExpect : P.expect (M (m + 1)) =
            Real.exp (-C * v i) * P.expect (fun ω => M m ω * Real.exp (s * Δ i ω)) := by
          unfold FinProb.expect
          calc
            _ = ∑ ω, P.w ω * (Real.exp (-C * v i) *
                  (M m ω * Real.exp (s * Δ i ω))) := by
              apply Finset.sum_congr rfl
              intro ω hω
              rw [← hstepM ω]
            _ = Real.exp (-C * v i) *
                  ∑ ω, P.w ω * (M m ω * Real.exp (s * Δ i ω)) := by
              calc
                _ = ∑ ω, Real.exp (-C * v i) *
                    (P.w ω * (M m ω * Real.exp (s * Δ i ω))) := by
                  apply Finset.sum_congr rfl
                  intro ω hω
                  ring
                _ = Real.exp (-C * v i) *
                    ∑ ω, P.w ω * (M m ω * Real.exp (s * Δ i ω)) := by
                  rw [← Finset.mul_sum]
        calc
          P.expect (M (m + 1)) =
              Real.exp (-C * v i) * P.expect (fun ω => M m ω * Real.exp (s * Δ i ω)) :=
            hstepExpect
          _ ≤ Real.exp (-C * v i) *
              (Real.exp (C * v i) * P.expect (M m)) :=
            mul_le_mul_of_nonneg_left htail' (Real.exp_nonneg _)
          _ = P.expect (M m) := by
            calc
              Real.exp (-C * v i) * (Real.exp (C * v i) * P.expect (M m)) =
                  (Real.exp (-C * v i) * Real.exp (C * v i)) * P.expect (M m) := by ring
              _ = P.expect (M m) := by
                have hcancel : Real.exp (-C * v i) * Real.exp (C * v i) = 1 := by
                  rw [← Real.exp_add]
                  simp
                rw [hcancel, one_mul]
          _ = P.expect (M m) := by simp
          _ ≤ 1 := ih hm_le
    have hVfull : Vprefix k = Vtot := by
      dsimp [Vprefix, vNat, Vtot]
      rw [← Fin.sum_univ_eq_sum_range (fun j => if hj : j < k then v ⟨j, hj⟩ else 0)]
      simp
    have hSfull (ω : Ω) : S k ω = ∑ i, Δ i ω := by
      dsimp [S, xNat]
      rw [← Fin.sum_univ_eq_sum_range (fun j => if hj : j < k then Δ ⟨j, hj⟩ ω else 0)]
      simp
    have hmgfSum : P.expect (fun ω => Real.exp (s * ∑ i, Δ i ω)) ≤
        Real.exp (C * Vtot) := by
      have hfactor : P.expect (fun ω => Real.exp (s * ∑ i, Δ i ω)) =
          Real.exp (C * Vtot) * P.expect (M k) := by
        unfold FinProb.expect
        calc
          _ = ∑ ω, Real.exp (C * Vtot) *
              (P.w ω * Real.exp (s * S k ω - C * Vprefix k)) := by
            apply Finset.sum_congr rfl
            intro ω hω
            change P.w ω * Real.exp (s * ∑ i, Δ i ω) =
              Real.exp (C * Vtot) * (P.w ω * Real.exp (s * S k ω - C * Vprefix k))
            have he : s * ∑ i, Δ i ω = C * Vtot +
                (s * S k ω - C * Vprefix k) := by
              rw [hSfull ω, hVfull]
              ring
            rw [he, Real.exp_add]
            ring_nf
          _ = Real.exp (C * Vtot) *
              ∑ ω, P.w ω * Real.exp (s * S k ω - C * Vprefix k) := by
            calc
              _ = ∑ ω, Real.exp (C * Vtot) *
                  (P.w ω * Real.exp (s * S k ω - C * Vprefix k)) := by
                apply Finset.sum_congr rfl
                intro ω hω
                ring
              _ = _ := by rw [← Finset.mul_sum]
      rw [hfactor]
      calc
        Real.exp (C * Vtot) * P.expect (M k) ≤ Real.exp (C * Vtot) * 1 :=
          mul_le_mul_of_nonneg_left (hmgf k le_rfl) (Real.exp_nonneg _)
        _ = Real.exp (C * Vtot) := by simp
    have hmark := FinProb.pr_exp_markov P (fun ω => ∑ i, Δ i ω) s t hs.le
    calc
      P.pr (fun ω => t ≤ ∑ i, Δ i ω) ≤
          Real.exp (-s * t) * P.expect (fun ω => Real.exp (s * ∑ i, Δ i ω)) := hmark
      _ ≤ Real.exp (-s * t) * Real.exp (C * Vtot) :=
        mul_le_mul_of_nonneg_left hmgfSum (Real.exp_nonneg _)
      _ = Real.exp (-s * t + C * Vtot) := by rw [← Real.exp_add]
      _ = Real.exp (-t ^ 2 / (2 * D)) := by
        congr 1
        dsimp [s, C, D]
        field_simp [ne_of_gt hD, ne_of_gt hVpos]
        ring_nf

private theorem FinProb.expect_pi_cons {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin (n + 1) → FinProb α) (f : (Fin (n + 1) → α) → ℝ) :
    (FinProb.pi P).expect f =
      (P 0).expect (fun a =>
        (FinProb.pi (fun i : Fin n => P i.succ)).expect (fun x => f (Fin.cons a x))) := by
  classical
  have hsumCons {m : ℕ} (g : (Fin (m + 1) → α) → ℝ) :
      (∑ x : Fin (m + 1) → α, g x) = ∑ a : α, ∑ y : Fin m → α, g (Fin.cons a y) := by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => α)) g]
    rw [Fintype.sum_prod_type]
    rfl
  unfold FinProb.expect
  rw [hsumCons]
  simp [FinProb.pi, Finset.mul_sum, Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm]

private theorem FinProb.expect_map {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinProb α) (e : α → β) (f : β → ℝ) :
    (FinProb.map P e).expect f = P.expect (fun x => f (e x)) := by
  classical
  unfold FinProb.expect FinProb.map
  calc
    _ = ∑ b, ∑ a, (if e a = b then P.w a else 0) * f b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, (if e a = b then P.w a else 0) * f b := Finset.sum_comm
    _ = ∑ a, P.w a * f (e a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (e a)]
      · simp
      · intro b hb hbe
        simp [Ne.symm hbe]
      · simp

private theorem FinProb.eq_of_w_eq {α : Type*} [Fintype α] (P Q : FinProb α)
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw pnon psum =>
    cases Q with
    | mk qw qnon qsum =>
      have hw : pw = qw := funext h
      subst qw
      rfl

private theorem FinProb.map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] {α : Type*} [Fintype α] [DecidableEq α]
    (P : ∀ i, FinProb (Ω i)) (e : ∀ i, Ω i → α) :
    FinProb.pi (fun i => FinProb.map (P i) (e i)) =
      FinProb.map (FinProb.pi P) (fun x i => e i (x i)) := by
  classical
  apply FinProb.eq_of_w_eq
  intro y
  change (∏ i, ∑ a, if e i a = y i then (P i).w a else 0) =
    ∑ x : (∀ i, Ω i), if (fun i => e i (x i)) = y then ∏ i, (P i).w (x i) else 0
  calc
    _ = ∑ x : (∀ i, Ω i), ∏ i, (if e i (x i) = y i then (P i).w (x i) else 0) :=
      Fintype.prod_sum (fun i (a : Ω i) => if e i a = y i then (P i).w a else 0)
    _ = ∑ x : (∀ i, Ω i), if (fun i => e i (x i)) = y then ∏ i, (P i).w (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : (fun i => e i (x i)) = y
      · have hcoord : ∀ i, e i (x i) = y i := fun i => congrFun h i
        simp [hcoord]
      · have h' : ¬ ∀ i, e i (x i) = y i := by
          intro hxy
          apply h
          funext i
          exact hxy i
        push_neg at h'
        obtain ⟨i, hi⟩ := h'
        rw [if_neg h]
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        simp [hi]

private theorem FinProb.expect_pi_reindex {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (e : κ ≃ ι) (P : ∀ i, FinProb α) (f : (ι → α) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun j => P (e j))).expect (fun x => f (fun i => x (e.symm i))) := by
  classical
  let E : (κ → α) ≃ (ι → α) := {
    toFun := fun x i => x (e.symm i)
    invFun := fun y j => y (e j)
    left_inv := by
      intro x
      funext j
      simp
    right_inv := by
      intro y
      funext i
      simp }
  have hE (x : κ → α) : E x = fun i => x (e.symm i) := rfl
  have hweight (x : κ → α) :
      (FinProb.pi (fun j => P (e j))).w x = (FinProb.pi P).w (E x) := by
    simp only [FinProb.pi]
    rw [hE]
    simpa using (Equiv.prod_comp e (fun i => (P i).w (x (e.symm i))))
  unfold FinProb.expect
  calc
    _ = ∑ x, (FinProb.pi P).w (E x) * f (E x) :=
      (Equiv.sum_comp E (fun y => (FinProb.pi P).w y * f y)).symm
    _ = ∑ x, (FinProb.pi (fun j => P (e j))).w x * f (E x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hweight]
    _ = _ := by simp [FinProb.expect, E]

private theorem FinProb.expect_exp_bounded_differences_fin {α : Type*} [Fintype α] :
    ∀ n (P : Fin n → FinProb α) (f : (Fin n → α) → ℝ) (c : Fin n → ℝ)
      (hc : ∀ i, 0 ≤ c i)
      (hlip : ∀ i x x', (∀ j, j ≠ i → x j = x' j) → |f x - f x'| ≤ c i)
      (r : ℝ),
      (FinProb.pi P).expect (fun x => Real.exp (r * (f x - (FinProb.pi P).expect f))) ≤
        Real.exp (r ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
      intro P f c hc hlip r
      let x₀ : Fin 0 → α := fun i => Fin.elim0 i
      have hconst (x : Fin 0 → α) : f x = f x₀ := by
        congr 1
        funext i
        exact Fin.elim0 i
      have hweight : (FinProb.pi P).w (default : Fin 0 → α) = 1 := by
        have hsum := (FinProb.pi P).sum_eq_one
        simpa using hsum
      have hmean : (FinProb.pi P).expect f = f x₀ := by
        unfold FinProb.expect
        calc
          _ = ∑ x, (FinProb.pi P).w x * f x₀ := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hconst]
          _ = f x₀ := by
            calc
              _ = (∑ x, (FinProb.pi P).w x) * f x₀ := by rw [Finset.sum_mul]
              _ = f x₀ := by rw [(FinProb.pi P).sum_eq_one]; ring
      have hcent (x : Fin 0 → α) : f x - (FinProb.pi P).expect f = 0 := by
        rw [hmean, hconst]
        ring
      have hfun :
          (fun x => Real.exp (r * (f x - (FinProb.pi P).expect f))) = fun _ => 1 := by
        funext x
        simp [hcent x]
      have hval :
          (FinProb.pi P).expect
            (fun x => Real.exp (r * (f x - (FinProb.pi P).expect f))) = 1 := by
        rw [hfun]
        simp [FinProb.expect, hweight]
      simpa using hval.le
  | succ n ih =>
      intro P f c hc hlip r
      let P0 : FinProb α := P 0
      let Pt : Fin n → FinProb α := fun i => P i.succ
      let ctail : Fin n → ℝ := fun i => c i.succ
      let fp : α → (Fin n → α) → ℝ := fun a x => f (Fin.cons a x)
      let g : α → ℝ := fun a => (FinProb.pi Pt).expect (fp a)
      let S : ℝ := ∑ i : Fin n, ctail i ^ 2
      let I : ℝ := (FinProb.pi P).expect f
      have hα : Nonempty α := by
        by_contra hn
        haveI : IsEmpty α := not_nonempty_iff.mp hn
        have hs := (P 0).sum_eq_one
        simp at hs
      have huniv : (Finset.univ : Finset α).Nonempty := by
        obtain ⟨a⟩ := hα
        exact ⟨a, Finset.mem_univ _⟩
      have htail (a : α) : ∀ j x x',
          (∀ l, l ≠ j → x l = x' l) → |fp a x - fp a x'| ≤ ctail j := by
        intro j x x' hxx'
        apply hlip j.succ (Fin.cons a x) (Fin.cons a x')
        intro l hlj
        obtain rfl | ⟨l', rfl⟩ := l.eq_zero_or_eq_succ
        · rfl
        ·
          simp only [Fin.cons_succ]
          apply hxx' l'
          intro heq
          apply hlj
          simp [heq]
      have hgdiff : ∀ a a', |g a - g a'| ≤ c 0 := by
        intro a a'
        have hpoint (x : Fin n → α) :
            |fp a x - fp a' x| ≤ c 0 := by
          apply hlip 0 (Fin.cons a x) (Fin.cons a' x)
          intro j hj
          obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim (hj rfl)
          ·
            rfl
        have hsum_le (a a' : α) (h : ∀ x, fp a x ≤ fp a' x + c 0) :
            g a ≤ g a' + c 0 := by
          unfold g FinProb.expect
          calc
            _ ≤ ∑ x, (FinProb.pi Pt).w x * (fp a' x + c 0) := by
              apply Finset.sum_le_sum
              intro x hx
              exact mul_le_mul_of_nonneg_left (h x) ((FinProb.pi Pt).nonneg x)
            _ = g a' + c 0 := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
              simp [g, FinProb.expect, (FinProb.pi Pt).sum_eq_one]
        have hforward : ∀ x, fp a x ≤ fp a' x + c 0 := by
          intro x
          have h := (abs_le.mp (hpoint x)).2
          linarith
        have hbackward : ∀ x, fp a' x ≤ fp a x + c 0 := by
          intro x
          have h := (abs_le.mp (hpoint x)).1
          linarith
        apply abs_le.mpr
        constructor
        · have h := hsum_le a' a hbackward
          linarith
        · have h := hsum_le a a' hforward
          linarith
      have hmean : I = (P0).expect g := by
        simpa [P0, Pt, g, fp, I] using FinProb.expect_pi_cons P f
      have hhead : P0.expect (fun a => Real.exp (r * (g a - P0.expect g))) ≤
          Real.exp (r ^ 2 * (c 0) ^ 2 / 8) := by
        obtain ⟨aLo, haLo, hLo⟩ := Finset.exists_min_image
          (Finset.univ : Finset α) g huniv
        obtain ⟨aHi, haHi, hHi⟩ := Finset.exists_max_image
          (Finset.univ : Finset α) g huniv
        let lo : ℝ := g aLo
        let hi : ℝ := g aHi
        have hbounds (a : α) : lo ≤ g a ∧ g a ≤ hi := by
          constructor
          · exact hLo a (Finset.mem_univ _)
          · exact hHi a (Finset.mem_univ _)
        have hwidth : hi - lo ≤ c 0 := by
          have h := (abs_le.mp (hgdiff aHi aLo)).2
          dsimp [lo, hi]
          linarith
        have hinterval : lo ≤ hi := (hbounds aHi).1
        have hhoeff := xHoeffdingLemma P0 g lo hi r hinterval hbounds
        have hsq : (hi - lo) ^ 2 ≤ (c 0) ^ 2 := by
          have hnonneg : 0 ≤ hi - lo := sub_nonneg.mpr hinterval
          nlinarith [mul_nonneg (sub_nonneg.mpr hwidth) (add_nonneg (hc 0) hnonneg)]
        calc
          _ ≤ Real.exp (r ^ 2 * (hi - lo) ^ 2 / 8) := hhoeff
          _ ≤ Real.exp (r ^ 2 * (c 0) ^ 2 / 8) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hsq)]
      have htailMgf (a : α) :
          (FinProb.pi Pt).expect (fun x => Real.exp (r * (fp a x - g a))) ≤
            Real.exp (r ^ 2 * S / 8) := by
        simpa [S, ctail, fp, g, FinProb.expect] using
          ih Pt (fp a) ctail (fun j => hc j.succ) (htail a) r
      have hsplit :
          (FinProb.pi P).expect (fun x => Real.exp (r * (f x - I))) =
            P0.expect (fun a => (FinProb.pi Pt).expect
              (fun x => Real.exp (r * (fp a x - I)))) := by
        simpa [P0, Pt, fp, I] using
          FinProb.expect_pi_cons P (fun x => Real.exp (r * (f x - I)))
      have hfactor (a : α) :
          (FinProb.pi Pt).expect (fun x => Real.exp (r * (fp a x - I))) =
            Real.exp (r * (g a - I)) *
              (FinProb.pi Pt).expect (fun x => Real.exp (r * (fp a x - g a))) := by
        unfold FinProb.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have he : r * (fp a x - I) = r * (g a - I) + r * (fp a x - g a) := by ring
        change (FinProb.pi Pt).w x * Real.exp (r * (fp a x - I)) =
          Real.exp (r * (g a - I)) *
            ((FinProb.pi Pt).w x * Real.exp (r * (fp a x - g a)))
        rw [he, Real.exp_add]
        ring
      have hterm (a : α) :
          (FinProb.pi Pt).expect (fun x => Real.exp (r * (fp a x - I))) ≤
            Real.exp (r * (g a - I)) * Real.exp (r ^ 2 * S / 8) := by
        calc
          _ = Real.exp (r * (g a - I)) *
                (FinProb.pi Pt).expect (fun x => Real.exp (r * (fp a x - g a))) := hfactor a
          _ ≤ _ := mul_le_mul_of_nonneg_left (htailMgf a) (Real.exp_nonneg _)
      have hheadI :
          P0.expect (fun a => Real.exp (r * (g a - I))) ≤
            Real.exp (r ^ 2 * (c 0) ^ 2 / 8) := by
        simpa [hmean] using hhead
      have hmgf :
          (FinProb.pi P).expect (fun x => Real.exp (r * (f x - I))) ≤
            Real.exp (r ^ 2 * (c 0 ^ 2 + S) / 8) := by
        calc
          _ = P0.expect (fun a => (FinProb.pi Pt).expect
                (fun x => Real.exp (r * (fp a x - I)))) := hsplit
          _ ≤ P0.expect (fun a =>
                Real.exp (r * (g a - I)) * Real.exp (r ^ 2 * S / 8)) := by
            unfold FinProb.expect
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (hterm a) (P0.nonneg a)
          _ ≤ Real.exp (r ^ 2 * S / 8) *
                Real.exp (r ^ 2 * (c 0) ^ 2 / 8) := by
            calc
              _ = Real.exp (r ^ 2 * S / 8) *
                    P0.expect (fun a => Real.exp (r * (g a - I))) := by
                  unfold FinProb.expect
                  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ ≤ _ := mul_le_mul_of_nonneg_left hheadI (Real.exp_nonneg _)
          _ = Real.exp (r ^ 2 * (c 0 ^ 2 + S) / 8) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hsum : (∑ i : Fin (n + 1), c i ^ 2) = c 0 ^ 2 + S := by
        rw [Fin.sum_univ_succ]
      simpa [hsum] using hmgf

private theorem FinProb.expect_exp_bounded_differences {ι : Type*} [Fintype ι]
    [DecidableEq ι] {α : Type*} [Fintype α]
    (P : ι → FinProb α) (f : (ι → α) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ i x x', (∀ j, j ≠ i → x j = x' j) → |f x - f x'| ≤ c i)
    (r : ℝ) :
    (FinProb.pi P).expect (fun x => Real.exp (r * (f x - (FinProb.pi P).expect f))) ≤
      Real.exp (r ^ 2 * (∑ i, c i ^ 2) / 8) := by
  classical
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let Pfin : Fin n → FinProb α := fun j => P (e j)
  let ffin : (Fin n → α) → ℝ := fun x => f (fun i => x (e.symm i))
  let cfin : Fin n → ℝ := fun j => c (e j)
  have hmean : (FinProb.pi P).expect f = (FinProb.pi Pfin).expect ffin := by
    simpa [Pfin, ffin] using FinProb.expect_pi_reindex e P f
  have hLipFin : ∀ j x x', (∀ k, k ≠ j → x k = x' k) →
      |ffin x - ffin x'| ≤ cfin j := by
    intro j x x' hxx'
    apply hlip (e j) (fun i => x (e.symm i)) (fun i => x' (e.symm i))
    intro i hie
    have hne : e.symm i ≠ j := by
      intro hij
      apply hie
      simpa [hij] using (e.apply_symm_apply i).symm
    exact congrArg (fun y : α => y) (hxx' (e.symm i) hne)
  have hfin := FinProb.expect_exp_bounded_differences_fin n Pfin ffin cfin
    (fun j => hc (e j)) hLipFin r
  have hcenter : (FinProb.pi P).expect f = (FinProb.pi Pfin).expect ffin := hmean
  have htrans := FinProb.expect_pi_reindex e P
    (fun y => Real.exp (r * (f y - (FinProb.pi P).expect f)))
  calc
    _ = (FinProb.pi Pfin).expect
          (fun x => Real.exp (r * (ffin x - (FinProb.pi P).expect f))) := by
        simpa [Pfin, ffin] using htrans
    _ = (FinProb.pi Pfin).expect
          (fun x => Real.exp (r * (ffin x - (FinProb.pi Pfin).expect ffin))) := by
        rw [← hcenter]
    _ ≤ Real.exp (r ^ 2 * (∑ i, cfin i ^ 2) / 8) := hfin
    _ = Real.exp (r ^ 2 * (∑ i, c i ^ 2) / 8) := by
        exact congrArg Real.exp <| congrArg (fun z : ℝ => r ^ 2 * z / 8) <|
          Equiv.sum_comp e (fun i : ι => c i ^ 2)


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
  classical
  let A := ∀ i, Ω i
  letI : DecidableEq A := Classical.decEq A
  have hΩ : ∀ j, Nonempty (Ω j) := by
    intro j
    by_contra hn
    haveI : IsEmpty (Ω j) := not_nonempty_iff.mp hn
    have hs := (P j).sum_eq_one
    simp at hs
  let baseline : A := fun j => Classical.choice (hΩ j)
  let enc : ∀ i, Ω i → A := fun i a => Function.update baseline i a
  let Q : ∀ i, FinProb A := fun i => FinProb.map (P i) (enc i)
  let T : (∀ i, Ω i) → ∀ i, A := fun x i => enc i (x i)
  let g : (∀ i, A) → ℝ := fun x => f (fun i => x i i)
  let S : ℝ := ∑ i, c i ^ 2
  let I : ℝ := (FinProb.pi P).expect f
  have hmap : FinProb.pi Q = FinProb.map (FinProb.pi P) T := by
    simpa [Q, T, enc] using FinProb.map_pi P enc
  have hmean : (FinProb.pi Q).expect g = I := by
    rw [hmap, FinProb.expect_map]
    simp [g, T, enc, I]
  have hLip : ∀ i x x', (∀ j, j ≠ i → x j = x' j) → |g x - g x'| ≤ c i := by
    intro i x x' hxx'
    apply hlip i (fun j => x j j) (fun j => x' j j)
    intro j hji
    exact congrArg (fun y : A => y j) (hxx' j hji)
  have hmgfQ (r : ℝ) :
      (FinProb.pi Q).expect (fun x => Real.exp (r * (g x - (FinProb.pi Q).expect g))) ≤
        Real.exp (r ^ 2 * S / 8) := by
    simpa [S] using FinProb.expect_exp_bounded_differences Q g c hc hLip r
  have hmgf (r : ℝ) :
      (FinProb.pi P).expect (fun x => Real.exp (r * (f x - I))) ≤
        Real.exp (r ^ 2 * S / 8) := by
    have hfun : (fun x => Real.exp (r * (f x - I))) =
        (fun x => Real.exp (r * (g (T x) - (FinProb.pi Q).expect g))) := by
      funext x
      simp [g, T, I, hmean, enc]
    calc
      _ = (FinProb.pi P).expect
            (fun x => Real.exp (r * (g (T x) - (FinProb.pi Q).expect g))) := by rw [hfun]
      _ = (FinProb.map (FinProb.pi P) T).expect
            (fun y => Real.exp (r * (g y - (FinProb.pi Q).expect g))) :=
          (FinProb.expect_map (P := FinProb.pi P) (e := T)
            (f := fun y : ∀ i, A => Real.exp (r * (g y - (FinProb.pi Q).expect g)))).symm
      _ = (FinProb.pi Q).expect
            (fun y => Real.exp (r * (g y - (FinProb.pi Q).expect g))) := by rw [← hmap]
      _ ≤ Real.exp (r ^ 2 * S / 8) := hmgfQ r
  have hmgfNeg (r : ℝ) :
      (FinProb.pi P).expect (fun y => Real.exp (r * -(f y - I))) ≤
        Real.exp (r ^ 2 * S / 8) := by
    have hfun : (fun y => Real.exp (r * -(f y - I))) =
        (fun y => Real.exp ((-r) * (f y - I))) := by
      funext y
      congr 1
      ring
    have hneg := hmgf (-r)
    have hr2 : (-r) ^ 2 = r ^ 2 := by ring
    rw [hfun]
    simpa [hr2] using hneg
  have hS : 0 < S := by simpa [S] using hwidth
  let r : ℝ := 4 * t / S
  have hr : 0 < r := by dsimp [r]; positivity
  have hupper :
      (FinProb.pi P).pr (fun y => t ≤ f y - I) ≤ Real.exp (-2 * t ^ 2 / S) := by
    calc
      _ ≤ Real.exp (-r * t) *
          (FinProb.pi P).expect (fun y => Real.exp (r * (f y - I))) :=
        FinProb.pr_exp_markov (FinProb.pi P) (fun y => f y - I) r t hr.le
      _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) :=
        mul_le_mul_of_nonneg_left (hmgf r) (Real.exp_nonneg _)
      _ = Real.exp (-2 * t ^ 2 / S) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        field_simp [ne_of_gt hS]
        ring
  have hlower :
      (FinProb.pi P).pr (fun y => t ≤ -(f y - I)) ≤ Real.exp (-2 * t ^ 2 / S) := by
    calc
      _ ≤ Real.exp (-r * t) *
          (FinProb.pi P).expect (fun y => Real.exp (r * -(f y - I))) :=
        FinProb.pr_exp_markov (FinProb.pi P) (fun y => -(f y - I)) r t hr.le
      _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact hmgfNeg r
      _ = Real.exp (-2 * t ^ 2 / S) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        field_simp [ne_of_gt hS]
        ring
  have hsplit (y : ∀ i, Ω i) :
      t ≤ |f y - I| → (t ≤ f y - I ∨ t ≤ -(f y - I)) := by
    intro h
    by_cases hy : 0 ≤ f y - I
    · left
      simpa [abs_of_nonneg hy] using h
    · right
      have habs : |f y - I| = -(f y - I) := abs_of_neg (lt_of_not_ge hy)
      rw [habs] at h
      exact h
  calc
    (FinProb.pi P).pr (fun y => t ≤ |f y - (FinProb.pi P).expect f|) ≤
        (FinProb.pi P).pr (fun y => t ≤ f y - I ∨ t ≤ -(f y - I)) :=
      FinProb.pr_mono _ _ _ (fun y => hsplit y)
    _ ≤ (FinProb.pi P).pr (fun y => t ≤ f y - I) +
          (FinProb.pi P).pr (fun y => t ≤ -(f y - I)) :=
      FinProb.pr_union_le _ _ _
    _ ≤ 2 * Real.exp (-2 * t ^ 2 / S) := by
      linarith [hupper, hlower]

end HypercubeRamsey
