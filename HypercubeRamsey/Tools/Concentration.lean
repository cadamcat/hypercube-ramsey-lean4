import HypercubeRamsey.Framework.FinProb

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
  sorry

/-- X-Chernoff: two-sided Hoeffding tails for independent finite bounded summands. -/
theorem xChernoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ) (a b : ι → ℝ)
    (hX : ∀ i ω, a i ≤ X i ω ∧ X i ω ≤ b i)
    (hwidth : 0 < ∑ i, (b i - a i) ^ 2) (t : ℝ) (ht : 0 < t) :
    (FinProb.pi P).pr (fun ω =>
      t ≤ |(∑ i, X i (ω i)) - ∑ i, (P i).expect (X i)|) ≤
        2 * Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  sorry

/-- X-Chernoff: multiplicative upper tail for independent `[0,1]` finite summands. -/
theorem xChernoff_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    let μ : ℝ := ∑ i, (P i).expect (X i)
    (FinProb.pi P).pr (fun ω => (1 + δ) * μ ≤ ∑ i, X i (ω i)) ≤
      Real.exp (-μ * δ ^ 2 / (2 + δ)) := by
  sorry

/-- X-Chernoff: multiplicative lower tail for independent `[0,1]` finite summands. -/
theorem xChernoff_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let μ : ℝ := ∑ i, (P i).expect (X i)
    (FinProb.pi P).pr (fun ω => ∑ i, X i (ω i) ≤ (1 - δ) * μ) ≤
      Real.exp (-μ * δ ^ 2 / 2) := by
  sorry

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
