import Mathlib

open MeasureTheory ProbabilityTheory unitInterval

namespace HypercubeRamsey

theorem bernoulliHoeffdingMGF (p θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.exp (-θ * p) * ((1 - p) + p * Real.exp θ) ≤ Real.exp (θ ^ 2 / 8) := by
  classical
  let pI : I := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false pI
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hXmeas : AEMeasurable X μ := by fun_prop
  have hXrange : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with b
    cases b <;> simp [X]
  have hmean : μ[X] = p := by
    simp [μ, pI, X, ProbabilityTheory.integral_bernoulliMeasure]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (X := X) (μ := μ) (a := (0 : ℝ)) (b := 1) hXmeas hXrange
  have hmgf := hsub.mgf_le θ
  rw [hmean] at hmgf
  have heq : ProbabilityTheory.mgf (fun b => X b - p) μ θ =
      Real.exp (-θ * p) * ((1 - p) + p * Real.exp θ) := by
    rw [ProbabilityTheory.mgf]
    change ∫ b, Real.exp (θ * (X b - p)) ∂ProbabilityTheory.bernoulliMeasure true false pI = _
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp [X, pI]
    rw [show θ * (1 - p) = (-θ * p) + θ by ring, Real.exp_add]
    ring
  rw [heq] at hmgf
  norm_num at hmgf
  have hcoeff : (1 : ℝ) / 4 * θ ^ 2 / 2 = θ ^ 2 / 8 := by ring
  rw [hcoeff] at hmgf
  have hneg : -(θ * p) = -θ * p := by ring
  rw [hneg] at hmgf
  exact hmgf

end HypercubeRamsey
