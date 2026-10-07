import HypercubeRamsey.S03.Height.Device

/-!
# L3.8a–e: scales, failures, and abstract overlap removal

The scale-induction interface is deliberately independent of cube geometry and of the number of crowd tests.
Its caller supplies the base-scale bounds, the private-child factorization, and the overlap-exception estimates.
This is the form needed when a consumer changes the regions or adds path constraints.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- The hypotheses on the exponents and on the linear dimension regime in L3.8. -/
structure HDAdmissible (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ) where
  hJ : 2 < J₀
  hb : 0 < b₀ ∧ b₀ < b ∧ b < 1
  hD : 1 ≤ D
  hsz : 0 < σ ∧ σ < ζ ∧ ζ < 1 ∧ 0 < θ ∧ θ < 1
  ha : ζ + σ + (1 - θ) < a ∧ a < b₀ ∧ a + 4 * σ < b
  hd : 0 < c_d ∧ c_d ≤ C_d

/-- The linear-radius and sublinear-radius regimes for D3.8. -/
inductive HDRegime (b₀ b : ℝ) (D : ℕ) : Type
  | lin (c_r : ℝ) (bounds : 0 < c_r ∧ c_r ≤ 1 / 4)
  | sub (ρ : ℝ) (bounds : 0 < ρ ∧ ρ < 1 ∧ b₀ + ((D : ℝ) + 1) * ρ < b)

/-- Whether a concrete dimension and radius fit a regime. -/
def HDRegime.ok {b₀ b : ℝ} {D : ℕ} : HDRegime b₀ b D → ℕ → ℕ → ℕ → Prop
  | .lin c_r _, _, d, r => c_r * d ≤ r ∧ 4 * r ≤ d
  | .sub ρ _, n, _, r => r = ⌊(n : ℝ) ^ (1 - ρ)⌋₊

private theorem scaleIndex_exists (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hx : 1 ≤ x := by omega
      have hstep : x + 1 ≤ 2 * x := by omega
      have hmult : 2 * x ≤ M * x := Nat.mul_le_mul_right x hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := hstep
        _ ≤ M * x := hmult
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring

/--
The first scale at least `n^(1-ζ)`, with `R₀ = ceil(log² n)` and `M = ceil(n^σ)`.
The `max` clauses make this a total definition; under the hypotheses of L3.8 and `n ≥ 2`, they agree with
the paper's scales (`R₀ ≥ 1` and `M ≥ 2`).
-/
noncomputable def topScale (n : ℕ) (σ ζ : ℝ) : ℕ := by
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  exact M ^ Nat.find (scaleIndex_exists M R₀ target (by dsimp [M]; omega) (by dsimp [R₀]; omega)) * R₀

/-- L3.8a's metric on site-level IDs. -/
def heightMetric {p : HDParams} (x y : p.Loc) : ℕ :=
  max (Nat.dist x.2.1 y.2.1) ((hammingDist x.1 y.1 + p.D - 1) / p.D)

/-- A finite abstract scale system: a family of parent events and private child failure suprema. -/
structure ScaleInductionInput (Config Rule Position Activation : Type*)
    [Fintype Config] [Fintype Position] [Fintype Activation] where
  positions : FinProb Position
  activations : FinProb Activation
  configurations : Finset Config
  children : ℕ
  parentFailure : Config → Rule → Position → Activation → Prop
  positionOverlapException : Config → Rule → Position → Prop
  activationOverlapException : Config → Rule → Position → Activation → Prop
  privateChildSup : Config → Rule → Fin children → Position → ℝ
  epsBase : ℝ
  epsPosition : ℝ
  epsActivation : ℝ
  scaleTarget : ℝ
  base_nonneg : 0 ≤ epsBase
  position_nonneg : 0 ≤ epsPosition
  activation_nonneg : 0 ≤ epsActivation
  scale_target_nonneg : 0 ≤ scaleTarget
  private_child_nonneg : ∀ c rule i P, 0 ≤ privateChildSup c rule i P
  base_estimate : ∀ c rule i, positions.expect (privateChildSup c rule i) ≤ epsBase
  private_factorization : ∀ c rule,
    positions.expect (fun P => ∏ i, privateChildSup c rule i P) ≤
      ∏ i, positions.expect (privateChildSup c rule i)
  position_overlap_estimate : ∀ c rule,
    positions.pr (positionOverlapException c rule) ≤ epsPosition
  activation_overlap_estimate : ∀ c rule,
    (positions.prod activations).pr (fun ω => activationOverlapException c rule ω.1 ω.2) ≤ epsActivation
  factorization : ∀ c rule,
    (positions.prod activations).pr (fun ω => parentFailure c rule ω.1 ω.2) ≤
      positions.pr (positionOverlapException c rule) +
        (positions.prod activations).pr (fun ω => activationOverlapException c rule ω.1 ω.2) +
        positions.expect (fun P => ∏ i, privateChildSup c rule i P)
  exponent_comparison : (configurations.card : ℝ) *
      (epsPosition + epsActivation + epsBase ^ children) ≤ scaleTarget

/-- The expected product of private child bounds is at most the product of the base-scale bounds. -/
theorem private_child_product_estimate {Config Position Activation : Type*}
    [Fintype Config] [Fintype Position] [Fintype Activation] {Rule : Type*}
    (I : ScaleInductionInput Config Rule Position Activation) (c : Config) (rule : Rule) :
    I.positions.expect (fun P => ∏ i, I.privateChildSup c rule i P) ≤ I.epsBase ^ I.children := by
  sorry

/--
L3.8e (abstract scale-induction step). `base_estimate` is the child-scale input; the two overlap estimates
are supplied separately for prospective positions and activations; `private_factorization` records the
independence after deleting overlaps. `factorization` is uniform in the fixed eligibility rule, so consumers
may use several crowd tests or restrict paths through slices without changing this induction interface.
`exponent_comparison` packages the count and exponent comparisons that turn the accumulated error into the
next-scale target bound.
-/
theorem scale_induction_step {Config Position Activation Rule : Type*}
    [Fintype Config] [Fintype Position] [Fintype Activation]
    (I : ScaleInductionInput Config Rule Position Activation) (rule : Rule) :
    (I.positions.prod I.activations).pr
      (fun ω => ∃ c ∈ I.configurations, I.parentFailure c rule ω.1 ω.2) ≤ I.scaleTarget := by
  sorry

end HypercubeRamsey
