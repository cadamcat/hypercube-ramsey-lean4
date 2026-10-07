import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.S03.Height.Scale

/-!
# Section 6 constants and scales

D6.0 (06:159–163, 06:531–534, 06:871–872).  The paper fixes `κ`, then very small successive constants
`d₂, δ₂, d₁, δ₁, d₀, D_*` (each small in terms of the previous ones and the absolute coarse dimension), and only
then, given `γ, p₀, K`, a small `α`.  The constants are fixed here as explicit numbers with ample slack:

* `κ(1 + log(4/c₁)) < .001` (06:159): `κ = 10⁻⁴`, `log 800 < 7`;
* `d₂ ≪ κ` (06:360: `d₂ (J+1) log n ≤ .14 k`), `C d₁ + δ₂ + d₀ < d₂` with `C = 602` the bound `|S| ≤ C u_β`
  (06:161–162), `602 d₀ + δ₁ ≤ d₁` (06:180, 06:182–187: the cap multiplies at most `|C(h)| ≤ 602` tag factors
  `n^{d₀}` and the predictive denominator `n^{δ₁}`), `2D_* < d₀` (06:159);
* `α = min(10⁻¹², p₀/2)`: `α < p₀` gives `mε → 0` (06:225), and `α` is far below every rate built from the
  constants above (`C α < c₃/4` with `c₃ ≥ δ₂/16`, 06:510–516).

`D_* = 10⁻¹⁶` is universal: it does not depend on `γ, p₀, K` (06:24–26, 06:163).
The height-device exponents are chosen after `α` (06:531–534): `λ = n^{10}`, `r = ⌊ρn⌋` with
`H_bin(2ρ) < log 2 − .55` (06:871–872; `ρ = 1/100`), crowd exponent `b = α/4000` so that `2n^b ≤ T = ⌈m^{.001}⌉`,
and `σ, ζ, 1 − θ` tiny multiples of `α`.
-/

namespace HypercubeRamsey
namespace S06

noncomputable section

/-- `c₀ = .01`, the relation threshold (06:43, 06:57). -/
def c₀ : ℝ := 1 / 100

/-- `c₁ = c₀/2`, the base-tag restriction threshold (06:95). -/
def c₁ : ℝ := c₀ / 2

/-- The tuple-length constant `κ` (06:159), renamed `κ₆` as in the blueprint. -/
def κ₆ : ℝ := 1 / 10 ^ 4

/-- Step 2 tag-comparison exponent `d₂` (06:215). -/
def d₂ : ℝ := 1 / 10 ^ 6

/-- Step 2 denominator exponent `δ₂` (06:201). -/
def δ₂ : ℝ := 1 / 10 ^ 8

/-- Step 1 posterior exponent `d₁` (06:170). -/
def d₁ : ℝ := 1 / 10 ^ 10

/-- Step 1 predictive-denominator exponent `δ₁` (06:178). -/
def δ₁ : ℝ := 1 / 10 ^ 14

/-- Base-tag domination exponent `d₀` (06:159–160, `T₀ ≤ n^{d₀} Λ`). -/
def d₀ : ℝ := 1 / 10 ^ 14

/-- The universal density exponent `D_*` of Lemma 6.1 (06:6, 06:159). -/
def Dstar₆ : ℝ := 1 / 10 ^ 16

/-- The final Step 3 history rate `c₂ = .001` (06:467, 06:507). -/
def c₂ : ℝ := 1 / 1000

/-- The linear height radius ratio `ρ` (06:532, 06:871–872). -/
def ρ₆ : ℝ := 1 / 100

/-- The fine-chunk exponent `α`, small in terms of all absolute constants and `p₀` (06:163). -/
def α₆ (p₀ : ℝ) : ℝ := min (1 / 10 ^ 12) (p₀ / 2)

/-- The defect `ε = n^{-p₀}` (06:11). -/
def ε₆ (p₀ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-p₀)

/-- The number of fine chunks `m = ⌈n^α⌉` (06:70). -/
def m₆ (p₀ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ α₆ p₀⌉₊

/-- The severity cutoff `J = ⌊m^{.04}⌋` (06:73). -/
def J₆ (m : ℕ) : ℕ := ⌊(m : ℝ) ^ (1 / 25 : ℝ)⌋₊

/-- The target fan `T = ⌈m^{.001}⌉` (06:163). -/
def T₆ (m : ℕ) : ℕ := ⌈(m : ℝ) ^ (1 / 1000 : ℝ)⌉₊

/-- The tuple length `k = ⌈κ J log n⌉` (06:125). -/
def k₆ (n m : ℕ) : ℕ := ⌈κ₆ * (J₆ m : ℝ) * Real.log n⌉₊

/-- The height-device centre density exponent: `λ = n^{10}` (06:532). -/
def J₀₆ : ℝ := 10

/-- Two even neighbours of one odd state are within encoded distance `D₀ = 10` (06:256). -/
def D₀₆ : ℕ := 10

/-- Height exponents, chosen after `α` (06:531–534).  `b` is the crowd exponent. -/
def b₆ (α : ℝ) : ℝ := α / 4000
def b₀₆ (α : ℝ) : ℝ := α / 8000
def a₆ (α : ℝ) : ℝ := α / 16000
def σ₆ (α : ℝ) : ℝ := α / 10 ^ 6
def ζ₆ (α : ℝ) : ℝ := 2 * α / 10 ^ 6
def θ₆ (α : ℝ) : ℝ := 1 - α / 10 ^ 6

/-- The encoded dimension `d` lies in `[n/2, 2n]` (06:235). -/
def cd₆ : ℝ := 1 / 2
def Cd₆ : ℝ := 2

/-- The admissible input exponents of Lemma 6.1. -/
def Admissible6 (γ p₀ K : ℝ) : Prop := 0 < γ ∧ γ < 1 ∧ 0 < p₀ ∧ 0 < K

/-- D6.0: the numerical relations among the absolute constants used by Steps 1–3 (06:159–163, 06:355–360).
(`κ(1 + log(4/c₁)) < .001` holds since `log 800 < 9`.) -/
theorem constants6_facts :
    0 < Dstar₆ ∧ 2 * Dstar₆ < d₀ ∧ 602 * d₀ + δ₁ ≤ d₁ ∧ 602 * d₁ + δ₂ + d₀ < d₂ ∧ 20 * d₂ < κ₆ ∧
      0 < δ₁ ∧ 0 < δ₂ ∧ c₁ = 1 / 200 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [Dstar₆, d₀, δ₁, d₁, δ₂, d₂, κ₆, c₁, c₀]

/-- D6.0: the height-device exponents satisfy the admissibility hypotheses of L3.8, and `α` is positive, below
`p₀` and below `10⁻¹²` (06:163, 06:531–534). -/
theorem height_exponents6_admissible (p₀ : ℝ) (hp : 0 < p₀) :
    0 < α₆ p₀ ∧ α₆ p₀ < p₀ ∧ α₆ p₀ ≤ 1 / 10 ^ 12 ∧ 0.9 < θ₆ (α₆ p₀) ∧
      α₆ p₀ < 2 * (1 - ζ₆ (α₆ p₀)) ∧
      Nonempty (HDAdmissible J₀₆ (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀))
        (θ₆ (α₆ p₀)) (a₆ (α₆ p₀)) cd₆ Cd₆ D₀₆) := by
  have hα0 : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hα1 : α₆ p₀ ≤ 1 / 10 ^ 12 := min_le_left _ _
  have hαp : α₆ p₀ < p₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨hα0, hαp, hα1, ?_, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · simp only [θ₆]; nlinarith
  · simp only [ζ₆]; nlinarith
  · norm_num [J₀₆]
  · simp only [b₀₆, b₆]; refine ⟨by positivity, by linarith, by nlinarith⟩
  · norm_num [D₀₆]
  · simp only [σ₆, ζ₆, θ₆]
    refine ⟨by positivity, by linarith, by nlinarith, by nlinarith, by nlinarith⟩
  · simp only [σ₆, ζ₆, θ₆, a₆, b₀₆, b₆]
    refine ⟨by linarith, by linarith, by linarith⟩
  · norm_num [cd₆, Cd₆]

end

end S06
end HypercubeRamsey
