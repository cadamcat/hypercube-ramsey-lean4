import HypercubeRamsey.S04.Defs
import HypercubeRamsey.S03.Height.Selection

/-!
# D4.1: parameters of the single-index Section 4 construction

Source: `sections/04-…tex`, lines 31–36, 89–98, 170–179, 228, 400–402, 469; blueprint
`research/blueprint/PART-A.md` D4.1.  With `ω = omega4 β γ` and `h = h4 β γ`:

* tuple length `k = ⌈n^{ω/3}⌉`, the cap `L = n^h`, the surplus `a_* = n^{-h}`;
* the height device (D3.8) on the even sites of `Q_n` (`d = n`), with `D = 2`, `b = ω/30`, `b₀ = b/4`,
  `ρ = b₀/10`, `r = ⌊n^{1-ρ}⌋` (sublinear regime), `λ = n^{10}`, `ζ = b₀/20`, `σ = ζ/10`, `θ = 1 - ζ`,
  `a = 10ζ`, and the top level `H = topScale n σ ζ` of L3.8;
* the selected-set bound `T = ⌈3 n^b⌉`, the constants `c₁ = 3/5`, `c₂ = c₁/2`, and the predictive threshold
  `ε₄ = exp(-c₂ a_* k n / 4)`.
-/

namespace HypercubeRamsey.S04

/-- D4.1: tuple length `k = ⌈n^{ω/3}⌉` (04:33). -/
noncomputable def tupLen (β γ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (omega4 β γ / 3)⌉₊

/-- D4.1: the cap `L = n^h` (04:33); `e^{-L}` is the least acceptable retained fraction. -/
noncomputable def capL (β γ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ h4 β γ

/-- D4.1: the density surplus `a_* = n^{-h}` (04:33). -/
noncomputable def aStar (β γ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-h4 β γ)

/-- D4.1: the crowd exponent `b = ω/30` (04:172). -/
noncomputable def bH (β γ : ℝ) : ℝ := omega4 β γ / 30

/-- D4.1: `b₀ = b/4` (04:172). -/
noncomputable def b0H (β γ : ℝ) : ℝ := bH β γ / 4

/-- D4.1: `ρ = b₀/10` (04:172). -/
noncomputable def rhoH (β γ : ℝ) : ℝ := b0H β γ / 10

/-- D4.1: `ζ = b₀/20` (04:174). -/
noncomputable def zetaH (β γ : ℝ) : ℝ := b0H β γ / 20

/-- D4.1: `σ = ζ/10` (04:174). -/
noncomputable def sigmaH (β γ : ℝ) : ℝ := zetaH β γ / 10

/-- D4.1: the choice `θ = 1 - ζ` for L3.8 (04:176; blueprint D4.1). -/
noncomputable def thetaH (β γ : ℝ) : ℝ := 1 - zetaH β γ

/-- D4.1: the choice `a = 10ζ` for L3.8 (04:176; blueprint D4.1). -/
noncomputable def aH (β γ : ℝ) : ℝ := 10 * zetaH β γ

/-- D4.1: the ball radius `r = ⌊n^{1-ρ}⌋` (04:173). -/
noncomputable def radius (β γ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 - rhoH β γ)⌋₊

/-- D4.1: the top level `H` of L3.8 (04:176–177). -/
noncomputable def topH (β γ : ℝ) (n : ℕ) : ℕ := topScale n (sigmaH β γ) (zetaH β γ)

/-- D4.1: `λ = n^{10}` (04:173). -/
noncomputable def lamH (n : ℕ) : ℝ := (n : ℝ) ^ (10 : ℝ)

/-- D4.1: the selected-set bound `T = ⌈3 n^b⌉` (04:178–179). -/
noncomputable def setBd (β γ : ℝ) (n : ℕ) : ℕ := ⌈3 * (n : ℝ) ^ bH β γ⌉₊

/-- D4.1: the single-entry constant `c₁` (04:228). -/
noncomputable def c1 : ℝ := 3 / 5

/-- D4.1: `c₂ = c₁/2 < c₁` (04:400–402). -/
noncomputable def c2 : ℝ := c1 / 2

/-- D4.1: the predictive threshold `ε₄ = exp(-c₂ a_* k n/4)` (04:409–411, 531). -/
noncomputable def eps4 (β γ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(c2 * aStar β γ n * (tupLen β γ n : ℝ) * (n : ℝ) / 4))

/-- D4.1: the D3.8 instance on the `n`-cube (`d = n`, `D = 2`). -/
@[reducible] noncomputable def hd (β γ : ℝ) (n : ℕ) : HDParams where
  n := n
  d := n
  D := 2
  r := radius β γ n
  H := topH β γ n
  lam := lamH n
  b₀ := b0H β γ
  b := bH β γ

/-- The exponent margin `ω > 0`. -/
theorem omega4_pos {β γ : ℝ} (hβ : 0 < β) (hγ : γ < 1) : 0 < omega4 β γ := by
  unfold omega4
  exact div_pos (lt_min hβ (by linarith)) (by norm_num)

/-- `ω < 1/1000`. -/
theorem omega4_lt {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) : omega4 β γ < 1 / 1000 := by
  unfold omega4
  have h1 : min β (1 - γ) ≤ 1 - γ := min_le_right _ _
  linarith

/-- D4.1: the exponents satisfy the admissibility hypotheses of L3.8 (`J₀ = 10`, `c_d = C_d = 1`, `D = 2`). -/
theorem hd_admissible {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    HDAdmissible 10 (b0H β γ) (bH β γ) (sigmaH β γ) (zetaH β γ) (thetaH β γ) (aH β γ) 1 1 2 := by
  have hω := omega4_pos hβ hγ
  have hω' := omega4_lt hβ hβγ
  simp only [b0H, bH, sigmaH, zetaH, thetaH, aH]
  refine ⟨by norm_num, ⟨?_, ?_, ?_⟩, by norm_num, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨by norm_num, le_rfl⟩⟩ <;>
    linarith

/-- D4.1: the sublinear-radius regime bounds `0 < ρ < 1`, `b₀ + (D+1)ρ < b`. -/
theorem hd_regime_bounds {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    0 < rhoH β γ ∧ rhoH β γ < 1 ∧ b0H β γ + (((2 : ℕ) : ℝ) + 1) * rhoH β γ < bH β γ := by
  have hω := omega4_pos hβ hγ
  have hω' := omega4_lt hβ hβγ
  simp only [rhoH, b0H, bH]
  push_cast
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- D4.1: the D3.8 regime of the construction (sublinear radius `r = ⌊n^{1-ρ}⌋`). -/
noncomputable def hdRegime {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    HDRegime (b0H β γ) (bH β γ) 2 :=
  .sub (rhoH β γ) (hd_regime_bounds hβ hβγ hγ)

/-- The regime fits every instance `hd β γ n`. -/
theorem hdRegime_ok {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (n : ℕ) :
    (hdRegime hβ hβγ hγ).ok (hd β γ n).n (hd β γ n).d (hd β γ n).r := rfl

end HypercubeRamsey.S04
