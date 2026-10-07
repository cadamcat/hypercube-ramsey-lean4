import HypercubeRamsey.Framework.Basic

/-!
# Laws, widths and densities
-/

namespace HypercubeRamsey

/-- A probability law on a host side. -/
structure Law (N : ℕ) where
  w : Fin N → ℝ
  nonneg : ∀ x, 0 ≤ w x
  sum_eq_one : ∑ x, w x = 1

variable {N : ℕ}

/-- The law vanishes off `A`. -/
def Law.SupportedIn (μ : Law N) (A : Finset (Fin N)) : Prop := ∀ x, x ∉ A → μ.w x = 0

/-- Width at most `t`: no atom exceeds `exp t / N` (the paper's `log (N max μ) ≤ t`). -/
def Law.WidthLE (μ : Law N) (t : ℝ) : Prop := ∀ x, μ.w x ≤ Real.exp t / N

open Classical in
/-- `d_G(μ, ν)`: the colour-`c` density seen by independent draws from `μ` and `ν`. -/
noncomputable def dens (E : Fin N → Fin N → Prop) (c : Colour) (μ ν : Law N) : ℝ :=
  ∑ x, ∑ y, μ.w x * ν.w y * (if Hits E c x y then 1 else 0)

end HypercubeRamsey
