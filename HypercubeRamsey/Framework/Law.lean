import HypercubeRamsey.Framework.Basic
import HypercubeRamsey.Framework.FinProb

/-!
# Laws, widths and densities

A law on a host side is a finite probability on `Fin N`. Widths are measured against the original side size `N`.
-/

namespace HypercubeRamsey

/-- A probability law on a host side. -/
abbrev Law (N : ℕ) := FinProb (Fin N)

variable {N : ℕ}

/-- The law vanishes off `A`. -/
def Law.SupportedIn (μ : Law N) (A : Finset (Fin N)) : Prop := ∀ x, x ∉ A → μ.w x = 0

/-- Width at most `t`: no atom exceeds `exp t / N` (the paper's `log (N max μ) ≤ t`). -/
def Law.WidthLE (μ : Law N) (t : ℝ) : Prop := ∀ x, μ.w x ≤ Real.exp t / N

open Classical in
/-- `d_G(μ, ν)`: the colour-`c` density seen by independent draws from `μ` and `ν`. -/
noncomputable def dens (E : Fin N → Fin N → Prop) (c : Colour) (μ ν : Law N) : ℝ :=
  ∑ x, ∑ y, μ.w x * ν.w y * (if Hits E c x y then 1 else 0)

open Classical in
/-- `codeg E c μ y y'`: mass of first-side labels joined to both `y` and `y'` in colour `c`. -/
noncomputable def codeg (E : Fin N → Fin N → Prop) (c : Colour) (μ : Law N) (y y' : Fin N) : ℝ :=
  ∑ x, μ.w x * (if Hits E c x y ∧ Hits E c x y' then 1 else 0)

/-- Point mass; degrees are `dens E c μ (Law.dirac y)`. -/
noncomputable def Law.dirac (y : Fin N) : Law N where
  w x := if x = y then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- `μ` conditioned on `A` (positive mass). -/
noncomputable def Law.restrict (μ : Law N) (A : Finset (Fin N)) (h : 0 < ∑ x ∈ A, μ.w x) : Law N where
  w x := if x ∈ A then μ.w x / ∑ y ∈ A, μ.w y else 0
  nonneg x := by split_ifs <;> [exact div_nonneg (μ.nonneg x) h.le; exact le_rfl]
  sum_eq_one := by
    classical
    rw [Finset.sum_ite_mem_eq, ← Finset.sum_div]
    exact div_self (ne_of_gt h)

/-- Mixture of laws. -/
noncomputable def Law.mix {ι : Type*} [Fintype ι] (ρ : FinProb ι) (μ : ι → Law N) : Law N where
  w x := ∑ i, ρ.w i * (μ i).w x
  nonneg x := Finset.sum_nonneg fun i _ => mul_nonneg (ρ.nonneg i) ((μ i).nonneg x)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [(μ _).sum_eq_one]
    simpa using ρ.sum_eq_one

theorem dens_transpose (E : Fin N → Fin N → Prop) (c : Colour) (μ ν : Law N) :
    dens (transposeRel E) c μ ν = dens E c ν μ := by
  classical
  simp only [dens]
  rw [Finset.sum_comm]
  simp_rw [hits_transpose]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem dens_add_dens_not (E : Fin N → Fin N → Prop) (μ ν : Law N) :
    dens E true μ ν + dens E false μ ν = 1 := by
  classical
  simp only [dens]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have hpair : ∀ x y, μ.w x * ν.w y * (if Hits E true x y then 1 else 0) +
      μ.w x * ν.w y * (if Hits E false x y then 1 else 0) = μ.w x * ν.w y := by
    intro x y
    by_cases hxy : E x y <;> simp [Hits, hxy]
  simp_rw [hpair]
  simp_rw [← Finset.mul_sum]
  simp [μ.sum_eq_one, ν.sum_eq_one]

end HypercubeRamsey
