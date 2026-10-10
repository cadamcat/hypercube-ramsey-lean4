import HypercubeRamsey.Framework.Props

/-!
# Vocabulary of Sections 12–18

For Sections 12–18, the cluster witness is named
`ClusterWitnessAt` here (the earlier `ClusterWitness` is a different, unused form).
-/

namespace HypercubeRamsey

open Filter

variable {N : ℕ}

open Classical in
/-- `I_x(y)`. -/
noncomputable def hit (E : Fin N → Fin N → Prop) (c : Colour) (x y : Fin N) : ℝ :=
  if Hits E c x y then 1 else 0

/-- `f_x(y) = 2 I_x(y) - 1`. -/
noncomputable def fv (E : Fin N → Fin N → Prop) (c : Colour) (x y : Fin N) : ℝ := 2 * hit E c x y - 1

/-- `D_π(x)`. -/
noncomputable def deg (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ) (x : Fin N) : ℝ :=
  ∑ y, π y * hit E c x y

/-- `K_π(x, z)`. -/
noncomputable def corr (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ) (x z : Fin N) : ℝ :=
  ∑ y, π y * fv E c x y * fv E c z y

/-- Uniform law on a nonempty set of labels. -/
noncomputable def Law.unif (A : Finset (Fin N)) (hA : A.Nonempty) : Law N := FinProb.uniform A hA

/-- `μ(· | S)`. -/
noncomputable def Law.cond (μ : Law N) (S : Finset (Fin N)) (h : 0 < ∑ x ∈ S, μ.w x) : Law N :=
  μ.restrict S h

/-- Discrepancy at index `k` for law pairs with one width at most `wS` and the other at most `wL`, in either
order, both colours. -/
def TwoBudgetDisc (T : Stage) (k : ℕ) (wS wL err : ℝ) : Prop :=
  ∀ (c : Colour) (μ ν : Law (T.S.N k)), μ.SupportedIn (T.X k) → ν.SupportedIn (T.Y k) →
    ((μ.WidthLE wL ∧ ν.WidthLE wS) ∨ (μ.WidthLE wS ∧ ν.WidthLE wL)) →
    |dens (T.S.E k) c μ ν - 1 / 2| ≤ err

/-- Orientation: `false ↦ T`, `true ↦ T.swap`. -/
def Stage.orient (T : Stage) : Bool → Stage
  | false => T
  | true => T.swap

/-- `b* = n^{-1+.04}`. -/
noncomputable def bstar (T : Stage) (k : ℕ) : ℝ := (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ))

/-- eq:source-2 in part C's form. -/
def InitDisc (T : Stage) (η0 : ℝ) : Prop :=
  ∀ᶠ k in atTop, TwoBudgetDisc T k ((T.S.n k : ℝ) ^ η0) ((T.S.n k : ℝ) ^ η0) ((T.S.n k : ℝ) ^ (-η0))

/-- eq:source-9 in part C's form. -/
def DeepDisc (T : Stage) (x α ε : ℝ) : Prop :=
  ∀ᶠ k in atTop, TwoBudgetDisc T k ((T.S.n k : ℝ) ^ x) (α * T.S.n k) ((T.S.n k : ℝ) ^ (-1 + ε))

/-- Proposition 10.1's witness on the retained sides at index `k`, first side `T.X k`, colour `c`. -/
def ClusterWitnessAt (T : Stage) (k : ℕ) (c : Colour) (ζ δ : ℝ) : Prop :=
  ∃ (m : ℕ) (μ : Law (T.S.N k)) (lam : Fin m → ℝ) (D : Fin m → Law (T.S.N k)),
    μ.SupportedIn (T.X k) ∧ (∀ j, (D j).SupportedIn (T.Y k)) ∧
    (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
    μ.WidthLE ((T.S.n k : ℝ) ^ δ) ∧
    (∀ y, ∑ j, lam j * (D j).w y ≤ Real.exp ((T.S.n k : ℝ) ^ δ) / T.S.N k) ∧
    (∀ j y, (D j).w y ≤ Real.exp (-((T.S.n k : ℝ) ^ ζ))) ∧
    (∀ j y y', 0 < (D j).w y → 0 < (D j).w y' →
      1 / 4 + (T.S.n k : ℝ) ^ (-δ) ≤ ∑ x, μ.w x * hit (T.S.E k) c x y * hit (T.S.E k) c x y')

end HypercubeRamsey
