import HypercubeRamsey.PartC.Cleaning

/-!
# Section 12 interaction vocabulary

The normalization and finite sums used in the deep discrepancy and interaction
estimates. These definitions keep the tuple and column indices explicit.
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open scoped BigOperators

variable {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)

/-- D12.0: the centered normalized indicator `I_x(y) / D_π(x) - 1`. -/
noncomputable def acoef (π : Fin N → ℝ) (x y : Fin N) : ℝ :=
  hit E c x y / deg E c π x - 1

/-- D12.0: the centered interaction over a set of tuple coordinates. -/
noncomputable def inter (π : Fin N → ℝ) {u : ℕ}
    (J : Finset (Fin u)) (xs : Fin u → Fin N) : ℝ :=
  ∑ y, π y * ∏ i ∈ J, acoef E c π (xs i) y

/-- D12.0: the positive product term in the centered moment expansion. -/
noncomputable def posTerm {d u : ℕ} (π : Fin d → Fin N → ℝ)
    (I : Finset (Fin u)) (xs : Fin u → Fin N) : ℝ :=
  ∏ l, ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)

/-- D12.0: the signed integrand in the heterogeneous centered moment identity. -/
noncomputable def Phi {d u : ℕ} (π : Fin d → Fin N → ℝ)
    (xs : Fin u → Fin N) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * posTerm E c π I xs

/-- D12.0: a tuple is moderate when every interaction of order at least two is small. -/
def Moderate {d u : ℕ} (π : Fin d → Fin N → ℝ) (t : ℝ)
    (xs : Fin u → Fin N) : Prop :=
  ∀ l (J : Finset (Fin u)), 2 ≤ J.card → |inter E c (π l) J xs| ≤ t

/-- D12.0: common-neighbour mass under heterogeneous second-side laws. -/
noncomputable def Zmass {d : ℕ} (τ : Fin N → ℝ) (π : Fin d → Fin N → ℝ)
    (ys : Fin d → Fin N) : ℝ :=
  ∑ x, τ x * ∏ l, (1 + acoef E c (π l) x (ys l))

/-- D12.0: the degree gate at scale `b`. -/
def DegGate (π : Fin N → ℝ) (C0 b : ℝ) (x : Fin N) : Prop :=
  |deg E c π x - 1 / 2| ≤ C0 * b

/-- D12.0: product weight for iid samples from a finite law. -/
noncomputable def prodW {u : ℕ} (τ : Fin N → ℝ) (xs : Fin u → Fin N) : ℝ :=
  ∏ i, τ (xs i)

/-- D12.0: one heterogeneous interaction setting at a stage index. -/
structure InterSetting (T : Stage) (k : ℕ) (xs4 : ℝ) where
  d : ℕ
  d_le : d ≤ T.S.n k
  τ : Law (T.S.N k)
  π : Fin d → Law (T.S.N k)
  τ_supp : τ.SupportedIn (T.X k)
  π_supp : ∀ l, (π l).SupportedIn (T.Y k)
  τ_width : τ.WidthLE ((T.S.n k : ℝ) ^ xs4)
  π_width : ∀ l, (π l).WidthLE ((T.S.n k : ℝ) ^ xs4)

/-- D12.0: the degree condition on the support of the first law. -/
def InterSetting.DegOK {T : Stage} {k : ℕ} {xs4 : ℝ}
    (S : InterSetting T k xs4) (c : Colour) (C0 : ℝ) : Prop :=
  ∀ l x, 0 < S.τ.w x →
    DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) x

/-- L12.6: simultaneous row-tail estimate at the original first-side set. -/
def RowTail {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (X₀ : Finset (Fin N)) (n ξ : ℝ) (x : Fin N) : Prop :=
  (((X₀.filter fun z => n ^ (-1.03 : ℝ) < |corr E c π x z|).card : ℝ) ≤
      Real.exp (-n ^ (0.2 : ℝ)) * X₀.card) ∧
    (∑ z ∈ X₀.filter (fun z => n ^ (-1.03 : ℝ) < |corr E c π x z| ∧
        |corr E c π x z| ≤ 4 * ξ),
      Real.exp (150 * n * |corr E c π x z|) ≤
        Real.exp (-n ^ (0.2 : ℝ)) * X₀.card)

end HypercubeRamsey.S12
