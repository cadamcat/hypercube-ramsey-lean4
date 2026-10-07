import HypercubeRamsey.PartC.All

/-!
Contracts requested from the Section 12 producer. Those modules are not on this branch yet; these declarations
give the proof lanes for Section 15 a stable finite-law interface to request during integration.
-/

namespace HypercubeRamsey.S15.Needs

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

variable {N : ℕ}

/-- D12.0: the centered normalized-hit coefficient, used only on positive degree gates. -/
noncomputable def acoef (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (x y : Fin N) : ℝ :=
  let d := deg E c π x
  if 0 < d then hit E c x y / d - 1 else -1

/-- D12.0: a joint interaction of a law with centered coefficients. -/
noncomputable def inter (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    {u : ℕ} (J : Finset (Fin u)) (xs : Fin u → Fin N) : ℝ :=
  ∑ y, π y * ∏ i ∈ J, acoef E c π (xs i) y

/-- D12.0: product weight of a tuple under a finite product law. -/
noncomputable def prodW {u : ℕ} (τ : Fin N → ℝ) (xs : Fin u → Fin N) : ℝ :=
  ∏ i, τ (xs i)

/-- D12.0: the positive product term in the centered-moment expansion. -/
noncomputable def posTerm (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (I : Finset (Fin u))
    (xs : Fin u → Fin N) : ℝ :=
  ∏ l, ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)

/-- D12.0: the signed integrand in equation (15.10). -/
noncomputable def Phi (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * posTerm E c π I xs

/-- D12.0: all interactions on a tuple are at most `t`. -/
def Moderate (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (t : ℝ) (xs : Fin u → Fin N) : Prop :=
  ∀ l (J : Finset (Fin u)), 2 ≤ J.card → |inter E c (π l) J xs| ≤ t

/-- D12.0: common-neighbour mass after heterogeneous odd labels. -/
noncomputable def Zmass (E : Fin N → Fin N → Prop) (c : Colour)
    {d : ℕ} (τ : Fin N → ℝ) (π : Fin d → Fin N → ℝ) (ys : Fin d → Fin N) : ℝ :=
  ∑ x, τ x * ∏ l, (1 + acoef E c (π l) x (ys l))

/-- D12.0: degree gate used by the interaction estimates. -/
def DegGate (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (C0 b : ℝ) (x : Fin N) : Prop := |deg E c π x - 1 / 2| ≤ C0 * b

/-- D12.0: heterogeneous laws and a small-width first law for Section 12. -/
structure InterSetting (T : Stage) (k : ℕ) (xs4 : ℝ) where
  d : ℕ
  d_le : d ≤ T.S.n k
  τ : Law (T.S.N k)
  π : Fin d → Law (T.S.N k)
  τ_supported : τ.SupportedIn (T.X k)
  π_supported : ∀ l, (π l).SupportedIn (T.Y k)
  τ_width : τ.WidthLE ((T.S.n k : ℝ) ^ xs4)
  π_width : ∀ l, (π l).WidthLE ((T.S.n k : ℝ) ^ xs4)

/-- D12.0: degree gates hold on the support of `τ`. -/
def InterSetting.DegOK {T : Stage} {k : ℕ} {xs4 : ℝ}
    (S : InterSetting T k xs4) (c : Colour) (C0 : ℝ) : Prop :=
  ∀ l x, 0 < S.τ.w x → DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) x

/-- SHARED: L12.0(a), deep discrepancy bounds the first-side degree-outlier mass. -/
theorem exceptional_first {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (ν τ : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w1)
    (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|, τ.w x ≤
      2 * Real.exp (w - W2) := by
  sorry

/-- SHARED: L12.0(b), the symmetric second-side degree-outlier bound. -/
theorem exceptional_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (τ ν : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w1)
    (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w) :
    ∑ y ∈ Finset.univ.filter fun y => err < |colDeg (T.S.E k) c τ y - 1 / 2|, ν.w y ≤
      2 * Real.exp (w - W2) := by
  sorry

/-- SHARED: L12.0(c), deep discrepancy bounds bounded signed degree tests. -/
theorem exceptional_signed {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (π : Law (T.S.N k)) (hπ : π.SupportedIn (T.Y k)) (hπw : π.WidthLE (w1 - Real.log 3))
    (h : Fin (T.S.N k) → ℝ) (hh : ∀ y, |h y| ≤ 1)
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter
      (fun x => 6 * err < |∑ y, π.w y * h y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
      τ.w x ≤ 4 * Real.exp (w - W2) := by
  sorry

/-- SHARED: L12.2, exact heterogeneous centered-moment expansion. -/
theorem centered_moment_identity {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ) :
    ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
        ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
  sorry

/-- SHARED: L12.3a, one-free-coordinate gated interaction tail. -/
theorem inter_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (J : Finset (Fin u)) (i0 : Fin u), i0 ∈ J → 2 ≤ J.card →
      ∀ xs : Fin u → Fin (T.S.N k),
        (∀ i ∈ J, i ≠ i0 →
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
        ∑ z ∈ Finset.univ.filter (fun z =>
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
            100 * 3 ^ u * C0 * bstar T k <
              |inter (T.S.E k) c (S.π l).w J (Function.update xs i0 z)|), S.τ.w z ≤
          Real.exp (-(κ.α * T.S.n k / 3)) := by
  sorry

/-- SHARED: L12.4, the moderate interaction moment bound. -/
theorem moderate_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
      |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
        (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) := by
  sorry

/-- SHARED: L12.5(iv), homogeneous extension peeling and the lower-tail estimate. -/
theorem homogeneous_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ Cu Qmin : ℝ, 0 < Cu ∧ 0 < Qmin ∧
    ∀ᶠ k in atTop, ∀ d ≤ T.S.n k, ∀ (τ π : Law (T.S.N k)) (Sp : Finset (Fin (T.S.N k)))
      (Q Γ t : ℝ),
      τ.SupportedIn (T.X k) → π.SupportedIn (T.Y k) →
      τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) →
      π.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) →
      (∀ x, x ∉ Sp → τ.w x = 0) → Qmin ≤ Q →
      NoClique (T.S.E k) c Sp π.w κ.θ Q → 0 ≤ Γ → Γ < 1 →
      (∀ x ∈ Sp, τ.w x * (deg (T.S.E k) c π.w x) ^ (-(d : ℝ)) *
        Real.exp (Cstar κ.u κ.ξ * Q) ≤ Γ) → 0 ≤ t → t < 1 →
      (∀ x ∈ Sp, DegGate (T.S.E k) c π.w C0 (bstar T k) x) →
      (∑ ys : Fin d → Fin (T.S.N k),
        if Zmass (T.S.E k) c τ.w (fun _ => π.w) ys < t then ∏ l, π.w (ys l) else 0) ≤
        (1 - t) ^ (-(κ.u : ℝ)) *
          ((T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) + Cu * Γ) := by
  sorry

end HypercubeRamsey.S15.Needs
