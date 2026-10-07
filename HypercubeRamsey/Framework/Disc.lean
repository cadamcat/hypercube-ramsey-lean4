import HypercubeRamsey.Framework.Patch

/-!
# Discrepancy predicates and the interface between the parts of the proof
-/

namespace HypercubeRamsey

open Filter

/-- Discrepancy on stage `T`: first law on `X` of width `≤ s₁ n`, second on `Y` of width `≤ s₂ n`,
error `≤ e n`, eventually, every colour. -/
def DiscAt (T : Stage) (s₁ s₂ e : ℝ → ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ (c : Colour) (μ ν : Law (T.S.N k)),
    μ.SupportedIn (T.X k) → ν.SupportedIn (T.Y k) →
    μ.WidthLE (s₁ (T.S.n k)) → ν.WidthLE (s₂ (T.S.n k)) →
    |dens (T.S.E k) c μ ν - 1 / 2| ≤ e (T.S.n k)

/-- eq:source-2 (Corollary 7.2). -/
def InitialDisc (T : Stage) (η : ℝ) : Prop :=
  DiscAt T (fun n => n ^ η) (fun n => n ^ η) (fun n => n ^ (-η))

/-- Corollary 8.2's conclusion, with `τ = min (η₀/2) 0.04 / 4`. -/
def AsymDisc (T : Stage) (η₀ : ℝ) : Prop :=
  ∀ β γ : ℝ, 0 < β → β < min (η₀ / 2) 0.04 / 4 / 4 → 0 < γ → γ < 1 →
    ∃ h > (0 : ℝ), DiscAt T (fun n => n ^ β) (fun n => n ^ γ) (fun n => n ^ (-h)) ∧
      DiscAt T.swap (fun n => n ^ β) (fun n => n ^ γ) (fun n => n ^ (-h))

/-- Corollary 11.4's conclusion: deep discrepancy for every error slack, both orientations. -/
def DeepRegime (T : Stage) : Prop :=
  ∀ ε > (0 : ℝ), ∃ x > (0 : ℝ), ∃ α > (0 : ℝ),
    DiscAt T (fun n => n ^ x) (fun n => α * n) (fun n => n ^ (-1 + ε)) ∧
    DiscAt T.swap (fun n => n ^ x) (fun n => α * n) (fun n => n ^ (-1 + ε))

/-- Full-dimensional cluster witness of Proposition 10.1 (first side `X`, cluster laws on `Y`). -/
def ClusterWitness (ζ δ : ℝ) (c : Colour) : PatchProp := fun n N E =>
  {AB | ∃ (μ : Law N) (m : ℕ) (lam : Fin m → ℝ) (D : Fin m → Law N) (ν : Law N),
    (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j = 1) ∧ (∀ y, ν.w y = ∑ j, lam j * (D j).w y) ∧
    μ.SupportedIn AB.1 ∧ (∀ j, (D j).SupportedIn AB.2) ∧
    μ.WidthLE ((n : ℝ) ^ δ) ∧ ν.WidthLE ((n : ℝ) ^ δ) ∧
    (∀ j y, (D j).w y ≤ Real.exp (-(n : ℝ) ^ ζ)) ∧
    (∀ j y y', (D j).w y ≠ 0 → (D j).w y' ≠ 0 → 1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E c μ y y')}

/-- Corollary 10.2's conclusion. -/
def ClusterAbsent (T : Stage) (η₀ : ℝ) : Prop :=
  ∀ ζ δ : ℝ, 0 < ζ → 0 < δ → δ < min η₀ (min ζ 1) / 2000 → ∀ c : Colour,
    EventuallyAbsent T (ClusterWitness ζ δ c) ∧ EventuallyAbsent T.swap (ClusterWitness ζ δ c)

theorem DiscAt.refine {T T' : Stage} {s₁ s₂ e : ℝ → ℝ} (h : DiscAt T s₁ s₂ e)
    (hr : T'.Refines T) : DiscAt T' s₁ s₂ e := by
  induction hr with
  | refl T => simpa using h
  | sub T φ hφ =>
      simpa [DiscAt, Stage.sub, BadSeq.comp] using hφ.tendsto_atTop.eventually h
  | @remove T X' Y' hX hY hsmall =>
      filter_upwards [h] with k hk c μ ν hμ hν hw₁ hw₂
      apply hk c μ ν
      · intro x hx
        apply hμ x
        intro hx'
        exact hx (hX k hx')
      · intro y hy
        apply hν y
        intro hy'
        exact hy (hY k hy')
      · exact hw₁
      · exact hw₂
  | trans hAB hBC ihAB ihBC => exact ihAB (ihBC h)

theorem DiscAt.swap_iff (T : Stage) (s₁ s₂ e : ℝ → ℝ) :
    DiscAt T.swap s₁ s₂ e ↔ DiscAt T s₂ s₁ e := by
  constructor
  · intro h
    filter_upwards [h] with k hk c μ ν hμ hν hw₁ hw₂
    have hbound := hk c ν μ hν hμ hw₂ hw₁
    change |dens (transposeRel (T.S.E k)) c ν μ - 1 / 2| ≤ e (T.S.n k) at hbound
    rw [dens_transpose (T.S.E k) c ν μ] at hbound
    exact hbound
  · intro h
    filter_upwards [h] with k hk c μ ν hμ hν hw₁ hw₂
    have hbound := hk c ν μ hν hμ hw₂ hw₁
    change |dens (T.S.E k) c ν μ - 1 / 2| ≤ e (T.S.n k) at hbound
    rw [← dens_transpose (T.S.E k) c μ ν] at hbound
    exact hbound

/-- Smaller width budgets and a larger error, eventually in the dimension. -/
theorem DiscAt.mono {T : Stage} {s₁ s₂ e s₁' s₂' e' : ℝ → ℝ} (h : DiscAt T s₁ s₂ e)
    (h₁ : ∀ᶠ x in atTop, s₁' x ≤ s₁ x) (h₂ : ∀ᶠ x in atTop, s₂' x ≤ s₂ x)
    (h₃ : ∀ᶠ x in atTop, e x ≤ e' x) : DiscAt T s₁' s₂' e' := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  filter_upwards [h, hn.eventually h₁, hn.eventually h₂, hn.eventually h₃]
    with k hk hs₁ hs₂ he c μ ν hμ hν hw₁ hw₂
  have hw₁' : μ.WidthLE (s₁ (T.S.n k)) := by
    intro x
    exact le_trans (hw₁ x) (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hs₁)) (by positivity))
  have hw₂' : ν.WidthLE (s₂ (T.S.n k)) := by
    intro x
    exact le_trans (hw₂ x) (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hs₂)) (by positivity))
  exact le_trans (hk c μ ν hμ hν hw₁' hw₂') he

theorem DeepRegime.refine {T T' : Stage} (h : DeepRegime T) (hr : T'.Refines T) :
    DeepRegime T' := by
  intro ε hε
  obtain ⟨x, hx, α, hα, hdisc, hdiscSwap⟩ := h ε hε
  exact ⟨x, hx, α, hα, DiscAt.refine hdisc hr,
    DiscAt.refine hdiscSwap hr.swap⟩

theorem AsymDisc.refine {T T' : Stage} {η₀ : ℝ} (h : AsymDisc T η₀) (hr : T'.Refines T) :
    AsymDisc T' η₀ := by
  intro β γ hβ hβbound hγ hγbound
  obtain ⟨q, hq, hdisc, hdiscSwap⟩ := h β γ hβ hβbound hγ hγbound
  exact ⟨q, hq, DiscAt.refine hdisc hr, DiscAt.refine hdiscSwap hr.swap⟩

private theorem eventuallyAbsent_refine_local {T T' : Stage} {P : PatchProp}
    (h : EventuallyAbsent T P) (hr : T'.Refines T) : EventuallyAbsent T' P := by
  induction hr with
  | refl T => simpa using h
  | sub T φ hφ =>
      exact hφ.tendsto_atTop.eventually h
  | @remove T X' Y' hX hY hsmall =>
      filter_upwards [h] with k hk A B hAB
      intro hsub
      apply hk A B hAB
      constructor
      · intro x hx
        exact hX k (hsub.1 hx)
      · intro y hy
        exact hY k (hsub.2 hy)
  | trans hAB hBC ihAB ihBC => exact ihAB (ihBC h)

theorem ClusterAbsent.refine {T T' : Stage} {η₀ : ℝ} (h : ClusterAbsent T η₀) (hr : T'.Refines T) :
    ClusterAbsent T' η₀ := by
  intro ζ δ hζ hδ hδbound c
  obtain ⟨habs, habsSwap⟩ := h ζ δ hζ hδ hδbound c
  exact ⟨eventuallyAbsent_refine_local habs hr,
    eventuallyAbsent_refine_local habsSwap hr.swap⟩

end HypercubeRamsey
