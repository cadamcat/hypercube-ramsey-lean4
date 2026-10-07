import HypercubeRamsey.S07.AnchorStage
import HypercubeRamsey.S03.ClockSampling

/-!
# L7.1, Steps 5–6: injective odd labels, posterior even rows and even loads

Source: `sections/07-…tex`, lines 313–391.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L7.1h, clock step (07:313–324): on a successful prehistory, Lemma 3.10 (`clock_sampling` with `B = 3`,
`C_g = 2`) applied to the odd rows (probability laws on valid cells, atoms `≤ L/N ≤ n^{-A}`, column sums
`≤ 10⁻⁸`), with predictive failure at each even role as forbidden predicate (scope its `n` odd neighbours,
product-law probability `r_v ≤ e^{-.02q} ≤ n^{-P}` since no alarm occurs), gives an injective odd assignment
avoiding all predictive failures with joint comparison `1 + ε n ≤ 2` on at most `n^3` rows. -/
theorem clock_rows (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N),
        GeomLocal Γ → RowLaw Γ M → RowCap Γ M → GoodPre Γ M σ W → ∃ J, ClockOK Γ M σ W J := by
  sorry

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

/-- L7.1i, cancellation (07:363–373): integrating the role's anchor and its product neighbour data gives the
data subdensity `M_v`, which cancels the posterior denominator:
`Σ_y M_v(y) F_x(y) μ(x) / M_v(y) ≤ μ(x) Σ_y F_x(y) ≤ μ(x)`; predictive success only decreases the integral. -/
theorem star_cancel (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hupd : StarRefUpdate Γ M) (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι) : StarCancel Γ M σ := by
  sorry

/-- L7.1i, clock comparison (07:347–352): the separated roles have disjoint odd neighbourhoods, the clock law is
supported on predictive success, and its joint comparison on the at most `n²` neighbouring odd labels replaces
the injection by independent draws from the odd rows; the integral then factors into the star integrals. -/
theorem clock_factor (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M)
    (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N))
    (hJ : ∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) : ClockFactor Γ M σ J := by
  sorry

/-- L7.1i, assembled moment (07:375–380): the clock comparison at every successful prehistory and the anchor
integral give `4^m ∏ N μ(x)` (for `m = 0` both sides are at most one). -/
theorem even_moment (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M)
    (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N))
    (hfac : ClockFactor Γ M σ J) (hint : EvenAnchorIntegral Γ M σ) : EvenMoment Γ M σ J := by
  sorry

end Nodes

/-- L7.1i, anchor integral (07:354–380): remove the cell events touching the separated target anchors (at most
`(2s+q+1)²` each, factor `2` per role); the remaining events do not read the targets, each star integral reads
anchors within distance two of its own target only (targets are at auxiliary distance at least six), so the
targets integrate independently and `star_cancel` bounds each factor. -/
theorem even_anchor_integral (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι),
      CondProductBound → GeomFacts Γ → RowLaw Γ M → AnchorLLL Γ M D₀ σ → StarCancel Γ M σ →
      EvenAnchorIntegral Γ M σ := by
  sorry

/-- L7.1i, even loads (07:338–391): for typical tags, Lemma 3.6 with near = auxiliary distance at most five
(fraction `(q+1)^5 2^{-q}`, cap `e^{.06q}` on predictive success), comparison means `N μ_{i_{g(v)}}(x)` of
average at most `C` (typicality) and a union over labels; even column sums are `|A|/N` times the normalized
average, at most one once `N ≥ C₀ 2^n`. -/
theorem even_loads (d C : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) (hC : 0 ≤ C) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
        (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)),
        GeomFacts Γ → RowLaw Γ M → EvenRowCap Γ M → Typical Γ M C σ →
        (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) → EvenMoment Γ M σ J →
        ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  sorry

/-- Step 6 assembled: at tags avoiding every `B_g` (so the cell events satisfy the local-lemma input) that are
typical, any clock-sampler family gives even column sums above one with probability at most `n 2^n 4^{-n}`. -/
theorem even_stage (D₀ d C : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hC : 0 ≤ C) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
        (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)),
        GeomFacts Γ → FilterFacts Γ M → AnchorLLL Γ M D₀ σ → Typical Γ M C σ →
        (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) →
        ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hint⟩ := even_anchor_integral D₀ d hD₀ hd hd'
  obtain ⟨n₂, C₂, hload⟩ := even_loads d C hd hd8 hC
  refine ⟨max n₁ n₂, C₂, ?_⟩
  intro n N hL E G X Y p κ Γ M σ J hG hF hA hty hJ
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hL.1
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hL.1
  have hmom : EvenMoment Γ M σ J :=
    even_moment Γ M hF.row_law σ J (clock_factor Γ M hF.row_law σ J hJ)
      (hint n hn₁ Γ M σ cond_product_bound hG hF.row_law hA
        (star_cancel Γ M hF.starRef_update hF.row_law σ))
  exact hload n N ⟨hn₂, hL.2.1, hL.2.2⟩ Γ M σ J hG hF.row_law hF.evenRow_cap hty hJ hmom

end HypercubeRamsey.S07
