import HypercubeRamsey.S08.L81.LoadNodes_q_s08_load

/-!
# Lemma 8.1, Step 9: selected-anchor load bounds

Source: `sections/08-…tex`, lines 304–363 (L8.1i).  Two scattered-moment applications: first to the comparison
means `B_g(x)` under the hidden law, then to the selected laws under the centre randomness at a fixed hidden
history.
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The comparison-mean load constant `8(40K + 1)` (08:350). -/
def compC (K : ℝ) : ℝ := 8 * (40 * K + 1)

/-- The selected-anchor load constant `4(compC K + 1)` (08:363). -/
def loadC (K : ℝ) : ℝ := 4 * (compC K + 1)

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1i(i) (08:313–332): given hidden tuples avoiding the hidden events, force a centre present and fix its tag
(independent of positions, activations and ties, law `S_g`): Lemma 3.8 bounds its gated selection probability at
level zero by `3/λ` (`height_selection_tie`) and at a positive level by `e^{-n^c}` (`height_selection_positive`,
forced centre); the presence probability is `λ/V`, so the sum over centres has weight `3 + Hλe^{-n^c} ≤ 3.1`.  On
the gates `S_g(i)U_{g,i}(x) ≤ η_g(i)μ_i(x)1[x hits Θ_{E(g)}]/((1-Δ)·.8A_g)`, so the mean is at most `B_g(x)`. -/
theorem select_mean (hη₀ : 0 < η₀) (hp : 0 < p)
    (hadm : HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.SelectMean := by
  exact Lane_q_s08_load.select_mean η₀ β p h hη₀ hp hadm

/-- L8.1i(ii) (08:336–343): under the raw hidden law `E η_g = Λ` (averaging `Θ_g`), the cross tuples are independent
of `Θ_g` and a retained `x` survives them with probability `α_x^{|E(g)|} ≤ 1.1A_g` (survival, `|E(g)| ≤ 2s`), and
`N E_Λ μ_i(x) ≤ 4K`; so `E B_g(x) ≤ 8 · 1.1 · 4K ≤ 40K`. -/
theorem bcomp_mean (hη₀ : 0 < η₀) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.BcompMean K := by
  exact Lane_q_s08_load.bcomp_mean η₀ γ β p K h hη₀ hK

/-- L8.1i(iii) (08:345–350): Lemma 3.6 (with labels, `scatteredMoments_union_labels`) for the comparison means under
the hidden law.  Rows are near when their keys are within distance eight (fraction `f_grid`); `B_g` reads `Θ` on
`B_grid(g, 1)`, its cap is `L_B = exp(O(hs + hn^β + n^{τ/2}))` and `n f_grid L_B ≤ 1`; for separated rows, removing
the at most `(2s+1)^3` hidden events touching each neighbourhood costs `(1 - x_H)^{-(2s+1)^3} ≤ 2`
(`CondProductBound`) and leaves raw means at most `40K`. -/
theorem comp_tail (cH : ℝ) (hcH : 0 < cH) (hη₀ : 0 < η₀) (hβτ : β < tau8 η₀ / 4) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → CondProductBound → D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) →
      D.BcompMean K →
      D.hiddenLaw.pr (fun Θ => ¬ D.CompOK (compC K) Θ) ≤ (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  exact Lane_q_s08_load.bcomp_tail η₀ γ β p K h cH hcH hη₀ hβτ hK

/-- L8.1i(iv) (08:352–363): at a hidden history avoiding the hidden events with comparison loads at most
`compC K`, Lemma 3.6 for the selected laws under positions, tags, activations and ties.  Selections at residual
words more than `2r + 8H + 4` apart read disjoint centre inputs (`SelLocal`), so success is kept as the local
legality indicator and separated rows factor into means at most `B_g(x)` (`SelectMean`); near rows have fraction
`f_res(2r + 8H + 4) ≤ e^{-cn}`, the cap is `L_U = exp(n^γ + n^{2τ} + O(1)) = e^{o(n)}`, and `n f_res L_U ≤ 1`. -/
theorem center_tail (c : ℝ) (hc : 0 < c) (hη₀ : 0 < η₀) (hγ₁ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → fRes η₀ D.n (2 * rH D.n + 8 * HH η₀ D.n + 4) ≤ Real.exp (-c * D.n) →
      D.SelLocal → D.SelectMean → D.SelConseq →
      ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → D.CompOK (compC K) Θ →
        (FinProb.bind D.posLaw fun _ => D.rawTAT Θ).pr
            (fun z => D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK (loadC K) ((Θ, z.1), z.2)) ≤
          (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  sorry

/-- L8.1i, averaging (08:304–312): the pre-anchor law draws the hidden history from the hidden law (supported on
histories avoiding the hidden events once these have positive raw probability), then positions, tags, activations
and ties; splitting on the comparison bound gives the joint load bound. -/
theorem load_tail (D : Ctx η₀ β p h) (C₁ C₂ a b : ℝ) (hb : 0 ≤ b)
    (hpos : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g))
    (hcomp : D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) ≤ a)
    (hcenter : ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → D.CompOK C₁ Θ →
      (FinProb.bind D.posLaw fun _ => D.rawTAT Θ).pr
        (fun z => D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK C₂ ((Θ, z.1), z.2)) ≤ b) :
    D.preLaw.pr (fun q => D.SelOK q ∧ ¬ D.LoadOK C₂ q) ≤ a + b := by
  exact Lane_q_s08_load.load_tail D C₁ C₂ a b hb hpos hcomp hcenter

end Nodes

end HypercubeRamsey.S08
