import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior

/-!
# L7.1, Steps 2–4: cell failure, predictive alarms, anchor avoidance and odd column sums

Source: `sections/07-…tex`, lines 150–161 (cell failure at fixed tags), 196–245 (alarms), 247–311 (anchor
conditioning and odd loads).
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

/-- L7.1d at fixed tags (07:150–161, 166): the raw failure probability of a cell is at most the key's
cross-failure probability (the cross anchors `W (h, t)` are independent with laws `μ_{σ h}`, as in
`crossFailKey`, for every `t`) plus `n²(q+1)e^{-n^p}` (the `q + 1` own anchors are independent draws from
`μ_{σ g}` and every label of `ν_{σ g}` has degree `≥ 1 - e^{-n^p}` into it; Markov's inequality). -/
theorem cell_invalid_prob (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hn : 1 ≤ n)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι) : CellInvalidBound Γ M σ := by
  sorry

/-- L7.1f(ii) (07:219–231): `E_{W_{g,t}} r_v ≤ e^{-.04q}` with everything else fixed: the integrand of `r_v`
over the role's anchor is the data subdensity `M_v`, `Q_v` does not move, and Lemma 3.7's first assertion
(`gated_posterior`, `ε = e^{-.04q}`) bounds the failure mass. -/
theorem alarm_mean (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hupd : StarRefUpdate Γ M) : AlarmMean Γ M := by
  sorry

/-- L7.1f(iii) (07:233–240): the alarm rate of an even role depends on it only through its cell and the
multiset of its neighbours' cells; at a cell `(g, t)` that multiset is fixed by the counts at `(g, t)` and at
the `≤ 2s` cells `(h, t)`, `h ∈ E(g)` (each auxiliary neighbour occurs once), so at most `(n+1)^{2s+1}` formulas
occur. -/
theorem alarm_reps (Γ : GridGeom d n s ℓ q) (hloc : GeomLocal Γ) (M : Menu7 n N E G X Y d p κ) :
    AlarmReps Γ M := by
  sorry

/-- L7.1f (07:240–245): a union over the alarm formulas of one cell and Markov's inequality,
`(n+1)^{2s+1} e^{.02q} e^{-.04q}`. -/
theorem alarm_prob (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hmean : AlarmMean Γ M)
    (hreps : AlarmReps Γ M) (σ : Γ.Key → M.ι) : AlarmProb Γ M σ := by
  sorry

end Nodes

/-- L7.1g, first part (07:247–259): at tags avoiding every `B_g` the cell events satisfy the local-lemma input
with charge `n^{-D₀/4}`: `CellBad` at `c` reads the anchors within distance two of `c`, two events meet only
within distance four (at most `(2s+q+1)^4` cells), and
`Pr(CellBad) ≤ n^{-D₀/2} + n²(q+1)e^{-n^p} + (n+1)^{2s+1}e^{-.02q} ≤ n^{-D₀/4}(1 - n^{-D₀/4})^{(2s+q+1)^4}`
for large `n`, since `16d < D₀/4`. -/
theorem anchor_lll (D₀ d p : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι),
      GeomFacts Γ → CellInvalidBound Γ M σ → AlarmProb Γ M σ → (∀ g, ¬ TagBad Γ M D₀ σ g) →
      AnchorLLL Γ M D₀ σ := by
  sorry

/-- L7.1g, moments (07:280–298): for odd roles whose grid keys are pairwise at distance at least three, the
two-stage law (tag law, then anchor law) satisfies `E ∏ Z_{u_j} ≤ 4^m ∏ d_{u_j}`, `Z_u = N p_{g(u),t(u)}(y)`,
`d_u` the raw mean.  First remove the cell events touching the disjoint lists (at most `(2s+q+1)^3` each, factor
`2` per role) and integrate the raw anchors; then remove the tag events touching the disjoint key balls (at most
`(2s+1)^2` each, factor `2` per role) and integrate the raw tags; `12d < D₀/4`. -/
theorem odd_moment (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      CondProductBound → GeomFacts Γ → TagLLL Γ M Q D₀ →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ) → OddMoment Γ M Q D₀ := by
  sorry

/-- L7.1g, odd loads (07:300–311): Lemma 3.6 with near = grid distance at most two (fraction
`(2s+1)²(2n^{-d/4})^s`, cap `L`), comparison means of average at most `K` (profile (ii) and the uniform
auxiliary word), and a union over labels; the column sum is `|B|/N` times the normalized average, at most
`θ₀ = 10⁻⁸` once `N ≥ C₀ 2^n`. -/
theorem odd_loads (D₀ d K : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
        GeomFacts Γ → RowCap Γ M → OddMoment Γ M P.Q D₀ →
        (FinProb.bind (tagLaw Γ M P.Q D₀) (anchorLaw Γ M)).pr
            (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  sorry

/-- Steps 2–4 assembled: at tags avoiding every `B_g` the cell events satisfy the local-lemma input, and under
the two-stage law the odd column sums exceed `θ₀` with probability at most `n 2^n 4^{-n}`. -/
theorem anchor_stage (D₀ d p K : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hp : 0 < p) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
        GeomFacts Γ → FilterFacts Γ M → TagLLL Γ M P.Q D₀ →
        (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ) ∧
          (FinProb.bind (tagLaw Γ M P.Q D₀) (anchorLaw Γ M)).pr
              (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
            (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hA⟩ := anchor_lll D₀ d p hD₀ hd hd' hp
  obtain ⟨n₂, hmom⟩ := odd_moment D₀ d hD₀ hd hd'
  obtain ⟨n₃, C₃, hodd⟩ := odd_loads D₀ d K hd hd8 hK
  refine ⟨max (max n₁ n₂) (max n₃ 1), C₃, ?_⟩
  intro n N hL E G X Y κ Γ M P hG hF hT
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL.1
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL.1
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL.1
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL.1
  have hAll : ∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ := fun σ hσ =>
    hA n hn₁ Γ M σ hG (cell_invalid_prob Γ M hn1 hG.loc σ)
      (alarm_prob Γ M (alarm_mean Γ M hF.starRef_update) (alarm_reps Γ hG.loc M) σ) hσ
  refine ⟨hAll, ?_⟩
  exact hodd n N ⟨hn₃, hL.2.1, hL.2.2⟩ Γ M P hG hF.row_cap
    (hmom n hn₂ Γ M P.Q cond_product_bound hG hT hAll)

end HypercubeRamsey.S07
