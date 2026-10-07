import HypercubeRamsey.S07.Support
import HypercubeRamsey.S07.EvenStage
import HypercubeRamsey.Framework.OneShot

/-!
# Lemma 7.1: small-grid purity exclusion

Source: `sections/07-…tex`, lines 41–392.  The stages (`tag_stage`, `anchor_stage`, `clock_rows`,
`even_stage`) and the three-stage averaging node `grid_realization_of` give a realization with valid cells, an
injective odd assignment avoiding predictive failure, and even column sums at most one (07:386–391); the
posterior even rows of that realization are Hall data (07:391–392), and the framework's `cubeAt_of_rows`
(F-HallEmbed) gives the cube.
-/

namespace HypercubeRamsey.S07

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

/-- The conclusion of the probabilistic construction in L7.1i, before applying Hall's embedding theorem. -/
def GridHallData {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) : Prop :=
  ∃ (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (p : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ),
      Function.Injective fB ∧
      (∀ a x, 0 ≤ p a x) ∧
      (∀ a, ∑ x, p a x = 1) ∧
      (∀ a x, p a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
        (cube n).Adj a.1 b.1 → Hits E G x (fB b)) ∧
      (∀ x, ∑ a, p a x ≤ 1)

/-- Monotonicity of the large regime in its constants. -/
theorem largeAt_weaken {n₀ n₀' : ℕ} {C₀ C₀' : ℝ} {n N : ℕ} (h : LargeAt n₀ C₀ n N)
    (hn : n₀' ≤ n₀) (hC : C₀' ≤ C₀) : LargeAt n₀' C₀' n N :=
  ⟨le_trans hn h.1, le_trans (mul_le_mul_of_nonneg_right hC (by positivity)) h.2.1, h.2.2⟩

/-- L7.1, Steps 4–6 averaged (07:386–391): if typical tags fail with probability at most `δ = n 2^n 4^{-n}`, the
odd column sums exceed `θ₀` with probability at most `δ` under the two-stage law, both avoidance events have
positive mass, successful prehistories admit clock-sampler laws, and at typical admitted tags every
clock-sampler family has even column sums above one with probability at most `δ`, then (as `3δ < 1` for large
`n`) some realization has valid cells, an injective odd assignment avoiding predictive failure, and even column
sums at most one. -/
theorem grid_realization_of :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {d : ℝ} {s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
      (Q : Γ.Key → FinProb M.ι) (D₀ C : ℝ), 0 < N →
      (tagLaw Γ M Q D₀).pr (fun σ => ¬ Typical Γ M C σ) ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).pr
          (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n →
      0 < (FinProb.pi Q).pr (fun σ => ∀ g, ¬ TagBad Γ M D₀ σ g) →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) →
        0 < (rawAnchors Γ M σ).pr (fun W => ∀ c, ¬ CellBad Γ M σ W c)) →
      (∀ σ W, GoodPre Γ M σ W → ∃ J, ClockOK Γ M σ W J) →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → Typical Γ M C σ →
        ∀ J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N),
          (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) →
          ∑ W, (anchorLaw Γ M σ).w W *
              (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
            (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) →
      ∃ (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N),
        (∀ c, CellValid Γ M σ W c) ∧ Function.Injective f ∧
        (∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a)) ∧
        ∀ x, evenColumn Γ M σ W f x ≤ 1 := by
  sorry

/-- F-HallEmbed input from a good realization (07:389–392): the posterior even rows are probability laws on the
common neighbourhoods of the injective odd labels, with column sums at most one. -/
theorem hall_data_of_realization {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hlaw : EvenRowLaw Γ M) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N)
    (hinj : Function.Injective f) (hpf : ∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a))
    (hcol : ∀ x, evenColumn Γ M σ W f x ≤ 1) : GridHallData (n := n) E G :=
  ⟨f, fun a x => evenRow Γ M σ W f a x, hinj, fun a x => (hlaw σ W f a (hpf a)).1 x,
    fun a => (hlaw σ W f a (hpf a)).2.1, fun a x hx => (hlaw σ W f a (hpf a)).2.2 x hx, hcol⟩

/-- L7.1, Steps 1–6 assembled at one dimension: on sets satisfying (7.1), every geometry and menu of the lemma
admit a good realization. -/
theorem grid_realization (D₀ d p κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hp : 0 < p) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ), Eq71At D₀ d n N E X Y →
        ∃ (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N),
          (∀ c, CellValid Γ M σ W c) ∧ Function.Injective f ∧
          (∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a)) ∧
          ∀ x, evenColumn Γ M σ W f x ≤ 1 := by
  have hd8 : d < 1 / 8 := by linarith
  set K : ℝ := 4 / κ with hKdef
  have hK : 0 ≤ K := by positivity
  set C : ℝ := 8 * (K + 1) with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨nF, hfilt⟩ := filterFacts d hd hd8
  obtain ⟨nT, htag⟩ := tag_stage D₀ d K hD₀ hD₀' hd hd' hK
  obtain ⟨nA, CA, hanchor⟩ := anchor_stage D₀ d p K hD₀ hD₀' hd hd' hp hK
  obtain ⟨nK, CK, hclock⟩ := clock_rows d hd hd8
  obtain ⟨nE, CE, heven⟩ := even_stage D₀ d C hD₀ hD₀' hd hd' hC
  obtain ⟨nR, hreal⟩ := grid_realization_of
  refine ⟨max (max (max nF nT) (max nA nK)) (max nE nR), max (max CA CK) (max CE 1), ?_⟩
  intro n N hL E G X Y Γ M h71
  have hn : max (max (max nF nT) (max nA nK)) (max nE nR) ≤ n := hL.1
  have hnF : nF ≤ n := by omega
  have hnT : nT ≤ n := by omega
  have hnR : nR ≤ n := by omega
  have hLA : LargeAt nA CA n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_left CA CK) (le_max_left _ _))
  have hLK : LargeAt nK CK n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_right CA CK) (le_max_left _ _))
  have hLE : LargeAt nE CE n N :=
    largeAt_weaken hL (by omega) (le_trans (le_max_left CE 1) (le_max_right _ _))
  have hNreal : (1 : ℝ) * 2 ^ n ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right CE 1) (le_max_right _ _))
      (by positivity)) hL.2.1
  have hN : 0 < N := by
    have h2 : (0 : ℝ) < 1 * 2 ^ n := by positivity
    exact_mod_cast lt_of_lt_of_le h2 hNreal
  have hG : GeomFacts Γ := geomFacts Γ
  have hF : FilterFacts Γ M := hfilt n hnF Γ M hN hG
  obtain ⟨P⟩ := grid_profiles balanced_mixture_sub Γ M hκ hN hF.row_law
  obtain ⟨hT, htyp⟩ := htag n hnT Γ M P hN hL.2.2 hG h71
  obtain ⟨hA, hodd⟩ := hanchor n N hLA Γ M P hG hF hT
  exact hreal n hnR Γ M P.Q D₀ C hN htyp hodd (cond_product_bound _ _ _ _ _ hT).1
    (fun σ hσ => (cond_product_bound _ _ _ _ _ (hA σ hσ)).1)
    (fun σ W hW => hclock n N hLK Γ M σ W hG.loc hF.row_law hF.row_cap hW)
    (fun σ hσ hty J hJ => heven n N hLE Γ M σ J hG hF (hA σ hσ) hty hJ)

/-- Lemma 7.1 before the Hall step: the one-shot hypotheses give Hall data. -/
theorem grid_hall_data_from_input
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → GridHallData (n := n) E G := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨nG, hgeom⟩ := gridGeom_exists d hd hd8
  obtain ⟨nF, hfilt⟩ := filterFacts d hd hd8
  obtain ⟨nR, CR, hreal⟩ := grid_realization D₀ d p₀ κ hD₀ hD₀' hd hd' hp₀ hκ
  refine ⟨max (max nG nF) nR, max CR 1, ?_⟩
  intro n N E X Y G hL h71 havail
  have hn : max (max nG nF) nR ≤ n := hL.1
  have hnG : nG ≤ n := by omega
  have hnF : nF ≤ n := by omega
  have hLR : LargeAt nR CR n N := largeAt_weaken hL (by omega) (le_max_left _ _)
  have hNreal : (1 : ℝ) * 2 ^ n ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right CR 1) (by positivity)) hL.2.1
  have hN : 0 < N := by
    have h2 : (0 : ℝ) < 1 * 2 ^ n := by positivity
    exact_mod_cast lt_of_lt_of_le h2 hNreal
  obtain ⟨M⟩ := menu7_of_available hκ.le havail
  obtain ⟨Γ⟩ := hgeom n hnG
  have hF : FilterFacts Γ M := hfilt n hnF Γ M hN (geomFacts Γ)
  obtain ⟨σ, W, f, _hvalid, hinj, hpf, hcol⟩ := hreal n N hLR Γ M h71
  exact hall_data_of_realization Γ M hF.evenRow_law σ W f hinj hpf hcol

/-- L7.1 (07:41–391), the one-shot small-grid purity exclusion. -/
theorem small_grid_purity
    (D₀ d p₀ κ : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10)
    (hd : 0 < d) (hd' : d < D₀ / 1000) (hp₀ : 0 < p₀) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop,
      ∀ X Y : Finset (Fin N), ∀ G : Colour,
        LargeAt n₀ C₀ n N → Eq71At D₀ d n N E X Y →
        AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y → CubeAt n N E := by
  obtain ⟨n₀, C₀, hnode⟩ := by
    exact grid_hall_data_from_input D₀ d p₀ κ hD₀ hD₀' hd hd' hp₀ hκ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y G hlarge h71 havail
  obtain ⟨fB, p, hinj, hp0, hp1, hsupp, hload⟩ :=
    hnode n N E X Y G hlarge h71 havail
  exact cubeAt_of_rows E G fB hinj p hp0 hp1 hsupp hload

end HypercubeRamsey.S07
