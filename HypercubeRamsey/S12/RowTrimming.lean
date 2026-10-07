import HypercubeRamsey.S12.InteractionTails

/-!
# Section 12 simultaneous row trimming
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.6: simultaneously trim rows for a finite family of narrow second-side laws. -/
theorem row_trimming (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    ∀ᶠ k in atTop,
      ∀ (X₀ : Finset (Fin (T.S.N k))) (hX₀ : X₀.Nonempty),
        X₀ ⊆ T.X k →
        Real.log ((T.S.N k : ℝ) / X₀.card) ≤
          (T.S.n k : ℝ) ^ (κ.xs / 4) →
        ∀ {ι : Type} (𝒥 : Finset ι) (π : ι → Law (T.S.N k)),
          (∀ j, (π j).SupportedIn (T.Y k)) →
          (∀ j, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
          (𝒥.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) →
          ∃ X₁ ⊆ X₀,
            ((X₀ \ X₁).card : ℝ) ≤
              Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) * X₀.card ∧
            ∀ j ∈ 𝒥, ∀ x ∈ X₁,
              RowTail (T.S.E k) c (π j).w X₀ (T.S.n k) κ.ξ x := by
  sorry

/-- L12.6b: a sufficiently close law inherits the relaxed row-tail estimate. -/
theorem rowTail_relax (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    ∀ᶠ k in atTop,
      ∀ (π π' : Law (T.S.N k)) (X₀ : Finset (Fin (T.S.N k)))
        (x : Fin (T.S.N k)),
        RowTail (T.S.E k) c π.w X₀ (T.S.n k) κ.ξ x →
        (∑ y, |π.w y - π'.w y|) ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) →
        RowTailRelaxed (T.S.E k) c π'.w X₀ (T.S.n k) κ.ξ x := by
  have hξ : 0 < κ.ξ := hκ.ξ_rng.1
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hpow01 : ∀ᶠ k in atTop, 2 ≤ (T.S.n k : ℝ) ^ (0.01 : ℝ) := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).comp hn |>.eventually
      (eventually_ge_atTop 2)
  have hpow197 : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-1.97 : ℝ) ≤ 1 / 2 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1.97)).comp hn
    exact ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)) |>.mono
      (fun _ h => le_of_lt h)
  have hpow3 : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 2 * κ.ξ := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hn
    exact ht.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 2 * κ.ξ)) |>.mono
      (fun _ h => le_of_lt h)
  have hn1 : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hthreshold : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (-1.03 : ℝ) ≤
        (T.S.n k : ℝ) ^ (-1.02 : ℝ) - (T.S.n k : ℝ) ^ (-3 : ℝ) := by
    filter_upwards [hn1, hpow01] with k hk h01
    have hlow : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ (T.S.n k : ℝ) ^ (-1.03 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk (by norm_num)
    have hfactor : (T.S.n k : ℝ) ^ (-1.02 : ℝ) =
        (T.S.n k : ℝ) ^ (-1.03 : ℝ) * (T.S.n k : ℝ) ^ (0.01 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      norm_num
    rw [hfactor]
    have hprod : 2 * (T.S.n k : ℝ) ^ (-1.03 : ℝ) ≤
        (T.S.n k : ℝ) ^ (-1.03 : ℝ) * (T.S.n k : ℝ) ^ (0.01 : ℝ) :=
      calc
        2 * (T.S.n k : ℝ) ^ (-1.03 : ℝ) =
            (T.S.n k : ℝ) ^ (-1.03 : ℝ) * 2 := by ring
        _ ≤ (T.S.n k : ℝ) ^ (-1.03 : ℝ) * (T.S.n k : ℝ) ^ (0.01 : ℝ) :=
          mul_le_mul_of_nonneg_left h01
            (show 0 ≤ (T.S.n k : ℝ) ^ (-1.03 : ℝ) by positivity)
    linarith
  have hweightError : ∀ᶠ k in atTop,
      100 * (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        50 * (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-1.03 : ℝ) := by
    filter_upwards [hn1, hpow197] with k hk h197
    have hfactor : (T.S.n k : ℝ) ^ (-2 : ℝ) =
        (T.S.n k : ℝ) ^ (-0.03 : ℝ) * (T.S.n k : ℝ) ^ (-1.97 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      norm_num
    have hfactor' : (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-1.03 : ℝ) =
        (T.S.n k : ℝ) ^ (-0.03 : ℝ) := by
      calc
        (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-1.03 : ℝ) =
        (T.S.n k : ℝ) ^ (1 : ℝ) * (T.S.n k : ℝ) ^ (-1.03 : ℝ) := by
          rw [Real.rpow_one]
        _ = (T.S.n k : ℝ) ^ ((1 : ℝ) + (-1.03 : ℝ)) := by
          rw [← Real.rpow_add (by positivity)]
        _ = (T.S.n k : ℝ) ^ (-0.03 : ℝ) := by congr 1 <;> norm_num
    rw [hfactor]
    have hprod := mul_le_mul_of_nonneg_left h197
      (show 0 ≤ 100 * (T.S.n k : ℝ) ^ (-0.03 : ℝ) by positivity)
    calc
      100 * ((T.S.n k : ℝ) ^ (-0.03 : ℝ) * (T.S.n k : ℝ) ^ (-1.97 : ℝ)) ≤
          50 * (T.S.n k : ℝ) ^ (-0.03 : ℝ) := by nlinarith
      _ = 50 * (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-1.03 : ℝ) := by
        rw [← hfactor']
        ring
  have hexp : ∀ᶠ k in atTop,
      Real.exp (-((T.S.n k : ℝ) ^ (0.2 : ℝ))) ≤
        Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ))) := by
    filter_upwards [hn1] with k hk
    have hp := Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (0.19 : ℝ) ≤ 0.2)
    exact Real.exp_le_exp.mpr (by linarith)
  filter_upwards [hn1, hthreshold, hweightError, hpow3, hexp] with
      k hk hthreshold hweightError hpow3 hexp
  intro π π' X₀ x hrow hl1
  have hfv : ∀ a y : Fin (T.S.N k), |fv (T.S.E k) c a y| = 1 := by
    intro a y
    unfold fv hit
    split_ifs <;> norm_num
  have hcorr : ∀ a b : Fin (T.S.N k),
      |corr (T.S.E k) c π.w a b - corr (T.S.E k) c π'.w a b| ≤
        ∑ y, |π.w y - π'.w y| := by
    intro a b
    rw [corr, corr]
    calc
      |(∑ y, π.w y * fv (T.S.E k) c a y * fv (T.S.E k) c b y) -
          ∑ y, π'.w y * fv (T.S.E k) c a y * fv (T.S.E k) c b y| =
          |∑ y, (π.w y - π'.w y) * fv (T.S.E k) c a y * fv (T.S.E k) c b y| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ ≤ ∑ y, |(π.w y - π'.w y) * fv (T.S.E k) c a y * fv (T.S.E k) c b y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, |π.w y - π'.w y| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_mul, abs_mul, hfv a y, hfv b y]
        ring
  have hn3 : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 2 * κ.ξ := hpow3
  have hlowerCorr : ∀ z : Fin (T.S.N k),
      (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z| →
        (T.S.n k : ℝ) ^ (-1.03 : ℝ) < |corr (T.S.E k) c π.w x z| := by
    intro z hzlarge
    have hdiffz : |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| ≤
        (T.S.n k : ℝ) ^ (-3 : ℝ) := le_trans (hcorr x z) hl1
    have hclosez : |corr (T.S.E k) c π'.w x z| ≤
        |corr (T.S.E k) c π.w x z| + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
      calc
        |corr (T.S.E k) c π'.w x z| =
            |corr (T.S.E k) c π.w x z -
              (corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z)| := by
          congr 1 <;> ring
        _ ≤ |corr (T.S.E k) c π.w x z| +
              |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| := abs_sub _ _
        _ ≤ _ := by nlinarith [hdiffz]
    have hlt : (T.S.n k : ℝ) ^ (-1.02 : ℝ) -
        (T.S.n k : ℝ) ^ (-3 : ℝ) < |corr (T.S.E k) c π.w x z| := by
      linarith
    exact lt_of_le_of_lt hthreshold hlt
  have hnewSubset : X₀.filter (fun z =>
      (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z|) ⊆
      X₀.filter (fun z => (T.S.n k : ℝ) ^ (-1.03 : ℝ) <
        |corr (T.S.E k) c π.w x z|) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hzX, hzlarge⟩
    exact ⟨hzX, hlowerCorr z hzlarge⟩
  have hnewWeightedSubset : X₀.filter (fun z =>
      (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z| ∧
        |corr (T.S.E k) c π'.w x z| ≤ 2 * κ.ξ) ⊆
      X₀.filter (fun z => (T.S.n k : ℝ) ^ (-1.03 : ℝ) <
        |corr (T.S.E k) c π.w x z| ∧
        |corr (T.S.E k) c π.w x z| ≤ 4 * κ.ξ) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hzX, hzlarge, hzsmall⟩
    refine ⟨hzX, ?_, ?_⟩
    · exact hlowerCorr z hzlarge
    · have hdiffz : |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| ≤
        (T.S.n k : ℝ) ^ (-3 : ℝ) := by
        exact le_trans (hcorr x z) hl1
      have hclosez : |corr (T.S.E k) c π.w x z| ≤
          |corr (T.S.E k) c π'.w x z| + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
        calc
          |corr (T.S.E k) c π.w x z| =
              |corr (T.S.E k) c π'.w x z +
                (corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z)| := by ring_nf
          _ ≤ |corr (T.S.E k) c π'.w x z| +
                |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| := abs_add_le _ _
          _ ≤ _ := by nlinarith [hdiffz]
      linarith
  have hweightPoint : ∀ z ∈ X₀.filter (fun z =>
      (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z| ∧
        |corr (T.S.E k) c π'.w x z| ≤ 2 * κ.ξ),
      Real.exp (100 * (T.S.n k : ℝ) * |corr (T.S.E k) c π'.w x z|) ≤
        Real.exp (150 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z|) := by
    intro z hz
    simp only [Finset.mem_filter] at hz
    have hdiffz : |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| ≤
        (T.S.n k : ℝ) ^ (-3 : ℝ) := by
      exact le_trans (hcorr x z) hl1
    have hclosez : |corr (T.S.E k) c π'.w x z| ≤
        |corr (T.S.E k) c π.w x z| + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
      calc
        |corr (T.S.E k) c π'.w x z| =
            |corr (T.S.E k) c π.w x z -
              (corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z)| := by
          congr 1 <;> ring
        _ ≤ |corr (T.S.E k) c π.w x z| +
              |corr (T.S.E k) c π.w x z - corr (T.S.E k) c π'.w x z| := abs_sub _ _
        _ ≤ _ := by nlinarith [hdiffz]
    have hlargeOld : (T.S.n k : ℝ) ^ (-1.03 : ℝ) <
        |corr (T.S.E k) c π.w x z| := by
      have hlt : (T.S.n k : ℝ) ^ (-1.02 : ℝ) -
          (T.S.n k : ℝ) ^ (-3 : ℝ) < |corr (T.S.E k) c π.w x z| := by
        linarith [hz.2.1, hclosez]
      exact hlowerCorr z hz.2.1
    have herror' : 100 * (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        50 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z| := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hlargeOld)
        (show 0 ≤ 50 * (T.S.n k : ℝ) by positivity)
      nlinarith
    apply Real.exp_le_exp.mpr
    have hlin := mul_le_mul_of_nonneg_left hclosez
      (show 0 ≤ 100 * (T.S.n k : ℝ) by positivity)
    have hnprod : (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-3 : ℝ) =
        (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      calc
        (T.S.n k : ℝ) * (T.S.n k : ℝ) ^ (-3 : ℝ) =
            (T.S.n k : ℝ) ^ (1 : ℝ) * (T.S.n k : ℝ) ^ (-3 : ℝ) := by simp
        _ = (T.S.n k : ℝ) ^ ((1 : ℝ) + (-3 : ℝ)) := by
          rw [← Real.rpow_add (by positivity)]
        _ = (T.S.n k : ℝ) ^ (-2 : ℝ) := by congr 1 <;> norm_num
    calc
      100 * (T.S.n k : ℝ) * |corr (T.S.E k) c π'.w x z| ≤
          100 * (T.S.n k : ℝ) *
            (|corr (T.S.E k) c π.w x z| + (T.S.n k : ℝ) ^ (-3 : ℝ)) := hlin
      _ = 100 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z| +
            100 * (T.S.n k : ℝ) ^ (-2 : ℝ) := by rw [← hnprod]; ring
      _ ≤ 100 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z| +
          50 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z| := by
          nlinarith [herror']
      _ = 150 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z| := by ring
  constructor
  · have hcard := Finset.card_le_card hnewSubset
    calc
      ((X₀.filter (fun z => (T.S.n k : ℝ) ^ (-1.02 : ℝ) <
        |corr (T.S.E k) c π'.w x z|)).card : ℝ) ≤
          ((X₀.filter (fun z => (T.S.n k : ℝ) ^ (-1.03 : ℝ) <
            |corr (T.S.E k) c π.w x z|)).card : ℝ) := by exact_mod_cast hcard
      _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.2 : ℝ))) * X₀.card := hrow.1
      _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ))) * X₀.card :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
  · calc
      (∑ z ∈ X₀.filter (fun z =>
          (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z| ∧
            |corr (T.S.E k) c π'.w x z| ≤ 2 * κ.ξ),
        Real.exp (100 * (T.S.n k : ℝ) * |corr (T.S.E k) c π'.w x z|)) ≤
          ∑ z ∈ X₀.filter (fun z =>
            (T.S.n k : ℝ) ^ (-1.02 : ℝ) < |corr (T.S.E k) c π'.w x z| ∧
              |corr (T.S.E k) c π'.w x z| ≤ 2 * κ.ξ),
            Real.exp (150 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z|) := by
        apply Finset.sum_le_sum
        intro z hz
        exact hweightPoint z hz
      _ ≤ ∑ z ∈ X₀.filter (fun z =>
            (T.S.n k : ℝ) ^ (-1.03 : ℝ) < |corr (T.S.E k) c π.w x z| ∧
              |corr (T.S.E k) c π.w x z| ≤ 4 * κ.ξ),
            Real.exp (150 * (T.S.n k : ℝ) * |corr (T.S.E k) c π.w x z|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hnewWeightedSubset
        intro z hz hznot
        exact Real.exp_nonneg _
      _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.2 : ℝ))) * X₀.card := hrow.2
      _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.19 : ℝ))) * X₀.card :=
        mul_le_mul_of_nonneg_right hexp (by positivity)

/-- L12.6: assembly exposing both the simultaneous trimming and interpolation relaxation. -/
theorem row_trimming_export (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) :
    (∀ᶠ k in atTop,
      ∀ (X₀ : Finset (Fin (T.S.N k))) (hX₀ : X₀.Nonempty),
        X₀ ⊆ T.X k →
        Real.log ((T.S.N k : ℝ) / X₀.card) ≤
          (T.S.n k : ℝ) ^ (κ.xs / 4) →
        ∀ {ι : Type} (𝒥 : Finset ι) (π : ι → Law (T.S.N k)),
          (∀ j, (π j).SupportedIn (T.Y k)) →
          (∀ j, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
          (𝒥.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) →
          ∃ X₁ ⊆ X₀,
            ((X₀ \ X₁).card : ℝ) ≤
              Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) * X₀.card ∧
            ∀ j ∈ 𝒥, ∀ x ∈ X₁,
              RowTail (T.S.E k) c (π j).w X₀ (T.S.n k) κ.ξ x) ∧
    (∀ᶠ k in atTop,
      ∀ (π π' : Law (T.S.N k)) (X₀ : Finset (Fin (T.S.N k)))
        (x : Fin (T.S.N k)),
        RowTail (T.S.E k) c π.w X₀ (T.S.n k) κ.ξ x →
        (∑ y, |π.w y - π'.w y|) ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) →
        RowTailRelaxed (T.S.E k) c π'.w X₀ (T.S.n k) κ.ξ x) := by
  exact ⟨row_trimming κ hκ T hDeep c, rowTail_relax κ hκ T hDeep c⟩

end HypercubeRamsey.S12
