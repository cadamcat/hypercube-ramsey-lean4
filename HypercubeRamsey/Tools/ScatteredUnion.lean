import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.Framework.FinProb

/-!
# L3.6c: scattered moments with a union over labels

This corollary packages the general scattered-moment estimate with Markov's inequality and a finite union
bound. It allows any finite label type whose size is at most `n·2^n`, rather than hard-coding `Fin N`.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- L3.6c: under the separated-product hypotheses of `scattered_moments`, if `n f L ≤ 1` and the number of
labels is at most `n·2^n`, then the success event and a large average at any label have total probability at
most `n·2^n·4⁻ⁿ`. -/
theorem scatteredMoments_union_labels
    {Ω U Label : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype Label] [DecidableEq Label] (P : FinProb Ω) (succ : Finset Ω)
    (Z : U → Label → Ω → ℝ) (hZ0 : ∀ v y ω, 0 ≤ Z v y ω)
    (L : ℝ) (hL : 0 ≤ L) (hZL : ∀ v y ω, ω ∈ succ → Z v y ω ≤ L)
    (near : U → Finset U) (hself : ∀ v, v ∈ near v)
    (f : ℝ) (hf : 0 ≤ f)
    (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (hn : 0 < n) (K D₀ : ℝ) (hK : 1 ≤ K) (hD₀ : 0 ≤ D₀)
    (d : U → Label → ℝ) (hd : ∀ v y, 0 ≤ d v y)
    (hmean : ∀ y, (Fintype.card U : ℝ)⁻¹ * ∑ v, d v y ≤ D₀)
    (hjoint : ∀ y (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) y ω ≤ K ^ m * ∏ i, d (s i) y)
    (hsmall : (n : ℝ) * f * L ≤ 1)
    (hlabels : (Fintype.card Label : ℝ) ≤ (n : ℝ) * 2 ^ n) :
    (∑ ω, if ω ∈ succ ∧ ∃ y,
      4 * K * (D₀ + 1) < (Fintype.card U : ℝ)⁻¹ * ∑ v, Z v y ω then P.w ω else 0) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  let average (y : Label) (ω : Ω) : ℝ :=
    (Fintype.card U : ℝ)⁻¹ * ∑ v, Z v y ω
  let threshold : ℝ := 4 * K * (D₀ + 1)
  have hU : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hD : 0 < D₀ + 1 := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hmeanNonneg (y : Label) :
      0 ≤ (Fintype.card U : ℝ)⁻¹ * ∑ v, d v y := by
    apply mul_nonneg (inv_nonneg.mpr hU.le)
    exact Finset.sum_nonneg fun v _ => hd v y
  have hmeanCap (y : Label) :
      (Fintype.card U : ℝ)⁻¹ * ∑ v, d v y + (n : ℝ) * f * L ≤ D₀ + 1 := by
    linarith [hmean y, hsmall]
  have hvarianceNonneg : 0 ≤ (n : ℝ) * f * L := by positivity
  have hbaseNonneg (y : Label) :
      0 ≤ (Fintype.card U : ℝ)⁻¹ * ∑ v, d v y + (n : ℝ) * f * L :=
    add_nonneg (hmeanNonneg y) hvarianceNonneg
  have hmomentCap (y : Label) :
      ∑ ω ∈ succ, P.w ω * (average y ω) ^ n ≤ K ^ n * (D₀ + 1) ^ n := by
    have hm := scattered_moments P.w P.nonneg succ
      (fun v ω => Z v y ω) (fun v ω => hZ0 v y ω) L hL
      (by intro v ω hω; exact hZL v y ω hω)
      near hself f hnear n K hK (fun v => d v y) (fun v => hd v y)
      (by
        intro m hm s hsep
        exact hjoint y m hm s hsep)
    dsimp [average]
    calc
      ∑ ω ∈ succ, P.w ω *
          ((Fintype.card U : ℝ)⁻¹ * ∑ v, Z v y ω) ^ n ≤
        K ^ n * ((Fintype.card U : ℝ)⁻¹ * ∑ v, d v y + n * f * L) ^ n := hm
      _ ≤ K ^ n * (D₀ + 1) ^ n := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hbaseNonneg y) (hmeanCap y) n) (by positivity)
  have hthresholdPow : threshold ^ n = (4 : ℝ) ^ n * K ^ n * (D₀ + 1) ^ n := by
    dsimp [threshold]
    rw [mul_pow, mul_pow]
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hDne : D₀ + 1 ≠ 0 := ne_of_gt hD
  have havgNonneg (y : Label) (ω : Ω) : 0 ≤ average y ω := by
    dsimp [average]
    apply mul_nonneg (inv_nonneg.mpr hU.le)
    exact Finset.sum_nonneg fun v _ => hZ0 v y ω
  have htail (y : Label) :
      (∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0) ≤
        (1 / 4 : ℝ) ^ n := by
    have hsumIte (g : Ω → ℝ) :
        (∑ ω ∈ succ, g ω) = ∑ ω, if ω ∈ succ then g ω else 0 := by
      classical
      exact (Finset.sum_ite_mem_eq succ g).symm
    have hmarkov : threshold ^ n *
        (∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0) ≤
          ∑ ω ∈ succ, P.w ω * (average y ω) ^ n := by
      rw [Finset.mul_sum, hsumIte]
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hs : ω ∈ succ
      · by_cases ht : threshold < average y ω
        · simp [hs, ht]
          have hp := pow_le_pow_left₀ (le_of_lt hthreshold) (le_of_lt ht) n
          calc
            threshold ^ n * P.w ω ≤ (average y ω) ^ n * P.w ω :=
              mul_le_mul_of_nonneg_right hp (P.nonneg ω)
            _ = P.w ω * (average y ω) ^ n := by ring
        · simp [hs, ht]
          exact mul_nonneg (P.nonneg ω) (pow_nonneg (havgNonneg y ω) n)
      · simp [hs]
    have hscaled := hmarkov.trans (hmomentCap y)
    have hpowpos : 0 < threshold ^ n := pow_pos hthreshold n
    calc
      (∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0) =
          (threshold ^ n)⁻¹ *
            (threshold ^ n *
              (∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0)) := by
        field_simp [ne_of_gt hpowpos]
      _ ≤ (threshold ^ n)⁻¹ * (K ^ n * (D₀ + 1) ^ n) :=
        mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hpowpos.le)
      _ = (1 / 4 : ℝ) ^ n := by
        rw [hthresholdPow]
        field_simp [hKne, hDne]
        have hfour : ((1 : ℝ) / 4) ^ n * (4 : ℝ) ^ n = 1 := by
          rw [div_pow, one_pow]
          exact div_mul_cancel₀ 1 (pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0))
        calc
          1 = ((1 : ℝ) / 4) ^ n * (4 : ℝ) ^ n := hfour.symm
          _ = (4 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n := by ring
  have hunion :
      (∑ ω, if ω ∈ succ ∧ ∃ y, threshold < average y ω then P.w ω else 0) ≤
        ∑ y, ∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0 := by
    calc
      (∑ ω, if ω ∈ succ ∧ ∃ y, threshold < average y ω then P.w ω else 0) ≤
          ∑ ω, ∑ y, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0 := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hs : ω ∈ succ
        · by_cases he : ∃ y, threshold < average y ω
          · obtain ⟨y, hy⟩ := he
            have hExists : ∃ y, threshold < average y ω := ⟨y, hy⟩
            let g : Label → ℝ := fun y' =>
              if threshold < average y' ω then P.w ω else 0
            have hsum : P.w ω ≤ ∑ y', g y' := by
              calc
                P.w ω = g y := by simp [g, hy]
                _ ≤ ∑ y', g y' :=
                  Finset.single_le_sum
                    (fun y' hy' => by
                      by_cases hcond : threshold < average y' ω
                      · simp [g, hcond, P.nonneg ω]
                      · simp [g, hcond])
                    (Finset.mem_univ y)
            simpa [hs, hExists, g] using hsum
          · have hno : ∀ y, ¬ threshold < average y ω := by
              intro y hy
              exact he ⟨y, hy⟩
            simp [hs, hno]
        · simp [hs]
      _ = ∑ y, ∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0 :=
        Finset.sum_comm
  change (∑ ω, if ω ∈ succ ∧ ∃ y, threshold < average y ω then P.w ω else 0) ≤ _
  calc
    (∑ ω, if ω ∈ succ ∧ ∃ y, threshold < average y ω then P.w ω else 0) ≤
        ∑ y, ∑ ω, if ω ∈ succ ∧ threshold < average y ω then P.w ω else 0 := hunion
    _ ≤ ∑ _y : Label, (1 / 4 : ℝ) ^ n :=
      Finset.sum_le_sum fun y hy => htail y
    _ = (Fintype.card Label : ℝ) * (1 / 4 : ℝ) ^ n := by simp
    _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hlabels (by positivity)

end HypercubeRamsey
