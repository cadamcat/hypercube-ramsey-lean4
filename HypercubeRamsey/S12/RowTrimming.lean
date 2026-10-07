import HypercubeRamsey.S12.InteractionTails
import HypercubeRamsey.S12.RowTrimming_q_s12_peel
import HypercubeRamsey.Framework.LawLemmas

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
  classical
  have hα : 0 < κ.α := hκ.α_rng.1
  have hξ : 0 < κ.ξ := hκ.ξ_rng.1
  have hξsmall : 600 * κ.ξ ≤ κ.α / 6 := by
    have huU : 0 ≤ (κ.u : ℝ) := Nat.cast_nonneg _
    have hu0 : (20 : ℝ) ≤ 10 * (κ.u : ℝ) + 100 := by nlinarith
    have hu : (-(10 * (κ.u : ℝ) + 100)) ≤ -20 := by linarith
    have hbase := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hu
    have hnum : 600 * Real.rpow 2 (-20 : ℝ) ≤ (1 : ℝ) / 6 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    have hξ' := mul_le_mul_of_nonneg_left (le_of_lt hκ.ξ_rng.2)
      (by norm_num : (0 : ℝ) ≤ 600)
    calc
      600 * κ.ξ ≤ 600 * (κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100))) := hξ'
      _ = κ.α * (600 * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100))) := by ring
      _ ≤ κ.α * (600 * Real.rpow 2 (-20 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase (by norm_num)) hα.le
      _ ≤ κ.α * (1 / 6) := mul_le_mul_of_nonneg_left hnum hα.le
      _ = κ.α / 6 := by ring
  have hn : Filter.Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hpow_gt : ∀ (r : ℝ), 0 < r → ∀ B : ℝ,
      ∀ᶠ k in atTop, B < (T.S.n k : ℝ) ^ r := by
    intro r hr B
    exact ((tendsto_rpow_atTop hr).comp hn).eventually (eventually_gt_atTop B)
  have hpow01 := hpow_gt 0.1 (by norm_num) 10
  have hpow02 := hpow_gt 0.02 (by norm_num) (100 * (3 : ℝ) ^ κ.u)
  have hpow034 := hpow_gt 0.34 (by norm_num) 300
  have hpow06 := hpow_gt 0.6 (by norm_num) (3 / κ.α)
  have hn1 : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hscale : ∀ᶠ k in atTop,
      100 * (3 : ℝ) ^ κ.u * bstar T k < (T.S.n k : ℝ) ^ (-0.94 : ℝ) := by
    filter_upwards [hn1, hpow02] with k hk hA
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    have hbstar : bstar T k = (T.S.n k : ℝ) ^ (-0.96 : ℝ) := by
      simp [bstar]
      norm_num
    have hfactor : (T.S.n k : ℝ) ^ (-0.94 : ℝ) =
        (T.S.n k : ℝ) ^ (-0.96 : ℝ) * (T.S.n k : ℝ) ^ (0.02 : ℝ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num
    calc
      100 * (3 : ℝ) ^ κ.u * bstar T k =
          100 * (3 : ℝ) ^ κ.u * (T.S.n k : ℝ) ^ (-0.96 : ℝ) := by rw [hbstar]
      _ < (T.S.n k : ℝ) ^ (0.02 : ℝ) * (T.S.n k : ℝ) ^ (-0.96 : ℝ) :=
        mul_lt_mul_of_pos_right hA (Real.rpow_pos_of_pos hnpos _)
      _ = (T.S.n k : ℝ) ^ (-0.94 : ℝ) := by rw [mul_comm, hfactor]
  have hlowExp : ∀ᶠ k in atTop,
      150 * (T.S.n k : ℝ) ^ (0.06 : ℝ) - (T.S.n k : ℝ) ^ (0.4 : ℝ) ≤
        -(1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
    filter_upwards [hn1, hpow034] with k hk h34
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    have hfactor : (T.S.n k : ℝ) ^ (0.4 : ℝ) =
        (T.S.n k : ℝ) ^ (0.06 : ℝ) * (T.S.n k : ℝ) ^ (0.34 : ℝ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num
    have hprod : 300 * (T.S.n k : ℝ) ^ (0.06 : ℝ) ≤
        (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
      rw [hfactor]
      calc
        300 * (T.S.n k : ℝ) ^ (0.06 : ℝ) =
            (T.S.n k : ℝ) ^ (0.06 : ℝ) * 300 := by ring
        _ ≤ (T.S.n k : ℝ) ^ (0.06 : ℝ) * (T.S.n k : ℝ) ^ (0.34 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt h34)
            (show 0 ≤ (T.S.n k : ℝ) ^ (0.06 : ℝ) by positivity)
    linarith
  have hhighExp : ∀ᶠ k in atTop,
      -(κ.α * (T.S.n k : ℝ) / 6) ≤
        -(1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
    filter_upwards [hn1, hpow06] with k hk h06
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    have hfactor : (T.S.n k : ℝ) =
        (T.S.n k : ℝ) ^ (0.4 : ℝ) * (T.S.n k : ℝ) ^ (0.6 : ℝ) := by
      calc
        (T.S.n k : ℝ) = (T.S.n k : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (T.S.n k : ℝ) ^ ((0.4 : ℝ) + (0.6 : ℝ)) := by congr 1 <;> norm_num
        _ = _ := by rw [← Real.rpow_add hnpos]
    have hprod : κ.α * (T.S.n k : ℝ) / 6 ≥
        (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt h06)
        (show 0 ≤ κ.α / 6 * (T.S.n k : ℝ) ^ (0.4 : ℝ) by positivity)
      have hcancel : κ.α / 6 * (T.S.n k : ℝ) ^ (0.4 : ℝ) * (3 / κ.α) =
          (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
        field_simp [ne_of_gt hα]
        ring
      calc
        κ.α * (T.S.n k : ℝ) / 6 = κ.α / 6 * (T.S.n k : ℝ) := by ring
        _ = κ.α / 6 * ((T.S.n k : ℝ) ^ (0.4 : ℝ) * (T.S.n k : ℝ) ^ (0.6 : ℝ)) :=
          congrArg (fun v : ℝ => κ.α / 6 * v) hfactor
        _ ≥ κ.α / 6 * (T.S.n k : ℝ) ^ (0.4 : ℝ) * (3 / κ.α) := by
          simpa [mul_assoc] using hmul
        _ = _ := hcancel
    linarith
  have hremoveExp : ∀ᶠ k in atTop,
      3 * Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ) +
          (T.S.n k : ℝ) ^ (0.2 : ℝ) -
            (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ)) ≤
        Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) := by
    filter_upwards [hn1, hpow01] with k hk h01
    have hnpos : 0 < (T.S.n k : ℝ) := by linarith
    have h21 : (10 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) ≤
        (T.S.n k : ℝ) ^ (0.2 : ℝ) := by
      have hfactor : (T.S.n k : ℝ) ^ (0.2 : ℝ) =
          (T.S.n k : ℝ) ^ (0.1 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        norm_num
      rw [hfactor]
      calc
        10 * (T.S.n k : ℝ) ^ (0.1 : ℝ) = (T.S.n k : ℝ) ^ (0.1 : ℝ) * 10 := by ring
        _ ≤ (T.S.n k : ℝ) ^ (0.1 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt h01)
            (show 0 ≤ (T.S.n k : ℝ) ^ (0.1 : ℝ) by positivity)
    have h32 : (10 : ℝ) * (T.S.n k : ℝ) ^ (0.2 : ℝ) ≤
        (T.S.n k : ℝ) ^ (0.3 : ℝ) := by
      have hfactor : (T.S.n k : ℝ) ^ (0.3 : ℝ) =
          (T.S.n k : ℝ) ^ (0.2 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        norm_num
      rw [hfactor]
      calc
        10 * (T.S.n k : ℝ) ^ (0.2 : ℝ) = (T.S.n k : ℝ) ^ (0.2 : ℝ) * 10 := by ring
        _ ≤ (T.S.n k : ℝ) ^ (0.2 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt h01)
            (show 0 ≤ (T.S.n k : ℝ) ^ (0.2 : ℝ) by positivity)
    have h43 : (10 : ℝ) * (T.S.n k : ℝ) ^ (0.3 : ℝ) ≤
        (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
      have hfactor : (T.S.n k : ℝ) ^ (0.4 : ℝ) =
          (T.S.n k : ℝ) ^ (0.3 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        norm_num
      rw [hfactor]
      calc
        10 * (T.S.n k : ℝ) ^ (0.3 : ℝ) = (T.S.n k : ℝ) ^ (0.3 : ℝ) * 10 := by ring
        _ ≤ (T.S.n k : ℝ) ^ (0.3 : ℝ) * (T.S.n k : ℝ) ^ (0.1 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt h01)
            (show 0 ≤ (T.S.n k : ℝ) ^ (0.3 : ℝ) by positivity)
    have hmargin : 3 + (T.S.n k : ℝ) ^ (0.1 : ℝ) +
        (T.S.n k : ℝ) ^ (0.2 : ℝ) + (T.S.n k : ℝ) ^ (0.3 : ℝ) ≤
          (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ) := by
      nlinarith
    have h3exp : (3 : ℝ) ≤ Real.exp 3 := by
      have h := Real.add_one_le_exp 3
      linarith
    calc
      3 * Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ) +
          (T.S.n k : ℝ) ^ (0.2 : ℝ) -
            (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ)) ≤
          Real.exp 3 * Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ) +
            (T.S.n k : ℝ) ^ (0.2 : ℝ) -
              (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ)) :=
        mul_le_mul_of_nonneg_right h3exp (Real.exp_nonneg _)
      _ = Real.exp (3 + (T.S.n k : ℝ) ^ (0.1 : ℝ) +
          (T.S.n k : ℝ) ^ (0.2 : ℝ) -
            (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
  have hTwo := corr_tail_two κ hκ T hDeep c κ.u 1 (by norm_num)
  have hOne := corr_tail_one κ hκ T hDeep c κ.u 1 (by norm_num)
  filter_upwards [hn1, hpow01, hscale, hlowExp, hhighExp, hremoveExp, hTwo, hOne] with
      k hk h01global hscale hlowExp hhighExp hremoveExp hTwo hOne
  intro X₀ hX₀ hX₀sub hlog ι 𝒥 π hπsup hπwidth h𝒥
  let n : ℝ := T.S.n k
  let m : ℝ := X₀.card
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Finset.card_pos.mpr hX₀
  have hN : 0 < T.S.N k := by
    obtain ⟨x, hx⟩ := hX₀
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at x
    exact Fin.elim0 x
  have hτwidth0 : (Law.unif X₀ hX₀).WidthLE
      (Real.log ((T.S.N k : ℝ) / (X₀.card : ℝ))) :=
    Law.uniform_width X₀ hX₀
  have hτwidth : (Law.unif X₀ hX₀).WidthLE (n ^ (κ.xs / 4 : ℝ)) := by
    exact Law.WidthLE.mono hτwidth0 (by simpa [n] using hlog)
  have hτsupp : (Law.unif X₀ hX₀).SupportedIn (T.X k) := by
    intro x hx
    have hx0 : x ∉ X₀ := fun hx0 => hx (hX₀sub hx0)
    simp [Law.unif, FinProb.uniform, hx0]
  let S : ι → InterSetting T k (κ.xs / 4) := fun j =>
    { d := 1
      d_le := by exact_mod_cast hk
      τ := Law.unif X₀ hX₀
      π := fun _ => π j
      τ_supp := hτsupp
      π_supp := by intro l; exact hπsup j
      τ_width := by simpa [n] using hτwidth
      π_width := by intro l; exact hπwidth j }
  have hl0 (j : ι) : Fin (S j).d := ⟨0, by simp [S]⟩
  let pairBad (j : ι) (x z : Fin (T.S.N k)) : Prop :=
    n ^ (-1.03 : ℝ) < |corr (T.S.E k) c (π j).w x z|
  let pairHigh (j : ι) (x z : Fin (T.S.N k)) : Prop :=
    n ^ (-0.94 : ℝ) < |corr (T.S.E k) c (π j).w x z| ∧
      |corr (T.S.E k) c (π j).w x z| ≤ 4 * κ.ξ
  let pairAll (j : ι) (x z : Fin (T.S.N k)) : Prop :=
    pairBad j x z ∧ |corr (T.S.E k) c (π j).w x z| ≤ 4 * κ.ξ
  let pairLow (j : ι) (x z : Fin (T.S.N k)) : Prop :=
    pairAll j x z ∧ |corr (T.S.E k) c (π j).w x z| ≤ n ^ (-0.94 : ℝ)
  let pairMid (j : ι) (x z : Fin (T.S.N k)) : Prop :=
    pairAll j x z ∧ n ^ (-0.94 : ℝ) < |corr (T.S.E k) c (π j).w x z|
  let pairWeight (j : ι) (x z : Fin (T.S.N k)) : ℝ :=
    Real.exp (150 * n * |corr (T.S.E k) c (π j).w x z|)
  let rowCount (j : ι) (x : Fin (T.S.N k)) : ℝ :=
    ((X₀.filter fun z => pairBad j x z).card : ℝ)
  let rowWeight (j : ι) (x : Fin (T.S.N k)) : ℝ :=
    ∑ z ∈ X₀.filter (fun z => pairAll j x z), pairWeight j x z
  have hpairProb (j : ι) :
      (∑ x, ∑ z, if pairBad j x z then
        (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) ≤
          Real.exp (-(n ^ (0.4 : ℝ))) := by
    simpa [S, n, pairBad] using hTwo (S j) (hl0 j)
  have hpairCount (j : ι) :
      (∑ x ∈ X₀, ∑ z ∈ X₀, if pairBad j x z then (1 : ℝ) else 0) ≤
        Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2 := by
    have heq := uniform_pair_sum X₀ hX₀ (pairBad j) (fun _ _ => (1 : ℝ))
    have heq' :
        (∑ x ∈ X₀, ∑ z ∈ X₀, if pairBad j x z then (1 : ℝ) else 0) =
          m ^ 2 * (∑ x, ∑ z, if pairBad j x z then
            (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) := by
      simpa [m, pairBad] using heq
    calc
      _ = m ^ 2 * (∑ x, ∑ z, if pairBad j x z then
            (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) := heq'
      _ ≤ m ^ 2 * Real.exp (-(n ^ (0.4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hpairProb j) (by positivity)
      _ = Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2 := by ring
  have hhighMass (j : ι) (x : Fin (T.S.N k)) :
      (∑ z, if pairHigh j x z then (Law.unif X₀ hX₀).w z else 0) ≤
        Real.exp (-(κ.α * n / 3)) := by
    have hsub : (Finset.univ.filter fun z => pairHigh j x z) ⊆
        Finset.univ.filter (fun z =>
          100 * (3 : ℝ) ^ κ.u * bstar T k <
            |corr (T.S.E k) c ((S j).π (hl0 j)).w x z|) := by
      intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      rcases hz with ⟨_, hzlarge, _⟩
      exact ⟨Finset.mem_univ _, lt_trans hscale hzlarge⟩
    have hone := hOne (S j) (hl0 j) x
    calc
      (∑ z, if pairHigh j x z then (Law.unif X₀ hX₀).w z else 0) =
          ∑ z ∈ Finset.univ.filter (fun z => pairHigh j x z),
            (Law.unif X₀ hX₀).w z := by simp [Finset.sum_filter]
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z =>
          100 * (3 : ℝ) ^ κ.u * bstar T k <
              |corr (T.S.E k) c ((S j).π (hl0 j)).w x z|), (Law.unif X₀ hX₀).w z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro z hz hznot
        exact (Law.unif X₀ hX₀).nonneg z
      _ ≤ Real.exp (-(κ.α * n / 3)) := by
        simpa [S, n] using hone
  have hhighProb (j : ι) :
      (∑ x, ∑ z, if pairHigh j x z then
        (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) ≤
          Real.exp (-(κ.α * n / 3)) := by
    calc
      (∑ x, ∑ z, if pairHigh j x z then
          (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) =
        ∑ x, (Law.unif X₀ hX₀).w x *
          (∑ z, if pairHigh j x z then (Law.unif X₀ hX₀).w z else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          (∑ z, if pairHigh j x z then
              (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) =
              ∑ z, (Law.unif X₀ hX₀).w x *
                (if pairHigh j x z then (Law.unif X₀ hX₀).w z else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hp : pairHigh j x z <;> simp [hp]
          _ = (Law.unif X₀ hX₀).w x *
              (∑ z, if pairHigh j x z then (Law.unif X₀ hX₀).w z else 0) := by
            rw [← Finset.mul_sum]
      _ ≤ ∑ x, (Law.unif X₀ hX₀).w x * Real.exp (-(κ.α * n / 3)) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hhighMass j x)
          ((Law.unif X₀ hX₀).nonneg x)
      _ = Real.exp (-(κ.α * n / 3)) := by
        rw [← Finset.sum_mul]
        simp [(Law.unif X₀ hX₀).sum_eq_one]
  have hratioLow : n * n ^ (-0.94 : ℝ) = n ^ (0.06 : ℝ) := by
    have hnpos : 0 < n := by dsimp [n]; exact_mod_cast hk
    calc
      n * n ^ (-0.94 : ℝ) = n ^ (1 : ℝ) * n ^ (-0.94 : ℝ) := by rw [Real.rpow_one]
      _ = n ^ ((1 : ℝ) + (-0.94 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = n ^ (0.06 : ℝ) := by congr 1 <;> norm_num
  have hlowWeightPoint (j : ι) (x z : Fin (T.S.N k))
      (hp : pairLow j x z) : pairWeight j x z ≤ Real.exp (150 * n ^ (0.06 : ℝ)) := by
    have habs := hp.2
    have hnnonneg : 0 ≤ n := by positivity
    have hexp : 150 * n * |corr (T.S.E k) c (π j).w x z| ≤ 150 * n ^ (0.06 : ℝ) := by
      calc
        150 * n * |corr (T.S.E k) c (π j).w x z| ≤ 150 * n * n ^ (-0.94 : ℝ) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
        _ = 150 * n ^ (0.06 : ℝ) := by
          calc
            150 * n * n ^ (-0.94 : ℝ) = 150 * (n * n ^ (-0.94 : ℝ)) := by ring
            _ = _ := by rw [hratioLow]
    exact Real.exp_le_exp.mpr hexp
  have hhighWeightPoint (j : ι) (x z : Fin (T.S.N k))
      (hp : pairHigh j x z) : pairWeight j x z ≤ Real.exp (600 * κ.ξ * n) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hp.2
      (show 0 ≤ 150 * n by positivity)
    nlinarith [hmul]
  have hpairHighCount (j : ι) :
      (∑ x ∈ X₀, ∑ z ∈ X₀, if pairHigh j x z then (1 : ℝ) else 0) ≤
        Real.exp (-(κ.α * n / 3)) * m ^ 2 := by
    have heq := uniform_pair_sum X₀ hX₀ (pairHigh j) (fun _ _ => (1 : ℝ))
    have heq' :
        (∑ x ∈ X₀, ∑ z ∈ X₀, if pairHigh j x z then (1 : ℝ) else 0) =
          m ^ 2 * (∑ x, ∑ z, if pairHigh j x z then
            (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) := by
      simpa [m, pairHigh] using heq
    calc
      _ = m ^ 2 * (∑ x, ∑ z, if pairHigh j x z then
            (Law.unif X₀ hX₀).w x * (Law.unif X₀ hX₀).w z else 0) := heq'
      _ ≤ m ^ 2 * Real.exp (-(κ.α * n / 3)) :=
        mul_le_mul_of_nonneg_left (hhighProb j) (by positivity)
      _ = Real.exp (-(κ.α * n / 3)) * m ^ 2 := by ring
  have hpairLowWeight (j : ι) :
      (∑ x ∈ X₀, ∑ z ∈ X₀,
        if pairLow j x z then pairWeight j x z else 0) ≤
          Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by
    have hterm : ∀ x ∈ X₀, ∀ z ∈ X₀,
        (if pairLow j x z then pairWeight j x z else 0) ≤
          Real.exp (150 * n ^ (0.06 : ℝ)) * (if pairBad j x z then (1 : ℝ) else 0) := by
      intro x hx z hz
      by_cases hp : pairLow j x z
      · have hb : pairBad j x z := hp.1.1
        simp [hp, hb]
        exact hlowWeightPoint j x z hp
      · simp [hp]
        positivity
    calc
      (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairLow j x z then pairWeight j x z else 0) ≤
        ∑ x ∈ X₀, ∑ z ∈ X₀,
          Real.exp (150 * n ^ (0.06 : ℝ)) *
            (if pairBad j x z then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro z hz
          exact hterm x hx z hz
      _ = Real.exp (150 * n ^ (0.06 : ℝ)) *
          (∑ x ∈ X₀, ∑ z ∈ X₀,
            if pairBad j x z then (1 : ℝ) else 0) := by
          calc
            _ = ∑ x ∈ X₀, Real.exp (150 * n ^ (0.06 : ℝ)) *
                (∑ z ∈ X₀, if pairBad j x z then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
      _ ≤ Real.exp (150 * n ^ (0.06 : ℝ)) *
          (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) :=
          mul_le_mul_of_nonneg_left (hpairCount j) (Real.exp_nonneg _)
      _ ≤ Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by
          have hexp : Real.exp (150 * n ^ (0.06 : ℝ)) *
              Real.exp (-(n ^ (0.4 : ℝ))) ≤
                Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) := by
            calc
              Real.exp (150 * n ^ (0.06 : ℝ)) * Real.exp (-(n ^ (0.4 : ℝ))) =
                  Real.exp (150 * n ^ (0.06 : ℝ) - n ^ (0.4 : ℝ)) := by
                    rw [← Real.exp_add]
                    congr 1 <;> ring
              _ ≤ _ := Real.exp_le_exp.mpr (by simpa [n] using hlowExp)
          calc
            Real.exp (150 * n ^ (0.06 : ℝ)) *
                (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) =
              (Real.exp (150 * n ^ (0.06 : ℝ)) *
                Real.exp (-(n ^ (0.4 : ℝ)))) * m ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have hpairMidWeight (j : ι) :
      (∑ x ∈ X₀, ∑ z ∈ X₀,
        if pairMid j x z then pairWeight j x z else 0) ≤
          Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by
    have hterm : ∀ x ∈ X₀, ∀ z ∈ X₀,
        (if pairMid j x z then pairWeight j x z else 0) ≤
          Real.exp (600 * κ.ξ * n) * (if pairHigh j x z then (1 : ℝ) else 0) := by
      intro x hx z hz
      by_cases hp : pairMid j x z
      · have hh : pairHigh j x z := ⟨hp.2, hp.1.2⟩
        simp [hp, hh]
        exact hhighWeightPoint j x z hh
      · simp [hp]
        positivity
    calc
      (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairMid j x z then pairWeight j x z else 0) ≤
        ∑ x ∈ X₀, ∑ z ∈ X₀,
          Real.exp (600 * κ.ξ * n) *
            (if pairHigh j x z then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro z hz
          exact hterm x hx z hz
      _ = Real.exp (600 * κ.ξ * n) *
          (∑ x ∈ X₀, ∑ z ∈ X₀,
            if pairHigh j x z then (1 : ℝ) else 0) := by
          calc
            _ = ∑ x ∈ X₀, Real.exp (600 * κ.ξ * n) *
                (∑ z ∈ X₀, if pairHigh j x z then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
      _ ≤ Real.exp (600 * κ.ξ * n) *
          (Real.exp (-(κ.α * n / 3)) * m ^ 2) :=
          mul_le_mul_of_nonneg_left (hpairHighCount j) (Real.exp_nonneg _)
      _ ≤ Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by
          have hcoef : 600 * κ.ξ * n - κ.α * n / 3 ≤ -(κ.α * n / 6) := by
            nlinarith [hξsmall, (show 0 ≤ n by positivity)]
          have hexp : Real.exp (600 * κ.ξ * n) *
              Real.exp (-(κ.α * n / 3)) ≤
                Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) := by
            calc
              Real.exp (600 * κ.ξ * n) * Real.exp (-(κ.α * n / 3)) =
                  Real.exp (600 * κ.ξ * n - κ.α * n / 3) := by
                    rw [← Real.exp_add]
                    congr 1 <;> ring
              _ ≤ _ := Real.exp_le_exp.mpr (by simpa [n] using le_trans hcoef hhighExp)
          calc
            Real.exp (600 * κ.ξ * n) *
                (Real.exp (-(κ.α * n / 3)) * m ^ 2) =
              (Real.exp (600 * κ.ξ * n) * Real.exp (-(κ.α * n / 3))) * m ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have hrowCountSum (j : ι) :
      (∑ x ∈ X₀, rowCount j x) ≤ Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2 := by
    have heq : (∑ x ∈ X₀, rowCount j x) =
        ∑ x ∈ X₀, ∑ z ∈ X₀, if pairBad j x z then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        rowCount j x = ∑ z ∈ X₀.filter (fun z => pairBad j x z), (1 : ℝ) := by
          simp [rowCount]
        _ = ∑ z ∈ X₀, if pairBad j x z then (1 : ℝ) else 0 := by
          simp [Finset.sum_filter]
    rw [heq]
    exact hpairCount j
  have hrowWeightSum (j : ι) :
      (∑ x ∈ X₀, rowWeight j x) ≤
        2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by
    have heq : (∑ x ∈ X₀, rowWeight j x) =
        ∑ x ∈ X₀, ∑ z ∈ X₀, if pairAll j x z then pairWeight j x z else 0 := by
      simp [rowWeight, Finset.sum_filter]
    have hsplitPoint (x z : Fin (T.S.N k)) :
        (if pairAll j x z then pairWeight j x z else 0) =
          (if pairLow j x z then pairWeight j x z else 0) +
            (if pairMid j x z then pairWeight j x z else 0) := by
      by_cases hP : pairAll j x z
      · by_cases hcut : n ^ (-0.94 : ℝ) < |corr (T.S.E k) c (π j).w x z|
        · have hnotle : ¬ |corr (T.S.E k) c (π j).w x z| ≤ n ^ (-0.94 : ℝ) :=
            not_le_of_gt hcut
          simp [pairLow, pairMid, hP, hcut, hnotle]
        · have hle : |corr (T.S.E k) c (π j).w x z| ≤ n ^ (-0.94 : ℝ) :=
            le_of_not_gt hcut
          simp [pairLow, pairMid, hP, hcut, hle]
      · simp [pairLow, pairMid, hP]
    have hsplitInner (x : Fin (T.S.N k)) :
        (∑ z ∈ X₀, if pairAll j x z then pairWeight j x z else 0) =
          (∑ z ∈ X₀, if pairLow j x z then pairWeight j x z else 0) +
            (∑ z ∈ X₀, if pairMid j x z then pairWeight j x z else 0) := by
      calc
        (∑ z ∈ X₀, if pairAll j x z then pairWeight j x z else 0) =
            ∑ z ∈ X₀,
              ((if pairLow j x z then pairWeight j x z else 0) +
                (if pairMid j x z then pairWeight j x z else 0)) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hsplitPoint x z
        _ = _ := by rw [Finset.sum_add_distrib]
    have hsplit :
        (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairAll j x z then pairWeight j x z else 0) =
        (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairLow j x z then pairWeight j x z else 0) +
        (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairMid j x z then pairWeight j x z else 0) := by
      calc
        (∑ x ∈ X₀, ∑ z ∈ X₀,
          if pairAll j x z then pairWeight j x z else 0) =
            ∑ x ∈ X₀,
              ((∑ z ∈ X₀, if pairLow j x z then pairWeight j x z else 0) +
                (∑ z ∈ X₀, if pairMid j x z then pairWeight j x z else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hsplitInner x
        _ = (∑ x ∈ X₀, ∑ z ∈ X₀,
              if pairLow j x z then pairWeight j x z else 0) +
            (∑ x ∈ X₀, ∑ z ∈ X₀,
              if pairMid j x z then pairWeight j x z else 0) := by
          simp_rw [Finset.sum_add_distrib]
    rw [heq, hsplit]
    calc
      _ ≤ Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 +
          Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 :=
        add_le_add (hpairLowWeight j) (hpairMidWeight j)
      _ = 2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2 := by ring
  let δ := Real.exp (-(n ^ (0.2 : ℝ))) * m
  have hδ : 0 < δ := mul_pos (Real.exp_pos _) hm
  have hcountRatio :
      (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) / δ =
        Real.exp (-(n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
    dsimp [δ]
    have hmne : m ≠ 0 := ne_of_gt hm
    have hene : Real.exp (-(n ^ (0.2 : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
    calc
      (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) /
          (Real.exp (-(n ^ (0.2 : ℝ))) * m) =
          (Real.exp (-(n ^ (0.4 : ℝ))) /
            Real.exp (-(n ^ (0.2 : ℝ)))) * m := by
        field_simp [hmne, hene] <;> ring
      _ = Real.exp (-(n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
        rw [← Real.exp_sub]
        congr 1 <;> ring
  have hweightRatio :
      (2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2) / δ =
        2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
    dsimp [δ]
    have hmne : m ≠ 0 := ne_of_gt hm
    have hene : Real.exp (-(n ^ (0.2 : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
    calc
      (2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2) /
          (Real.exp (-(n ^ (0.2 : ℝ))) * m) =
          2 * (Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) /
            Real.exp (-(n ^ (0.2 : ℝ)))) * m := by
        field_simp [hmne, hene] <;> ring
      _ = 2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
        rw [← Real.exp_sub]
        congr 2 <;> ring
  have hbadCount (j : ι) :
      ((X₀.filter fun x => δ < rowCount j x).card : ℝ) ≤
        Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
    calc
      ((X₀.filter fun x => δ < rowCount j x).card : ℝ) ≤
          (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) / δ :=
        filter_card_le_of_sum_bound X₀ (rowCount j) δ
          (Real.exp (-(n ^ (0.4 : ℝ))) * m ^ 2) hδ
          (by intro x hx; positivity) (hrowCountSum j)
      _ = Real.exp (-(n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := hcountRatio
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hm.le
        exact Real.exp_le_exp.mpr (by
          have hn4 : 0 ≤ n ^ (0.4 : ℝ) := by positivity
          nlinarith)
  have hbadWeight (j : ι) :
      ((X₀.filter fun x => δ < rowWeight j x).card : ℝ) ≤
        2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
    calc
      ((X₀.filter fun x => δ < rowWeight j x).card : ℝ) ≤
          (2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2) / δ :=
        filter_card_le_of_sum_bound X₀ (rowWeight j) δ
          (2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) * m ^ 2) hδ
          (by intro x hx; positivity) (hrowWeightSum j)
      _ = 2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m :=
        hweightRatio
  let badFor (j : ι) := X₀.filter fun x =>
    δ < rowCount j x ∨ δ < rowWeight j x
  have hbadFor (j : ι) : ((badFor j).card : ℝ) ≤
      3 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
    have hcard : (badFor j).card ≤
        (X₀.filter fun x => δ < rowCount j x).card +
          (X₀.filter fun x => δ < rowWeight j x).card := by
      dsimp [badFor]
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    have hcard' : ((badFor j).card : ℝ) ≤
        ((X₀.filter fun x => δ < rowCount j x).card : ℝ) +
          ((X₀.filter fun x => δ < rowWeight j x).card : ℝ) := by exact_mod_cast hcard
    calc
      ((badFor j).card : ℝ) ≤ _ := hcard'
      _ ≤ Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m +
          2 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m :=
        add_le_add (hbadCount j) (hbadWeight j)
      _ = 3 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by ring
  let bad := 𝒥.biUnion badFor
  have hbadSubset : bad ⊆ X₀ := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    exact (Finset.mem_filter.mp hxj).1
  have hbadCard : (bad.card : ℝ) ≤ Real.exp (-(n ^ (0.3 : ℝ))) * m := by
    have hbiNat : bad.card ≤ ∑ j ∈ 𝒥, (badFor j).card :=
      Finset.card_biUnion_le (s := 𝒥) (t := badFor)
    have hbi : (bad.card : ℝ) ≤ ∑ j ∈ 𝒥, ((badFor j).card : ℝ) := by
      exact_mod_cast hbiNat
    calc
      (bad.card : ℝ) ≤ ∑ j ∈ 𝒥, ((badFor j).card : ℝ) := hbi
      _ ≤ ∑ j ∈ 𝒥,
          3 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbadFor j
      _ = (𝒥.card : ℝ) *
          (3 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m) := by simp
      _ ≤ Real.exp (n ^ (0.1 : ℝ)) *
          (3 * Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ)) * m) :=
        mul_le_mul_of_nonneg_right h𝒥 (by positivity)
      _ = 3 * (Real.exp (n ^ (0.1 : ℝ)) *
          Real.exp (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ))) * m := by ring
      _ = 3 * Real.exp (n ^ (0.1 : ℝ) +
          (-((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) + n ^ (0.2 : ℝ))) * m := by
        rw [← Real.exp_add]
      _ = 3 * Real.exp (n ^ (0.1 : ℝ) + n ^ (0.2 : ℝ) -
          (1 / 2 : ℝ) * n ^ (0.4 : ℝ)) * m := by congr 2 <;> ring
      _ ≤ Real.exp (-(n ^ (0.3 : ℝ))) * m :=
        mul_le_mul_of_nonneg_right hremoveExp (by positivity)
  let X₁ : Finset (Fin (T.S.N k)) := X₀ \ bad
  have hX₁ : X₁ ⊆ X₀ := Finset.sdiff_subset
  have hremoved : X₀ \ X₁ = bad := by
    ext x
    by_cases hx : x ∈ X₀
    · simp [X₁, hx]
    · have hxb : x ∉ bad := fun h => hx (hbadSubset h)
      simp [X₁, hx, hxb]
  refine ⟨X₁, hX₁, ?_, ?_⟩
  · simpa [hremoved, m, n] using hbadCard
  · intro j hj x hx
    have hx0 : x ∈ X₀ := hX₁ hx
    have hxnot : x ∉ bad := (Finset.mem_sdiff.mp hx).2
    have hxnotj : x ∉ badFor j := by
      intro hmem
      exact hxnot (Finset.mem_biUnion.mpr ⟨j, hj, hmem⟩)
    have hgood : ¬ (δ < rowCount j x ∨ δ < rowWeight j x) := by
      intro h
      exact hxnotj (Finset.mem_filter.mpr ⟨hx0, h⟩)
    constructor
    · have hc := le_of_not_gt (fun h => hgood (Or.inl h))
      simpa [rowCount, pairBad, n, m, δ] using hc
    · have hw := le_of_not_gt (fun h => hgood (Or.inr h))
      simpa [rowWeight, pairAll, pairBad, pairWeight, n, m, δ] using hw

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
