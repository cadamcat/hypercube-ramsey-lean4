import HypercubeRamsey.S13.ResidualBounds_q_s13_resid_cluster
import HypercubeRamsey.S13.ResidualBounds_q_s13_resid_finite

namespace HypercubeRamsey.Lane_q_s13_resid_step

open HypercubeRamsey
open Filter
open Classical
open scoped BigOperators

theorem eventual_scale_step
    (κ : CConsts) (hκ : CConsts.Admissible κ) (T : Stage)
    (hClu : HypercubeRamsey.Lane_q_s13_resid_finite.ClusterAbsenceInputAux κ T)
    (hClean : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o →
          HypercubeRamsey.Lane_q_s13_resid.CleanClusterBinsAux κ T k RX RY b o)
    (hCodegree : ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (c : Colour)
      (μ : Law N) (y y' : Fin N),
      (∑ x : Fin N, μ.w x * hit E c x y * hit E c x y') =
        (1 + (if c then 1 else -1) * (2 * colDeg E true μ y - 1) +
          (if c then 1 else -1) * (2 * colDeg E true μ y' - 1) +
          pairCorr E false μ y y') / 4)
    (β q ζ δ : ℚ)
    (hβ : 0 < β) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδAbs : (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000)
    (hβα : (β : ℝ) * κ.aC < δ) (hζq : ζ < q)
    (hprior : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → (b : ℝ) < (T.S.n k : ℝ) ^ (β : ℝ)) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → (b : ℝ) < (T.S.n k : ℝ) ^ (q : ℝ) := by
  have hNoFalse := hClu ζ δ hζ hδ hδAbs true false
  have hNoTrue := hClu ζ δ hζ hδ hδAbs true true
  have hζR : 0 < (ζ : ℝ) := by exact_mod_cast hζ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hGap1Pos : 0 < (δ : ℝ) - (β : ℝ) * κ.aC := sub_pos.mpr hβα
  have hGap1 : ∀ᶠ k in atTop,
      1 + Real.log 4 ≤ (T.S.n k : ℝ) ^ ((δ : ℝ) - (β : ℝ) * κ.aC) := by
    have htend := (tendsto_rpow_atTop hGap1Pos).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (1 + Real.log 4))
  have hGap2Pos : 0 < (q : ℝ) - (ζ : ℝ) := sub_pos.mpr (by exact_mod_cast hζq)
  have hGap2 : ∀ᶠ k in atTop,
      2 ≤ (T.S.n k : ℝ) ^ ((q : ℝ) - (ζ : ℝ)) := by
    have htend := (tendsto_rpow_atTop hGap2Pos).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (2 : ℝ))
  have hZeta : ∀ᶠ k in atTop,
      Real.log 2 ≤ (T.S.n k : ℝ) ^ (ζ : ℝ) := by
    have htend := (tendsto_rpow_atTop hζR).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (Real.log 2))
  have hηC : ∀ᶠ k in atTop,
      8 + 8 / κ.θ ≤ (T.S.n k : ℝ) ^ κ.η0 := by
    have htend := (tendsto_rpow_atTop hκ.η0_pos).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (8 + 8 / κ.θ))
  have hδC : ∀ᶠ k in atTop,
      8 + 8 / κ.θ ≤ (T.S.n k : ℝ) ^ (δ : ℝ) := by
    have htend := (tendsto_rpow_atTop hδR).comp
      (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (8 + 8 / κ.θ))
  have hn1 : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        T.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hprior, hClean, hNoFalse, hNoTrue, hGap1, hGap2, hZeta,
    hηC, hδC, hn1] with k hprior hclean hnoFalse hnoTrue hgap1 hgap2 hζpow hηCk hδCk hn
  intro RX RY hRX hRY b o hb hCluAt
  have hpriorB := hprior RX RY hRX hRY b o hb hCluAt
  by_cases hlt : (b : ℝ) < (T.S.n k : ℝ) ^ (q : ℝ)
  · exact hlt
  have hlarge : (T.S.n k : ℝ) ^ (q : ℝ) ≤ (b : ℝ) := le_of_not_gt hlt
  have hnpos : (0 : ℝ) < T.S.n k := by linarith
  have hpowerB : (b : ℝ) ^ κ.aC ≤ (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) := by
    calc
      (b : ℝ) ^ κ.aC ≤ ((T.S.n k : ℝ) ^ (β : ℝ)) ^ κ.aC :=
        Real.rpow_le_rpow (Nat.cast_nonneg b) (le_of_lt hpriorB) hκ.aC_rng.1.le
      _ = (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) :=
        (Real.rpow_mul (x := (T.S.n k : ℝ)) (by positivity) (β : ℝ) κ.aC).symm
  have hpowerBδ : (b : ℝ) ^ κ.aC ≤ (T.S.n k : ℝ) ^ (δ : ℝ) :=
    hpowerB.trans (Real.rpow_le_rpow_of_exponent_le hn (le_of_lt hβα))
  have hbaseOne : 1 ≤ (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) := by
    calc
      1 = (T.S.n k : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) :=
        Real.rpow_le_rpow_of_exponent_le hn
          (mul_nonneg (by exact_mod_cast hβ.le) hκ.aC_rng.1.le)
  have hpowAdd : (T.S.n k : ℝ) ^ (δ : ℝ) =
      (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) *
        (T.S.n k : ℝ) ^ ((δ : ℝ) - (β : ℝ) * κ.aC) := by
    rw [← Real.rpow_add hnpos]
    congr 1 <;> ring
  have hmix : (b : ℝ) ^ κ.aC + Real.log 4 ≤ (T.S.n k : ℝ) ^ (δ : ℝ) := by
    have hgapminus : Real.log 4 ≤
        (T.S.n k : ℝ) ^ ((δ : ℝ) - (β : ℝ) * κ.aC) - 1 := by linarith [hgap1]
    have hmul :
        (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) * Real.log 4 ≤
          (T.S.n k : ℝ) ^ ((β : ℝ) * κ.aC) *
            ((T.S.n k : ℝ) ^ ((δ : ℝ) - (β : ℝ) * κ.aC) - 1) := by
      exact mul_le_mul_of_nonneg_left hgapminus
        (Real.rpow_nonneg (by linarith [hn]) ((β : ℝ) * κ.aC))
    rw [hpowAdd]
    nlinarith [hpowerB, hbaseOne, hmul,
      Real.rpow_nonneg (by linarith [hn]) ((β : ℝ) * κ.aC)]
  have hpowQAdd : (T.S.n k : ℝ) ^ (q : ℝ) =
      (T.S.n k : ℝ) ^ (ζ : ℝ) *
        (T.S.n k : ℝ) ^ ((q : ℝ) - (ζ : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    congr 1 <;> ring
  have hpowQ : 2 * (T.S.n k : ℝ) ^ (ζ : ℝ) ≤
      (T.S.n k : ℝ) ^ (q : ℝ) := by
    have hmul : (T.S.n k : ℝ) ^ (ζ : ℝ) * 2 ≤
        (T.S.n k : ℝ) ^ (ζ : ℝ) * (T.S.n k : ℝ) ^ ((q : ℝ) - (ζ : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hgap2
        (Real.rpow_nonneg (by linarith [hn]) (ζ : ℝ))
    rw [hpowQAdd]
    nlinarith [hmul]
  have hblog : (T.S.n k : ℝ) ^ (ζ : ℝ) + Real.log 2 ≤ (b : ℝ) := by
    linarith [hlarge, hpowQ, hζpow]
  have hExpAdd : Real.exp ((T.S.n k : ℝ) ^ (ζ : ℝ) + Real.log 2) =
      2 * Real.exp ((T.S.n k : ℝ) ^ (ζ : ℝ)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have htwice : 2 * Real.exp ((T.S.n k : ℝ) ^ (ζ : ℝ)) ≤ Real.exp (b : ℝ) := by
    rw [← hExpAdd]
    exact Real.exp_le_exp.mpr hblog
  have hBinAtom : Real.exp ((T.S.n k : ℝ) ^ (ζ : ℝ)) ≤ Real.exp (b : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [htwice]
  have hθpos : 0 < κ.θ := hκ.θ_rng.1
  have hCpos : 0 < (8 + 8 / κ.θ : ℝ) := by positivity
  have hCgeθ : 8 / κ.θ ≤ 8 + 8 / κ.θ := by linarith
  have hCge8 : 8 ≤ 8 + 8 / κ.θ := by
    have hdiv : 0 ≤ 8 / κ.θ := le_of_lt (div_pos (by norm_num) hθpos)
    linarith
  have hInvCθ : (8 + 8 / κ.θ : ℝ)⁻¹ ≤ κ.θ / 8 := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 / κ.θ) hCgeθ
    have hEq : (8 / κ.θ : ℝ)⁻¹ = κ.θ / 8 := by
      field_simp [ne_of_gt hθpos]
    simpa [hEq] using h
  have hInvC8 : (8 + 8 / κ.θ : ℝ)⁻¹ ≤ (1 / 8 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hCge8
    norm_num at h ⊢
    exact h
  have hηinv : (T.S.n k : ℝ) ^ (-κ.η0) ≤ (8 + 8 / κ.θ : ℝ)⁻¹ := by
    rw [Real.rpow_neg hnpos.le]
    simpa only [one_div] using one_div_le_one_div_of_le hCpos hηCk
  have hδinv : (T.S.n k : ℝ) ^ (-(δ : ℝ)) ≤ (8 + 8 / κ.θ : ℝ)⁻¹ := by
    rw [Real.rpow_neg hnpos.le]
    simpa only [one_div] using one_div_le_one_div_of_le hCpos hδCk
  have hSmall : (T.S.n k : ℝ) ^ (-κ.η0) + (T.S.n k : ℝ) ^ (-(δ : ℝ)) ≤
      min (κ.θ / 4) (1 / 4 : ℝ) := by
    apply le_min
    · linarith [hηinv, hδinv, hInvCθ]
    · linarith [hηinv, hδinv, hInvC8]
  cases o with
  | false =>
      have hcleanBins := hclean RX RY hRX hRY b false hb hCluAt
      have hForbidden := HypercubeRamsey.Lane_q_s13_resid_cluster.cleaned_clusterWitnessAt
        κ T k RX RY b (ζ : ℝ) (δ : ℝ) hRX hRY hCluAt hcleanBins
        hpowerBδ hmix hBinAtom hSmall hCodegree
      exact (hnoFalse hForbidden).elim
  | true =>
      have hCluSwap := HypercubeRamsey.Lane_q_s13_resid.cluWitness_swap_aux
        κ T k RX RY b hCluAt
      have hcleanOrig := hclean RX RY hRX hRY b true hb hCluAt
      have hcleanSwap := HypercubeRamsey.Lane_q_s13_resid.cleanBins_swap_aux
        κ T k RX RY b hcleanOrig
      have hForbidden := HypercubeRamsey.Lane_q_s13_resid_cluster.cleaned_clusterWitnessAt
        κ T.swap k RY RX b (ζ : ℝ) (δ : ℝ) hRY hRX hCluSwap hcleanSwap
        hpowerBδ hmix hBinAtom hSmall hCodegree
      exact (hnoTrue hForbidden).elim

end HypercubeRamsey.Lane_q_s13_resid_step
