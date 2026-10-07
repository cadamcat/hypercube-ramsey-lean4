import HypercubeRamsey.S13.ResidualBounds_q_s13_resid_step

namespace HypercubeRamsey.Lane_q_s13_resid_grid

open HypercubeRamsey
open Filter
open Classical
open scoped BigOperators

private def ScaleBoundAt (κ : CConsts) (T : Stage) (β : ℚ) : Prop :=
  ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
    RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
      CluScaleWitness κ T k RX RY b o → (b : ℝ) < (T.S.n k : ℝ) ^ (β : ℝ)

theorem finite_grid_cluster_bound_aux
    (κ : CConsts) (hκ : CConsts.Admissible κ) (T : Stage)
    (_hInit : InitDisc T κ.η0)
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
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → (b : ℝ) < (T.S.n k : ℝ) ^ γ := by
  let P : ℕ → Prop := fun j =>
    ScaleBoundAt κ T (HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent j)
  have hP0 : P 0 := by
    simpa [P, ScaleBoundAt,
      HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent] using
      HypercubeRamsey.Lane_q_s13_resid_finite.initial_scale_bound κ T
  have hP : ∀ j, P j := by
    intro j
    induction j with
    | zero => exact hP0
    | succ j ih =>
        let β := HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent j
        let q := HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent (j + 1)
        let ζ := HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent j / 20
        have hβrange := HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent_range j
        have hβpos : 0 < (β : ℝ) := by exact_mod_cast hβrange.1
        have hβle : (β : ℝ) ≤ 2 := by exact_mod_cast hβrange.2
        have hζpos : 0 < ζ := by
          dsimp [ζ]
          exact div_pos hβrange.1 (by norm_num)
        have hqeq : q = β / 10 := by
          dsimp [q, β]
          exact HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent_succ j
        have hζq : ζ < q := by
          dsimp [ζ]
          rw [hqeq]
          have hbeta : 0 < (β : ℚ) := hβrange.1
          nlinarith
        have hζle : (ζ : ℝ) ≤ 1 := by
          have hζcast : (ζ : ℝ) = (β : ℝ) / 20 := by
            dsimp [ζ, β]
            norm_num
          rw [hζcast]
          nlinarith [hβle]
        have hminη : min κ.η0 1 ≤ κ.η0 := min_le_left _ _
        have haη : κ.aC < κ.η0 / 10 ^ 6 := by
          exact lt_of_lt_of_le hκ.aC_rng.2
            (div_le_div_of_nonneg_right hminη (by positivity))
        have ha1 : κ.aC < 1 / 10 ^ 6 := by
          exact lt_of_lt_of_le hκ.aC_rng.2
            (div_le_div_of_nonneg_right (min_le_right _ _ ) (by positivity))
        have hβη : (β : ℝ) * κ.aC < κ.η0 / 2000 := by
          have hmul := mul_lt_mul_of_pos_left haη hβpos
          have hbound := mul_le_mul_of_nonneg_right hβle
            (div_nonneg hκ.η0_pos.le (by positivity))
          nlinarith [hmul, hbound, hκ.η0_pos]
        have hβsmall : (β : ℝ) * κ.aC < (β : ℝ) / 40000 := by
          have hconst : (1 : ℝ) / 10 ^ 6 < 1 / 40000 := by norm_num
          have hmulA := mul_lt_mul_of_pos_left ha1 hβpos
          have hmulB := mul_lt_mul_of_pos_left hconst hβpos
          nlinarith [hmulA, hmulB]
        have hUpper : (β : ℝ) * κ.aC <
            min (κ.η0 / 2000) ((β : ℝ) / 40000) := lt_min hβη hβsmall
        obtain ⟨δ, hδlo, hδhi⟩ := exists_rat_btwn hUpper
        have hδposR : 0 < (δ : ℝ) := by
          have hβa : 0 < (β : ℝ) * κ.aC := mul_pos hβpos hκ.aC_rng.1
          exact lt_trans hβa hδlo
        have hδposQ : 0 < δ := by exact_mod_cast hδposR
        have hδeta : (δ : ℝ) < κ.η0 / 2000 :=
          lt_of_lt_of_le hδhi (min_le_left _ _)
        have hδzeta : (δ : ℝ) < (ζ : ℝ) / 2000 := by
          have hEqQ : β / 40000 = ζ / 2000 := by
            dsimp [β, ζ]
            ring
          have hEq : ((β : ℝ) / 40000) = (ζ : ℝ) / 2000 := by
            exact_mod_cast hEqQ
          rw [← hEq]
          exact lt_of_lt_of_le hδhi (min_le_right _ _)
        have hminζ : min (ζ : ℝ) 1 = (ζ : ℝ) := min_eq_left hζle
        have hδAbs : (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 := by
          rw [hminζ]
          by_cases hηζ : κ.η0 ≤ (ζ : ℝ)
          · rw [min_eq_left hηζ]
            exact hδeta
          · have hζη : (ζ : ℝ) ≤ κ.η0 := le_of_not_ge hηζ
            rw [min_eq_right hζη]
            exact hδzeta
        have hPnext := HypercubeRamsey.Lane_q_s13_resid_step.eventual_scale_step
          κ hκ T hClu hClean hCodegree β q ζ δ hβrange.1 hζpos hδposQ hδAbs
          hδlo hζq ih
        simpa [P, ScaleBoundAt] using hPnext
  have hgeomPow :
      Tendsto (fun j : ℕ => (2 : ℝ) * (1 / 10 : ℝ) ^ j) atTop (nhds 0) := by
    have hpow : Tendsto (fun j : ℕ => (1 / 10 : ℝ) ^ j) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (tendsto_const_nhds.mul hpow)
  have hgeom : Tendsto
      (fun j : ℕ =>
        (HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent j : ℝ))
      atTop (nhds 0) := by
    simpa [HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent_cast] using hgeomPow
  have hsmallIndex : ∀ᶠ j : ℕ in atTop,
      (HypercubeRamsey.Lane_q_s13_resid_finite.gridExponent j : ℝ) < γ :=
    hgeom.eventually (Iio_mem_nhds hγ)
  obtain ⟨M, hM⟩ := hsmallIndex.exists
  have hPM := hP M
  have hn1 : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        T.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hPM, hn1] with k hk hn
  intro RX RY hRX hRY b o hb hWitness
  have hbound := hk RX RY hRX hRY b o hb hWitness
  have hpow := Real.rpow_le_rpow_of_exponent_le hn (le_of_lt hM)
  exact lt_of_lt_of_le hbound hpow

end HypercubeRamsey.Lane_q_s13_resid_grid
