import HypercubeRamsey.S13.ResidualScales
import HypercubeRamsey.Framework.PartC

/-!
# Section 13.2: asymptotic bounds on residual scales
-/

namespace HypercubeRamsey.S13

open Filter

/-- L13.2 input (sections/13, lines 34–50): (B-C) on the exact rational parameters and
`ClusterWitnessAt` interface used by `partC_main`. -/
def ClusterAbsenceInput (κ : CConsts) (T : Stage) : Prop :=
  ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ →
    (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
    ∀ (c : Colour) (o : Bool),
      ∀ᶠ k in atTop, ¬ ClusterWitnessAt (T.orient o) k c ζ δ

/-- L13.2a (sections/13, lines 34–50): deep discrepancy bounds every bias witness. -/
theorem bias_scale_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b : ℕ, IsDyadic b → 2 ≤ b →
        BiasWitness κ T k RX RY b →
          (b : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
  classical
  have dens_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
      (μ ν : Law N) : 0 ≤ dens E c μ ν := by
    unfold dens
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    have hμ := μ.nonneg x
    have hν := ν.nonneg y
    by_cases h : Hits E c x y
    · simpa [h] using mul_nonneg hμ hν
    · simp [h]
  have dens_le_one {N : ℕ} (E : Fin N → Fin N → Prop) (μ ν : Law N) :
      dens E true μ ν ≤ 1 := by
    have hblue := dens_nonneg E false μ ν
    rw [← dens_add_dens_not E μ ν]
    linarith
  have hnEvent : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (1 : ℝ))
  have hgap : 0 < 1 - κ.aB := by
    have haC : κ.aC < 1 := by
      have hmin : min κ.η0 (1 : ℝ) ≤ (1 : ℝ) := min_le_right _ _
      linarith [hκ.aC_rng.2]
    have haB : κ.aB < 1 := by
      linarith [hκ.aB_rng.2.1, haC]
    linarith
  have hlinearEvent : ∀ᶠ k in atTop,
      1 / κ.αι ≤ (T.S.n k : ℝ) ^ (1 - κ.aB) := by
    have htend :=
      (tendsto_rpow_atTop hgap).comp (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_ge_atTop (1 / κ.αι))
  filter_upwards [hDeepι, hnEvent, hlinearEvent] with k hDeep hkN hklinear
  intro RX RY hRX hRY b hbdyadic hb2 hbias
  rcases hbias with ⟨U, V, hU, hV, hURX, hVRY, hUcard, hVcard, hbias⟩
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith [hkN]
  have hncast : (1 : ℝ) ≤ (T.S.n k : ℝ) := hkN
  have hNpos : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hnlinear : (T.S.n k : ℝ) ^ κ.aB ≤ κ.αι * T.S.n k := by
    have hfactor :
        1 ≤ (T.S.n k : ℝ) ^ (1 - κ.aB) * κ.αι :=
      (div_le_iff₀ hκ.αι_pos).mp hklinear
    have hprod : (T.S.n k : ℝ) ^ κ.aB *
        (T.S.n k : ℝ) ^ (1 - κ.aB) = T.S.n k := by
      calc
        (T.S.n k : ℝ) ^ κ.aB * (T.S.n k : ℝ) ^ (1 - κ.aB) =
            (T.S.n k : ℝ) ^ (κ.aB + (1 - κ.aB)) :=
          (Real.rpow_add hnpos _ _).symm
        _ = T.S.n k := by rw [show κ.aB + (1 - κ.aB) = 1 by ring, Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_left hfactor
      (Real.rpow_nonneg hnpos.le κ.aB)
    calc
      (T.S.n k : ℝ) ^ κ.aB = (T.S.n k : ℝ) ^ κ.aB * 1 := by ring
      _ ≤ (T.S.n k : ℝ) ^ κ.aB *
          ((T.S.n k : ℝ) ^ (1 - κ.aB) * κ.αι) := by simpa using hmul
      _ = κ.αι * T.S.n k := by rw [show
          (T.S.n k : ℝ) ^ κ.aB *
              ((T.S.n k : ℝ) ^ (1 - κ.aB) * κ.αι) =
            κ.αι * ((T.S.n k : ℝ) ^ κ.aB *
              (T.S.n k : ℝ) ^ (1 - κ.aB)) by ring, hprod]
  have width_of_card {A : Finset (Fin (T.S.N k))} (hA : A.Nonempty)
      (hcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ A.card)
      {t : ℝ} (hzt : (b : ℝ) ^ κ.aB ≤ t) :
      (Law.unifCore A hA).WidthLE t := by
    intro x
    by_cases hx : x ∈ A
    · have hrecip : (A.card : ℝ)⁻¹ ≤
          Real.exp ((b : ℝ) ^ κ.aB) / (T.S.N k : ℝ) := by
        calc
        (A.card : ℝ)⁻¹ ≤
            ((T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)))⁻¹ :=
          by
            simpa only [one_div] using one_div_le_one_div_of_le
              (mul_pos hNpos (Real.exp_pos _)) hcard
          _ = Real.exp ((b : ℝ) ^ κ.aB) / (T.S.N k : ℝ) := by
            rw [Real.exp_neg]
            field_simp [ne_of_gt hNpos,
              ne_of_gt (Real.exp_pos ((b : ℝ) ^ κ.aB))]
      calc
        (Law.unifCore A hA).w x = (A.card : ℝ)⁻¹ := by
          simp [Law.unifCore, hx]
        _ ≤ Real.exp ((b : ℝ) ^ κ.aB) / (T.S.N k : ℝ) := hrecip
        _ ≤ Real.exp t / (T.S.N k : ℝ) :=
          div_le_div_of_nonneg_right
            (Real.exp_le_exp.mpr hzt) (by positivity)
    · have hpos : 0 ≤ Real.exp t / (T.S.N k : ℝ) := by positivity
      simpa [Law.unifCore, hx] using hpos
  have hbLeN : (b : ℝ) ≤ (T.S.n k : ℝ) := by
    have hdens0 := dens_nonneg (T.S.E k) true (Law.unifCore U hU) (Law.unifCore V hV)
    have hdens1 := dens_le_one (T.S.E k) (Law.unifCore U hU) (Law.unifCore V hV)
    have hdev : |dens (T.S.E k) true (Law.unifCore U hU)
        (Law.unifCore V hV) - 1 / 2| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor <;> linarith
    exact le_trans (div_le_iff₀ hnpos |>.mp (le_trans hbias hdev)) (by linarith)
  have hbpowSmall : (b : ℝ) ^ κ.aB ≤ (T.S.n k : ℝ) ^ κ.xι := by
    have hbnonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
    have hbpow := Real.rpow_le_rpow hbnonneg hbLeN hκ.aB_rng.1.le
    exact hbpow.trans (Real.rpow_le_rpow_of_exponent_le hncast hκ.aB_rng.2.2)
  have hbpowLarge : (b : ℝ) ^ κ.aB ≤ κ.αι * T.S.n k := by
    have hbnonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
    exact (Real.rpow_le_rpow hbnonneg hbLeN hκ.aB_rng.1.le).trans hnlinear
  have hUsmall := width_of_card hU hUcard hbpowSmall
  have hVsmall := width_of_card hV hVcard hbpowSmall
  have hUlarge := width_of_card hU hUcard hbpowLarge
  have hVlarge := width_of_card hV hVcard hbpowLarge
  have hUsupport : (Law.unifCore U hU).SupportedIn (T.X k) := by
    intro x hx
    have hxU : x ∉ U := by
      intro hx'
      exact hx (hRX (hURX hx'))
    simp [Law.unifCore, hxU]
  have hVsupport : (Law.unifCore V hV).SupportedIn (T.Y k) := by
    intro x hx
    have hxV : x ∉ V := by
      intro hx'
      exact hx (hRY (hVRY hx'))
    simp [Law.unifCore, hxV]
  have hdisc := hDeep true (Law.unifCore U hU) (Law.unifCore V hV)
    hUsupport hVsupport (Or.inl ⟨hUlarge, hVsmall⟩)
  have hmul := mul_le_mul_of_nonneg_right (le_trans hbias hdisc) hnpos.le
  have hleft : (b : ℝ) / (T.S.n k : ℝ) * T.S.n k = b := by
    field_simp [ne_of_gt hnpos]
  have hright : (T.S.n k : ℝ) ^ (-1 + κ.ι / 2) * T.S.n k =
      (T.S.n k : ℝ) ^ (κ.ι / 2) := by
    calc
      (T.S.n k : ℝ) ^ (-1 + κ.ι / 2) * T.S.n k =
          (T.S.n k : ℝ) ^ (-1 + κ.ι / 2) * (T.S.n k : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (T.S.n k : ℝ) ^ ((-1 + κ.ι / 2) + 1) :=
            (Real.rpow_add hnpos _ _).symm
      _ = (T.S.n k : ℝ) ^ (κ.ι / 2) := by congr 1 <;> ring
  calc
    (b : ℝ) = (b : ℝ) / (T.S.n k : ℝ) * T.S.n k := hleft.symm
    _ ≤ (T.S.n k : ℝ) ^ (-1 + κ.ι / 2) * T.S.n k := hmul
    _ = (T.S.n k : ℝ) ^ (κ.ι / 2) := hright

/-- L13.2a (sections/13, lines 34–50): the maximum bias scale obeys the witness bound. -/
theorem bias_scale_max_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k →
        (gScale κ T k RX RY : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
  have hWitness := bias_scale_bound κ hκ T hDeepι
  have hιpos : 0 < κ.ι / 2 := by linarith [hκ.ι_rng.1]
  have hpow : ∀ᶠ k in atTop, 1 < (T.S.n k : ℝ) ^ (κ.ι / 2) := by
    have htend :=
      (tendsto_rpow_atTop hιpos).comp
        (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hWitness, hpow] with k hW hpow
  intro RX RY hRX hRY
  by_cases hscale : 2 ≤ gScale κ T k RX RY
  · exact hW RX RY hRX hRY (gScale κ T k RX RY)
      (gScale_isDyadic κ T k RX RY) hscale
      (gScale_witness κ T k RX RY hscale)
  · have hge : 1 ≤ gScale κ T k RX RY := by
      unfold gScale
      exact Nat.one_le_pow' _ 1
    have heq : gScale κ T k RX RY = 1 := by omega
    rw [heq]
    simpa using le_of_lt hpow

/-- L13.2b1 (sections/13, lines 34–50): cleaned cluster-bin data. The first set and law are
preserved; only bin labels are removed. -/
def CleanClusterBins (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) (o : Bool) : Prop :=
  ∀ (U : Finset (Fin (T.S.N k))) (hU : U.Nonempty) (m : ℕ)
    (B : Fin m → Finset (Fin (T.S.N k))),
    U ⊆ (if o then RY else RX) →
    (∀ j, B j ⊆ (if o then RX else RY)) →
    Set.PairwiseDisjoint Set.univ B →
    (∀ j, Real.exp b ≤ (B j).card) →
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ U.card →
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ (Finset.univ.biUnion B).card →
    (∀ j, ∀ y ∈ B j, ∀ y' ∈ B j, y ≠ y' →
      κ.θ < pairCorr (T.S.E k) o (Law.unifCore U hU) y y') →
    ∃ B' : Fin m → Finset (Fin (T.S.N k)),
      (∀ j, B' j ⊆ B j) ∧ Set.PairwiseDisjoint Set.univ B' ∧
      (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) / 4 ≤
      (Finset.univ.biUnion B').card ∧
      ∀ j y, y ∈ B' j →
        |(if o then rowDeg (T.S.E k) true y (Law.unifCore U hU)
          else colDeg (T.S.E k) true (Law.unifCore U hU) y) - 1 / 2| ≤
          (T.S.n k : ℝ) ^ (-κ.η0)

/-- L13.2b1 (sections/13, lines 34–50): trim column outliers while preserving a fixed fraction of
the total cluster-bin mass. -/
theorem clean_cluster_scale_witness (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → CleanClusterBins κ T k RX RY b o := by
  sorry

/-- L13.2b2 (sections/13, lines 34–50): codegree identity with red means and
colour-independent centered correlation. -/
theorem codegree_identity (N : ℕ) (E : Fin N → Fin N → Prop) (c : Colour)
    (μ : Law N) (y y' : Fin N) :
    (∑ x, μ.w x * hit E c x y * hit E c x y') =
      (1 + (if c then 1 else -1) * (2 * colDeg E true μ y - 1) +
        (if c then 1 else -1) * (2 * colDeg E true μ y' - 1) +
        pairCorr E false μ y y') / 4 := by
  classical
  let s : ℝ := if c then 1 else -1
  have hhit (x z : Fin N) : hit E c x z = (1 + s * fv E true x z) / 2 := by
    cases c <;> by_cases h : E x z <;> simp [s, hit, fv, Hits, h] <;> ring
  have hs : s * s = 1 := by cases c <;> simp [s]
  have hs2 : s ^ 2 = 1 := by nlinarith [hs]
  have hmean (z : Fin N) :
      (∑ x, μ.w x * fv E true x z) = 2 * colDeg E true μ z - 1 := by
    calc
      (∑ x, μ.w x * fv E true x z) =
          ∑ x, (2 * (μ.w x * hit E true x z) - μ.w x) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [fv]
            ring
      _ = 2 * (∑ x, μ.w x * hit E true x z) - ∑ x, μ.w x := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * colDeg E true μ z - 1 := by
            simp [colDeg, hit, μ.sum_eq_one]
  have hsum :
      (∑ x, μ.w x * (1 + s * fv E true x y + s * fv E true x y' +
        fv E true x y * fv E true x y')) =
        1 + s * (∑ x, μ.w x * fv E true x y) +
          s * (∑ x, μ.w x * fv E true x y') + pairCorr E false μ y y' := by
    calc
      _ = ∑ x, (μ.w x + s * (μ.w x * fv E true x y) +
          s * (μ.w x * fv E true x y') +
          μ.w x * fv E true x y * fv E true x y') := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = 1 + s * (∑ x, μ.w x * fv E true x y) +
          s * (∑ x, μ.w x * fv E true x y') + pairCorr E false μ y y' := by
            simp only [Finset.sum_add_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum, μ.sum_eq_one]
            simp [pairCorr]
  calc
    (∑ x, μ.w x * hit E c x y * hit E c x y') =
        (∑ x, μ.w x * (1 + s * fv E true x y + s * fv E true x y' +
          fv E true x y * fv E true x y')) / 4 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            rw [hhit x y, hhit x y']
            ring_nf
            rw [hs2]
            ring
    _ = (1 + s * (∑ x, μ.w x * fv E true x y) +
        s * (∑ x, μ.w x * fv E true x y') + pairCorr E false μ y y') / 4 := by
          rw [hsum]
    _ = (1 + (if c then 1 else -1) * (2 * colDeg E true μ y - 1) +
        (if c then 1 else -1) * (2 * colDeg E true μ y' - 1) +
        pairCorr E false μ y y') / 4 := by simp [s, hmean]

/-- L13.2b3 (sections/13, lines 34–50): the finite grid turns a cluster witness into one of
the forbidden `ClusterWitnessAt` instances. `hClean` and `hCodegree` are the
separate trimming and algebra nodes above. -/
theorem finite_grid_cluster_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hClu : ClusterAbsenceInput κ T)
    (hClean : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → CleanClusterBins κ T k RX RY b o)
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
  sorry

/-- L13.2b3 (sections/13, lines 34–50): every cluster-scale witness is smaller than the
specified positive power. -/
theorem cluster_witness_scale_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hClu : ClusterAbsenceInput κ T)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ b o, IsDyadic b →
        CluScaleWitness κ T k RX RY b o → (b : ℝ) < (T.S.n k : ℝ) ^ γ := by
  exact finite_grid_cluster_bound κ hκ T hInit hClu
    (clean_cluster_scale_witness κ hκ T hInit)
    codegree_identity γ hγ

/-- L13.2b3 (sections/13, lines 34–50): the maximum cluster scale satisfies the same
positive-power bound. -/
theorem cluster_scale_max_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hClu : ClusterAbsenceInput κ T)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k →
        (qScale κ T k RX RY : ℝ) < (T.S.n k : ℝ) ^ γ := by
  have hWitness := cluster_witness_scale_bound κ hκ T hInit hClu γ hγ
  have hpow : ∀ᶠ k in atTop, 1 < (T.S.n k : ℝ) ^ γ := by
    have htend :=
      (tendsto_rpow_atTop hγ).comp
        (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    exact htend.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hWitness, hpow] with k hW hpow
  intro RX RY hRX hRY
  by_cases hscale : 2 ≤ qScale κ T k RX RY
  · obtain ⟨o, hcluster⟩ := qScale_witness κ T k RX RY hscale
    exact hW RX RY hRX hRY (qScale κ T k RX RY) o
      (qScale_isDyadic κ T k RX RY) hcluster
  · have hge : 1 ≤ qScale κ T k RX RY := by
      unfold qScale
      exact Nat.one_le_pow' _ 1
    have heq : qScale κ T k RX RY = 1 := by omega
    rw [heq]
    simpa using hpow

/-- L13.2b (sections/13, lines 34–50): package witness and maximum-scale bounds. -/
theorem cluster_scale_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hClu : ClusterAbsenceInput κ T)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k →
        ((∀ b o, IsDyadic b → CluScaleWitness κ T k RX RY b o →
            (b : ℝ) < (T.S.n k : ℝ) ^ γ) ∧
          (qScale κ T k RX RY : ℝ) < (T.S.n k : ℝ) ^ γ) := by
  filter_upwards [cluster_witness_scale_bound κ hκ T hInit hClu γ hγ,
    cluster_scale_max_bound κ hκ T hInit hClu γ hγ] with k hWitness hMaximum
  intro RX RY hRX hRY
  exact ⟨hWitness RX RY hRX hRY, hMaximum RX RY hRX hRY⟩

/-- L13.2 (sections/13, lines 34–50): both residual-scale bounds at exponent `γ`. -/
def ResidualScaleBoundsAt (κ : CConsts) (T : Stage) (γ : ℝ) : Prop :=
  (∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
    RX ⊆ T.X k → RY ⊆ T.Y k →
      ((∀ b, IsDyadic b → 2 ≤ b → BiasWitness κ T k RX RY b →
          (b : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2)) ∧
        (gScale κ T k RX RY : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2))) ∧
  (∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
    RX ⊆ T.X k → RY ⊆ T.Y k →
      ((∀ b o, IsDyadic b → CluScaleWitness κ T k RX RY b o →
          (b : ℝ) < (T.S.n k : ℝ) ^ γ) ∧
        (qScale κ T k RX RY : ℝ) < (T.S.n k : ℝ) ^ γ))

/-- L13.2 (sections/13, lines 34–50): reusable scale bounds for every positive grid exponent. -/
def ResidualScaleBoundFacts (κ : CConsts) (T : Stage) : Prop :=
  ∀ γ : ℝ, 0 < γ → ResidualScaleBoundsAt κ T γ

/-- L13.2 (sections/13, lines 34–50): residual bias and cluster scales obey their asymptotic
bounds. The assembly explicitly composes the bias and finite-grid cluster nodes. -/
theorem residual_scale_bounds (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) : ResidualScaleBoundFacts κ T := by
  intro γ hγ
  constructor
  · filter_upwards [bias_scale_bound κ hκ T hDeepι,
      bias_scale_max_bound κ hκ T hDeepι] with k hWitness hMaximum
    intro RX RY hRX hRY
    exact ⟨hWitness RX RY hRX hRY, hMaximum RX RY hRX hRY⟩
  · filter_upwards [cluster_scale_bound κ hκ T hInit hClu γ hγ] with k hCluster
    intro RX RY hRX hRY
    exact hCluster RX RY hRX hRY

end HypercubeRamsey.S13
