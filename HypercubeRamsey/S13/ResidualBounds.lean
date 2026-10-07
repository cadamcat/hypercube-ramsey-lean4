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
  sorry

/-- L13.2a (sections/13, lines 34–50): the maximum bias scale obeys the witness bound. -/
theorem bias_scale_max_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k →
        (gScale κ T k RX RY : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
  sorry

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
      (∀ j, B' j = ∅ ∨ ((B j).card : ℝ) / 2 ≤ (B' j).card) ∧
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
  sorry

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
  sorry

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
