import HypercubeRamsey.S14.Construction

/-!
# Section 14 balanced profiles and finite low-mode data

The profile proof is split into continuity, pretrim, capped-range, fixed-point,
price-cap and total-variation nodes (P14.2a–f). The export assembles these
nodes after obtaining the solver family from P14.1.
-/

namespace HypercubeRamsey.S14

open Classical
open Filter
open scoped BigOperators

/-- A family of the per-patch solvers produced by P14.1. -/
structure SolverFamily {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (mesh : Mesh 𝒯) where
  solverAt : ∀ i : Fin 𝒯.m, SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh)

/-- Unrestricted profile `π⁰_i(p)` from the mean odd law. -/
noncomputable def rawWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯}
    (F : SolverFamily 𝒯 mesh) (p : mesh.Param) (i : Fin 𝒯.m)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  (F.solverAt i).solver.oddMean p g y

/-- Conditioned and pretrimmed output profile `πᵢ^{out}(p)`. -/
noncomputable def outputWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯}
    (F : SolverFamily 𝒯 mesh) (p : mesh.Param) (i : Fin 𝒯.m)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) : ℝ :=
  if 𝒯.mode = .lowCluster then (F.solverAt i).solver.lowOut p g y
  else (F.solverAt i).solver.oddMean p g y

/-- Continuity of the output profile on the mesh parameter space. -/
def OutputContinuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop :=
  ∀ i (g : Group 𝒯 i) y, Continuous fun p => outputWeight F p i g y

/-- Mass and conditioning estimates for the low-mode pretrim. -/
structure PretrimFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop where
  good_probability : ∀ i p,
    ((F.solverAt i).solver.recLaw p).pr (F.solverAt i).solver.AllGood ≥
      1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  good_positive : ∀ i p,
    0 < ((F.solverAt i).solver.recLaw p).pr (F.solverAt i).solver.AllGood
  retained_positive : ∀ i W g, (F.solverAt i).solver.AllGood W →
    0 < ∑ D ∈ (F.solverAt i).solver.pretrimBins W g, (F.solverAt i).solver.q g W D
  retained_bins : ∀ i W g,
    (F.solverAt i).solver.AllGood W →
      1 - (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
        ∑ D ∈ (F.solverAt i).solver.pretrimBins W g, (F.solverAt i).solver.q g W D

/-- The output profiles lie in the capped law domain of D14.M. -/
structure OutputLawFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) : Prop where
  nonneg : ∀ p i g y, 0 ≤ outputWeight F p i g y
  support : ∀ p i g y, y ∉ (𝒯.P i).Y → outputWeight F p i g y = 0
  sum_one : ∀ p i g, ∑ y, outputWeight F p i g y = 1
  cap : ∀ p i g y,
    (𝒯.P i).M * outputWeight F p i g y ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)

private theorem record_weight_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) :
    Continuous fun p => (S.recLaw p).w W := by
  change Continuous fun p => ∏ r, S.lawRec p r (W r)
  exact continuous_finsetProd _ (fun r hr => S.lawRec_cont r (W r))

private theorem rec_good_probability_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) :
    Continuous fun p => (S.recLaw p).pr S.AllGood := by
  classical
  unfold FinLaw.pr
  apply continuous_finsetSum _
  intro W hW
  by_cases hg : S.AllGood W
  · simp [hg]
    exact record_weight_continuous S W
  · simp [hg]
    exact continuous_const

private theorem raw_weight_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (y : Fin (T.S.N k)) :
    Continuous fun p => S.oddMean p g y := by
  classical
  unfold SliceSolver.oddMean SliceSolver.oddMarginal FinLaw.E
  apply continuous_finsetSum _
  intro W hW
  exact (record_weight_continuous S W).mul continuous_const

private theorem low_output_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh)
    (hpre : ∀ p, 0 < (S.recLaw p).pr S.AllGood)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) :
    Continuous fun p => S.lowOut p g y := by
  classical
  unfold SliceSolver.lowOut
  refine Continuous.div ?_ (rec_good_probability_continuous S) ?_
  · apply continuous_finsetSum _
    intro W hW
    have hw := record_weight_continuous S W
    by_cases hg : S.AllGood W
    · simp [hg]
      exact hw.mul continuous_const
    · simp [hg]
      exact continuous_const
  · intro p
    exact ne_of_gt (hpre p)

private theorem marginal_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i)
    (W : ∀ r, S.Val r) (y : Fin (T.S.N k)) : 0 ≤ S.oddMarginal g W y := by
  unfold SliceSolver.oddMarginal
  exact Finset.sum_nonneg fun D hD => mul_nonneg (S.q_nonneg g W D) (S.U_nonneg g W D y)

private theorem marginal_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r) :
    ∑ y, S.oddMarginal g W y = 1 := by
  classical
  unfold SliceSolver.oddMarginal
  rw [Finset.sum_comm]
  calc
    (∑ D, ∑ y, S.q g W D * S.U g W D y) =
        ∑ D, S.q g W D * ∑ y, S.U g W D y := by
          apply Finset.sum_congr rfl
          intro D hD
          rw [Finset.mul_sum]
    _ = ∑ D, S.q g W D := by simp [S.U_sum]
    _ = 1 := S.q_sum g W

private theorem marginal_support {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r)
    (y : Fin (T.S.N k)) (hy : y ∉ (𝒯.P i).Y) : S.oddMarginal g W y = 0 := by
  classical
  unfold SliceSolver.oddMarginal
  apply Finset.sum_eq_zero
  intro D hD
  have hsub : D.1 ⊆ (𝒯.P i).Y := Finpartition.le (𝒯.P i).bins D.2
  have hUy : S.U g W D y = 0 := by
    by_contra hne
    exact hy (hsub (S.U_support g W D y hne))
  simp [hUy]

private theorem raw_weight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) : 0 ≤ S.oddMean p g y := by
  unfold SliceSolver.oddMean FinLaw.E
  exact Finset.sum_nonneg fun W hW =>
    mul_nonneg ((S.recLaw p).nonneg W) (marginal_nonneg S g W y)

private theorem raw_weight_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i) :
    ∑ y, S.oddMean p g y = 1 := by
  classical
  unfold SliceSolver.oddMean FinLaw.E
  calc
    (∑ y, ∑ W, (S.recLaw p).w W * S.oddMarginal g W y) =
        ∑ W, ∑ y, (S.recLaw p).w W * S.oddMarginal g W y := by
          rw [Finset.sum_comm]
    _ = ∑ W, (S.recLaw p).w W * ∑ y, S.oddMarginal g W y := by
          apply Finset.sum_congr rfl
          intro W hW
          rw [Finset.mul_sum]
    _ =
        ∑ W, (S.recLaw p).w W := by simp [marginal_sum_one]
    _ = 1 := (S.recLaw p).sum_one

private theorem raw_weight_support {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) (hy : y ∉ (𝒯.P i).Y) :
    S.oddMean p g y = 0 := by
  unfold SliceSolver.oddMean FinLaw.E
  simp_rw [marginal_support S g _ y hy]
  simp

private theorem raw_weight_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param)
    (g : Group 𝒯 i) (y : Fin (T.S.N k)) :
    S.oddMean p g y ≤ 8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
      (𝒯.P i).M := by
  classical
  unfold SliceSolver.oddMean SliceSolver.oddMarginal FinLaw.E
  calc
    (∑ W, (S.recLaw p).w W * ∑ D, S.q g W D * S.U g W D y) ≤
        ∑ W, (S.recLaw p).w W *
          (8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
            (𝒯.P i).M) := by
          apply Finset.sum_le_sum
          intro W hW
          exact mul_le_mul_of_nonneg_left (S.marginal_cap g W y)
            ((S.recLaw p).nonneg W)
    _ = 8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
          (𝒯.P i).M := by
          rw [← Finset.sum_mul, (S.recLaw p).sum_one, one_mul]

private noncomputable def qinLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) : FinLaw (Bin 𝒯 i) :=
  FinLaw.cond ⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩ (S.pretrimBins W g) hpos

private theorem qin_eq_qinLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) (D : Bin 𝒯 i) :
    S.qin W g D = (qinLaw S W g hpos).w D := by
  classical
  by_cases hD : D ∈ S.pretrimBins W g <;>
    simp [SliceSolver.qin, qinLaw, FinLaw.cond, hD]

private theorem qin_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) (D : Bin 𝒯 i) :
    0 ≤ S.qin W g D := by
  rw [qin_eq_qinLaw S W g hpos D]
  exact (qinLaw S W g hpos).nonneg D

private theorem qin_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    ∑ D, S.qin W g D = 1 := by
  classical
  calc
    (∑ D, S.qin W g D) = ∑ D, (qinLaw S W g hpos).w D := by
      apply Finset.sum_congr rfl
      intro D hD
      exact qin_eq_qinLaw S W g hpos D
    _ = 1 := (qinLaw S W g hpos).sum_one

private theorem qin_le_four_thirds {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hden : (3 / 4 : ℝ) ≤ ∑ D ∈ S.pretrimBins W g, S.q g W D)
    (D : Bin 𝒯 i) : S.qin W g D ≤ (4 / 3 : ℝ) * S.q g W D := by
  classical
  have hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D := by linarith
  by_cases hD : D ∈ S.pretrimBins W g
  · rw [SliceSolver.qin, if_pos hD]
    apply (div_le_iff₀ hpos).2
    have hq := S.q_nonneg g W D
    nlinarith [mul_le_mul_of_nonneg_left hden hq]
  · rw [SliceSolver.qin, if_neg hD]
    positivity [S.q_nonneg g W D]

private theorem low_inner_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hpos : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    ∑ y, ∑ D, S.qin W g D * S.U g W D y = 1 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ D, ∑ y, S.qin W g D * S.U g W D y) =
        ∑ D, S.qin W g D * ∑ y, S.U g W D y := by
          apply Finset.sum_congr rfl
          intro D hD
          rw [Finset.mul_sum]
    _ = ∑ D, S.qin W g D := by simp [S.U_sum]
    _ = 1 := qin_sum_one S W g hpos

private theorem low_output_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) (hgood : 0 < (S.recLaw p).pr S.AllGood)
    (hpos : ∀ W, S.AllGood W →
      0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    0 ≤ S.lowOut p g y := by
  classical
  unfold SliceSolver.lowOut
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro W hW
    by_cases hg : S.AllGood W
    · simp [hg]
      apply mul_nonneg ((S.recLaw p).nonneg W)
      apply Finset.sum_nonneg
      intro D hD
      exact mul_nonneg
        (qin_nonneg S W g (hpos W hg) D) (S.U_nonneg g W D y)
    · simp [hg]
  · exact hgood.le

private theorem low_output_support {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) (hy : y ∉ (𝒯.P i).Y)
    (hgood : 0 < (S.recLaw p).pr S.AllGood) : S.lowOut p g y = 0 := by
  classical
  unfold SliceSolver.lowOut
  have hinner (W : ∀ r, S.Val r) :
      ∑ D, S.qin W g D * S.U g W D y = 0 := by
    apply Finset.sum_eq_zero
    intro D hD
    have hsub : D.1 ⊆ (𝒯.P i).Y := Finpartition.le (𝒯.P i).bins D.2
    have hUy : S.U g W D y = 0 := by
      by_contra hne
      exact hy (hsub (S.U_support g W D y hne))
    simp [hUy]
  simp_rw [hinner]
  simp

private theorem low_output_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (hgood : 0 < (S.recLaw p).pr S.AllGood)
    (hpos : ∀ W, S.AllGood W →
      0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    ∑ y, S.lowOut p g y = 1 := by
  classical
  unfold SliceSolver.lowOut
  rw [← Finset.sum_div]
  have hnum :
      (∑ y, ∑ W, (S.recLaw p).w W *
        (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0)) =
      (S.recLaw p).pr S.AllGood := by
    rw [Finset.sum_comm]
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hg : S.AllGood W
    · simp only [hg, if_pos]
      rw [← Finset.mul_sum, low_inner_sum_one S W g (hpos W hg)]
      simp
    · simp [hg]
  rw [hnum]
  exact div_self (ne_of_gt hgood)

private theorem low_output_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) (hgood : 0 < (S.recLaw p).pr S.AllGood)
    (hpre : ∀ W, S.AllGood W →
      (3 / 4 : ℝ) ≤ ∑ D ∈ S.pretrimBins W g, S.q g W D)
    (hcap : (32 / 3 : ℝ) * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i))
    (hM : 0 < (𝒯.P i).M) :
    S.lowOut p g y ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
      (𝒯.P i).M := by
  classical
  let C := Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
    ((𝒯.P i).M : ℝ)
  have hMr : 0 < ((𝒯.P i).M : ℝ) := Nat.cast_pos.mpr hM
  have hC : 0 ≤ C := div_nonneg (le_of_lt (Real.exp_pos _)) hMr.le
  have hinner (W : ∀ r, S.Val r) (hg : S.AllGood W) :
      (∑ D, S.qin W g D * S.U g W D y) ≤ C := by
    have hqcap : ∀ D, S.qin W g D ≤ (4 / 3 : ℝ) * S.q g W D :=
      fun D => qin_le_four_thirds S W g (hpre W hg) D
    calc
      (∑ D, S.qin W g D * S.U g W D y) ≤
          ∑ D, (4 / 3 : ℝ) * (S.q g W D * S.U g W D y) := by
            apply Finset.sum_le_sum
            intro D hD
            calc
              S.qin W g D * S.U g W D y ≤
                  ((4 / 3 : ℝ) * S.q g W D) * S.U g W D y :=
                mul_le_mul_of_nonneg_right (hqcap D) (S.U_nonneg g W D y)
              _ = (4 / 3 : ℝ) * (S.q g W D * S.U g W D y) := by ring
      _ = (4 / 3 : ℝ) * ∑ D, S.q g W D * S.U g W D y := by
            rw [← Finset.mul_sum]
      _ ≤ (4 / 3 : ℝ) *
          (8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).M) :=
            mul_le_mul_of_nonneg_left (S.marginal_cap g W y) (by norm_num)
      _ = ((32 / 3 : ℝ) *
          Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)) / (𝒯.P i).M := by ring
      _ ≤ C := by
            apply div_le_div_of_nonneg_right hcap hMr.le
  have hnum :
      (∑ W, (S.recLaw p).w W *
        (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0)) ≤
      (S.recLaw p).pr S.AllGood * C := by
    calc
      _ ≤ ∑ W, (if S.AllGood W then (S.recLaw p).w W * C else 0) := by
        apply Finset.sum_le_sum
        intro W hW
        by_cases hg : S.AllGood W
        · simp only [hg, if_pos]
          exact mul_le_mul_of_nonneg_left (hinner W hg) ((S.recLaw p).nonneg W)
        · simp [hg]
      _ = (S.recLaw p).pr S.AllGood * C := by
        unfold FinLaw.pr
        calc
          (∑ W, if S.AllGood W then (S.recLaw p).w W * C else 0) =
              ∑ W, (if S.AllGood W then (S.recLaw p).w W else 0) * C := by
                apply Finset.sum_congr rfl
                intro W hW
                split_ifs <;> ring
          _ = (∑ W, if S.AllGood W then (S.recLaw p).w W else 0) * C := by
                rw [Finset.sum_mul]
  unfold SliceSolver.lowOut
  apply (div_le_iff₀ hgood).2
  simpa [C, mul_comm] using hnum

private theorem low_output_pos_raw_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) (hgood : 0 < (S.recLaw p).pr S.AllGood)
    (hret : ∀ W, S.AllGood W →
      0 < ∑ D ∈ S.pretrimBins W g, S.q g W D)
    (hout : 0 < S.lowOut p g y) : 0 < S.oddMean p g y := by
  classical
  let P := S.recLaw p
  let inner (W : ∀ r, S.Val r) :=
    ∑ D, S.qin W g D * S.U g W D y
  have hnum : 0 < ∑ W, P.w W * (if S.AllGood W then inner W else 0) := by
    have hdiv : 0 <
        (∑ W, P.w W * (if S.AllGood W then inner W else 0)) / P.pr S.AllGood := by
      simpa [SliceSolver.lowOut, P, inner] using hout
    exact (div_pos_iff_of_pos_right hgood).mp hdiv
  have hWpos : ∃ W, 0 < P.w W * (if S.AllGood W then inner W else 0) := by
    by_contra hn
    have hall : ∀ W, P.w W * (if S.AllGood W then inner W else 0) ≤ 0 := by
      intro W
      exact le_of_not_gt (fun h => hn ⟨W, h⟩)
    have hsum := Finset.sum_nonpos (s := Finset.univ)
      (f := fun W => P.w W * (if S.AllGood W then inner W else 0))
      (fun W hW => hall W)
    linarith
  obtain ⟨W, hterm⟩ := hWpos
  have hWgood : S.AllGood W := by
    by_contra hg
    simp [hg] at hterm
  have hinner_nonneg : 0 ≤ inner W := by
    apply Finset.sum_nonneg
    intro D hD
    exact mul_nonneg
      (qin_nonneg S W g (hret W hWgood) D) (S.U_nonneg g W D y)
  have hPpos : 0 < P.w W := by
    by_contra hn
    have hz : P.w W = 0 := le_antisymm (le_of_not_gt hn) (P.nonneg W)
    simp [hWgood, hz] at hterm
  have hinnerpos : 0 < inner W := by
    by_contra hn
    have hz : inner W = 0 := le_antisymm (le_of_not_gt hn) hinner_nonneg
    simp [hWgood, hz] at hterm
  have hDpos : ∃ D, 0 < S.qin W g D * S.U g W D y := by
    by_contra hn
    have hall : ∀ D, S.qin W g D * S.U g W D y ≤ 0 := by
      intro D
      exact le_of_not_gt (fun h => hn ⟨D, h⟩)
    have hsum := Finset.sum_nonpos (s := Finset.univ)
      (f := fun D => S.qin W g D * S.U g W D y)
      (fun D hD => hall D)
    linarith
  obtain ⟨D, hDterm⟩ := hDpos
  have hqinpos : 0 < S.qin W g D := by
    by_contra hn
    have hz : S.qin W g D = 0 :=
      le_antisymm (le_of_not_gt hn) (qin_nonneg S W g (hret W hWgood) D)
    rw [hz, zero_mul] at hDterm
    norm_num at hDterm
  have hqpos : 0 < S.q g W D := by
    by_contra hn
    have hDnot : D ∉ S.pretrimBins W g := by
      intro hDmem
      have hq := (Finset.mem_filter.mp hDmem).2.1
      exact (not_lt_of_ge (le_of_not_gt hn)) hq
    simp [SliceSolver.qin, hDnot] at hqinpos
  have hUpos : 0 < S.U g W D y := by
    by_contra hn
    have hz : S.U g W D y = 0 :=
      le_antisymm (le_of_not_gt hn) (S.U_nonneg g W D y)
    rw [hz, mul_zero] at hDterm
    norm_num at hDterm
  have hrawD : 0 < S.q g W D * S.U g W D y := mul_pos hqpos hUpos
  have hmarginal : 0 < S.oddMarginal g W y := by
    unfold SliceSolver.oddMarginal
    exact lt_of_lt_of_le hrawD (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun D => S.q g W D * S.U g W D y)
      (fun D hD => mul_nonneg (S.q_nonneg g W D) (S.U_nonneg g W D y))
      (Finset.mem_univ D))
  unfold SliceSolver.oddMean FinLaw.E
  exact lt_of_lt_of_le (mul_pos hPpos hmarginal)
    (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun W => P.w W * S.oddMarginal g W y)
      (fun W hW => mul_nonneg (P.nonneg W) (marginal_nonneg S g W y))
      (Finset.mem_univ W))

private theorem flipPos_involutive {n : ℕ} (v : CubePos n) (l : Fin n) :
    flipPos (flipPos v l) l = v := by
  funext j
  by_cases hj : j = l
  · subst j
    simp [flipPos]
  · simp [flipPos, hj]

private theorem incident_card_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) :
    Fintype.card {v : EvenRole 𝒯 i // SliceSolver.Incident v g} ≤
      (𝒯.P i).h * (𝒯.P i).h := by
  classical
  let I := {v : EvenRole 𝒯 i // SliceSolver.Incident v g}
  let l (v : I) : Fin (𝒯.P i).h := Classical.choose v.property
  have hl (v : I) : flipPos v.1.1 (l v) ∈ groupFiber g :=
    Classical.choose_spec v.property
  have himage (v : I) :
      flipPos v.1.1 (l v) ∈ Finset.univ.image (flipPos g.1) := by
    simpa [groupFiber] using hl v
  let l' (v : I) : Fin (𝒯.P i).h :=
    Classical.choose (Finset.mem_image.mp (himage v))
  have hl' (v : I) : flipPos g.1 (l' v) = flipPos v.1.1 (l v) :=
    (Classical.choose_spec (Finset.mem_image.mp (himage v))).2
  have hrecon (v : I) :
      flipPos (flipPos g.1 (l' v)) (l v) = v.1.1 := by
    have h := congrArg (fun z => flipPos z (l v)) (hl' v)
    rw [flipPos_involutive] at h
    exact h
  let f : I → Fin (𝒯.P i).h × Fin (𝒯.P i).h := fun v => (l v, l' v)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have h₁ : l a = l b := congrArg Prod.fst hab
    have h₂ : l' a = l' b := congrArg Prod.snd hab
    calc
      a.1.1 = flipPos (flipPos g.1 (l' a)) (l a) := (hrecon a).symm
      _ = flipPos (flipPos g.1 (l' b)) (l b) := by rw [h₁, h₂]
      _ = b.1.1 := hrecon b
  have hcard := Fintype.card_le_of_injective f hf
  exact hcard.trans_eq (by simp [Nat.card_prod])

private theorem finLaw_pr_nonneg {α : Type*} [Fintype α] (P : FinLaw α)
    (A : α → Prop) : 0 ≤ P.pr A := by
  classical
  unfold FinLaw.pr
  exact Finset.sum_nonneg fun x hx => by
    split_ifs
    · exact P.nonneg x
    · exact le_rfl

private theorem finLaw_pr_compl {α : Type*} [Fintype α] (P : FinLaw α)
    (A : α → Prop) : P.pr A + P.pr (fun x => ¬ A x) = 1 := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib, ← P.sum_one]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

private theorem bin_zero_event_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (g : Group 𝒯 i) (v : EvenRole 𝒯 i) :
    (∑ D : Bin 𝒯 i, (S.refLaw W).pr (fun ω =>
      ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0)) =
      (S.refLaw W).pr (fun ω => S.σ v W (nbrLabels v.1 ω.2) = 0) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hz : S.σ v W (nbrLabels v.1 ω.2) = 0
  · simp [hz]
  · simp [hz]

private theorem pretrim_bad_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (g : Group 𝒯 i) (v : EvenRole 𝒯 i) (hgood : S.AllGood W) :
    (∑ D ∈ Finset.univ.filter (fun D : Bin 𝒯 i =>
      Real.sqrt (sliceEps κ (𝒯.P i).h) * S.q g W D <
          (S.refLaw W).pr (fun ω =>
            ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0)),
      S.q g W D) ≤ Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  classical
  let δ := Real.sqrt (sliceEps κ (𝒯.P i).h)
  let B := Finset.univ.filter (fun D : Bin 𝒯 i =>
    δ * S.q g W D <
      (S.refLaw W).pr (fun ω =>
        ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0))
  have hδ : 0 < δ := by
    dsimp [δ, sliceEps]
    exact Real.sqrt_pos.2 (Real.exp_pos _)
  have hδsq : δ * δ = sliceEps κ (𝒯.P i).h := by
    exact Real.mul_self_sqrt (le_of_lt (Real.exp_pos (-0.001 * κ.a *
      (𝒯.kScale i : ℝ) * (𝒯.P i).h)))
  have hsum : δ * (∑ D ∈ B, S.q g W D) ≤ sliceEps κ (𝒯.P i).h := by
    calc
      δ * (∑ D ∈ B, S.q g W D) =
          ∑ D ∈ B, δ * S.q g W D := by rw [Finset.mul_sum]
      _ ≤ ∑ D ∈ B, (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) := by
        apply Finset.sum_le_sum
        intro D hD
        exact le_of_lt (Finset.mem_filter.mp hD).2
      _ ≤ ∑ D : Bin 𝒯 i, (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        intro D hD hnot
        exact finLaw_pr_nonneg _ _
      _ = (S.refLaw W).pr (fun ω => S.σ v W (nbrLabels v.1 ω.2) = 0) :=
        bin_zero_event_sum S W g v
      _ ≤ sliceEps κ (𝒯.P i).h := S.Hgood_zero v W (hgood v)
  have hmass : (∑ D ∈ B, S.q g W D) ≤ δ := by
    by_contra hnot
    have hlt : δ < ∑ D ∈ B, S.q g W D := lt_of_not_ge hnot
    have hm := mul_lt_mul_of_pos_left hlt hδ
    rw [← hδsq] at hsum
    linarith
  simpa [B, δ] using hmass

private theorem bad_pretrim_bin_witness {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (g : Group 𝒯 i) (D : Bin 𝒯 i) (hq : 0 < S.q g W D)
    (hD : D ∉ S.pretrimBins W g) :
    ∃ v : EvenRole 𝒯 i, SliceSolver.Incident v g ∧
      Real.sqrt (sliceEps κ (𝒯.P i).h) * S.q g W D <
        (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) := by
  classical
  have hall : ¬ ∀ v : EvenRole 𝒯 i, SliceSolver.Incident v g →
      (S.refLaw W).pr (fun ω =>
        ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) ≤
          Real.sqrt (sliceEps κ (𝒯.P i).h) * S.q g W D := by
    intro h
    apply hD
    simp only [SliceSolver.pretrimBins, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hq, h⟩
  push_neg at hall
  rcases hall with ⟨v, hv, hfail⟩
  exact ⟨v, hv, hfail⟩

private theorem outputWeight_group_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (p : mesh.Param) (i : Fin 𝒯.m) (g g' : Group 𝒯 i)
    (y : Fin (T.S.N k)) : outputWeight F p i g y = outputWeight F p i g' y := by
  by_cases hmode : 𝒯.mode = .lowCluster
  · simp [outputWeight, hmode]
    exact (F.solverAt i).low_output_invariant p g g' y hmode
  · simp [outputWeight, hmode]
    simpa [SliceSolver.recLaw, recordLaw, FinLaw.pi,
      SliceSolver.oddMean, SliceSolver.oddMarginal] using
      (F.solverAt i).solver.averaged_marginal_invariant p g g' y

private theorem retained_bin_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (g : Group 𝒯 i) (hgood : S.AllGood W) :
    1 - (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
      ∑ D ∈ S.pretrimBins W g, S.q g W D := by
  classical
  let δ := Real.sqrt (sliceEps κ (𝒯.P i).h)
  let bad := Finset.univ.filter (fun D : Bin 𝒯 i => D ∉ S.pretrimBins W g)
  let I := {v : EvenRole 𝒯 i // SliceSolver.Incident v g}
  have hδ : 0 < δ := by
    dsimp [δ, sliceEps]
    exact Real.sqrt_pos.2 (Real.exp_pos _)
  have hIcard : (Fintype.card I : ℝ) ≤ (𝒯.P i).h ^ 2 := by
    have hnat := incident_card_bound g
    exact_mod_cast (by simpa [pow_two] using hnat)
  have hpoint : ∀ D ∈ bad, S.q g W D ≤
      ∑ v : I, if δ * S.q g W D <
        (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)
        then S.q g W D else 0 := by
    intro D hD
    by_cases hq : 0 < S.q g W D
    · obtain ⟨v, hv, hfail⟩ :=
        bad_pretrim_bin_witness S W g D hq (Finset.mem_filter.mp hD).2
      let v' : I := ⟨v, hv⟩
      have hs := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun z : I => if δ * S.q g W D <
          (S.refLaw W).pr (fun ω =>
            ω.1 g = D ∧ S.σ z.1 W (nbrLabels z.1.1 ω.2) = 0)
          then S.q g W D else 0)
        (fun z hz => by split_ifs <;> positivity)
        (Finset.mem_univ v')
      have hfail' : δ * S.q g W D < (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v'.1 W (nbrLabels v'.1.1 ω.2) = 0) := by
        simpa [v'] using hfail
      have hterm : (if δ * S.q g W D < (S.refLaw W).pr (fun ω =>
          ω.1 g = D ∧ S.σ v'.1 W (nbrLabels v'.1.1 ω.2) = 0)
          then S.q g W D else 0) = S.q g W D := if_pos hfail'
      rw [hterm] at hs
      exact hs
    · have hq0 : S.q g W D = 0 := by
        exact le_antisymm (le_of_not_gt hq) (S.q_nonneg g W D)
      simp [hq0]
  have hbad_sum : (∑ D ∈ bad, S.q g W D) ≤
      (𝒯.P i).h ^ 2 * δ := by
    calc
      (∑ D ∈ bad, S.q g W D) ≤
          ∑ D ∈ bad, ∑ v : I, if δ * S.q g W D <
            (S.refLaw W).pr (fun ω =>
              ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)
            then S.q g W D else 0 := by
          apply Finset.sum_le_sum
          intro D hD
          exact hpoint D hD
      _ = ∑ v : I, ∑ D ∈ bad, if δ * S.q g W D <
            (S.refLaw W).pr (fun ω =>
              ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)
            then S.q g W D else 0 := by
          rw [Finset.sum_comm]
      _ ≤ ∑ v : I, δ := by
          apply Finset.sum_le_sum
          intro v hv
          let Bv := Finset.univ.filter (fun D : Bin 𝒯 i =>
            δ * S.q g W D < (S.refLaw W).pr (fun ω =>
              ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0))
          have hsum_eq :
              (∑ D ∈ bad, if δ * S.q g W D <
                (S.refLaw W).pr (fun ω =>
                  ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)
                then S.q g W D else 0) =
              ∑ D ∈ bad.filter (fun D => δ * S.q g W D <
                (S.refLaw W).pr (fun ω =>
                  ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)),
                S.q g W D := by
            rw [← Finset.sum_filter]
          calc
            (∑ D ∈ bad, if δ * S.q g W D <
                (S.refLaw W).pr (fun ω =>
                  ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)
                then S.q g W D else 0) =
              ∑ D ∈ bad.filter (fun D => δ * S.q g W D <
                (S.refLaw W).pr (fun ω =>
                  ω.1 g = D ∧ S.σ v.1 W (nbrLabels v.1.1 ω.2) = 0)),
                S.q g W D := hsum_eq
            _ ≤ ∑ D ∈ Bv, S.q g W D := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro D hD
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  (Finset.mem_filter.mp hD).2⟩
              · intro D hD hnot
                exact S.q_nonneg g W D
            _ ≤ δ := by
              simpa [Bv, δ] using pretrim_bad_mass S W g v.1 hgood
      _ = (Fintype.card I : ℝ) * δ := by simp
      _ ≤ (𝒯.P i).h ^ 2 * δ := by
          exact mul_le_mul_of_nonneg_right hIcard hδ.le
  have hsplit :
      (∑ D ∈ S.pretrimBins W g, S.q g W D) +
        (∑ D ∈ bad, S.q g W D) = ∑ D : Bin 𝒯 i, S.q g W D := by
    dsimp [bad]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun D : Bin 𝒯 i => D ∈ S.pretrimBins W g)]
    simp
  rw [S.q_sum g W] at hsplit
  linarith

/-- P14.2a: continuity of the conditioned, pretrimmed output law. -/
theorem output_continuous {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hpre : PretrimFacts F) : OutputContinuous F := by
  intro i g y
  by_cases hmode : 𝒯.mode = .lowCluster
  · simp [outputWeight, hmode]
    exact low_output_continuous (F.solverAt i).solver
      (fun p => hpre.good_positive i p) g y
  · simp [outputWeight, hmode]
    exact raw_weight_continuous (F.solverAt i).solver g y

/-- P14.2b: conditioning and bin pretrim retain positive mass, uniformly in
the parameter point. -/
theorem pretrim_well_defined {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hκ : κ.Admissible) (hconst : HeightConstantContract κ)
    (hscales : ∀ i, PatchScales 𝒯 i) : PretrimFacts F := by
  classical
  refine {
    good_probability := ?_
    good_positive := ?_
    retained_positive := ?_
    retained_bins := ?_
  }
  · intro i p
    let S := (F.solverAt i).solver
    let P := S.recLaw p
    have hbad_eq : P.pr (fun W => ¬ S.AllGood W) =
        P.pr (fun W => ∃ v, ¬ S.Hgood v W) := by
      congr 1
      funext W
      simp [SliceSolver.AllGood]
    have hcompl := finLaw_pr_compl P S.AllGood
    have hbad := S.Hgood_bad p
    have hbound : 1 - P.pr S.AllGood ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) := by
      rw [hbad_eq] at hcompl
      have hEq : P.pr (fun W => ∃ v, ¬ S.Hgood v W) = 1 - P.pr S.AllGood := by
        linarith [hcompl]
      rw [← hEq]
      exact hbad
    linarith
  · intro i p
    have hh : 0 < (𝒯.P i).h :=
      lt_of_lt_of_le hκ.h0_pos (hscales i).h_large
    have hrpow : 0 < Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hh) _
    have hexp : Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    let S := (F.solverAt i).solver
    let P := S.recLaw p
    have hbad_eq : P.pr (fun W => ¬ S.AllGood W) =
        P.pr (fun W => ∃ v, ¬ S.Hgood v W) := by
      congr 1
      funext W
      simp [SliceSolver.AllGood]
    have hcomp := finLaw_pr_compl P S.AllGood
    rw [hbad_eq] at hcomp
    have hEq : P.pr (fun W => ∃ v, ¬ S.Hgood v W) = 1 - P.pr S.AllGood := by
      linarith [hcomp]
    have hpos : 0 < 1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) :=
      sub_pos.mpr hexp
    have hbadbound : P.pr (fun W => ∃ v, ¬ S.Hgood v W) ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) := by
      exact S.Hgood_bad p
    rw [hEq] at hbadbound
    have hprob' : 1 - Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) ≤
        P.pr S.AllGood := by
      linarith [hbadbound]
    exact lt_of_lt_of_le hpos hprob'
  · intro i W g hgood
    have hmass := retained_bin_mass (F.solverAt i).solver W g hgood
    have hsmall := (hscales i).pretrim_small
    have hlower : (3 / 4 : ℝ) ≤
        ∑ D ∈ (F.solverAt i).solver.pretrimBins W g,
          (F.solverAt i).solver.q g W D := by
      nlinarith
    linarith
  · intro i W g hgood
    exact retained_bin_mass (F.solverAt i).solver W g hgood

/-- P14.2c: the S1 bounds place every output profile in the capped input
domain, including the low-mode conditioning and pretrim factors. -/
theorem output_in_capped_domain {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hκ : κ.Admissible) (hscales : ∀ i, PatchScales 𝒯 i)
    (hpre : PretrimFacts F) : OutputLawFacts F := by
  classical
  refine {
    nonneg := ?_
    support := ?_
    sum_one := ?_
    cap := ?_
  }
  · intro p i g y
    by_cases hmode : 𝒯.mode = .lowCluster
    · simp [outputWeight, hmode]
      exact low_output_nonneg (F.solverAt i).solver p g y (hpre.good_positive i p)
        (fun W hg => hpre.retained_positive i W g hg)
    · simp [outputWeight, hmode]
      exact raw_weight_nonneg (F.solverAt i).solver p g y
  · intro p i g y hy
    by_cases hmode : 𝒯.mode = .lowCluster
    · simp [outputWeight, hmode]
      exact low_output_support (F.solverAt i).solver p g y hy (hpre.good_positive i p)
    · simp [outputWeight, hmode]
      exact raw_weight_support (F.solverAt i).solver p g y hy
  · intro p i g
    by_cases hmode : 𝒯.mode = .lowCluster
    · simp [outputWeight, hmode]
      apply low_output_sum_one (F.solverAt i).solver p g
        (hpre.good_positive i p)
      intro W hg
      exact hpre.retained_positive i W g hg
    · simp [outputWeight, hmode]
      exact raw_weight_sum_one (F.solverAt i).solver p g
  · intro p i g y
    by_cases hmode : 𝒯.mode = .lowCluster
    · simp [outputWeight, hmode]
      have hden (W : ∀ r, (F.solverAt i).solver.Val r)
          (hg : (F.solverAt i).solver.AllGood W) :
          (3 / 4 : ℝ) ≤
            ∑ D ∈ (F.solverAt i).solver.pretrimBins W g,
              (F.solverAt i).solver.q g W D := by
        have hret := hpre.retained_bins i W g hg
        have hsmall := (hscales i).pretrim_small
        nlinarith
      have hlow := low_output_cap (F.solverAt i).solver p g y
        (hpre.good_positive i p) hden (hscales i).cap_slack
        (Nat.cast_pos.mpr (hscales i).M_pos)
      calc
        (𝒯.P i).M * (F.solverAt i).solver.lowOut p g y ≤
            (𝒯.P i).M *
              (Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
                (𝒯.P i).M) :=
                  mul_le_mul_of_nonneg_left hlow
                    (le_of_lt (Nat.cast_pos.mpr (hscales i).M_pos))
        _ = Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
              field_simp [ne_of_gt (Nat.cast_pos.mpr (hscales i).M_pos)]
    · simp [outputWeight, hmode]
      have hraw := raw_weight_cap (F.solverAt i).solver p g y
      have hM : 0 < ((𝒯.P i).M : ℝ) := Nat.cast_pos.mpr (hscales i).M_pos
      calc
        (𝒯.P i).M * (F.solverAt i).solver.oddMean p g y ≤
            (𝒯.P i).M *
              (8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) /
                (𝒯.P i).M) := by
                  exact mul_le_mul_of_nonneg_left hraw (le_of_lt hM)
        _ = 8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
              field_simp [ne_of_gt hM]
        _ ≤ (32 / 3 : ℝ) * Real.exp
              (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
                exact mul_le_mul_of_nonneg_right (by norm_num)
                  (le_of_lt (Real.exp_pos _))
        _ ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) :=
              (hscales i).cap_slack

/-- A fixed point of the simultaneous output and price-response map. -/
structure ProfileFixedPoint {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh) where
  point : mesh.Param
  fixed_profile : ∀ i (g : Group 𝒯 i) y,
    (mesh.paramLaw point i).w y = outputWeight F point i g y
  price_maximizer : ∀ i,
    ∀ z : Fin (T.S.N k) → ℝ,
      (∀ y, 0 ≤ z y) → (∀ y, y ∉ (𝒯.P i).Y → z y = 0) →
      (∑ y, z y = 1) →
        ∑ y, z y * (mesh.paramLaw point i).w y ≤
          ∑ y, mesh.paramPrice point i y * (mesh.paramLaw point i).w y

private def profileMix {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (P Q : ParameterProfile 𝒯) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : ParameterProfile 𝒯 := by
  classical
  refine {
    law := fun i => {
      w := fun y => a * (P.law i).w y + b * (Q.law i).w y
      nonneg := fun y => add_nonneg (mul_nonneg ha ((P.law i).nonneg y))
        (mul_nonneg hb ((Q.law i).nonneg y))
      sum_eq_one := ?_
    }
    price := fun i y => a * P.price i y + b * Q.price i y
    law_supported := ?_
    law_cap := ?_
    price_simplex := ?_
  }
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [(P.law i).sum_eq_one, (Q.law i).sum_eq_one]
    nlinarith
  · intro i y hy
    simp only
    rw [P.law_supported i y hy, Q.law_supported i y hy]
    ring
  · intro i y
    change (𝒯.P i).M *
        (a * (P.law i).w y + b * (Q.law i).w y) ≤
      Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
    calc
      (𝒯.P i).M * (a * (P.law i).w y + b * (Q.law i).w y) =
          a * ((𝒯.P i).M * (P.law i).w y) +
            b * ((𝒯.P i).M * (Q.law i).w y) := by ring
      _ ≤ a * Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) +
            b * Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (P.law_cap i y) ha)
            (mul_le_mul_of_nonneg_left (Q.law_cap i y) hb)
      _ = Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
          calc
            a * Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) +
                b * Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) =
              (a + b) * Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by ring
            _ = Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by rw [hab]; ring
  · intro i
    rcases P.price_simplex i with ⟨hp0, hpS, hp1⟩
    rcases Q.price_simplex i with ⟨hq0, hqS, hq1⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y
      exact add_nonneg (mul_nonneg ha (hp0 y)) (mul_nonneg hb (hq0 y))
    · intro y hy
      simp [hpS y hy, hqS y hy]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1]
      nlinarith

private theorem profileMix_coordinates {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (P Q : ParameterProfile 𝒯) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (profileMix P Q a b ha hb hab).coordinates =
      a • P.coordinates + b • Q.coordinates := by
  ext i y <;> simp [ParameterProfile.coordinates, profileMix] <;> ring

private theorem price_best_response_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (μ : Law (T.S.N k)) (i : Fin 𝒯.m)
    (hsupp : μ.SupportedIn (𝒯.P i).Y) :
    ∃ z : Fin (T.S.N k) → ℝ,
      (∀ y, 0 ≤ z y) ∧ (∀ y, y ∉ (𝒯.P i).Y → z y = 0) ∧
      ∑ y, z y = 1 ∧
      ∀ q : Fin (T.S.N k) → ℝ, (∀ y, 0 ≤ q y) →
        (∀ y, y ∉ (𝒯.P i).Y → q y = 0) → ∑ y, q y = 1 →
        ∑ y, q y * μ.w y ≤ ∑ y, z y * μ.w y := by
  classical
  have hN : 0 < T.S.N k := T.S.N_pos k
  have hpos : ∃ y, 0 < μ.w y := by
    by_contra hn
    have hall : ∀ y, μ.w y ≤ 0 := by
      intro y
      exact le_of_not_gt (fun hy => hn ⟨y, hy⟩)
    have hsum := Finset.sum_nonpos (s := Finset.univ) (f := μ.w)
      (fun y hy => hall y)
    rw [μ.sum_eq_one] at hsum
    norm_num at hsum
  obtain ⟨y₀, hy₀⟩ := hpos
  obtain ⟨ymax, hymax, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (T.S.N k))) μ.w
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hypos : 0 < μ.w ymax := lt_of_lt_of_le hy₀ (hmax y₀ (Finset.mem_univ _))
  have hyY : ymax ∈ (𝒯.P i).Y := by
    by_contra hy
    have := hsupp ymax hy
    linarith
  let z : Fin (T.S.N k) → ℝ := fun y => if y = ymax then 1 else 0
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases h : y = ymax <;> simp [z, h]
  · intro y hy
    by_cases h : y = ymax
    · subst y
      exact (hy hyY).elim
    · simp [z, h]
  · simp [z]
  · intro q hq0 hqS hq1
    calc
      (∑ y, q y * μ.w y) ≤ μ.w ymax := by
        calc
          (∑ y, q y * μ.w y) ≤ ∑ y, q y * μ.w ymax := by
            apply Finset.sum_le_sum
            intro y hy
            exact mul_le_mul_of_nonneg_left (hmax y (Finset.mem_univ _)) (hq0 y)
          _ = μ.w ymax := by
            rw [← Finset.sum_mul, hq1]
            ring
      _ = ∑ y, z y * μ.w y := by
        calc
          μ.w ymax = ∑ y, if y = ymax then μ.w ymax else 0 := by simp
          _ = ∑ y, z y * μ.w y := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : y = ymax <;> simp [z, h]

private def zeroGroup {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (i : Fin 𝒯.m) : Group 𝒯 i := by
  refine ⟨fun _ => false, ?_⟩
  constructor
  · simp [IsEvenRole]
  · funext j
    simp [wordSyndrome]

/-- P14.2d: Kakutani on the compact convex finite-dimensional parameter
domain gives the simultaneous fixed profile and price maximizers. -/
theorem fixed_point {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (domain : MeshProfileDomain mesh)
    (F : SolverFamily 𝒯 mesh) (hcont : OutputContinuous F)
    (hpre : PretrimFacts F) (hout : OutputLawFacts F) :
    Nonempty (ProfileFixedPoint F) := by
  classical
  let V := (Fin 𝒯.m → Fin (T.S.N k) → ℝ) ×
    (Fin 𝒯.m → Fin (T.S.N k) → ℝ)
  let coord : ParameterProfile 𝒯 → V := fun P => P.coordinates
  let K : Set V := Set.range coord
  have hKconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨P, rfl⟩
    rcases hy with ⟨Q, rfl⟩
    refine ⟨profileMix P Q a b ha hb hab, ?_⟩
    exact profileMix_coordinates P Q a b ha hb hab
  let φ : domain.carrier → V := fun x =>
    (domain.profileOf (domain.encode.symm x)).coordinates
  have hφ : Continuous φ := by
    exact continuous_induced_dom.comp
      (domain.profileOf_continuous.comp domain.decode_continuous)
  have hKrange : K = Set.range φ := by
    ext z
    constructor
    · rintro ⟨P, rfl⟩
      refine ⟨⟨domain.coordinates P, domain.coordinates_mem P⟩, ?_⟩
      dsimp [φ]
      have heq : domain.encode.symm ⟨domain.coordinates P, domain.coordinates_mem P⟩ =
          domain.realize P := by
        apply domain.encode.injective
        simpa using (domain.realize_coordinates P).symm
      rw [heq, domain.profileOf_realize]
    · rintro ⟨x, rfl⟩
      exact ⟨domain.profileOf (domain.encode.symm x), rfl⟩
  have hKcompact : IsCompact K := by
    rw [hKrange]
    letI : CompactSpace domain.carrier :=
      isCompact_iff_compactSpace.mp domain.domain.compact
    exact isCompact_range hφ
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := domain.domain.nonempty
    refine ⟨coord (domain.profileOf (domain.encode.symm ⟨x, hx⟩)), ?_⟩
    exact ⟨domain.profileOf (domain.encode.symm ⟨x, hx⟩), rfl⟩
  let State := {x : V // x ∈ K}
  let stateProfile : State → ParameterProfile 𝒯 := fun x => Classical.choose x.property
  have hstateCoord (x : State) : coord (stateProfile x) = x.1 :=
    Classical.choose_spec x.property
  have hstateProfile_cont : Continuous stateProfile := by
    rw [instParameterProfileTop]
    apply continuous_induced_rng.mpr
    convert continuous_subtype_val using 1
    funext x
    exact hstateCoord x
  let statePoint (x : State) : mesh.Param := domain.realize (stateProfile x)
  have hstatePoint_cont : Continuous statePoint :=
    domain.realize_continuous.comp hstateProfile_cont
  let outLaw (p : mesh.Param) (i : Fin 𝒯.m) (y : Fin (T.S.N k)) : ℝ :=
    outputWeight F p i (zeroGroup i) y
  have hout_cont (i : Fin 𝒯.m) (y : Fin (T.S.N k)) :
      Continuous fun x : State => outLaw (statePoint x) i y := by
    exact (hcont i (zeroGroup i) y).comp hstatePoint_cont
  let response (x : State) : Set V := {z |
    z ∈ K ∧
    (∀ i y, z.1 i y = outLaw (statePoint x) i y) ∧
    (∀ i (q : Fin (T.S.N k) → ℝ), (∀ y, 0 ≤ q y) →
      (∀ y, y ∉ (𝒯.P i).Y → q y = 0) → (∑ y, q y = 1) →
      ∑ y, q y * x.1.1 i y ≤ ∑ y, z.2 i y * x.1.1 i y)}
  have hresponse_subset : ∀ x : State, response x ⊆ K := by
    intro x z hz
    exact hz.1
  have hresponse_nonempty : ∀ x : State, (response x).Nonempty := by
    intro x
    let P := stateProfile x
    let p := statePoint x
    let best : ∀ i : Fin 𝒯.m, Fin (T.S.N k) → ℝ := fun i =>
      Classical.choose (price_best_response_exists (P.law i) i (P.law_supported i))
    have hbest (i : Fin 𝒯.m) :=
      Classical.choose_spec (price_best_response_exists (P.law i) i (P.law_supported i))
    let Q : ParameterProfile 𝒯 := {
      law := fun i => {
        w := fun y => outLaw p i y
        nonneg := fun y => hout.nonneg p i (zeroGroup i) y
        sum_eq_one := hout.sum_one p i (zeroGroup i)
      }
      price := best
      law_supported := by
        intro i y hy
        exact hout.support p i (zeroGroup i) y hy
      law_cap := by
        intro i y
        exact hout.cap p i (zeroGroup i) y
      price_simplex := by
        intro i
        exact ⟨(hbest i).1, (hbest i).2.1, (hbest i).2.2.1⟩
    }
    have hxLaw (i : Fin 𝒯.m) (y : Fin (T.S.N k)) :
        x.1.1 i y = (P.law i).w y := by
      have h := congrArg (fun z : V => z.1 i y) (hstateCoord x)
      simpa [coord, ParameterProfile.coordinates] using h.symm
    refine ⟨coord Q, ⟨Q, rfl⟩, ?_, ?_⟩
    · intro i y
      rfl
    · intro i q hq0 hqS hq1
      have h := (hbest i).2.2.2 q hq0 hqS hq1
      have hfirst :
          (∑ y, q y * x.1.1 i y) ≤ ∑ y, best i y * x.1.1 i y := by
        simpa [hxLaw i] using h
      calc
        (∑ y, q y * x.1.1 i y) ≤ ∑ y, best i y * x.1.1 i y := hfirst
        _ = ∑ y, (coord Q).2 i y * x.1.1 i y := by
          apply Finset.sum_congr rfl
          intro y hy
          rfl
  have hresponse_convex : ∀ x : State, Convex ℝ (response x) := by
    intro x z hz w hw a b ha hb hab
    rcases hz with ⟨hzK, hzl, hzp⟩
    rcases hw with ⟨hwK, hwl, hwp⟩
    refine ⟨hKconv hzK hwK ha hb hab, ?_, ?_⟩
    · intro i y
      have hz := hzl i y
      have hw := hwl i y
      change a * z.1 i y + b * w.1 i y = outLaw (statePoint x) i y
      rw [hz, hw, ← add_mul, hab, one_mul]
    · intro i q hq0 hqS hq1
      have hza := hzp i q hq0 hqS hq1
      have hwb := hwp i q hq0 hqS hq1
      let μ := fun y => x.1.1 i y
      have hpayPrice (r s : Fin (T.S.N k) → ℝ) :
          (∑ y, (a * r y + b * s y) * μ y) =
            a * (∑ y, r y * μ y) + b * (∑ y, s y * μ y) := by
        calc
          (∑ y, (a * r y + b * s y) * μ y) =
              ∑ y, (a * (r y * μ y) + b * (s y * μ y)) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
          _ = a * (∑ y, r y * μ y) + b * (∑ y, s y * μ y) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hright :
          (∑ y, (a * z.2 i y + b * w.2 i y) * μ y) =
            a * (∑ y, z.2 i y * μ y) + b * (∑ y, w.2 i y * μ y) :=
        hpayPrice (fun y => z.2 i y) (fun y => w.2 i y)
      calc
        (∑ y, q y * μ y) = (a + b) * (∑ y, q y * μ y) := by rw [hab]; ring
        _ = a * (∑ y, q y * μ y) + b * (∑ y, q y * μ y) := by ring
        _ ≤ a * (∑ y, z.2 i y * μ y) + b * (∑ y, w.2 i y * μ y) :=
          add_le_add (mul_le_mul_of_nonneg_left hza ha)
            (mul_le_mul_of_nonneg_left hwb hb)
        _ = ∑ y, (a * z.2 i y + b * w.2 i y) * μ y := hright.symm
  have hKclosed : IsClosed K := hKcompact.isClosed
  let lawGraph : Set (State × V) :=
    ⋂ i : Fin 𝒯.m, ⋂ y : Fin (T.S.N k),
      {v : State × V | v.2.1 i y = outLaw (statePoint v.1) i y}
  let priceGraph : Set (State × V) :=
    ⋂ i : Fin 𝒯.m, ⋂ q : Fin (T.S.N k) → ℝ,
      ⋂ hq0 : (∀ y, 0 ≤ q y),
      ⋂ hqS : (∀ y, y ∉ (𝒯.P i).Y → q y = 0),
      ⋂ hq1 : (∑ y, q y = 1),
        {v : State × V | ∑ y, q y * v.1.1.1 i y ≤
          ∑ y, v.2.2 i y * v.1.1.1 i y}
  have hgraphSet :
      {v : State × V | v.2 ∈ response v.1} =
        ({v : State × V | v.2 ∈ K} ∩ lawGraph) ∩ priceGraph := by
    ext ⟨x, z⟩
    simp [response, lawGraph, priceGraph]
    tauto
  have hLawGraph : IsClosed lawGraph := by
    dsimp [lawGraph]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro y
    apply isClosed_eq
    · have hVfst : Continuous (fun v : State × V =>
          (v.2.1 : Fin 𝒯.m → Fin (T.S.N k) → ℝ)) :=
        continuous_fst.comp continuous_snd
      have hI : Continuous (fun v : State × V =>
          (v.2.1 i : Fin (T.S.N k) → ℝ)) :=
        (continuous_apply i).comp hVfst
      exact (continuous_apply y).comp hI
    · exact (hout_cont i y).comp continuous_fst
  have hPriceGraph : IsClosed priceGraph := by
    dsimp [priceGraph]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro q
    apply isClosed_iInter
    intro hq0
    apply isClosed_iInter
    intro hqS
    apply isClosed_iInter
    intro hq1
    have hCurrentV : Continuous (fun v : State × V => (v.1.1 : V)) :=
      continuous_subtype_val.comp continuous_fst
    have hCurrentProf : Continuous (fun v : State × V =>
        (v.1.1.1 : Fin 𝒯.m → Fin (T.S.N k) → ℝ)) :=
      continuous_fst.comp hCurrentV
    have hCurrentAtI : Continuous (fun v : State × V =>
        (v.1.1.1 i : Fin (T.S.N k) → ℝ)) :=
      (continuous_apply i).comp hCurrentProf
    have hCurrentAt (y : Fin (T.S.N k)) :
        Continuous fun v : State × V => v.1.1.1 i y :=
      (continuous_apply y).comp hCurrentAtI
    have hPriceV : Continuous (fun v : State × V =>
        (v.2.2 : Fin 𝒯.m → Fin (T.S.N k) → ℝ)) :=
      continuous_snd.comp continuous_snd
    have hPriceAtI : Continuous (fun v : State × V =>
        (v.2.2 i : Fin (T.S.N k) → ℝ)) :=
      (continuous_apply i).comp hPriceV
    have hPriceAt (y : Fin (T.S.N k)) :
        Continuous fun v : State × V => v.2.2 i y :=
      (continuous_apply y).comp hPriceAtI
    apply isClosed_le
    · exact continuous_finsetSum _ (fun y hy => continuous_const.mul (hCurrentAt y))
    · exact continuous_finsetSum _ (fun y hy => (hPriceAt y).mul (hCurrentAt y))
  have hgraph : closedGraph response := by
    rw [closedGraph, hgraphSet]
    exact ((hKclosed.preimage continuous_snd).inter hLawGraph).inter hPriceGraph
  have hresponse_facts : ∀ x : State,
      response x ⊆ K ∧ Convex ℝ (response x) ∧ (response x).Nonempty := by
    intro x
    exact ⟨hresponse_subset x, hresponse_convex x, hresponse_nonempty x⟩
  obtain ⟨x, hx⟩ := kakutani_fixed_point K hKconv hKcompact hKne
    response hgraph hresponse_facts
  let P := stateProfile x
  let p := domain.realize P
  have hLawCoord (i : Fin 𝒯.m) (y : Fin (T.S.N k)) :
      (mesh.paramLaw p i).w y = x.1.1 i y := by
    calc
      (mesh.paramLaw p i).w y = (P.law i).w y := by rw [domain.realize_law]
      _ = x.1.1 i y := by
        have h := congrArg (fun z : V => z.1 i y) (hstateCoord x)
        simpa [coord, ParameterProfile.coordinates] using h
  have hPriceCoord (i : Fin 𝒯.m) (y : Fin (T.S.N k)) :
      mesh.paramPrice p i y = x.1.2 i y := by
    calc
      mesh.paramPrice p i y = P.price i y := domain.realize_price P i y
      _ = x.1.2 i y := by
        have h := congrArg (fun z : V => z.2 i y) (hstateCoord x)
        simpa [coord, ParameterProfile.coordinates] using h
  rcases hx with ⟨hxK, hxlaw, hxprice⟩
  refine ⟨⟨p, ?_, ?_⟩⟩
  · intro i g y
    calc
      (mesh.paramLaw p i).w y = x.1.1 i y := hLawCoord i y
      _ = outLaw p i y := hxlaw i y
      _ = outputWeight F p i g y := outputWeight_group_eq F p i (zeroGroup i) g y
  · intro i z hz0 hzS hz1
    calc
      (∑ y, z y * (mesh.paramLaw p i).w y) =
          ∑ y, z y * x.1.1 i y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hLawCoord i y]
      _ ≤ ∑ y, x.1.2 i y * x.1.1 i y := hxprice i z hz0 hzS hz1
      _ = ∑ y, mesh.paramPrice p i y * (mesh.paramLaw p i).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hPriceCoord i y, hLawCoord i y]

/-- P14.2e: the fixed-point law has maximum atom at most `11/M`, by the
active-mask price bound and the price-maximizer identity. -/
theorem active_price_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hpre : PretrimFacts F)
    (p : ProfileFixedPoint F) :
    ∀ i y, (mesh.paramLaw p.point i).w y ≤ 11 / (𝒯.P i).M := by
  classical
  intro i y
  let π := mesh.paramLaw p.point i
  change π.w y ≤ 11 / (𝒯.P i).M
  have hposY : ∃ x, 0 < π.w x := by
    by_contra hn
    have hall : ∀ x, π.w x ≤ 0 := by
      intro x
      exact le_of_not_gt (fun hx => hn ⟨x, hx⟩)
    have hsum := Finset.sum_nonpos (s := Finset.univ) (f := π.w)
      (fun x hx => hall x)
    rw [π.sum_eq_one] at hsum
    norm_num at hsum
  obtain ⟨x₀, hx₀⟩ := hposY
  have hx₀Y : x₀ ∈ (𝒯.P i).Y := by
    by_contra hx
    have := mesh.paramLaw_supp p.point i x₀ hx
    linarith
  have hMnat : 0 < (𝒯.P i).M := by
    rw [← (𝒯.P i).cardY]
    exact Finset.card_pos.mpr ⟨x₀, hx₀Y⟩
  have hM : 0 < ((𝒯.P i).M : ℝ) := Nat.cast_pos.mpr hMnat
  have hnNat : 0 < T.S.n k := by
    by_contra hnot
    have hn0 : T.S.n k = 0 := by omega
    have hle := T.S.N_le k
    have hNpos := T.S.N_pos k
    rw [hn0] at hle
    simp at hle
    omega
  have hn : 1 ≤ (T.S.n k : ℝ) := by
    have hnNat' : 1 ≤ T.S.n k := Nat.one_le_iff_ne_zero.mpr hnNat.ne'
    exact_mod_cast hnNat'
  have hpriceCap (x : Fin (T.S.N k)) (hπ : 0 < π.w x) :
      mesh.paramPrice p.point i x ≤ 11 / (𝒯.P i).M := by
    let g := zeroGroup i
    have hout : 0 < outputWeight F p.point i g x := by
      rw [← p.fixed_profile i g x]
      exact hπ
    have hraw : 0 < (F.solverAt i).solver.oddMean p.point g x := by
      by_cases hlow : 𝒯.mode = .lowCluster
      · have houtlow : 0 < (F.solverAt i).solver.lowOut p.point g x := by
          simpa [outputWeight, hlow] using hout
        exact low_output_pos_raw_pos (F.solverAt i).solver p.point g x
          (hpre.good_positive i p.point)
          (fun W hg => hpre.retained_positive i W g hg) houtlow
      · simpa [outputWeight, hlow] using hout
    obtain ⟨v, hv, hcheap⟩ := (F.solverAt i).cheap_raw_support p.point g x hraw
    have hlocal := mesh.local_price v p.point hv i x
    have hlocal' := (abs_le.mp hlocal).2
    have hdenle : (𝒯.P i).M ≤ (T.S.n k : ℝ) * (𝒯.P i).M := by
      nlinarith [mul_le_mul_of_nonneg_right hn hM.le]
    have hfrac : 1 / ((T.S.n k : ℝ) * (𝒯.P i).M) ≤ 1 / (𝒯.P i).M :=
      one_div_le_one_div_of_le hM hdenle
    calc
      mesh.paramPrice p.point i x ≤ mesh.paramPrice (mesh.base v) i x +
          1 / ((T.S.n k : ℝ) * (𝒯.P i).M) := by linarith
      _ ≤ 10 / (𝒯.P i).M + 1 / (𝒯.P i).M := add_le_add hcheap hfrac
      _ = 11 / (𝒯.P i).M := by ring
  by_cases hπy : 0 < π.w y
  · have hyY : y ∈ (𝒯.P i).Y := by
      by_contra hy
      have hsupp := mesh.paramLaw_supp p.point i y hy
      linarith
    let z : Fin (T.S.N k) → ℝ := fun x => if x = y then 1 else 0
    have hz0 : ∀ x, 0 ≤ z x := by intro x; by_cases h : x = y <;> simp [z, h]
    have hzS : ∀ x, x ∉ (𝒯.P i).Y → z x = 0 := by
      intro x hx
      by_cases h : x = y
      · subst x
        exact (hx hyY).elim
      · simp [z, h]
    have hzsum : ∑ x, z x = 1 := by simp [z]
    have hbest := p.price_maximizer i z hz0 hzS hzsum
    have hprice_avg : (∑ x, mesh.paramPrice p.point i x * π.w x) ≤
        11 / (𝒯.P i).M := by
      calc
        (∑ x, mesh.paramPrice p.point i x * π.w x) ≤
            ∑ x, (11 / (𝒯.P i).M) * π.w x := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases hxpos : 0 < π.w x
              · exact mul_le_mul_of_nonneg_right (hpriceCap x hxpos) (π.nonneg x)
              · have hxzero : π.w x = 0 := le_antisymm (le_of_not_gt hxpos) (π.nonneg x)
                simp [hxzero]
        _ = 11 / (𝒯.P i).M := by
          calc
            (∑ x, (11 / (𝒯.P i).M) * π.w x) =
                (∑ x, π.w x) * (11 / (𝒯.P i).M) := by
                  calc
                    (∑ x, (11 / (𝒯.P i).M) * π.w x) =
                        ∑ x, π.w x * (11 / (𝒯.P i).M) := by
                          apply Finset.sum_congr rfl
                          intro x hx
                          ring
                    _ = (∑ x, π.w x) * (11 / (𝒯.P i).M) :=
                      (Finset.sum_mul (s := Finset.univ) (f := π.w)
                        (a := 11 / (𝒯.P i).M)).symm
            _ = 11 / (𝒯.P i).M := by rw [π.sum_eq_one, one_mul]
    have hzy : (∑ x, z x * π.w x) = π.w y := by simp [z]
    rw [hzy] at hbest
    exact hbest.trans hprice_avg
  · have hzero : π.w y = 0 := le_antisymm (le_of_not_gt hπy) (π.nonneg y)
    rw [hzero]
    exact div_nonneg (by norm_num) hM.le

private theorem good_history_trim_tv {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (hgood : S.AllGood W)
    (hret : 0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    (1 / 2 : ℝ) * ∑ y,
      |S.oddMarginal g W y - ∑ D, S.qin W g D * S.U g W D y| ≤
        (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  classical
  let B := S.pretrimBins W g
  let bad := Finset.univ.filter (fun D : Bin 𝒯 i => D ∉ B)
  let Q := ∑ D ∈ B, S.q g W D
  have hQle : Q ≤ 1 := by
    have hsplit : Q + (∑ D ∈ bad, S.q g W D) = ∑ D, S.q g W D := by
      dsimp [Q, bad, B]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun D : Bin 𝒯 i => D ∈ S.pretrimBins W g)]
      simp
    rw [S.q_sum g W] at hsplit
    have hbadnonneg : 0 ≤ ∑ D ∈ bad, S.q g W D :=
      Finset.sum_nonneg fun D hD => S.q_nonneg g W D
    linarith
  have hsplit (f : Bin 𝒯 i → ℝ) :
      (∑ D ∈ B, f D) + (∑ D ∈ bad, f D) = ∑ D, f D := by
    dsimp [B, bad]
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun D : Bin 𝒯 i => D ∈ S.pretrimBins W g)]
    simp
  have hqinone := qin_sum_one S W g hret
  have hqinbad : ∑ D ∈ bad, S.qin W g D = 0 := by
    apply Finset.sum_eq_zero
    intro D hD
    have hnot : D ∉ B := (Finset.mem_filter.mp hD).2
    simp [SliceSolver.qin, B, hnot]
  have hqinB : ∑ D ∈ B, S.qin W g D = 1 := by
    have h := hsplit (fun D => S.qin W g D)
    rw [hqinbad, hqinone] at h
    linarith
  have hqnot : ∑ D ∈ bad, S.q g W D = 1 - Q := by
    have h := hsplit (fun D => S.q g W D)
    rw [S.q_sum g W] at h
    change Q + (∑ D ∈ bad, S.q g W D) = 1 at h
    linarith
  have hqin_ge (D : Bin 𝒯 i) (hD : D ∈ B) :
      S.q g W D ≤ S.qin W g D := by
    rw [SliceSolver.qin, if_pos hD]
    apply (le_div_iff₀ hret).2
    have hq := S.q_nonneg g W D
    nlinarith [mul_le_mul_of_nonneg_left hQle hq]
  have hBabs : ∑ D ∈ B, |S.q g W D - S.qin W g D| =
      ∑ D ∈ B, (S.qin W g D - S.q g W D) := by
    apply Finset.sum_congr rfl
    intro D hD
    rw [abs_of_nonpos (sub_nonpos.mpr (hqin_ge D hD))]
    ring
  have hbadabs : ∑ D ∈ bad, |S.q g W D - S.qin W g D| =
      ∑ D ∈ bad, S.q g W D := by
    apply Finset.sum_congr rfl
    intro D hD
    have hnot : D ∉ B := (Finset.mem_filter.mp hD).2
    have hzero : S.qin W g D = 0 := by simp [SliceSolver.qin, B, hnot]
    rw [hzero]
    simp only [sub_zero]
    exact abs_of_nonneg (S.q_nonneg g W D)
  have hqin_l1 :
      (∑ D, |S.q g W D - S.qin W g D|) = 2 * (1 - Q) := by
    calc
      (∑ D, |S.q g W D - S.qin W g D|) =
          (∑ D ∈ B, |S.q g W D - S.qin W g D|) +
            (∑ D ∈ bad, |S.q g W D - S.qin W g D|) := (hsplit _).symm
      _ = (∑ D ∈ B, (S.qin W g D - S.q g W D)) +
            (∑ D ∈ bad, S.q g W D) := by rw [hBabs, hbadabs]
      _ = 2 * (1 - Q) := by
            rw [Finset.sum_sub_distrib, hqinB]
            have hBq : (∑ D ∈ B, S.q g W D) = Q := rfl
            rw [hBq, hqnot]
            ring
  have hpoint (y : Fin (T.S.N k)) :
      |S.oddMarginal g W y - ∑ D, S.qin W g D * S.U g W D y| ≤
        ∑ D, |S.q g W D - S.qin W g D| * S.U g W D y := by
    unfold SliceSolver.oddMarginal
    have heq : (∑ D, S.q g W D * S.U g W D y) -
        (∑ D, S.qin W g D * S.U g W D y) =
          ∑ D, (S.q g W D - S.qin W g D) * S.U g W D y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro D hD
      ring
    rw [heq]
    calc
      |∑ D, (S.q g W D - S.qin W g D) * S.U g W D y| ≤
          ∑ D, |(S.q g W D - S.qin W g D) * S.U g W D y| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ D, |S.q g W D - S.qin W g D| * S.U g W D y := by
            apply Finset.sum_congr rfl
            intro D hD
            rw [abs_mul, abs_of_nonneg (S.U_nonneg g W D y)]
  have hL1 :
      (∑ y, |S.oddMarginal g W y - ∑ D, S.qin W g D * S.U g W D y|) ≤
        ∑ D, |S.q g W D - S.qin W g D| := by
    calc
      _ ≤ ∑ y, ∑ D, |S.q g W D - S.qin W g D| * S.U g W D y :=
          Finset.sum_le_sum fun y hy => hpoint y
      _ = ∑ D, |S.q g W D - S.qin W g D| * ∑ y, S.U g W D y := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro D hD
            rw [Finset.mul_sum]
      _ = ∑ D, |S.q g W D - S.qin W g D| := by simp [S.U_sum]
  rw [hqin_l1] at hL1
  have hQbound : 1 - Q ≤
      (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
    have h := retained_bin_mass S W g hgood
    change 1 - (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤ Q at h
    linarith
  calc
    (1 / 2 : ℝ) * ∑ y,
        |S.oddMarginal g W y - ∑ D, S.qin W g D * S.U g W D y| ≤
      (1 / 2 : ℝ) * (2 * (1 - Q)) := by
        exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
    _ ≤ (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
        nlinarith [hQbound]

private theorem good_raw_numerator_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i) :
    (∑ y, ∑ W, (S.recLaw p).w W *
      (if S.AllGood W then S.oddMarginal g W y else 0)) =
      (S.recLaw p).pr S.AllGood := by
  classical
  rw [Finset.sum_comm]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro W hW
  by_cases hg : S.AllGood W
  · have hleft : ∑ y, (S.recLaw p).w W * S.oddMarginal g W y =
        (S.recLaw p).w W := by
      rw [← Finset.mul_sum, marginal_sum_one, mul_one]
    simp only [hg, if_pos]
    exact hleft
  · simp [hg]

private theorem bad_raw_numerator_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i) :
    (∑ y, ∑ W, (S.recLaw p).w W *
      (if S.AllGood W then 0 else S.oddMarginal g W y)) =
      (S.recLaw p).pr (fun W => ¬ S.AllGood W) := by
  classical
  rw [Finset.sum_comm]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro W hW
  by_cases hg : S.AllGood W
  · simp [hg]
  · have hleft : ∑ y, (S.recLaw p).w W * S.oddMarginal g W y =
        (S.recLaw p).w W := by
      rw [← Finset.mul_sum, marginal_sum_one, mul_one]
    simp only [hg, if_neg, not_false_eq_true]
    exact hleft

private theorem good_trim_numerator_sum_one {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (hret : ∀ W, S.AllGood W →
      0 < ∑ D ∈ S.pretrimBins W g, S.q g W D) :
    (∑ y, ∑ W, (S.recLaw p).w W *
      (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0)) =
      (S.recLaw p).pr S.AllGood := by
  classical
  rw [Finset.sum_comm]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro W hW
  by_cases hg : S.AllGood W
  · have hleft : ∑ y, (S.recLaw p).w W *
        (∑ D, S.qin W g D * S.U g W D y) = (S.recLaw p).w W := by
      rw [← Finset.mul_sum, low_inner_sum_one S W g (hret W hg), mul_one]
    simp only [hg, if_pos]
    exact hleft
  · simp [hg]

/-- P14.2f: conditioning on the test event and pretrimming bins changes the
unrestricted mean by the stated low-mode total-variation amount. -/
theorem low_mode_tv {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (F : SolverFamily 𝒯 mesh)
    (hconst : HeightConstantContract κ) (hpre : PretrimFacts F)
    (p : ProfileFixedPoint F) :
    ∀ i, 𝒯.mode = .lowCluster → ∀ g : Group 𝒯 i,
      (1 / 2 : ℝ) * ∑ y,
        |rawWeight F p.point i g y -
          (mesh.paramLaw p.point i).w y| ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) +
        2 * (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  classical
  intro i hlow g
  let S := (F.solverAt i).solver
  let P := S.recLaw p.point
  let e := P.pr S.AllGood
  let badMass := P.pr (fun W => ¬ S.AllGood W)
  let η := (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h)
  let raw (y : Fin (T.S.N k)) := S.oddMean p.point g y
  let goodNum (y : Fin (T.S.N k)) :=
    ∑ W, P.w W * (if S.AllGood W then S.oddMarginal g W y else 0)
  let badNum (y : Fin (T.S.N k)) :=
    ∑ W, P.w W * (if S.AllGood W then 0 else S.oddMarginal g W y)
  let trimNum (y : Fin (T.S.N k)) :=
    ∑ W, P.w W *
      (if S.AllGood W then ∑ D, S.qin W g D * S.U g W D y else 0)
  let condRaw (y : Fin (T.S.N k)) := goodNum y / e
  have he : 0 < e := hpre.good_positive i p.point
  have hret (W : ∀ r, S.Val r) (hg : S.AllGood W) :
      0 < ∑ D ∈ S.pretrimBins W g, S.q g W D :=
    hpre.retained_positive i W g hg
  have hnotGoodEq : badMass = P.pr (fun W => ∃ v, ¬ S.Hgood v W) := by
    dsimp [badMass]
    congr 1
    funext W
    simp [SliceSolver.AllGood]
  have hbad : badMass ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) := by
    rw [hnotGoodEq]
    exact S.Hgood_bad p.point
  have hcomp := finLaw_pr_compl P S.AllGood
  have hmass : e + badMass = 1 := by
    simpa [e, badMass] using finLaw_pr_compl P S.AllGood
  have hrawsplit (y : Fin (T.S.N k)) : raw y = goodNum y + badNum y := by
    unfold raw SliceSolver.oddMean FinLaw.E
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun W => S.AllGood W)]
    simp [P, goodNum, badNum, Finset.sum_filter]
  have hgoodnumsum : ∑ y, goodNum y = e := by
    dsimp [goodNum, e]
    exact good_raw_numerator_sum_one S p.point g
  have hbadnumsum : ∑ y, badNum y = badMass := by
    dsimp [badNum, badMass]
    exact bad_raw_numerator_sum S p.point g
  have htrimnumsum : ∑ y, trimNum y = e := by
    dsimp [trimNum, e]
    exact good_trim_numerator_sum_one S p.point g hret
  have hcondsum : ∑ y, condRaw y = 1 := by
    dsimp [condRaw]
    rw [← Finset.sum_div, hgoodnumsum, div_self (ne_of_gt he)]
  have hgoodnum_nonneg (y : Fin (T.S.N k)) : 0 ≤ goodNum y := by
    dsimp [goodNum]
    apply Finset.sum_nonneg
    intro W hW
    by_cases hg : S.AllGood W
    · simp [hg]
      exact mul_nonneg (P.nonneg W) (marginal_nonneg S g W y)
    · simp [hg]
  have hbadnum_nonneg (y : Fin (T.S.N k)) : 0 ≤ badNum y := by
    dsimp [badNum]
    apply Finset.sum_nonneg
    intro W hW
    by_cases hg : S.AllGood W
    · simp [hg]
    · simp [hg]
      exact mul_nonneg (P.nonneg W) (marginal_nonneg S g W y)
  have hcond_nonneg (y : Fin (T.S.N k)) : 0 ≤ condRaw y :=
    div_nonneg (hgoodnum_nonneg y) he.le
  have hGfactor (y : Fin (T.S.N k)) : goodNum y = e * condRaw y := by
    dsimp [condRaw]
    field_simp [ne_of_gt he]
  have hmass' : e = 1 - badMass := by linarith [hmass]
  have hfirst (y : Fin (T.S.N k)) :
      raw y - condRaw y = badNum y - badMass * condRaw y := by
    rw [hrawsplit y, hGfactor y, hmass']
    ring
  have hA : (1 / 2 : ℝ) * ∑ y, |raw y - condRaw y| ≤ badMass := by
    have hpoint (y : Fin (T.S.N k)) :
        |raw y - condRaw y| ≤ badNum y + badMass * condRaw y := by
      rw [hfirst y]
      calc
        |badNum y - badMass * condRaw y| ≤
            |badNum y - 0| + |0 - badMass * condRaw y| := abs_sub_le _ _ _
        _ = badNum y + badMass * condRaw y := by
            simp only [sub_zero, zero_sub, abs_neg]
            rw [abs_of_nonneg (hbadnum_nonneg y),
              abs_of_nonneg (mul_nonneg (finLaw_pr_nonneg P _) (hcond_nonneg y))]
    have hsum : ∑ y, (badNum y + badMass * condRaw y) = 2 * badMass := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbadnumsum, hcondsum]
      ring
    calc
      (1 / 2 : ℝ) * ∑ y, |raw y - condRaw y| ≤
          (1 / 2 : ℝ) * ∑ y, (badNum y + badMass * condRaw y) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy => hpoint y)
              (by norm_num)
      _ = badMass := by rw [hsum]; ring
  have hper (W : ∀ r, S.Val r) (hg : S.AllGood W) :
      ∑ y, |S.oddMarginal g W y -
        ∑ D, S.qin W g D * S.U g W D y| ≤ 2 * η := by
    have h := good_history_trim_tv S W g hg (hret W hg)
    dsimp [η]
    nlinarith
  have hGH (y : Fin (T.S.N k)) :
      goodNum y - trimNum y =
        ∑ W, if S.AllGood W then
          P.w W * (S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y) else 0 := by
    dsimp [goodNum, trimNum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hg : S.AllGood W <;> simp [hg] <;> ring
  have hcondTrim (y : Fin (T.S.N k)) :
      condRaw y - S.lowOut p.point g y = (goodNum y - trimNum y) / e := by
    dsimp [condRaw, goodNum, trimNum, e]
    unfold SliceSolver.lowOut
    field_simp [ne_of_gt he]
    ring
  have hBpoint (y : Fin (T.S.N k)) :
      |condRaw y - S.lowOut p.point g y| ≤
        (∑ W, if S.AllGood W then P.w W *
          |S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y| else 0) / e := by
    rw [hcondTrim y, hGH y]
    have habs :
        |∑ W, if S.AllGood W then
          P.w W * (S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y) else 0| ≤
        ∑ W, if S.AllGood W then P.w W *
          |S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y| else 0 := by
      calc
        |∑ W, if S.AllGood W then
            P.w W * (S.oddMarginal g W y -
              ∑ D, S.qin W g D * S.U g W D y) else 0| ≤
            ∑ W, |if S.AllGood W then
              P.w W * (S.oddMarginal g W y -
                ∑ D, S.qin W g D * S.U g W D y) else 0| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ W, if S.AllGood W then P.w W *
            |S.oddMarginal g W y -
              ∑ D, S.qin W g D * S.U g W D y| else 0 := by
                apply Finset.sum_le_sum
                intro W hW
                by_cases hg : S.AllGood W
                · simp only [hg, if_pos, abs_mul, abs_of_nonneg (P.nonneg W)]
                  exact le_rfl
                · simp [hg]
    have heabs : |e| = e := abs_of_pos he
    calc
      |(∑ W, if S.AllGood W then
          P.w W * (S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y) else 0) / e| =
        |∑ W, if S.AllGood W then
          P.w W * (S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y) else 0| / e := by
              rw [abs_div, heabs]
      _ ≤ (∑ W, if S.AllGood W then P.w W *
          |S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y| else 0) / e :=
              div_le_div_of_nonneg_right habs he.le
  have hB : (1 / 2 : ℝ) *
      ∑ y, |condRaw y - S.lowOut p.point g y| ≤ η := by
    have hnum :
        (∑ W, if S.AllGood W then P.w W *
          ∑ y, |S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y| else 0) ≤ 2 * η * e := by
      calc
        _ ≤ ∑ W, if S.AllGood W then P.w W * (2 * η) else 0 := by
          apply Finset.sum_le_sum
          intro W hW
          by_cases hg : S.AllGood W
          · simp only [hg, if_pos]
            exact mul_le_mul_of_nonneg_left (hper W hg) (P.nonneg W)
          · simp [hg]
        _ = 2 * η * e := by
          have hgoodmass : (∑ W, if S.AllGood W then P.w W else 0) = e := rfl
          calc
            (∑ W, if S.AllGood W then P.w W * (2 * η) else 0) =
                ∑ W, (if S.AllGood W then P.w W else 0) * (2 * η) := by
                  apply Finset.sum_congr rfl
                  intro W hW
                  split_ifs <;> ring
            _ = (∑ W, if S.AllGood W then P.w W else 0) * (2 * η) :=
              (Finset.sum_mul (s := Finset.univ)
                (f := fun W => if S.AllGood W then P.w W else 0)
                (a := 2 * η)).symm
            _ = 2 * η * e := by rw [hgoodmass]; ring
    have hl1 : ∑ y, |condRaw y - S.lowOut p.point g y| ≤ 2 * η := by
      calc
        _ ≤ ∑ y, (∑ W, if S.AllGood W then P.w W *
          |S.oddMarginal g W y -
            ∑ D, S.qin W g D * S.U g W D y| else 0) / e :=
              Finset.sum_le_sum fun y hy => hBpoint y
        _ = (∑ W, if S.AllGood W then P.w W *
            ∑ y, |S.oddMarginal g W y -
              ∑ D, S.qin W g D * S.U g W D y| else 0) / e := by
                rw [← Finset.sum_div]
                congr 1
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro W hW
                by_cases hg : S.AllGood W
                · simp only [hg, if_pos]
                  rw [Finset.mul_sum]
                · simp [hg]
        _ ≤ (2 * η * e) / e := div_le_div_of_nonneg_right hnum he.le
        _ = 2 * η := by field_simp [ne_of_gt he]
    nlinarith [hl1]
  have htriangle : (1 / 2 : ℝ) *
      ∑ y, |raw y - S.lowOut p.point g y| ≤ badMass + η := by
    calc
      (1 / 2 : ℝ) * ∑ y, |raw y - S.lowOut p.point g y| ≤
      (1 / 2 : ℝ) *
            (∑ y, |raw y - condRaw y| + ∑ y, |condRaw y - S.lowOut p.point g y|) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_le_sum fun y hy => abs_sub_le _ _ _
      _ = (1 / 2 : ℝ) * ∑ y, |raw y - condRaw y| +
            (1 / 2 : ℝ) * ∑ y, |condRaw y - S.lowOut p.point g y| := by ring
      _ ≤ badMass + η := add_le_add hA hB
  have hη : 0 ≤ η := by positivity
  have hfixedlow (y : Fin (T.S.N k)) :
      (mesh.paramLaw p.point i).w y = S.lowOut p.point g y := by
    rw [p.fixed_profile i g y]
    simp [S, outputWeight, hlow]
  have hrawEq (y : Fin (T.S.N k)) : rawWeight F p.point i g y = raw y := rfl
  have hTV : (1 / 2 : ℝ) * ∑ y,
      |rawWeight F p.point i g y - (mesh.paramLaw p.point i).w y| ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) + 2 * η := by
    calc
      _ = (1 / 2 : ℝ) * ∑ y, |raw y - S.lowOut p.point g y| := by
            apply congrArg (fun z => (1 / 2 : ℝ) * z)
            apply Finset.sum_congr rfl
            intro y hy
            rw [hrawEq y, hfixedlow y]
      _ ≤ badMass + η := htriangle
      _ ≤ Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) + 2 * η := by
            linarith [hbad, hη]
  calc
    (1 / 2 : ℝ) * ∑ y,
        |rawWeight F p.point i g y - (mesh.paramLaw p.point i).w y| ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) + 2 * η := hTV
    _ = Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) +
        2 * (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
          dsimp [η]
          ring

/-- Active mesh vertices at the selected profile. -/
noncomputable def activeVertices {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (p : mesh.Param) : Finset mesh.V :=
  Finset.univ.filter fun v => 0 < mesh.wt v p

/-- The union of the cleaned corners used at the selected profile. -/
noncomputable def profileEnvelope {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (p : mesh.Param) (i : Fin 𝒯.m) :
    Finset (Fin (T.S.N k)) :=
  (activeVertices p).biUnion fun v => mesh.corner v i

/-- All conclusions of Proposition 14.2 at one profile point. -/
structure BalancedProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} (hclean : MeshCleaned mesh) where
  solvers : SolverFamily 𝒯 mesh
  fixedPoint : ProfileFixedPoint solvers
  cap : ∀ i y, (mesh.paramLaw fixedPoint.point i).w y ≤ 11 / (𝒯.P i).M
  corner_clean : ∀ v i, v ∈ activeVertices fixedPoint.point →
    CleanProps 𝒯 i (mesh.paramLaw fixedPoint.point) (mesh.corner v i)
  envelope_subset : ∀ i, profileEnvelope fixedPoint.point i ⊆ (𝒯.P i).X
  envelope_degree : ∀ i x, x ∈ profileEnvelope fixedPoint.point i →
    OwnDegOK 𝒯 i (mesh.paramLaw fixedPoint.point i) x
  envelope_other_degree : ∀ i j, j ≠ i → ∀ x ∈ profileEnvelope fixedPoint.point i,
    |deg (T.S.E k) 𝒯.c (mesh.paramLaw fixedPoint.point j).w x - 1 / 2| ≤ 3 * bstar T k
  envelope_row_tail : ∀ i j, ∀ x ∈ profileEnvelope fixedPoint.point i,
    RowTailRelaxed (T.S.E k) 𝒯.c (mesh.paramLaw fixedPoint.point j).w
      (𝒯.P i).X (T.S.n k) κ.ξ x
  low_tv : ∀ i, 𝒯.mode = .lowCluster → ∀ g : Group 𝒯 i,
    (1 / 2 : ℝ) * ∑ y,
      |rawWeight solvers fixedPoint.point i g y -
        (mesh.paramLaw fixedPoint.point i).w y| ≤
      Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14)) +
        2 * (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h)

/-- Proposition 14.2: balanced patch profiles for every mesh and solver
family in a valid cluster tiling. -/
theorem balanced_profiles (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) (hinit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 → 𝒯.mode.isCluster →
      ∀ (mesh : Mesh 𝒯) (hclean : MeshCleaned mesh) (_domain : MeshProfileDomain mesh)
        (ready : MeshReady mesh),
        Nonempty (BalancedProfile (𝒯 := 𝒯) (mesh := mesh) hclean) := by
  have hsolver := internal_slice_solver κ hκ hconst T hinit
  have hscales := patch_scales κ hκ T
  filter_upwards [hsolver, hscales] with k hsolver hscales
  intro 𝒯 h𝒯 hcluster mesh hclean _domain ready
  classical
  let F : SolverFamily 𝒯 mesh := ⟨fun i => Classical.choice (hsolver 𝒯 h𝒯 hcluster mesh hclean ready i)⟩
  have hscale : ∀ i, PatchScales 𝒯 i := hscales 𝒯 h𝒯 hcluster
  have hpre : PretrimFacts F := pretrim_well_defined F hκ hconst hscale
  have hcont : OutputContinuous F := output_continuous F hpre
  have hout : OutputLawFacts F := output_in_capped_domain F hκ hscale hpre
  obtain ⟨fixed⟩ := fixed_point _domain F hcont hpre hout
  have hcap := active_price_cap F hpre fixed
  have htv := low_mode_tv F hconst hpre fixed
  refine ⟨{
    solvers := F
    fixedPoint := fixed
    cap := hcap
    corner_clean := ?_
    envelope_subset := ?_
    envelope_degree := ?_
    envelope_other_degree := ?_
    envelope_row_tail := ?_
    low_tv := htv
  }⟩
  · intro v i hv
    apply hclean v fixed.point i
    simpa [activeVertices] using hv
  · intro i x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).sub hxv
  · intro i x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).degOwn x hxv
  · intro i j hij x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).degOther j hij x hxv
  · intro i j x hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hxv⟩
    exact (hclean v fixed.point i (by simpa [activeVertices] using hv)).rowTail j x hxv

/-- L14.3: finite low-mode primitive data at every parameter point. -/
theorem finite_low_mode_data (κ : CConsts) (hκ : κ.Admissible)
    (hconst : HeightConstantContract κ) (T : Stage) (hinit : InitDisc T κ.η0) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k), Tiling.Valid 𝒯 →
      𝒯.mode = .lowCluster → ∀ mesh : Mesh 𝒯, MeshCleaned mesh → MeshReady mesh →
        ∀ i : Fin 𝒯.m, ∀ p : mesh.Param,
          ∃ S : SolverWitness (𝒯 := 𝒯) (i := i) (mesh := mesh),
            (((Finset.univ.filter fun W =>
              0 < (S.solver.recLaw p).w W).card : ℕ) : ℝ) ≤
              Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  have hsolver := internal_slice_solver κ hκ hconst T hinit
  filter_upwards [hsolver] with k hsolver
  intro 𝒯 h𝒯 hlow mesh hclean ready i p
  have hcluster : 𝒯.mode.isCluster := by
    rw [hlow]
    simp [Mode.isCluster]
  obtain ⟨S⟩ := hsolver 𝒯 h𝒯 hcluster mesh hclean ready i
  refine ⟨S, ?_⟩
  exact S.solver.low_support hlow p

end HypercubeRamsey.S14
