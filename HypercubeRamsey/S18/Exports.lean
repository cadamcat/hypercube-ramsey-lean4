import HypercubeRamsey.S18.Nodes

/-!
# Section 18 exports
-/

namespace HypercubeRamsey
namespace S18

open Filter

/-- C18.F / `partC_main` (PART-C.md §1.3): combine the admissible constants,
profile extraction, the high-mode exports, and C18.Flow. -/
theorem partC_main_proof (T : Stage) (η0 : ℝ) (hη0 : 0 < η0)
    (hInit : InitDisc T η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hClu : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ →
      (δ : ℝ) < min η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop,
        ¬ ClusterWitnessAt (T.orient o) k c ζ δ) : False := by
  obtain ⟨κ, hκ, hκη, hThresholds, hConstants, hDeepκ₁, hDeepκ₂⟩ :=
    exists_late_constants T η0 hη0 hDeep
  have hInitκ : InitDisc T κ.η0 := by simpa [hκη] using hInit
  have hCluκ : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ →
      (δ : ℝ) < min κ.η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop,
        ¬ ClusterWitnessAt (T.orient o) k c ζ δ := by
    intro ζ δ hζ hδ hδ' c o
    apply hClu ζ δ hζ hδ
    simpa [hκη] using hδ'
  have hProfiles := profiled_tiling_exists hκ hConstants T hInitκ hDeep hDeepκ₁ hDeepκ₂ hCluκ
  have hLow := C18_Flow hκ hThresholds hConstants T hInitκ hDeep hDeepκ₁ hDeepκ₂
  have hLowSwap := C18_Flow hκ hThresholds hConstants T.swap
    (orient_init hInitκ true) (orient_deep hDeep true)
    (orient_deep_budget hDeepκ₁ true) (orient_deep_budget hDeepκ₂ true)
  have hDirect := high_direct_cube hκ T hDeepκ₁
  have hDirectSwap := high_direct_cube hκ T.swap
    (orient_deep_budget hDeepκ₁ true)
  have hCluster := high_cluster_cube hκ T hDeepκ₁
  have hClusterSwap := high_cluster_cube hκ T.swap
    (orient_deep_budget hDeepκ₁ true)
  have hContradiction : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hProfiles, hLow, hLowSwap, hDirect, hDirectSwap,
        hCluster, hClusterSwap] with k hProfile hLow0 hLow1 hDirect0 hDirect1 hCluster0 hCluster1
    rcases hProfile with ⟨o, PT, hPT, hCorners, hUniform⟩
    have hCube : CubeIn (T.orient o) k PT.tiling.c := by
      cases o with
      | false =>
        cases hmode : PT.tiling.mode with
        | bounded => exact hLow0 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | lowDirect => exact hLow0 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | highDirect => exact hDirect0 PT hPT hmode
        | lowCluster => exact hLow0 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | highSmall => exact hCluster0 PT hPT (Or.inl hmode)
        | highLarge => exact hCluster0 PT hPT (Or.inr hmode)
      | true =>
        cases hmode : PT.tiling.mode with
        | bounded => exact hLow1 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | lowDirect => exact hLow1 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | highDirect => exact hDirect1 PT hPT hmode
        | lowCluster => exact hLow1 PT hPT (by simp [Mode.isLow, hmode]) hCorners hUniform
        | highSmall => exact hCluster1 PT hPT (Or.inl hmode)
        | highLarge => exact hCluster1 PT hPT (Or.inr hmode)
    cases o with
    | false => exact T.S.no_cube k PT.tiling.c hCube
    | true =>
        have hTranspose : Nonempty ((OAI.HypercubeRamsey.cube (T.S.n k)).Copy
            (OAI.HypercubeRamsey.crossGraph
              (Hits (transposeRel (T.S.E k)) PT.tiling.c))) := by
          simpa [CubeIn, Stage.orient, Stage.swap, BadSeq.swap] using hCube
        exact T.S.no_cube k PT.tiling.c
          (cube_copy_of_transpose (T.S.E k) PT.tiling.c hTranspose)
  rcases hContradiction.exists with ⟨k, hFalse⟩
  exact hFalse

end S18
end HypercubeRamsey
