import HypercubeRamsey.S15.Defs

/-! L15.1: direct assignment, its mass gates, and its column estimate. -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Filter
open scoped BigOperators

/-- L15.1a (15:21–22): crossing filters preserve the direct row mass. -/
def DirectCrossingClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys =>
        |directCrossingMass PT hPT ys a - 1| >
          Real.exp (20 * (PT.tiling.P (patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- L15.1b (15:23–31): the post-crossing bulk law has a lower-tail bound. -/
def DirectBulkClaim (κ : CConsts) (T : Stage) : Prop :=
  ∃ Cbulk : ℝ, 0 < Cbulk ∧
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys =>
        9 / 10 ≤ directCrossingMass PT hPT ys a ∧
          directBulkMass PT hPT ys a < 3 / 4) ≤
            4 ^ κ.u * ((T.S.n k : ℝ) ^ (-((3 * κ.R : ℕ) : ℝ)) +
              Cbulk * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)))

/-- L15.1c (15:19, 31): full independent row mass is at least one half except with probability `n^-R`. -/
def DirectMassClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys => directRowMass PT hPT ys a < 1 / 2) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- L15.1f output: the direct row formula normalizes to a fractional Hall system. -/
structure DirectCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) where
  sampler : DirectSampler PT hPT
  labels : OddAssignment T k
  positive : sampler.law.w labels ≠ 0
  rows : DirectHallRows (T := T) (k := k) PT.tiling.c
  labels_eq : rows.oddLabel = labels
  row_eq : rows.row = fun a x => directNormalizedRow PT hPT labels a x

/-- L15.1d (15:33–34): the clock sampler avoids every direct row mass failure and is injective. -/
def DirectSamplerClaim (κ : CConsts) (T : Stage) (hDeep : DeepDisc T κ.xs κ.α 0.04) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), Nonempty (DirectSampler PT hPT)

/-- L15.1e (15:36): the `n`th patch-column moment under the clock law is uniformly bounded. -/
def DirectMomentClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), ∀ J : DirectSampler PT hPT,
      ∀ i x, x ∈ PT.envelope i →
        J.law.E (fun ys =>
          patchColumnAverage PT i (directRowWeight PT hPT) ys x ^ (T.S.n k)) ≤
            κ.A0 ^ (T.S.n k)

/-- L15.1f (15:38–40): one clock outcome has all mass gates and all column loads. -/
def DirectCertificateClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), Nonempty (DirectCertificate PT hPT)

/-- L15.1a: the deep-discrepancy crossing-filter estimate. -/
theorem high_direct_crossing_filters (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    DirectCrossingClaim κ T ∧ ClusterCrossingClaim κ T := by
  sorry

/-- L15.1b: bulk lower-tail estimate, using the crossing-filter stage. -/
theorem high_direct_bulk_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T) :
    DirectBulkClaim κ T := by
  sorry

/-- L15.1c: assemble the crossing and bulk estimates into the independent row-mass bound. -/
theorem high_direct_mass_estimate (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T)
    (hBulk : DirectBulkClaim κ T) : DirectMassClaim κ T := by
  sorry

/-- L15.1d: apply the clock sampler to the row-failure predicates. -/
theorem high_direct_clock_injection (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hMass : DirectMassClaim κ T) :
    DirectSamplerClaim κ T hDeep := by
  sorry

/-- L15.1e: scattered-moment estimate under any clock sampler from L15.1d. -/
theorem high_direct_column_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSampler : DirectSamplerClaim κ T hDeep) :
    DirectMomentClaim κ T := by
  sorry

/-- L15.1f: Markov, the union bound, and the mass gates yield a direct Hall certificate. -/
theorem high_direct_load_existence (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSampler : DirectSamplerClaim κ T hDeep)
    (hMoment : DirectMomentClaim κ T) : DirectCertificateClaim κ T := by
  sorry

/-- Hall assembly retains the sampler support and normalized-row identity. -/
theorem direct_certificate_to_cube {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (C : DirectCertificate PT hPT) :
    ∃ P : FinLaw (OddAssignment T k), P = directRawLaw PT hPT ∧
      CubeIn T k PT.tiling.c ∧ C.sampler.rawLaw = directRawLaw PT hPT ∧
      C.sampler.law.w C.labels ≠ 0 ∧ C.rows.oddLabel = C.labels ∧
      C.rows.row = fun a x => directNormalizedRow PT hPT C.labels a x := by
  have hRows := rows_to_cube PT.tiling.c C.rows
  exact ⟨directRawLaw PT hPT, rfl, hRows.1, C.sampler.rawLaw_eq,
    C.positive, C.labels_eq, C.row_eq⟩

/-- L15.1 (`lem:high-direct-assignment`, 15:8–41): every valid high-direct profiled tiling gives a cube. -/
theorem high_direct (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode = .highDirect → CubeIn T k PT.tiling.c := by
  have hCross := high_direct_crossing_filters κ hκ T hDeep
  have hBulk := high_direct_bulk_lower_tail κ hκ T hDeep hCross.1
  have hMass := high_direct_mass_estimate κ hκ T hDeep hCross.1 hBulk
  have hSampler := high_direct_clock_injection κ hκ T hDeep hMass
  have hMoment := high_direct_column_moment κ hκ T hDeep hSampler
  have hFinal := high_direct_load_existence κ hκ T hDeep hSampler hMoment
  filter_upwards [hFinal] with k hk
  intro PT hPT hmode
  obtain ⟨C⟩ := hk PT hPT hmode
  obtain ⟨_, _, hCube, _, _, _, _⟩ := direct_certificate_to_cube C
  exact hCube

end HypercubeRamsey.S15
