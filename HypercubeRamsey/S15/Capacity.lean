import HypercubeRamsey.S15.Defs

/-! Physical-bin buckets and touching certificate charges (section 15, lines 129–150). -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Classical
open scoped BigOperators

noncomputable def clusterBinProbability {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) : ℝ :=
  ∑ D' : clusterBinType g, if D'.1 = D then
    (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' else 0

noncomputable def clusterCapacityAtom {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) (y : Fin (T.S.N k)) : ℝ :=
  (PT.tiling.P g.1.1).h * ∑ D' : clusterBinType g, if D'.1 = D then
    (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) D' y else 0

noncomputable def clusterBucketWidth {N : ℕ} (D : Finset (Fin N)) (j : ℕ) : ℝ :=
  (D.card : ℝ) ^ (-0.5 : ℝ) * (2 : ℝ) ^ (-(j : ℤ))

noncomputable def clusterCapacityBucket {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (D : Finset (Fin (T.S.N k)))
    (y : Fin (T.S.N k)) (j : ℕ) : Finset (ClusterGroupIndex PT) :=
  Finset.univ.filter fun g => clusterBucketWidth D j / 2 < clusterCapacityAtom PT hPT hm W g D y ∧
    clusterCapacityAtom PT hPT hm W g D y ≤ clusterBucketWidth D j

noncomputable def clusterBucketMean {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (D : Finset (Fin (T.S.N k)))
    (y : Fin (T.S.N k)) (j : ℕ) : ℝ :=
  ∑ g ∈ clusterCapacityBucket PT hPT hm W D y j,
    clusterBinProbability PT hPT hm W g D * clusterCapacityAtom PT hPT hm W g D y

noncomputable def clusterCertificateSize {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (D : Finset (Fin (T.S.N k)))
    (y : Fin (T.S.N k)) (j : ℕ) : ℕ :=
  ⌊(κ.Kp * clusterBucketMean PT hPT hm W D y j +
    κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) / clusterBucketWidth D j⌋₊ + 1

def clusterCapacityAvoided {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT) : Prop :=
  ∀ i (D : Bin PT.tiling i) y, y ∈ D.1 → ∀ j (A : Finset (ClusterGroupIndex PT)),
    A ⊆ clusterCapacityBucket PT hPT hm W D.1 y j →
    A.card = clusterCertificateSize PT hPT hm W D.1 y j →
      ¬ ∀ g ∈ A, (B g).1 = D.1

/-- Conditional charge touching a group pinned to this physical bin, summed over its columns. -/
noncomputable def clusterPinnedCapacityCharge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (D : Finset (Fin (T.S.N k)))
    (g : ClusterGroupIndex PT) : ℝ :=
  ∑ y ∈ D, ∑' j : ℕ,
    ∑ A ∈ (clusterCapacityBucket PT hPT hm W D y j).powerset,
      if g ∈ A ∧ A.card = clusterCertificateSize PT hPT hm W D y j then
        (2 : ℝ) ^ A.card * (∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D) else 0

end HypercubeRamsey.S15
