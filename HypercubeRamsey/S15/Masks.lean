import HypercubeRamsey.S15.Defs

/-! Fixed removal masks and the nonnegative integrals in section 15, lines 183–219. -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Classical
open scoped BigOperators

def clusterCoreNear {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (a b : EvenPosition T k) : Prop :=
  (hammingDist (outsideWord PT hPT i a.1) (outsideWord PT hPT i b.1) : ℝ) ≤ 4 ∧
  (hammingDist (internalWord PT hPT i a.1) (internalWord PT hPT i b.1) : ℝ) ≤
    100 * κ.ρ * (PT.tiling.P i).h

def clusterCrossingNear {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (a b : EvenPosition T k) : Prop :=
  (hammingDist a.1 b.1 : ℝ) ≤ (T.S.n k : ℝ) ^ (2 * κ.ι)

/-- The crossing graph is formed before any core-bin removals. -/
def clusterCrossingEdge {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (vs : Fin (T.S.n k) → EvenPosition T k)
    (G : Finset (Fin (T.S.n k))) (r t : Fin (T.S.n k)) : Prop :=
  r ∉ G ∧ t ∉ G ∧ r ≠ t ∧ clusterCrossingNear PT (vs r) (vs t)

noncomputable def clusterCrossingNonisolated {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (vs : Fin (T.S.n k) → EvenPosition T k)
    (G : Finset (Fin (T.S.n k))) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun r => ∃ t, clusterCrossingEdge PT vs G r t

/-- Vertices minus components, with one least vertex representing each component. -/
noncomputable def clusterCrossingRank {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (vs : Fin (T.S.n k) → EvenPosition T k)
    (G : Finset (Fin (T.S.n k))) : ℕ :=
  T.S.n k - (Finset.univ.filter fun r : Fin (T.S.n k) =>
    ∀ t, Relation.ReflTransGen (clusterCrossingEdge PT vs G) t r → r ≤ t).card

/-- Conservative exponential slack, sufficient for crossing forests and crossing-bin repeats. -/
noncomputable def clusterCrossingFraction (T : Stage) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(T.S.n k : ℤ)) * Real.exp (0.01 * T.S.n k)

/-- Rank tail under independent uniform patch positions, including the empty-patch convention. -/
noncomputable def clusterCrossingRankTail {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (G : Finset (Fin (T.S.n k))) (j : ℕ) : ℝ :=
  (∑ vs : Fin (T.S.n k) → EvenPosition T k,
    if (∀ r, vs r ∈ evenPatchPositions PT.tiling i) ∧ j ≤ clusterCrossingRank PT vs G
    then (1 : ℝ) else 0) / ((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k)

/-- A fixed position tuple and its geometric, core-bin and crossing-bin removal masks. -/
structure ClusterMask {κ : CConsts} {T : Stage} {k : ℕ} (PT : ProfiledTiling κ T k) where
  positions : Fin (T.S.n k) → EvenPosition T k
  geometric : Finset (Fin (T.S.n k))
  coreBins : Finset (Fin (T.S.n k))
  crossingBins : Finset (Fin (T.S.n k) × OddPosition T k)

noncomputable instance clusterMaskFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) : Fintype (ClusterMask PT) :=
  Fintype.ofEquiv
    ((Fin (T.S.n k) → EvenPosition T k) × Finset (Fin (T.S.n k)) ×
      Finset (Fin (T.S.n k)) × Finset (Fin (T.S.n k) × OddPosition T k))
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      invFun := fun M => (M.positions, M.geometric, M.coreBins, M.crossingBins)
      left_inv := by intro p; rfl
      right_inv := by intro M; cases M; rfl }

noncomputable def clusterKeptRows {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (M : ClusterMask PT) : Finset (Fin (T.S.n k)) :=
  Finset.univ \ (M.geometric ∪ M.coreBins)

/-- Groups sampled for internal and bulk labels; counterfactual bins in `σ` are integrated out. -/
noncomputable def clusterCoreGroups {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterGroupIndex PT) :=
  (Finset.univ.filter fun b : OddPosition T k =>
    Adjacent a b ∧ patchAt PT hPT b.1 = patchAt PT hPT a.1).image
      (clusterGroupIndexAt PT hPT hm)

/-- Crossing queries remaining after the geometric crossing-graph deletion. -/
noncomputable def clusterAllowedCrossings {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (M : ClusterMask PT) :
    Finset (Fin (T.S.n k) × OddPosition T k) :=
  Finset.univ.filter fun q => q.1 ∈ clusterKeptRows M ∧
    q.1 ∉ clusterCrossingNonisolated PT M.positions M.geometric ∧
    q.2 ∈ clusterCrossingNeighbours PT hPT (M.positions q.1)

/-- A fixed order of physical queries: row number, then binary word number. -/
noncomputable def clusterQueryOrder {T : Stage} {k : ℕ}
    (q : Fin (T.S.n k) × OddPosition T k) : ℕ :=
  q.1.val * 2 ^ (T.S.n k) + ∑ j : Fin (T.S.n k), if q.2.1 j then 2 ^ j.val else 0

def ClusterMaskGeometry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (M : ClusterMask PT) : Prop :=
  (∀ r, M.positions r ∈ evenPatchPositions PT.tiling i) ∧
  (∀ r, r ∈ M.geometric ↔ ∃ t, t < r ∧ clusterCoreNear PT hPT i (M.positions t) (M.positions r)) ∧
  Disjoint M.geometric M.coreBins ∧ M.crossingBins ⊆ clusterAllowedCrossings PT hPT M

/-- Necessary earlier core-bin repeat, including earlier rows already removed by bin repeats. -/
def clusterCoreRepeat {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (B : ClusterBinAssignment PT) (r : Fin (T.S.n k)) : Prop :=
  ∃ t, t < r ∧ t ∉ M.geometric ∧
    ∃ g ∈ clusterCoreGroups PT hPT hm (M.positions r),
    ∃ g' ∈ clusterCoreGroups PT hPT hm (M.positions t), (B g).1 = (B g').1

def clusterCrossingRepeat {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (B : ClusterBinAssignment PT)
    (q : Fin (T.S.n k) × OddPosition T k) : Prop :=
  ∃ p ∈ clusterAllowedCrossings PT hPT M, clusterQueryOrder p < clusterQueryOrder q ∧
    (B (clusterGroupIndexAt PT hPT hm p.2)).1 = (B (clusterGroupIndexAt PT hPT hm q.2)).1

def ClusterMaskConsistent {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) (B : ClusterBinAssignment PT) : Prop :=
  if PT.tiling.mode = .highSmall then
    (∀ r, r ∈ M.coreBins ↔ r ∉ M.geometric ∧ clusterCoreRepeat PT hPT hm M B r) ∧
    (∀ q, q ∈ M.crossingBins ↔ q ∈ clusterAllowedCrossings PT hPT M ∧
      clusterCrossingRepeat PT hPT hm M B q)
  else M.coreBins = ∅ ∧ M.crossingBins = ∅

/-- Product in section 15, lines 199–203, with conditional denominators replaced by nominal ones. -/
noncomputable def clusterKeptProduct {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) : ℝ :=
  (∏ r ∈ clusterKeptRows M,
    ((PT.tiling.P i).M * clusterSigma PT hPT hm W I (M.positions r) x *
      ∏ b ∈ clusterBulkNeighbours PT hPT (M.positions r),
        (let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x
         if 0 < d then hit (T.S.E k) PT.tiling.c x
           (clusterLabelFromInternal (hPT := hPT) hm I b) / d else 0))) *
    ∏ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins,
      (let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)).w x
       if 0 < d then hit (T.S.E k) PT.tiling.c x
         (clusterLabelFromInternal (hPT := hPT) hm I q.2) / d else 0)

noncomputable def clusterMaskedIntegral {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) : ℝ :=
  CS.law.E fun ω => if CS.historyLoad ω ∧ ClusterMaskConsistent PT hPT hm M (CS.bins ω)
    then clusterKeptProduct PT hPT hm i x M (CS.history ω) (CS.internal ω) else 0

/-- After conditional label comparison, before bin comparison: both entering gates remain. -/
noncomputable def clusterAfterLabelIntegral {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) : ℝ :=
  CS.binStage.historyLaw.E fun W => if clusterHistoryLoad PT hPT hm W then
    (CS.binStage.binLaw W).E fun B => if ClusterMaskConsistent PT hPT hm M B then
      (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W)
      else 0 else 0

/-- Kept reference product after reverse integration of removed bin variables. -/
noncomputable def clusterReferenceMean {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) : ℝ :=
  (clusterIndependentBinKernel PT hPT hm W).E fun B =>
    (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W)

noncomputable def clusterCoreRepeatCost {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) : ℝ :=
  (T.S.n k : ℝ) ^ 4 * 4 * Real.exp
    (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) * (PT.tiling.P i).d / (PT.tiling.P i).M

/-- Row caps and the costs of graph and crossing-bin factor deletions, outside the tested integral. -/
noncomputable def clusterMaskPayoff {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (M : ClusterMask PT) : ℝ :=
  4 ^ (T.S.n k) * (2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain i)) ^
    (M.geometric.card + M.coreBins.card) *
    3 ^ (2 * clusterCrossingRank PT M.positions M.geometric * (PT.tiling.P i).ℓ + M.crossingBins.card)

end HypercubeRamsey.S15
