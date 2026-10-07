import HypercubeRamsey.S15.Masks
import HypercubeRamsey.S15.ClusterNodes_q_s15_c3

namespace HypercubeRamsey.Lane_sol_s15_mask

open HypercubeRamsey.S15 Classical
open scoped BigOperators

theorem nominal_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x y : Fin N) : 0 ≤ normalizedHit E c π x y := by
  unfold normalizedHit
  dsimp only
  split_ifs with h
  · apply div_nonneg _ h.le
    unfold hit
    split_ifs <;> norm_num
  · exact le_rfl

theorem sigma_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ clusterSigma PT hPT hm W I a x := by
  exact (clusterSolver PT hPT hm _).σ_nonneg _ _ _ _

theorem keptProduct_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT) :
    0 ≤ clusterKeptProduct PT hPT hm i x M W I := by
  change 0 ≤ (∏ r ∈ clusterKeptRows M,
    ((PT.tiling.P i).M * clusterSigma PT hPT hm W I (M.positions r) x *
      ∏ b ∈ clusterBulkNeighbours PT hPT (M.positions r),
        normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x
          (clusterLabelFromInternal (hPT := hPT) hm I b))) *
    ∏ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins,
      normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)) x
        (clusterLabelFromInternal (hPT := hPT) hm I q.2)
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro r hr
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sigma_nonneg PT hPT hm W I _ x))
      (Finset.prod_nonneg fun b hb => nominal_nonneg _ _ _ _ _)
  · exact Finset.prod_nonneg fun q hq => nominal_nonneg _ _ _ _ _

theorem payoff_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (M : ClusterMask PT) :
    0 ≤ clusterMaskPayoff PT i M := by
  unfold clusterMaskPayoff
  positivity

noncomputable def orderedMask {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (vs : Fin (T.S.n k) → EvenPosition T k)
    (B : ClusterBinAssignment PT) : ClusterMask PT := by
  let G := Finset.univ.filter fun r =>
    ∃ t, t < r ∧ clusterCoreNear PT hPT i (vs t) (vs r)
  let M₀ : ClusterMask PT := ⟨vs, G, ∅, ∅⟩
  exact if PT.tiling.mode = .highSmall then
    let C := Finset.univ.filter fun r => r ∉ G ∧ clusterCoreRepeat PT hPT hm M₀ B r
    let M₁ : ClusterMask PT := ⟨vs, G, C, ∅⟩
    ⟨vs, G, C,
      (clusterAllowedCrossings PT hPT M₁).filter (clusterCrossingRepeat PT hPT hm M₁ B)⟩
    else M₀

theorem orderedMask_positions {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (vs : Fin (T.S.n k) → EvenPosition T k)
    (B : ClusterBinAssignment PT) : (orderedMask PT hPT hm i vs B).positions = vs := by
  unfold orderedMask
  split_ifs <;> rfl

theorem orderedMask_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (vs : Fin (T.S.n k) → EvenPosition T k)
    (B : ClusterBinAssignment PT) (hvs : ∀ r, vs r ∈ evenPatchPositions PT.tiling i) :
    ClusterMaskGeometry PT hPT i (orderedMask PT hPT hm i vs B) := by
  have hpos := orderedMask_positions PT hPT hm i vs B
  refine ⟨by simpa only [hpos] using hvs, ?_, ?_, ?_⟩
  · intro r
    by_cases hs : PT.tiling.mode = .highSmall <;>
      simp only [orderedMask, hs, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
  · apply Finset.disjoint_left.mpr
    intro r hr hc
    by_cases hs : PT.tiling.mode = .highSmall
    · simp only [orderedMask, hs, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc
      simp only [orderedMask, hs, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
        true_and] at hr
      exact hc.1 hr
    · simp [orderedMask, hs] at hc
  · by_cases hs : PT.tiling.mode = .highSmall
    · intro q hq
      simp only [orderedMask, hs, ↓reduceIte, clusterAllowedCrossings, clusterKeptRows,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact hq.1
    · simp [orderedMask, hs]

theorem orderedMask_consistent {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (vs : Fin (T.S.n k) → EvenPosition T k)
    (B : ClusterBinAssignment PT) :
    ClusterMaskConsistent PT hPT hm (orderedMask PT hPT hm i vs B) B := by
  by_cases hs : PT.tiling.mode = .highSmall
  · simp only [ClusterMaskConsistent, orderedMask, hs, ↓reduceIte,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · simp [ClusterMaskConsistent, orderedMask, hs]

theorem patchAt_of_even_mem {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (a : EvenPosition T k) (ha : a ∈ evenPatchPositions PT.tiling i) :
    patchAt PT hPT a.1 = i := by
  have hmem : a.1 ∈ PT.tiling.leaf i := (Finset.mem_filter.mp ha).2
  exact ((Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).2 i hmem).symm

theorem cap_product {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (f : α → ℝ) (c : ℝ) (h0 : ∀ a, 0 ≤ f a)
    (hc : ∀ a ∈ D, f a ≤ c) :
    (∏ a, f a) ≤ c ^ D.card * ∏ a ∈ Finset.univ \ D, f a := by
  rw [← Finset.prod_sdiff (Finset.subset_univ D)]
  have hp : (∏ a ∈ D, f a) ≤ c ^ D.card := by
    simpa using Finset.prod_le_prod₀ (fun a ha => h0 a) hc
  calc
    (∏ a ∈ Finset.univ \ D, f a) * ∏ a ∈ D, f a ≤
        (∏ a ∈ Finset.univ \ D, f a) * c ^ D.card :=
      mul_le_mul_of_nonneg_left hp (Finset.prod_nonneg fun a ha => h0 a)
    _ = _ := mul_comm _ _

theorem delete_product {α : Type*} [DecidableEq α]
    (S D : Finset α) (f : α → ℝ) (c : ℝ) (hD : D ⊆ S)
    (h0 : ∀ a ∈ S, 0 ≤ f a) (hc : ∀ a ∈ D, f a ≤ c) :
    (∏ a ∈ S, f a) ≤ c ^ D.card * ∏ a ∈ S \ D, f a := by
  rw [← Finset.prod_sdiff hD]
  have hp : (∏ a ∈ D, f a) ≤ c ^ D.card := by
    simpa using Finset.prod_le_prod₀ (fun a ha => h0 a (hD ha)) hc
  calc
    (∏ a ∈ S \ D, f a) * ∏ a ∈ D, f a ≤
        (∏ a ∈ S \ D, f a) * c ^ D.card :=
      mul_le_mul_of_nonneg_left hp (Finset.prod_nonneg fun a ha => h0 a (Finset.mem_sdiff.mp ha).1)
    _ = _ := mul_comm _ _

theorem bulk_crossing_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Disjoint (clusterBulkNeighbours PT hPT a) (clusterCrossingNeighbours PT hPT a) := by
  apply Finset.disjoint_left.mpr
  intro b hb hc
  exact (Finset.mem_filter.mp hc).2.2 (Finset.mem_filter.mp hb).2.2.1

theorem masked_pointwise {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (ω : CS.Outcome)
    (hcap : ∀ a, (PT.tiling.P (patchAt PT hPT a.1)).M * CS.row ω a x ≤
      2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)))
    (hrow : ∀ a, CS.row ω a x ≤ 4 * clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) a x *
      ∏ b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a,
        normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x (CS.label ω b))
    (hhit : ∀ (b : OddPosition T k) y,
      normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x y ≤ 3)
    (hcross : (∏ r ∈ clusterKeptRows M,
      ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r),
        normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x (CS.label ω b)) ≤
      3 ^ (2 * clusterCrossingRank PT M.positions M.geometric * (PT.tiling.P i).ℓ) *
        ∏ q ∈ clusterAllowedCrossings PT hPT M,
          normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)) x (CS.label ω q.2)) :
    (∏ r, (PT.tiling.P i).M * CS.row ω (M.positions r) x) ≤
      clusterMaskPayoff PT i M *
        clusterKeptProduct PT hPT hm i x M (CS.history ω) (CS.internal ω) := by
  let f := fun r => (PT.tiling.P i).M * CS.row ω (M.positions r) x
  let H := fun (b : OddPosition T k) => normalizedHit (T.S.E k) PT.tiling.c
    (PT.π (patchAt PT hPT b.1)) x (CS.label ω b)
  let A := fun r => (PT.tiling.P i).M *
    clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) (M.positions r) x *
      ∏ b ∈ clusterBulkNeighbours PT hPT (M.positions r), H b
  let C := 2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain i)
  let J := 2 * clusterCrossingRank PT M.positions M.geometric * (PT.tiling.P i).ℓ
  have hf0 : ∀ r, 0 ≤ f r := fun r => mul_nonneg (Nat.cast_nonneg _) (CS.row_nonneg ω _ x)
  have hA0 : ∀ r, 0 ≤ A r := by
    intro r
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sigma_nonneg PT hPT hm _ _ _ x))
      (Finset.prod_nonneg fun b hb => nominal_nonneg _ _ _ _ _)
  have hH0 : ∀ b, 0 ≤ H b := fun b => nominal_nonneg _ _ _ _ _
  have hfC : ∀ r ∈ M.geometric ∪ M.coreBins, f r ≤ C := by
    intro r hr
    have heq := patchAt_of_even_mem PT hPT i (M.positions r) (hM.1 r)
    simpa [f, C, heq] using hcap (M.positions r)
  have hrem := cap_product (M.geometric ∪ M.coreBins) f C hf0 hfC
  have hcard : (M.geometric ∪ M.coreBins).card = M.geometric.card + M.coreBins.card :=
    Finset.card_union_of_disjoint hM.2.2.1
  rw [hcard] at hrem
  change (∏ r, f r) ≤ C ^ (M.geometric.card + M.coreBins.card) *
    ∏ r ∈ clusterKeptRows M, f r at hrem
  have hfA : ∀ r, f r ≤ 4 * A r *
      ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r), H b := by
    intro r
    have hr := mul_le_mul_of_nonneg_left (hrow (M.positions r))
      (show (0 : ℝ) ≤ (PT.tiling.P i).M from Nat.cast_nonneg _)
    rw [Finset.prod_union (bulk_crossing_disjoint PT hPT (M.positions r))] at hr
    convert hr using 1 <;> dsimp [f, A, H] <;> ring
  have hkept : (∏ r ∈ clusterKeptRows M, f r) ≤
      4 ^ (clusterKeptRows M).card * (∏ r ∈ clusterKeptRows M, A r) *
        ∏ r ∈ clusterKeptRows M,
          ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r), H b := by
    calc
      (∏ r ∈ clusterKeptRows M, f r) ≤
          ∏ r ∈ clusterKeptRows M,
            4 * A r * ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r), H b :=
        Finset.prod_le_prod₀ (fun r hr => hf0 r) (fun r hr => hfA r)
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const]
  have hdel := delete_product (clusterAllowedCrossings PT hPT M) M.crossingBins
    (fun q => H q.2) 3 hM.2.2.2 (fun q hq => hH0 q.2)
      (fun q hq => hhit q.2 (CS.label ω q.2))
  have hfour : (4 : ℝ) ^ (clusterKeptRows M).card ≤ 4 ^ (T.S.n k) := by
    apply pow_le_pow_right₀ (by norm_num)
    have hh := Finset.card_le_card (Finset.subset_univ (clusterKeptRows M))
    simpa using hh
  have hPA0 : 0 ≤ ∏ r ∈ clusterKeptRows M, A r := Finset.prod_nonneg fun r hr => hA0 r
  have hPQ0 : 0 ≤ ∏ q ∈ clusterAllowedCrossings PT hPT M, H q.2 :=
    Finset.prod_nonneg fun q hq => hH0 q.2
  calc
    (∏ r, f r) ≤ C ^ (M.geometric.card + M.coreBins.card) *
        (4 ^ (clusterKeptRows M).card * (∏ r ∈ clusterKeptRows M, A r) *
          ∏ r ∈ clusterKeptRows M,
            ∏ b ∈ clusterCrossingNeighbours PT hPT (M.positions r), H b) :=
      hrem.trans (mul_le_mul_of_nonneg_left hkept (by dsimp [C]; positivity))
    _ ≤ C ^ (M.geometric.card + M.coreBins.card) *
        (4 ^ (T.S.n k) * (∏ r ∈ clusterKeptRows M, A r) *
          (3 ^ J * (3 ^ M.crossingBins.card *
            ∏ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins, H q.2))) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hfour hPA0
      · exact hcross.trans (mul_le_mul_of_nonneg_left hdel (by positivity))
      · exact Finset.prod_nonneg fun r hr => Finset.prod_nonneg fun b hb => hH0 b
      · exact mul_nonneg (by positivity) hPA0
    _ = clusterMaskPayoff PT i M *
        clusterKeptProduct PT hPT hm i x M (CS.history ω) (CS.internal ω) := by
      have hl : ∀ b, CS.label ω b = clusterLabelFromInternal (hPT := hPT) hm (CS.internal ω) b :=
        CS.label_eq ω
      change _ = (4 ^ (T.S.n k) * C ^ (M.geometric.card + M.coreBins.card) *
        3 ^ (J + M.crossingBins.card)) *
        ((∏ r ∈ clusterKeptRows M,
          ((PT.tiling.P i).M * clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) (M.positions r) x *
            ∏ b ∈ clusterBulkNeighbours PT hPT (M.positions r),
              normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x
                (clusterLabelFromInternal (hPT := hPT) hm (CS.internal ω) b))) *
          ∏ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins,
            normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT q.2.1)) x
              (clusterLabelFromInternal (hPT := hPT) hm (CS.internal ω) q.2))
      simp only [← hl, pow_add]
      dsimp [A, H]
      ring

end HypercubeRamsey.Lane_sol_s15_mask
