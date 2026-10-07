import HypercubeRamsey.S13.ResidualBounds
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Framework.Embedding

/-!
# Section 13.3: extraction, type selection, and prefix allocation
-/

namespace HypercubeRamsey.S13

open Filter
open Classical
open scoped BigOperators

/-- P13.3a (sections/13, lines 141–147): direct patch data extracted from a bias witness. -/
def DirectPatchData (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (g : ℕ) : Prop :=
  ∃ (c : Colour) (X Y : Finset (Fin (T.S.N k))),
    X.Nonempty ∧ ∃ hY : Y.Nonempty, X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-(g : ℝ) ^ κ.aB) ≤ X.card ∧
    ∀ x ∈ X, (1 / 2 : ℝ) + g / (4 * T.S.n k) ≤
      deg (T.S.E k) c (Law.unifCore Y hY).w x

/-- L13.0 (sections/13, lines 147–148): exact-size uniform subsampling preserves a finite family
of bounded averages. -/
def UniformSubsampleStatement : Prop :=
  ∀ (N J m n : ℕ) (V : Finset (Fin N)) (f : Fin J → Fin N → ℝ),
    1 ≤ n → m ≤ V.card → n ^ 12 ≤ m →
    J ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 →
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V' : Finset (Fin N), V' ⊆ V ∧ V'.card = m ∧
      ∀ j, |(∑ y ∈ V', f j y) / m - (∑ y ∈ V, f j y) / V.card| ≤
        (n : ℝ) ^ (-2 : ℝ)

/-- L13.0 (sections/13, lines 244–249): a capped law admits a large uniform approximant for
finitely many bounded tests. -/
def LawSubsampleStatement : Prop :=
  ∀ (N J n : ℕ) (π : Law N) (t : ℝ) (f : Fin J → Fin N → ℝ),
    1 ≤ n → (n : ℝ) ^ 12 ≤ t → (∀ y, t * π.w y ≤ 1) →
    J ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 →
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V : Finset (Fin N), V.Nonempty ∧
      (∀ y ∈ V, 0 < π.w y) ∧
      (V.card : ℝ) ≥ t / 2 ∧
      ∀ j, |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| ≤ (n : ℝ) ^ (-2 : ℝ)

/-- L13.0a (sections/13, lines 147–148): exact-size sampling with at most exponentially many tests. -/
theorem uniform_subsample : UniformSubsampleStatement := by
  sorry

/-- L13.0b (sections/13, lines 244–249): Bernoulli sampling from the positive support of a capped law. -/
theorem law_subsample : LawSubsampleStatement := by
  sorry

/-- L13.0: assemble the two sampling contracts. -/
theorem random_subset_lemma : UniformSubsampleStatement ∧ LawSubsampleStatement :=
  ⟨uniform_subsample, law_subsample⟩

/-- L13.3a (sections/13, lines 141–147): direct bias extraction from a witness and absence at twice its budget. -/
theorem direct_patch_from_bias (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSampling : UniformSubsampleStatement)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      (κ.M1 * κ.Q0 ≤ (g : ℝ)) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g := by
  sorry

/-- P13.3b (sections/13, lines 95–99, 148): common bins of the prescribed size,
with a diagonal codegree margin. -/
def ClusterPatchData (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool) (d : ℕ) : Prop :=
  ∃ (X Y : Finset (Fin (T.S.N k))) (m : ℕ)
    (B : Fin m → Finset (Fin (T.S.N k))),
    X.Nonempty ∧ Y.Nonempty ∧ 0 < d ∧ X ⊆ (if o then RY else RX) ∧
    Y ⊆ (if o then RX else RY) ∧ X.card = Y.card ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-(q : ℝ) ^ κ.aC) ≤ X.card ∧
    (∀ j, B j ⊆ Y) ∧ Set.PairwiseDisjoint Set.univ B ∧
    (∀ j, (B j).card = d) ∧ Y = Finset.univ.biUnion B ∧
    ∀ j y y', y ∈ B j → y' ∈ B j →
      (1 / 4 : ℝ) + 3 * κ.a ≤
        (∑ x ∈ X, hit (if o then transposeRel (T.S.E k) else T.S.E k) true x y *
          hit (if o then transposeRel (T.S.E k) else T.S.E k) true x y') / X.card

/-- P13.3b (sections/13, lines 148, 151–155): a cluster witness yields equal sides partitioned into bins. -/
theorem cluster_patch_from_witness (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hSampling : UniformSubsampleStatement)
    (hClean : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ q o, IsDyadic q →
        CluScaleWitness κ T k RX RY q o → CleanClusterBins κ T k RX RY q o)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      IsDyadic q → κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) →
        ClusterPatchData κ T k RX RY q o d := by
  sorry

/-- P13.3c (sections/13, line 140): truncate two large residual sides to a common size. -/
theorem bounded_patch (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (hX : (T.S.N k : ℝ) / 2 ≤ RX.card) (hY : (T.S.N k : ℝ) / 2 ≤ RY.card) :
    ∃ X Y : Finset (Fin (T.S.N k)), X.Nonempty ∧ Y.Nonempty ∧
      X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
      (1 / 400 : ℝ) * T.S.N k ≤ X.card := by
  classical
  let m := min RX.card RY.card
  obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_left _ _)
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right _ _)
  have hNpos : 0 < (T.S.N k : ℝ) := by
    exact_mod_cast T.S.N_pos k
  have hmin : (T.S.N k : ℝ) / 2 ≤ (m : ℝ) := by
    dsimp [m]
    rw [Nat.cast_min]
    exact le_min hX hY
  have hmpos : 0 < m := by
    exact_mod_cast (show (0 : ℝ) < (m : ℝ) by linarith)
  have hXne : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; exact hmpos)
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; exact hmpos)
  refine ⟨X, Y, hXne, hYne, hXsub, hYsub, ?_, ?_⟩
  · rw [hXcard, hYcard]
  · rw [hXcard]
    linarith

/-- D13.T/P13.3d (sections/13, lines 52–126, 128–159): extraction data independent of prefix allocation. -/
/- The extraction data which does not depend on the prefix words or on the
allocation estimates. This is the output of the repeated patch passes. -/
structure ExtractionData {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop where
  reserveX_card : 𝒯.reserveX.card = T.S.N k / 3
  reserveY_card : 𝒯.reserveY.card = T.S.N k / 3
  reserveX_subset : 𝒯.reserveX ⊆ T.X k
  reserveY_subset : 𝒯.reserveY ⊆ T.Y k
  patch_supports : ∀ i, (𝒯.P i).X ⊆ (𝒯.P i).resX ∧
    (𝒯.P i).resX ⊆ T.X k \ 𝒯.reserveX ∧
    (𝒯.P i).Y ⊆ (𝒯.P i).resY ∧
    (𝒯.P i).resY ⊆ T.Y k \ 𝒯.reserveY
  patch_nonempty : ∀ i, (𝒯.P i).X.Nonempty ∧ (𝒯.P i).Y.Nonempty
  bins_card : ∀ i, ∀ B ∈ (𝒯.P i).bins.parts, B.card = (𝒯.P i).d
  patch_X_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).X (𝒯.P j).X
  patch_Y_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).Y (𝒯.P j).Y
  S_upper : 𝒯.S ≤ T.S.N k
  measured_scales : ∀ i, (𝒯.P i).g = gScale κ T k (𝒯.P i).resX (𝒯.P i).resY ∧
    (𝒯.P i).q = qScale κ T k (𝒯.P i).resX (𝒯.P i).resY
  bounded_scale_cutoff : 𝒯.mode = .bounded → ∀ i,
    max (𝒯.P i).g (𝒯.P i).q < κ.M1 * κ.Q0
  bounded_data : 𝒯.mode = .bounded → 𝒯.m = 1 ∧ ∀ i,
    (𝒯.P i).ℓ = 0 ∧ (𝒯.P i).h = 0 ∧ (𝒯.P i).d = 1 ∧
    (1 / 400 : ℝ) * T.S.N k ≤ (𝒯.P i).M ∧ 𝒯.Q i = κ.Qbd
  /-- The eventual residual-scale bound for direct modes, required by `Tiling.Valid` (consumed in Section 15). -/
  direct_scale_bound : (𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) → ∀ i,
    ((𝒯.P i).g : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2)
  direct_data : (𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) → ∀ i,
    κ.M1 * κ.Q0 ≤ max (𝒯.P i).g (𝒯.P i).q ∧
    κ.M1 * (𝒯.P i).q < (𝒯.P i).g ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-Real.rpow ((𝒯.P i).g : ℝ) κ.aB) ≤ (𝒯.P i).M ∧
    (∀ x ∈ (𝒯.P i).X,
      (1 / 2 : ℝ) + (𝒯.P i).g / (4 * T.S.n k) ≤
        deg (T.S.E k) 𝒯.c (Law.unifCore (𝒯.P i).Y (patch_nonempty i).2).w x) ∧
    (𝒯.P i).h = 0 ∧ (𝒯.P i).d = 1 ∧
    ((𝒯.mode = .highDirect) ↔ κ.KB * Real.log (T.S.n k) < (𝒯.P i).g)
  cluster_data : (𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) → ∀ i,
    κ.M1 * κ.Q0 ≤ max (𝒯.P i).g (𝒯.P i).q ∧
    (𝒯.P i).g ≤ κ.M1 * (𝒯.P i).q ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) ≤ (𝒯.P i).M ∧
    ((𝒯.mode = .highSmall) →
      (𝒯.P i).d = min ⌊Real.exp ((𝒯.P i).q / 2)⌋₊
        ⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊) ∧
    ((𝒯.mode = .lowCluster ∨ 𝒯.mode = .highLarge) →
      (𝒯.P i).d = ⌊Real.exp ((𝒯.P i).q / 2)⌋₊) ∧
    (∀ B ∈ (𝒯.P i).bins.parts, ∀ y ∈ B, ∀ y' ∈ B,
      (1 / 4 : ℝ) + 3 * κ.a ≤
        (∑ x ∈ (𝒯.P i).X,
          hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') / (𝒯.P i).M) ∧
    (𝒯.P i).h = 2 ^ Nat.log2 (𝒯.P i).h ∧
    (Real.rpow (𝒯.P i).q (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P i).h) ∧
    ((𝒯.P i).h : ℝ) < 2 * Real.rpow (𝒯.P i).q
      (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ∧
    ((𝒯.mode = .lowCluster) ↔
      (𝒯.P i).q ≤ Real.rpow (Real.log (T.S.n k)) κ.cq) ∧
    ((𝒯.mode = .highSmall) ↔
      (Real.rpow (Real.log (T.S.n k)) κ.cq < (𝒯.P i).q ∧
       (𝒯.P i).q ≤ (Real.log (T.S.n k)) ^ 2)) ∧
    ((𝒯.mode = .highLarge) ↔ (Real.log (T.S.n k)) ^ 2 < (𝒯.P i).q)
  clique_scales : ∀ i,
    (𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q ^ 2 ≤ 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).q ^ 2 ∧ 𝒯.kScale i < 𝒯.Q i) ∧
    ((𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).g / (2 * Real.sqrt κ.M1) < 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).g / Real.sqrt κ.M1 ∧ (𝒯.P i).q < 𝒯.Q i)

/-- Changing only the prefix words preserves every extraction fact. -/
private theorem extractionData_withWords {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : ExtractionData 𝒯)
    (w : Fin 𝒯.m → CubePos (T.S.n k)) :
    ExtractionData (κ := κ) (T := T) (k := k) {𝒯 with w := w} := by
  cases 𝒯 with
  | mk mode c m P S oldWords reserveX reserveY Q =>
    cases h𝒯
    constructor <;> assumption

/-- P13.3d–e (sections/13, lines 128–168): one uniform mode/orientation/colour family. -/
structure PassFamily (κ : CConsts) (T : Stage) (k : ℕ) where
  orientation : Bool
  tiling : Tiling κ (T.orient orientation) k
  extracted : ExtractionData tiling
  mass_sum : ∑ i, (tiling.P i).M = tiling.S

/-- P13.3d (sections/13, lines 128–159): extraction pass families grouped by finite type. -/
structure PassCollection (κ : CConsts) (T : Stage) (k : ℕ) where
  families : List (PassFamily κ T k)
  families_mass : ∀ f ∈ families, ∑ i, (f.tiling.P i).M = f.tiling.S
  type_tags_nodup : (families.map fun f : PassFamily κ T k =>
    (f.orientation, f.tiling.mode, f.tiling.c)).Nodup
  mass_or_bounded :
    (∃ f ∈ families, f.tiling.mode = .bounded ∧
      (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
    ((families.filter fun f => f.tiling.mode ≠ .bounded).map
      (fun f => f.tiling.S)).sum * 10 ≥ T.S.N k

/-- P13.3f (sections/13, lines 170–182): rounded family with dyadic weights summing to one. -/
structure RoundedFamily (κ : CConsts) (T : Stage) (k : ℕ) where
  orientation : Bool
  tiling : Tiling κ (T.orient orientation) k
  extracted : ExtractionData tiling
  S_lower : (1 / 400 : ℝ) * T.S.N k ≤ tiling.S
  S_upper : tiling.S ≤ T.S.N k
  selected_mass : (tiling.S : ℝ) / 2 < ∑ i, (tiling.P i).M
  dyadic_mass_lower : ∀ i, (tiling.P i).M / tiling.S ≤
    (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ))
  dyadic_mass_upper : ∀ i,
    (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ)) < 2 * (tiling.P i).M / tiling.S
  dyadic_sum : ∑ i, (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ)) = 1

/-- P13.3f (sections/13, lines 170–182): rounding retains an injective
subfamily, keeps the pre-restriction mass and reserves, and changes only
prefix lengths. `HEq` transports patches across the equal orientations. -/
structure RoundingProvenance {κ : CConsts} {T : Stage} {k : ℕ}
    (f : PassFamily κ T k) (R : RoundedFamily κ T k) where
  orientation : R.orientation = f.orientation
  mode : R.tiling.mode = f.tiling.mode
  colour : R.tiling.c = f.tiling.c
  mass : R.tiling.S = f.tiling.S
  reserveX : HEq R.tiling.reserveX f.tiling.reserveX
  reserveY : HEq R.tiling.reserveY f.tiling.reserveY
  index : Fin R.tiling.m → Fin f.tiling.m
  injective : Function.Injective index
  patches : ∀ i, HEq
    {R.tiling.P i with ℓ := (f.tiling.P (index i)).ℓ} (f.tiling.P (index i))
  clique_scales : ∀ i, R.tiling.Q i = f.tiling.Q (index i)

/-- P13.3h (sections/13, lines 193, 210): all prefixes leave a free coordinate,
and all internal tails lie beyond every prefix. -/
structure PrefixDimensionFit {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k) : Prop where
  free : ∀ i, (R.tiling.P i).ℓ < (T.orient R.orientation).S.n k
  fit : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
    (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
      (T.orient R.orientation).S.n k

/-- P13.3g (sections/13, lines 170–182): complete prefix-code property for assigned words. -/
def PrefixCodeComplete {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) : Prop :=
  ∀ v : CubePos ((T.orient R.orientation).S.n k), ∃! i,
    v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)

/-- P13.3h (sections/13, lines 184–204): parity counts, crossing flips, and internal-coordinate fit. -/
structure PrefixGeometry {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) : Prop where
  prefix_internal_length :
    (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
      (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
        (T.orient R.orientation).S.n k
  leaf_card : ∀ i, Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ)
  parity_leaf_card : ∀ i,
    Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ - 1)
  odd_leaf_card : ∀ i,
    Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ ¬ IsEvenRole v} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ - 1)
  role_count_bounds : ∀ i,
    (2 : ℝ) ^ ((T.orient R.orientation).S.n k - 1) *
        (R.tiling.P i).M / (T.S.N k : ℝ) ≤
          (Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) ∧
      (Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
          v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) ≤
        (2 : ℝ) ^ ((T.orient R.orientation).S.n k) *
          (R.tiling.P i).M / ((1 / 400 : ℝ) * T.S.N k)
  crossing_flips : ∀ i (v : CubePos ((T.orient R.orientation).S.n k)),
    v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) →
    ∃ f : {j : Fin ((T.orient R.orientation).S.n k) //
      j.val < (R.tiling.P i).ℓ} → Fin R.tiling.m,
      (∀ j, f j ≠ i ∧
        Function.update v j.1 (!v j.1) ∈
          prefixLeaf (R.tiling.P (f j)).ℓ (w (f j))) ∧ Function.Injective f
  coordinate_partition : ∀ i,
    Tiling.crossingCoords R.tiling i ∪
      (Tiling.bulkCoords R.tiling i ∪ Tiling.Icoord R.tiling i) = Finset.univ
  coordinate_disjoint : ∀ i,
    Disjoint (Tiling.crossingCoords R.tiling i) (Tiling.bulkCoords R.tiling i) ∧
    Disjoint (Tiling.crossingCoords R.tiling i) (Tiling.Icoord R.tiling i) ∧
    Disjoint (Tiling.bulkCoords R.tiling i) (Tiling.Icoord R.tiling i)
  internal_card : ∀ i, (Tiling.Icoord R.tiling i).card = (R.tiling.P i).h
  internal_nested : ∀ i j, (R.tiling.P i).h ≤ (R.tiling.P j).h →
    Tiling.Icoord R.tiling i ⊆ Tiling.Icoord R.tiling j

/-- Attach the Kraft words to the extracted family. -/
private def withPrefixWords {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) :
    RoundedFamily κ T k where
  orientation := R.orientation
  tiling := {R.tiling with w := w}
  extracted := extractionData_withWords R.extracted w
  S_lower := R.S_lower
  S_upper := R.S_upper
  selected_mass := R.selected_mass
  dyadic_mass_lower := R.dyadic_mass_lower
  dyadic_mass_upper := R.dyadic_mass_upper
  dyadic_sum := R.dyadic_sum

/-- Attaching words preserves the retained subfamily and all extraction data. -/
private def roundingProvenance_withWords {κ : CConsts} {T : Stage} {k : ℕ}
    {f : PassFamily κ T k} {R : RoundedFamily κ T k}
    (h : RoundingProvenance f R)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) :
    RoundingProvenance f (withPrefixWords R w) where
  orientation := h.orientation
  mode := h.mode
  colour := h.colour
  mass := h.mass
  reserveX := h.reserveX
  reserveY := h.reserveY
  index := h.index
  injective := h.injective
  patches := h.patches
  clique_scales := h.clique_scales

/-- P13.3i (sections/13, lines 151–155, 205–215): scale and gain inequalities required by later sections. -/
def AllocationBounds {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop :=
  ∀ i, (max (𝒯.P i).h (𝒯.P i).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι ∧
    (𝒯.mode = .bounded ∨
      ((𝒯.P i).ℓ : ℝ) ≤ 𝒯.gain i / (1000 * κ.u) ∧
      Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤ 𝒯.gain i / (1000 * κ.u))

/-- P13.3i (sections/13, lines 151–155, 205–215): estimates selecting later low and high modes. -/
def ScaleRegimeFacts {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop :=
  (∀ i, 𝒯.mode.isCluster →
    (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤ Real.rpow ((𝒯.P i).q : ℝ) (κ.aC / 2) ∧
      (𝒯.kScale i : ℝ) * 𝒯.tScale i < Real.log (𝒯.P i).d) ∧
  (𝒯.mode = .lowCluster → ∀ i,
    ((𝒯.P i).h : ℝ) ≤ Real.rpow (Real.log (T.S.n k)) (1 / 10 : ℝ)) ∧
  ((𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) → ∀ i,
    (Real.log (T.S.n k)) ^ 5 < (𝒯.P i).h) ∧
  (𝒯.mode = .highSmall → ∀ i,
    ((𝒯.P i).h : ℝ) < Real.rpow ((𝒯.P i).d : ℝ) (1 / 40 : ℝ))

/-- P13.3d (sections/13, lines 128–159): residual scales and patch nodes drive repeated extraction passes. -/
theorem extraction_passes (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T)
    (hSamplingU : UniformSubsampleStatement)
    (hBiasNode : ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      κ.M1 * κ.Q0 ≤ (g : ℝ) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g)
    (hClusterNode : ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      IsDyadic q → κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) →
        ClusterPatchData κ T k RX RY q o d)
    (hBoundedNode : ∀ k RX RY,
      (T.S.N k : ℝ) / 2 ≤ RX.card → (T.S.N k : ℝ) / 2 ≤ RY.card →
      ∃ X Y : Finset (Fin (T.S.N k)), X.Nonempty ∧ Y.Nonempty ∧
        X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
        (1 / 400 : ℝ) * T.S.N k ≤ X.card)
    (hScaleSpec : ResidualScaleSpec)
    (hScaleBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, Nonempty (PassCollection κ T k) := by
  sorry

/-- P13.3e (sections/13, lines 159–168): select one bounded family or a nonbounded type carrying at least
one twentieth of the extracted mass. -/
theorem type_selection (κ : CConsts) (T : Stage) (k : ℕ)
    (families : List (PassFamily κ T k))
    (hFamilyMass : ∀ f ∈ families, ∑ i, (f.tiling.P i).M = f.tiling.S)
    (htags : (families.map fun f : PassFamily κ T k =>
      (f.orientation, f.tiling.mode, f.tiling.c)).Nodup)
    (hmass : (∃ f ∈ families, f.tiling.mode = .bounded ∧
      (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
      ((families.filter fun f => f.tiling.mode ≠ .bounded).map
        (fun f => f.tiling.S)).sum * 10 ≥ T.S.N k) :
    ∃ f : PassFamily κ T k, f ∈ families ∧
      ((f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) := by
  classical
  rcases hmass with hbounded | hnonbounded
  · rcases hbounded with ⟨f, hf, hmode, hsize⟩
    exact ⟨f, hf, Or.inl ⟨hmode, hsize⟩⟩
  · let tag : PassFamily κ T k → Bool × Mode × Colour :=
      fun f => (f.orientation, f.tiling.mode, f.tiling.c)
    let L := families.filter fun f => f.tiling.mode ≠ .bounded
    have htagsL : (L.map tag).Nodup := by
      apply List.Nodup.sublist _ htags
      exact (List.filter_sublist).map tag
    let possible : Finset (Bool × Mode × Colour) :=
      Finset.univ.filter fun t => t.2.1 ≠ .bounded
    have hpossible : possible.card = 20 := by
      decide
    have hlen : L.length ≤ 20 := by
      let s := (L.map tag).toFinset
      have hs : s ⊆ possible := by
        intro t ht
        rcases List.mem_toFinset.mp ht with ht
        rcases List.mem_map.mp ht with ⟨f, hf, rfl⟩
        simp only [possible, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [L] using (List.mem_filter.mp hf).2
      calc
        L.length = s.card := by
          simpa [s] using (List.toFinset_card_of_nodup htagsL).symm
        _ ≤ possible.card := Finset.card_le_card hs
        _ = 20 := hpossible
    have hNpos : 0 < T.S.N k := T.S.N_pos k
    have hmassNat : (L.map fun f => f.tiling.S).sum * 10 ≥ T.S.N k := by
      simpa [L] using hnonbounded
    have hLne : L ≠ [] := by
      intro hnil
      simp [hnil] at hmassNat
      omega
    by_contra hnone
    have hsmall : ∀ f ∈ L, (f.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k := by
      intro f hf
      rcases (show f ∈ families ∧ f.tiling.mode ≠ .bounded by simpa [L] using hf) with
        ⟨hfam, hmode⟩
      have hnot : ¬ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S := by
        intro hs
        exact hnone ⟨f, hfam, Or.inr ⟨hmode, hs⟩⟩
      exact lt_of_not_ge hnot
    have hsum_bound : ∀ xs : List (PassFamily κ T k),
        (∀ f ∈ xs, (f.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k) →
        (xs.map fun f => (f.tiling.S : ℝ)).sum ≤
          (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        intro hall
        have ha := hall a (by simp)
        have htail := ih (by
          intro f hf
          exact hall f (by simp [hf]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [Nat.cast_add, Nat.cast_one]
        calc
          _ ≤ (1 / 200 : ℝ) * T.S.N k + (xs.map fun f => (f.tiling.S : ℝ)).sum :=
            add_le_add_left ha.le _
          _ ≤ (1 / 200 : ℝ) * T.S.N k +
              (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) :=
            add_le_add_right htail _
          _ = ((xs.length : ℝ) + 1) * ((1 / 200 : ℝ) * T.S.N k) := by ring
    obtain ⟨f₀, xs, hLdef⟩ := List.exists_cons_of_ne_nil hLne
    have hhead : (f₀.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k := by
      apply hsmall f₀
      rw [hLdef]
      simp
    have htail := hsum_bound xs (by
      intro f hf
      apply hsmall f
      rw [hLdef]
      exact List.mem_cons_of_mem _ hf)
    have hsumlt : (L.map fun f => (f.tiling.S : ℝ)).sum <
        (L.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) := by
      rw [hLdef]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.cast_add, Nat.cast_one]
      apply lt_of_lt_of_le
      · exact add_lt_add_left hhead _
      · calc
          _ ≤ (1 / 200 : ℝ) * T.S.N k +
              (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) :=
            add_le_add_right htail _
          _ = ((xs.length : ℝ) + 1) * ((1 / 200 : ℝ) * T.S.N k) := by ring
    have hlenR : (L.length : ℝ) ≤ 20 := by exact_mod_cast hlen
    have hmassR : (T.S.N k : ℝ) ≤
        (L.map fun f => (f.tiling.S : ℝ)).sum * 10 := by
      have hc : (T.S.N k : ℝ) ≤
          (((L.map fun f => f.tiling.S).sum * 10 : ℕ) : ℝ) := by
        exact_mod_cast hmassNat
      simpa [Nat.cast_mul, Nat.cast_sum, List.map_map, Function.comp_def] using hc
    have hsumSmall : (L.map fun f => (f.tiling.S : ℝ)).sum * 10 <
        (T.S.N k : ℝ) := by
      have htarget : 0 ≤ (1 / 200 : ℝ) * T.S.N k := by positivity
      calc
        _ < ((L.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k)) * 10 :=
          mul_lt_mul_of_pos_right hsumlt (by norm_num)
        _ ≤ (20 : ℝ) * ((1 / 200 : ℝ) * T.S.N k) * 10 := by
          gcongr
        _ = T.S.N k := by ring
    exact (not_lt_of_ge hmassR) hsumSmall
    

/-- P13.3f (sections/13, lines 170–182): round dyadic masses upward and retain the first complete segment. -/
theorem dyadic_rounding (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (f : PassFamily κ T k)
    (hExtracted : ExtractionData f.tiling)
    (hSelected : (f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) :
    ∃ R : RoundedFamily κ T k, Nonempty (RoundingProvenance f R) := by
  sorry

/-- P13.3g (sections/13, lines 170–182): Kraft's equality gives a complete prefix code. -/
theorem kraft_prefix_code (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (hLength : ∀ i, (R.tiling.P i).ℓ ≤ (T.orient R.orientation).S.n k) :
    ∃ w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k),
      PrefixCodeComplete R w := by
  sorry

private theorem allocation_prefixLeaf_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} = 2 ^ (n - ell) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans hell⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hS_eq : S = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  have hScard : S.card = ell := by
    rw [hS_eq]
    simp
  let choices : Fin n → Finset Bool := fun j =>
    if j ∈ S then {w j} else Finset.univ
  let Q := Fintype.piFinset choices
  have hpred (v : CubePos n) : v ∈ prefixLeaf ell w ↔ v ∈ Q := by
    change (∀ j : Fin n, j.val < ell → v j = w j) ↔ v ∈ Q
    constructor
    · intro hv
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hj : j ∈ S
      · have hfix := hv j (Finset.mem_filter.mp hj).2
        simp [Q, choices, hj, hfix]
      · simp [Q, choices, hj]
    · intro hv j hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hmem := Fintype.mem_piFinset.mp hv j
      simpa [Q, choices, hjS] using hmem
  have hF : Finset.univ.filter (fun v : CubePos n => v ∈ prefixLeaf ell w) = Q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred v
  have hsub := Fintype.card_congr ((Equiv.refl (CubePos n)).subtypeEquiv hpred)
  calc
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} =
        Fintype.card {v : CubePos n // v ∈ Q} := hsub
    _ = Q.card := Fintype.card_coe Q
    _ = 2 ^ (n - ell) := by
      change (Fintype.piFinset choices).card = _
      rw [Fintype.card_piFinset]
      have hchoice : ∀ j : Fin n, (choices j).card = if j ∈ S then 1 else 2 := by
        intro j
        by_cases hj : j ∈ S <;> simp [choices, hj]
      simp_rw [hchoice]
      rw [Finset.prod_ite]
      have hfilter : Finset.univ.filter (fun j : Fin n => j ∉ S) = Finset.univ \ S := by
        ext j
        simp
      rw [hfilter, Finset.prod_const_one, Finset.prod_const (b := 2),
        Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [hScard]

private theorem allocation_prefixLeaf_even_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} =
      2 ^ (n - ell - 1) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans hell⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hS_eq : S = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  have hScard : S.card = ell := by rw [hS_eq]; simp
  let z : ∀ j : S, Bool := fun j => w j.1
  have hprefix (v : CubePos n) :
      (∀ j : S, v j.1 = z j) ↔ v ∈ prefixLeaf ell w := by
    constructor
    · intro hz
      change ∀ j : Fin n, j.val < ell → v j = w j
      intro j hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      simpa [z] using hz ⟨j, hjS⟩
    · intro hv
      change ∀ j : Fin n, j.val < ell → v j = w j at hv
      intro j
      exact hv j (Finset.mem_filter.mp j.property).2
  have hSlt : S.card < n := by simpa [hScard] using hell
  have hParity := parity_projection_uniform S hSlt z
  have hfilter :
      Finset.univ.filter (fun v : CubePos n => v ∈ prefixLeaf ell w ∧ IsEvenRole v) =
        (evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, evenRoleSet]
    constructor
    · rintro ⟨hp, he⟩
      exact ⟨he, (hprefix v).mpr hp⟩
    · rintro ⟨he, hz⟩
      exact ⟨(hprefix v).mp hz, he⟩
  have hcard :
      Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} =
        ((evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j)).card := by
    rw [Fintype.card_subtype]
    simpa using congrArg Finset.card hfilter
  calc
    _ = ((evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j)).card := hcard
    _ = 2 ^ (n - S.card - 1) := hParity
    _ = 2 ^ (n - ell - 1) := by rw [hScard]

private theorem allocation_prefixLeaf_odd_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ ¬ IsEvenRole v} =
      2 ^ (n - ell - 1) := by
  classical
  let P : CubePos n → Prop := fun v => v ∈ prefixLeaf ell w
  have hsplit :
      Fintype.card {v : CubePos n // P v ∧ IsEvenRole v} +
        Fintype.card {v : CubePos n // P v ∧ ¬ IsEvenRole v} =
          Fintype.card {v : CubePos n // P v} := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter P) IsEvenRole
    simpa [P, Fintype.card_subtype, Finset.filter_filter, and_comm] using h
  have hleaf := allocation_prefixLeaf_card w hell
  have heven := allocation_prefixLeaf_even_card w hell
  have hpow : 2 ^ (n - ell) = 2 * 2 ^ (n - ell - 1) := by
    have hsplitExp : n - ell = (n - ell - 1) + 1 := by omega
    calc
      2 ^ (n - ell) = 2 ^ ((n - ell - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (n - ell - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - ell - 1) := by ring
  have hsplit' :
      Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} +
        Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ ¬ IsEvenRole v} =
          Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} := by
    simpa [P] using hsplit
  rw [hleaf, heven, hpow] at hsplit'
  omega

private theorem allocation_prefixCoords_card {n ell : ℕ} (hle : ell ≤ n) :
    (Finset.univ.filter fun j : Fin n => j.val < ell).card = ell := by
  classical
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans_le hle⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hset : (Finset.univ.filter fun j : Fin n => j.val < ell) = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  rw [hset]
  simp

/-- P13.3h (sections/13, lines 184–204): prefix geometry gives role counts and distinct crossing leaves. -/
theorem allocation_geometry (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hCode : PrefixCodeComplete R w)
    (hFit : PrefixDimensionFit R) : PrefixGeometry R w := by
  classical
  let n := (T.orient R.orientation).S.n k
  have hEllLe (i : Fin R.tiling.m) :
      (R.tiling.P i).ℓ ≤ Finset.univ.sup fun j : Fin R.tiling.m => (R.tiling.P j).ℓ :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin R.tiling.m => (R.tiling.P j).ℓ) (Finset.mem_univ i)
  have hHLe (i : Fin R.tiling.m) :
      (R.tiling.P i).h ≤ Finset.univ.sup fun j : Fin R.tiling.m => (R.tiling.P j).h :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin R.tiling.m => (R.tiling.P j).h) (Finset.mem_univ i)
  have hDim (i : Fin R.tiling.m) : (R.tiling.P i).ℓ + (R.tiling.P i).h ≤ n := by
    have hℓ := hEllLe i
    have hh := hHLe i
    have h := hFit.fit
    omega
  have hNpos : (0 : ℝ) < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hSpos : (0 : ℝ) < (R.tiling.S : ℝ) :=
    lt_of_lt_of_le (by positivity) R.S_lower
  have hSupper : (R.tiling.S : ℝ) ≤ (T.S.N k : ℝ) := by exact_mod_cast R.S_upper
  refine {
    prefix_internal_length := hFit.fit
    leaf_card := ?_
    parity_leaf_card := ?_
    odd_leaf_card := ?_
    role_count_bounds := ?_
    crossing_flips := ?_
    coordinate_partition := ?_
    coordinate_disjoint := ?_
    internal_card := ?_
    internal_nested := ?_ }
  · intro i
    exact allocation_prefixLeaf_card (w i) (hFit.free i)
  · intro i
    exact allocation_prefixLeaf_even_card (w i) (hFit.free i)
  · intro i
    exact allocation_prefixLeaf_odd_card (w i) (hFit.free i)
  · intro i
    constructor
    · have hMnonneg : (0 : ℝ) ≤ (R.tiling.P i).M := by positivity
      have hfrac : (R.tiling.P i).M / (T.S.N k : ℝ) ≤
          (R.tiling.P i).M / (R.tiling.S : ℝ) :=
        div_le_div_of_nonneg_left hMnonneg hSpos hSupper
      have hdyadic : (2 : ℝ) ^ (-((R.tiling.P i).ℓ : ℤ)) =
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by simp
      have hpow : (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
          (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        have hfree := hFit.free i
        have hℓ : (R.tiling.P i).ℓ ≤ n - 1 := by omega
        calc
          _ = (2 : ℝ) ^ (n - 1 - (R.tiling.P i).ℓ) := by congr 1 <;> omega
          _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
            pow_sub₀ (2 : ℝ) (by norm_num) hℓ
      have hcard :
          (Fintype.card {v : CubePos n //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) =
            (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := by
        exact_mod_cast allocation_prefixLeaf_even_card (w i) (hFit.free i)
      have hdyLow : (R.tiling.P i).M / (R.tiling.S : ℝ) ≤
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        simpa only [hdyadic] using R.dyadic_mass_lower i
      rw [hcard]
      calc
        (2 : ℝ) ^ (n - 1) * (R.tiling.P i).M / (T.S.N k : ℝ) =
            (2 : ℝ) ^ (n - 1) * ((R.tiling.P i).M / (T.S.N k : ℝ)) := by ring
        _ ≤ (2 : ℝ) ^ (n - 1) * ((R.tiling.P i).M / (R.tiling.S : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ ≤ (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
          mul_le_mul_of_nonneg_left hdyLow (by positivity)
        _ = (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := hpow.symm
    · have hMnonneg : (0 : ℝ) ≤ (R.tiling.P i).M := by positivity
      have hquarter : (0 : ℝ) < (1 / 400 : ℝ) * (T.S.N k : ℝ) := by positivity
      have hfrac : (R.tiling.P i).M / (R.tiling.S : ℝ) ≤
          (R.tiling.P i).M / ((1 / 400 : ℝ) * (T.S.N k : ℝ)) :=
        div_le_div_of_nonneg_left hMnonneg hquarter R.S_lower
      have hdyadic : (2 : ℝ) ^ (-((R.tiling.P i).ℓ : ℤ)) =
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by simp
      have hdyHigh : ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ <
          2 * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by
        calc
          _ < 2 * (R.tiling.P i).M / (R.tiling.S : ℝ) := by
            simpa only [hdyadic] using R.dyadic_mass_upper i
          _ = 2 * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by ring
      have hfree := hFit.free i
      have hpow : (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
          (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        have hℓ : (R.tiling.P i).ℓ ≤ n - 1 := by omega
        calc
          _ = (2 : ℝ) ^ (n - 1 - (R.tiling.P i).ℓ) := by congr 1 <;> omega
          _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
            pow_sub₀ (2 : ℝ) (by norm_num) hℓ
      have hcard :
          (Fintype.card {v : CubePos n //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) =
            (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := by
        exact_mod_cast allocation_prefixLeaf_even_card (w i) (hFit.free i)
      have hpowSucc : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := by
        have hfree := hFit.free i
        have hn : n - 1 + 1 = n := by omega
        calc
          (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ ((n - 1) + 1) := by rw [pow_succ]
          _ = (2 : ℝ) ^ n := by rw [hn]
      rw [hcard]
      exact le_of_lt <| calc
        (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
            (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := hpow
        _ < (2 : ℝ) ^ (n - 1) *
            (2 * ((R.tiling.P i).M / (R.tiling.S : ℝ))) :=
          mul_lt_mul_of_pos_left hdyHigh (by positivity)
        _ = (2 : ℝ) ^ n * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by
          calc
            _ = ((2 : ℝ) ^ (n - 1) * 2) *
                ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by ring
            _ = (2 : ℝ) ^ n * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by rw [hpowSucc]
        _ ≤ (2 : ℝ) ^ n *
            ((R.tiling.P i).M / ((1 / 400 : ℝ) * (T.S.N k : ℝ))) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = (2 : ℝ) ^ n * (R.tiling.P i).M /
            ((1 / 400 : ℝ) * (T.S.N k : ℝ)) := by ring
  · intro i v hv
    classical
    let hLeaves (x : CubePos n) : ∃ t : Fin R.tiling.m,
        x ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := (hCode x).exists
    let f : {j : Fin n // j.val < (R.tiling.P i).ℓ} → Fin R.tiling.m :=
      fun j => Classical.choose (hLeaves (flipPos v j.1))
    have hf (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) :
        flipPos v j.1 ∈ prefixLeaf (R.tiling.P (f j)).ℓ (w (f j)) :=
      Classical.choose_spec (hLeaves (flipPos v j.1))
    have hflipNot (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) :
        flipPos v j.1 ∉ prefixLeaf (R.tiling.P i).ℓ (w i) := by
      intro hmem
      have hvj := hv j.1 j.2
      have hfj := hmem j.1 j.2
      have hnot : v j.1 ≠ w i j.1 := by
        change Function.update v j.1 (!v j.1) j.1 = w i j.1 at hfj
        rw [Function.update_self] at hfj
        exact Bool.not_eq_iff.mp hfj
      exact hnot hvj
    have hnotIndex (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) : f j ≠ i := by
      intro heq
      apply hflipNot j
      simpa [heq] using hf j
    have hinj : Function.Injective f := by
      intro a b hab
      by_contra hne
      have hcoord : a.1 ≠ b.1 := by
        intro heq
        apply hne
        exact Subtype.ext heq
      let t := f a
      have htargetA : flipPos v a.1 ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
        simpa [t] using hf a
      have htargetB : flipPos v b.1 ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
        simpa [t, hab] using hf b
      by_cases hshort : (R.tiling.P t).ℓ ≤ a.1.val
      · have horig : v ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
          intro q hq
          have hqa : q ≠ a.1 := by
            intro heq
            have := congrArg Fin.val heq
            omega
          have hupdate : Function.update v a.1 (!v a.1) q = v q :=
            Function.update_of_ne hqa _ _
          calc
            v q = Function.update v a.1 (!v a.1) q := hupdate.symm
            _ = w t q := htargetA q hq
        rcases hCode v with ⟨u, hu, huniq⟩
        have htu : t = u := huniq t horig
        have hiu : i = u := huniq i hv
        exact hnotIndex a (by simpa [t] using htu.trans hiu.symm)
      · have hshort' : a.1.val < (R.tiling.P t).ℓ := by omega
        have hTA := htargetA a.1 hshort'
        have hnotA : v a.1 ≠ w t a.1 := by
          change Function.update v a.1 (!v a.1) a.1 = w t a.1 at hTA
          rw [Function.update_self] at hTA
          exact Bool.not_eq_iff.mp hTA
        have hupdate : Function.update v b.1 (!v b.1) a.1 = v a.1 :=
          Function.update_of_ne hcoord _ _
        have hTB := htargetB a.1 hshort'
        change Function.update v b.1 (!v b.1) a.1 = w t a.1 at hTB
        rw [hupdate] at hTB
        have hvalB : v a.1 = w t a.1 := by
          exact hTB
        exact hnotA hvalB
    exact ⟨f, fun j => ⟨hnotIndex j, hf j⟩, hinj⟩
  · intro i
    have hdim := hDim i
    ext j
    simp [Tiling.crossingCoords, Tiling.bulkCoords, Tiling.Icoord, topCoordinates]
    omega
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro j hjC hjB
      simp [Tiling.crossingCoords, Tiling.bulkCoords] at hjC hjB
      omega
    · apply Finset.disjoint_left.mpr
      intro j hjC hjI
      simp [Tiling.crossingCoords, Tiling.Icoord, topCoordinates] at hjC hjI
      have hdi := hDim i
      omega
    · apply Finset.disjoint_left.mpr
      intro j hjB hjI
      simp [Tiling.bulkCoords, Tiling.Icoord, topCoordinates] at hjB hjI
      omega
  · intro i
    change (Finset.univ.filter fun j : Fin n => n - (R.tiling.P i).h ≤ j.val).card =
      (R.tiling.P i).h
    let P : Finset (Fin n) := Finset.univ.filter fun j => j.val < n - (R.tiling.P i).h
    have hPcard : P.card = n - (R.tiling.P i).h :=
      allocation_prefixCoords_card (Nat.sub_le n _)
    have htop :
        Finset.univ.filter (fun j : Fin n => n - (R.tiling.P i).h ≤ j.val) =
          Finset.univ \ P := by
      ext j
      simp [P]
    rw [htop, Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    have hhi : (R.tiling.P i).h ≤ n := by
      have hdi := hDim i
      omega
    simp [P, hPcard]
    omega
  · intro i j hij
    intro x hx
    simp [Tiling.Icoord, topCoordinates] at hx ⊢
    omega

/-- P13.3i (sections/13, lines 151–155, 205–215): fixed thresholds fit prefixes and internal dimensions
inside the assigned gain budget. -/
theorem scale_bookkeeping (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ R : RoundedFamily κ T k,
      AllocationBounds R.tiling ∧ ScaleRegimeFacts R.tiling := by
  sorry

/-- P13.3i→h (sections/13, line 210): uniformly small dimensions fit, with a
free parity coordinate, at all sufficiently large indices. -/
theorem allocation_dimension_fit (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ R : RoundedFamily κ T k,
      AllocationBounds R.tiling → PrefixDimensionFit R := by
  have hιhalf : κ.ι < (1 / 2 : ℝ) := by
    have hmin₁ : min κ.η0 (0.01 : ℝ) ≤ (0.01 : ℝ) := min_le_right _ _
    have hmin₂ : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ (0.01 : ℝ) :=
      (min_le_right _ _).trans hmin₁
    have hι := hκ.ι_rng.2
    nlinarith
  have hnlarge : ∀ᶠ k in atTop, 4 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 4
  filter_upwards [hnlarge] with k hk
  intro R hAlloc
  let n := T.S.n k
  have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hnbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have horient : (T.orient R.orientation).S.n k = n := by
    cases R.orientation <;> rfl
  have hpow : (n : ℝ) ^ κ.ι ≤ (n : ℝ) / 2 := by
    calc
      (n : ℝ) ^ κ.ι ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnbase hιhalf.le
      _ = Real.sqrt (n : ℝ) := by rw [← Real.sqrt_eq_rpow]
      _ ≤ (n : ℝ) / 2 := by
        rw [Real.sqrt_le_left (by positivity)]
        have hprod := mul_nonneg (sub_nonneg.mpr hnreal) (show (0 : ℝ) ≤ n by positivity)
        nlinarith [hprod]
  have hhalf : ∀ i : Fin R.tiling.m,
      (R.tiling.P i).h ≤ n / 2 ∧ (R.tiling.P i).ℓ ≤ n / 2 := by
    intro i
    have hmaxReal : max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) <
        (n : ℝ) / 2 := by
      calc
        _ < ((T.orient R.orientation).S.n k : ℝ) ^ κ.ι := (hAlloc i).1
        _ = (n : ℝ) ^ κ.ι := by rw [horient]
        _ ≤ (n : ℝ) / 2 := hpow
    have hmaxTwiceRealLt : (2 : ℝ) *
        max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) < n :=
      (lt_div_iff₀' (by norm_num : (0 : ℝ) < 2)).mp hmaxReal
    have hmaxTwiceReal : (2 : ℝ) *
        max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) ≤ n := by
      exact hmaxTwiceRealLt.le
    have hhtwiceReal : (2 : ℝ) * (R.tiling.P i).h ≤ n := by
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hmaxTwiceReal
    have heltwiceReal : (2 : ℝ) * (R.tiling.P i).ℓ ≤ n := by
      exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hmaxTwiceReal
    have hhtwice : 2 * (R.tiling.P i).h ≤ n := by exact_mod_cast hhtwiceReal
    have heltwice : 2 * (R.tiling.P i).ℓ ≤ n := by exact_mod_cast heltwiceReal
    exact ⟨by omega, by omega⟩
  have hEllSup : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) ≤ n / 2 := by
    apply Finset.sup_le
    intro i hi
    exact (hhalf i).2
  have hHSup : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤ n / 2 := by
    apply Finset.sup_le
    intro i hi
    exact (hhalf i).1
  have hfree : ∀ i, (R.tiling.P i).ℓ < (T.orient R.orientation).S.n k := by
    intro i
    rw [horient]
    have hi := (hhalf i).2
    omega
  have hfit :
      (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
        (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
          (T.orient R.orientation).S.n k := by
    rw [horient]
    omega
  exact ⟨hfree, hfit⟩

private theorem tiling_valid_of_parts {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hPrefix : PrefixCodeComplete R w)
    (hGeometry : PrefixGeometry R w)
    (hAlloc : AllocationBounds R.tiling) :
    Tiling.Valid (κ := κ) (withPrefixWords R w).tiling := by
  let Rw := withPrefixWords R w
  let 𝒯 : Tiling κ (T.orient R.orientation) k := Rw.tiling
  have hE : ExtractionData 𝒯 := Rw.extracted
  have hN : (T.orient R.orientation).S.N k = T.S.N k := by
    cases R.orientation <;> rfl
  have hS : (1 / 400 : ℝ) * (T.orient R.orientation).S.N k ≤ 𝒯.S := by
    change (1 / 400 : ℝ) * (T.orient R.orientation).S.N k ≤ R.tiling.S
    simpa [hN] using R.S_lower
  have hSupper : 𝒯.S ≤ (T.orient R.orientation).S.N k := by
    change R.tiling.S ≤ (T.orient R.orientation).S.N k
    simpa [hN] using R.S_upper
  refine {
    reserveX_card := hE.reserveX_card
    reserveY_card := hE.reserveY_card
    reserveX_subset := hE.reserveX_subset
    reserveY_subset := hE.reserveY_subset
    patch_supports := hE.patch_supports
    patch_nonempty := hE.patch_nonempty
    bins_card := hE.bins_card
    patch_X_disjoint := hE.patch_X_disjoint
    patch_Y_disjoint := hE.patch_Y_disjoint
    S_lower := hS
    S_upper := hSupper
    selected_mass := R.selected_mass
    dyadic_mass_lower := R.dyadic_mass_lower
    dyadic_mass_upper := R.dyadic_mass_upper
    dyadic_sum := R.dyadic_sum
    prefix_complete := ?_
    prefix_internal_length := hGeometry.prefix_internal_length
    measured_scales := hE.measured_scales
    bounded_scale_cutoff := hE.bounded_scale_cutoff
    bounded_data := hE.bounded_data
    direct_scale_bound := hE.direct_scale_bound
    direct_data := hE.direct_data
    cluster_data := hE.cluster_data
    allocation_bounds := by
      simpa [𝒯, Rw, withPrefixWords, AllocationBounds, Tiling.gain] using hAlloc
    clique_scales := hE.clique_scales }
  intro v
  change ∃! i, v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)
  exact hPrefix v

/-- P13.3 (sections/13, lines 52–216): allocation with the retained-subfamily
provenance, all role/crossing/internal-coordinate facts, and scale regimes. -/
theorem extraction_allocation_with_facts (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ R : RoundedFamily κ T k, ∃ f : PassFamily κ T k,
      Nonempty (RoundingProvenance f R) ∧ Tiling.Valid R.tiling ∧
        PrefixGeometry R R.tiling.w ∧ ScaleRegimeFacts R.tiling := by
  have hSample := random_subset_lemma
  have hScaleSpec := d13_1_residual_scale_specification
  have hScaleBounds := residual_scale_bounds κ hκ T hInit hDeepι hClu
  have hDirect := direct_patch_from_bias κ hκ T hSample.1 hScaleBounds
  have hClusterTrim := clean_cluster_scale_witness κ hκ T hInit
  have hCluster := cluster_patch_from_witness κ hκ T hInit hSample.1 hClusterTrim hScaleBounds
  have hBounded := bounded_patch κ T
  have hPass := extraction_passes κ hκ T hInit hDeep hDeepι hClu
    hSample.1 hDirect hCluster hBounded hScaleSpec hScaleBounds
  have hBook := scale_bookkeeping κ hκ T hScaleBounds
  have hFit := allocation_dimension_fit κ hκ T
  filter_upwards [hPass, hBook, hFit] with k hPool hkBook hkFit
  obtain ⟨pool⟩ := hPool
  obtain ⟨f, hf, hselected⟩ := type_selection κ T k pool.families
    pool.families_mass pool.type_tags_nodup pool.mass_or_bounded
  have hFamilyExtraction := f.extracted
  obtain ⟨R, ⟨hKeep⟩⟩ :=
    dyadic_rounding κ hκ T k f hFamilyExtraction hselected
  have hScaleFacts := hkBook R
  have hDimensions := hkFit R hScaleFacts.1
  obtain ⟨w, hCode⟩ := kraft_prefix_code κ T k R (fun i => (hDimensions.free i).le)
  have hGeom := allocation_geometry κ T k R w hCode hDimensions
  refine ⟨withPrefixWords R w, f, ⟨roundingProvenance_withWords hKeep w⟩, ?_, ?_, ?_⟩
  · exact tiling_valid_of_parts R w hCode hGeom hScaleFacts.1
  · exact ⟨hGeom.prefix_internal_length, hGeom.leaf_card, hGeom.parity_leaf_card,
      hGeom.odd_leaf_card, hGeom.role_count_bounds, hGeom.crossing_flips,
      hGeom.coordinate_partition, hGeom.coordinate_disjoint, hGeom.internal_card,
      hGeom.internal_nested⟩
  · exact hScaleFacts.2

/-- P13.3: the original tiling export, projected from the full allocation assembly. -/
theorem extraction_allocation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ 𝒯 : Tiling κ (T.orient o) k, Tiling.Valid 𝒯 := by
  filter_upwards [extraction_allocation_with_facts κ hκ T hInit hDeep hDeepι hClu]
    with k hk
  obtain ⟨R, f, hKeep, hValid, hGeometry, hRegime⟩ := hk
  exact ⟨R.orientation, R.tiling, hValid⟩

end HypercubeRamsey.S13
