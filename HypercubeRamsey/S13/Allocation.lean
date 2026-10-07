import HypercubeRamsey.S13.ResidualBounds
import HypercubeRamsey.Tools.Concentration
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
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V' : Finset (Fin N), V' ⊆ V ∧ V'.card = m ∧
      ∀ j, |(∑ y ∈ V', f j y) / m - (∑ y ∈ V, f j y) / V.card| ≤
        (n : ℝ) ^ (-2 : ℝ)

/-- L13.0 (sections/13, lines 244–249): a capped law admits a large uniform approximant for
finitely many bounded tests. -/
def LawSubsampleStatement : Prop :=
  ∀ (N J n : ℕ) (π : Law N) (t : ℝ) (f : Fin J → Fin N → ℝ),
    0 < t → (∀ y, t * π.w y ≤ 1) →
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V : Finset (Fin N), V.Nonempty ∧
      (V.card : ℝ) ≥ t / 2 ∧
      ∀ j, |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| ≤ (n : ℝ) ^ (-2 : ℝ)

/-- L13.0 (sections/13, lines 147–148, 244–249): the random-subset guarantees used in Sections 13.3 and 13.4. -/
theorem random_subset_lemma : UniformSubsampleStatement ∧ LawSubsampleStatement := by
  sorry

/-- L13.3a (sections/13, lines 141–147): direct bias extraction from a witness and absence at twice its budget. -/
theorem direct_patch_from_bias (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSampling : UniformSubsampleStatement) :
    ∀ (k : ℕ) (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      (κ.M1 * κ.Q0 ≤ (g : ℝ)) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g := by
  sorry

/-- P13.3b (sections/13, lines 148, 151–155): common cluster bins with a diagonal codegree margin. -/
def ClusterPatchData (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool) : Prop :=
  ∃ (X Y : Finset (Fin (T.S.N k))) (d m : ℕ)
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
    (hInit : InitDisc T κ.η0) (hSampling : LawSubsampleStatement)
    (hClean : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ q o, IsDyadic q →
        CluScaleWitness κ T k RX RY q o → CleanClusterBins κ T k RX RY q o) :
    ∀ (k : ℕ) (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ClusterPatchData κ T k RX RY q o := by
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
  S_lower : (1 / 400 : ℝ) * T.S.N k ≤ 𝒯.S
  S_upper : 𝒯.S ≤ T.S.N k
  measured_scales : ∀ i, (𝒯.P i).g = gScale κ T k (𝒯.P i).resX (𝒯.P i).resY ∧
    (𝒯.P i).q = qScale κ T k (𝒯.P i).resX (𝒯.P i).resY
  bounded_scale_cutoff : 𝒯.mode = .bounded → ∀ i,
    max (𝒯.P i).g (𝒯.P i).q < κ.M1 * κ.Q0
  bounded_data : 𝒯.mode = .bounded → 𝒯.m = 1 ∧ ∀ i,
    (𝒯.P i).ℓ = 0 ∧ (𝒯.P i).h = 0 ∧ (𝒯.P i).d = 1 ∧
    (1 / 400 : ℝ) * T.S.N k ≤ (𝒯.P i).M ∧ 𝒯.Q i = κ.Qbd
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

/-- A private projection bundle keeps every P13.3h component on the export
proof frontier. -/
private structure PrefixGeometryProjections {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) : Prop where
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

private theorem project_prefix_geometry {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (h : PrefixGeometry R w) : PrefixGeometryProjections R w :=
  ⟨h.leaf_card, h.parity_leaf_card, h.odd_leaf_card, h.role_count_bounds,
    h.crossing_flips, h.coordinate_partition⟩

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
    (hSamplingL : LawSubsampleStatement)
    (hBiasNode : ∀ (k : ℕ) (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      κ.M1 * κ.Q0 ≤ (g : ℝ) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g)
    (hClusterNode : ∀ (k : ℕ) (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ClusterPatchData κ T k RX RY q o)
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
  sorry

/-- P13.3f (sections/13, lines 170–182): round dyadic masses upward and retain the first complete segment. -/
theorem dyadic_rounding (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (f : PassFamily κ T k)
    (hExtracted : ExtractionData f.tiling)
    (hSelected : (f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) :
    ∃ R : RoundedFamily κ T k,
      R.orientation = f.orientation ∧ R.tiling.mode = f.tiling.mode ∧
      R.tiling.c = f.tiling.c := by
  sorry

/-- P13.3g (sections/13, lines 170–182): Kraft's equality gives a complete prefix code. -/
theorem kraft_prefix_code (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k) :
    ∃ w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k),
      PrefixCodeComplete R w := by
  sorry

/-- P13.3h (sections/13, lines 184–204): prefix geometry gives role counts and distinct crossing leaves. -/
theorem allocation_geometry (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hCode : PrefixCodeComplete R w) : PrefixGeometry R w := by
  sorry

/-- P13.3i (sections/13, lines 151–155, 205–215): fixed thresholds fit prefixes and internal dimensions
inside the assigned gain budget. -/
theorem scale_bookkeeping (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k) :
    AllocationBounds R.tiling ∧ ScaleRegimeFacts R.tiling := by
  sorry

private theorem tiling_valid_of_parts {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hPrefix : PrefixCodeComplete R w)
    (hGeometry : PrefixGeometry R w)
    (_hGeometryProjections : PrefixGeometryProjections R w)
    (_hScaleRegime : ScaleRegimeFacts R.tiling)
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
    direct_data := hE.direct_data
    cluster_data := hE.cluster_data
    allocation_bounds := by
      simpa [𝒯, Rw, withPrefixWords, AllocationBounds, Tiling.gain] using hAlloc
    clique_scales := hE.clique_scales }
  intro v
  change ∃! i, v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)
  exact hPrefix v

/-- P13.3 (sections/13, lines 52–216): extraction and allocation in one selected mode, orientation, and colour. -/
theorem extraction_allocation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ 𝒯 : Tiling κ (T.orient o) k, Tiling.Valid 𝒯 := by
  have hSample := random_subset_lemma
  have hDirect := direct_patch_from_bias κ hκ T hSample.1
  have hClusterTrim := clean_cluster_scale_witness κ hκ T hInit
  have hCluster := cluster_patch_from_witness κ hκ T hInit hSample.2 hClusterTrim
  have hBounded := bounded_patch κ T
  have hScaleSpec := d13_1_residual_scale_specification
  have hScaleBounds := residual_scale_bounds κ hκ T hInit hDeepι hClu
  have hPass := extraction_passes κ hκ T hInit hDeep hDeepι hClu
    hSample.1 hSample.2 hDirect hCluster hBounded hScaleSpec hScaleBounds
  filter_upwards [hPass] with k hPool
  obtain ⟨pool⟩ := hPool
  obtain ⟨f, hf, hselected⟩ := type_selection κ T k pool.families
    pool.families_mass pool.type_tags_nodup pool.mass_or_bounded
  have hFamilyExtraction := f.extracted
  obtain ⟨R, hOrient, hMode, hColour⟩ :=
    dyadic_rounding κ hκ T k f hFamilyExtraction hselected
  obtain ⟨w, hCode⟩ := kraft_prefix_code κ T k R
  have hGeom := allocation_geometry κ T k R w hCode
  have hGeomProjections := project_prefix_geometry R w hGeom
  have hScaleFacts := scale_bookkeeping κ hκ T k R
  refine ⟨R.orientation, (withPrefixWords R w).tiling, ?_⟩
  exact tiling_valid_of_parts R w hCode hGeom hGeomProjections
    hScaleFacts.2 hScaleFacts.1

end HypercubeRamsey.S13
