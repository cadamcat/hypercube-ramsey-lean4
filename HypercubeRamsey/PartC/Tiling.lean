import HypercubeRamsey.PartC.Consts

/-!
# Section 13 patch and tiling definitions (D13.1 and D13.T)

This file records the extracted scales, patches, prefix geometry, and the
named validity obligations used by the later section lanes.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Absolute-bias witness in a residual pair. -/
def BiasWitness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) : Prop :=
  ∃ (U V : Finset (Fin (T.S.N k))) (hU : U.Nonempty) (hV : V.Nonempty),
    U ⊆ RX ∧ V ⊆ RY ∧
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aB) ≤ U.card ∧
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aB) ≤ V.card ∧
    (b : ℝ) / T.S.n k ≤
      |dens (T.S.E k) true (Law.unifCore U hU) (Law.unifCore V hV) - 1 / 2|

/-- Correlation of two labels when the law is on the first side (`o = false`) or second side (`o = true`). -/
noncomputable def pairCorr {N : ℕ} (E : Fin N → Fin N → Prop) (o : Bool)
    (μ : Law N) (y y' : Fin N) : ℝ :=
  if o then corr E true μ.w y y' else
    ∑ x, μ.w x * fv E true x y * fv E true x y'

/-- Cluster-scale witness with disjoint bins of labels. -/
def CluScaleWitness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) (o : Bool) : Prop :=
  ∃ (U : Finset (Fin (T.S.N k))) (hU : U.Nonempty) (m : ℕ)
    (B : Fin m → Finset (Fin (T.S.N k))),
    U ⊆ (if o then RY else RX) ∧
    (∀ j, B j ⊆ (if o then RX else RY)) ∧
    Set.PairwiseDisjoint Set.univ B ∧
    (∀ j, Real.exp b ≤ (B j).card) ∧
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ U.card ∧
    (T.S.N k : ℝ) * Real.exp (-(b : ℝ) ^ κ.aC) ≤ (Finset.univ.biUnion B).card ∧
    ∀ j, ∀ y ∈ B j, ∀ y' ∈ B j, y ≠ y' →
      κ.θ < pairCorr (T.S.E k) o (Law.unifCore U hU) y y'

/-- Largest measured dyadic bias scale, with `1` for an empty witness set. -/
noncomputable def gScale (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : ℕ :=
  2 ^ ((Finset.range (2 * T.S.n k + 2)).filter
    (fun j => 1 ≤ j ∧ BiasWitness κ T k RX RY (2 ^ j))).sup id

/-- Largest measured dyadic cluster scale, with `1` for an empty witness set. -/
noncomputable def qScale (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : ℕ :=
  2 ^ ((Finset.range (T.S.N k + 2)).filter
    (fun j => 1 ≤ j ∧ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o)).sup id

/-- D13.T: extraction mode of a patch tiling. -/
inductive Mode
  | bounded | lowDirect | highDirect | lowCluster | highSmall | highLarge
  deriving DecidableEq

instance : Fintype Mode := ⟨
  {Mode.bounded, Mode.lowDirect, Mode.highDirect, Mode.lowCluster, Mode.highSmall, Mode.highLarge},
  by intro x; cases x <;> simp⟩

/-- Whether a mode is a cluster mode. -/
def Mode.isCluster : Mode → Prop
  | .lowCluster | .highSmall | .highLarge => True
  | _ => False

/-- Whether a mode is among the later low-mode cases. -/
def Mode.isLow : Mode → Prop
  | .bounded | .lowDirect | .lowCluster => True
  | _ => False

/-- D13.T: one extracted patch, with equal-sized first and second supports. -/
structure Patch (T : Stage) (k : ℕ) where
  X : Finset (Fin (T.S.N k))
  Y : Finset (Fin (T.S.N k))
  M : ℕ
  resX : Finset (Fin (T.S.N k))
  resY : Finset (Fin (T.S.N k))
  g : ℕ
  q : ℕ
  h : ℕ
  ℓ : ℕ
  d : ℕ
  bins : Finpartition Y
  cardX : X.card = M
  cardY : Y.card = M
  X_res : X ⊆ resX
  Y_res : Y ⊆ resY

/-- D13.T: family of extracted, allocated patches at one stage index. -/
structure Tiling (κ : CConsts) (T : Stage) (k : ℕ) where
  mode : Mode
  c : Colour
  m : ℕ
  P : Fin m → Patch T k
  S : ℕ
  w : Fin m → CubePos (T.S.n k)
  reserveX : Finset (Fin (T.S.N k))
  reserveY : Finset (Fin (T.S.N k))
  Q : Fin m → ℕ

namespace Tiling

/-- Prefix leaf assigned to patch `i`. -/
def leaf {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Set (CubePos (T.S.n k)) :=
  prefixLeaf (𝒯.P i).ℓ (𝒯.w i)

/-- Tail coordinates used as the internal coordinates of patch `i`. -/
def Icoord {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Finset (Fin (T.S.n k)) :=
  topCoordinates (T.S.n k) (𝒯.P i).h

/-- Gain budget attached to a patch. -/
noncomputable def gain {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : ℝ :=
  match 𝒯.mode with
  | .bounded => 0
  | .lowDirect | .highDirect => (𝒯.P i).g / 1000
  | .lowCluster | .highSmall | .highLarge => κ.a * (𝒯.P i).h / 10 ^ 6

/-- Internal sampler tuple count `⌈h^(3ω)⌉`. -/
noncomputable def kScale {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : ℕ := sliceK κ (𝒯.P i).h

/-- Internal sampler round count `⌈h^ω⌉`. -/
noncomputable def tScale {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : ℕ := sliceT κ (𝒯.P i).h

/-- A cell-free view of the crossing and bulk coordinates. -/
def crossingCoords {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun j => j.val < (𝒯.P i).ℓ

/-- Coordinates neither in the prefix nor in the internal tail. -/
def bulkCoords {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun j =>
    (𝒯.P i).ℓ ≤ j.val ∧ j ∉ 𝒯.Icoord i

/-- D13.T: named validity fields for the extraction and prefix-allocation output. -/
structure Valid {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) : Prop where
  reserveX_card : 𝒯.reserveX.card = T.S.N k / 3
  reserveY_card : 𝒯.reserveY.card = T.S.N k / 3
  reserveX_subset : 𝒯.reserveX ⊆ T.X k
  reserveY_subset : 𝒯.reserveY ⊆ T.Y k
  patch_supports : ∀ i, (𝒯.P i).X ⊆ (𝒯.P i).resX ∧
    (𝒯.P i).resX ⊆ T.X k \ 𝒯.reserveX ∧
    (𝒯.P i).Y ⊆ (𝒯.P i).resY ∧
    (𝒯.P i).resY ⊆ T.Y k \ 𝒯.reserveY
  patch_nonempty : ∀ i, (𝒯.P i).X.Nonempty ∧ (𝒯.P i).Y.Nonempty
  /-- Every physical bin has `d` labels in every mode (singleton bins in direct and bounded
  modes, sections/16 line 15). -/
  bins_card : ∀ i, ∀ B ∈ (𝒯.P i).bins.parts, B.card = (𝒯.P i).d
  patch_X_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).X (𝒯.P j).X
  patch_Y_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).Y (𝒯.P j).Y
  S_lower : (1 / 400 : ℝ) * T.S.N k ≤ 𝒯.S
  S_upper : 𝒯.S ≤ T.S.N k
  selected_mass : (𝒯.S : ℝ) / 2 < ∑ i, (𝒯.P i).M
  dyadic_mass_lower : ∀ i, (𝒯.P i).M / 𝒯.S ≤ (2 : ℝ) ^ (-((𝒯.P i).ℓ : ℤ))
  dyadic_mass_upper : ∀ i, (2 : ℝ) ^ (-((𝒯.P i).ℓ : ℤ)) < 2 * (𝒯.P i).M / 𝒯.S
  dyadic_sum : ∑ i, (2 : ℝ) ^ (-((𝒯.P i).ℓ : ℤ)) = 1
  prefix_complete : ∀ v : CubePos (T.S.n k), ∃! i, v ∈ 𝒯.leaf i
  prefix_internal_length : (Finset.univ.sup fun i : Fin 𝒯.m => (𝒯.P i).ℓ) +
    (Finset.univ.sup fun i : Fin 𝒯.m => (𝒯.P i).h) ≤ T.S.n k
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
    ((𝒯.P i).h : ℝ) < 2 * Real.rpow (𝒯.P i).q (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ∧
    ((𝒯.mode = .lowCluster) ↔ (𝒯.P i).q ≤ Real.rpow (Real.log (T.S.n k)) κ.cq) ∧
    ((𝒯.mode = .highSmall) ↔
      (Real.rpow (Real.log (T.S.n k)) κ.cq < (𝒯.P i).q ∧
       (𝒯.P i).q ≤ (Real.log (T.S.n k)) ^ 2)) ∧
    ((𝒯.mode = .highLarge) ↔ (Real.log (T.S.n k)) ^ 2 < (𝒯.P i).q)
  allocation_bounds : ∀ i,
    (max (𝒯.P i).h (𝒯.P i).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι ∧
    (𝒯.mode = .bounded ∨
      ((𝒯.P i).ℓ : ℝ) ≤ 𝒯.gain i / (1000 * κ.u) ∧
      Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤ 𝒯.gain i / (1000 * κ.u))
  clique_scales : ∀ i,
    (𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q ^ 2 ≤ 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).q ^ 2 ∧ 𝒯.kScale i < 𝒯.Q i) ∧
    ((𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).g / (2 * Real.sqrt κ.M1) < 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).g / Real.sqrt κ.M1 ∧ (𝒯.P i).q < 𝒯.Q i)

end Tiling

end HypercubeRamsey
