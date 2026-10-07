import HypercubeRamsey.S18.Needs

namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators

noncomputable def densityScale (T : Stage) (k : ℕ) : ℝ :=
  (T.S.N k : ℝ) / (2 : ℝ) ^ T.S.n k

/-- The paper index is the number of classes remaining, not the processed index. -/
noncomputable def lateError (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (remaining : ℕ) : ℝ :=
  Real.rpow (densityScale T k) (-κ.β) * Real.exp (-κ.β * PT.tiling.gain i) *
    Real.rpow 2 (-κ.β * remaining)

def ScheduleAt (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (G : LowGeom PT) (Kβ : ℝ) : Prop :=
  ∀ i, (∀ j : Fin G.r, Real.rpow (T.S.n k : ℝ) (-0.02) ≤
    lateError κ T k PT i (G.r - j.val)) ∧
    (∑ j : Fin G.r, lateError κ T k PT i (G.r - j.val)) ≤
      Kβ * Real.rpow (densityScale T k) (-κ.β) * Real.exp (-κ.β * PT.tiling.gain i)

def SmallErrors (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) (G : LowGeom PT) (ε : ℝ) : Prop :=
  ∀ i, (max 1 (PT.tiling.P i).h : ℝ) *
    (∑ j : Fin G.r, lateError κ T k PT i (G.r - j.val)) ≤ ε

def LargeIndex (κ : CConsts) (T : Stage) (k : ℕ) : Prop :=
  Real.exp κ.Q0 ≤ (T.S.n k : ℝ)

theorem eventually_largeIndex (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, LargeIndex κ T k := by
  let n₀ := ⌈Real.exp κ.Q0⌉₊
  have hn : ∀ᶠ k in atTop, n₀ ≤ T.S.n k := T.S.n_tendsto.eventually_ge_atTop n₀
  filter_upwards [hn] with k hk
  have hcast : (n₀ : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hk
  exact le_trans (Nat.le_ceil _) hcast

/-- Data constructed jointly by §§16–17. `sigma` is read from the own fresh
cell; early labels, palettes and list failures have the formulas below.
The estimate fields are upstream obligations, not new late estimates. -/
structure LateData {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) where
  geom : LowGeom PT
  fresh : FreshCell geom
  encoding : LateEncoding fresh
  l16_valid : L16QuantitativeValidity geom fresh
  chi : Fin PT.tiling.m → ℕ
  low_mode : PT.tiling.mode.isLow
  constants : κ.Admissible
  chi_pos : ∀ i, 0 < chi i
  colourOf : ∀ v : Pos T k, Fin (chi (geom.patchOf v))
  palettes : ∀ i, Fin (chi i) → Finset (Fin (T.S.N k))
  palette_nonempty : ∀ i a, (palettes i a).Nonempty
  palette_subset : ∀ i a, palettes i a ⊆ (PT.tiling.P i).X
  palettes_global_disjoint : ∀ p q : (Σ i : Fin PT.tiling.m, Fin (chi i)), p ≠ q →
    Disjoint (palettes p.1 p.2) (palettes q.1 q.2)
  palette_disjoint : ∀ i a a', a ≠ a' → Disjoint (palettes i a) (palettes i a')
  palette_size : ∀ i a, (palettes i a).card ≤ 2 * ((PT.tiling.P i).M : ℝ) / chi i
  fallback : Fin (T.S.N k)
  /-- Initial odd labels already assigned by the cell states; dummies at late roles. -/
  late_pool_pos : ∀ j, 0 < (encoding.base.latePool j).card
  processed_mono : ∀ j t, j.val ≤ t.val → encoding.base.processed j ⊆ encoding.base.processed t
  class_before : ∀ j t, j.val < t.val → encoding.base.classes j ⊆ encoding.base.processed t
  early_injective : ∀ x : encoding.InitInput, 0 < encoding.permLaw.w x → x.1 ∈ permPools geom →
    (∀ C, fresh.typical C (x.1 C)) →
    Function.Injective (fun b : {v : Pos T k // ¬ IsEvenRole v} =>
      fresh.label (geom.cellOf b.1) ((encoding.initialState x) (geom.cellOf b.1)) b.1)
  early_support : ∀ x : encoding.InitInput, 0 < encoding.permLaw.w x →
    (∀ C, fresh.typical C (x.1 C)) → ∀ b, ¬ IsEvenRole b →
    fresh.label (geom.cellOf b) ((encoding.initialState x) (geom.cellOf b)) b ∈ (PT.tiling.P (geom.patchOf b)).Y

namespace LateData
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} (D : LateData hPT)

noncomputable def palette (v : Pos T k) := D.palettes (D.geom.patchOf v) (D.colourOf v)
noncomputable def sigma (v : Pos T k) (s : Config D.fresh) (x : Fin (T.S.N k)) : ℝ :=
  D.fresh.prior (D.geom.cellOf v) (s (D.geom.cellOf v)) v x
noncomputable def earlyLabel (s : Config D.fresh) (b : Pos T k) :=
  D.fresh.label (D.geom.cellOf b) (s (D.geom.cellOf b)) b
noncomputable def externalEarly (v : Pos T k) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => a ∉ PT.tiling.Icoord (D.geom.patchOf v) ∧
    D.geom.classOf (flipPos v a) = none
noncomputable def initialWeight (v : Pos T k) (s : Config D.fresh) (x : Fin (T.S.N k)) : ℝ :=
  D.sigma v s x * ∏ a ∈ D.externalEarly v,
    (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) then 1 else 0) /
      rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a)))
noncomputable def withheldList (v : Pos T k) (s : Config D.fresh)
    (J : Finset (Fin (T.S.n k))) : Finset (Fin (T.S.N k)) :=
  (PT.envelope (D.geom.patchOf v)).filter fun x =>
    ∀ a ∈ D.externalEarly v \ J, Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a))
noncomputable def listFailure (v : Pos T k) (s : Config D.fresh) : Prop :=
  (∑ x, D.initialWeight v s x) < 1 / 2 ∨
    ∃ J : Finset (Fin (T.S.n k)), J ⊆ D.externalEarly v ∧
      (J.card : ℝ) ≤ Real.log (T.S.n k) ^ 4 ∧
      Real.exp (Real.log (T.S.n k) ^ 8) < (D.withheldList v s J).card
noncomputable def internalValid (v : Pos T k) (s : Config D.fresh) : Prop :=
  (∀ x, 0 ≤ D.sigma v s x) ∧ (∑ x, D.sigma v s x) = 1 ∧
  (if PT.tiling.mode.isCluster then
    ∀ x, (T.S.N k : ℝ) * D.sigma v s x ≤
      (2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h *
        Real.exp (-500 * PT.tiling.gain (D.geom.patchOf v))
   else ∃ q ∈ PT.activeVertices, ∀ x, D.sigma v s x =
    if x ∈ PT.mesh.corner q (D.geom.patchOf v) then
      1 / ((PT.mesh.corner q (D.geom.patchOf v)).card : ℝ) else 0) ∧
  (∃ q ∈ PT.activeVertices, ∀ x, x ∉ PT.mesh.corner q (D.geom.patchOf v) → D.sigma v s x = 0) ∧
  (∀ a ∈ PT.tiling.Icoord (D.geom.patchOf v), ∀ x, D.sigma v s x ≠ 0 →
    Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)))
noncomputable def initialValid (v : Pos T k) (s : Config D.fresh) : Prop :=
  D.internalValid v s ∧ ¬ D.listFailure v s ∧
    1 / (4 * (D.chi (D.geom.patchOf v) : ℝ)) ≤ ∑ x ∈ D.palette v, D.initialWeight v s x

/-- Exact normalization with a fixed point-mass fallback, including zero mass. -/
noncomputable def normalize (D : LateData hPT) (w : Fin (T.S.N k) → ℝ) : Law (T.S.N k) :=
  if hw : (∀ x, 0 ≤ w x) ∧ 0 < ∑ x, w x then
    { w := fun x => w x / ∑ z, w z
      nonneg := fun x => div_nonneg (hw.1 x) hw.2.le
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hw.2) }
  else Law.dirac D.fallback
noncomputable def initialPrior (v : Pos T k) (s : Config D.fresh) : Law (T.S.N k) :=
  if D.initialValid v s then D.normalize (fun x => if x ∈ D.palette v then D.initialWeight v s x else 0)
  else Law.dirac D.fallback
noncomputable def priorAt (j : Fin (D.geom.r + 1)) (v : Pos T k)
    (h : D.encoding.base.History j) : Law (T.S.N k) :=
  if D.initialValid v h.1 then D.normalize fun x =>
    (D.initialPrior v h.1).w x *
      ∏ b : D.encoding.base.ProcessedRole j,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
        else 1
  else Law.dirac D.fallback
noncomputable def currentPrior (j : Fin D.geom.r) := D.priorAt j.castSucc
noncomputable def remainingNeighbors (v : Pos T k) (j : Fin D.geom.r) : ℕ :=
  (Finset.univ.filter fun a : Fin (T.S.n k) =>
    ∃ s : Fin D.geom.r, j.val ≤ s.val ∧ D.geom.classOf (flipPos v a) = some s).card
noncomputable def error (v : Pos T k) (j : Fin D.geom.r) : ℝ :=
  lateError κ T k PT (D.geom.patchOf v) (D.geom.r - j.val)
noncomputable def nonconflict (v : Pos T k) (x z : Fin (T.S.N k)) : Prop :=
  |pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) x z| ≤ κ.ξ
noncomputable def directCells (v : Pos T k) : Finset D.geom.Cell :=
  {D.geom.cellOf v} ∪ (D.externalEarly v).image (fun a => D.geom.cellOf (flipPos v a))

noncomputable def withKernels (K : LateKernels D.encoding.base) : LateData hPT :=
  { D with encoding := { D.encoding with kernels := K } }

noncomputable def beforeHistory {t : Fin (D.geom.r + 1)}
    (h : D.encoding.base.History t) (j : Fin (D.geom.r + 1)) (hj : j.val ≤ t.val) :
    D.encoding.base.History j :=
  (h.1, fun b => h.2 ⟨b.1, D.processed_mono j t hj b.2⟩)
noncomputable def pastRows {t : Fin (D.geom.r + 1)}
    (h : D.encoding.base.History t) (j : Fin D.geom.r) (hj : j.val < t.val) :
    D.encoding.base.ClassRows j :=
  fun b => h.2 ⟨b.1, D.class_before j t hj b.2⟩

/-- Whole-cell law: iid unpinned pool conditioned on individual typicality,
then a fresh state. The zero branch is excluded by `Spec.typical_positive`. -/
noncomputable def cellPoolLaw (C : D.geom.Cell) : FinLaw (D.fresh.Pool C) :=
  FinLaw.map D.encoding.iidLaw (fun P => P C)
noncomputable def typicalPools (C : D.geom.Cell) : Finset (D.fresh.Pool C) :=
  Finset.univ.filter (D.fresh.typical C)
noncomputable def typicalFresh (C : D.geom.Cell) : FinLaw (D.fresh.Pool C × D.fresh.State C) :=
  let law := D.cellPoolLaw C
  let good := D.typicalPools C
  if h : 0 < ∑ P ∈ good, law.w P then
    FinLaw.bind (FinLaw.cond law good h) (D.fresh.fresh C)
  else FinLaw.dirac ((D.l16_valid.pools_nonempty.choose C), D.fresh.fallback C)

/-- Fresh sampler comparison on separated group consultations, for
arbitrary bounded nonnegative tests. This is the explicit §§16 input bridge;
it carries calibration and repeat losses, not any endpoint or Hall estimate. -/
noncomputable def freshQueryIntegral (q : ℕ) (odd : Fin q → Pos T k)
    (f : Fin q → Fin (T.S.N k) → ℝ) : ℝ :=
  D.encoding.iidLaw.E (fun pools =>
    if ∀ a, D.fresh.typical (D.geom.cellOf (odd a)) (pools (D.geom.cellOf (odd a))) then
      (FinLaw.pi fun C => D.fresh.fresh C (pools C)).E (fun s => ∏ a, f a (D.earlyLabel s (odd a))) else 0)
def FreshCalibration : Prop :=
  (∀ v y, IsEvenRole v →
    D.encoding.iidLaw.E (fun pools => if D.fresh.typical (D.geom.cellOf v) (pools (D.geom.cellOf v)) then
      (D.fresh.fresh (D.geom.cellOf v) (pools (D.geom.cellOf v))).E (fun s => D.fresh.prior (D.geom.cellOf v) s v y)
      else 0) ≤ κ.KB / ((PT.tiling.P (D.geom.patchOf v)).M : ℝ)) ∧
  (∀ q : ℕ, q ≤ T.S.n k ^ 2 → ∀ odd : Fin q → Pos T k, Function.Injective odd →
    (∀ a, ¬ IsEvenRole (odd a) ∧ D.geom.classOf (odd a) = none) →
    (∀ a a', a ≠ a' → D.geom.cellOf (odd a) = D.geom.cellOf (odd a') →
      (hammingDist (odd a) (odd a') : ℝ) >
        20 * κ.ρ * (PT.tiling.P (D.geom.patchOf (odd a))).h) →
    ∀ f : Fin q → Fin (T.S.N k) → ℝ, (∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) →
      D.freshQueryIntegral q odd f ≤ Real.exp (0.002 * q) *
        ∏ a, ((∑ y, (PT.πraw (D.geom.patchOf (odd a))).w y * f a y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3))))

noncomputable def upstreamBad (f : D.geom.Cell ⊕ Pos T k) (x : D.encoding.InitInput) : Prop :=
  match f with
  | .inl C => ¬ D.fresh.typical C (x.1 C)
  | .inr v => Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) <
      (FinLaw.pi fun C => D.fresh.fresh C (x.1 C)).pr (D.encoding.events.S v)

/-- Upstream §§16–17 statements needed for arbitrary *constructed* data. -/
structure Spec : Prop where
  corner_mass : ProfileCornerMass PT
  fresh_internal : ∀ (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh), (∀ C, D.fresh.typical C (pools C)) →
    0 < (FinLaw.pi fun C => D.fresh.fresh C (pools C)).w s →
      ∀ v, IsEvenRole v → D.internalValid v s
  thresholds : LateThresholds κ
  calibration : D.FreshCalibration
  /-- L17.2's pool/list input estimate, also under any one global slot pin. -/
  upstream_bad : ∀ f, D.encoding.permLaw.pr (D.upstreamBad f) ≤
    Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2))
  upstream_bad_pinned : ∀ C (slot : Fin (D.geom.nslot C)) (bin : Bin PT.tiling (D.geom.cellPatch C)) f,
    D.encoding.permLaw.pr (fun x => x.1 C slot = bin ∧ D.upstreamBad f x) /
      D.encoding.permLaw.pr (fun x => x.1 C slot = bin) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2))
  typical_positive : ∀ C, 0 < ∑ P ∈ D.typicalPools C, (D.cellPoolLaw C).w P
  fresh_singleton : ∀ b, ¬ IsEvenRole b → D.geom.classOf b = none → ∀ y,
    (D.typicalFresh (D.geom.cellOf b)).pr (fun Ps =>
      D.fresh.label (D.geom.cellOf b) Ps.2 b = y) ≤
        (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) * (PT.π (D.geom.patchOf b)).w y
  scope_eq : ∀ v, D.encoding.events.scope v = D.directCells v
  palette_counts : ∀ i a,
    let rows := Finset.univ.filter fun v : Pos T k => IsEvenRole v ∧
      (D.geom.patchOf v = i ∧ D.palette v = D.palettes i a)
    (rows.card : ℝ) ≤ κ.KB * ((PT.tiling.P i).M : ℝ) / D.chi i / densityScale T k ∧
      (2 : ℝ) ^ ((T.S.n k : ℝ) - Real.sqrt (T.S.n k)) ≤ rows.card
  palette_separation : ∀ v w, IsEvenRole v → IsEvenRole w → v ≠ w → D.palette v = D.palette w →
    (∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf v) → v a = w a) →
      500 * κ.ρ * (PT.tiling.P (D.geom.patchOf v)).h < (hammingDist v w : ℝ)
  events_eq : ∀ v s, D.encoding.events.S v s ↔ IsEvenRole v ∧ D.listFailure v s
  initial_cap : ∀ v s, IsEvenRole v → D.initialValid v s → ∀ x,
    (D.initialPrior v s).w x ≤ 4 * κ.KB / densityScale T k *
      Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v ⟨0, D.l16_valid.r_pos⟩ : ℝ))
  initial_success : ∀ x : D.encoding.InitInput, 0 < D.encoding.permLaw.w x →
    (∀ C, D.fresh.typical C (x.1 C)) →
    (∀ v, ¬ D.encoding.events.S v (D.encoding.initialState x)) →
    ∀ v, IsEvenRole v → D.initialValid v (D.encoding.initialState x)
  prior_local : ∀ v s s', (∀ C ∈ D.directCells v, s C = s' C) →
    D.initialWeight v s = D.initialWeight v s'

end LateData
end HypercubeRamsey.S18
