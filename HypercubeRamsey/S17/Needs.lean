import HypercubeRamsey.S17.Defs

/-!
# Producer contracts needed by Section 17

These certificates must be supplied by Sections 13--16. They state geometry,
sampler provenance, finite-history, and comparison inputs, never a Section 17
list, palette, or resampling probability conclusion. Constants `K` are fixed
before the eventual index and all local data.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

namespace ListGateContext

variable (D : ListGateContext κ T k PT)

/-- SHARED: L16.1 geometry and L16.0 scales, for the actual `LowGeom`.
Slice separation means nearby positions in one cell belong to the same
internal slice. Star-cell distinctness is the consequence needed in §17. -/
structure S17GeometryValidity (K : ℝ) : Prop where
  ids_injective : Function.Injective D.G.ids
  class_scale : κ.A0 * Real.log (T.S.n k : ℝ) ≤ D.G.r ∧
    (D.G.r : ℝ) < 2 * κ.A0 * Real.log (T.S.n k : ℝ)
  late_count : ∀ v : Pos T k, IsEvenRole v →
    (D.G.r : ℝ) / 2 ≤ (Finset.univ.filter fun j : Fin (T.S.n k) =>
      (D.G.classOf (flipPos v j)).isSome).card
  internal_late_count : ∀ v : Pos T k, IsEvenRole v →
    ((PT.tiling.Icoord (D.G.patchOf v)).filter fun j =>
      (D.G.classOf (flipPos v j)).isSome).card ≤ 1
  cell_nonempty : ∀ C : D.G.Cell, ∃ v, D.G.cellOf v = C
  slice_closed : ∀ v w : Pos T k, D.G.patchOf w = D.G.patchOf v →
    (∀ j, j ∉ PT.tiling.Icoord (D.G.patchOf v) → v j = w j) →
    D.G.cellOf v = D.G.cellOf w
  slice_separated : ∀ v w : Pos T k, D.G.cellOf v = D.G.cellOf w →
    (hammingDist v w : ℝ) ≤ (Real.log (T.S.n k : ℝ)) ^ 3 →
    ∀ j, j ∉ PT.tiling.Icoord (D.G.patchOf v) → v j = w j
  star_distinct : ∀ v : Pos T k, IsEvenRole v →
    (∀ w ∈ D.externalEarly v, D.G.cellOf w ≠ D.G.cellOf v) ∧
    (∀ w ∈ D.externalEarly v, ∀ z ∈ D.externalEarly v,
      D.G.cellOf w = D.G.cellOf z → w = z)
  cell_size : ∀ C : D.G.Cell,
    (Finset.univ.filter fun v : Pos T k => D.G.cellOf v = C).card ≤
      (T.S.n k) ^ κ.Ac
  slots_eq : ∀ C : D.G.Cell, D.G.nslot C =
    ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (D.G.cellPatch C)).d⌉₊
  slots_lower : ∀ C : D.G.Cell,
    Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) - 1) ≤ D.G.nslot C
  slots_upper : ∀ C : D.G.Cell,
    (D.G.nslot C : ℝ) ≤ Real.rpow (T.S.n k : ℝ) ((κ.Ac : ℝ) + 1)
  slot_factor_eq : ∀ b : Pos T k, D.slotFactor b =
    (Fintype.card (Bin PT.tiling (D.G.patchOf b)) : ℝ) /
      D.G.nslot (D.G.cellOf b)
  height_bound : ∀ i, ((PT.tiling.P i).h : ℝ) ≤
    Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ)
  prefix_bound : ∀ i, ((PT.tiling.P i).ℓ : ℝ) ≤
    K * Real.sqrt (Real.log (T.S.n k : ℝ))
  mass_bound : ∀ i, Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
    K * Real.sqrt (Real.log (T.S.n k : ℝ))
  degree_drift : ∀ i x, x ∈ PT.envelope i →
    (T.S.n k : ℝ) * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
      K * Real.log (T.S.n k : ℝ)
  conflict_bound : ∀ i a, a ∈ PT.activeVertices → ∀ x,
    (((PT.mesh.corner a i).filter fun z =>
      κ.ξ < |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|).card : ℝ) ≤
      K * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ))

/-- Internal solver word after the parity-changing translation of §14:35,95.
An odd outer parity flips internal coordinate zero. -/
def SolverRoleMatches (v : Pos T k)
    (e : EvenRole PT.tiling (D.G.patchOf v)) : Prop :=
  ∀ (hle : (PT.tiling.P (D.G.patchOf v)).h ≤ T.S.n k)
    (j : Fin (PT.tiling.P (D.G.patchOf v)).h),
    e.1 j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (D.G.patchOf v) then false else v l) ∧ j.val = 0
      then !(v ⟨T.S.n k - (PT.tiling.P (D.G.patchOf v)).h + j.val,
        by omega⟩)
      else v ⟨T.S.n k - (PT.tiling.P (D.G.patchOf v)).h + j.val,
        by omega⟩

/-- SHARED: the unrestricted base experiment in L16.7 is the solver's raw
record/reference experiment; direct modes use the deterministic cleaned law.
The functional identity ties the abstract finite outcome type to that producer. -/
structure BasePriorSource (v : Pos T k) where
  Ω : Type
  [outcomes : Fintype Ω]
  law : FinLaw Ω
  readout : Ω → Fin (T.S.N k) → ℝ
  solver_source : IsEvenRole v → PT.tiling.mode.isCluster →
    ∃ (S : SliceSolver κ PT.tiling (D.G.patchOf v) PT.mesh)
      (e : EvenRole PT.tiling (D.G.patchOf v)),
      PT.solver (D.G.patchOf v) = some S ∧ D.SolverRoleMatches v e ∧
      ∀ Φ : (Fin (T.S.N k) → ℝ) → ℝ,
        law.E (fun ω => Φ (readout ω)) =
          (S.recLaw PT.parameter).E (fun W =>
            (S.refLaw W).E (fun ω => Φ (S.σ e W (nbrLabels e.1 ω.2))))
  direct_source : IsEvenRole v → ¬ PT.tiling.mode.isCluster →
    ∃ σ : Fin (T.S.N k) → ℝ, D.CleanInitialPrior v σ ∧ ∀ ω, readout ω = σ

instance (v : Pos T k) (B : D.BasePriorSource v) : Fintype B.Ω := B.outcomes

/-- Only the local row readout is counted, not the configuration outside the
star. Finite families are fixed before choosing the label colouring. -/
abbrev LocalReadout (v : Pos T k) :=
  (Fin (T.S.N k) → ℝ) ×
    ({w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k))

/-- SHARED: L14.3/L16 finite data, the actual permission table, and L16.7
base comparison. Zero-mass invalid states are excluded by explicit validity
and local typicality. The comparison excludes an own-pool slot pin. -/
structure S17SamplerData (K : ℝ) where
  base : ∀ v : Pos T k, D.BasePriorSource v
  permittedBin : ∀ b : Pos T k, Bin PT.tiling (D.G.patchOf b) → Prop
  permission_present : ∀ (C : D.G.Cell) (P : D.F.Pool C) b,
    ∀ (hcell : D.G.cellOf b = C) y,
      y ∈ D.permittedLabels C P b ↔
        ∃ j : Fin (D.G.nslot C), y ∈ (P j).1 ∧
          permittedBin b (cast (by rw [← hcell, D.G.cellOf_patch]) (P j))
  permission_test : ∀ v : Pos T k, IsEvenRole v →
    ∀ b ∈ D.externalEarly v, ∀ B : Bin PT.tiling (D.G.patchOf b),
      permittedBin b B → ∀ y ∈ B.1,
        (base v).law.pr (fun ω => (base v).readout ω ≠ 0 ∧
          |(∑ x, (base v).readout ω x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
            2 * bstar T k) ≤ Real.exp (-κ.cperm * T.S.n k)
  localHistories : ∀ v : Pos T k, Finset (D.LocalReadout v)
  priorHistories : ∀ v : Pos T k, Finset (Fin (T.S.N k) → ℝ)
  history_count : ∀ v, Real.log (max 1 ((localHistories v).card : ℝ)) ≤
    Real.rpow (T.S.n k : ℝ) (2.01 : ℝ)
  prior_count : ∀ v, Real.log (max 1 ((priorHistories v).card : ℝ)) ≤
    Real.rpow (T.S.n k : ℝ) (2.01 : ℝ)
  history_cover : ∀ (v : Pos T k) (pools : D.PoolAssignment) (s : Config D.F),
    IsEvenRole v → D.LocalPoolsTypical v pools →
    (∀ C ∈ D.scopeCells v, D.stateValid C (pools C) (s C)) →
      (D.prior s v, fun w => D.label s w.1) ∈ localHistories v
  prior_cover : ∀ v σ, IsEvenRole v → D.ValidInitialPrior v σ → σ ∈ priorHistories v
  /-- Actual raw posterior, with all internal labels, including late dummies. -/
  posterior_origin : ∀ (v : Pos T k) (P : D.F.Pool (D.G.cellOf v))
      (s : D.F.State (D.G.cellOf v)), IsEvenRole v →
    D.F.typical (D.G.cellOf v) P → D.stateValid (D.G.cellOf v) P s →
    PT.tiling.mode.isCluster →
    ∃ (S : SliceSolver κ PT.tiling (D.G.patchOf v) PT.mesh)
      (e : EvenRole PT.tiling (D.G.patchOf v)) (W : ∀ r, S.Val r)
      (ys : InternalLabels PT.tiling (D.G.patchOf v)),
      PT.solver (D.G.patchOf v) = some S ∧ D.SolverRoleMatches v e ∧
      0 < (S.recLaw PT.parameter).w W ∧
      (∀ (hle : (PT.tiling.P (D.G.patchOf v)).h ≤ T.S.n k)
        (j : Fin (PT.tiling.P (D.G.patchOf v)).h),
        ys j = D.F.label (D.G.cellOf v) s
          (flipPos v ⟨T.S.n k - (PT.tiling.P (D.G.patchOf v)).h + j.val,
            by omega⟩)) ∧
      D.F.prior (D.G.cellOf v) s v = S.σ e W ys
  internal_hits : ∀ v P s, IsEvenRole v →
    D.F.typical (D.G.cellOf v) P → D.stateValid (D.G.cellOf v) P s →
    ∀ j ∈ PT.tiling.Icoord (D.G.patchOf v), ∀ x,
      D.F.prior (D.G.cellOf v) s v x ≠ 0 →
      Hits (T.S.E k) PT.tiling.c x
        (D.F.label (D.G.cellOf v) s (flipPos v j))
  base_comparison : ∀ (hpools : (permPools D.G).Nonempty) v,
    IsEvenRole v → ∀ Φ : (Fin (T.S.N k) → ℝ) → ℝ,
      (∀ σ, 0 ≤ Φ σ) → Φ 0 = 0 →
      (iidPoolLaw D.G hpools).E (fun pools =>
        if D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) then
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).E
            (fun s => Φ (D.F.prior (D.G.cellOf v) s v)) else 0) ≤
        K * (base v).law.E (fun ω => Φ ((base v).readout ω))

/-- SHARED: fixed-index L16.1/2/6/7 certificate, replacing the incomplete
prior-cap-only interface. `K` is an upstream fixed constant, not selected per
index. Pool probability tails and singleton bounds are L16 conclusions. -/
structure L16QuantitativeValidity (K : ℝ) where
  geometry : D.S17GeometryValidity K
  sampler : D.S17SamplerData K
  pool_support_nonempty : (permPools D.G).Nonempty
  pool_typical_tail : ∀ v,
    (permPoolLaw D.G pool_support_nonempty).pr
      (fun pools => ¬ D.LocalPoolsTypical v pools) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k))
  pool_typical_tail_pinned : ∀ v (pin : D.PoolPin)
      (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
        (permPoolLaw D.G pool_support_nonempty).w pools),
    (D.pinnedPoolLaw pool_support_nonempty pin hpin).pr
      (fun pools => ¬ D.LocalPoolsTypical v pools) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k))
  singleton_bound : ∀ C P b y, D.F.typical C P → D.G.cellOf b = C →
    ¬ IsEvenRole b →
    (D.F.fresh C P).pr (fun s => D.F.label C s b = y) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * D.slotFactor b *
        (PT.π (D.G.patchOf b)).w y *
          (if y ∈ D.permittedLabels C P b then 1 else 0)
  prior_shape : ∀ v P s, IsEvenRole v → D.F.typical (D.G.cellOf v) P →
    D.stateValid (D.G.cellOf v) P s →
    D.CleanInitialPrior v (D.F.prior (D.G.cellOf v) s v)
  corner_size : ∀ i a, a ∈ PT.activeVertices →
    (1 - κ.a) * (PT.tiling.P i).M ≤ (PT.mesh.corner a i).card
  /-- Permutation-to-iid comparison on polynomially many queried slots,
  retaining a possible global pin; no restriction on unqueried slots. -/
  pool_iid_comparison : ∀ (μ : FinLaw D.PoolAssignment),
    D.IsPermOrPinnedPoolLaw pool_support_nonempty μ →
    ∃ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G pool_support_nonempty ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G pool_support_nonempty).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G pool_support_nonempty) (D.poolPinSet pin) hpin) ∧
      ∀ (slots : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
        (f : D.PoolAssignment → ℝ),
        slots.card ≤ (T.S.n k) ^ (κ.Ac + 4) → (∀ pools, 0 ≤ f pools) →
        (∀ p q, (∀ a ∈ slots, p a.1 a.2 = q a.1 a.2) → f p = f q) →
        μ.E f ≤ (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * ν.E f

end ListGateContext
end HypercubeRamsey
