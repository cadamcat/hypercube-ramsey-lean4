import HypercubeRamsey.PartC.Resampling

/-!
# Section 17 initial list gates and finite experiment data

The list event is evaluated from the fresh-cell state readouts of D16.F.  An
external early neighbour is a noninternal coordinate flip, including bulk
neighbours in the same patch, which has not been assigned a late class.
`FreshCell.prior` is the Section 16 readout; the quantitative certificate in
`Needs.lean` requires its solver origin and the dummy hit at late internal
neighbours.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

/-- Number `T_s` of initial resampling rounds, `⌈log² n⌉`. -/
noncomputable def initialResamplingRounds (T : Stage) (k : ℕ) : ℕ :=
  ⌈(Real.log (T.S.n k : ℝ)) ^ 2⌉₊

/-- D17.L input data: a valid profiled tiling, the low-mode cell geometry,
and the fresh state sampler with its state and permission contracts. -/
structure ListGateContext (κ : CConsts) (T : Stage) (k : ℕ)
    (PT : ProfiledTiling κ T k) where
  tiling_valid : PT.Valid
  mode_low : PT.tiling.mode.isLow
  G : LowGeom PT
  F : FreshCell G
  stateValid : ∀ C : G.Cell, F.Pool C → F.State C → Prop
  permittedLabels : ∀ C : G.Cell, F.Pool C → Pos T k → Finset (Fin (T.S.N k))
  /-- The L16.6 factor `B_b/L_b^{slot}` for a singleton label comparison. -/
  slotFactor : Pos T k → ℝ
  fresh_spec : FreshCell.Spec F stateValid permittedLabels

namespace ListGateContext

variable (D : ListGateContext κ T k PT)

/-- Convert the framework `Law` to the finite-weight law used by Part C. -/
noncomputable def lawAsFinLaw {N : ℕ} (μ : Law N) : FinLaw (Fin N) where
  w := μ.w
  nonneg := μ.nonneg
  sum_one := μ.sum_eq_one

/-- External early neighbours of an even role (D17.L).  Internal neighbours
flip the allocated internal coordinates; bulk and crossing flips are external. -/
noncomputable def externalEarly (v : Pos T k) : Finset (Pos T k) :=
  Finset.univ.filter fun w =>
    D.G.classOf w = none ∧ ∃ j : Fin (T.S.n k),
      j ∉ PT.tiling.Icoord (D.G.patchOf v) ∧ w = flipPos v j

/-- The cell scope read by `S_v`: its own cell and the cells carrying the
external early labels. -/
noncomputable def scopeCells (v : Pos T k) : Finset D.G.Cell :=
  {D.G.cellOf v} ∪ (D.externalEarly v).image D.G.cellOf

/-- The label read from a configuration at a cube position. -/
def label (s : Config D.F) (v : Pos T k) : Fin (T.S.N k) :=
  D.F.label (D.G.cellOf v) (s (D.G.cellOf v)) v

/-- The internal probability prior read at the even role. -/
def prior (s : Config D.F) (v : Pos T k) : Fin (T.S.N k) → ℝ :=
  D.F.prior (D.G.cellOf v) (s (D.G.cellOf v)) v

/-- One external hit ratio in the initial row. -/
noncomputable def hitRatio (w : Pos T k) (x y : Fin (T.S.N k)) : ℝ :=
  hit (T.S.E k) PT.tiling.c x y /
    deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x

/-- The unnormalised initial row `U_v^0` for a fixed prior and external
label assignment. -/
noncomputable def row (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (ys : Pos T k → Fin (T.S.N k)) (x : Fin (T.S.N k)) : ℝ :=
  σ x * ∏ w ∈ D.externalEarly v, D.hitRatio w x (ys w)

/-- The total initial row mass `M_v^0`. -/
noncomputable def rowMass (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (ys : Pos T k → Fin (T.S.N k)) : ℝ :=
  ∑ x, D.row v σ ys x

/-- The unweighted support left after omitting `J` external early incidences. -/
noncomputable def omittedList (v : Pos T k) (J : Finset (Pos T k))
    (ys : Pos T k → Fin (T.S.N k)) : Finset (Fin (T.S.N k)) :=
  Finset.univ.filter fun x =>
    x ∈ PT.envelope (D.G.patchOf v) ∧
      ∀ w ∈ D.externalEarly v \ J, Hits (T.S.E k) PT.tiling.c x (ys w)

/-- The Section 17 list event on a fixed row and external labels. -/
noncomputable def gateBad (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (ys : Pos T k → Fin (T.S.N k)) : Prop :=
  D.rowMass v σ ys < 1 / 2 ∨
    ∃ J : Finset (Pos T k), J ⊆ D.externalEarly v ∧
      (J.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 ∧
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
        (D.omittedList v J ys).card

/-- The low-row-mass clause of `S_v`. -/
noncomputable def gateMassFailure (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (ys : Pos T k → Fin (T.S.N k)) : Prop :=
  D.rowMass v σ ys < 1 / 2

/-- The omitted-support clause of `S_v`. -/
noncomputable def gateSupportFailure (v : Pos T k)
    (ys : Pos T k → Fin (T.S.N k)) : Prop :=
  ∃ J : Finset (Pos T k), J ⊆ D.externalEarly v ∧
    (J.card : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 4 ∧
    Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 8) <
      (D.omittedList v J ys).card

/-- The Section 17 event evaluated on actual fresh-cell readouts. -/
noncomputable def event (v : Pos T k) (s : Config D.F) : Prop :=
  IsEvenRole v ∧ D.gateBad v (D.prior s v) (D.label s)

/-- D17.L packaged as the shared resampling event, with its exact read scope.
The scope certificate follows because `S_v` reads only its own prior and the
external early labels. -/
noncomputable def asListEvent : ListEvent D.F := by
  classical
  refine ⟨D.event, D.scopeCells, ?_⟩
  intro v s₁ s₂ hscope
  have hown : s₁ (D.G.cellOf v) = s₂ (D.G.cellOf v) :=
    hscope _ (by simp [scopeCells])
  have hlabels : ∀ w ∈ D.externalEarly v, D.label s₁ w = D.label s₂ w := by
    intro w hw
    unfold label
    congr 1
    apply hscope
    unfold scopeCells
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hprior : D.prior s₁ v = D.prior s₂ v := by
    funext x
    simp [prior, hown]
  have hrow : ∀ x, D.row v (D.prior s₁ v) (D.label s₁) x =
      D.row v (D.prior s₂ v) (D.label s₂) x := by
    intro x
    unfold row
    rw [hprior]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [hlabels w hw]
  have hmass : D.rowMass v (D.prior s₁ v) (D.label s₁) =
      D.rowMass v (D.prior s₂ v) (D.label s₂) := by
    unfold rowMass
    apply Finset.sum_congr rfl
    intro x hx
    exact hrow x
  have hlists : ∀ J, D.omittedList v J (D.label s₁) =
      D.omittedList v J (D.label s₂) := by
    intro J
    apply Finset.ext
    intro x
    simp only [omittedList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hhits⟩
      refine ⟨hx, ?_⟩
      intro w hw
      rw [← hlabels w (Finset.mem_sdiff.mp hw).1]
      exact hhits w hw
    · rintro ⟨hx, hhits⟩
      refine ⟨hx, ?_⟩
      intro w hw
      rw [hlabels w (Finset.mem_sdiff.mp hw).1]
      exact hhits w hw
  have hgate : D.gateBad v (D.prior s₁ v) (D.label s₁) ↔
      D.gateBad v (D.prior s₂ v) (D.label s₂) := by
    unfold gateBad
    rw [hmass]
    constructor
    · rintro (hm | ⟨J, hJ, hcard, hsize⟩)
      · exact Or.inl hm
      · exact Or.inr ⟨J, hJ, hcard, by rw [← hlists J]; exact hsize⟩
    · rintro (hm | ⟨J, hJ, hcard, hsize⟩)
      · exact Or.inl hm
      · exact Or.inr ⟨J, hJ, hcard, by rw [hlists J]; exact hsize⟩
  constructor
  · rintro ⟨heven, hbad⟩
    exact ⟨heven, hgate.mp hbad⟩
  · rintro ⟨heven, hbad⟩
    exact ⟨heven, hgate.mpr hbad⟩

/-- Shape of a cleaned initial probability prior. The exponential cap belongs
only to cluster mode; in direct/bounded modes the prior is uniform on the
selected cleaned corner. The cardinality loss is the cleaning input. -/
def CleanInitialPrior (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) : Prop :=
  (∀ x, 0 ≤ σ x) ∧ (∑ x, σ x = 1) ∧
  ∃ a : PT.mesh.V, a ∈ PT.activeVertices ∧
    (∀ x, σ x ≠ 0 → x ∈ PT.mesh.corner a (D.G.patchOf v)) ∧
    (PT.tiling.mode.isCluster → ∀ x,
      (T.S.N k : ℝ) * σ x ≤ 2 ^ (PT.tiling.P (D.G.patchOf v)).h *
        Real.exp (-500 * PT.tiling.gain (D.G.patchOf v))) ∧
    (¬ PT.tiling.mode.isCluster →
      (1 - κ.a) * (PT.tiling.P (D.G.patchOf v)).M ≤
        (PT.mesh.corner a (D.G.patchOf v)).card ∧
      ∀ x, σ x = if x ∈ PT.mesh.corner a (D.G.patchOf v) then
        1 / ((PT.mesh.corner a (D.G.patchOf v)).card : ℝ) else 0)

/-- Priors are actual valid own-cell readouts, in addition to their cleaned
shape. Their solver/dummy-hit origin is supplied by `Needs.lean`. -/
def ValidInitialPrior (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) : Prop :=
  D.CleanInitialPrior v σ ∧
    ∃ P : D.F.Pool (D.G.cellOf v), ∃ s : D.F.State (D.G.cellOf v),
      D.F.typical (D.G.cellOf v) P ∧ D.stateValid (D.G.cellOf v) P s ∧
      ∀ x, σ x = D.F.prior (D.G.cellOf v) s v x

/-- Normalization already implies the convenience subprobability bound. -/
theorem validInitialPriorSubprob (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (hσ : D.ValidInitialPrior v σ) : ∑ x, σ x ≤ 1 := by
  exact le_of_eq hσ.1.2.1

/-- Nonemptiness of every patch support, projected from `PT.Valid`. -/
theorem patchXNonempty (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m) :
    (PT.tiling.P i).X.Nonempty :=
  let hTV : Tiling.Valid PT.tiling := ProfiledTiling.Valid.tiling_valid D.tiling_valid
  (Tiling.Valid.patch_nonempty hTV i).1

/-- Mass of a prior on the intersection of the pinned neighbourhoods. -/
noncomputable def pinnedPriorMass (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k)) : ℝ :=
  ∑ x, σ x * if x ∈ (PT.tiling.P (D.G.patchOf v)).X then
      ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)
    else 0

/-- Pinned-neighbourhood mass of the prior read from the own-cell state. -/
noncomputable def pinnedStatePriorMass (v : Pos T k)
    (s : D.F.State (D.G.cellOf v)) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)) : ℝ :=
  ∑ x, D.F.prior (D.G.cellOf v) s v x *
    ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)

/-- The maximum number of pinned incidences allowed by L17.1 and L17.2a. -/
noncomputable def pinBudget (κ : CConsts) : ℕ := ⌈20 * (κ.R : ℝ)⌉₊

/-- Independent external labels, with selected labels fixed in advance. -/
noncomputable def pinnedLabelLaw (v : Pos T k) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)) :
    FinLaw ({w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :=
  FinLaw.pi fun w =>
    if w.1 ∈ pins then FinLaw.dirac (fixed w.1)
    else lawAsFinLaw (PT.π (D.G.patchOf w.1))

/-- Extend labels on the external early neighbourhood to all cube positions.
Values away from the neighbourhood are never read. -/
noncomputable def labelsOfPinnedSample (v : Pos T k) (hN : 0 < T.S.N k)
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    Pos T k → Fin (T.S.N k) := fun w =>
  if hw : w ∈ D.externalEarly v then ys ⟨w, hw⟩ else ⟨0, hN⟩

/-- Independent fresh cell states at fixed pools. -/
noncomputable def freshConfigLaw (pools : ∀ C : D.G.Cell, D.F.Pool C) :
    FinLaw (Config D.F) :=
  FinLaw.pi fun C => D.F.fresh C (pools C)

/-- Fresh-cell probability of the list event at fixed pools. -/
noncomputable def freshEventProbability (v : Pos T k)
    (pools : ∀ C : D.G.Cell, D.F.Pool C) : ℝ :=
  (D.freshConfigLaw pools).pr (D.event v)

/-- All cells read by the list event have individually typical pools. -/
def LocalPoolsTypical (v : Pos T k) (pools : ∀ C : D.G.Cell, D.F.Pool C) : Prop :=
  ∀ C ∈ D.scopeCells v, D.F.typical C (pools C)

/-- Slot-to-bin pin in a global permutation pool assignment. -/
structure PoolPin where
  cell : D.G.Cell
  slot : Fin (D.G.nslot cell)
  bin : Bin PT.tiling (D.G.cellPatch cell)

/-- Global pool assignments supported by the permutation pool law. -/
abbrev PoolAssignment := ∀ C : D.G.Cell, CellPool D.G C

/-- The event that a global pool assignment satisfies one prescribed slot pin. -/
noncomputable def poolPinSet (pin : D.PoolPin) : Finset D.PoolAssignment :=
  Finset.univ.filter fun pools => pools pin.cell pin.slot = pin.bin

/-- Permutation pools conditioned on one positive-probability slot-to-bin pin. -/
noncomputable def pinnedPoolLaw (hpools : (permPools D.G).Nonempty)
    (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
      (permPoolLaw D.G hpools).w pools) : FinLaw D.PoolAssignment :=
  FinLaw.cond (permPoolLaw D.G hpools) (D.poolPinSet pin) hpin

/-- A pool law from the two experiments used in Section 17: the unconditioned
permutation pools or those same pools conditioned on one global slot pin. -/
def IsPermOrPinnedPoolLaw (hpools : (permPools D.G).Nonempty)
    (μ : FinLaw (PoolAssignment D)) : Prop :=
  μ = permPoolLaw D.G hpools ∨
    ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
      (permPoolLaw D.G hpools).w pools),
      μ = D.pinnedPoolLaw hpools pin hpin

/-- The compatibility event `A_v` from the proof of L17.2a. For every small
set of incidences and every permitted choice of one label per incidence, the
own-cell prior almost always has mass at least `.9 · 2^{-s}` on their common
neighbourhood. -/
noncomputable def compatiblePool (v : Pos T k) (pools : PoolAssignment D) : Prop :=
  ∀ pins : Finset (Pos T k), pins ⊆ D.externalEarly v →
    pins.card ≤ pinBudget κ →
    ∀ fixed : Pos T k → Fin (T.S.N k),
      (∀ w ∈ pins, fixed w ∈ D.permittedLabels (D.G.cellOf w) (pools (D.G.cellOf w)) w) →
      (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr
        (fun s => D.pinnedStatePriorMass v s pins fixed <
            (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ))) ≤
        Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))

/-- The auxiliary compatibility failure on a pool that is otherwise locally
typical. -/
noncomputable def compatibilityFailure (v : Pos T k) (pools : PoolAssignment D) : Prop :=
  D.LocalPoolsTypical v pools ∧ ¬ D.compatiblePool v pools

/-- The pool success event in L17.2, eq:source-23. -/
noncomputable def poolSuccess (v : Pos T k) (pools : PoolAssignment D) : Prop :=
  D.LocalPoolsTypical v pools ∧
    D.freshEventProbability v pools ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))

/-- Pool event excluded by the uniform pool estimate. -/
noncomputable def poolException (v : Pos T k) (pools : PoolAssignment D) : Prop :=
  ¬ D.poolSuccess v pools

/-- Binary word of the internal top coordinates of a patch role. -/
def internalBits (i : Fin PT.tiling.m) (hle : (PT.tiling.P i).h ≤ T.S.n k)
    (v : Pos T k) : Fin (PT.tiling.P i).h → ZMod 2 := fun j =>
  if v ⟨T.S.n k - (PT.tiling.P i).h + j.val, by omega⟩ then 1 else 0

/-- A binary linear palette code on the internal words of one patch. -/
structure PaletteCode (i : Fin PT.tiling.m)
    (hle : (PT.tiling.P i).h ≤ T.S.n k) where
  dimension : ℕ
  map : (Fin (PT.tiling.P i).h → ZMod 2) →ₗ[ZMod 2]
    (Fin dimension → ZMod 2)

namespace PaletteCode

variable {D} {i : Fin PT.tiling.m}
variable {hle : (PT.tiling.P i).h ≤ T.S.n k}

/-- Colour of a full cube role induced by the internal linear map. -/
def roleColour (ψ : PaletteCode i hle) (v : Pos T k) : Fin ψ.dimension → ZMod 2 :=
    ψ.map (internalBits i hle v)

/-- Number of colours in a binary vector palette. -/
def chi (ψ : PaletteCode i hle) : ℕ := 2 ^ ψ.dimension

/-- Labels assigned to the palette of one role. -/
noncomputable def palette (ψ : PaletteCode i hle)
    (colours : Fin (T.S.N k) → (Fin ψ.dimension → ZMod 2))
    (v : Pos T k) : Finset (Fin (T.S.N k)) :=
  Finset.univ.filter fun x =>
    x ∈ (PT.tiling.P i).X ∧ colours x = ψ.roleColour v

end PaletteCode

/-- Probability law of the fresh states on a deterministic target set. -/
noncomputable def freshTargetLaw (targets : Finset D.G.Cell)
    (pools : ∀ C : D.G.Cell, D.F.Pool C) :
    FinLaw (∀ C : {C : D.G.Cell // C ∈ targets}, D.F.State C) :=
  FinLaw.pi fun C => D.F.fresh C.1 (pools C.1)

/-- Restriction of a full cell configuration to deterministic target cells. -/
def targetProjection (targets : Finset D.G.Cell) (s : Config D.F) :
    ∀ C : {C : D.G.Cell // C ∈ targets}, D.F.State C := fun C => s C.1

/-- A palette assignment is a label colouring by the linear-code colour space. -/
abbrev PaletteAssignment {i : Fin PT.tiling.m}
    {hle : (PT.tiling.P i).h ≤ T.S.n k} (ψ : PaletteCode i hle) :=
  Fin (T.S.N k) → (Fin ψ.dimension → ZMod 2)

end ListGateContext

set_option linter.style.haveILetI false
/-- Union bound for two events under an explicit finite law. -/
theorem FinLaw.pr_or_le {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  letI : DecidablePred B := fun ω => Classical.propDecidable (B ω)
  letI : DecidablePred (fun ω => A ω ∨ B ω) :=
    fun ω => Classical.propDecidable (A ω ∨ B ω)
  unfold FinLaw.pr
  have hpoint : ∀ ω, (if A ω ∨ B ω then P.w ω else 0) ≤
      (if A ω then P.w ω else 0) + (if B ω then P.w ω else 0) := by
    intro ω
    by_cases hA : A ω <;> by_cases hB : B ω <;>
      simp [hA, hB, P.nonneg ω]
  calc
    Finset.univ.sum (fun ω => if A ω ∨ B ω then P.w ω else 0) ≤
        Finset.univ.sum (fun ω => (if A ω then P.w ω else 0) + (if B ω then P.w ω else 0)) :=
          Finset.sum_le_sum fun ω _ => hpoint ω
    _ = Finset.univ.sum (fun ω => if A ω then P.w ω else 0) +
          Finset.univ.sum (fun ω => if B ω then P.w ω else 0) := by
      rw [Finset.sum_add_distrib]
set_option linter.style.haveILetI true

end HypercubeRamsey
