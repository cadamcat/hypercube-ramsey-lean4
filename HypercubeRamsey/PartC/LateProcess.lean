import HypercubeRamsey.PartC.Resampling

/-!
# Section 18 late-process encoding (D18.E, G26)

The three laws of sections/18 lines 11–38 in their order:

1. *Initial process* (L1): pools (permutation slots; iid slots in the annealed baseline) and
   independent cell tapes, then the deterministic finite resampling of D17.R, giving `S_fin`.
   Terminal avoidance conditions this pair (pools, tapes), before any late draw
   (sections/18 lines 659–676).
2. *Reference late transitions* (L2): from an entering history, a product over the rows of the
   current class of reference row kernels (mask, sketches, label).
3. *Actual late assignment* (L3): a conditional injective sampler per class at the entering
   history, with upper comparison at factor two to the product reference law on every small set
   of rows, required only on the histories where the run proceeds (sections/18 lines 827–861).

Histories are dependent products of the initial configuration and the row outputs already
processed. Class runs, reference runs from any configuration (needed for `p_F(S_fin)`, the
transfer experiment and the baseline), the terminal-conditioned experiment and the final pair draw
are definitions; mask profiles, reference kernels, the actual samplers, bad events, alarms and the
terminal event are inputs, supplied by D18.L, D18.T, D18.G and P18.4.

Classes are processed in increasing index; the class with index `j` is processed with `r − j`
classes remaining (the paper numbers the classes `r, …, 1` in processing order).
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Sketch length `m = ⌈n^{.25}⌉` (sections/18 line 97). -/
noncomputable def sketchLength (T : Stage) (k : ℕ) : ℕ := ⌈(T.S.n k : ℝ) ^ (0.25 : ℝ)⌉₊

/-- Fixed class partition, processing schedule and late pools (D18.L). -/
structure LateProcessBase {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  classes : Fin G.r → Finset (Pos T k)
  class_disjoint : ∀ i j, i ≠ j → Disjoint (classes i) (classes j)
  class_of_spec : ∀ b j, b ∈ classes j ↔ G.classOf b = some j
  processed : Fin (G.r + 1) → Finset (Pos T k)
  processed_zero : processed 0 = ∅
  processed_step : ∀ j : Fin G.r,
    processed j.castSucc ∪ classes j = processed j.succ
  class_fresh : ∀ j : Fin G.r, Disjoint (classes j) (processed j.castSucc)
  processed_last : processed (Fin.last G.r) =
    Finset.univ.filter fun b => ∃ j : Fin G.r, G.classOf b = some j
  /-- Late pool of each class: disjoint subsets of the reserved second-side labels, each of size
  `M_late = ⌊⌊N/3⌋/r⌋`. -/
  latePool : Fin G.r → Finset (Fin (T.S.N k))
  latePool_reserve : ∀ j, latePool j ⊆ PT.tiling.reserveY
  latePool_disjoint : ∀ j j', j ≠ j' → Disjoint (latePool j) (latePool j')
  latePool_card : ∀ j, (latePool j).card = T.S.N k / 3 / G.r

namespace LateProcessBase

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
  {F : FreshCell G}

/-- The late pool read by a row (empty for a position that is not a late role). -/
noncomputable def latePoolOf (B : LateProcessBase F) (b : Pos T k) : Finset (Fin (T.S.N k)) :=
  match G.classOf b with
  | some j => B.latePool j
  | none => ∅

/-- Allowed masks at a row: subsets of its late pool of at least half the pool's size. -/
abbrev AllowedMask (B : LateProcessBase F) (b : Pos T k) :=
  {S : Finset (Fin (T.S.N k)) // S ⊆ B.latePoolOf b ∧ (B.latePoolOf b).card ≤ 2 * S.card}

noncomputable instance instAllowedMaskFintype (B : LateProcessBase F) (b : Pos T k) :
    Fintype (B.AllowedMask b) :=
  Fintype.subtype (Finset.univ.filter fun S : Finset (Fin (T.S.N k)) =>
    S ⊆ B.latePoolOf b ∧ (B.latePoolOf b).card ≤ 2 * S.card) (by intro S; simp)

noncomputable instance instLatePoolLabelFintype (B : LateProcessBase F) (b : Pos T k) :
    Fintype {y : Fin (T.S.N k) // y ∈ B.latePoolOf b} :=
  Fintype.subtype (B.latePoolOf b) (by intro y; rfl)

/-- One late row output: the mask, one sketch of length `m` for each of the `n` even neighbours
`flipPos b k'` (first-side labels), and the label in the late pool. -/
abbrev RowOut (B : LateProcessBase F) (b : Pos T k) :=
  B.AllowedMask b ×
    (Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) ×
    {y : Fin (T.S.N k) // y ∈ B.latePoolOf b}

noncomputable instance instRowOutFintype (B : LateProcessBase F) (b : Pos T k) :
    Fintype (B.RowOut b) := inferInstance

/-- Mask component of a late row output. -/
def rowMask (B : LateProcessBase F) {b : Pos T k} (o : B.RowOut b) : B.AllowedMask b := o.1

/-- Label component of a late row output. -/
def rowLabel (B : LateProcessBase F) {b : Pos T k} (o : B.RowOut b) : Fin (T.S.N k) := o.2.2.1

noncomputable instance instClassRoleFintype (B : LateProcessBase F) (j : Fin G.r) :
    Fintype {x : Pos T k // x ∈ B.classes j} :=
  Fintype.subtype (B.classes j) (by intro x; rfl)

/-- Possible outputs of one late class. -/
abbrev ClassRows (B : LateProcessBase F) (j : Fin G.r) :=
  ∀ b : {x : Pos T k // x ∈ B.classes j}, B.RowOut b.1

/-- Rows already processed at stage `j`. -/
abbrev ProcessedRole (B : LateProcessBase F) (j : Fin (G.r + 1)) :=
  {b : Pos T k // b ∈ B.processed j}

noncomputable instance instProcessedRoleFintype (B : LateProcessBase F) (j : Fin (G.r + 1)) :
    Fintype (B.ProcessedRole j) :=
  Fintype.subtype (B.processed j) (by intro b; rfl)

/-- History: the initial cell configuration and the dependent product of processed row outputs. -/
abbrev History (B : LateProcessBase F) (j : Fin (G.r + 1)) :=
  Config F × (∀ b : B.ProcessedRole j, B.RowOut b.1)

/-- Embed an initial configuration into the empty processed history. -/
noncomputable def initialHistory (B : LateProcessBase F) (s : Config F) : B.History 0 := by
  refine (s, ?_)
  intro b
  have hfalse : False := by
    simpa [B.processed_zero] using b.2
  exact hfalse.elim

/-- Extend a history by one class's row outputs. -/
noncomputable def extend (B : LateProcessBase F) (j : Fin G.r) (h : B.History j.castSucc)
    (out : B.ClassRows j) : B.History j.succ :=
  (h.1, fun b =>
    if hb : b.1 ∈ B.processed j.castSucc then h.2 ⟨b.1, hb⟩
    else
      have hmem : b.1 ∈ B.processed j.castSucc ∪ B.classes j := by
        rw [B.processed_step j]
        exact b.2
      out ⟨b.1, (Finset.mem_union.mp hmem).resolve_left hb⟩)

/-- Class-by-class run from an initial configuration, with a given per-class transition. -/
noncomputable def runFrom (B : LateProcessBase F)
    (step : ∀ j : Fin G.r, B.History j.castSucc → FinLaw (B.ClassRows j)) (s : Config F) :
    ∀ m (hm : m ≤ G.r), FinLaw (B.History ⟨m, Nat.lt_succ_of_le hm⟩)
  | 0, _ => FinLaw.dirac (B.initialHistory s)
  | m + 1, hm =>
      FinLaw.map (FinLaw.bind (B.runFrom step s m (Nat.le_of_succ_le hm)) (step ⟨m, hm⟩))
        (fun x => B.extend ⟨m, hm⟩ x.1 x.2)

/-- The full run through all late classes. -/
noncomputable def runFull (B : LateProcessBase F)
    (step : ∀ j : Fin G.r, B.History j.castSucc → FinLaw (B.ClassRows j)) (s : Config F) :
    FinLaw (B.History (Fin.last G.r)) :=
  B.runFrom step s G.r le_rfl

end LateProcessBase

/-- Mask profiles (fixed in advance, independent across rows) and reference row kernels (D18.T),
defined on every history including invalid ones. -/
structure LateKernels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G} (B : LateProcessBase F) where
  maskProfile : ∀ b : Pos T k, FinLaw (B.AllowedMask b)
  refK : ∀ j : Fin G.r,
    ∀ b : {x : Pos T k // x ∈ B.classes j},
      B.History j.castSucc → FinLaw (B.RowOut b.1)
  refK_mask_marginal : ∀ (j : Fin G.r) (b : {x : Pos T k // x ∈ B.classes j})
      (h : B.History j.castSucc),
    FinLaw.map (refK j b h) (fun out : B.RowOut b.1 => out.1) = maskProfile b.1

namespace LateKernels

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
  {F : FreshCell G} {B : LateProcessBase F}

/-- Independent product reference transition (L2) for one class at a fixed entering history. -/
noncomputable def referenceTransition (K : LateKernels B) (j : Fin G.r)
    (h : B.History j.castSucc) : FinLaw (B.ClassRows j) :=
  FinLaw.pi (fun b => K.refK j b h)

/-- Unconstrained reference late process from an initial configuration (gives
`p_F(S) = Pr_ref(F ∣ S)` and the transfer experiment of Section 18.2). -/
noncomputable def refRun (K : LateKernels B) (s : Config F) :
    FinLaw (B.History (Fin.last G.r)) :=
  B.runFull K.referenceTransition s

end LateKernels

/-- Data of the late exposure process: class schedule, kernels, initial list events `S_v` with their
scopes (D17.L), the resampling schedule (`T_s = ⌈log² n⌉` rounds, a fixed event order), and the fact
that all slots fit injectively into their patches' bins (so the pool laws exist). -/
structure LateEncoding {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  base : LateProcessBase F
  kernels : LateKernels base
  events : ListEvent F
  Ts : ℕ
  Ts_eq : Ts = ⌈Real.log (T.S.n k) ^ 2⌉₊
  order : Pos T k → ℕ
  pools_nonempty : (permPools G).Nonempty

namespace LateEncoding

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {G : LowGeom PT}
  {F : FreshCell G}

/-- Inputs of the initial process: pools and tapes. -/
abbrev InitInput (E : LateEncoding F) := (∀ C, F.Pool C) × Tapes F E.Ts

/-- `S_fin`: the configuration after the `Ts` resampling rounds at the given pools and tapes. -/
noncomputable def initialState (E : LateEncoding F) (x : E.InitInput) : Config F :=
  E.events.resample E.Ts E.order Finset.univ x.1 x.2.extend

/-- Pools from a given pool law, independent tapes. -/
noncomputable def initialLaw (E : LateEncoding F) (pools : FinLaw (∀ C, F.Pool C)) :
    FinLaw E.InitInput :=
  FinLaw.bind pools (fun _ => tapeLaw F E.Ts)

/-- Permutation pool law (L16.1c). -/
noncomputable def poolLaw (E : LateEncoding F) : FinLaw (∀ C, F.Pool C) :=
  permPoolLaw G E.pools_nonempty

/-- iid slot law of the annealed baseline. -/
noncomputable def iidLaw (E : LateEncoding F) : FinLaw (∀ C, F.Pool C) :=
  iidPoolLaw G E.pools_nonempty

/-- Unconditioned initial sampling on permutation pools. -/
noncomputable def permLaw (E : LateEncoding F) : FinLaw E.InitInput := E.initialLaw E.poolLaw

/-- Terminal-conditioned initial sampling `𝔼_term`: the initial inputs conditioned on the terminal
avoidance event (requirements T1–T3, D18.G), whose positivity is P18.3(ii). -/
noncomputable def terminalLaw (E : LateEncoding F) (terminal : Finset E.InitInput)
    (hpos : 0 < ∑ x ∈ terminal, E.permLaw.w x) : FinLaw E.InitInput :=
  FinLaw.cond E.permLaw terminal hpos

/-- Annealed baseline: iid slots, the full initial process, unconstrained reference late
transitions (used to choose the mask profiles). -/
noncomputable def baseline (E : LateEncoding F) :
    FinLaw (E.InitInput × E.base.History (Fin.last G.r)) :=
  FinLaw.bind (E.initialLaw E.iidLaw) (fun x => E.kernels.refRun (E.initialState x))

/-- Specification of actual class samplers (L3), required at entering histories where the run
proceeds: distinct labels, avoidance of the current bad events and future alarms, and upper
comparison at factor two with the product reference law for every nonnegative test of at most
`exp((log n)³)` rows (this covers the `n^{O(r)}` queried rows, side data included). -/
def SamplerSpec (E : LateEncoding F)
    (act : ∀ j : Fin G.r, E.base.History j.castSucc → FinLaw (E.base.ClassRows j))
    (enter : ∀ j : Fin G.r, E.base.History j.castSucc → Prop)
    (bad alarm : ∀ j : Fin G.r, E.base.History j.castSucc → Finset (E.base.ClassRows j)) :
    Prop :=
  ∀ j h, enter j h →
    (∀ out, (act j h).w out ≠ 0 →
      Function.Injective (fun b => E.base.rowLabel (out b)) ∧ out ∉ bad j h ∧ out ∉ alarm j h) ∧
    (∀ S : Finset {x : Pos T k // x ∈ E.base.classes j},
      (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      ∀ Ψ : E.base.ClassRows j → ℝ, (∀ out, 0 ≤ Ψ out) → DependsOn Ψ (S : Set _) →
        (act j h).E Ψ ≤ 2 * (E.kernels.referenceTransition j h).E Ψ)

/-- Full late experiment: terminal-conditioned initial sampling, the actual class-by-class run
from `S_fin`, then the final pair draw. -/
noncomputable def experiment (E : LateEncoding F) (terminal : Finset E.InitInput)
    (hpos : 0 < ∑ x ∈ terminal, E.permLaw.w x)
    (act : ∀ j : Fin G.r, E.base.History j.castSucc → FinLaw (E.base.ClassRows j))
    {Pair : Type} [Fintype Pair] (pairSampler : E.base.History (Fin.last G.r) → FinLaw Pair) :
    FinLaw ((E.InitInput × E.base.History (Fin.last G.r)) × Pair) :=
  FinLaw.bind
    (FinLaw.bind (E.terminalLaw terminal hpos) (fun x => E.base.runFull act (E.initialState x)))
    (fun z => pairSampler z.2)

end LateEncoding

end HypercubeRamsey
