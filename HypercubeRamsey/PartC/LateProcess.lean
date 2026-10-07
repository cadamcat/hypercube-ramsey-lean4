import HypercubeRamsey.PartC.Resampling

/-!
# Section 18 late-process encoding (D18.E, G26)

The encoding makes histories dependent products of the initial cell state and
the row outputs already processed. Every class has both its product reference
transition and its actual injective sampler. The full experiment is assembled
with dependent finite-law binds, terminal conditioning, and the final pair draw.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Fixed class partition and row-output vocabulary for the late process. -/
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
  Mask : Pos T k → Type
  [maskFinite : ∀ b, Fintype (Mask b)]
  maskAllowed : ∀ b, Mask b → Prop
  [maskAllowedDec : ∀ b, DecidablePred (maskAllowed b)]
  sketchRows : Pos T k → ℕ
  sketchLength : Pos T k → ℕ
  latePool : Pos T k → Finset (Fin (T.S.N k))

namespace LateProcessBase

instance instMaskFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) : Fintype (B.Mask b) := B.maskFinite b

instance instMaskAllowedDecidable {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) : DecidablePred (B.maskAllowed b) :=
  B.maskAllowedDec b

/-- Allowed mask profiles at a row. -/
abbrev AllowedMask {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) :=
  {m : B.Mask b // B.maskAllowed b m}

noncomputable instance instAllowedMaskFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) : Fintype (B.AllowedMask b) :=
  Fintype.subtype (Finset.univ.filter fun m => B.maskAllowed b m) (by intro m; simp)

noncomputable instance instLatePoolLabelFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) :
    Fintype {y : Fin (T.S.N k) // y ∈ B.latePool b} :=
  Fintype.subtype (B.latePool b) (by intro y; rfl)

/-- One late row output: allowed mask, all finite sketches, and a label in the late pool. -/
abbrev RowOut {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) :=
  B.AllowedMask b ×
    (Fin (B.sketchRows b) → Fin (B.sketchLength b) → Fin (T.S.N k)) ×
    {y : Fin (T.S.N k) // y ∈ B.latePool b}

noncomputable instance instRowOutFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (b : Pos T k) : Fintype (B.RowOut b) := inferInstance

/-- Mask component of a late row output. -/
def rowMask {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) {b : Pos T k} (o : B.RowOut b) : B.AllowedMask b := o.1

/-- Possible outputs of one late class. -/
abbrev ClassRows {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (j : Fin G.r) :=
  ∀ b : {x : Pos T k // x ∈ B.classes j}, B.RowOut b.1

noncomputable instance instClassRoleFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (j : Fin G.r) :
    Fintype {x : Pos T k // x ∈ B.classes j} :=
  Fintype.subtype (B.classes j) (by intro x; rfl)

/-- Rows already processed at stage `j`. -/
abbrev ProcessedRole {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (j : Fin (G.r + 1)) :=
  {b : Pos T k // b ∈ B.processed j}

noncomputable instance instProcessedRoleFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (j : Fin (G.r + 1)) : Fintype (B.ProcessedRole j) :=
  Fintype.subtype (B.processed j) (by intro b; rfl)

/-- History equals the initial cell configuration and the dependent product of processed row outputs. -/
abbrev History {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (j : Fin (G.r + 1)) :=
  Config F × (∀ b : B.ProcessedRole j, B.RowOut b.1)

/-- Embed an initial configuration into the empty processed history. -/
noncomputable def initialHistory {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (B : LateProcessBase F) (s : Config F) : B.History 0 := by
  classical
  refine (s, ?_)
  intro b
  have hfalse : False := by
    simpa [B.processed_zero] using b.2
  exact hfalse.elim

end LateProcessBase

/-- Complete finite-law interface for the late exposure process. -/
structure LateEncoding {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  base : LateProcessBase F
  /-- Independent fixed-in-advance mask profiles. -/
  maskProfile : ∀ b : Pos T k, FinLaw (base.AllowedMask b)
  Pools : Type
  [poolFinite : Fintype Pools]
  Tape : Pools → Type
  [tapeFinite : ∀ p, Fintype (Tape p)]
  poolLaw : FinLaw Pools
  tapeLaw : ∀ p, FinLaw (Tape p)
  /-- Initial Section 17 process law at fixed pools and tapes. -/
  initialProcess : ∀ p, Tape p → FinLaw (Config F)
  /-- Reference kernels, defined on every history including invalid ones. -/
  refK : ∀ j : Fin G.r,
    ∀ b : {x : Pos T k // x ∈ base.classes j},
      base.History j.castSucc → FinLaw (base.RowOut b.1)
  refK_mask_marginal : ∀ (j : Fin G.r) (b : {x : Pos T k // x ∈ base.classes j})
      (h : base.History j.castSucc),
    FinLaw.map (refK j b h) (fun out : base.RowOut b.1 => out.1) = maskProfile b.1
  /-- Actual conditional injective sampler for each late class. -/
  act : ∀ j : Fin G.r, base.History j.castSucc → FinLaw (base.ClassRows j)
  act_injective : ∀ (j : Fin G.r) (h : base.History j.castSucc) (out : base.ClassRows j),
    (act j h).w out ≠ 0 →
      Function.Injective (fun b : {x : Pos T k // x ∈ base.classes j} => (out b).2.2.1)
  lateError : ℝ
  lateError_nonneg : 0 ≤ lateError
  comparisonScope : ∀ j : Fin G.r, Set ({x : Pos T k // x ∈ base.classes j})
  /-- L3.10 upper comparison for the actual class sampler on its stated scope. -/
  act_ref_upper : ∀ (j : Fin G.r) (h : base.History j.castSucc)
      (Ψ : base.ClassRows j → ℝ),
    (∀ out, 0 ≤ Ψ out) →
    DependsOn Ψ (comparisonScope j) →
    (act j h).E Ψ ≤ (1 + lateError) *
      (FinLaw.pi (fun b => refK j b h)).E Ψ
  /-- Extend a history with one class's row outputs. -/
  extend : ∀ j : Fin G.r, base.History j.castSucc → base.ClassRows j → base.History j.succ
  extend_old : ∀ (j : Fin G.r) (h : base.History j.castSucc)
      (out : base.ClassRows j) (b : base.ProcessedRole j.castSucc),
    (extend j h out).2 ⟨b.1, by
      rw [← base.processed_step j]
      exact Finset.mem_union.mpr (Or.inl b.2)⟩ = h.2 b
  extend_new : ∀ (j : Fin G.r) (h : base.History j.castSucc)
      (out : base.ClassRows j) (b : {x : Pos T k // x ∈ base.classes j}),
    (extend j h out).2 ⟨b.1, by
      rw [← base.processed_step j]
      exact Finset.mem_union.mpr (Or.inr b.2)⟩ = out b
  /-- Full actual class-by-class run, constrained by the bind recursion below. -/
  run : ∀ j : Fin (G.r + 1), ∀ p, Tape p → FinLaw (base.History j)
  run_zero : ∀ p t,
    run 0 p t = FinLaw.map (initialProcess p t) base.initialHistory
  run_step : ∀ j : Fin G.r, ∀ p t,
    run j.succ p t =
      FinLaw.map (FinLaw.bind (run j.castSucc p t) (act j))
        (fun ht => extend j ht.1 ht.2)
  /-- Terminal-avoidance event; it is a finite set of full class histories. -/
  terminal : ∀ p, Tape p → Finset (base.History (Fin.last G.r))
  terminal_positive : ∀ p t,
    0 < ∑ h ∈ terminal p t, (run (Fin.last G.r) p t).w h
  /-- Bad events and alarms are finite sets of outputs at each fixed class. -/
  badOutputs : ∀ j : Fin G.r, Finset (base.ClassRows j)
  alarms : ∀ j : Fin G.r, Finset (base.ClassRows j)
  PairDraw : Type
  [pairFinite : Fintype PairDraw]
  pairSampler : base.History (Fin.last G.r) → FinLaw PairDraw

instance instPoolsFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) : Fintype E.Pools := E.poolFinite

instance instTapeFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) : ∀ p, Fintype (E.Tape p) := E.tapeFinite

instance instPairDrawFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) : Fintype E.PairDraw := E.pairFinite

namespace LateEncoding

/-- Independent product reference transition for one class. -/
noncomputable def referenceTransition {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) (j : Fin G.r) (h : E.base.History j.castSucc) :
    FinLaw (E.base.ClassRows j) :=
  FinLaw.pi (fun b => E.refK j b h)

/-- Pool and tape experiment, sampled by dependent finite-law bind. -/
noncomputable def poolTapeLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) : FinLaw (Sigma E.Tape) :=
  FinLaw.bindD E.poolLaw E.tapeLaw

/-- Run the classes and condition the final history on terminal avoidance. -/
noncomputable def terminalRun {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) (pt : Sigma E.Tape) :
    FinLaw (E.base.History (Fin.last G.r)) :=
  FinLaw.cond (E.run (Fin.last G.r) pt.1 pt.2) (E.terminal pt.1 pt.2)
    (E.terminal_positive pt.1 pt.2)

/-- Pool/tape choice paired with the terminal-conditioned class history. -/
noncomputable def terminalExperiment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) :
    FinLaw (Sigma E.Tape × E.base.History (Fin.last G.r)) :=
  FinLaw.map (FinLaw.bindD E.poolTapeLaw E.terminalRun) (fun x => (x.1, x.2))

/-- Full late experiment after terminal-conditioned initial sampling and pair draws. -/
noncomputable def experiment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : LateEncoding F) :
    FinLaw ((Sigma E.Tape × E.base.History (Fin.last G.r)) × E.PairDraw) :=
  FinLaw.bind (E.terminalExperiment)
    (fun x => E.pairSampler x.2)

end LateEncoding

end HypercubeRamsey
