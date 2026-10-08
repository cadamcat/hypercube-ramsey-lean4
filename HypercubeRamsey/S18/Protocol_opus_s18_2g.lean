import HypercubeRamsey.S18.Nodes_sol_s18_1c
import HypercubeRamsey.S18.Run_sol_s18_n4
import HypercubeRamsey.S18.Protocol_opus_s18_2g_sol

/-!
# Lane opus-s18-2g: the class-ordered transfer protocol of L18.2g (TeX 18:420–453)

Design (see `runs/lanes/opus-s18-2g/NOTES.md`):

* `Seed` holds, for every late row `b` of every class `j`, an independent mask draw, one sketch
  table per coordinate indexed by `SketchIndex = Config × ProcessedLabels` and one label table
  indexed by the *visible* side data (mask, sketches with erased coordinates blanked).
* `simHistory s σ` is the full (mathematical) simulation of `deletedExperiment`'s run from
  `X.state s`; predecessor sketch tables are evaluated at `blockConfig` (affected sites) or
  `X.fixed` (unaffected sites) and at predecessor-restricted labels, so the protocol evaluates the
  *same* table entries (no index switching; sol-s18-1c NOTES).
* The protocol asks the affected calls in class order (`plan`), answers with `encodeSketch` in the
  fixed withheld list, recomputes predecessor labels from the seed and decoded replies
  (`protoLabels`), and outputs the tested prefix law at the failure row (no abort branch is needed:
  every `prefixLabelLaw` is broad).

Open obligations are the `sorry` lemmas below; each docstring gives TeX lines and size.
-/

namespace HypercubeRamsey.S18.Lane_opus_s18_2g
open Classical Filter
open scoped BigOperators
open HypercubeRamsey.Lane_sol_s18_1c

set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

section Defs
variable (D : LateData hPT) (X : CriticalTransferData D)

/-- A `Law` as a `FinLaw` (defeq to sol-s18-1c's private `asFinLaw`). -/
noncomputable def lawFin {N : ℕ} (P : Law N) : FinLaw (Fin N) := ⟨P.w, P.nonneg, P.sum_eq_one⟩

/-- Sketch site of a call (defeq to sol-s18-1c's private `callSite`). -/
noncomputable def site (c : SketchCall D X) : Pos T k := flipPos c.2.1.1 c.2.2

/-- Critical external inputs (defeq to sol-s18-1c's private `criticalExternalInputs`). -/
noncomputable def critInputs (w : Pos T k) : Finset (Fin (T.S.n k)) :=
  (D.externalEarly w).filter fun j => D.geom.cellOf (flipPos w j) ∈ X.criticalCells

/-- The fixed withheld list `L_w` of TeX 18:383–392, read from noncritical data only. -/
noncomputable def fixedList (c : SketchCall D X) : Finset (Fin (T.S.N k)) :=
  D.withheldList (site D X c) X.fixed (critInputs D X (site D X c))

/-- The responding block of a site (TransferGeometry.one_block when it applies). -/
noncomputable def blockOfSite (w : Pos T k) : Fin (T.S.n k) :=
  if h : ∃ a, D.directCells w ∩ X.criticalCells ⊆ X.blockCells a then Classical.choose h
  else X.failure.2.2.2.2

noncomputable def blockOf (c : SketchCall D X) : Fin (T.S.n k) := blockOfSite D X (site D X c)

abbrev Sketch := Fin (sketchLength T k) → Fin (T.S.N k)
abbrev SketchArray := Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)
abbrev SketchIndex (j : Fin D.geom.r) := Config D.fresh × ProcessedLabels D j.castSucc
abbrev LabelIndex (b : Pos T k) := D.encoding.base.AllowedMask b × SketchArray (T := T) (k := k)
abbrev RowSeed (j : Fin D.geom.r) (b : Pos T k) :=
  D.encoding.base.AllowedMask b ×
    ((Fin (T.S.n k) → SketchIndex D j → Sketch (T := T) (k := k)) ×
      (LabelIndex D b → {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}))
noncomputable instance sketchTables_fintype (j : Fin D.geom.r) :
    Fintype (Fin (T.S.n k) → SketchIndex D j → Sketch (T := T) (k := k)) := inferInstance
noncomputable instance labelTable_fintype (b : Pos T k) :
    Fintype (LabelIndex D b → {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) := inferInstance
noncomputable instance rowSeed_fintype (j : Fin D.geom.r) (b : Pos T k) : Fintype (RowSeed D j b) :=
  instFintypeProd _ _
abbrev ClassSeed (j : Fin D.geom.r) := ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j}, RowSeed D j b.1
abbrev Seed := ∀ j : Fin D.geom.r, ClassSeed D j
noncomputable instance classSeed_fintype (j : Fin D.geom.r) : Fintype (ClassSeed D j) := inferInstance
noncomputable instance seed_fintype : Fintype (Seed D) := inferInstance

theorem processed_pool_nonempty (j : Fin (D.geom.r + 1)) (b : D.encoding.base.ProcessedRole j) :
    Nonempty {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} := by
  have hmem : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r) :=
    D.processed_mono j (Fin.last D.geom.r) (Nat.lt_succ_iff.mp j.isLt) b.2
  rw [D.encoding.base.processed_last] at hmem
  obtain ⟨j', hj'⟩ := (Finset.mem_filter.mp hmem).2
  have hpool : D.encoding.base.latePoolOf b.1 = D.encoding.base.latePool j' := by
    simp [LateProcessBase.latePoolOf, hj']
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (D.late_pool_pos j')
  exact ⟨⟨y, hpool ▸ hy⟩⟩

theorem class_pool_nonempty (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j}) :
    Nonempty {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} := by
  have hj : D.geom.classOf b.1 = some j := (D.encoding.base.class_of_spec b.1 j).mp b.2
  have hpool : D.encoding.base.latePoolOf b.1 = D.encoding.base.latePool j := by
    simp [LateProcessBase.latePoolOf, hj]
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (D.late_pool_pos j)
  exact ⟨⟨y, hpool ▸ hy⟩⟩

noncomputable def defaultLabel (j : Fin (D.geom.r + 1)) (b : D.encoding.base.ProcessedRole j) :
    {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} :=
  Classical.choice (processed_pool_nonempty D j b)

noncomputable def rowDefaultLabel (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j}) :
    {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} :=
  Classical.choice (class_pool_nonempty D j b)

/-- Predecessor-restricted labels: the only label index a protocol can reconstruct. -/
noncomputable def restrictLabels (j : Fin D.geom.r) (L : ProcessedLabels D j.castSucc) :
    ProcessedLabels D j.castSucc := fun b =>
  if b.1 ∈ X.predecessors D.geom.r then L b else defaultLabel D j.castSucc b

/-- Erased tests at a row in the deleted process (`transferStep`): nonempty only before the failure class. -/
noncomputable def stepErased (j : Fin D.geom.r) (b : Pos T k) : Finset (Fin (T.S.n k)) :=
  if j.val < X.failure.1.val then rowErasedTests D X b else ∅

/-- Side data visible to the deleted label kernel: erased sketches blanked. -/
noncomputable def visible (j : Fin D.geom.r) (b : Pos T k) (sk : SketchArray (T := T) (k := k)) :
    SketchArray (T := T) (k := k) :=
  fun a => if a ∈ stepErased D X j b then fun _ => D.fallback else sk a

/-- Iid sketch kernel at a label-history index (TeX 18:97–99). -/
noncomputable def sketchKernel (j : Fin D.geom.r) (w : Pos T k) (idx : SketchIndex D j) :
    FinLaw (Sketch (T := T) (k := k)) :=
  FinLaw.pi fun _ => lawFin (D.currentPrior j w (labelHistory D j.castSucc idx.1 idx.2))

theorem allowedMask_nonempty' (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b) : mask.1.Nonempty := by
  have hclass : D.geom.classOf b = some j := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
    simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hmaskpos : 0 < mask.1.card := by have := mask.2.2; omega
  exact Finset.card_pos.mp hmaskpos

theorem labelWeight_nonneg' (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) : 0 ≤ D.labelWeight j side tests y := by
  unfold LateData.labelWeight
  split_ifs with hmass hpass
  · apply div_nonneg
    · unfold LateData.maskWeight
      split_ifs <;> positivity
    · exact (Real.exp_pos _).le.trans hmass
  · simp
  · unfold LateData.maskWeight
    split_ifs <;> positivity

private theorem uniformWeight_total' {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) :
    (∑ y, if y ∈ S then (1 / (S.card : ℝ)) else 0) = 1 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  field_simp

theorem labelWeight_total' (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    (∑ y, D.labelWeight j side tests y) = 1 := by
  unfold LateData.labelWeight
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests
  · simp_rw [if_pos hmass]
    have hden : 0 < D.retainedMass j side tests := (Real.exp_pos _).trans_le hmass
    calc
      (∑ y, if D.passes j side tests y then
          D.maskWeight side y / D.retainedMass j side tests else 0) =
          (∑ y, if D.passes j side tests y then D.maskWeight side y else 0) /
            D.retainedMass j side tests := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro y _
              split_ifs <;> simp
      _ = D.retainedMass j side tests / D.retainedMass j side tests := by
        simp [LateData.retainedMass]
      _ = 1 := div_self (ne_of_gt hden)
  · simp_rw [if_neg hmass]
    have hmasktotal := uniformWeight_total' side.1.1 hmask
    simpa [LateData.maskWeight] using hmasktotal

theorem labelWeight_zero_of_not_mask' (j : Fin D.geom.r) {b : Pos T k}
    (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k))
    (hy : y ∉ side.1.1) : D.labelWeight j side tests y = 0 := by
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]

/-- The label-table law has total mass one on the late pool (copy of sol-s18-1c's private
`lateLabelLaw` argument). -/
theorem labelKernel_sum_one (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j})
    (idx : LabelIndex D b.1) (tests : Finset (Fin (T.S.n k))) :
    ∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1},
      D.labelWeight j (idx.1, idx.2, rowDefaultLabel D j b) tests y.1 = 1 := by
  let side : D.encoding.base.RowOut b.1 := (idx.1, idx.2, rowDefaultLabel D j b)
  let pool := D.encoding.base.latePoolOf b.1
  have hzero (y : Fin (T.S.N k)) (hy : y ∉ pool) : D.labelWeight j side tests y = 0 := by
    apply labelWeight_zero_of_not_mask' D j side tests y
    intro hmem
    exact hy (side.1.2.1 hmem)
  have hsubtype :
      (∑ y : {y : Fin (T.S.N k) // y ∈ pool}, D.labelWeight j side tests y.1) =
        ∑ y ∈ pool, D.labelWeight j side tests y := by
    simpa [pool] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin (T.S.N k))))
        (p := fun y => y ∈ pool) (f := fun y => D.labelWeight j side tests y))
  have hpoolSum : (∑ y ∈ pool, D.labelWeight j side tests y) =
      ∑ y, D.labelWeight j side tests y := by
    have hcomp : (∑ y ∈ Finset.univ \ pool, D.labelWeight j side tests y) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact hzero y (Finset.mem_sdiff.mp hy).2
    rw [← Finset.sum_sdiff pool.subset_univ, hcomp, zero_add]
  change (∑ y : {y : Fin (T.S.N k) // y ∈ pool}, D.labelWeight j side tests y.1) = 1
  rw [hsubtype, hpoolSum]
  exact labelWeight_total' D j side tests (allowedMask_nonempty' D j b.1 b.2 idx.1)

noncomputable def labelKernel (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j})
    (idx : LabelIndex D b.1) : FinLaw {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} where
  w y := D.labelWeight j (idx.1, idx.2, rowDefaultLabel D j b) (Finset.univ \ stepErased D X j b.1) y.1
  nonneg y := labelWeight_nonneg' D j _ _ _
  sum_one := labelKernel_sum_one D j b idx _

noncomputable def rowSeedLaw (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j}) :
    FinLaw (RowSeed D j b.1) :=
  FinLaw.bind (D.encoding.kernels.maskProfile b.1) fun _ =>
    FinLaw.bind (FinLaw.pi fun a : Fin (T.S.n k) => FinLaw.pi fun idx : SketchIndex D j =>
        sketchKernel D j (flipPos b.1 a) idx) fun _ =>
      FinLaw.pi fun idx : LabelIndex D b.1 => labelKernel D X j b idx

noncomputable def classSeedLaw (j : Fin D.geom.r) : FinLaw (ClassSeed D j) :=
  FinLaw.pi fun b => rowSeedLaw D X j b

noncomputable def seedLaw : FinLaw (Seed D) := FinLaw.pi fun j => classSeedLaw D X j

/-! ### The mathematical simulation (reads the whole raw state) -/

/-- Table index used at sketch `(j,b,a)` from entering history `h`. -/
noncomputable def sketchIndex (s : X.Raw) (j : Fin D.geom.r) (b : Pos T k) (a : Fin (T.S.n k))
    (h : D.encoding.base.History j.castSucc) : SketchIndex D j :=
  if b ∈ X.predecessors D.geom.r ∧ flipPos b a ∉ X.erased then
    (if (D.directCells (flipPos b a) ∩ X.criticalCells).Nonempty then
        blockConfig D X (blockOfSite D X (flipPos b a)) s else X.fixed,
      restrictLabels D X j (historyLabels D h))
  else (h.1, historyLabels D h)

/-- One simulated row from its own seed component. -/
noncomputable def rowSim (s : X.Raw) (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (ρ : RowSeed D j b.1) : D.encoding.base.RowOut b.1 :=
  (ρ.1, (fun a => ρ.2.1 a (sketchIndex D X s j b.1 a h)),
    ρ.2.2 (ρ.1, visible D X j b.1 (fun a => ρ.2.1 a (sketchIndex D X s j b.1 a h))))

noncomputable def simRow (s : X.Raw) (j : Fin D.geom.r) (σ : ClassSeed D j)
    (h : D.encoding.base.History j.castSucc) : D.encoding.base.ClassRows j := fun b =>
  rowSim D X s j b h (σ b)

noncomputable def simFrom (s : X.Raw) (σ : Seed D) :
    ∀ m (hm : m ≤ D.geom.r), D.encoding.base.History ⟨m, Nat.lt_succ_of_le hm⟩
  | 0, _ => D.encoding.base.initialHistory (X.state s)
  | m + 1, hm =>
      D.encoding.base.extend ⟨m, hm⟩ (simFrom s σ m (Nat.le_of_succ_le hm))
        (simRow D X s ⟨m, hm⟩ (σ ⟨m, hm⟩) (simFrom s σ m (Nat.le_of_succ_le hm)))

noncomputable def simHistory (s : X.Raw) (σ : Seed D) : D.encoding.base.History (Fin.last D.geom.r) :=
  simFrom D X s σ D.geom.r le_rfl

/-! ### The protocol (reads one block per call) -/

noncomputable def cap : ℕ := ⌊Real.exp (Real.log (T.S.n k : ℝ) ^ 8)⌋₊

abbrev Reply := SketchReply (cap (T := T) (k := k)) (sketchLength T k)

/-- Affected calls in class order (TeX 18:422–423). -/
noncomputable def plan : List (SketchCall D X) :=
  (affectedCalls D X).toList.mergeSort (fun c c' => decide (c.1.val ≤ c'.1.val))

/-- Decoded sketch of call `c` from a transcript (fallback if absent or aborted). -/
noncomputable def decodeAt (t : List (Reply (T := T) (k := k))) (c : SketchCall D X) : Sketch (T := T) (k := k) :=
  match t[(plan D X).idxOf c]? with
  | some r => (decodeSketch (fixedList D X c) D.fallback r).getD (fun _ => D.fallback)
  | none => fun _ => D.fallback

noncomputable def toProcessed (j : Fin D.geom.r) (L : Pos T k → Fin (T.S.N k)) :
    ProcessedLabels D j.castSucc := fun b =>
  if h : b.1 ∈ X.predecessors D.geom.r ∧ L b.1 ∈ D.encoding.base.latePoolOf b.1 then ⟨L b.1, h.2⟩
  else defaultLabel D j.castSucc b

/-- Protocol sketch at `(j,b,a)`: oracle (decoded reply) at affected sites, the fixed-input table
entry at unaffected sites, fallback at erased or non-predecessor sites. -/
noncomputable def protoSketch (σ : Seed D) (oracle : SketchCall D X → Sketch (T := T) (k := k))
    (L : Pos T k → Fin (T.S.N k)) (j : Fin D.geom.r)
    (b : {x : Pos T k // x ∈ D.encoding.base.classes j}) (a : Fin (T.S.n k)) : Sketch (T := T) (k := k) :=
  if hpe : b.1 ∈ X.predecessors D.geom.r ∧ flipPos b.1 a ∉ X.erased then
    if (D.directCells (flipPos b.1 a) ∩ X.criticalCells).Nonempty then oracle ⟨j, ⟨b.1, b.2, hpe.1⟩, a⟩
    else (σ j b).2.1 a (X.fixed, toProcessed D X j L)
  else fun _ => D.fallback

/-- Predecessor labels of classes `< m`, recomputed from the seed and an oracle. -/
noncomputable def protoLabels (σ : Seed D) (oracle : SketchCall D X → Sketch (T := T) (k := k)) :
    ℕ → Pos T k → Fin (T.S.N k)
  | 0 => fun _ => D.fallback
  | m + 1 => fun b =>
    if hm : m < D.geom.r then
      if hb : b ∈ D.encoding.base.classes ⟨m, hm⟩ ∧ b ∈ X.predecessors D.geom.r then
        ((σ ⟨m, hm⟩ ⟨b, hb.1⟩).2.2
          ((σ ⟨m, hm⟩ ⟨b, hb.1⟩).1,
            visible D X ⟨m, hm⟩ b
              (protoSketch D X σ oracle (protoLabels σ oracle m) ⟨m, hm⟩ ⟨b, hb.1⟩))).1
      else protoLabels σ oracle m b
    else protoLabels σ oracle m b

noncomputable def request (_σ : Seed D) (t : List (Reply (T := T) (k := k))) : Fin (T.S.n k) :=
  if h : t.length < (plan D X).length then blockOf D X ((plan D X)[t.length]) else X.failure.2.2.2.2

noncomputable def answer (σ : Seed D) (t : List (Reply (T := T) (k := k))) (s : X.Raw) :
    Reply (T := T) (k := k) :=
  if h : t.length < (plan D X).length then
    let c := (plan D X)[t.length]
    encodeSketch (fixedList D X c) cap (sketchLength T k)
      ((σ c.1 ⟨c.2.1.1, c.2.1.2.1⟩).2.1 c.2.2
        (blockConfig D X (blockOf D X c) s,
          toProcessed D X c.1 (protoLabels D X σ (decodeAt D X t) c.1.val)))
  else none

noncomputable def replies (σ : Seed D) (s : X.Raw) : ℕ → List (Reply (T := T) (k := k))
  | 0 => []
  | t + 1 => replies σ s t ++ [answer D X σ (replies σ s t) s]

/-- Failure-row side data reconstructed by the protocol. -/
noncomputable def protoSide (σ : Seed D) (t : List (Reply (T := T) (k := k))) :
    D.encoding.base.RowOut X.failure.2.1.1 :=
  ((σ X.failure.1 X.failure.2.1).1,
    (fun a => protoSketch D X σ (decodeAt D X t)
      (protoLabels D X σ (decodeAt D X t) X.failure.1.val) X.failure.1 X.failure.2.1 a),
    rowDefaultLabel D X.failure.1 X.failure.2.1)

/-- Output: the tested prefix law at the failure row (TeX 18:437–438). -/
noncomputable def output (σ : Seed D) (t : List (Reply (T := T) (k := k))) : Law (T.S.N k) :=
  prefixLabelLaw D X.failure.1 (protoSide D X σ t)
    (D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val)
    (allowedMask_nonempty' D X.failure.1 X.failure.2.1.1 X.failure.2.1.2 (protoSide D X σ t).1)

end Defs

/-! ### Open obligations (statements only; each a single argument) -/

section Obligations
variable {D : LateData hPT} {X : CriticalTransferData D}

theorem replies_length' (σ : Seed D) (s : X.Raw) (t : ℕ) : (replies D X σ s t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [replies, ih]

/-! #### O1: law agreement, decomposed -/

theorem finLaw_ext' {A : Type*} [Fintype A] (P Q : FinLaw A) (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P
  cases Q
  congr 1
  exact funext h

/-- Weight of a pushforward, for whatever decidability instance the term carries. -/
theorem map_w' {α β : Type*} [Fintype α] [Fintype β] (inst : DecidableEq β) (P : FinLaw α)
    (f : α → β) (y : β) :
    (@FinLaw.map α β _ _ inst P f).w y = ∑ a, @ite _ (f a = y) (inst (f a) y) (P.w a) 0 := rfl

/-- A constant pushforward is a point mass, for any decidability instances. -/
theorem map_const' {α β : Type*} [Fintype α] [Fintype β] (P : FinLaw α) (c : β)
    (i1 i2 : DecidableEq β) : @FinLaw.map α β _ _ i1 P (fun _ => c) = @FinLaw.dirac β _ i2 c := by
  apply finLaw_ext'
  intro y
  rw [map_w']
  change _ = @ite _ (y = c) (i2 y c) 1 0
  by_cases h : c = y
  · subst h
    simp [P.sum_one]
  · have h' : ¬ y = c := fun e => h e.symm
    simp [h, h']

/-- Evaluating an independent table at a fixed index has that index's law. -/
theorem map_pi_eval {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    (K : I → FinLaw B) (a : I) : FinLaw.map (FinLaw.pi K) (fun seed => seed a) = K a := by
  apply finLaw_ext'
  intro y
  let f : I → B → ℝ := fun i c => if i = a then (if c = y then (K i).w c else 0) else (K i).w c
  have hprod : ∏ i, ∑ c, f i c = (K a).w y := by
    rw [Fintype.prod_eq_mul_prod_compl a]
    have h1 : ∑ c, f a c = (K a).w y := by simp [f]
    have h2 : ∏ i ∈ ({a}ᶜ : Finset I), ∑ c, f i c = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hia : i ≠ a := by simpa using hi
      simp only [f, if_neg hia]
      exact (K i).sum_one
    rw [h1, h2, mul_one]
  change (∑ seed : I → B, if seed a = y then ∏ i, (K i).w (seed i) else 0) = (K a).w y
  rw [← hprod, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ a = y
  · rw [if_pos hσ]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = a
    · subst hi
      simp [f, hσ]
    · simp [f, hi]
  · rw [if_neg hσ]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [f, hσ])

/-- The label weight reads only the mask and the sketches outside the omitted tests. -/
theorem labelWeight_offE (j : Fin D.geom.r) {b : Pos T k} (side side' : D.encoding.base.RowOut b)
    (E : Finset (Fin (T.S.n k))) (hmask : side.1 = side'.1)
    (hsk : ∀ a, a ∉ E → side.2.1 a = side'.2.1 a) (y : Fin (T.S.N k)) :
    D.labelWeight j side (Finset.univ \ E) y = D.labelWeight j side' (Finset.univ \ E) y := by
  have hp (u : Fin (T.S.N k)) :
      D.passes j side (Finset.univ \ E) u ↔ D.passes j side' (Finset.univ \ E) u := by
    constructor <;> intro h a ha <;>
      simpa only [LateData.sketchHit, hsk a (Finset.mem_sdiff.mp ha).2] using h a ha
  have hm (u : Fin (T.S.N k)) : D.maskWeight side u = D.maskWeight side' u := by
    unfold LateData.maskWeight
    rw [hmask]
  have hmass : D.retainedMass j side (Finset.univ \ E) = D.retainedMass j side' (Finset.univ \ E) := by
    unfold LateData.retainedMass
    simp_rw [hp, hm]
  unfold LateData.labelWeight
  rw [hmass, hp, hm]

/-- Index correctness: every table index used by the simulation has the actual current prior. -/
theorem sketchIndex_correct (hD : D.Spec) (hG : TransferGeometry X) (s : X.Raw) (hs : X.rawLaw.w s ≠ 0)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j) (a : Fin (T.S.n k))
    (h : D.encoding.base.History j.castSucc) (hh : h.1 = X.state s) :
    D.currentPrior j (flipPos b a) (labelHistory D j.castSucc (sketchIndex D X s j b a h).1
      (sketchIndex D X s j b a h).2) = D.currentPrior j (flipPos b a) h := by
  unfold sketchIndex
  by_cases hpe : b ∈ X.predecessors D.geom.r ∧ flipPos b a ∉ X.erased
  · rw [if_pos hpe]
    have hlab : ∀ cfg : Config D.fresh, D.currentPrior j (flipPos b a)
        (labelHistory D j.castSucc cfg (restrictLabels D X j (historyLabels D h))) =
          D.currentPrior j (flipPos b a) (cfg, h.2) := by
      intro cfg
      apply currentPrior_predecessor_local D X hD (⟨j, ⟨b, hb, hpe.1⟩, a⟩ : SketchCall D X)
      · intro C _
        rfl
      · intro b' hb'
        simp only [labelHistory, restrictLabels, if_pos hb', historyLabels, LateProcessBase.rowLabel]
    by_cases hcrit : (D.directCells (flipPos b a) ∩ X.criticalCells).Nonempty
    · rw [if_pos hcrit]
      dsimp only
      rw [hlab]
      have hdir : flipPos b a ∈ X.directEven := Finset.mem_biUnion.mpr ⟨b, hpe.1,
        Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
      have hex : ∃ a', D.directCells (flipPos b a) ∩ X.criticalCells ⊆ X.blockCells a' :=
        hG.one_block _ (Finset.mem_sdiff.mpr ⟨hdir, hpe.2⟩)
      have hbo : blockOfSite D X (flipPos b a) = Classical.choose hex := by
        simp only [blockOfSite, dif_pos hex]
      rw [hbo]
      exact (block_currentPrior_eq D X hD _ s hs j (flipPos b a) h hh (Classical.choose_spec hex)).symm
    · rw [if_neg hcrit]
      dsimp only
      rw [hlab]
      apply Lane_sol_s18_n4.priorAt_local D hD j.castSucc (flipPos b a)
      · intro C hC
        have hnc : C ∉ X.criticalCells := fun hcC => hcrit ⟨C, Finset.mem_inter.mpr ⟨hC, hcC⟩⟩
        rw [hh]
        exact (rawLaw_noncritical_fixed D X s hs C hnc).symm
      · intro b' _
        rfl
  · rw [if_neg hpe]
    exact (currentPrior_labelHistory D j (flipPos b a) h).symm

private theorem ite_triple {M S Y : Type*} (m m0 : M) (G sk0 : S) (Lv Lv0 y0 : Y)
    (hL : m = m0 → G = sk0 → Lv = Lv0) (A B C : ℝ)
    [Decidable ((m, G, Lv) = (m0, sk0, y0))] [Decidable (m = m0)] [Decidable (G = sk0)]
    [Decidable (Lv0 = y0)] :
    (if (m, G, Lv) = (m0, sk0, y0) then A * (B * C) else 0) =
      (if m = m0 then A else 0) * ((if G = sk0 then B else 0) * (if Lv0 = y0 then C else 0)) := by
  by_cases hm : m = m0
  · by_cases hG : G = sk0
    · have hLv := hL hm hG
      by_cases hy : Lv0 = y0
      · have he : (m, G, Lv) = (m0, sk0, y0) := by rw [hm, hG, hLv, hy]
        rw [if_pos he, if_pos hm, if_pos hG, if_pos hy]
      · have he : (m, G, Lv) ≠ (m0, sk0, y0) := by
          intro he
          apply hy
          rw [← hLv]
          exact (Prod.mk.inj (Prod.mk.inj he).2).2
        rw [if_neg he, if_pos hm, if_pos hG, if_neg hy]
        ring
    · have he : (m, G, Lv) ≠ (m0, sk0, y0) := fun he => hG (Prod.mk.inj (Prod.mk.inj he).2).1
      rw [if_neg he, if_pos hm, if_neg hG]
      ring
  · have he : (m, G, Lv) ≠ (m0, sk0, y0) := fun he => hm (Prod.mk.inj he).1
    rw [if_neg he, if_neg hm]
    ring

/-- (O1-row) One simulated row has the deleted row law (TeX 18:97–104, 18:362–375). -/
theorem rowSim_law (hD : D.Spec) (hG : TransferGeometry X) (s : X.Raw) (hs : X.rawLaw.w s ≠ 0)
    (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hh : h.1 = X.state s) :
    FinLaw.map (rowSeedLaw D X j b) (rowSim D X s j b h) =
      deletedRowKernel D j b h (Finset.univ \ stepErased D X j b.1) := by
  apply finLaw_ext'
  rintro ⟨m0, sk0, y0⟩
  let idx : Fin (T.S.n k) → SketchIndex D j := fun a => sketchIndex D X s j b.1 a h
  let Tsk := FinLaw.pi fun a : Fin (T.S.n k) =>
    FinLaw.pi fun i : SketchIndex D j => sketchKernel D j (flipPos b.1 a) i
  let Tlab := FinLaw.pi fun i : LabelIndex D b.1 => labelKernel D X j b i
  let g : (Fin (T.S.n k) → SketchIndex D j → Sketch (T := T) (k := k)) → SketchArray (T := T) (k := k) :=
    fun Tt a => Tt a (idx a)
  let i0 : LabelIndex D b.1 := (m0, visible D X j b.1 sk0)
  have hsplit : (FinLaw.map (rowSeedLaw D X j b) (rowSim D X s j b h)).w (m0, sk0, y0) =
      (D.encoding.kernels.maskProfile b.1).w m0 *
        ((FinLaw.map Tsk g).w sk0 * (FinLaw.map Tlab (fun L => L i0)).w y0) := by
    change (∑ ρ : RowSeed D j b.1, if rowSim D X s j b h ρ = (m0, sk0, y0) then
        (D.encoding.kernels.maskProfile b.1).w ρ.1 * (Tsk.w ρ.2.1 * Tlab.w ρ.2.2) else 0) =
      (D.encoding.kernels.maskProfile b.1).w m0 *
        ((∑ Tt, if g Tt = sk0 then Tsk.w Tt else 0) * (∑ L, if L i0 = y0 then Tlab.w L else 0))
    calc (∑ ρ : RowSeed D j b.1, if rowSim D X s j b h ρ = (m0, sk0, y0) then
          (D.encoding.kernels.maskProfile b.1).w ρ.1 * (Tsk.w ρ.2.1 * Tlab.w ρ.2.2) else 0)
        = ∑ m, ∑ Tt, ∑ L, (if m = m0 then (D.encoding.kernels.maskProfile b.1).w m else 0) *
            ((if g Tt = sk0 then Tsk.w Tt else 0) * (if L i0 = y0 then Tlab.w L else 0)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun Tt _ => Finset.sum_congr rfl fun L _ => ?_
          exact ite_triple m m0 (g Tt) sk0 (L (m, visible D X j b.1 (g Tt))) (L i0) y0
            (fun hm hg => by rw [hm, hg]) _ _ _
      _ = (∑ m, if m = m0 then (D.encoding.kernels.maskProfile b.1).w m else 0) *
            ((∑ Tt, if g Tt = sk0 then Tsk.w Tt else 0) * (∑ L, if L i0 = y0 then Tlab.w L else 0)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun Tt _ => ?_
          rw [Finset.mul_sum]
      _ = _ := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hT : FinLaw.map Tsk g = FinLaw.pi fun a => sketchKernel D j (flipPos b.1 a) (idx a) := by
    have h1 := pi_map_coordinatewise
      (fun a : Fin (T.S.n k) => FinLaw.pi fun i : SketchIndex D j => sketchKernel D j (flipPos b.1 a) i)
      (fun (a : Fin (T.S.n k)) (t : SketchIndex D j → Sketch (T := T) (k := k)) => t (idx a))
    refine h1.trans ?_
    congr 1
    funext a
    exact map_pi_eval _ _
  have hL : FinLaw.map Tlab (fun L => L i0) = labelKernel D X j b i0 := map_pi_eval _ _
  rw [hsplit, hT, hL, deletedRowKernel_formula]
  dsimp only [LateProcessBase.rowLabel]
  have hprod : (FinLaw.pi fun a => sketchKernel D j (flipPos b.1 a) (idx a)).w sk0 =
      ∏ a, ∏ t, (D.currentPrior j (flipPos b.1 a) h).w (sk0 a t) := by
    change (∏ a, ∏ t, (D.currentPrior j (flipPos b.1 a)
      (labelHistory D j.castSucc (idx a).1 (idx a).2)).w (sk0 a t)) = _
    apply Finset.prod_congr rfl
    intro a _
    exact congrArg (fun P : Law (T.S.N k) => ∏ t, P.w (sk0 a t))
      (sketchIndex_correct hD hG s hs j b.1 b.2 a h hh)
  have hlab : (labelKernel D X j b i0).w y0 =
      D.labelWeight j (m0, sk0, y0) (Finset.univ \ stepErased D X j b.1) y0.1 := by
    change D.labelWeight j (m0, visible D X j b.1 sk0, rowDefaultLabel D j b)
      (Finset.univ \ stepErased D X j b.1) y0.1 = _
    apply labelWeight_offE
    · rfl
    · intro a ha
      change visible D X j b.1 sk0 a = sk0 a
      simp [visible, ha]
  rw [hprod, hlab]
  ring

/-- (O1-class) One simulated class has the law of `transferStep` (TeX 18:362–375). -/
theorem classSim_law (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (s : X.Raw) (hs : X.rawLaw.w s ≠ 0)
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) (hh : h.1 = X.state s) :
    FinLaw.map (classSeedLaw D X j) (fun σ => simRow D X s j σ h) = transferStep D X j h := by
  have h1 := pi_map_coordinatewise (fun b => rowSeedLaw D X j b) (fun b ρ => rowSim D X s j b h ρ)
  have h2 : FinLaw.pi (fun b => FinLaw.map (rowSeedLaw D X j b) (rowSim D X s j b h)) =
      transferStep D X j h := by
    calc FinLaw.pi (fun b => FinLaw.map (rowSeedLaw D X j b) (rowSim D X s j b h))
        = FinLaw.pi (fun b => deletedRowKernel D j b h (Finset.univ \ stepErased D X j b.1)) := by
          congr 1
          funext b
          exact rowSim_law hD hG s hs j b h hh
      _ = transferStep D X j h := by
          unfold transferStep
          by_cases hj : j.val < X.failure.1.val
          · rw [if_pos hj]
            unfold deletedTransition
            simp only [stepErased, if_pos hj]
          · rw [if_neg hj]
            unfold LateKernels.referenceTransition
            congr 1
            funext b
            apply finLaw_ext'
            intro out
            rw [deletedRowKernel_formula, hT.reference_formula]
            simp only [stepErased, if_neg hj, Finset.sdiff_empty]
  convert h1.trans h2 using 2
  all_goals first | rfl | (funext σ; rfl)

/-- The simulated history up to `m` reads only the class seeds before `m`. -/
theorem simFrom_depends (s : X.Raw) : ∀ m (hm : m ≤ D.geom.r) (σ σ' : Seed D),
    (∀ i : Fin D.geom.r, i.val < m → σ i = σ' i) → simFrom D X s σ m hm = simFrom D X s σ' m hm
  | 0, _, _, _, _ => rfl
  | m + 1, hm, σ, σ', hσ => by
    have ih := simFrom_depends s m (Nat.le_of_succ_le hm) σ σ'
      (fun i hi => hσ i (Nat.lt_succ_of_lt hi))
    simp only [simFrom]
    rw [ih, hσ ⟨m, hm⟩ (Nat.lt_succ_self m)]

/-- Fibres of one coordinate carry equal mass for an integrand blind to that coordinate. -/
theorem sum_fiber_const {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] (i0 : I) (H : (∀ i, A i) → ℝ)
    (hH : ∀ σ c, H (Function.update σ i0 c) = H σ) (c c' : A i0) :
    (∑ σ : ∀ i, A i, if σ i0 = c then H σ else 0) = ∑ σ : ∀ i, A i, if σ i0 = c' then H σ else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun σ => Function.update σ i0 c') (fun σ => Function.update σ i0 c)
  · intro σ _
    simp
  · intro σ _
    simp
  · intro σ hσ
    have hc : σ i0 = c := by simpa using hσ
    rw [Function.update_idem, ← hc, Function.update_eq_self]
  · intro σ hσ
    have hc : σ i0 = c' := by simpa using hσ
    rw [Function.update_idem, ← hc, Function.update_eq_self]
  · intro σ _
    exact (hH σ c').symm

/-- Independence of one product coordinate from an integrand blind to it. -/
theorem sum_split_coord {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] (w : ∀ i, A i → ℝ) (i0 : I)
    (hw : ∑ c, w i0 c = 1) (G : (∀ i, A i) → ℝ) (hG : ∀ σ c, G (Function.update σ i0 c) = G σ)
    (φ : A i0 → ℝ) :
    ∑ σ : ∀ i, A i, G σ * φ (σ i0) * ∏ i, w i (σ i) =
      (∑ σ : ∀ i, A i, G σ * ∏ i, w i (σ i)) * ∑ c, φ c * w i0 c := by
  let R : (∀ i, A i) → ℝ := fun σ => ∏ i ∈ ({i0}ᶜ : Finset I), w i (σ i)
  let H : (∀ i, A i) → ℝ := fun σ => G σ * R σ
  have hH : ∀ σ c, H (Function.update σ i0 c) = H σ := by
    intro σ c
    simp only [H, R, hG]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ i0 := by simpa using hi
    rw [Function.update_of_ne hne]
  have hprod (σ : ∀ i, A i) : ∏ i, w i (σ i) = w i0 (σ i0) * R σ :=
    Fintype.prod_eq_mul_prod_compl i0 _
  let K : A i0 → ℝ := fun c => ∑ σ : ∀ i, A i, if σ i0 = c then H σ else 0
  have hfib (ψ : A i0 → ℝ) : ∑ σ : ∀ i, A i, ψ (σ i0) * H σ = ∑ c, ψ c * K c := by
    simp only [K, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.sum_eq_single (σ i0)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  have hK : ∀ c c', K c = K c' := fun c c' => sum_fiber_const i0 H hH c c'
  have hL : ∑ σ : ∀ i, A i, G σ * φ (σ i0) * ∏ i, w i (σ i) =
      ∑ σ : ∀ i, A i, (φ (σ i0) * w i0 (σ i0)) * H σ := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [hprod]
    simp only [H]
    ring
  have hR : ∑ σ : ∀ i, A i, G σ * ∏ i, w i (σ i) = ∑ σ : ∀ i, A i, w i0 (σ i0) * H σ := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [hprod]
    simp only [H]
    ring
  rw [hL, hR, hfib (fun c => φ c * w i0 c), hfib (fun c => w i0 c)]
  calc ∑ c, φ c * w i0 c * K c = ∑ c, φ c * w i0 c * (∑ c', w i0 c' * K c') := by
        apply Finset.sum_congr rfl
        intro c _
        congr 1
        calc K c = (∑ c', w i0 c') * K c := by rw [hw, one_mul]
          _ = ∑ c', w i0 c' * K c' := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun c' _ => by rw [hK c c']
    _ = (∑ c', w i0 c' * K c') * ∑ c, φ c * w i0 c := by
        rw [← Finset.sum_mul]
        ring

/-- (O1-run) Class-by-class induction: the seeded run has the deleted run's law. -/
theorem simFrom_law (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (s : X.Raw) (hs : X.rawLaw.w s ≠ 0) : ∀ m (hm : m ≤ D.geom.r),
    FinLaw.map (seedLaw D X) (fun σ => simFrom D X s σ m hm) =
      D.encoding.base.runFrom (transferStep D X) (X.state s) m hm := by
  intro m
  induction m with
  | zero =>
    intro hm
    exact map_const' (seedLaw D X) (D.encoding.base.initialHistory (X.state s)) _ _
  | succ m ih =>
    intro hm
    apply finLaw_ext'
    intro H
    rw [runFrom_step_weight D (transferStep D X) (X.state s) m hm H]
    set j : Fin D.geom.r := ⟨m, hm⟩ with hj
    set H0 : D.encoding.base.History j.castSucc :=
      D.beforeHistory H ⟨m, by omega⟩ (by simp) with hH0
    set R : D.encoding.base.ClassRows j := D.pastRows H j (by simp [j]) with hR
    have hcond : ∀ σ : Seed D, (simFrom D X s σ (m + 1) hm = H) ↔
        (simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 ∧ simRow D X s j (σ j) H0 = R) := by
      intro σ
      constructor
      · intro he
        have hx := congrArg (fun H' : D.encoding.base.History j.succ =>
          (D.beforeHistory H' j.castSucc (by simp), D.pastRows H' j (by simp))) he
        simp only [simFrom] at hx
        rw [Lane_sol_s18_n4.beforeHistory_extend_self, Lane_sol_s18_n4.pastRows_extend_self] at hx
        have h0 : simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 := congrArg Prod.fst hx
        refine ⟨h0, ?_⟩
        have h1 := congrArg Prod.snd hx
        simp only at h1
        rw [h0] at h1
        exact h1
      · rintro ⟨h0, h1⟩
        simp only [simFrom]
        change D.encoding.base.extend j (simFrom D X s σ m _)
          (simRow D X s j (σ j) (simFrom D X s σ m _)) = H
        rw [h0, h1]
        exact Lane_sol_s18_n4.extend_beforeHistory_pastRows D j H
    rw [map_w']
    refine (Finset.sum_congr rfl fun σ _ => ?_ : _ = ∑ σ : Seed D,
        (if simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 then (1 : ℝ) else 0) *
          (if simRow D X s j (σ j) H0 = R then (1 : ℝ) else 0) *
            ∏ i, (classSeedLaw D X i).w (σ i)).trans ?_
    · change @ite _ _ _ (∏ i, (classSeedLaw D X i).w (σ i)) 0 = _
      by_cases hc : simFrom D X s σ (m + 1) hm = H
      · obtain ⟨h0, h1⟩ := (hcond σ).mp hc
        simp [hc, h0, h1]
      · by_cases h0 : simFrom D X s σ m (Nat.le_of_succ_le hm) = H0
        · by_cases h1 : simRow D X s j (σ j) H0 = R
          · exact absurd ((hcond σ).mpr ⟨h0, h1⟩) hc
          · simp [hc, h1]
        · simp [hc, h0]
    have hblind : ∀ (σ : Seed D) (c : ClassSeed D j),
        (if simFrom D X s (Function.update σ j c) m (Nat.le_of_succ_le hm) = H0 then (1 : ℝ) else 0) =
          (if simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 then (1 : ℝ) else 0) := by
      intro σ c
      rw [simFrom_depends s m (Nat.le_of_succ_le hm) (Function.update σ j c) σ
        (fun i hi => Function.update_of_ne (by intro he; rw [he] at hi; exact lt_irrefl _ hi) _ _)]
    have key := sum_split_coord (fun i => (classSeedLaw D X i).w) j (classSeedLaw D X j).sum_one
      (fun σ => if simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 then (1 : ℝ) else 0) hblind
      (fun c => if simRow D X s j c H0 = R then (1 : ℝ) else 0)
    rw [key]
    have hfirst : (∑ σ : Seed D, (if simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 then (1 : ℝ) else 0) *
        ∏ i, (classSeedLaw D X i).w (σ i)) =
        (D.encoding.base.runFrom (transferStep D X) (X.state s) m (Nat.le_of_succ_le hm)).w H0 := by
      rw [← ih (Nat.le_of_succ_le hm), map_w']
      apply Finset.sum_congr rfl
      intro σ _
      change _ = @ite _ _ _ (∏ i, (classSeedLaw D X i).w (σ i)) 0
      by_cases h0 : simFrom D X s σ m (Nat.le_of_succ_le hm) = H0 <;> simp [h0]
    have hsecond : (∑ c, (if simRow D X s j c H0 = R then (1 : ℝ) else 0) * (classSeedLaw D X j).w c) =
        (FinLaw.map (classSeedLaw D X j) (fun c => simRow D X s j c H0)).w R := by
      rw [map_w']
      apply Finset.sum_congr rfl
      intro c _
      by_cases h1 : simRow D X s j c H0 = R <;> simp [h1]
    rw [hfirst, hsecond]
    by_cases hw : (D.encoding.base.runFrom (transferStep D X) (X.state s) m
        (Nat.le_of_succ_le hm)).w H0 = 0
    · rw [hw, zero_mul, zero_mul]
    · have hstart : H0.1 = X.state s := runFrom_initial_support D (transferStep D X) (X.state s) m
        (Nat.le_of_succ_le hm) H0 hw
      rw [classSim_law hD hT hG s hs j H0 hstart]

/-- (O1) Law agreement, TeX 18:420–427 with 18:338–375. For `s` in the raw support, the seeded
simulation has exactly the law of the deleted run. -/
theorem simHistory_law (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (s : X.Raw) (hs : X.rawLaw.w s ≠ 0) :
    FinLaw.map (seedLaw D X) (simHistory D X s) =
      D.encoding.base.runFull (transferStep D X) (X.state s) :=
  simFrom_law hD hT hG s hs D.geom.r le_rfl

/-- (O2) Pathwise agreement on the retained event, TeX 18:428–434. On `retainedFailure` for the
simulated history, every affected reply decodes to the simulated sketch (induction over classes,
`plan` sorted by class and nodup, `decode_encodeSketch`, `protoLabels` reads only earlier classes),
so the protocol output equals the tested prefix law of the simulated failure row
(`prefixLaw_erased_invariant`). ~350 lines. -/
theorem output_eq_on_retained (hD : D.Spec) (hG : TransferGeometry X)
    (s : X.Raw) (hs : X.rawLaw.w s ≠ 0) (σ : Seed D)
    (hret : retainedFailure D X (s, simHistory D X s σ)) :
    output D X σ (replies D X σ s (plan D X).length) =
      prefixLabelLaw D X.failure.1 (D.pastRows (simHistory D X s σ) X.failure.1 X.failure.1.isLt X.failure.2.1)
        (D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val)
        (allowedMask_nonempty' D X.failure.1 X.failure.2.1.1 X.failure.2.1.2
          (D.pastRows (simHistory D X s σ) X.failure.1 X.failure.1.isLt X.failure.2.1).1) := by
  let H : ∀ i : Fin (D.geom.r + 1), D.encoding.base.History i :=
    fun i => simFrom D X s σ i.val (Nat.lt_succ_iff.mp i.isLt)
  let rows : ∀ j : Fin D.geom.r, D.encoding.base.ClassRows j :=
    fun j => simRow D X s j (σ j) (H j.castSucc)
  have hstep : ∀ j : Fin D.geom.r,
      H j.succ = D.encoding.base.extend j (H j.castSucc) (rows j) := by
    intro j
    rfl
  have hbefore (i t : Fin (D.geom.r + 1)) (hit : i.val ≤ t.val) :
      D.beforeHistory (H t) i hit = H i :=
    Lane_sol_s18_2g_o2.beforeHistory_of_extends D H rows hstep i t hit
  have hpast (j : Fin D.geom.r) (t : Fin (D.geom.r + 1)) (hjt : j.val < t.val) :
      D.pastRows (H t) j hjt = rows j :=
    Lane_sol_s18_2g_o2.pastRows_of_extends D H rows hstep j t hjt
  have hpastFull (j : Fin D.geom.r) (b : {x : Pos T k // x ∈ D.encoding.base.classes j}) :
      D.pastRows (simHistory D X s σ) j j.isLt b =
        rowSim D X s j b (H j.castSucc) (σ j b) :=
    congrFun (hpast j (Fin.last D.geom.r) j.isLt) b
  sorry

theorem sameBlock_trans' {a b c : Fin (T.S.n k)} (hab : X.sameBlock a b) (hbc : X.sameBlock b c) :
    X.sameBlock a c := by
  unfold CriticalTransferData.sameBlock at hab hbc ⊢
  rcases hab with hab | ⟨⟨t1, ht1, ha1⟩, ⟨t2, ht2, hb2⟩⟩
  · rcases hbc with hbc | ⟨⟨t3, ht3, hb3⟩, ⟨t4, ht4, hc4⟩⟩
    · left
      have h := D.geom.Lsub.add_mem hab hbc
      rwa [sub_add_sub_cancel] at h
    · right
      refine ⟨⟨t3, ht3, ?_⟩, ⟨t4, ht4, hc4⟩⟩
      have h := D.geom.Lsub.add_mem hab hb3
      rwa [sub_add_sub_cancel] at h
  · rcases hbc with hbc | ⟨_, ⟨t4, ht4, hc4⟩⟩
    · right
      refine ⟨⟨t1, ht1, ha1⟩, ⟨t2, ht2, ?_⟩⟩
      have h := D.geom.Lsub.add_mem (D.geom.Lsub.neg_mem hbc) hb2
      rwa [neg_sub, sub_add_sub_cancel] at h
    · right
      exact ⟨⟨t1, ht1, ha1⟩, ⟨t4, ht4, hc4⟩⟩

theorem blockCells_subset_of_sameBlock {a a' : Fin (T.S.n k)} (h : X.sameBlock a a') :
    X.blockCells a' ⊆ X.blockCells a := by
  intro C hC
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨htc, hs⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htc, sameBlock_trans' h hs⟩, rfl⟩

theorem plan_perm : (plan D X).Perm (affectedCalls D X).toList := List.mergeSort_perm _ _

theorem mem_plan {c : SketchCall D X} : c ∈ plan D X ↔ c ∈ affectedCalls D X := by
  rw [plan_perm.mem_iff, Finset.mem_toList]

theorem plan_nodup : (plan D X).Nodup := plan_perm.nodup_iff.mpr (Finset.nodup_toList _)

/-- An affected call meets its responding block in a direct cell. -/
theorem affected_block (hG : TransferGeometry X) {c : SketchCall D X} (hc : c ∈ affectedCalls D X) :
    ∃ C, C ∈ D.directCells (site D X c) ∧ C ∈ X.blockCells (blockOf D X c) := by
  obtain ⟨hne, C, hC⟩ := (Finset.mem_filter.mp hc).2
  have hdir : site D X c ∈ X.directEven := Finset.mem_biUnion.mpr ⟨c.2.1.1, c.2.1.2.2,
    Finset.mem_image.mpr ⟨c.2.2, Finset.mem_univ _, rfl⟩⟩
  have hex : ∃ a, D.directCells (site D X c) ∩ X.criticalCells ⊆ X.blockCells a :=
    hG.one_block _ (Finset.mem_sdiff.mpr ⟨hdir, hne⟩)
  refine ⟨C, (Finset.mem_inter.mp hC).1, ?_⟩
  have hb : blockOf D X c = Classical.choose hex := by
    simp only [blockOf, blockOfSite, dif_pos hex]
  rw [hb]
  exact Classical.choose_spec hex hC

theorem request_replies (σ : Seed D) (s : X.Raw) (t : ℕ) (ht : t < (plan D X).length) :
    request D X σ (replies D X σ s t) = blockOf D X ((plan D X)[t]) := by
  have hlen : (replies D X σ s t).length = t := replies_length' σ s t
  have hlt : (replies D X σ s t).length < (plan D X).length := by rw [hlen]; exact ht
  unfold request
  rw [dif_pos hlt]
  congr 2

/-- (O3) Per-block call count, TeX 18:446–451: `sameBlock` is an equivalence on coordinates
(Lsub is a subgroup), so an affected call answered by a block equivalent to `a` meets
`blockCells a`; `plan` is nodup; then `block_sketchCalls_card`. -/
theorem calls_bound' (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hbudget : ((D.geom.r * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
      (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 20)
    (σ : Seed D) (s : X.Raw) (a : Fin (T.S.n k)) :
    ((Finset.range (plan D X).length).filter fun t =>
      X.sameBlock a (request D X σ (replies D X σ s t))).card ≤ ⌈Real.log (T.S.n k) ^ 20⌉₊ := by
  have hSnat : (Finset.univ.filter fun c : SketchCall D X =>
      (D.directCells (site D X c) ∩ X.blockCells a).Nonempty).card ≤
      D.geom.r * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
        (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
          ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) := by
    have h := block_sketchCalls_card D X hG hmargin a
    simp only [Nat.mul_assoc] at h ⊢
    exact h
  have hS : ((Finset.univ.filter fun c : SketchCall D X =>
      (D.directCells (site D X c) ∩ X.blockCells a).Nonempty).card : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 20 := (Nat.cast_le.mpr hSnat).trans hbudget
  have hcard : ((Finset.range (plan D X).length).filter fun t =>
      X.sameBlock a (request D X σ (replies D X σ s t))).card ≤
      (Finset.univ.filter fun c : SketchCall D X =>
        (D.directCells (site D X c) ∩ X.blockCells a).Nonempty).card := by
    have h := Finset.card_le_card_of_injOn (fun t => (plan D X)[t]?)
      (s := (Finset.range (plan D X).length).filter fun t =>
        X.sameBlock a (request D X σ (replies D X σ s t)))
      (t := (Finset.univ.filter fun c : SketchCall D X =>
        (D.directCells (site D X c) ∩ X.blockCells a).Nonempty).map
          ⟨Option.some, Option.some_injective _⟩) ?_ ?_
    · simpa only [Finset.card_map] using h
    · intro t ht
      obtain ⟨htr, hsb⟩ := Finset.mem_filter.mp ht
      have hlt : t < (plan D X).length := Finset.mem_range.mp htr
      rw [request_replies σ s t hlt] at hsb
      have hmem : (plan D X)[t] ∈ affectedCalls D X := mem_plan.mp (List.getElem_mem hlt)
      obtain ⟨C, hCdir, hCblock⟩ := affected_block hG hmem
      refine Finset.mem_map.mpr ⟨(plan D X)[t], Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        C, Finset.mem_inter.mpr ⟨hCdir, blockCells_subset_of_sameBlock hsb hCblock⟩⟩, ?_⟩
      simp [List.getElem?_eq_getElem hlt]
    · intro t1 ht1 t2 ht2 heq
      have h1 : t1 < (plan D X).length := Finset.mem_range.mp (Finset.mem_filter.mp ht1).1
      have h2 : t2 < (plan D X).length := Finset.mem_range.mp (Finset.mem_filter.mp ht2).1
      simp only [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.some.injEq] at heq
      exact (plan_nodup.getElem_inj_iff).mp heq
  have hreal : (((Finset.range (plan D X).length).filter fun t =>
      X.sameBlock a (request D X σ (replies D X σ s t))).card : ℝ) ≤
      (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) :=
    ((Nat.cast_le.mpr hcard).trans hS).trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- (O4) The output law lies on the second side (interface repair 8, TeX 18:617–628):
`prefixLabelLaw` vanishes off the mask ⊆ late pool ⊆ `reserveY` ⊆ `T.Y k`. -/
theorem output_supported (σ : Seed D) (t : List (Reply (T := T) (k := k))) :
    (output D X σ t).SupportedIn (T.Y k) := by
  intro x hx
  change D.labelWeight X.failure.1 (protoSide D X σ t)
    (D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val) x = 0
  apply labelWeight_zero_of_not_mask'
  intro hmask
  have hj : D.geom.classOf X.failure.2.1.1 = some X.failure.1 :=
    (D.encoding.base.class_of_spec X.failure.2.1.1 X.failure.1).mp X.failure.2.1.2
  have hpool : D.encoding.base.latePoolOf X.failure.2.1.1 = D.encoding.base.latePool X.failure.1 := by
    simp [LateProcessBase.latePoolOf, hj]
  have hin : x ∈ D.encoding.base.latePoolOf X.failure.2.1.1 := (protoSide D X σ t).1.2.1 hmask
  rw [hpool] at hin
  exact hx (hPT.tiling_valid.reserveY_subset (D.encoding.base.latePool_reserve X.failure.1 hin))

end Obligations

/-! ### Generic finite-law facts and the protocol -/

section Assembly

theorem pr_bind' {α β : Type*} [Fintype α] [Fintype β] (P : FinLaw α) (K : α → FinLaw β)
    (A : α × β → Prop) :
    (FinLaw.bind P K).pr A = ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := by
  unfold FinLaw.pr FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem pr_map' {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (P : FinLaw α) (f : α → β)
    (A : β → Prop) : (FinLaw.map P f).pr A = P.pr (fun a => A (f a)) := by
  unfold FinLaw.pr FinLaw.map
  calc (∑ b, if A b then ∑ a, (if f a = b then P.w a else 0) else 0)
      = ∑ b, ∑ a, (if f a = b ∧ A b then P.w a else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hA : A b
        · rw [if_pos hA]
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : f a = b <;> simp [h, hA]
        · rw [if_neg hA]
          symm
          apply Finset.sum_eq_zero
          intro a _
          simp [hA]
    _ = ∑ a, ∑ b, (if f a = b ∧ A b then P.w a else 0) := Finset.sum_comm
    _ = ∑ a, if A (f a) then P.w a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single (f a)]
        · simp
        · intro b _ hb
          have hne : f a ≠ b := fun h => hb h.symm
          simp [hne]
        · simp

theorem pr_mono_support' {α : Type*} [Fintype α] (P : FinLaw α) {A B : α → Prop}
    (h : ∀ a, P.w a ≠ 0 → A a → B a) : P.pr A ≤ P.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro a _
  by_cases hA : A a
  · by_cases hw : P.w a = 0
    · rw [if_pos hA, hw]
      split_ifs <;> simp
    · rw [if_pos hA, if_pos (h a hw hA)]
  · rw [if_neg hA]
    split_ifs
    · exact P.nonneg a
    · exact le_rfl

variable {D : LateData hPT} {X : CriticalTransferData D}

theorem answer_local' (σ : Seed D) (t : List (Reply (T := T) (k := k))) (s s' : X.Raw)
    (hs : ∀ C ∈ X.blockCells (request D X σ t), s C = s' C) :
    answer D X σ t s = answer D X σ t s' := by
  unfold answer
  by_cases h : t.length < (plan D X).length
  · have hreq : request D X σ t = blockOf D X ((plan D X)[t.length]) := by
      simp only [request, dif_pos h]
    rw [hreq] at hs
    simp only [dif_pos h]
    rw [blockConfig_local D X _ s s' hs]
  · simp only [dif_neg h]

theorem plan_length : (plan D X).length = (affectedCalls D X).card := by
  simp [plan, List.length_mergeSort, Finset.length_toList]

theorem reply_card' : (Fintype.card (Reply (T := T) (k := k)) : ℝ) ≤
    1 + Real.exp (Real.log (T.S.n k) ^ 8 * sketchLength T k) :=
  sketchReply_card (Real.log (T.S.n k) ^ 8) (sketchLength T k)

/-- Erased-sketch integration and the law/pathwise agreements give the protocol event. -/
theorem deleted_le_protocol (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X) :
    (deletedExperiment D X).pr (retainedFailure D X) ≤
      (FinLaw.bind X.rawLaw (fun _ => seedLaw D X)).pr (fun sseed =>
        ∃ x z, X.allowed x z ∧ X.survives sseed.1 x z ∧
          X.deviates (output D X sseed.2 (replies D X sseed.2 sseed.1 (plan D X).length)) x z) := by
  unfold deletedExperiment
  rw [pr_bind', pr_bind']
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : X.rawLaw.w s = 0
  · simp [hs]
  · apply mul_le_mul_of_nonneg_left _ (X.rawLaw.nonneg s)
    rw [← simHistory_law hD hT hG s hs, pr_map']
    apply pr_mono_support'
    intro σ _ hret
    have hout := output_eq_on_retained hD hG s hs σ hret
    obtain ⟨x, z, hall, hsurv, hdev⟩ := hret.2
    exact ⟨x, z, hall, hsurv, by rw [hout]; exact hdev⟩

/-- The frozen reduction inequality (TeX 18:338–453). -/
theorem reduction' (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hcount : ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 4) :
    X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
      Real.exp (1000 * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℝ) *
        ∑ j : Fin D.geom.r, D.error X.target j) *
      (FinLaw.bind X.rawLaw (fun _ => seedLaw D X)).pr (fun sseed =>
        ∃ x z, X.allowed x z ∧ X.survives sseed.1 x z ∧
          X.deviates (output D X sseed.2 (replies D X sseed.2 sseed.1 (plan D X).length)) x z) :=
  (failure_retained_comparison D hT X hG hsmall hmargin hcount).trans
    (mul_le_mul_of_nonneg_left (deleted_le_protocol hD hT hG) (Real.exp_nonneg _))

/-- The total transfer protocol of TeX 18:420–453. -/
noncomputable def protocol (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hcount : ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 4)
    (hbudget : ((D.geom.r * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
      (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 20)
    (hbroad : ∀ σ t, (output D X σ t).WidthLE (κ.α * T.S.n k / 2)) :
    TransferProtocol X where
  Seed := Seed D
  seedLaw := seedLaw D X
  Reply := Reply (T := T) (k := k)
  defaultReply := none
  reply_card := reply_card'
  steps := (plan D X).length
  steps_bound := by
    rw [plan_length]
    exact affectedCalls_card D X hG hmargin hbudget
  request := request D X
  answer := answer D X
  answer_local := answer_local'
  replies := replies D X
  replies_zero := fun _ _ => rfl
  replies_step := fun _ _ _ => rfl
  calls_bound := fun σ s a => calls_bound' hG hmargin hbudget σ s a
  output := output D X
  output_supported := fun σ s => output_supported (D := D) (X := X) σ _
  broad := fun σ s => hbroad σ _
  reduction := reduction' hD hT hG hsmall hmargin hcount

/-- The output-support field of interface repair 8 for `protocol`. -/
theorem protocol_output_supported (hD : D.Spec) (hT : TransitionData D) (hG : TransferGeometry X)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hcount : ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 4)
    (hbudget : ((D.geom.r * (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
      (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 20)
    (hbroad : ∀ σ t, (output D X σ t).WidthLE (κ.α * T.S.n k / 2)) :
    let P := protocol hD hT hG hsmall hmargin hcount hbudget hbroad
    ∀ seed s, (P.output seed (P.replies seed s P.steps)).SupportedIn (T.Y k) :=
  by
    intro P σ s
    exact output_supported (D := D) (X := X) σ _

end Assembly

end HypercubeRamsey.S18.Lane_opus_s18_2g
