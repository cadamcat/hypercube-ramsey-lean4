import HypercubeRamsey.S18.Defs

/-!
# Section 18 blueprint nodes

Each declaration below corresponds to one Section 18 blueprint node or
sub-node. Proofs of individual nodes are placeholders for the proof lane;
section exports are assembled explicitly from their sub-nodes.
-/

namespace HypercubeRamsey
namespace S18

open Classical Filter
open scoped BigOperators

/-- D18.L (18:43–87): construct the initial-list data, fixed late pools,
current priors, and encoding after the L16.1 quantitative facts are available. -/
theorem D18_L {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (hLarge : LargeIndex κ T k)
    (h16 : ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F) :
    Nonempty (LateData hPT) := by
  sorry

/-- D18.T (18:89–166): package the actual-history gate, the three local
requirements, deletion kernels, and the current bad/alarm events. -/
theorem D18_T {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) :
    Nonempty (TransitionData D) := by
  sorry

/-- D18.G (18:662–676): define the three terminal requirements and their
deterministic local scopes for the initial-input process. -/
theorem D18_G {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) : Nonempty (TerminalRequirements D R) := by
  sorry

/-- D18.C (18:233–264): define the critical-cell transfer experiment with a
total block-response protocol and fixed independent seeds. -/
theorem D18_C {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) : Nonempty (CriticalTransferData D R) := by
  sorry

/-- L18.0a (18:75–87): summable error schedule, including uniform vanishing
after multiplication by the maximum internal dimension. -/
theorem L18_0a {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∃ Kβ : ℝ, 0 < Kβ ∧
      ∀ᶠ k in atTop,
        ∀ PT : ProfiledTiling κ T k, PT.Valid → PT.tiling.mode.isLow →
          ∀ G : LowGeom PT, ScheduleAt κ T k PT G Kβ ∧
            ∀ ε : ℝ, 0 < ε → ∀ i : Fin PT.tiling.m,
              (max 1 (PT.tiling.P i).h : ℝ) *
                (∑ j : Fin G.r, lateError κ T k PT i j.val) < ε := by
  sorry

/-- L18.0b (18:126–134): current-list cap after the gated late hits. -/
theorem L18_0b {κ : CConsts} (hκ : κ.Admissible) {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Kβ : ℝ) (hKβ : 0 < Kβ)
    (hSchedule : ScheduleAt κ T k PT D.geom Kβ)
    (hVanishing : ∀ ε : ℝ, 0 < ε → ∀ i : Fin PT.tiling.m,
      (max 1 (PT.tiling.P i).h : ℝ) *
        (∑ j : Fin D.geom.r, lateError κ T k PT i j.val) < ε) :
    CurrentListCapFacts D R := by
  sorry

/-- L18.1a (18:168–184): concentration of the sketch-conflict requirement. -/
theorem L18_1a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) :
    ∀ j h, R.gate j h →
      (D.encoding.kernels.referenceTransition j h).pr
        (fun out => ¬ R.R1 j h out) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (0.09 : ℝ)) := by
  sorry

/-- L18.1b (18:184–211): broad prefixes and pointwise deletion-kernel
comparison on the gate, with the external and internal batch lengths retained. -/
theorem L18_1b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) :
    ∀ j h, R.gate j h → ∀ out, R.R1 j h out → R.R2 j h out →
      ∀ b : {x : Pos T k // x ∈ D.encoding.base.classes j},
        Real.exp (-((κ.α / 100) * (T.S.n k : ℝ))) ≤ R.prefixMass j b h out ∧
        (D.encoding.kernels.refK j b h).w (out b) ≤
          Real.exp (1000 * R.deletionLength j b *
            lateError κ T k PT (D.geom.patchOf b.1) j.val) *
              (R.deleted j b h).w (out b) := by
  sorry

/-- L18.1c (18:211–229): exponentially small true-hit failure after R1 and R2. -/
theorem L18_1c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) :
    ∀ j h, R.gate j h →
      (D.encoding.kernels.referenceTransition j h).pr
        (fun out => R.R1 j h out ∧ R.R2 j h out ∧ ¬ R.R3 j h out) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (0.09 : ℝ)) := by
  sorry

/-- L18.1 (18:168–229): the local transition conclusions, assembled from its
three separately exposed sub-nodes. -/
theorem L18_1 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (hκ : κ.Admissible)
    (D : LateData hPT) (R : TransitionData D) (Kβ : ℝ) (hKβ : 0 < Kβ)
    (hSchedule : ScheduleAt κ T k PT D.geom Kβ)
    (hVanishing : ∀ ε : ℝ, 0 < ε → ∀ i : Fin PT.tiling.m,
      (max 1 (PT.tiling.P i).h : ℝ) *
        (∑ j : Fin D.geom.r, lateError κ T k PT i j.val) < ε) :
    LocalTransitionFacts D R := by
  exact ⟨D.large_index, L18_0b hκ D R Kβ hKβ hSchedule hVanishing,
    L18_1a D R, L18_1b D R, L18_1c D R⟩

/-- D18.I (18:962–985): fixed initial pair tests, envelope conditions, and
deterministic consultation scopes for one palette. -/
theorem D18_I {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) :
    Nonempty (InitialPairData D) := by
  sorry

/-- L18.2a (18:277–285): critical-label domination and consultation locality. -/
theorem L18_2a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (hLocal : LocalTransitionFacts D R) :
    TransferStepBound D X ⟨0, by decide⟩ := by
  sorry

/-- L18.2b (18:290–325): finite predecessor closure and coset-parity identity. -/
theorem L18_2b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2a : TransferStepBound D X ⟨0, by decide⟩) :
    TransferStepBound D X ⟨1, by decide⟩ := by
  sorry

/-- L18.2c (18:327–336): identify the erased word and its internal-neighbour
support from the parity identity. -/
theorem L18_2c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2b : TransferStepBound D X ⟨1, by decide⟩) :
    TransferStepBound D X ⟨2, by decide⟩ := by
  sorry

/-- L18.2f (18:377–415): one-block locality and the bound on omitted early
inputs at every affected sketch site. -/
theorem L18_2f {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2b : TransferStepBound D X ⟨1, by decide⟩)
    (h2c : TransferStepBound D X ⟨2, by decide⟩) :
    TransferStepBound D X ⟨5, by decide⟩ := by
  sorry

/-- L18.2d (18:338–350): erase the direct roles meeting the designated word
using the deletion kernels, with side-draw factors unchanged. -/
theorem L18_2d {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2c : TransferStepBound D X ⟨2, by decide⟩)
    (h2f : TransferStepBound D X ⟨5, by decide⟩)
    (hLocal : LocalTransitionFacts D R) :
    TransferStepBound D X ⟨3, by decide⟩ := by
  sorry

/-- L18.2e (18:352–375): retain only the envelope event; the erased sketch
factors integrate to one and the failure is contained in this event. -/
theorem L18_2e {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2d : TransferStepBound D X ⟨3, by decide⟩)
    (h2f : TransferStepBound D X ⟨5, by decide⟩) :
    TransferStepBound D X ⟨4, by decide⟩ := by
  sorry

/-- L18.2g (18:420–453): a total bounded-response protocol, with replies
depending only on the requested block and the transcript so far. -/
theorem L18_2g {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2e : TransferStepBound D X ⟨4, by decide⟩)
    (h2f : TransferStepBound D X ⟨5, by decide⟩) :
    TransferStepBound D X ⟨6, by decide⟩ := by
  sorry

/-- L18.2h (18:455–470): each block's complete reply sequence has at most
`exp(n^.4)` possible values. -/
theorem L18_2h {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2f : TransferStepBound D X ⟨5, by decide⟩)
    (h2g : TransferStepBound D X ⟨6, by decide⟩) :
    TransferStepBound D X ⟨7, by decide⟩ := by
  sorry

/-- L18.2i (18:472–490): uniform survival lower bound for single and allowed
nonconflicting pair witnesses. -/
theorem L18_2i {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2a : TransferStepBound D X ⟨0, by decide⟩) :
    TransferStepBound D X ⟨8, by decide⟩ := by
  sorry

/-- L18.2j (18:500–524): transcript-cylinder factorization and the adaptive
block union bound. -/
theorem L18_2j {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2a : TransferStepBound D X ⟨0, by decide⟩)
    (h2g : TransferStepBound D X ⟨6, by decide⟩)
    (h2h : TransferStepBound D X ⟨7, by decide⟩) :
    TransferStepBound D X ⟨9, by decide⟩ := by
  sorry

/-- L18.2k (18:526–571): survival estimate under a transcript cylinder. -/
theorem L18_2k {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2i : TransferStepBound D X ⟨8, by decide⟩)
    (h2j : TransferStepBound D X ⟨9, by decide⟩) :
    TransferStepBound D X ⟨10, by decide⟩ := by
  sorry

/-- L18.2l (18:573–615): likelihood-ratio martingale and stopped second
moment estimate, with the witness independent of the raw blocks. -/
theorem L18_2l {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (h2j : TransferStepBound D X ⟨9, by decide⟩)
    (h2k : TransferStepBound D X ⟨10, by decide⟩) :
    TransferStepBound D X ⟨11, by decide⟩ := by
  sorry

/-- L18.2m (18:617–628): tilted deviation probability, after stopping at the
barrier or an exceptional cylinder. -/
theorem L18_2m {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (ha : TransferStepBound D X ⟨0, by decide⟩)
    (hb : TransferStepBound D X ⟨1, by decide⟩)
    (hc : TransferStepBound D X ⟨2, by decide⟩)
    (hd : TransferStepBound D X ⟨3, by decide⟩)
    (he : TransferStepBound D X ⟨4, by decide⟩)
    (hf : TransferStepBound D X ⟨5, by decide⟩)
    (hg : TransferStepBound D X ⟨6, by decide⟩)
    (hh : TransferStepBound D X ⟨7, by decide⟩)
    (hi : TransferStepBound D X ⟨8, by decide⟩)
    (hj : TransferStepBound D X ⟨9, by decide⟩)
    (hk : TransferStepBound D X ⟨10, by decide⟩)
    (hl : TransferStepBound D X ⟨11, by decide⟩)
    (h16 : L16QuantitativeValidity D.geom D.fresh)
    (hBlock : ∀ C, C ∈ X.criticalCells → X.block C < X.blockCount) :
    TransferBound D X := by
  sorry

/-- L18.2 (18:266–657): late-prefix transfer, assembled from the critical-cell
geometry, erasure, protocol, survival, and stopped-martingale nodes. -/
theorem L18_2 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (X : CriticalTransferData D R)
    (hLocal : LocalTransitionFacts D R) : TransferBound D X := by
  have ha := L18_2a D R X hLocal
  have hb := L18_2b D R X ha
  have hc := L18_2c D R X hb
  have hf := L18_2f D R X hb hc
  have hd := L18_2d D R X hc hf hLocal
  have he := L18_2e D R X hd hf
  have hg := L18_2g D R X he hf
  have hh := L18_2h D R X hf hg
  have hi := L18_2i D R X ha
  have hj := L18_2j D R X ha hg hh
  have hk := L18_2k D R X hi hj
  have hl := L18_2l D R X hj hk
  exact L18_2m D R X ha hb hc hd he hf hg hh hi hj hk hl D.l16_valid X.block_lt

/-- P18.3a (18:678–690): pool-typicality and initial-list failures, including
the one-global-slot-pin bound. -/
theorem P18_3a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R) :
    TerminalStepBound D R Q ⟨0, by decide⟩ := by
  sorry

/-- P18.3b (18:691–714): small expected late-event risk from L18.1a and
L18.1c, followed by the terminal threshold. -/
theorem P18_3b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R)
    (hLocal : LocalTransitionFacts D R) :
    TerminalStepBound D R Q ⟨1, by decide⟩ := by
  sorry

/-- P18.3c (18:715–737): define replay as a total function of pools, tapes,
and a marked execution list; prove agreement by induction on rounds. -/
theorem P18_3c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R)
    {X : CriticalTransferData D R} (hTransfer : TransferBound D X) :
    TerminalStepBound D R Q ⟨2, by decide⟩ := by
  sorry

/-- P18.3d (18:738–751): replay estimate after terminal conditioning and the
permutation-to-iid slot comparison. -/
theorem P18_3d {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R)
    (hc : TerminalStepBound D R Q ⟨2, by decide⟩) :
    TerminalStepBound D R Q ⟨3, by decide⟩ := by
  sorry

/-- P18.3e (18:752–771): leaf decomposition and the uniform-injection swap
coupling, including equal fibre sizes for conditioning on a leaf. -/
theorem P18_3e {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R)
    (hc : TerminalStepBound D R Q ⟨2, by decide⟩)
    (hd : TerminalStepBound D R Q ⟨3, by decide⟩) :
    TerminalStepBound D R Q ⟨4, by decide⟩ := by
  sorry

/-- P18.3f (18:773–798): apply the lopsided local lemma with the charges and
the local comparison, producing a positive terminal event. -/
theorem P18_3f {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (Q : TerminalRequirements D R)
    (hLocal : LocalTransitionFacts D R)
    (h0 : TerminalStepBound D R Q ⟨0, by decide⟩)
    (h1 : TerminalStepBound D R Q ⟨1, by decide⟩)
    (h2 : TerminalStepBound D R Q ⟨2, by decide⟩)
    (h3 : TerminalStepBound D R Q ⟨3, by decide⟩)
    (h4 : TerminalStepBound D R Q ⟨4, by decide⟩) :
    Nonempty (TerminalCertificate D R) := by
  sorry

/-- P18.3 (18:678–799): terminal avoidance and local comparison, assembled
from the six terminal sub-nodes. -/
theorem P18_3 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) {X : CriticalTransferData D R}
    (hLocal : LocalTransitionFacts D R) (hTransfer : TransferBound D X) :
    Nonempty (TerminalCertificate D R) := by
  obtain ⟨Q⟩ := D18_G D R
  have h0 := P18_3a D R Q
  have h1 := P18_3b D R Q hLocal
  have h2 := P18_3c D R Q hTransfer
  have h3 := P18_3d D R Q h2
  have h4 := P18_3e D R Q h2 h3
  exact P18_3f D R Q hLocal h0 h1 h2 h3 h4

/-- P18.4a (18:810–825): balanced mask profiles in the annealed baseline,
chosen independently of all sampled histories. -/
theorem P18_4a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) :
    MaskBalance D := by
  sorry

/-- P18.4b (18:827–861): at one class, use the fixed-history clock sampler
to avoid current bad events and future alarms with factor-two comparison. -/
theorem P18_4b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (hBalance : MaskBalance D) (hLocal : LocalTransitionFacts D R)
    {X : CriticalTransferData D R} (hTransfer : TransferBound D X) :
    Nonempty (ClassSamplerData D R) := by
  sorry

/-- P18.4c (18:863–905): bound column loads on reached histories by backward
integration through the class comparisons and the balanced baseline. -/
theorem P18_4c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : ClassSamplerData D R) (hBalance : MaskBalance D)
    (hLocal : LocalTransitionFacts D R)
    {X : CriticalTransferData D R} (hTransfer : TransferBound D X) :
    ∃ full : D.encoding.base.History (Fin.last D.geom.r) → Prop,
      FullRunProbability D R C A full := by
  sorry

/-- P18.4d (18:904–909): package the chosen class samplers and full-run bound
as the completion certificate. -/
theorem P18_4d {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : ClassSamplerData D R) (full : D.encoding.base.History (Fin.last D.geom.r) → Prop)
    (hfull : FullRunProbability D R C A full) : Nonempty (CompletionCertificate D R C) := by
  exact ⟨⟨A, full, hfull⟩⟩

/-- P18.4 (18:804–909): complete the conditional late assignment with high
probability, preserving the reached-history comparison. -/
theorem P18_4 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (hLocal : LocalTransitionFacts D R) {X : CriticalTransferData D R}
    (hTransfer : TransferBound D X) : Nonempty (CompletionCertificate D R C) := by
  have hBalance := P18_4a D
  obtain ⟨A⟩ := P18_4b D R C hBalance hLocal hTransfer
  obtain ⟨full, hfull⟩ := P18_4c D R C A hBalance hLocal hTransfer
  exact P18_4d D R C A full hfull

/-- P18.5a (18:914–945): pair-law validity, palette size, and bounded partner
counts on a full run. -/
theorem P18_5a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (A : InitialPairData D) : PairInitialFacts D A := by
  sorry

/-- P18.5b (18:993–1025): backward integration of late factors, retaining the
reach indicator and side-data predicates until each sampler comparison. -/
theorem P18_5b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (hPair : PairInitialFacts D A) (hLocal : LocalTransitionFacts D R)
    {X : CriticalTransferData D R} (hTransfer : TransferBound D X) :
    EndpointStepBound D R C A H ⟨0, by decide⟩ := by
  sorry

/-- P18.5c (18:1027–1056): compare terminal-conditioned, resampled, and
fresh-cell expectations in the order required by the local scopes. -/
theorem P18_5c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (h2b : EndpointStepBound D R C A H ⟨0, by decide⟩)
    (hPools : ∀ x ∈ C.terminal, C.requirements.poolGood x)
    (hInitial : ∀ x ∈ C.terminal, C.requirements.initialAvoid x)
    (hLate : ∀ x ∈ C.terminal,
      C.requirements.pLate x ≤ Real.exp (-(T.S.n k : ℝ) ^ (0.01 : ℝ))) :
    EndpointStepBound D R C A H ⟨1, by decide⟩ := by
  sorry

/-- P18.5d (18:1058–1090): isolated-row kernel, including its row-sum and
entry bounds. -/
theorem P18_5d {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (h2c : EndpointStepBound D R C A H ⟨1, by decide⟩) :
    EndpointStepBound D R C A H ⟨2, by decide⟩ := by
  sorry

/-- P18.5e (18:1092–1124): reduce non-isolated rows to finitely many
pair-hit queries with disjoint primitive consultations. -/
theorem P18_5e {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (h2d : EndpointStepBound D R C A H ⟨2, by decide⟩) :
    EndpointStepBound D R C A H ⟨3, by decide⟩ := by
  sorry

/-- P18.5f (18:1126–1168): compare repeated bins and reverse-integrate the
removed variables with their multiplicative losses. -/
theorem P18_5f {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (h2e : EndpointStepBound D R C A H ⟨3, by decide⟩) :
    EndpointStepBound D R C A H ⟨4, by decide⟩ := by
  sorry

/-- P18.5g (18:1170–1220): restore pool restrictions, remove the load
conditioning, and produce the symmetric endpoint kernels. -/
theorem P18_5g {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (hPair : PairInitialFacts D A)
    (h2b : EndpointStepBound D R C A H ⟨0, by decide⟩)
    (h2c : EndpointStepBound D R C A H ⟨1, by decide⟩)
    (h2d : EndpointStepBound D R C A H ⟨2, by decide⟩)
    (h2e : EndpointStepBound D R C A H ⟨3, by decide⟩)
    (h2f : EndpointStepBound D R C A H ⟨4, by decide⟩) :
    Nonempty (EndpointCertificate D R C A H) := by
  sorry

/-- P18.5 (18:947–1221): joint endpoint kernels, assembled from D18.I and
the six comparison and pooling sub-nodes. -/
theorem P18_5 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (H : CompletionCertificate D R C) (hLocal : LocalTransitionFacts D R)
    {X : CriticalTransferData D R} (hTransfer : TransferBound D X) :
    Nonempty (Σ A : InitialPairData D, EndpointCertificate D R C A H) := by
  obtain ⟨A⟩ := D18_I D
  have hPair := P18_5a D A
  have h2b := P18_5b D R C A H hPair hLocal hTransfer
  have h2c := P18_5c D R C A H h2b C.pools C.initial C.late
  have h2d := P18_5d D R C A H h2c
  have h2e := P18_5e D R C A H h2d
  have h2f := P18_5f D R C A H h2e
  exact ⟨⟨A, Classical.choice (P18_5g D R C A H hPair h2b h2c h2d h2e h2f)⟩⟩

/-- L18.6a (18:1223–1248): geometric averaging for a random set of rows up to
the cutoff `t₀`. -/
theorem L18_6a {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H)
    (hFull : FullRunProbability D R C H.samplers H.full)
    (hK : 0 < E.K) (hCprime : 0 < E.Cprime)
    (hPalette : A.palette.Nonempty)
    (hKernel : ∀ v x z, 0 ≤ E.kernel v x z)
    (hRows : ∀ v x, ∑ z, E.kernel v x z ≤ E.K / (A.palette.card : ℝ))
    (hEntries : ∀ v x z,
      E.kernel v x z ≤ (A.palette.card : ℝ)⁻¹ ^ 2 * Real.exp (0.01 * (T.S.n k : ℝ)))
    (hJoint : ∀ assignment : PairAssignment T k,
      (D.encoding.experiment C.terminal C.positive H.samplers.act
        (pairSampler := A.pairSampler)).pr
        (fun out => H.full out.1.2 ∧ ∀ v ∈ A.rows, out.2 v = assignment v) ≤
        Real.exp (2 * (D.geom.r : ℝ)) * E.K ^ A.rows.card *
          Real.exp (0.01 * (T.S.n k : ℝ) * A.nonisolates +
            E.Cprime * A.rows.card * A.rank) *
          ∏ v ∈ A.rows, E.kernel v (assignment v).1 (assignment v).2) :
    HallStepBound D R C A H E ⟨0, by decide⟩ := by
  sorry

/-- L18.6b (18:1249–1276): tree-diagram counts and the two additional mergers
required by a connected Hall obstruction, retaining distinct endpoints. -/
theorem L18_6b {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H)
    (h6a : HallStepBound D R C A H E ⟨0, by decide⟩) :
    HallStepBound D R C A H E ⟨1, by decide⟩ := by
  sorry

/-- L18.6c (18:1277–1300): sum the large connected sets and small Hall
obstructions over all patches and palettes. -/
theorem L18_6c {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H)
    (h6a : HallStepBound D R C A H E ⟨0, by decide⟩)
    (h6b : HallStepBound D R C A H E ⟨1, by decide⟩) :
    HallStepBound D R C A H E ⟨2, by decide⟩ := by
  sorry

/-- L18.6d (18:1301–1311): absence of the enumerated obstructions implies a
Hall matching in every palette. -/
theorem L18_6d {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H)
    (h6a : HallStepBound D R C A H E ⟨0, by decide⟩)
    (h6b : HallStepBound D R C A H E ⟨1, by decide⟩)
    (h6c : HallStepBound D R C A H E ⟨2, by decide⟩) :
    Nonempty (HallCertificate D) := by
  sorry

/-- L18.6 (18:1223–1311): two-endpoint Hall estimate assembled from the
geometric, tree-counting, and obstruction-sum sub-nodes. -/
theorem L18_6 {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (R : TransitionData D) (C : TerminalCertificate D R)
    (A : InitialPairData D) (H : CompletionCertificate D R C)
    (E : EndpointCertificate D R C A H) : Nonempty (HallCertificate D) := by
  have h6a := L18_6a D R C A H E H.fullRun E.K_pos E.Cprime_pos
    E.palette_nonempty E.kernel_nonneg E.row_sum E.entry_bound E.jointBound
  have h6b := L18_6b D R C A H E h6a
  have h6c := L18_6c D R C A H E h6a h6b
  exact L18_6d D R C A H E h6a h6b h6c

/-- C18.Fcube (18:1313–1322): convert the injective endpoint selection into
the cross-cube copy using the framework embedding theorem. -/
theorem C18_Fcube {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (H : HallCertificate D) : CubeIn T k PT.tiling.c := by
  exact cube_copy_of_parts H.assignment.evenLabel H.assignment.oddLabel
    H.assignment.even_injective H.assignment.odd_injective H.assignment.edge

/-- Assemble the low-mode experiment at one valid profile. -/
theorem lowmode_cube_at {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (hLarge : LargeIndex κ T k)
    (h16 : ∃ G : LowGeom PT, ∃ F : FreshCell G, L16QuantitativeValidity G F)
    (Kβ : ℝ) (hKβ : 0 < Kβ) (hSchedule : ∀ G : LowGeom PT,
      ScheduleAt κ T k PT G Kβ ∧
        ∀ ε : ℝ, 0 < ε → ∀ i : Fin PT.tiling.m,
          (max 1 (PT.tiling.P i).h : ℝ) *
            (∑ j : Fin G.r, lateError κ T k PT i j.val) < ε) :
    CubeIn T k PT.tiling.c := by
  obtain ⟨D⟩ := D18_L hκ T k hPT hLow hLarge h16
  obtain ⟨R⟩ := D18_T D
  have hLocal := L18_1 hκ D R Kβ hKβ (hSchedule D.geom).1 (hSchedule D.geom).2
  obtain ⟨X⟩ := D18_C D R
  have hTransfer := L18_2 D R X hLocal
  obtain ⟨C⟩ := P18_3 D R hLocal hTransfer
  obtain ⟨H⟩ := P18_4 D R C hLocal hTransfer
  obtain ⟨⟨A, E⟩⟩ := P18_5 D R C H hLocal hTransfer
  obtain ⟨Hall⟩ := L18_6 D R C A H E
  exact C18_Fcube D Hall

/-- C18.Flow (18:1301–1310): every valid bounded or low profile yields a
monochromatic cross-cube, assembled from terminal avoidance, late completion,
endpoint kernels, the two-endpoint Hall estimate, and the embedding lemma. -/
theorem C18_Flow {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode.isLow → CubeIn T k PT.tiling.c := by
  have h16 := l16_quantitative_validity hκ T hInit hDeep
  obtain ⟨Kβ, hKβ, hSchedule⟩ := L18_0a hκ T
  have hLarge := eventually_largeIndex κ T
  filter_upwards [h16, hSchedule, hLarge] with k hk16 hkSchedule hkLarge
  intro PT hPT hLow
  rcases hk16 PT hPT hLow with ⟨G, F, h16valid⟩
  exact lowmode_cube_at hκ T k hPT hLow hkLarge ⟨G, F, h16valid⟩ Kβ hKβ
    (fun G => hkSchedule PT hPT hLow G)
