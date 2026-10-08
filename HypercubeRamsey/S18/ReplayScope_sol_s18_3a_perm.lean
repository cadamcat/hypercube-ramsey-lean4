import HypercubeRamsey.S18.PermutationReplay_sol_s18_3a_perm
import HypercubeRamsey.S18.Nodes_sol_s18_4b

namespace HypercubeRamsey.Lane_sol_s18_3a_perm
open Classical
open scoped BigOperators
open Lane_sol_s18_4b (continuation continuation_step continuation_last)

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

/-- Initial direct-cell agreement and processed-row agreement in one ball. -/
def LocalHistoryAgree (q : Fin (D.geom.r + 1)) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History q) : Prop :=
  (∀ w ∈ cubeBall v R, ∀ C ∈ D.directCells w, h.1 C = h'.1 C) ∧
  ∀ b : D.encoding.base.ProcessedRole q, _root_.hammingDist v b.1 ≤ R → h.2 b = h'.2 b

private theorem flip_distance (v : Pos T k) (a : Fin (T.S.n k)) :
    _root_.hammingDist v (flipPos v a) = 1 := by
  have heq : (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j) = {a} := by
    ext j
    by_cases hj : j = a
    · subst j; cases hv : v a <;> simp [flipPos, hv]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [show flipPos v a j = v j from Function.update_of_ne hj _ _]
      simp [hj]
  change (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j).card = 1
  rw [heq, Finset.card_singleton]

private theorem localHistory_mono {q : Fin (D.geom.r + 1)} {v : Pos T k}
    {R R' : ℕ} {h h' : D.encoding.base.History q}
    (ha : LocalHistoryAgree D q v R h h') (hR : R' ≤ R) :
    LocalHistoryAgree D q v R' h h' := by
  refine ⟨?_, fun b hb => ha.2 b (hb.trans hR)⟩
  intro w hw
  apply ha.1 w
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.trans hR⟩

private theorem localHistory_extend (j : Fin D.geom.r) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History j.castSucc) (out out' : D.encoding.base.ClassRows j)
    (ha : LocalHistoryAgree D j.castSucc v R h h')
    (ho : ∀ b, _root_.hammingDist v b.1 ≤ R → out b = out' b) :
    LocalHistoryAgree D j.succ v R (D.encoding.base.extend j h out)
      (D.encoding.base.extend j h' out') := by
  refine ⟨ha.1, ?_⟩
  intro b hb
  dsimp [LateProcessBase.extend]
  split_ifs with hmem
  · exact ha.2 ⟨b.1, hmem⟩ hb
  · exact ho _ hb

private theorem localHistory_before {q : Fin (D.geom.r + 1)}
    (i : Fin (D.geom.r + 1)) (hi : i.val ≤ q.val) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History q) (ha : LocalHistoryAgree D q v R h h') :
    LocalHistoryAgree D i v R (D.beforeHistory h i hi) (D.beforeHistory h' i hi) :=
  ⟨ha.1, fun b hb => ha.2 ⟨b.1, D.processed_mono i q hi b.2⟩ hb⟩

private theorem rowOut_nonempty (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    Nonempty (D.encoding.base.RowOut b.1) := by
  by_contra hn
  haveI := not_nonempty_iff.mp hn
  have hs := (D.encoding.kernels.refK j b h).sum_one
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
  norm_num at hs

private theorem localPriorAt (hD : D.Spec) (q : Fin (D.geom.r + 1))
    (v w : Pos T k) (R : ℕ) (h h' : D.encoding.base.History q)
    (ha : LocalHistoryAgree D q v R h h') (hw : _root_.hammingDist v w + 1 ≤ R) :
    D.priorAt q w h = D.priorAt q w h' := by
  apply Lane_sol_s18_n4.priorAt_local D hD
  · exact ha.1 w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  · intro b hb
    apply congrArg D.encoding.base.rowLabel
    apply ha.2
    have ht := _root_.hammingDist_triangle v w b.1
    change _root_.hammingDist w b.1 = 1 at hb
    omega

private theorem localRowKernel (hD : D.Spec) (H : S18.TransitionData D)
    (j : Fin D.geom.r) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History j.castSucc)
    (ha : LocalHistoryAgree D j.castSucc v (R + 2) h h')
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (hb : _root_.hammingDist v b.1 ≤ R) :
    D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h' := by
  apply Lane_sol_s18_n4.referenceRow_local D H
  intro a
  apply localPriorAt D hD j.castSucc v (flipPos b.1 a) (R + 2) h h' ha
  have ht := _root_.hammingDist_triangle v b.1 (flipPos b.1 a)
  have hf := flip_distance b.1 a
  omega

/-- Each remaining class enlarges the initial-cell and row scopes by two. -/
theorem continuation_directCell_local (hD : D.Spec) (H : S18.TransitionData D)
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (v : Pos T k) (R : ℕ)
    (hg : ∀ h h', LocalHistoryAgree D (Fin.last D.geom.r) v R h h' → g h = g h')
    (q : Fin (D.geom.r + 1)) (h h' : D.encoding.base.History q)
    (ha : LocalHistoryAgree D q v (R + 2 * (D.geom.r - q.val)) h h') :
    continuation D g q h = continuation D g q h' := by
  by_cases hq : q.val < D.geom.r
  · let j : Fin D.geom.r := ⟨q.val, hq⟩
    change continuation D g j.castSucc h = continuation D g j.castSucc h'
    let R' := R + 2 * (D.geom.r - j.succ.val)
    have hR : R + 2 * (D.geom.r - j.val) = R' + 2 := by dsimp [R']; omega
    have ha' : LocalHistoryAgree D j.castSucc v (R' + 2) h h' := by
      change LocalHistoryAgree D j.castSucc v (R + 2 * (D.geom.r - j.val)) h h' at ha
      rwa [hR] at ha
    let S := Finset.univ.filter fun b : {v : Pos T k // v ∈ D.encoding.base.classes j} =>
      _root_.hammingDist v b.1 ≤ R'
    let f := fun out => continuation D g j.succ (D.encoding.base.extend j h out)
    have hf : ∀ out out', (∀ b ∈ S, out b = out' b) → f out = f out' := by
      intro out out' ho
      apply continuation_directCell_local hD H g v R hg
      apply localHistory_extend
      · exact ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩
      · intro b hb
        exact ho b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    have hfun : f = fun out => continuation D g j.succ (D.encoding.base.extend j h' out) := by
      funext out
      apply continuation_directCell_local hD H g v R hg
      apply localHistory_extend
      · exact localHistory_mono D ha' (by omega)
      · intro _ _; rfl
    letI : ∀ b : {v : Pos T k // v ∈ D.encoding.base.classes j},
        Nonempty (D.encoding.base.RowOut b.1) := rowOut_nonempty D j h
    rw [continuation_step, continuation_step]
    change (FinLaw.pi (fun b => D.encoding.kernels.refK j b h)).E f = _
    rw [S18.Lane_sol_s18_n5.pi_E_local
      (fun b => D.encoding.kernels.refK j b h)
      (fun b => D.encoding.kernels.refK j b h') S f hf
      (fun b hb => localRowKernel D hD H j v R' h h' ha' b (Finset.mem_filter.mp hb).2), hfun]
    rfl
  · have hql : q = Fin.last D.geom.r := Fin.ext (by simp; omega)
    subst q
    rw [continuation_last, continuation_last]
    apply hg
    simpa [LocalHistoryAgree] using ha
termination_by D.geom.r - q.val

private theorem localR3 (hD : D.Spec) (j : Fin D.geom.r) (v b : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History j.castSucc)
    (ha : LocalHistoryAgree D j.castSucc v R h h') (hb : _root_.hammingDist v b + 2 ≤ R)
    (out : D.encoding.base.RowOut b) : D.R3 j h out ↔ D.R3 j h' out := by
  have hp : ∀ a, D.currentPrior j (flipPos b a) h = D.currentPrior j (flipPos b a) h' := by
    intro a
    apply localPriorAt D hD j.castSucc v (flipPos b a) R h h' ha
    have ht := _root_.hammingDist_triangle v b (flipPos b a)
    have hf := flip_distance b a
    omega
  simp only [S18.LateData.R3, hp]

private theorem localGate (hD : D.Spec) (j : Fin D.geom.r) (b : Pos T k)
    (h h' : D.encoding.base.History j.castSucc)
    (ha : LocalHistoryAgree D j.castSucc b (6 * D.geom.r + 2) h h') :
    D.gate j b h ↔ D.gate j b h' := by
  have hrows : ∀ (s : Fin D.geom.r) (hs : s.val < j.val)
      (c : {x : Pos T k // x ∈ D.encoding.base.classes s}),
      c.1 ∈ cubeBall b (6 * D.geom.r) → D.pastRows h s hs c = D.pastRows h' s hs c := by
    intro s hs c hc
    apply ha.2 ⟨c.1, D.class_before s j.castSucc hs c.2⟩
    change _root_.hammingDist b c.1 ≤ 6 * D.geom.r + 2
    have hd := (Finset.mem_filter.mp hc).2
    omega
  have hR3 : ∀ (s : Fin D.geom.r) (hs : s.val < j.val)
      (c : {x : Pos T k // x ∈ D.encoding.base.classes s}),
      c.1 ∈ cubeBall b (6 * D.geom.r) →
      (D.R3 s (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)) (D.pastRows h s hs c) ↔
        D.R3 s (D.beforeHistory h' s.castSucc (Nat.le_of_lt hs)) (D.pastRows h' s hs c)) := by
    intro s hs c hc
    rw [hrows s hs c hc]
    apply localR3 D hD s b c.1 (6 * D.geom.r + 2)
    · exact localHistory_before D (q := j.castSucc) s.castSucc (Nat.le_of_lt hs) b _ h h' ha
    · have hd := (Finset.mem_filter.mp hc).2
      omega
  have hvalid : ∀ w ∈ cubeBall b (6 * D.geom.r), D.initialValid w h.1 ↔ D.initialValid w h'.1 := by
    intro w hw
    apply S18.Lane_sol_s18_n5.initialValid_local D hD
    apply ha.1 w
    have hd := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hinit : (∀ w ∈ cubeBall b (6 * D.geom.r), IsEvenRole w → D.initialValid w h.1) ↔
      (∀ w ∈ cubeBall b (6 * D.geom.r), IsEvenRole w → D.initialValid w h'.1) := by
    apply forall_congr'; intro w
    apply imp_congr_right; intro hw
    apply imp_congr_right; intro _
    exact hvalid w hw
  unfold S18.LateData.gate
  apply and_congr hinit
  apply forall_congr'; intro s
  apply forall_congr'; intro hs
  apply forall_congr'; intro c
  apply imp_congr_right; intro hc
  exact and_congr (hR3 s hs c hc) (by rw [hrows s hs c hc])

theorem prefixFailure_directCell_local (hD : D.Spec) (F : S18.PrefixIndex D)
    (h h' : D.encoding.base.History (Fin.last D.geom.r))
    (ha : LocalHistoryAgree D (Fin.last D.geom.r) F.2.1.1 (6 * D.geom.r + 2) h h') :
    D.prefixFailure F h ↔ D.prefixFailure F h' := by
  let before := D.beforeHistory h F.1.castSucc (Nat.le_of_lt F.1.isLt)
  let before' := D.beforeHistory h' F.1.castSucc (Nat.le_of_lt F.1.isLt)
  have hab : LocalHistoryAgree D F.1.castSucc F.2.1.1 (6 * D.geom.r + 2) before before' :=
    localHistory_before D _ _ _ _ h h' ha
  have hout : D.pastRows h F.1 F.1.isLt F.2.1 = D.pastRows h' F.1 F.1.isLt F.2.1 := by
    apply ha.2
    simp [_root_.hammingDist]
  have hgate := localGate D hD F.1 F.2.1.1 before before' hab
  have hp : D.initialPrior (flipPos F.2.1.1 F.2.2.2.2) h.1 =
      D.initialPrior (flipPos F.2.1.1 F.2.2.2.2) h'.1 := by
    apply Lane_sol_s18_n4.initialPrior_local D hD
    apply ha.1
    have hf := flip_distance F.2.1.1 F.2.2.2.2
    have hr := D.l16_valid.r_pos
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  simp only [S18.LateData.prefixFailure, hout]
  change (_ ∧ D.gate F.1 F.2.1.1 before ∧ _) ↔ (_ ∧ D.gate F.1 F.2.1.1 before' ∧ _)
  simp only [hgate, S18.LateData.prefixMoments, S18.LateData.beforeHistory, hp]

/-- The reference prefix risk consults only the deterministic 10r seed. -/
theorem referencePrefixRisk_local (hD : D.Spec) (H : S18.TransitionData D)
    (F : S18.PrefixIndex D) (s s' : Config D.fresh)
    (hs : ∀ C ∈ (cubeBall F.2.1.1 (10 * D.geom.r)).biUnion D.directCells, s C = s' C) :
    (D.encoding.kernels.refRun s).pr (D.prefixFailure F) =
      (D.encoding.kernels.refRun s').pr (D.prefixFailure F) := by
  let g := fun full : D.encoding.base.History (Fin.last D.geom.r) =>
    if D.prefixFailure F full then (1 : ℝ) else 0
  have hE (s : Config D.fresh) : (D.encoding.kernels.refRun s).pr (D.prefixFailure F) =
      continuation D g 0 (D.encoding.base.initialHistory s) := by
    have heq : (D.encoding.kernels.refRun s).pr (D.prefixFailure F) =
        (D.encoding.kernels.refRun s).E g := by
      simp only [FinLaw.pr, FinLaw.E, g, mul_ite, mul_one, mul_zero]
    rw [heq, Lane_sol_s18_4b.continuation_disintegration D g s 0]
    simp only [Fin.val_zero, LateProcessBase.runFrom, FinLaw.E, FinLaw.dirac, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    erw [Finset.sum_eq_single (D.encoding.base.initialHistory s)]
    · simp
    · intro h _ hne
      simp [hne]
    · simp
  rw [hE s, hE s']
  apply continuation_directCell_local D hD H g F.2.1.1 (6 * D.geom.r + 2)
  · intro h h' ha
    simp only [g, prefixFailure_directCell_local D hD F h h' ha]
  · refine ⟨?_, ?_⟩
    · intro w hw C hC
      apply hs C
      apply Finset.mem_biUnion.mpr
      refine ⟨w, ?_, hC⟩
      have hd := (Finset.mem_filter.mp hw).2
      have hr := D.l16_valid.r_pos
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp at hd; omega⟩
    · intro b _
      have hb := b.2
      have hb' : b.1 ∈ (∅ : Finset (Pos T k)) := by
        simpa only [D.encoding.base.processed_zero] using hb
      exact False.elim (by simpa using hb')

private theorem graph_seed (A : Finset (Pos T k)) (r : ℕ) :
    A ⊆ D.encoding.events.graphBall A r := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact fun _ hv => Finset.mem_union.mpr (Or.inl (ih hv))

private theorem graph_radius (A : Finset (Pos T k)) {r s : ℕ} (hrs : r ≤ s) :
    D.encoding.events.graphBall A r ⊆ D.encoding.events.graphBall A s := by
  induction s with
  | zero =>
    have hr : r = 0 := by omega
    subst r
    exact Finset.Subset.refl _
  | succ s ih =>
    by_cases heq : r = s + 1
    · subst r; exact Finset.Subset.refl _
    · exact fun _ hv => Finset.mem_union.mpr (Or.inl (ih (by omega) hv))

private theorem graph_add (A B : Finset (Pos T k)) (m : ℕ)
    (hA : A ⊆ D.encoding.events.graphBall B m) (r : ℕ) :
    D.encoding.events.graphBall A r ⊆ D.encoding.events.graphBall B (m + r) := by
  induction r with
  | zero => simpa only [ListEvent.graphBall, Nat.add_zero] using hA
  | succ r ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact graph_radius D B (by omega) (ih hv)
    · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
      have hmem : v ∈ D.encoding.events.graphBall B (m + r + 1) :=
        Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ih hu, hadj⟩))
      simpa only [Nat.add_assoc] using hmem

noncomputable def replayCells (seed : Finset D.geom.Cell) (t : ℕ) : Finset D.geom.Cell :=
  seed ∪ (D.encoding.events.graphBall (seed.biUnion D.encoding.events.incidentEvents)
    (2 * t + 1)).biUnion D.encoding.events.scope

private theorem replayCells_step (seed : Finset D.geom.Cell) (t : ℕ) :
    replayCells D (replayCells D seed 0) t ⊆ replayCells D seed (t + 1) := by
  let B := seed.biUnion D.encoding.events.incidentEvents
  have hinc : (replayCells D seed 0).biUnion D.encoding.events.incidentEvents ⊆
      D.encoding.events.graphBall B 2 := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    have hCv := (Finset.mem_filter.mp hvC).2
    rcases Finset.mem_union.mp hC with hC | hC
    · apply graph_seed D B 2
      exact Finset.mem_biUnion.mpr ⟨C, hC, hvC⟩
    · obtain ⟨w, hw, hCw⟩ := Finset.mem_biUnion.mp hC
      by_cases heq : v = w
      · subst v
        exact graph_radius D B (by omega) hw
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, w, hw, heq, ?_⟩
        exact Finset.not_disjoint_iff.mpr ⟨C, hCv, hCw⟩
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact Finset.mem_union.mpr (Or.inl hC)
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨v, graph_radius D B (by omega) hv, hCv⟩))
  · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨v, ?_, hCv⟩
    have hb := graph_add D _ B 2 hinc (2 * t + 1) hv
    simpa only [show 2 + (2 * t + 1) = 2 * (t + 1) + 1 by omega] using hb

/-- A total forced replay has the same deterministic finite propagation
scope as a priority run; forcing a marked site does not read a new input. -/
theorem replay_directCell_local (marked : Finset (Pos T k))
    (pattern : ℕ → Finset (Pos T k)) (t : ℕ) (seed : Finset D.geom.Cell)
    (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ replayCells D seed t, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    ∀ C ∈ seed,
      (S18.replayRounds D marked pattern x t).1 C =
        (S18.replayRounds D marked pattern x' t).1 C ∧
      (S18.replayRounds D marked pattern x t).2 C =
        (S18.replayRounds D marked pattern x' t).2 C := by
  induction t generalizing seed with
  | zero =>
    intro C hC
    obtain ⟨hp, ht⟩ := hx C (Finset.mem_union.mpr (Or.inl hC))
    simp only [S18.replayRounds, Tapes.extend, hp, ht, and_self]
  | succ t ih =>
    let seed' := replayCells D seed 0
    have hprev := ih seed' (fun C hC => hx C (replayCells_step D seed t hC))
    let E := D.encoding.events
    let prev := S18.replayRounds D marked pattern x t
    let prev' := S18.replayRounds D marked pattern x' t
    have hactive (C : D.geom.Cell) (hC : C ∈ seed) (v : Pos T k) (hCv : C ∈ E.scope v) :
        v ∈ E.active D.encoding.order Finset.univ prev.1 ↔
          v ∈ E.active D.encoding.order Finset.univ prev'.1 := by
      have hv : v ∈ seed.biUnion E.incidentEvents := Finset.mem_biUnion.mpr
        ⟨C, hC, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv⟩⟩
      have hs (w : Pos T k) (hw : w ∈ E.graphBall (seed.biUnion E.incidentEvents) 1) :
          E.S w prev.1 ↔ E.S w prev'.1 := by
        apply E.scope_ok
        intro C hC
        exact (hprev C (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨w, hw, hC⟩)))).1
      have htruth := hs v (graph_seed D _ 1 hv)
      have hn (u : Pos T k) (hadj : E.Adjacent u v) : E.S u prev.1 ↔ E.S u prev'.1 := by
        apply hs u
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hadj⟩))
      simp only [ListEvent.active, Finset.mem_filter, Finset.mem_univ, true_and, true_implies]
      constructor
      · intro ha
        refine ⟨htruth.mp ha.1, ?_⟩
        intro u hbefore hadj
        exact (hn u hadj).not.mp (ha.2 u hbefore hadj)
      · intro ha
        refine ⟨htruth.mpr ha.1, ?_⟩
        intro u hbefore hadj
        exact (hn u hadj).not.mpr (ha.2 u hbefore hadj)
    intro C hC
    have hi := hprev C (Finset.mem_union.mpr (Or.inl hC))
    have hp := hx C (Finset.mem_union.mpr (Or.inl hC))
    have htouch : (∃ v ∈ (pattern t ∩ marked) ∪
        (E.active D.encoding.order Finset.univ prev.1 \ marked), C ∈ E.scope v) ↔
        (∃ v ∈ (pattern t ∩ marked) ∪
          (E.active D.encoding.order Finset.univ prev'.1 \ marked), C ∈ E.scope v) := by
      constructor
      · rintro ⟨v, hv, hCv⟩
        refine ⟨v, ?_, hCv⟩
        simpa only [Finset.mem_union, Finset.mem_sdiff, hactive C hC v hCv] using hv
      · rintro ⟨v, hv, hCv⟩
        refine ⟨v, ?_, hCv⟩
        simpa only [Finset.mem_union, Finset.mem_sdiff, hactive C hC v hCv] using hv
    let touches : Prop := ∃ v ∈ (pattern t ∩ marked) ∪
      (E.active D.encoding.order Finset.univ prev.1 \ marked), C ∈ E.scope v
    let touches' : Prop := ∃ v ∈ (pattern t ∩ marked) ∪
      (E.active D.encoding.order Finset.univ prev'.1 \ marked), C ∈ E.scope v
    have ht : touches ↔ touches' := htouch
    have hs : prev.1 C = prev'.1 C := hi.1
    have hc : prev.2 C = prev'.2 C := hi.2
    simp only [S18.replayRounds]
    change (if touches then x.2.extend C (prev.2 C + 1) (x.1 C) else prev.1 C) =
        (if touches' then x'.2.extend C (prev'.2 C + 1) (x'.1 C) else prev'.1 C) ∧
      (if touches then prev.2 C + 1 else prev.2 C) = (if touches' then prev'.2 C + 1 else prev'.2 C)
    by_cases h : touches
    · have h' := ht.mp h
      simp only [if_pos h, if_pos h', hc, hp.1]
      simp only [Tapes.extend, hp.2, and_self]
    · have h' := ht.not.mp h
      simp only [if_neg h, if_neg h', hs, hc, and_self]

theorem forcedReplayRisk_local (hD : D.Spec) (H : S18.TransitionData D)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (critical : Finset D.geom.Cell)
    (pattern : ℕ → Finset (Pos T k)) (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    Lane_sol_s18_n4.forcedReplayRisk D critical pattern F x =
      Lane_sol_s18_n4.forcedReplayRisk D critical pattern F x' := by
  unfold Lane_sol_s18_n4.forcedReplayRisk
  rw [Lane_sol_s18_n4.prefixLateFailure_eq D F hkind]
  let seed := (cubeBall F.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells
  have hinput : ∀ C ∈ replayCells D seed D.encoding.Ts, x.1 C = x'.1 C ∧ x.2 C = x'.2 C := by
    intro C hC
    apply hx C
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Finset.mem_union.mpr (Or.inl hC)
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨v, graph_radius D _ (by omega) hv, hCv⟩))
  apply referencePrefixRisk_local D hD H F.2
  intro C hC
  exact (replay_directCell_local D (S18.replayMarked D critical) pattern D.encoding.Ts
    seed x x' hinput C hC).1

/-- After integrating the independent tapes, the enlarged replay test reads
only whole pools in `lateRegion`, including its critical typicality gate. -/
theorem replayPoolTest_local (hD : D.Spec) (H : S18.TransitionData D)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (omitted : Option D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (P Q : ∀ C, D.fresh.Pool C) (hp : ∀ C ∈ D.lateRegion F, P C = Q C) :
    let X : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
    (tapeLaw D.fresh D.encoding.Ts).E (fun tapes =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (P C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (P, tapes) else 0) =
    (tapeLaw D.fresh D.encoding.Ts).E (fun tapes =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (Q C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (Q, tapes) else 0) := by
  classical
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  have htyp : (∀ C ∈ X.criticalCells, D.fresh.typical C (P C)) ↔
      ∀ C ∈ X.criticalCells, D.fresh.typical C (Q C) := by
    apply forall_congr'; intro C
    apply imp_congr_right; intro hC
    rw [hp C (Lane_sol_s18_n4.criticalCells_in_lateRegion D F hvalid omitted _ hC)]
  apply congrArg (tapeLaw D.fresh D.encoding.Ts).E
  funext tapes
  change (if ∀ C ∈ X.criticalCells, D.fresh.typical C (P C) then
    Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (P, tapes) else 0) =
      (if ∀ C ∈ X.criticalCells, D.fresh.typical C (Q C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (Q, tapes) else 0)
  simp only [htyp]
  split_ifs
  · exact forcedReplayRisk_local D hD H F hkind X.criticalCells pattern (P, tapes) (Q, tapes)
      (fun C hC => ⟨hp C hC, rfl⟩)
  · rfl

end HypercubeRamsey.Lane_sol_s18_3a_perm
