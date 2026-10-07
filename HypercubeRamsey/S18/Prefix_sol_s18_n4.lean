import HypercubeRamsey.S18.Risk_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid}

private theorem bindPrExpectation {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : α → FinLaw β) (A : β → Prop) :
    (FinLaw.bind P Q).pr (fun x => A x.2) = P.E (fun a => (Q a).pr A) := by
  simp only [FinLaw.pr, FinLaw.E, FinLaw.bind, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero]

theorem prefixLateFailure_eq (D : S18.LateData hPT) (F : S18.LateEvent D)
    (hkind : F.1.val = 1) : S18.lateFailure D F = D.prefixFailure F.2 := by
  funext h
  apply propext
  simp only [S18.lateFailure, hkind, one_ne_zero, if_false, if_true,
    S18.LateData.prefixFailure]
  tauto

theorem replayState_entry (D : S18.LateData hPT) (marked : Finset (Pos T k))
    (pattern : ℕ → Finset (Pos T k)) (x : D.encoding.InitInput) (t : ℕ)
    (C : D.geom.Cell) :
    (S18.replayRounds D marked pattern x t).1 C =
      x.2.extend C ((S18.replayRounds D marked pattern x t).2 C) (x.1 C) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [S18.replayRounds]
    split_ifs <;> simp_all

theorem replayCounter_le (D : S18.LateData hPT) (marked : Finset (Pos T k))
    (pattern : ℕ → Finset (Pos T k)) (x : D.encoding.InitInput) (t : ℕ)
    (C : D.geom.Cell) : (S18.replayRounds D marked pattern x t).2 C ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [S18.replayRounds]
    split_ifs <;> omega

/-- Replacing all entries in a critical cell by one state produces a total
replay input, with the original pools and tapes elsewhere. -/
noncomputable def criticalReplayInput (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) (outside : D.encoding.InitInput)
    (raw : ∀ C, D.fresh.Pool C × D.fresh.State C) : D.encoding.InitInput :=
  (fun C => if C ∈ critical then (raw C).1 else outside.1 C,
    fun C => if C ∈ critical then fun _ _ => (raw C).2 else outside.2 C)

theorem criticalReplayState (D : S18.LateData hPT) (hReplay : S18.ReplayFacts D)
    (critical : Finset D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (outside : D.encoding.InitInput) (raw : ∀ C, D.fresh.Pool C × D.fresh.State C)
    (t : ℕ) (C : D.geom.Cell) :
    (S18.replayRounds D (S18.replayMarked D critical) pattern
      (criticalReplayInput D critical outside raw) t).1 C =
      if C ∈ critical then (raw C).2 else
        (S18.replayRounds D (S18.replayMarked D critical) pattern outside t).1 C := by
  by_cases hC : C ∈ critical
  · rw [if_pos hC, replayState_entry]
    simp [criticalReplayInput, Tapes.extend, hC]
  · rw [if_neg hC]
    exact (hReplay.2.1 critical pattern (criticalReplayInput D critical outside raw)
      outside t (fun C hC => by simp [criticalReplayInput, hC]) C hC).1

/-- The omitted cell, including a pinned pool cell, is left among the fixed
outside inputs of the transfer experiment. -/
theorem omitted_not_critical (D : S18.LateData hPT) (X : S18.CriticalTransferData D)
    (C : D.geom.Cell) (hC : X.omitted = some C) : C ∉ X.criticalCells := by
  intro hm
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
  have hnot := (Finset.mem_filter.mp ha).2.2
  exact hnot (by simpa [heq] using hC)

/-- Target cells contain a common cell of every marked site and its touching
neighbor. Each marked execution is therefore itself a closure seed. -/
noncomputable def replayTargets (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) : Finset D.geom.Cell :=
  (critical.biUnion D.encoding.events.incidentEvents).biUnion D.encoding.events.scope

theorem markedSite_touches_target (D : S18.LateData hPT) (hD : D.Spec)
    (critical : Finset D.geom.Cell) (v : Pos T k)
    (hv : v ∈ S18.replayMarked D critical) :
    ∃ C ∈ replayTargets D critical, C ∈ D.encoding.events.scope v := by
  rcases Finset.mem_union.mp hv with ht | ht
  · refine ⟨D.geom.cellOf v, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨v, ht, ?_⟩
      rw [hD.scope_eq]
      simp [S18.LateData.directCells]
    · rw [hD.scope_eq]
      simp [S18.LateData.directCells]
  · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp ht).2
    obtain ⟨C, hCv, hCu⟩ := Finset.not_disjoint_iff.mp hadj.2
    exact ⟨C, Finset.mem_biUnion.mpr ⟨u, hu, hCu⟩, hCv⟩

noncomputable def markedOccurrences (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) (x : D.encoding.InitInput) :
    Finset (Pos T k × Fin D.encoding.Ts) :=
  Finset.univ.filter fun o => o.1 ∈ S18.actualPattern D (S18.replayMarked D critical) x o.2

noncomputable def replayBackwardClosure (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) (x : D.encoding.InitInput) :
    Finset (Pos T k × Fin D.encoding.Ts) :=
  let executed := fun o : Pos T k × Fin D.encoding.Ts =>
    o.1 ∈ D.encoding.events.active D.encoding.order Finset.univ
      (D.encoding.events.runRounds o.2.val D.encoding.order Finset.univ x.1 x.2.extend).1
  let edge := fun later earlier : Pos T k × Fin D.encoding.Ts =>
    executed later ∧ executed earlier ∧ earlier.2.val < later.2.val ∧
      ¬ Disjoint (D.encoding.events.scope later.1) (D.encoding.events.scope earlier.1)
  Finset.univ.filter fun o => executed o ∧ ∃ seed, executed seed ∧
    (∃ C ∈ replayTargets D critical, C ∈ D.encoding.events.scope seed.1) ∧
      Relation.ReflTransGen edge seed o

theorem markedOccurrences_in_closure (D : S18.LateData hPT) (hD : D.Spec)
    (critical : Finset D.geom.Cell) (x : D.encoding.InitInput) :
    markedOccurrences D critical x ⊆ replayBackwardClosure D critical x := by
  intro o ho
  have hact : o.1 ∈ D.encoding.events.active D.encoding.order Finset.univ
      (D.encoding.events.runRounds o.2.val D.encoding.order Finset.univ x.1 x.2.extend).1 ∩
        S18.replayMarked D critical := (Finset.mem_filter.mp ho).2
  have hmark := (Finset.mem_inter.mp hact).2
  have hexec := (Finset.mem_inter.mp hact).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexec, o, hexec,
    markedSite_touches_target D hD critical o.1 hmark, Relation.ReflTransGen.refl⟩

/-- A finite occurrence set specifies the forced sites in each recorded round. -/
noncomputable def occurrencePattern (D : S18.LateData hPT)
    (W : Finset (Pos T k × Fin D.encoding.Ts)) (t : ℕ) : Finset (Pos T k) :=
  (W.filter fun o => o.2.val = t).image Prod.fst

theorem occurrencePattern_actual (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) (x : D.encoding.InitInput)
    (t : ℕ) (ht : t < D.encoding.Ts) :
    occurrencePattern D (markedOccurrences D critical x) t =
      S18.actualPattern D (S18.replayMarked D critical) x t := by
  ext v
  constructor
  · intro hv
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ho, hr⟩ := Finset.mem_filter.mp ho
    have hact := (Finset.mem_filter.mp ho).2
    simpa only [hr] using hact
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨(v, ⟨t, ht⟩), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

noncomputable def boundedOccurrencePatterns {α : Type*} [DecidableEq α]
    (sites : Finset α) (Ts : ℕ) : Finset (Finset (α × Fin Ts)) :=
  (Finset.range (Ts + 1)).biUnion fun m => (sites ×ˢ Finset.univ).powersetCard m

theorem boundedOccurrencePatterns_mem {α : Type*} [DecidableEq α]
    (sites : Finset α) (Ts : ℕ) (W : Finset (α × Fin Ts))
    (hW : W ⊆ sites ×ˢ Finset.univ) (hcard : W.card ≤ Ts) :
    W ∈ boundedOccurrencePatterns sites Ts := by
  exact Finset.mem_biUnion.mpr ⟨W.card, Finset.mem_range.mpr (by omega),
    Finset.mem_powersetCard.mpr ⟨hW, rfl⟩⟩

theorem boundedOccurrencePatterns_card {α : Type*} [DecidableEq α]
    (sites : Finset α) (Ts : ℕ) :
    (boundedOccurrencePatterns sites Ts).card ≤
      (Ts + 1) * (max 1 (sites.card * Ts)) ^ Ts := by
  calc
    (boundedOccurrencePatterns sites Ts).card ≤
        ∑ m ∈ Finset.range (Ts + 1), ((sites ×ˢ Finset.univ).powersetCard m).card :=
      Finset.card_biUnion_le
    _ = ∑ m ∈ Finset.range (Ts + 1), Nat.choose (sites.card * Ts) m := by simp
    _ ≤ ∑ m ∈ Finset.range (Ts + 1), (max 1 (sites.card * Ts)) ^ Ts := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m ≤ Ts := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      calc
        Nat.choose (sites.card * Ts) m ≤ (sites.card * Ts) ^ m := Nat.choose_le_pow _ _
        _ ≤ (max 1 (sites.card * Ts)) ^ m := Nat.pow_le_pow_left (le_max_right _ _) _
        _ ≤ (max 1 (sites.card * Ts)) ^ Ts :=
          Nat.pow_le_pow_right (by omega) hmle
    _ = (Ts + 1) * (max 1 (sites.card * Ts)) ^ Ts := by simp

theorem actualPattern_cover (D : S18.LateData hPT) (critical : Finset D.geom.Cell)
    (x : D.encoding.InitInput) (hcard : (markedOccurrences D critical x).card ≤ D.encoding.Ts) :
    ∃ W ∈ boundedOccurrencePatterns (S18.replayMarked D critical) D.encoding.Ts,
      ∀ t < D.encoding.Ts, occurrencePattern D W t =
        S18.actualPattern D (S18.replayMarked D critical) x t := by
  refine ⟨markedOccurrences D critical x, ?_, occurrencePattern_actual D critical x⟩
  apply boundedOccurrencePatterns_mem _ _ _ _ hcard
  intro o ho
  exact Finset.mem_product.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp ho).2).2, Finset.mem_univ _⟩

/-- For an arbitrary fixed replay pattern and arbitrary outside inputs,
the normalized critical fresh experiment is exactly the transfer law. -/
theorem criticalFreshReplayBound (D : S18.LateData hPT)
    (hReplay : S18.ReplayFacts D) (c : ℝ) (hTransfer : S18.TransferBound D c)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (omitted : Option D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (outside : D.encoding.InitInput) :
    let X₀ : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
    let fixed := (S18.replayRounds D (S18.replayMarked D X₀.criticalCells)
      pattern outside D.encoding.Ts).1
    let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
    X.rawLaw.E (fun raw => forcedReplayRisk D X.criticalCells pattern F
      (criticalReplayInput D X.criticalCells outside raw)) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  dsimp only
  let X₀ : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  let fixed := (S18.replayRounds D (S18.replayMarked D X₀.criticalCells)
    pattern outside D.encoding.Ts).1
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
  change X.rawLaw.E _ ≤ _
  have hfixed : X.criticalCells = X₀.criticalCells := rfl
  have hstate (raw : X.Raw) (hraw : 0 < X.rawLaw.w raw) :
      (S18.replayRounds D (S18.replayMarked D X.criticalCells) pattern
        (criticalReplayInput D X.criticalCells outside raw) D.encoding.Ts).1 = X.state raw := by
    funext C
    rw [criticalReplayState D hReplay]
    by_cases hC : C ∈ X.criticalCells
    · simp [hC, S18.CriticalTransferData.state]
    · have hcoord : 0 < (if C ∈ X.criticalCells then D.typicalFresh C
          else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)).w (raw C) := by
        by_contra hn
        have hz : (if C ∈ X.criticalCells then D.typicalFresh C
            else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)).w (raw C) = 0 :=
          le_antisymm (le_of_not_gt hn) (FinLaw.nonneg _ _)
        have hp : X.rawLaw.w raw = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ C) hz
        linarith
      simp only [if_neg hC, FinLaw.dirac] at hcoord
      have heq : raw C = (D.l16_valid.pools_nonempty.choose C, X.fixed C) := by
        by_contra hne
        simp [hne] at hcoord
      simp [hC, S18.CriticalTransferData.state, heq, X, fixed, hfixed]
  have hE : X.rawLaw.E (fun raw => forcedReplayRisk D X.criticalCells pattern F
        (criticalReplayInput D X.criticalCells outside raw)) =
      X.rawLaw.E (fun raw => (D.encoding.kernels.refRun (X.state raw)).pr
        (D.prefixFailure F.2)) := by
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro raw _
    by_cases hw : 0 < X.rawLaw.w raw
    · unfold forcedReplayRisk
      dsimp only
      rw [hstate raw hw, prefixLateFailure_eq D F hkind]
    · have hz : X.rawLaw.w raw = 0 := le_antisymm (le_of_not_gt hw) (X.rawLaw.nonneg raw)
      simp [hz]
  rw [hE, ← bindPrExpectation]
  exact hTransfer X

theorem criticalTypicalWeight_le (D : S18.LateData hPT) (hD : D.Spec)
    (C : D.geom.Cell) (Ps : D.fresh.Pool C × D.fresh.State C)
    (htyp : D.fresh.typical C Ps.1) :
    (FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C)).w Ps ≤ (D.typicalFresh C).w Ps := by
  have hpos := hD.typical_positive C
  have hmass : (∑ P ∈ D.typicalPools C, (D.cellPoolLaw C).w P) ≤ 1 := by
    calc
      (∑ P ∈ D.typicalPools C, (D.cellPoolLaw C).w P) ≤
          ∑ P, (D.cellPoolLaw C).w P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun P _ _ => (D.cellPoolLaw C).nonneg P)
      _ = 1 := (D.cellPoolLaw C).sum_one
  have hmem : Ps.1 ∈ D.typicalPools C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htyp⟩
  simp only [S18.LateData.typicalFresh, dif_pos hpos, FinLaw.bind, FinLaw.cond,
    if_pos hmem]
  apply mul_le_mul_of_nonneg_right _ ((D.fresh.fresh C Ps.1).nonneg Ps.2)
  exact (le_div_iff₀ hpos).2 (by nlinarith [(D.cellPoolLaw C).nonneg Ps.1])

/-- Retaining critical-pool typicality before normalization has cost at most
one. This comparison does not enlarge away the critical typicality gate. -/
theorem criticalTypicalIntegral_le (D : S18.LateData hPT) (hD : D.Spec)
    (X : S18.CriticalTransferData D) (f : X.Raw → ℝ) (hf : ∀ s, 0 ≤ f s) :
    (FinLaw.pi fun C => if C ∈ X.criticalCells then
      FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C)
      else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)).E
      (fun s => if ∀ C ∈ X.criticalCells, D.fresh.typical C (s C).1 then f s else 0) ≤
        X.rawLaw.E f := by
  unfold FinLaw.E
  apply Finset.sum_le_sum
  intro s _
  by_cases ht : ∀ C ∈ X.criticalCells, D.fresh.typical C (s C).1
  · simp only [if_pos ht]
    apply mul_le_mul_of_nonneg_right _ (hf s)
    apply Finset.prod_le_prod₀
    · intro C _
      exact FinLaw.nonneg _ _
    · intro C _
      by_cases hC : C ∈ X.criticalCells
      · simp only [S18.CriticalTransferData.rawLaw, FinLaw.pi, if_pos hC]
        exact criticalTypicalWeight_le D hD C (s C) (ht C hC)
      · simp only [S18.CriticalTransferData.rawLaw, FinLaw.pi, if_neg hC, le_refl]
  · simp only [if_neg ht, mul_zero]
    exact mul_nonneg (X.rawLaw.nonneg s) (hf s)

/-- The terminal entry selected in one cell has the fresh law for the actual
pool, independently of which fixed entry is prescribed. -/
theorem prescribedTapeEntryLaw (D : S18.LateData hPT) (C : D.geom.Cell)
    (entry : Fin (D.encoding.Ts + 2)) (P : D.fresh.Pool C) :
    FinLaw.map (FinLaw.pi fun _ : Fin (D.encoding.Ts + 2) =>
      FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
        (fun tape => tape entry P) = D.fresh.fresh C P := by
  letI : DecidableEq (D.fresh.Pool C → D.fresh.State C) := Classical.decEq _
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro s
  have hE := S16.Lane_q_s16_comp2.map_expect
    (FinLaw.pi fun _ : Fin (D.encoding.Ts + 2) =>
      FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
    (fun tape => tape entry P) (fun y => if y = s then 1 else 0)
  have hentry := S16.Lane_q_s16_comp2.map_expect
    (FinLaw.pi fun _ : Fin (D.encoding.Ts + 2) =>
      FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
    (fun tape => tape entry) (fun row => if row P = s then 1 else 0)
  have hentryLaw : FinLaw.map (FinLaw.pi fun _ : Fin (D.encoding.Ts + 2) =>
      FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
      (fun tape => tape entry) = FinLaw.pi (fun Q : D.fresh.Pool C => D.fresh.fresh C Q) :=
    Lane_q_s17_res1.pi_map_coordinate_law _ entry
  rw [hentryLaw] at hentry
  have hpool := S16.Lane_q_s16_comp2.map_expect
    (FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
    (fun row => row P) (fun y => if y = s then 1 else 0)
  have hpoolLaw : FinLaw.map (FinLaw.pi fun Q : D.fresh.Pool C => D.fresh.fresh C Q)
      (fun row => row P) = D.fresh.fresh C P := Lane_q_s17_res1.pi_map_coordinate_law _ P
  rw [hpoolLaw] at hpool
  have heq := hE.trans (hentry.symm.trans hpool.symm)
  simpa only [FinLaw.E, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using heq

noncomputable def cellTapeLaw (D : S18.LateData hPT) (C : D.geom.Cell) :
    FinLaw (Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C) :=
  FinLaw.pi fun _ : Fin (D.encoding.Ts + 2) =>
    FinLaw.pi fun P : D.fresh.Pool C => D.fresh.fresh C P

/-- Draw an iid cell pool and an independent full lookup tape, then read the
prescribed entry at that pool. The resulting joint law is pool/fresh sampling. -/
theorem prescribedPoolTapeLaw (D : S18.LateData hPT) (C : D.geom.Cell)
    (entry : Fin (D.encoding.Ts + 2)) :
    FinLaw.map (FinLaw.bind (D.cellPoolLaw C) (fun _ => cellTapeLaw D C))
      (fun x => (x.1, x.2 entry x.1)) =
        FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C) := by
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro Ps
  change (∑ x : D.fresh.Pool C × (Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C),
      if (x.1, x.2 entry x.1) = Ps then
        (D.cellPoolLaw C).w x.1 * (cellTapeLaw D C).w x.2 else 0) =
    (D.cellPoolLaw C).w Ps.1 * (D.fresh.fresh C Ps.1).w Ps.2
  rw [Fintype.sum_prod_type]
  have hsum (P : D.fresh.Pool C) :
      (∑ tape, if (P, tape entry P) = Ps then
        (D.cellPoolLaw C).w P * (cellTapeLaw D C).w tape else 0) =
      if P = Ps.1 then
        (D.cellPoolLaw C).w Ps.1 * (D.fresh.fresh C Ps.1).w Ps.2 else 0 := by
    by_cases hP : P = Ps.1
    · subst P
      have heq (tape : Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C) :
          (Ps.1, tape entry Ps.1) = Ps ↔ tape entry Ps.1 = Ps.2 := by
        cases Ps
        simp
      simp only [heq, ite_true]
      calc
        _ = (D.cellPoolLaw C).w Ps.1 *
            ∑ tape, if tape entry Ps.1 = Ps.2 then (cellTapeLaw D C).w tape else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tape _
          by_cases ht : tape entry Ps.1 = Ps.2 <;> simp [ht]
        _ = _ := congrArg (fun w => (D.cellPoolLaw C).w Ps.1 * w)
          (congrArg (fun Q => Q.w Ps.2) (prescribedTapeEntryLaw D C entry Ps.1))
    · have hne (tape : Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C) :
          (P, tape entry P) ≠ Ps := by
        intro heq
        exact hP (congrArg Prod.fst heq)
      simp [hP, hne]
  simp_rw [hsum]
  simp

theorem criticalCells_card_le (D : S18.LateData hPT) (X : S18.CriticalTransferData D) :
    X.criticalCells.card ≤ T.S.n k := by
  calc
    X.criticalCells.card ≤ X.criticalCoords.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (T.S.n k))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = T.S.n k := by simp

private noncomputable def incidentStar (v : Pos T k) : Finset (Pos T k) :=
  insert v (Finset.univ.image (flipPos v))

private theorem incidentStar_symm {v w : Pos T k} (hw : w ∈ incidentStar v) :
    v ∈ incidentStar w := by
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    funext b
    by_cases hb : b = a
    · subst b
      simp [flipPos]
    · simp [flipPos, hb]

private theorem incidentStar_card (v : Pos T k) : (incidentStar v).card ≤ T.S.n k + 1 := by
  calc
    (incidentStar v).card ≤ (Finset.univ.image (flipPos v)).card + 1 := Finset.card_insert_le _ _
    _ ≤ T.S.n k + 1 := by
      simpa using Nat.add_le_add_right
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin (T.S.n k)))) (f := flipPos v)) 1

theorem eventScope_card_le (D : S18.LateData hPT) (hD : D.Spec) (v : Pos T k) :
    (D.encoding.events.scope v).card ≤ T.S.n k + 1 := by
  rw [hD.scope_eq]
  calc
    (D.directCells v).card ≤ 1 + (D.externalEarly v).card :=
      (Finset.card_union_le _ _).trans (by
        simpa using Nat.add_le_add_left (Finset.card_image_le (s := D.externalEarly v)
          (f := fun a => D.geom.cellOf (flipPos v a))) 1)
    _ ≤ T.S.n k + 1 := by
      have h := Finset.card_le_card (Finset.filter_subset
        (fun a : Fin (T.S.n k) => a ∉ PT.tiling.Icoord (D.geom.patchOf v) ∧
          D.geom.classOf (flipPos v a) = none) Finset.univ)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      simpa only [S18.LateData.externalEarly, Nat.add_comm] using Nat.add_le_add_left h 1

theorem incidentEvents_card_le (D : S18.LateData hPT) (hD : D.Spec) (C : D.geom.Cell) :
    (D.encoding.events.incidentEvents C).card ≤ T.S.n k ^ κ.Ac * (T.S.n k + 1) := by
  let positions := Finset.univ.filter fun b : Pos T k => D.geom.cellOf b = C
  have hsub : D.encoding.events.incidentEvents C ⊆ positions.biUnion incidentStar := by
    intro v hv
    have hscope := (Finset.mem_filter.mp hv).2
    rw [hD.scope_eq] at hscope
    have hstar : ∃ b ∈ incidentStar v, D.geom.cellOf b = C := by
      rcases Finset.mem_union.mp hscope with hown | hext
      · exact ⟨v, Finset.mem_insert_self _ _, (Finset.mem_singleton.mp hown).symm⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hext
        exact ⟨flipPos v a, Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩), rfl⟩
    obtain ⟨b, hb, hcell⟩ := hstar
    exact Finset.mem_biUnion.mpr
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩, incidentStar_symm hb⟩
  calc
    (D.encoding.events.incidentEvents C).card ≤ (positions.biUnion incidentStar).card :=
      Finset.card_le_card hsub
    _ ≤ positions.card * (T.S.n k + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => incidentStar_card b)
    _ ≤ T.S.n k ^ κ.Ac * (T.S.n k + 1) :=
      Nat.mul_le_mul_right _ (D.l16_valid.cell_size C)

theorem replayMarked_card_le (D : S18.LateData hPT) (hD : D.Spec)
    (critical : Finset D.geom.Cell) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter fun w => D.encoding.events.Adjacent w v).card ≤ d) :
    (S18.replayMarked D critical).card ≤
      critical.card * (T.S.n k ^ κ.Ac * (T.S.n k + 1)) * (d + 1) := by
  let touching := critical.biUnion D.encoding.events.incidentEvents
  have ht : touching.card ≤ critical.card * (T.S.n k ^ κ.Ac * (T.S.n k + 1)) :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun C _ => incidentEvents_card_le D hD C)
  have hn : (Finset.univ.filter fun w => ∃ v ∈ touching, D.encoding.events.Adjacent w v) =
      touching.biUnion (fun v => Finset.univ.filter fun w => D.encoding.events.Adjacent w v) := by
    ext w
    simp
  calc
    (S18.replayMarked D critical).card ≤ touching.card +
        (Finset.univ.filter fun w => ∃ v ∈ touching, D.encoding.events.Adjacent w v).card :=
      Finset.card_union_le _ _
    _ ≤ touching.card + touching.card * d := by
      rw [hn]
      exact Nat.add_le_add_left (Finset.card_biUnion_le_card_mul _ _ _
        (fun v _ => hdegree v)) _
    _ = touching.card * (d + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ ht

theorem replayTargets_card_le (D : S18.LateData hPT) (hD : D.Spec)
    (critical : Finset D.geom.Cell) :
    (replayTargets D critical).card ≤
      critical.card * (T.S.n k ^ κ.Ac * (T.S.n k + 1)) * (T.S.n k + 1) := by
  calc
    (replayTargets D critical).card ≤
        (critical.biUnion D.encoding.events.incidentEvents).card * (T.S.n k + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => eventScope_card_le D hD v)
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_biUnion_le_card_mul _ _ _
      (fun C _ => incidentEvents_card_le D hD C))

private theorem flip_hamming_le (v : Pos T k) (a : Fin (T.S.n k)) :
    _root_.hammingDist v (flipPos v a) ≤ 1 := by
  have hsub : (Finset.univ.filter fun b => v b ≠ flipPos v a b) ⊆ {a} := by
    intro b hb
    by_contra hn
    have hba : b ≠ a := by simpa using hn
    exact (Finset.mem_filter.mp hb).2 (by simp [flipPos, hba])
  simpa [_root_.hammingDist] using Finset.card_le_card hsub

theorem criticalCells_in_seed (D : S18.LateData hPT) (F : S18.LateEvent D)
    (hvalid : D.prefixValid F.2) (omitted : Option D.geom.Cell)
    (fixed : Config D.fresh) :
    (S18.CriticalTransferData.mk F.2 hvalid omitted fixed).criticalCells ⊆
      (cubeBall F.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells := by
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
  intro C hC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
  apply Finset.mem_biUnion.mpr
  refine ⟨flipPos X.target a, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hdist := _root_.hammingDist_triangle F.2.2.1.1 X.target (flipPos X.target a)
    have hfirst : _root_.hammingDist F.2.2.1.1 X.target ≤ 1 := flip_hamming_le _ _
    have hsecond := flip_hamming_le X.target a
    have hr := D.l16_valid.r_pos
    omega
  · change D.geom.cellOf (flipPos X.target a) ∈ D.directCells (flipPos X.target a)
    simp [S18.LateData.directCells]

theorem criticalCells_in_lateRegion (D : S18.LateData hPT) (F : S18.LateEvent D)
    (hvalid : D.prefixValid F.2) (omitted : Option D.geom.Cell) (fixed : Config D.fresh) :
    (S18.CriticalTransferData.mk F.2 hvalid omitted fixed).criticalCells ⊆ D.lateRegion F := by
  exact fun _ hC => Finset.mem_union.mpr (Or.inl (criticalCells_in_seed D F hvalid omitted fixed hC))

noncomputable def replayClosure (D : S18.LateData hPT)
    (critical : Finset D.geom.Cell) (x : D.encoding.InitInput) : Prop :=
  D.encoding.Ts < (replayBackwardClosure D critical x).card

/-- The valid-prefix proof has two analytic inputs: a closure tail, and a
fixed-pattern integral. Its finite pattern cover and replay enlargement are
supplied here by the actual resampling experiment. -/
theorem validPrefixProbabilityBound (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (δ : ℝ) (F : S18.LateEvent D)
    (hvalid : D.prefixValid F.2) (omitted : Option D.geom.Cell)
    (P : FinLaw D.encoding.InitInput) (closureCost patternCost bound : ℝ)
    (hclosure :
      let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
      P.pr (fun x => D.poolGate (D.lateRegion F) x ∧ replayClosure D X.criticalCells x) ≤ closureCost)
    (hpattern :
      let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
      ∀ W ∈ boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts,
        P.E (fun x => if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
          forcedReplayRisk D X.criticalCells (occurrencePattern D W) F x else 0) ≤ patternCost)
    (hbudget :
      let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
      closureCost + (Real.exp (-Real.rpow (T.S.n k : ℝ) δ))⁻¹ *
        ((boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card *
          patternCost) ≤ bound) :
    P.pr (S18.terminalFailure D δ (.inr (.inr F))) ≤ bound := by
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  let critical := X.criticalCells
  let patterns := boundedOccurrencePatterns (S18.replayMarked D critical) D.encoding.Ts
  let gate := D.poolGate (D.lateRegion F)
  let consistent := fun W x => gate x ∧ ¬ replayClosure D critical x ∧
    ∀ t < D.encoding.Ts, occurrencePattern D W t =
      S18.actualPattern D (S18.replayMarked D critical) x t
  have hcover : ∀ x, gate x ∧ ¬ replayClosure D critical x →
      ∃ W ∈ patterns, consistent W x := by
    intro x hx
    have hcard : (markedOccurrences D critical x).card ≤ D.encoding.Ts := by
      have hsub := markedOccurrences_in_closure D hD critical x
      have hsmall := le_of_not_gt hx.2
      exact (Finset.card_le_card hsub).trans hsmall
    obtain ⟨W, hW, hpat⟩ := actualPattern_cover D critical x hcard
    exact ⟨W, hW, hx.1, hx.2, hpat⟩
  have hp : ∀ W ∈ patterns,
      P.E (fun x => @ite ℝ (consistent W x) (Classical.propDecidable _) (D.pLate F x) 0) ≤ patternCost := by
    intro W hW
    apply (forcedReplayIntegralEnlargement D hReplay P critical (occurrencePattern D W) F
      (consistent W) (fun x => ∀ C ∈ critical, D.fresh.typical C (x.1 C))
      (fun x hx => hx.2.2) ?_).trans
    · convert hpattern W hW using 1
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro x _
      change P.w x * (@ite ℝ (∀ C ∈ critical, D.fresh.typical C (x.1 C))
        (Classical.propDecidable _) (forcedReplayRisk D critical (occurrencePattern D W) F x) 0) =
        P.w x * (if ∀ C ∈ critical, D.fresh.typical C (x.1 C) then
          forcedReplayRisk D critical (occurrencePattern D W) F x else 0)
      by_cases ht : ∀ C ∈ critical, D.fresh.typical C (x.1 C) <;> simp [ht]
    · intro x hx C hC
      exact hx.1.1 C (criticalCells_in_lateRegion D F hvalid omitted X.fixed hC)
  apply riskBoundFromReplayPatterns P gate (replayClosure D critical) patterns consistent
    (D.pLate F) (Real.exp (-Real.rpow (T.S.n k : ℝ) δ)) (Real.exp_pos _)
    (fun x => Lane_q_s17_res1.finLaw_pr_nonneg _ _) hcover
    closureCost patternCost bound hclosure hp hbudget

noncomputable def initialPinnedLaw (D : S18.LateData hPT) (pin : Option (S18.SlotPin D)) :
    FinLaw D.encoding.InitInput :=
  match pin with
  | none => D.encoding.permLaw
  | some p =>
    let A := Finset.univ.filter (S18.pinEvent D p)
    if h : 0 < ∑ x ∈ A, D.encoding.permLaw.w x then FinLaw.cond D.encoding.permLaw A h
    else D.encoding.permLaw

theorem initialProbability_le_pinnedLaw (D : S18.LateData hPT) (pin : Option (S18.SlotPin D))
    (F : D.encoding.InitInput → Prop) :
    S18.initialProbability D pin F ≤ (initialPinnedLaw D pin).pr F := by
  cases pin with
  | none => exact le_rfl
  | some p =>
    let A := Finset.univ.filter (S18.pinEvent D p)
    have hden : D.encoding.permLaw.pr (S18.pinEvent D p) =
        ∑ x ∈ A, D.encoding.permLaw.w x := by
      simp only [A, FinLaw.pr, Finset.sum_filter]
    change D.encoding.permLaw.pr (fun x => S18.pinEvent D p x ∧ F x) /
      D.encoding.permLaw.pr (S18.pinEvent D p) ≤ _
    rw [hden]
    by_cases hpos : 0 < ∑ x ∈ A, D.encoding.permLaw.w x
    · change _ ≤ (if h : 0 < ∑ x ∈ A, D.encoding.permLaw.w x then
        FinLaw.cond D.encoding.permLaw A h else D.encoding.permLaw).pr F
      rw [dif_pos hpos]
      apply le_of_eq
      unfold FinLaw.pr FinLaw.cond
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      have hx : x ∈ A ↔ S18.pinEvent D p x := by simp [A]
      by_cases hp : S18.pinEvent D p x <;> by_cases hf : F x <;>
        simp [hp, hf, hx]
    · have hzero : (∑ x ∈ A, D.encoding.permLaw.w x) = 0 :=
        le_antisymm (le_of_not_gt hpos) (Finset.sum_nonneg (fun x _ => D.encoding.permLaw.nonneg x))
      rw [hzero]
      simp only [div_zero]
      exact Lane_q_s17_res1.finLaw_pr_nonneg _ _

set_option maxHeartbeats 400000 in
theorem validPrefixPinnedBoundFromEstimates (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (δ : ℝ) (F : S18.LateEvent D)
    (hvalid : D.prefixValid F.2) (pin : Option (S18.SlotPin D))
    (closureCost patternCost : ℝ)
    (hclosure :
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
      (initialPinnedLaw D pin).pr (fun x =>
        D.poolGate (D.lateRegion F) x ∧ replayClosure D X.criticalCells x) ≤ closureCost)
    (hpattern :
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
      ∀ W ∈ boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts,
        (initialPinnedLaw D pin).E (fun x =>
          if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
            forcedReplayRisk D X.criticalCells (occurrencePattern D W) F x else 0) ≤ patternCost)
    (hbudget :
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
      closureCost + (Real.exp (-Real.rpow (T.S.n k : ℝ) δ))⁻¹ *
        ((boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card *
          patternCost) ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))) :
    S18.initialProbability D pin (S18.terminalFailure D δ (.inr (.inr F))) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  exact (initialProbability_le_pinnedLaw D pin _).trans
    (validPrefixProbabilityBound (κ := κ) (T := T) (k := k) (PT := PT) (hPT := hPT)
      D hD hReplay δ F hvalid (pin.map (fun p => p.1))
      (initialPinnedLaw D pin) closureCost patternCost
      (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)))
      hclosure hpattern hbudget)

end HypercubeRamsey.Lane_sol_s18_n4
