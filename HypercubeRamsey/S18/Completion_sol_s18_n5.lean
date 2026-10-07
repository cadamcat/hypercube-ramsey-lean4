import HypercubeRamsey.S18.Comparisons_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem terminal_input_support (D : LateData hPT) {δ ε : ℝ}
    (C : TerminalCertificate D δ ε) (x : D.encoding.InitInput)
    (hx : (D.encoding.terminalLaw (terminalSet D δ) C.positive).w x ≠ 0) :
    x ∈ terminalSet D δ ∧ x.1 ∈ permPools D.geom ∧ 0 < D.encoding.permLaw.w x := by
  have hm : x ∈ terminalSet D δ := by
    by_contra hn
    exact hx (by simp [LateEncoding.terminalLaw, FinLaw.cond, hn])
  have hw : D.encoding.permLaw.w x ≠ 0 := by
    intro hn
    exact hx (by simp [LateEncoding.terminalLaw, FinLaw.cond, hn])
  have hp : x.1 ∈ permPools D.geom := by
    by_contra hn
    exact hw (by simp [LateEncoding.permLaw, LateEncoding.initialLaw, FinLaw.bind,
      LateEncoding.poolLaw, permPoolLaw, FinLaw.uniform, hn])
  exact ⟨hm, hp, lt_of_le_of_ne (D.encoding.permLaw.nonneg x) hw.symm⟩

/-- Once every entering check passes, support of the actual samplers gives
all the completion conclusions. Bad avoidance is used only after the gate
has been established by induction on the processing index. -/
theorem full_of_entering_supported (D : LateData hPT) (hD : D.Spec)
    {δ ε : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    {K27 : ℝ} (hBroad : BroadDeletionFacts D K27)
    (x : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
    (hx : (D.encoding.terminalLaw (terminalSet D δ) C.positive).w x ≠ 0)
    (hinit : h.1 = D.encoding.initialState x)
    (henter : ∀ j : Fin D.geom.r,
      D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)))
    (hsupport : ∀ j : Fin D.geom.r,
      (A.act j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))).w
        (D.pastRows h j j.isLt) ≠ 0) : D.full δ x h := by
  obtain ⟨hterm, hperm, hpos⟩ := terminal_input_support D C x hx
  have htyp := (C.pools x hterm).1
  have hvalid : ∀ v, IsEvenRole v → D.initialValid v h.1 := by
    rw [hinit]
    exact hD.initial_success x hpos htyp (C.initial x hterm)
  have hsampler := fun j => (A.sampler j _ (henter j)).1 _ (hsupport j)
  have hconclusions : ∀ q : ℕ, ∀ j : Fin D.geom.r, j.val = q →
      ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
        D.gate j b.1 (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) ∧
        D.R3 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows h j j.isLt b) ∧
        D.deletionConclusion j (D.pastRows h j j.isLt b) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro j hj b
      have hg : D.gate j b.1 (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) := by
        constructor
        · intro w _ hw
          exact hvalid w hw
        · intro s hs b' _
          have hpast := (ih s.val (by omega) s rfl b').2
          simpa only [LateData.beforeHistory, LateData.pastRows] using hpast
      have hR1 : D.R1 j (D.pastRows h j j.isLt b) := by
        by_contra hn
        exact (hsampler j).2.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, b, hg, Or.inl hn⟩)
      have hR2 : D.R2 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
          (D.pastRows h j j.isLt b) := by
        by_contra hn
        exact (hsampler j).2.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, b, hg, Or.inr (Or.inl hn)⟩)
      have hR3 : D.R3 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
          (D.pastRows h j j.isLt b) := by
        by_contra hn
        exact (hsampler j).2.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, b, hg, Or.inr (Or.inr ⟨hR1, hR2, hn⟩)⟩)
      exact ⟨hg, hR3, (hBroad j b.1 _ _ b.2 hg hR1 hR2).2.1⟩
  have hearly := D.early_injective x hpos hperm htyp
  have hearly_reserve : ∀ b : {v : Pos T k // ¬ IsEvenRole v},
      D.earlyLabel h.1 b.1 ∉ PT.tiling.reserveY := by
    intro b
    have hmem := D.early_support x hpos htyp b.1 b.2
    rw [← hinit] at hmem
    exact (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports _).2.2.2
      ((hPT.tiling_valid.patch_supports _).2.2.1 hmem))).2
  have hlate (b : {v : Pos T k // ¬ IsEvenRole v})
      (hb : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r)) :
      ∃ j : Fin D.geom.r, ∃ hj : b.1 ∈ D.encoding.base.classes j,
        D.oddAt h b = D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨b.1, hj⟩) := by
    have hc := hb
    rw [D.encoding.base.processed_last] at hc
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hc).2
    have hm := (D.encoding.base.class_of_spec b.1 j).mpr hj
    exact ⟨j, hm, by simp [LateData.oddAt, hb, LateData.pastRows]⟩
  have hpool (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
      D.encoding.base.rowLabel (D.pastRows h j j.isLt b) ∈ D.encoding.base.latePool j := by
    have hmem := (D.pastRows h j j.isLt b).2.2.2
    simpa only [LateProcessBase.latePoolOf, LateProcessBase.rowLabel,
      (D.encoding.base.class_of_spec b.1 j).mp b.2] using hmem
  have hinj : Function.Injective (D.oddAt h) := by
    intro b c heq
    by_cases hb : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r)
    · obtain ⟨j, hj, hbj⟩ := hlate b hb
      by_cases hc : c.1 ∈ D.encoding.base.processed (Fin.last D.geom.r)
      · obtain ⟨s, hs, hcs⟩ := hlate c hc
        by_cases hjs : j = s
        · subst s
          have heq' := (hsampler j).1 (show
            D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨b.1, hj⟩) =
            D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨c.1, hs⟩) by
              rw [← hbj, ← hcs]; exact heq)
          exact Subtype.ext (congrArg
            (fun t : {v : Pos T k // v ∈ D.encoding.base.classes j} => t.1) heq')
        · exfalso
          exact (Finset.disjoint_left.mp (D.encoding.base.latePool_disjoint j s hjs))
            (hpool j ⟨b.1, hj⟩) (by rw [← hbj, heq, hcs]; exact hpool s ⟨c.1, hs⟩)
      · exfalso
        apply hearly_reserve c
        have hres := D.encoding.base.latePool_reserve j (hpool j ⟨b.1, hj⟩)
        rw [← hbj, heq] at hres
        simpa only [LateData.oddAt, dif_neg hc] using hres
    · by_cases hc : c.1 ∈ D.encoding.base.processed (Fin.last D.geom.r)
      · obtain ⟨s, hs, hcs⟩ := hlate c hc
        exfalso
        apply hearly_reserve b
        have hres := D.encoding.base.latePool_reserve s (hpool s ⟨c.1, hs⟩)
        rw [← hcs, ← heq] at hres
        simpa only [LateData.oddAt, dif_neg hb] using hres
      · apply hearly
        simpa only [LateData.oddAt, dif_neg hb, dif_neg hc, LateData.earlyLabel, hinit] using heq
  refine ⟨hterm, hperm, hpos, hinit, hvalid, hinj, ?_⟩
  intro j
  exact ⟨henter j, (hsampler j).1, (hsampler j).2.1, (hsampler j).2.2,
    hconclusions j.val j rfl⟩

private theorem map_support {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (b : β) (hb : (FinLaw.map P f).w b ≠ 0) :
    ∃ a, f a = b ∧ P.w a ≠ 0 := by
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  by_cases heq : f a = b
  · exact ⟨a, heq, by simpa only [heq, if_true] using ha⟩
  · exact False.elim (ha (by simp [heq]))

theorem beforeHistory_self (D : LateData hPT) (t : Fin (D.geom.r + 1))
    (h : D.encoding.base.History t) : D.beforeHistory h t le_rfl = h := by
  apply Prod.ext rfl
  funext b
  rfl

theorem beforeHistory_extend (D : LateData hPT) (t : Fin D.geom.r)
    (h : D.encoding.base.History t.castSucc) (out : D.encoding.base.ClassRows t)
    (j : Fin (D.geom.r + 1)) (hj : j.val ≤ t.val) :
    D.beforeHistory (D.encoding.base.extend t h out) j
      (by simpa only [Fin.val_succ] using Nat.le_trans hj (Nat.le_succ t.val)) =
      D.beforeHistory h j hj := by
  apply Prod.ext
  · rfl
  · funext b
    have hb := D.processed_mono j t.castSucc hj b.2
    simp only [LateData.beforeHistory, LateProcessBase.extend, dif_pos hb]

theorem pastRows_extend_before (D : LateData hPT) (t : Fin D.geom.r)
    (h : D.encoding.base.History t.castSucc) (out : D.encoding.base.ClassRows t)
    (j : Fin D.geom.r) (hj : j.val < t.val) :
    D.pastRows (D.encoding.base.extend t h out) j
      (by simpa only [Fin.val_succ] using Nat.lt_succ_of_lt hj) = D.pastRows h j hj := by
  funext b
  have hb := D.class_before j t.castSucc hj b.2
  simp only [LateData.pastRows, LateProcessBase.extend, dif_pos hb]

theorem pastRows_extend_current (D : LateData hPT) (t : Fin D.geom.r)
    (h : D.encoding.base.History t.castSucc) (out : D.encoding.base.ClassRows t) :
    D.pastRows (D.encoding.base.extend t h out) t (by simp) = out := by
  funext b
  have hb : b.1 ∉ D.encoding.base.processed t.castSucc := by
    exact fun hn => Finset.disjoint_left.mp (D.encoding.base.class_fresh t) b.2 hn
  simp only [LateData.pastRows, LateProcessBase.extend, dif_neg hb]

/-- Positive-weight final histories retain their initial state and each
actual transition. This is a support statement about the defined runFrom. -/
theorem runFrom_support (D : LateData hPT)
    (act : ∀ j : Fin D.geom.r,
      D.encoding.base.History j.castSucc → FinLaw (D.encoding.base.ClassRows j))
    (s : Config D.fresh) (m : ℕ) (hm : m ≤ D.geom.r)
    (h : D.encoding.base.History ⟨m, Nat.lt_succ_of_le hm⟩)
    (hw : (D.encoding.base.runFrom act s m hm).w h ≠ 0) :
    h.1 = s ∧ ∀ j : Fin D.geom.r, ∀ hj : j.val < m,
      (act j (D.beforeHistory h j.castSucc (Nat.le_of_lt hj))).w
        (D.pastRows h j hj) ≠ 0 := by
  classical
  induction m with
  | zero =>
    have hh : h = D.encoding.base.initialHistory s := by
      simp only [LateProcessBase.runFrom, FinLaw.dirac] at hw
      split_ifs at hw with heq
      · exact heq
      · exact False.elim (hw rfl)
    subst h
    exact ⟨rfl, fun j hj => False.elim (by omega)⟩
  | succ m ih =>
    obtain ⟨z, hz, hzw⟩ := map_support _ _ h hw
    have hprev : (D.encoding.base.runFrom act s m (Nat.le_of_succ_le hm)).w z.1 ≠ 0 :=
      (mul_ne_zero_iff.mp hzw).1
    have hout : (act ⟨m, hm⟩ z.1).w z.2 ≠ 0 := (mul_ne_zero_iff.mp hzw).2
    obtain ⟨hinit, hpast⟩ := ih _ z.1 hprev
    change D.encoding.base.extend ⟨m, hm⟩ z.1 z.2 = h at hz
    subst h
    refine ⟨hinit, ?_⟩
    intro j hj
    by_cases hlt : j.val < m
    · rw [beforeHistory_extend D _ _ _ _ (show j.castSucc.val ≤ m from hlt.le),
        pastRows_extend_before D _ _ _ j hlt]
      exact hpast j hlt
    · have heq : j = ⟨m, hm⟩ := Fin.ext (show j.val = m from by omega)
      subst j
      rw [beforeHistory_extend D _ _ _ _ le_rfl, beforeHistory_self,
        pastRows_extend_current]
      exact hout

theorem beforeHistory_zero (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) :
    D.beforeHistory h 0 (by simp) = D.encoding.base.initialHistory h.1 := by
  unfold LateData.beforeHistory LateProcessBase.initialHistory
  apply Prod.ext
  · rfl
  · funext b
    have hn : False := by simpa [D.encoding.base.processed_zero] using b.2
    exact hn.elim

theorem futureRisk_initial (D : LateData hPT) (s : Config D.fresh) (f : LateEvent D) :
    D.futureRisk f (D.encoding.base.initialHistory s) =
      (D.encoding.kernels.refRun s).pr (lateFailure D f) := by
  let P := D.encoding.kernels.refRun s
  let initial := D.encoding.base.initialHistory s
  have hagrees : ∀ full, P.w full ≠ 0 → D.agreesWithHistory initial full := by
    intro full hw
    have hs := (runFrom_support D D.encoding.kernels.referenceTransition s D.geom.r le_rfl full hw).1
    unfold LateData.agreesWithHistory
    rw [beforeHistory_zero, hs]
  have hden : P.pr (D.agreesWithHistory initial) = 1 := by
    calc
      _ = ∑ full, P.w full := by
        apply Finset.sum_congr rfl
        intro full _
        by_cases hw : P.w full = 0
        · simp [hw]
        · simp [hagrees full hw]
      _ = 1 := P.sum_one
  have hnum : P.pr (fun full => D.agreesWithHistory initial full ∧ lateFailure D f full) =
      P.pr (lateFailure D f) := by
    apply Finset.sum_congr rfl
    intro full _
    by_cases hw : P.w full = 0
    · simp [hw]
    · simp [hagrees full hw]
  change P.pr (fun full => D.agreesWithHistory initial full ∧ lateFailure D f full) /
    P.pr (D.agreesWithHistory initial) = _
  rw [hnum, hden, div_one]

theorem terminal_initial_incoming (D : LateData hPT) {δ ε : ℝ}
    (C : TerminalCertificate D δ ε) (x : D.encoding.InitInput)
    (hx : x ∈ terminalSet D δ) :
    0 < (D.encoding.kernels.refRun (D.encoding.initialState x)).pr
      (D.agreesWithHistory (D.encoding.base.initialHistory (D.encoding.initialState x))) ∧
    ∀ f : LateEvent D, D.futureRisk f (D.encoding.base.initialHistory (D.encoding.initialState x)) ≤
      D.threshold δ 0 := by
  have hden : (D.encoding.kernels.refRun (D.encoding.initialState x)).pr
      (D.agreesWithHistory (D.encoding.base.initialHistory (D.encoding.initialState x))) = 1 := by
    calc
      _ = ∑ h, (D.encoding.kernels.refRun (D.encoding.initialState x)).w h := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hw : (D.encoding.kernels.refRun (D.encoding.initialState x)).w h = 0
        · simp [hw]
        · have hs := (runFrom_support D D.encoding.kernels.referenceTransition
            (D.encoding.initialState x) D.geom.r le_rfl h hw).1
          have heq : D.agreesWithHistory
              (D.encoding.base.initialHistory (D.encoding.initialState x)) h := by
            unfold LateData.agreesWithHistory
            rw [beforeHistory_zero, hs]
          simp [heq]
      _ = 1 := (D.encoding.kernels.refRun (D.encoding.initialState x)).sum_one
  refine ⟨by rw [hden]; norm_num, ?_⟩
  intro f
  rw [futureRisk_initial]
  simpa only [LateData.pLate, LateData.threshold, Nat.cast_zero, zero_mul, zero_div, add_zero]
    using C.late x hx f

theorem actual_supported_full (D : LateData hPT) (hD : D.Spec)
    {δ ε K27 : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (hBroad : BroadDeletionFacts D K27) (x : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r))
    (hw : (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).w (x, h) ≠ 0)
    (henter : ∀ j : Fin D.geom.r,
      D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))) :
    D.full δ x h := by
  obtain ⟨hx, hh⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hinit, hsteps⟩ := runFrom_support D A.act (D.encoding.initialState x)
    D.geom.r le_rfl h hh
  exact full_of_entering_supported D hD C A hBroad x h hx hinit henter
    (fun j => hsteps j j.isLt)

noncomputable def reached (D : LateData hPT) (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History (Fin.last D.geom.r)) : Prop :=
  ∀ s : Fin D.geom.r, s.val < j.val →
    D.enter δ s (D.beforeHistory h s.castSucc (Nat.le_of_lt s.isLt))

theorem first_nonenter (D : LateData hPT) (δ : ℝ)
    (h : D.encoding.base.History (Fin.last D.geom.r))
    (hn : ¬ ∀ j : Fin D.geom.r,
      D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))) :
    ∃ j : Fin D.geom.r, reached D δ j h ∧
      ¬ D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) := by
  let failed := Finset.univ.filter fun j : Fin D.geom.r =>
    ¬ D.enter δ j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
  have hfailed : failed.Nonempty := by
    obtain ⟨j, hj⟩ := not_forall.mp hn
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j := failed.min' hfailed
  refine ⟨j, ?_, (Finset.mem_filter.mp (failed.min'_mem hfailed)).2⟩
  intro s hs
  by_contra hn
  have hmem : s ∈ failed := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
  have hmin := failed.min'_le s hmem
  exact (not_le_of_gt hs) hmin

/-- The only probabilistic obligation left after completion induction is
the probability of a first failed entering check at a reached history. -/
theorem fullRunProbability_of_first_stop (D : LateData hPT) (hD : D.Spec)
    {δ ε K27 εrun : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (hBroad : BroadDeletionFacts D K27)
    (hstop : (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).pr
        (fun z => ∃ j : Fin D.geom.r, reached D δ j z.2 ∧
          ¬ D.enter δ j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))) ≤ εrun) :
    FullRunProbability D C A εrun := by
  classical
  let P := FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
    (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))
  let Stop := fun z : D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r) =>
    ∃ j : Fin D.geom.r, reached D δ j z.2 ∧
      ¬ D.enter δ j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))
  have hcover : ∀ z, P.w z ≤
      (if D.full δ z.1 z.2 then P.w z else 0) + (if Stop z then P.w z else 0) := by
    intro z
    by_cases hz : P.w z = 0
    · simp [hz]
    · by_cases hs : Stop z
      · simp only [hs, if_true]
        split_ifs <;> linarith [P.nonneg z]
      · have he : ∀ j : Fin D.geom.r,
            D.enter δ j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) := by
          by_contra hn
          exact hs (first_nonenter D δ z.2 hn)
        have hf := actual_supported_full D hD C A hBroad z.1 z.2 hz he
        simp [hf, hs]
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hcover z)
  rw [Finset.sum_add_distrib, P.sum_one] at hsum
  have hStopEq : (∑ z, if Stop z then P.w z else 0) = P.pr Stop := by
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro z _
    by_cases hs : Stop z <;> simp [hs]
  rw [hStopEq] at hsum
  have hsum' : 1 ≤ P.pr (fun z => D.full δ z.1 z.2) + P.pr Stop := hsum
  change P.pr Stop ≤ εrun at hstop
  change 1 - εrun ≤ P.pr (fun z => D.full δ z.1 z.2)
  linarith only [hsum', hstop]

private theorem pr_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (F : I → Ω → Prop) :
    P.pr (fun x => ∃ i, F i x) ≤ ∑ i, P.pr (F i) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, F i x
  · obtain ⟨i, hi⟩ := hx
    rw [if_pos ⟨i, hi⟩]
    have hnneg : ∀ i ∈ Finset.univ, 0 ≤ (if F i x then P.w x else 0) := by
      intro i _
      split_ifs
      · exact P.nonneg x
      · exact le_rfl
    simpa only [hi, if_true] using
      (Finset.single_le_sum hnneg (Finset.mem_univ i))
  · have hnone : ∀ i, ¬ F i x := fun i hi => hx ⟨i, hi⟩
    simp [hx, hnone]

theorem reached_column_tail_on {Ω : Type*} [Fintype Ω] (D : LateData hPT)
    (j : Fin D.geom.r) (P : FinLaw Ω) (history : Ω → D.encoding.base.History j.castSucc)
    (Reached : Ω → Prop) (θ K : ℝ) (hθ : 0 < θ) (n : ℕ)
    (hmoment : ∀ y, P.E (fun z => if Reached z then D.columnSum j (history z) y ^ n else 0) ≤ K) :
    ∀ y, P.pr (fun z => Reached z ∧ θ < D.columnSum j (history z) y) ≤ K / θ ^ n := by
  intro y
  apply (le_div_iff₀ (pow_pos hθ n)).mpr
  apply le_trans _ (hmoment y)
  unfold FinLaw.pr FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  have hc : 0 ≤ D.columnSum j (history z) y := by
    unfold LateData.columnSum FinLaw.pr
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun out _ => by
      split_ifs; exact FinLaw.nonneg _ out; exact le_rfl
  by_cases hr : Reached z
  · by_cases ht : θ < D.columnSum j (history z) y
    · simp only [hr, ht, and_self, if_true]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ.le ht.le n) (P.nonneg z)
    · simp only [hr, ht, and_false, if_false, if_true, zero_mul]
      exact mul_nonneg (P.nonneg z) (pow_nonneg hc n)
  · simp [hr]

/-- Incoming-risk/support induction and the reached moments suffice for the
whole run. The probability estimate here reads the actual class-run law. -/
theorem fullRunProbability_of_reached_moments (D : LateData hPT) (hD : D.Spec)
    {δ ε K27 : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (hBroad : BroadDeletionFacts D K27) (hθ : 0 < κ.θ0) (m : ℕ) (M : Fin D.geom.r → ℝ)
    (hincoming : ∀ x h,
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).w (x, h) ≠ 0 →
      ∀ j : Fin D.geom.r, reached D δ j h →
      let before := D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)
      0 < (D.encoding.kernels.refRun before.1).pr (D.agreesWithHistory before) ∧
        ∀ f : LateEvent D, j.val ≤ f.2.1.val → D.futureRisk f before ≤ D.threshold δ j.val)
    (hmoments : ∀ j y,
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then
          D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ m else 0) ≤ M j) :
    FullRunProbability D C A ((T.S.N k : ℝ) * ∑ j, M j / κ.θ0 ^ m) := by
  let P := FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
    (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))
  let Fail := fun j (z : D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r)) =>
    reached D δ j z.2 ∧ ¬ D.enter δ j
      (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))
  let Column := fun j y (z : D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r)) =>
    reached D δ j z.2 ∧ κ.θ0 < D.columnSum j
      (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y
  have hreduce : ∀ j, P.pr (Fail j) ≤ P.pr (fun z => ∃ y, Column j y z) := by
    intro j
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : P.w z = 0
    · simp [hz]
    · by_cases hf : Fail j z
      · obtain ⟨hp, hr⟩ := hincoming z.1 z.2 hz j hf.1
        have hcol : ∃ y, Column j y z := by
          have hn : ¬ ∀ y, D.columnSum j
              (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ≤ κ.θ0 := by
            intro hc
            exact hf.2 ⟨hp, hr, hc⟩
          obtain ⟨y, hy⟩ := not_forall.mp hn
          exact ⟨y, hf.1, lt_of_not_ge hy⟩
        simp [hf, hcol]
      · simp only [hf, if_false]
        split_ifs; exact P.nonneg z; exact le_rfl
  apply fullRunProbability_of_first_stop D hD C A hBroad
  calc
    _ ≤ ∑ j, P.pr (Fail j) := pr_exists_le_sum P Fail
    _ ≤ ∑ j, P.pr (fun z => ∃ y, Column j y z) := Finset.sum_le_sum fun j _ => hreduce j
    _ ≤ ∑ j, ∑ y : Fin (T.S.N k), P.pr (Column j y) :=
      Finset.sum_le_sum fun j _ => pr_exists_le_sum P (Column j)
    _ ≤ ∑ j, ∑ _y : Fin (T.S.N k), M j / κ.θ0 ^ m := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro y _
      exact reached_column_tail_on D j P
        (fun z => D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))
        (fun z => reached D δ j z.2) κ.θ0 (M j) hθ m (hmoments j) y
    _ = _ := by simp [Finset.mul_sum]

end HypercubeRamsey.S18.Lane_sol_s18_n5
