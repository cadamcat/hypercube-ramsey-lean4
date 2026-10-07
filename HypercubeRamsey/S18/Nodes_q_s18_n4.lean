import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_q_s18_n4

open Classical
open scoped BigOperators

theorem upstreamBadPinnedBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (hD : D.Spec)
    (pin : Option (S18.SlotPin D)) (f : D.geom.Cell ⊕ Pos T k)
    (hn : 1 ≤ T.S.n k) :
    S18.initialProbability D pin (D.upstreamBad f) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  have hn' : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  have hP : 0 ≤ (κ.P : ℝ) := by positivity
  have hTs : 0 ≤ (D.encoding.Ts : ℝ) := by positivity
  have hexp : -((κ.P : ℝ) * D.encoding.Ts / 2) ≤
      -((κ.P : ℝ) * D.encoding.Ts / 3) := by
    have hmul : 0 ≤ (κ.P : ℝ) * D.encoding.Ts := mul_nonneg hP hTs
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn' hexp
  cases pin with
  | none =>
      simpa [S18.initialProbability] using (le_trans (hD.upstream_bad f) hpow)
  | some p =>
      rcases p with ⟨C, slot, bin⟩
      change (D.encoding.permLaw.pr
          (fun x => x.1 C slot = bin ∧ D.upstreamBad f x) /
          D.encoding.permLaw.pr (fun x => x.1 C slot = bin)) ≤ _
      exact le_trans (hD.upstream_bad_pinned C slot bin f) hpow

theorem terminalSet_properties
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (x : D.encoding.InitInput) (hx : x ∈ S18.terminalSet D δ) :
    D.poolGood x ∧
      (∀ v, ¬ D.encoding.events.S v (D.encoding.initialState x)) ∧
      (∀ f, D.pLate f x ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) δ)) := by
  classical
  have hAvoid : ∀ f, ¬ S18.terminalFailure D δ f x := by
    simpa [S18.terminalSet] using hx
  have hTypical : ∀ C, D.fresh.typical C (x.1 C) := by
    intro C
    by_contra hbad
    exact hAvoid (.inl (.inl C)) (by simpa [S18.terminalFailure] using hbad)
  have hList : ∀ v, D.poolListOK x.1 v := by
    intro v
    by_contra hbad
    exact hAvoid (.inl (.inr v)) (by simpa [S18.terminalFailure] using hbad)
  have hInitialGate : ∀ v, D.poolGate (D.initialRegion v) x := by
    intro v
    constructor
    · exact fun C hC => hTypical C
    · intro w hscope
      exact hList w
  have hInitial : ∀ v, ¬ D.encoding.events.S v (D.encoding.initialState x) := by
    intro v hS
    have h := hAvoid (.inr (.inl v))
    exact h (by simpa [S18.terminalFailure] using ⟨hInitialGate v, hS⟩)
  have hLate : ∀ f, D.pLate f x ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) δ) := by
    intro f
    by_contra hlarge
    have hthreshold : Real.exp (-Real.rpow (T.S.n k : ℝ) δ) < D.pLate f x :=
      lt_of_not_ge hlarge
    have hLateGate : D.poolGate (D.lateRegion f) x := by
      constructor
      · exact fun C hC => hTypical C
      · intro v hscope
        exact hList v
    have h := hAvoid (.inr (.inr f))
    exact h (by simpa [S18.terminalFailure] using
      ⟨hLateGate, hthreshold⟩)
  exact ⟨⟨hTypical, hList⟩, hInitial, hLate⟩

theorem terminalCertificateOfBounds
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ ε : ℝ)
    (hpos : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    (hcomparison : ∀ seed : Finset D.geom.Cell,
      (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      ∀ Ψ : D.encoding.InitInput → ℝ, (∀ x, 0 ≤ Ψ x) →
      (∀ x x', (∀ C ∈ D.expandCells seed,
        x.1 C = x'.1 C ∧ x.2 C = x'.2 C) → Ψ x = Ψ x') →
      (D.encoding.terminalLaw (S18.terminalSet D δ) hpos).E Ψ ≤
        (1 + ε) * D.encoding.permLaw.E Ψ) :
    S18.TerminalCertificate D δ ε := by
  classical
  refine ⟨hpos, ?_, ?_, ?_, hcomparison⟩
  · intro x hx
    exact (terminalSet_properties D δ x hx).1
  · intro x hx
    exact (terminalSet_properties D δ x hx).2.1
  · intro x hx
    exact (terminalSet_properties D δ x hx).2.2

theorem leafProbabilityBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (L : S18.LeafCoupling D δ)
    (leaf : L.Leaf) :
    D.encoding.permLaw.pr (fun x => x ∈ L.leaf leaf) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  classical
  have hsubset : ∀ x, x ∈ L.leaf leaf →
      S18.terminalFailure D δ (L.requirement leaf) x := by
    intro x hx
    exact (L.covers (L.requirement leaf) x).2 ⟨leaf, rfl, hx⟩
  have hmono : D.encoding.permLaw.pr (fun x => x ∈ L.leaf leaf) ≤
      D.encoding.permLaw.pr (S18.terminalFailure D δ (L.requirement leaf)) := by
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro x hx
    by_cases hleaf : x ∈ L.leaf leaf
    · simp [hleaf, hsubset x hleaf]
    · by_cases hfail : S18.terminalFailure D δ (L.requirement leaf) x
      · simp only [if_neg hleaf, if_pos hfail]
        exact D.encoding.permLaw.nonneg x
      · simp [hleaf, hfail]
  have h := hRisk none (L.requirement leaf)
  simpa [S18.initialProbability] using le_trans hmono h

private theorem runRounds_succ {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : ListEvent F) (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, F.Pool C) (tapes : ∀ C, ℕ → TapeEntry F C) :
    E.runRounds (Ts + 1) order events pools tapes =
      E.round order events pools tapes
        (E.runRounds Ts order events pools tapes).1
        (E.runRounds Ts order events pools tapes).2 := by
  rfl

private theorem replayRounds_succ {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (marked : Finset (Pos T k)) (pattern : ℕ → Finset (Pos T k))
    (x : D.encoding.InitInput) (t : ℕ) :
    S18.replayRounds D marked pattern x (t + 1) =
      let prev := S18.replayRounds D marked pattern x t
      let selected := (pattern t ∩ marked) ∪
        (D.encoding.events.active D.encoding.order Finset.univ prev.1 \ marked)
      let touches := fun C => ∃ v ∈ selected, C ∈ D.encoding.events.scope v
      ((fun C => if touches C then x.2.extend C (prev.2 C + 1) (x.1 C) else prev.1 C),
       fun C => if touches C then prev.2 C + 1 else prev.2 C) := by
  rfl

private theorem replay_agreement {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT) :
    S18.ReplayAgreement D := by
  intro marked x t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [replayRounds_succ, runRounds_succ, ih]
      have hsel :
          (S18.actualPattern D marked x t ∩ marked) ∪
              (D.encoding.events.active D.encoding.order Finset.univ
                (D.encoding.events.runRounds t D.encoding.order Finset.univ x.1 x.2.extend).1 \ marked) =
            D.encoding.events.active D.encoding.order Finset.univ
              (D.encoding.events.runRounds t D.encoding.order Finset.univ x.1 x.2.extend).1 := by
        rw [S18.actualPattern]
        ext v
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      dsimp only
      rw [hsel]
      rfl

private theorem event_touches_mem_buffer {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) {v : Pos T k}
    (h : ∃ C ∈ critical, C ∈ D.encoding.events.scope v) :
    v ∈ S18.replayMarked D critical := by
  rcases h with ⟨C, hC, hscope⟩
  change v ∈ (critical.biUnion D.encoding.events.incidentEvents) ∪ _
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_biUnion.mpr ⟨C, hC,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hscope⟩⟩)

private theorem adjacent_symm {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (E : ListEvent F) {v u : Pos T k} (h : E.Adjacent u v) : E.Adjacent v u := by
  rcases h with ⟨hne, hdis⟩
  refine ⟨hne.symm, ?_⟩
  intro hdis'
  exact hdis (disjoint_comm.mp hdis')

private theorem buffer_of_touch_adjacent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) {v u : Pos T k}
    (hu : ∃ C ∈ critical, C ∈ D.encoding.events.scope u)
    (hvu : D.encoding.events.Adjacent v u) :
    v ∈ S18.replayMarked D critical := by
  rcases hu with ⟨C, hC, hscope⟩
  change v ∈ (critical.biUnion D.encoding.events.incidentEvents) ∪ _
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨u, Finset.mem_biUnion.mpr ⟨C, hC,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hscope⟩⟩, hvu⟩

private theorem active_iff_of_outside {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (s s' : Config D.fresh)
    (hcfg : ∀ C, C ∉ critical → s C = s' C) {v : Pos T k}
    (hv : v ∉ S18.replayMarked D critical) :
    (v ∈ D.encoding.events.active order events s ↔
      v ∈ D.encoding.events.active order events s') := by
  have hvAvoid : ∀ C ∈ D.encoding.events.scope v, C ∉ critical := by
    intro C hscope hC
    exact hv (event_touches_mem_buffer D critical ⟨C, hC, hscope⟩)
  have hvS : D.encoding.events.S v s ↔ D.encoding.events.S v s' :=
    D.encoding.events.scope_ok v s s' (fun C hC => hcfg C (hvAvoid C hC))
  simp only [ListEvent.active, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hm, hS, hprior⟩
    refine ⟨hm, hvS.mp hS, ?_⟩
    intro u hu hbefore hadj
    have huAvoid : ∀ C ∈ D.encoding.events.scope u, C ∉ critical := by
      intro C hscope hC
      exact hv (buffer_of_touch_adjacent D critical ⟨C, hC, hscope⟩
        (adjacent_symm D.encoding.events hadj))
    have huS : D.encoding.events.S u s ↔ D.encoding.events.S u s' :=
      D.encoding.events.scope_ok u s s' (fun C hC => hcfg C (huAvoid C hC))
    intro huS'
    exact hprior u hu hbefore hadj (huS.mpr huS')
  · rintro ⟨hm, hS, hprior⟩
    refine ⟨hm, hvS.mpr hS, ?_⟩
    intro u hu hbefore hadj
    have huAvoid : ∀ C ∈ D.encoding.events.scope u, C ∉ critical := by
      intro C hscope hC
      exact hv (buffer_of_touch_adjacent D critical ⟨C, hC, hscope⟩
        (adjacent_symm D.encoding.events hadj))
    have hEq : D.encoding.events.S u s ↔ D.encoding.events.S u s' :=
      D.encoding.events.scope_ok u s s' (fun C hC => hcfg C (huAvoid C hC))
    intro hS
    exact hprior u hu hbefore hadj (hEq.mp hS)

private theorem replay_selected_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) (pattern : ℕ → Finset (Pos T k))
    (x x' : D.encoding.InitInput) (t : ℕ)
    (hcfg : ∀ C, C ∉ critical →
      (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1 C =
        (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 C) :
    (pattern t ∩ S18.replayMarked D critical) ∪
        (D.encoding.events.active D.encoding.order Finset.univ
          (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1 \
          S18.replayMarked D critical) =
      (pattern t ∩ S18.replayMarked D critical) ∪
        (D.encoding.events.active D.encoding.order Finset.univ
          (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 \
          S18.replayMarked D critical) := by
  apply Finset.ext
  intro v
  by_cases hv : v ∈ S18.replayMarked D critical
  · simp [hv]
  · have hactive := active_iff_of_outside D critical D.encoding.order Finset.univ
      (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1
      (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 hcfg hv
    simp [hv, hactive]

private theorem replay_outside {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) (pattern : ℕ → Finset (Pos T k))
    (x x' : D.encoding.InitInput)
    (hinput : ∀ C, C ∉ critical → x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    ∀ t C, C ∉ critical →
      (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1 C =
        (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 C ∧
      (S18.replayRounds D (S18.replayMarked D critical) pattern x t).2 C =
        (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).2 C := by
  intro t
  induction t with
  | zero =>
      intro C hC
      rcases hinput C hC with ⟨hpool, htape⟩
      constructor
      · change x.2.extend C 0 (x.1 C) = x'.2.extend C 0 (x'.1 C)
        simp [Tapes.extend, hpool, htape]
      · rfl
  | succ t ih =>
      intro C hC
      have hcfg : ∀ C, C ∉ critical →
          (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1 C =
            (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 C :=
        fun C hC => (ih C hC).1
      have hsel := replay_selected_eq D critical pattern x x' t hcfg
      rcases ih C hC with ⟨hstate, hcount⟩
      rcases hinput C hC with ⟨hpool, htape⟩
      rw [replayRounds_succ, replayRounds_succ]
      constructor
      · dsimp only
        simp only [hsel]
        by_cases ht : ∃ v ∈ (pattern t ∩ S18.replayMarked D critical) ∪
            (D.encoding.events.active D.encoding.order Finset.univ
              (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 \
              S18.replayMarked D critical),
              C ∈ D.encoding.events.scope v
        · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at ht ⊢
          simp [ht, Tapes.extend, hpool, htape, hcount]
        · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at ht ⊢
          simp [ht, hstate]
      · dsimp only
        simp only [hsel]
        by_cases ht : ∃ v ∈ (pattern t ∩ S18.replayMarked D critical) ∪
            (D.encoding.events.active D.encoding.order Finset.univ
              (S18.replayRounds D (S18.replayMarked D critical) pattern x' t).1 \
              S18.replayMarked D critical),
              C ∈ D.encoding.events.scope v
        · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at ht ⊢
          simp [ht, hcount]
        · simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at ht ⊢
          simp [ht, hcount]

private theorem replay_critical_counter {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT)
    (critical : Finset (D.geom.Cell)) (pattern : ℕ → Finset (Pos T k))
    (x : D.encoding.InitInput) :
    ∀ t C, C ∈ critical →
      (S18.replayRounds D (S18.replayMarked D critical) pattern x t).2 C =
        ∑ j ∈ Finset.range t,
          if ∃ v ∈ pattern j ∩ S18.replayMarked D critical,
              C ∈ D.encoding.events.scope v then 1 else 0 := by
  intro t
  induction t with
  | zero =>
      intro C hC
      simp [S18.replayRounds]
  | succ t ih =>
      intro C hC
      have htouch :
          (∃ v ∈ (pattern t ∩ S18.replayMarked D critical) ∪
            (D.encoding.events.active D.encoding.order Finset.univ
              (S18.replayRounds D (S18.replayMarked D critical) pattern x t).1 \
              S18.replayMarked D critical), C ∈ D.encoding.events.scope v) ↔
          ∃ v ∈ pattern t ∩ S18.replayMarked D critical,
            C ∈ D.encoding.events.scope v := by
        constructor
        · rintro ⟨v, hv, hscope⟩
          rcases Finset.mem_union.mp hv with hforced | hordinary
          · exact ⟨v, hforced, hscope⟩
          · have hmarked := event_touches_mem_buffer D critical ⟨C, hC, hscope⟩
            exact False.elim ((Finset.mem_sdiff.mp hordinary).2 hmarked)
        · rintro ⟨v, hv, hscope⟩
          exact ⟨v, Finset.mem_union.mpr (Or.inl hv), hscope⟩
      rw [replayRounds_succ]
      dsimp only
      simp only [htouch, Finset.sum_range_succ]
      by_cases h : ∃ v ∈ pattern t ∩ S18.replayMarked D critical,
          C ∈ D.encoding.events.scope v
      · have h' : ∃ v, (v ∈ pattern t ∧ v ∈ S18.replayMarked D critical) ∧
            C ∈ D.encoding.events.scope v := by
          simpa only [Finset.mem_inter] using h
        simp [h', ih C hC]
      · have h' : ¬ ∃ v, (v ∈ pattern t ∧ v ∈ S18.replayMarked D critical) ∧
            C ∈ D.encoding.events.scope v := by
          simpa only [Finset.mem_inter] using h
        simp [h', ih C hC]

theorem replay_facts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : S18.LateData hPT) :
    S18.ReplayFacts D := by
  refine ⟨replay_agreement D, ?_, ?_⟩
  · intro critical pattern x x' t hinput C hC
    exact replay_outside D critical pattern x x' hinput t C hC
  · intro critical pattern x t C hC
    exact replay_critical_counter D critical pattern x t C hC

end HypercubeRamsey.Lane_q_s18_n4
