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

private theorem finLawPr_eq_mass_filter
    {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = LocalLemma.mass P.w (Finset.univ.filter A) := by
  classical
  simp [FinLaw.pr, LocalLemma.mass, Finset.sum_filter]

private theorem prodOneSubLower
    {I : Type*} [DecidableEq I] (S : Finset I) (q : I → ℝ)
    (hq0 : ∀ i ∈ S, 0 ≤ q i) (hq1 : ∀ i ∈ S, q i ≤ 1) :
    1 - ∑ i ∈ S, q i ≤ ∏ i ∈ S, (1 - q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hi0 := hq0 i (Finset.mem_insert_self i S)
      have hi1 := hq1 i (Finset.mem_insert_self i S)
      have hq0' : ∀ j ∈ S, 0 ≤ q j := fun j hj => hq0 j (Finset.mem_insert_of_mem hj)
      have hq1' : ∀ j ∈ S, q j ≤ 1 := fun j hj => hq1 j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ S, q j := Finset.sum_nonneg fun j hj => hq0' j hj
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (q i + ∑ j ∈ S, q j) ≤ (1 - q i) * (1 - ∑ j ∈ S, q j) := by
          nlinarith [mul_nonneg hi0 hsum0]
        _ ≤ (1 - q i) * ∏ j ∈ S, (1 - q j) :=
          mul_le_mul_of_nonneg_left (ih hq0' hq1') (sub_nonneg.mpr hi1)

theorem leafAvoidancePositive
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2) :
    0 < ∑ x ∈ Finset.univ.filter (fun x : D.encoding.InitInput =>
      ∀ i, x ∉ L.leaf i), D.encoding.permLaw.w x := by
  classical
  let p : L.Leaf → ℝ := fun i => D.encoding.permLaw.pr (fun x => x ∈ L.leaf i)
  let q : L.Leaf → ℝ := fun i => 2 * p i
  let adj : L.Leaf → L.Leaf → Prop := fun i j => j ≠ i ∧ L.adjacent i j
  letI : DecidableRel adj := Classical.decRel _
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    unfold p FinLaw.pr
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact D.encoding.permLaw.nonneg x
    · exact le_rfl
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (by norm_num) (hp0 i)
  have hqLt : ∀ i, q i < 1 := by
    intro i
    have hi := hprob i
    dsimp [q, p] at hi ⊢
    linarith
  have hq1 : ∀ i, q i ≤ 1 := fun i => (hqLt i).le
  have hsymm : ∀ i j, adj i j → adj j i := by
    intro i j hij
    rcases hij with ⟨hne, hadj⟩
    refine ⟨hne.symm, ?_⟩
    apply (L.adjacent_eq j i).mpr
    rcases (L.adjacent_eq i j).mp hadj with hdom | himage | htape
    · exact Or.inl (by
        intro hdis
        exact hdom (disjoint_comm.mp hdis))
    · exact Or.inr (Or.inl (by
        intro hdis
        exact himage (disjoint_comm.mp hdis)))
    · exact Or.inr (Or.inr (by
        intro hdis
        exact htape (disjoint_comm.mp hdis)))
  have hirr : ∀ i, ¬ adj i i := by
    intro i hi
    exact hi.1 rfl
  have hcond : ∀ i (S : Finset L.Leaf), i ∉ S →
      (∀ j ∈ S, ¬ adj i j) →
      LocalLemma.mass D.encoding.permLaw.w
          (L.leaf i ∩ LocalLemma.avoid L.leaf S) ≤
        p i * LocalLemma.mass D.encoding.permLaw.w
          (LocalLemma.avoid L.leaf S) := by
    intro i S hiS hnon
    have hnon' : ∀ j ∈ S, ¬ L.adjacent i j := by
      intro j hj hadj
      have hji : j ≠ i := by
        intro hEq
        exact hiS (hEq ▸ hj)
      exact hnon j hj ⟨hji, hadj⟩
    have hraw := L.nonneighbor_bound i S hnon'
    have hnum : LocalLemma.mass D.encoding.permLaw.w
        (L.leaf i ∩ LocalLemma.avoid L.leaf S) =
        D.encoding.permLaw.pr (fun x => x ∈ L.leaf i ∧ ∀ j ∈ S, x ∉ L.leaf j) := by
      rw [finLawPr_eq_mass_filter]
      congr 1
      ext x
      simp [LocalLemma.avoid]
    have hden : LocalLemma.mass D.encoding.permLaw.w
        (LocalLemma.avoid L.leaf S) =
        D.encoding.permLaw.pr (fun x => ∀ j ∈ S, x ∉ L.leaf j) := by
      rw [finLawPr_eq_mass_filter]
      congr 1
      ext x
      simp [LocalLemma.avoid]
    rw [← hnum, ← hden] at hraw
    simpa [p] using hraw
  have hneighborCharge : ∀ i,
      (∑ j ∈ Finset.univ.filter (adj i), q j) ≤ 1 / 2 := by
    intro i
    have hcharge' :
        (∑ j ∈ Finset.univ.filter (fun j => L.adjacent i j), q j) ≤ 1 / 2 := by
      simpa [q, p, Finset.sum_filter] using hcharge i
    have hsub : Finset.univ.filter (adj i) ⊆
        Finset.univ.filter (fun j => L.adjacent i j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        (Finset.mem_filter.mp hj).2.2⟩
    calc
      (∑ j ∈ Finset.univ.filter (adj i), q j) ≤
          ∑ j ∈ Finset.univ.filter (fun j => L.adjacent i j), q j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hq0 j)
      _ ≤ 1 / 2 := hcharge'
  have hpx : ∀ i, p i ≤ q i *
      ∏ j ∈ Finset.univ.filter (adj i), (1 - q j) := by
    intro i
    have hprod := prodOneSubLower (Finset.univ.filter (adj i)) q
      (fun j hj => hq0 j) (fun j hj => hq1 j)
    have hsum : ∑ j ∈ Finset.univ.filter (adj i), q j ≤ 1 / 2 := hneighborCharge i
    have hprodHalf : 1 / 2 ≤ ∏ j ∈ Finset.univ.filter (adj i), (1 - q j) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hprodHalf (hq0 i)
    dsimp [q]
    nlinarith
  have hLLL := LocalLemma.conditional_avoidance
    D.encoding.permLaw.w D.encoding.permLaw.nonneg D.encoding.permLaw.sum_one
    L.leaf adj hsymm hirr p q hcond hq0 hqLt hpx
  simpa [LocalLemma.mass, LocalLemma.avoid] using hLLL.1

theorem terminalSetAvoidLeaves
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (x : D.encoding.InitInput) :
    x ∈ S18.terminalSet D δ ↔ ∀ i, x ∉ L.leaf i := by
  classical
  constructor
  · intro hx i hi
    have hgood : ∀ f, ¬ S18.terminalFailure D δ f x := by
      simpa [S18.terminalSet] using hx
    have hfail := (L.covers (L.requirement i) x).2 ⟨i, rfl, hi⟩
    exact hgood (L.requirement i) hfail
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro f hfail
    obtain ⟨i, hreq, hleaf⟩ := (L.covers f x).1 hfail
    exact hx i hleaf

theorem terminalSetPositiveOfLeafBounds
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2) :
    0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x := by
  have hpos := leafAvoidancePositive D δ L hprob hcharge
  have hEq : S18.terminalSet D δ = Finset.univ.filter
      (fun x : D.encoding.InitInput => ∀ i, x ∉ L.leaf i) := by
    ext x
    simpa using terminalSetAvoidLeaves D δ L x
  rw [hEq]
  exact hpos

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
