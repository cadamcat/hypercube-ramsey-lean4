import HypercubeRamsey.S18.Prefix_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def lateSeedCells (D : S18.LateData hPT) (F : S18.LateEvent D) : Finset D.geom.Cell :=
  (cubeBall F.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells

noncomputable def lateRestrictedEvents (D : S18.LateData hPT) (F : S18.LateEvent D) :
    Finset (Pos T k) :=
  D.encoding.events.graphBall
    ((lateSeedCells D F).biUnion D.encoding.events.incidentEvents) (2 * D.encoding.Ts + 3)

private theorem seed_in_graphBall (D : S18.LateData hPT) (sites : Finset (Pos T k)) (r : ℕ) :
    sites ⊆ D.encoding.events.graphBall sites r := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact fun _ hx => Finset.mem_union.mpr (Or.inl (ih hx))

private theorem ball_radius_mono (D : S18.LateData hPT) (sites : Finset (Pos T k))
    {m r : ℕ} (hm : m ≤ r) : D.encoding.events.graphBall sites m ⊆
      D.encoding.events.graphBall sites r := by
  induction r with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    exact Finset.Subset.refl _
  | succ r ih =>
    by_cases heq : m = r + 1
    · subst m; exact Finset.Subset.refl _
    · exact fun _ hv => Finset.mem_union.mpr (Or.inl (ih (by omega) hv))

private theorem ball_add (D : S18.LateData hPT) (A B : Finset (Pos T k)) (m : ℕ)
    (hA : A ⊆ D.encoding.events.graphBall B m) (r : ℕ) :
    D.encoding.events.graphBall A r ⊆ D.encoding.events.graphBall B (m + r) := by
  induction r with
  | zero => simpa only [ListEvent.graphBall, Nat.add_zero] using hA
  | succ r ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ball_radius_mono D B (by omega) (ih hv)
    · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
      have hmem : v ∈ D.encoding.events.graphBall B (m + r + 1) :=
        Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ih hu, hadj⟩))
      simpa only [Nat.add_assoc] using hmem

/-- Priority decisions at round r need one more neighbor than event truth.
This is the deterministic step needed to transfer a backward closure. -/
theorem activeRoundLocality (D : S18.LateData hPT) (r : ℕ)
    (pools : ∀ C, D.fresh.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.fresh C)
    (events : Finset (Pos T k)) (v : Pos T k)
    (hball : D.encoding.events.graphBall {v} (2 * r + 4) ⊆ events) :
    (v ∈ D.encoding.events.active D.encoding.order Finset.univ
      (D.encoding.events.runRounds r D.encoding.order Finset.univ pools tapes).1) ↔
    (v ∈ D.encoding.events.active D.encoding.order events
      (D.encoding.events.runRounds r D.encoding.order events pools tapes).1) := by
  let E := D.encoding.events
  have hloc := (resampleLocality (D := Lane_q_s18_n4.lateListContext D) E r
    D.encoding.order pools tapes).2
  have hvE : v ∈ events := hball
    (seed_in_graphBall D {v} _ (Finset.mem_singleton_self v))
  have htruth := hloc v events ((ball_radius_mono D {v} (by omega)).trans hball)
  have hn (u : Pos T k) (hadj : E.Adjacent u v) :
      u ∈ events ∧ (E.S u (E.runRounds r D.encoding.order Finset.univ pools tapes).1 ↔
        E.S u (E.runRounds r D.encoding.order events pools tapes).1) := by
    have hu1 : u ∈ E.graphBall {v} 1 := Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, Finset.mem_singleton_self v, hadj⟩))
    have hseed : {u} ⊆ E.graphBall {v} 1 := by
      intro w hw
      have hwu : w = u := Finset.mem_singleton.mp hw
      simpa [hwu] using hu1
    have hsub := (ball_add D {u} {v} 1 hseed (2 * r + 3)).trans
      ((ball_radius_mono D {v} (by omega)).trans hball)
    exact ⟨hball (ball_radius_mono D {v} (by omega) hu1), hloc u events hsub⟩
  simp only [ListEvent.active, Finset.mem_filter, Finset.mem_univ, true_and, true_implies]
  constructor
  · intro h
    refine ⟨hvE, htruth.mp h.1, ?_⟩
    intro u hu hbefore hadj
    exact (hn u hadj).2.not.mp (h.2 u hbefore hadj)
  · intro h
    refine ⟨htruth.mpr h.2.1, ?_⟩
    intro u hbefore hadj
    exact (hn u hadj).2.not.mpr (h.2.2 u (hn u hadj).1 hbefore hadj)

/-- Scope overlap advances a graph-ball radius by at most one, including
repeated executions of the same event. -/
private theorem overlap_step (D : S18.LateData hPT) (seeds : Finset (Pos T k))
    (r : ℕ) {v w : Pos T k} (hv : v ∈ D.encoding.events.graphBall seeds r)
    (hvw : ¬ Disjoint (D.encoding.events.scope v) (D.encoding.events.scope w)) :
    w ∈ D.encoding.events.graphBall seeds (r + 1) := by
  by_cases heq : w = v
  · subst w
    exact ball_radius_mono D seeds (by omega) hv
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, v, hv, heq, fun h => hvw h.symm⟩))

/-- A backward path gains at most one graph step per lost round. -/
private theorem backwardPath_radius (D : S18.LateData hPT)
    (seeds events : Finset (Pos T k)) (pools : ∀ C, D.fresh.Pool C)
    (tapes : Tapes D.fresh D.encoding.Ts)
    (seed o : ExecutionOccurrence T k D.encoding.Ts)
    (hseed : seed.1 ∈ D.encoding.events.graphBall seeds 1)
    (hp : Relation.ReflTransGen
      (backwardOccurrenceEdge (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.order events pools tapes) seed o) :
    o.1 ∈ D.encoding.events.graphBall seeds (D.encoding.Ts - o.2.val) := by
  induction hp with
  | refl => exact ball_radius_mono D seeds (by have := seed.2.isLt; omega) hseed
  | @tail b c hbc he ih =>
    have hstep := overlap_step D seeds _ ih he.2.2.2
    exact ball_radius_mono D seeds (by have := he.2.2.1; have := b.2.isLt; omega) hstep

/-- Transfer a backward path whenever executions agree in its radius envelope. -/
private theorem backwardPath_transfer (D : S18.LateData hPT)
    (seeds eventsA eventsB : Finset (Pos T k)) (pools : ∀ C, D.fresh.Pool C)
    (tapes : Tapes D.fresh D.encoding.Ts)
    (hexec : ∀ o : ExecutionOccurrence T k D.encoding.Ts,
      o.1 ∈ D.encoding.events.graphBall seeds (D.encoding.Ts - o.2.val) →
      (occurrenceExecuted (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.Ts D.encoding.order eventsA pools tapes o ↔
       occurrenceExecuted (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.Ts D.encoding.order eventsB pools tapes o))
    (seed o : ExecutionOccurrence T k D.encoding.Ts)
    (hseed : seed.1 ∈ D.encoding.events.graphBall seeds 1)
    (hp : Relation.ReflTransGen
      (backwardOccurrenceEdge (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.order eventsA pools tapes) seed o) :
    Relation.ReflTransGen
      (backwardOccurrenceEdge (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.order eventsB pools tapes) seed o := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc he ih =>
    have hb := backwardPath_radius D seeds eventsA pools tapes seed b hseed hbc
    have hc := backwardPath_radius D seeds eventsA pools tapes seed c hseed (hbc.tail he)
    exact ih.tail ⟨(hexec b hb).mp he.1, (hexec c hc).mp he.2.1, he.2.2⟩

/-- The late gate contains all decisions along both backward executions.
The decreasing round index pays for each additional scope-graph step. -/
theorem replayBackwardClosure_eq_restricted (D : S18.LateData hPT)
    (F : S18.LateEvent D) (hvalid : D.prefixValid F.2) (omitted : Option D.geom.Cell)
    (fixed : Config D.fresh) (x : D.encoding.InitInput) :
    let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
    replayBackwardClosure D X.criticalCells x =
      backwardClosure (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.order (lateRestrictedEvents D F)
        x.1 x.2 (replayTargets D X.criticalCells) := by
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
  let seeds := (lateSeedCells D F).biUnion D.encoding.events.incidentEvents
  let events := lateRestrictedEvents D F
  let E := D.encoding.events
  let Ctx := Lane_q_s18_n4.lateListContext D
  have hexec (o : ExecutionOccurrence T k D.encoding.Ts)
      (ho : o.1 ∈ E.graphBall seeds (D.encoding.Ts - o.2.val)) :
      occurrenceExecuted (D := Ctx) E D.encoding.Ts D.encoding.order Finset.univ x.1 x.2 o ↔
      occurrenceExecuted (D := Ctx) E D.encoding.Ts D.encoding.order events x.1 x.2 o := by
    apply activeRoundLocality D o.2.val x.1 x.2.extend events o.1
    have hseed : {o.1} ⊆ E.graphBall seeds (D.encoding.Ts - o.2.val) := by
      intro v hv
      simpa only [Finset.mem_singleton.mp hv] using ho
    exact (ball_add D {o.1} seeds _ hseed (2 * o.2.val + 4)).trans
      (ball_radius_mono D seeds (by have := o.2.isLt; omega))
  have hnear (o : ExecutionOccurrence T k D.encoding.Ts)
      (htarget : ∃ C, C ∈ replayTargets D X.criticalCells ∧ C ∈ E.scope o.1) :
      o.1 ∈ E.graphBall seeds 1 := by
    obtain ⟨C, hC, hCo⟩ := htarget
    obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨C', hC', hvC'⟩ := Finset.mem_biUnion.mp hv
    have hvSeed : v ∈ seeds := Finset.mem_biUnion.mpr
      ⟨C', criticalCells_in_seed D F hvalid omitted fixed hC', hvC'⟩
    have hover : ¬ Disjoint (E.scope v) (E.scope o.1) :=
      Finset.not_disjoint_iff.mpr ⟨C, hCv, hCo⟩
    exact overlap_step D seeds 0 hvSeed hover
  change replayBackwardClosure D X.criticalCells x =
    backwardClosure (D := Ctx) E D.encoding.order events x.1 x.2
      (replayTargets D X.criticalCells)
  apply Finset.ext
  intro o
  simp only [replayBackwardClosure, backwardClosure, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ho, seed, hseed, ht, hp⟩
    have hs := hnear seed ht
    have hrad := backwardPath_radius D seeds Finset.univ x.1 x.2 seed o hs hp
    refine ⟨(hexec o hrad).mp ho, seed,
      (hexec seed (ball_radius_mono D seeds (by have := seed.2.isLt; omega) hs)).mp hseed, ht, ?_⟩
    exact backwardPath_transfer D seeds Finset.univ events x.1 x.2 hexec seed o hs hp
  · rintro ⟨ho, seed, hseed, ht, hp⟩
    have hs := hnear seed ht
    have hrad := backwardPath_radius D seeds events x.1 x.2 seed o hs hp
    refine ⟨(hexec o hrad).mpr ho, seed,
      (hexec seed (ball_radius_mono D seeds (by have := seed.2.isLt; omega) hs)).mpr hseed, ht, ?_⟩
    exact backwardPath_transfer D seeds events Finset.univ x.1 x.2
      (fun o ho => (hexec o ho).symm) seed o hs hp

private theorem poolTape_pr_bind {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr A =
      ∑ a, P.w a * Q.pr (fun b => A (a, b)) := by
  simp [FinLaw.pr, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_ite]

private theorem poolTape_pr_first {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun x => A x.1) = P.pr A := by
  rw [poolTape_pr_bind]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : A a
  · simp [ha, Q.sum_one]
  · simp [ha]

private theorem poolTape_gated_bound {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (pin gate : α → Prop)
    (bad : α → β → Prop) (q : ℝ) (hq : 0 ≤ q)
    (hbad : ∀ a, gate a → Q.pr (bad a) ≤ q) :
    (FinLaw.bind P (fun _ => Q)).pr
      (fun x => pin x.1 ∧ gate x.1 ∧ bad x.1 x.2) ≤ q * P.pr pin := by
  rw [poolTape_pr_bind]
  have hpoint (a : α) : Q.pr (fun b => pin a ∧ gate a ∧ bad a b) ≤
      if pin a then q else 0 := by
    by_cases hp : pin a
    · by_cases hg : gate a
      · simpa only [hp, hg, true_and, if_true] using hbad a hg
      · simpa [FinLaw.pr, hp, hg] using hq
    · simp [FinLaw.pr, hp]
  calc
    _ ≤ ∑ a, P.w a * (if pin a then q else 0) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a)
    _ = _ := by
      simp [FinLaw.pr, Finset.mul_sum, mul_ite, ite_mul, mul_comm]

private theorem poolTape_cond_pr {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A B : Ω → Prop)
    (h : 0 < ∑ x ∈ Finset.univ.filter A, P.w x) :
    (FinLaw.cond P (Finset.univ.filter A) h).pr B =
      P.pr (fun x => A x ∧ B x) / P.pr A := by
  have hmass : P.pr A = ∑ x ∈ Finset.univ.filter A, P.w x := by
    simp only [FinLaw.pr, Finset.sum_filter]
  rw [hmass]
  unfold FinLaw.pr FinLaw.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]

/-- A tape tail uniform over gated pools survives conditioning on a pool
slot, including the fallback used for zero-mass pins. -/
theorem initialPinnedPoolTapeBound (D : S18.LateData hPT)
    (region : Finset D.geom.Cell)
    (bad : (∀ C, D.fresh.Pool C) → Tapes D.fresh D.encoding.Ts → Prop)
    (q : ℝ) (hq : 0 ≤ q)
    (hbad : ∀ pools, poolGateFor D region pools →
      (tapeLaw D.fresh D.encoding.Ts).pr (bad pools) ≤ q)
    (pin : Option (S18.SlotPin D)) :
    (initialPinnedLaw D pin).pr (fun x => poolGateFor D region x.1 ∧ bad x.1 x.2) ≤ q := by
  let P := D.encoding.poolLaw
  let Q := tapeLaw D.fresh D.encoding.Ts
  let gate := poolGateFor D region
  have huncond : D.encoding.permLaw.pr (fun x => gate x.1 ∧ bad x.1 x.2) ≤ q := by
    change (FinLaw.bind P (fun _ => Q)).pr (fun x => gate x.1 ∧ bad x.1 x.2) ≤ q
    have h := poolTape_gated_bound P Q (fun _ => True) gate bad q hq hbad
    have htrue : P.pr (fun _ => True) = 1 := by
      simp only [FinLaw.pr, ite_true]
      exact P.sum_one
    simpa only [true_and, htrue, mul_one] using h
  cases pin with
  | none => exact huncond
  | some p =>
    let A := S18.pinEvent D p
    let Ap := fun pools : ∀ C, D.fresh.Pool C => pools p.1 p.2.1 = p.2.2
    have hden : D.encoding.permLaw.pr A = P.pr Ap := poolTape_pr_first P Q Ap
    have hmass : D.encoding.permLaw.pr A =
        ∑ x ∈ Finset.univ.filter A, D.encoding.permLaw.w x := by
      simp only [FinLaw.pr, Finset.sum_filter]
    change (if h : 0 < ∑ x ∈ Finset.univ.filter A, D.encoding.permLaw.w x then
      FinLaw.cond D.encoding.permLaw (Finset.univ.filter A) h
      else D.encoding.permLaw).pr (fun x => gate x.1 ∧ bad x.1 x.2) ≤ q
    by_cases hpos : 0 < ∑ x ∈ Finset.univ.filter A, D.encoding.permLaw.w x
    · rw [dif_pos hpos, poolTape_cond_pr, hden]
      apply (div_le_iff₀ (by rwa [← hden, hmass])).2
      exact poolTape_gated_bound P Q Ap gate bad q hq hbad
    · rw [dif_neg hpos]
      exact huncond

theorem restrictedScopes_in_lateRegion (D : S18.LateData hPT) (F : S18.LateEvent D) :
    (lateRestrictedEvents D F).biUnion D.encoding.events.scope ⊆ D.lateRegion F := by
  exact fun _ hx => Finset.mem_union.mpr (Or.inr hx)

theorem replayTargets_polynomial (D : S18.LateData hPT) (hD : D.Spec)
    (X : S18.CriticalTransferData D) (hn : 2 ≤ T.S.n k) :
    (replayTargets D X.criticalCells).card ≤ T.S.n k ^ (10 * (κ.Ac + 10)) := by
  let n := T.S.n k
  have hn2 : n + 1 ≤ n ^ 2 := by dsimp [n]; nlinarith
  calc
    _ ≤ X.criticalCells.card * (n ^ κ.Ac * (n + 1)) * (n + 1) := replayTargets_card_le D hD _
    _ ≤ n * (n ^ κ.Ac * n ^ 2) * n ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (criticalCells_card_le D X) (Nat.mul_le_mul_left _ hn2)) hn2
    _ = n ^ (κ.Ac + 5) := by simp only [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

set_option maxHeartbeats 400000 in
/-- The S17 closure tail can be instantiated on the exact finite process
covered by the late pool gate. Restoring the unrestricted execution closure
is a separate deterministic locality obligation. -/
theorem restrictedLateClosureTapeBound (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec →
      ∀ (F : S18.LateEvent D) (hvalid : D.prefixValid F.2) (omitted : Option D.geom.Cell),
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
      ∀ pools, poolGateFor D (D.lateRegion F) pools →
        (tapeLaw D.fresh D.encoding.Ts).pr (fun tapes =>
          D.encoding.Ts < (backwardClosure (D := Lane_q_s18_n4.lateListContext D)
            (Ts := D.encoding.Ts) D.encoding.events D.encoding.order (lateRestrictedEvents D F)
              pools tapes (replayTargets D X.criticalCells)).card) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) := by
  filter_upwards [finiteResamplingClosureTail κ hκ T,
    T.S.n_tendsto.eventually_ge_atTop 2] with k htail hn
  intro PT hPT D hD F hvalid omitted
  dsimp only
  let Ctx := Lane_q_s18_n4.lateListContext D
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  let E := D.encoding.events
  let events := lateRestrictedEvents D F
  let targets := replayTargets D X.criticalCells
  let root := F.2.2.1.1
  let Ts := initialResamplingRounds T k
  have hTs : D.encoding.Ts = Ts := D.encoding.Ts_eq
  intro pools hgate
  have hrootSeed : D.geom.cellOf root ∈ lateSeedCells D F := by
    apply Finset.mem_biUnion.mpr
    refine ⟨root, ?_, ?_⟩
    · simp [cubeBall, root]
    · simp [S18.LateData.directCells]
  have hroot : root ∈ events := by
    apply seed_in_graphBall D _ _
    apply Finset.mem_biUnion.mpr
    refine ⟨D.geom.cellOf root, hrootSeed, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hD.scope_eq]
    simp [S18.LateData.directCells]
  have hcriticalSeed : X.criticalCells ⊆ lateSeedCells D F :=
    criticalCells_in_seed D F hvalid omitted X.fixed
  have htargets : targets ⊆ events.biUnion E.scope := by
    intro C hC
    obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨C', hC', hvC'⟩ := Finset.mem_biUnion.mp hv
    apply Finset.mem_biUnion.mpr
    refine ⟨v, ?_, hCv⟩
    apply seed_in_graphBall D _ _
    exact Finset.mem_biUnion.mpr ⟨C', hcriticalSeed hC', hvC'⟩
  have hscope : events.biUnion E.scope ⊆ D.lateRegion F := restrictedScopes_in_lateRegion D F
  have hinput : FiniteResamplingInput Ctx E events pools targets root := by
    refine ⟨hn, hroot, eventDegreeBound D hD hn,
      replayTargets_polynomial D hD X hn, ?_, ?_⟩
    · intro C hC
      apply hgate.1 C
      rcases Finset.mem_union.mp hC with hC | hC
      · exact hscope (htargets hC)
      · exact hscope hC
    · intro v hv
      exact hgate.2 v (fun C hC => hscope (Finset.mem_biUnion.mpr ⟨v, hv, hC⟩))
  have hcover : TargetWitnessCover (D := Ctx) (Ts := Ts) E D.encoding.order events pools targets :=
    fun tapes => finiteResamplingTargetWitness (D := Ctx) E D.encoding.order events pools targets tapes
  have hcount : TargetWitnessCountBound (D := Ctx) (Ts := Ts) E
      (T.S.n k ^ (κ.Ac + 4)) events targets :=
    finiteResamplingTargetCount (D := Ctx) E _ events targets hinput.degree
  have htests : WitnessTestBound (D := Ctx) (Ts := Ts) E events pools :=
    finiteResamplingWitnessTests (D := Ctx) E Ts hn events pools hinput.fresh_failure
  have h := htail PT Ctx E D.encoding.order events pools targets root hinput hcover hcount htests
  change (tapeLaw D.fresh D.encoding.Ts).pr (fun tapes =>
    D.encoding.Ts < (backwardClosure (D := Ctx) (Ts := D.encoding.Ts) E D.encoding.order
      events pools tapes targets).card) ≤
    Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2))
  rw [hTs]
  exact h

end HypercubeRamsey.Lane_sol_s18_n4
