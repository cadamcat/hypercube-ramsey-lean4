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
