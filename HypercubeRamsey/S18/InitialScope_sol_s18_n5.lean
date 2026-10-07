import HypercubeRamsey.S18.Locality_sol_s18_n5
import HypercubeRamsey.S17.Nodes_q_s17_res1

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem graphBall_seed_mono (D : LateData hPT) {S R : Finset (Pos T k)}
    (hSR : S ⊆ R) : ∀ t, D.encoding.events.graphBall S t ⊆ D.encoding.events.graphBall R t := by
  intro t
  induction t with
  | zero => exact hSR
  | succ t ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union.mpr (Or.inl (ih hv))
    · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, u, ih hu, hadj⟩))

private theorem active_congr (D : LateData hPT) (events : Finset (Pos T k))
    (s s' : Config D.fresh)
    (hS : ∀ v ∈ events, D.encoding.events.S v s ↔ D.encoding.events.S v s') :
    D.encoding.events.active D.encoding.order events s =
      D.encoding.events.active D.encoding.order events s' := by
  ext v
  simp only [ListEvent.active, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hv, hs, hprev⟩
    refine ⟨hv, (hS v hv).mp hs, ?_⟩
    intro u hu hbefore hadj
    exact (hS u hu).not.mp (hprev u hu hbefore hadj)
  · rintro ⟨hv, hs, hprev⟩
    refine ⟨hv, (hS v hv).mpr hs, ?_⟩
    intro u hu hbefore hadj
    exact (hS u hu).not.mpr (hprev u hu hbefore hadj)

/-- A restricted simultaneous simulation reads only its event scopes and
the cells whose output is requested. Counters are included in the invariant. -/
theorem restricted_rounds_input_local (D : LateData hPT) (events : Finset (Pos T k))
    (region : Finset D.geom.Cell)
    (hregion : ∀ v ∈ events, D.encoding.events.scope v ⊆ region)
    (x x' : D.encoding.InitInput)
    (hinput : ∀ C ∈ region, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    ∀ t C, C ∈ region →
      (D.encoding.events.runRounds t D.encoding.order events x.1 x.2.extend).1 C =
        (D.encoding.events.runRounds t D.encoding.order events x'.1 x'.2.extend).1 C ∧
      (D.encoding.events.runRounds t D.encoding.order events x.1 x.2.extend).2 C =
        (D.encoding.events.runRounds t D.encoding.order events x'.1 x'.2.extend).2 C := by
  intro t
  induction t with
  | zero =>
    intro C hC
    obtain ⟨hp, ht⟩ := hinput C hC
    change x.2.extend C 0 (x.1 C) = x'.2.extend C 0 (x'.1 C) ∧ (0 : ℕ) = 0
    simp only [Tapes.extend, hp, ht]
    exact ⟨trivial, trivial⟩
  | succ t ih =>
    let prev := D.encoding.events.runRounds t D.encoding.order events x.1 x.2.extend
    let prev' := D.encoding.events.runRounds t D.encoding.order events x'.1 x'.2.extend
    have hsel : D.encoding.events.active D.encoding.order events prev.1 =
        D.encoding.events.active D.encoding.order events prev'.1 := by
      apply active_congr D
      intro v hv
      apply D.encoding.events.scope_ok
      intro C hC
      exact (ih C (hregion v hv hC)).1
    intro C hC
    have hc := ih C hC
    obtain ⟨hp, ht⟩ := hinput C hC
    change (if _ : ∃ v ∈ D.encoding.events.active D.encoding.order events prev.1,
        C ∈ D.encoding.events.scope v then x.2.extend C (prev.2 C + 1) (x.1 C) else prev.1 C) =
      (if _ : ∃ v ∈ D.encoding.events.active D.encoding.order events prev'.1,
        C ∈ D.encoding.events.scope v then x'.2.extend C (prev'.2 C + 1) (x'.1 C) else prev'.1 C) ∧
      (if ∃ v ∈ D.encoding.events.active D.encoding.order events prev.1,
        C ∈ D.encoding.events.scope v then prev.2 C + 1 else prev.2 C) =
      (if ∃ v ∈ D.encoding.events.active D.encoding.order events prev'.1,
        C ∈ D.encoding.events.scope v then prev'.2 C + 1 else prev'.2 C)
    have hstate : prev.1 C = prev'.1 C := hc.1
    have hcount : prev.2 C = prev'.2 C := hc.2
    simp only [hsel, hstate, hcount, Tapes.extend, hp, ht]
    exact ⟨trivial, trivial⟩

set_option maxHeartbeats 400000 in
/-- The full finite resampling output on seed cells is a function of the
prescribed deterministic horizon, with its pools and finite tapes. -/
theorem initialState_input_local (D : LateData hPT) (seed : Finset D.geom.Cell)
    (x x' : D.encoding.InitInput)
    (hinput : ∀ C ∈ D.expandCells seed, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    ∀ C ∈ seed, D.encoding.initialState x C = D.encoding.initialState x' C := by
  obtain ⟨validState, permittedLabels, hfresh⟩ := D.l16_valid.fresh_spec
  let Ctx : ListGateContext κ T k PT := {
    tiling_valid := hPT
    mode_low := D.low_mode
    G := D.geom
    F := D.fresh
    stateValid := validState
    permittedLabels := permittedLabels
    slotFactor := fun _ => 0
    fresh_spec := hfresh }
  let events := D.encoding.events.graphBall
    (seed.biUnion D.encoding.events.incidentEvents) (2 * D.encoding.Ts + 3)
  have hscope : ∀ v ∈ events, D.encoding.events.scope v ⊆ D.expandCells seed := by
    intro v hv C hC
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨v, hv, hC⟩))
  have hlocal := restricted_rounds_input_local D events (D.expandCells seed) hscope x x' hinput
  intro C hC
  have hCregion : C ∈ D.expandCells seed := Finset.mem_union.mpr (Or.inl hC)
  have hinc : D.encoding.events.incidentEvents C ⊆ seed.biUnion D.encoding.events.incidentEvents := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨C, hC, hv⟩
  have hball : D.encoding.events.graphBall (D.encoding.events.incidentEvents C)
      (2 * D.encoding.Ts + 3) ⊆ events := graphBall_seed_mono D hinc _
  have hx := (HypercubeRamsey.Lane_q_s17_res1.resampleLocality (D := Ctx) D.encoding.events
    D.encoding.Ts D.encoding.order x.1 x.2.extend).1 C events hball
  have hx' := (HypercubeRamsey.Lane_q_s17_res1.resampleLocality (D := Ctx) D.encoding.events
    D.encoding.Ts D.encoding.order x'.1 x'.2.extend).1 C events hball
  exact hx.trans ((hlocal D.encoding.Ts C hCregion).1.trans hx'.symm)

end HypercubeRamsey.S18.Lane_sol_s18_n5
