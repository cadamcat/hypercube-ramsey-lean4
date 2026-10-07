import HypercubeRamsey.S17.Needs

namespace HypercubeRamsey.Lane_q_s17_res1

open Classical

private theorem graphBall_mono_radius
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) : ∀ {n m : ℕ}, n ≤ m →
      LE.graphBall seed n ⊆ LE.graphBall seed m := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      exact Finset.Subset.rfl
  | succ m ih =>
      by_cases hn : n ≤ m
      · exact (ih hn).trans (by
          change LE.graphBall seed m ⊆
            LE.graphBall seed m ∪
              Finset.univ.filter (fun w => ∃ v ∈ LE.graphBall seed m, LE.Adjacent w v)
          exact Finset.subset_union_left)
      · have : n = m + 1 := by omega
        subst n
        exact Finset.Subset.rfl

private theorem graphBall_adj_extend
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) {n : ℕ} {v w : Pos T k}
    (hv : v ∈ LE.graphBall seed n) (hadj : LE.Adjacent w v) :
    w ∈ LE.graphBall seed (n + 1) := by
  change w ∈ LE.graphBall seed n ∪
    Finset.univ.filter (fun x => ∃ y ∈ LE.graphBall seed n, LE.Adjacent x y)
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, v, hv, hadj⟩

private theorem graphBall_subset_add
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed other : Finset (Pos T k)) (n : ℕ)
    (hseed : other ⊆ LE.graphBall seed n) :
    ∀ m : ℕ, LE.graphBall other m ⊆ LE.graphBall seed (n + m) := by
  intro m
  induction m with
  | zero =>
      simpa [ListEvent.graphBall] using hseed
  | succ m ih =>
      intro x hx
      rw [ListEvent.graphBall] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have hmem := ih hx
        exact graphBall_mono_radius LE seed (by omega) hmem
      · rcases Finset.mem_filter.mp hx with ⟨_, y, hy, hxy⟩
        exact graphBall_adj_extend LE seed (ih hy) hxy

private theorem incident_subset_ball_one
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (C : D.G.Cell) (v : Pos T k) (hCv : C ∈ LE.scope v) :
    LE.incidentEvents C ⊆ LE.graphBall {v} 1 := by
  intro w hw
  have hwC : C ∈ LE.scope w := (Finset.mem_filter.mp hw).2
  by_cases hEq : w = v
  · subst w
    change v ∈ ({v} ∪ Finset.univ.filter (fun x => ∃ y ∈ ({v} : Finset (Pos T k)), LE.Adjacent x y))
    exact Finset.mem_union.mpr (Or.inl (by simp))
  · have hadj : LE.Adjacent w v := by
      refine ⟨hEq, ?_⟩
      intro hdis
      exact (Finset.disjoint_left.mp hdis) hwC hCv
    change w ∈ ({v} ∪ Finset.univ.filter (fun x => ∃ y ∈ ({v} : Finset (Pos T k)), LE.Adjacent x y))
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, v, by simp, hadj⟩

private theorem incident_subset_ball_one_of_root
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) (v : Pos T k) (hv : v ∈ seed)
    (C : D.G.Cell) (hCv : C ∈ LE.scope v) :
    LE.incidentEvents C ⊆ LE.graphBall seed 1 := by
  intro w hw
  have hwC : C ∈ LE.scope w := (Finset.mem_filter.mp hw).2
  by_cases hEq : w = v
  · subst w
    change v ∈ seed ∪ Finset.univ.filter (fun x => ∃ y ∈ seed, LE.Adjacent x y)
    exact Finset.mem_union.mpr (Or.inl hv)
  · have hadj : LE.Adjacent w v := by
      refine ⟨hEq, ?_⟩
      intro hdis
      exact (Finset.disjoint_left.mp hdis) hwC hCv
    exact graphBall_adj_extend LE seed hv hadj

private theorem event_mem_incident
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    {C : D.G.Cell} {v : Pos T k} (hCv : C ∈ LE.scope v) :
    v ∈ LE.incidentEvents C := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv⟩

private theorem run_cell_locality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    ∀ C, LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events →
      (LE.runRounds Ts order Finset.univ pools tapes).1 C =
          (LE.runRounds Ts order events pools tapes).1 C ∧
        (LE.runRounds Ts order Finset.univ pools tapes).2 C =
          (LE.runRounds Ts order events pools tapes).2 C := by
  induction Ts with
  | zero =>
      intro C _
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro C hball
      let fullPrev := LE.runRounds n order Finset.univ pools tapes
      let partPrev := LE.runRounds n order events pools tapes
      have hfull : LE.runRounds (n + 1) order Finset.univ pools tapes =
          LE.round order Finset.univ pools tapes fullPrev.1 fullPrev.2 := by
        simp [fullPrev, ListEvent.runRounds]
      have hpart : LE.runRounds (n + 1) order events pools tapes =
          LE.round order events pools tapes partPrev.1 partPrev.2 := by
        simp [partPrev, ListEvent.runRounds]
      have hball' : LE.graphBall (LE.incidentEvents C) (2 * n + 4) ⊆ events := by
        have hr : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
        simpa [hr] using hball
      have hactive (v : Pos T k) (hvC : C ∈ LE.scope v) :
          (v ∈ LE.active order Finset.univ fullPrev.1) ↔
            (v ∈ LE.active order events partPrev.1) := by
        have hvInc : v ∈ LE.incidentEvents C := event_mem_incident LE hvC
        have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
          simpa [ListEvent.graphBall] using hvInc
        have hvBall : v ∈ LE.graphBall (LE.incidentEvents C) (2 * n + 4) :=
          graphBall_mono_radius LE _ (by omega) hvBall0
        have hvEvents : v ∈ events := hball' hvBall
        have hscopeState : ∀ x, x ∈ LE.scope v → fullPrev.1 x = partPrev.1 x := by
          intro x hx
          have hseed : LE.incidentEvents x ⊆ LE.graphBall (LE.incidentEvents C) 1 :=
            incident_subset_ball_one_of_root LE (LE.incidentEvents C) v hvInc x hx
          have hlocal := graphBall_subset_add LE (LE.incidentEvents C)
            (LE.incidentEvents x) 1 hseed (2 * n + 2)
          have hsub : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆
              LE.graphBall (LE.incidentEvents C) (2 * n + 3) := by
            have hr : 1 + (2 * n + 2) = 2 * n + 3 := by omega
            rw [hr] at hlocal
            exact hlocal
          have hsub' : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆ events :=
            hsub.trans (fun y hy => hball' (graphBall_mono_radius LE _ (by omega) hy))
          exact (ih x hsub').1
        have hSv : LE.S v fullPrev.1 ↔ LE.S v partPrev.1 :=
          LE.scope_ok v fullPrev.1 partPrev.1 hscopeState
        have hblock (w : Pos T k) (hw : LE.Adjacent w v) :
            (LE.S w fullPrev.1 ↔ LE.S w partPrev.1) := by
          have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
            simpa [ListEvent.graphBall] using hvInc
          have hvBallOne := graphBall_adj_extend LE (LE.incidentEvents C) hvBall0 hw
          have hwBall : w ∈ LE.graphBall (LE.incidentEvents C) (2 * n + 4) :=
            graphBall_mono_radius LE _ (by omega) hvBallOne
          have _hwEvents : w ∈ events := hball' hwBall
          have hstate : ∀ x, x ∈ LE.scope w → fullPrev.1 x = partPrev.1 x := by
            intro x hx
            have hseed₁ : LE.incidentEvents x ⊆ LE.graphBall {w} 1 :=
              incident_subset_ball_one LE x w hx
            have hseed₂ : ({w} : Finset (Pos T k)) ⊆
                LE.graphBall (LE.incidentEvents C) 1 := by
              intro y hy
              have : y = w := Finset.mem_singleton.mp hy
              subst y
              exact hvBallOne
            have hseed : LE.incidentEvents x ⊆
                LE.graphBall (LE.incidentEvents C) 2 := by
              have hsub := graphBall_subset_add LE (LE.incidentEvents C) {w} 1 hseed₂ 1
              exact (Finset.Subset.trans hseed₁ hsub)
            have hlocal := graphBall_subset_add LE (LE.incidentEvents C)
              (LE.incidentEvents x) 2 hseed (2 * n + 2)
            have hsub : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆
                LE.graphBall (LE.incidentEvents C) (2 * n + 4) := by
              have hr : 2 + (2 * n + 2) = 2 * n + 4 := by omega
              rw [hr] at hlocal
              exact hlocal
            have hsub' : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆ events :=
              hsub.trans hball'
            exact (ih x hsub').1
          exact LE.scope_ok w fullPrev.1 partPrev.1 hstate
        constructor
        · intro hfullActive
          change v ∈ Finset.univ.filter _ at hfullActive
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfullActive
          rcases hfullActive with ⟨hSvFull, hbeforeFull⟩
          change v ∈ Finset.univ.filter _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hvEvents, hSv.mp hSvFull, ?_⟩
          intro w hwEvents hbefore hwAdj hSwPart
          have hwAdj' : LE.Adjacent w v := hwAdj
          exact (hbeforeFull w trivial hbefore hwAdj')
            ((hblock w hwAdj').mpr hSwPart)
        · intro hpartActive
          change v ∈ Finset.univ.filter _ at hpartActive
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpartActive
          rcases hpartActive with ⟨hvEvents', hSvPart, hbeforePart⟩
          change v ∈ Finset.univ.filter _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hSv.mpr hSvPart, ?_⟩
          intro w _ hbefore hwAdj hSwFull
          have hSwPart := (hblock w hwAdj).mp hSwFull
          have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
            simpa [ListEvent.graphBall] using hvInc
          have hwBall := graphBall_adj_extend LE (LE.incidentEvents C) hvBall0 hwAdj
          exact hbeforePart w (hball' (graphBall_mono_radius LE _ (by omega) hwBall))
            hbefore hwAdj hSwPart
      have htouch :
          (∃ v ∈ LE.active order Finset.univ fullPrev.1, C ∈ LE.scope v) ↔
            (∃ v ∈ LE.active order events partPrev.1, C ∈ LE.scope v) := by
        constructor
        · rintro ⟨v, hv, hvC⟩
          exact ⟨v, (hactive v hvC).mp hv, hvC⟩
        · rintro ⟨v, hv, hvC⟩
          exact ⟨v, (hactive v hvC).mpr hv, hvC⟩
      have hprevSubset : LE.graphBall (LE.incidentEvents C) (2 * n + 2) ⊆ events :=
        (graphBall_mono_radius LE _ (by omega)).trans hball'
      have hprev := ih C hprevSubset
      change fullPrev.1 C = partPrev.1 C ∧ fullPrev.2 C = partPrev.2 C at hprev
      rcases hprev with ⟨hprevState, hprevCount⟩
      rw [hfull, hpart]
      simp [ListEvent.round, fullPrev, partPrev, htouch, hprevState, hprevCount]

theorem resampleLocality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    LE.CellLocalitySpec Ts order pools tapes ∧
      LE.EventTruthLocalitySpec Ts order pools tapes := by
  constructor
  · intro C events hsubset
    have hsmall : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events :=
      (graphBall_mono_radius LE _ (by omega)).trans hsubset
    simpa [ListEvent.resample] using
      (run_cell_locality LE Ts order events pools tapes C hsmall).1
  · intro v events hsubset
    apply LE.scope_ok v _ _
    intro C hC
    have hseed : LE.incidentEvents C ⊆ LE.graphBall {v} 1 :=
      incident_subset_ball_one LE C v hC
    have hball := graphBall_subset_add LE {v} (LE.incidentEvents C) 1 hseed
      (2 * Ts + 2)
    have hsub : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆
        LE.graphBall {v} (2 * Ts + 3) := by
      have hr : 1 + (2 * Ts + 2) = 2 * Ts + 3 := by omega
      simpa [hr] using hball
    have hevents : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events :=
      hsub.trans hsubset
    have hfullEq := (run_cell_locality LE Ts order events pools tapes C hevents).1
    simpa [ListEvent.resample] using hfullEq

end HypercubeRamsey.Lane_q_s17_res1
