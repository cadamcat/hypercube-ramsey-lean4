import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row
import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_row_laws

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT}

/-- The raw local label projection agrees with the solver's reference
projection, retaining every group shared by the internal star. -/
theorem raw_local_reference_expect (R : CellRawData G)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (s : R.Slice C)
    (e : EvenRole PT.tiling (G.cellPatch C))
    (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
    (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (hGroup : ∀ s z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
      R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
        groups (s, S.groupOf z))
    (hQ : ∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D)
    (hU : ∀ W s g D y, (R.U C W (groups (s, g)) D).w y = S.U g (records s (W s)) D y)
    (W : R.Hist C) (fallback : Fin (T.S.N k)) (Φ : InternalLabels PT.tiling (G.cellPatch C) → ℝ) :
    (R.rawLaw C W).E (fun ω => Φ (nbrLabels e.1 (R.wordLabel C ω.2 s fallback))) =
      (S.refLaw (records s (W s))).E (fun ω => Φ (nbrLabels e.1 ω.2)) := by
  let wordRole (j : Fin (PT.tiling.P (G.cellPatch C)).h) : OddCellRole G C :=
    ⟨(R.cellWords C (s, flipPos e.1 j)).1,
      (R.cellWords C (s, flipPos e.1 j)).2,
      by
        intro h
        have hword := (R.word_parity hc C s (flipPos e.1 j)).mp h
        exact ((Lane_sol_s16_prod1.flip_parity e.1 j).mp hword) e.2⟩
  have hwordRole : Function.Injective wordRole := by
    intro a b hab
    have hpos := congrArg Subtype.val hab
    have hwords : R.cellWords C (s, flipPos e.1 a) = R.cellWords C (s, flipPos e.1 b) :=
      Subtype.ext hpos
    have hflip := congrArg Prod.snd ((R.cellWords C).injective hwords)
    exact flip_injective e.1 hflip
  have hlabels (ys : OddCellRole G C → Fin (T.S.N k)) :
      nbrLabels e.1 (R.wordLabel C ys s fallback) = fun j => ys (wordRole j) := by
    funext j
    unfold nbrLabels CellRawData.wordLabel
    rw [dif_pos (wordRole j).2.2]
  let gmap (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C)) := groups (s, g)
  have hgmap : Function.Injective gmap := by
    intro a b hab
    exact congrArg Prod.snd (groups.injective hab)
  let q : HypercubeRamsey.Group PT.tiling (G.cellPatch C) → FinLaw (Bin PT.tiling (G.cellPatch C)) :=
    fun g => ⟨S.q g (records s (W s)), S.q_nonneg g _, S.q_sum g _⟩
  let u (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C)) (b : Bin PT.tiling (G.cellPatch C)) :
      FinLaw (Fin (T.S.N k)) := ⟨S.U g (records s (W s)) b, S.U_nonneg g _ b, S.U_sum g _ b⟩
  have hq (g) : R.qraw C W (gmap g) = q g := by
    apply Lane_q_s16_prod2.finLaw_ext
    intro b
    exact hQ W s g b
  have hu (a : R.Group C → Bin PT.tiling (G.cellPatch C)) (j) :
      R.U C W (R.groupOf C (wordRole j)) (a (R.groupOf C (wordRole j))) =
        u (S.groupOf (flipPos e.1 j)) (a (gmap (S.groupOf (flipPos e.1 j)))) := by
    rw [show R.groupOf C (wordRole j) = gmap (S.groupOf (flipPos e.1 j)) from
      hGroup s (flipPos e.1 j) (wordRole j).2.2]
    apply Lane_q_s16_prod2.finLaw_ext
    intro y
    exact hU W s _ _ y
  unfold CellRawData.rawLaw
  rw [Lane_q_s16_comp2.bind_expect]
  simp only [hlabels]
  have hinner (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :
      (FinLaw.pi (fun r => R.U C W (R.groupOf C r) (a (R.groupOf C r)))).E
        (fun labels => Φ (fun j => labels (wordRole j))) =
      (FinLaw.pi (fun j => u (S.groupOf (flipPos e.1 j))
        (a (gmap (S.groupOf (flipPos e.1 j)))))).E Φ := by
    rw [pi_injection_expect _ wordRole hwordRole]
    simp only [hu]
  simp only [hinner]
  rw [pi_injection_expect (R.qraw C W) gmap hgmap
    (fun a => (FinLaw.pi (fun j => u (S.groupOf (flipPos e.1 j))
      (a (S.groupOf (flipPos e.1 j))))).E Φ)]
  simp only [hq]
  unfold SliceSolver.refLaw internalRefLaw
  rw [Lane_q_s16_comp2.bind_expect]
  apply congrArg (FinLaw.pi q).E
  funext a
  exact (pi_injection_expect (fun z => u (S.groupOf z) (a (S.groupOf z)))
    (fun j => flipPos e.1 j) (flip_injective e.1) Φ).symm

private def BaseSolverAt (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : PriorExperiment (T.S.N k)) (i : Fin PT.tiling.m)
    (hi : i = D.G.patchOf v) : Prop :=
  ∃ (S : SliceSolver κ PT.tiling i PT.mesh) (e : EvenRole PT.tiling i),
    PT.solver i = some S ∧ D.SolverRoleMatches v (cast (by rw [hi]) e) ∧
    ∀ Φ : (Fin (T.S.N k) → ℝ) → ℝ, P.expect Φ =
      (S.recLaw PT.parameter).E (fun W => (S.refLaw W).E
        (fun ω => Φ (S.σ e W (nbrLabels e.1 ω.2))))

private theorem base_solver_transport (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : PriorExperiment (T.S.N k)) (i : Fin PT.tiling.m)
    (hi : i = D.G.patchOf v) (h : BaseSolverAt D v P i hi) :
    BaseSolverAt D v P (D.G.patchOf v) rfl := by
  subst i
  exact h

/-- The unrestricted raw base experiment carries S17's repaired ordered
solver provenance. The comparison and permission table use this same law. -/
noncomputable def physical_base_source {F : FreshCell G} (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).BasePriorSource v := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  let R := physical.raw
  let C := G.cellOf v
  let P := R.baseExperiment C v
  refine {
    Ω := P.State
    outcomes := inferInstance
    law := P.law
    readout := P.prior
    solver_source := ?_
    direct_source := ?_ }
  · intro he hc
    rcases physical.source_valid with hsource | hsource
    · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hsource.2.2 C
      let p := (R.cellWords C).symm ⟨v, rfl⟩
      have hsite : (R.cellWords C p).1 = v :=
        congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v, rfl⟩)
      have heword : IsEvenRole p.2 := (R.word_parity hc C p.1 p.2).mp (by rwa [hsite])
      let e : EvenRole PT.tiling (G.cellPatch C) := ⟨p.2, heword⟩
      let fallback : Fin (T.S.N k) := ⟨0, T.S.N_pos k⟩
      have hp (W : R.Hist C) (labels : OddCellRole G C → Fin (T.S.N k)) :
          R.rawPrior C W labels v =
            S.σ e (records p.1 (W p.1)) (nbrLabels e.1 (R.wordLabel C labels p.1 fallback)) := by
        have h := hPrior W p.1 e labels fallback
        change R.rawPrior C W labels (R.cellWords C p).1 = _ at h
        rwa [hsite] at h
      change BaseSolverAt D v P (G.patchOf v) rfl
      apply base_solver_transport D v P (G.cellPatch C) (G.cellOf_patch v)
      refine ⟨S, e, hS, raw_word_order_solver_role R R.word_order hc D rfl v C p.1 e rfl hsite, ?_⟩
      intro Φ
      dsimp only [P, PriorExperiment.expect, CellRawData.baseExperiment]
      rw [Lane_q_s16_comp2.bind_expect]
      have hlocal (W : R.Hist C) :
          (R.rawLaw C W).E (fun ω => Φ (R.rawPrior C W ω.2 v)) =
          (S.refLaw (records p.1 (W p.1))).E
            (fun ω => Φ (S.σ e (records p.1 (W p.1)) (nbrLabels e.1 ω.2))) := by
        simp only [hp]
        exact raw_local_reference_expect R hc C p.1 e S records groups hGroup hQ hU
          W fallback (fun ys => Φ (S.σ e (records p.1 (W p.1)) ys))
      simp only [hlocal]
      let test (W : ∀ r, S.Val r) :=
        (S.refLaw W).E (fun ω => Φ (S.σ e W (nbrLabels e.1 ω.2)))
      change (FinLaw.pi (R.sliceLaw C)).E (fun W => test (records p.1 (W p.1))) =
        (S.recLaw PT.parameter).E test
      rw [Lane_q_s16_prod2.finLaw_pi_E_coordinate (R.sliceLaw C) p.1
        (fun W => test (records p.1 W))]
      rw [hLaw p.1, Lane_q_s16_comp2.map_expect]
      simp only [Equiv.apply_symm_apply]
    · exact (hsource.1 hc).elim
  · intro he hc
    rcases physical.source_valid with hsource | hsource
    · have hm : PT.tiling.mode.isCluster := by simp [hsource.1, Mode.isCluster]
      exact (hc hm).elim
    · obtain ⟨_, _, _, _, _, _, hEnv, hPrior⟩ := hsource.2 C
      let σ := (Law.unifCore (PT.envelope (G.cellPatch C)) hEnv).w
      refine ⟨σ, ?_, ?_⟩
      · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (hPT.direct_single_corner hc)
        have hqmem : q ∈ PT.activeVertices := by rw [hq]; simp
        have hpatch : G.cellPatch C = G.patchOf v := G.cellOf_patch v
        have henv : PT.envelope (G.cellPatch C) = PT.mesh.corner q (G.patchOf v) := by
          rw [hpatch, hPT.envelope_eq, hq]
          simp
        dsimp only [ListGateContext.CleanInitialPrior, D, Lane_sol_s18_dl.physical_list_context]
        refine ⟨(Law.unifCore _ hEnv).nonneg, (Law.unifCore _ hEnv).sum_eq_one,
          q, hqmem, ?_, ?_, ?_⟩
        · intro x hx
          change (if x ∈ PT.envelope (G.cellPatch C) then _ else 0) ≠ 0 at hx
          by_contra hn
          have hnot : x ∉ PT.envelope (G.cellPatch C) := by
            simpa only [henv] using hn
          simp [hnot] at hx
        · intro h
          exact (hc h).elim
        · intro _
          refine ⟨Lane_sol_fix_corner.active_corner_card_lower_waste hPT _ q hqmem, ?_⟩
          intro x
          dsimp only [σ, Law.unifCore]
          simp only [henv, one_div]
      · intro ω
        exact hPrior ω.1 ω.2.2 v rfl he

end HypercubeRamsey.S18.Lane_sol_d18l_row
