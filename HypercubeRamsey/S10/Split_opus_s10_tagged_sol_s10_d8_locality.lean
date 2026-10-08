import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d8

/-! Proof syntax for the local group calculation. It expands in the owned
module after the experiment definitions, so no import cycle is introduced. -/

namespace HypercubeRamsey.Lane_sol_s10_d8
open Classical OAI.HypercubeRamsey HypercubeRamsey.S10
open scoped BigOperators

set_option hygiene false in
macro "s10_d8_group_history_eq " n:term:max δ:term:max M:term:max t:term:max : tactic =>
  `(tactic| all_goals
      intro q h h' hP hW hS hA hτ
      let B := (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9
      have hcenter : q ∈ siteDomain q 3 B := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have hmask : h.mask q = h'.mask q := hS q hcenter
      have hCandidateDomain : ∀ (u : _root_.HypercubeRamsey.Lane_opus_s10_tagged.History ($n) N ($δ))
          (v : _root_.HypercubeRamsey.Lane_opus_s10_tagged.Site ($n) ($δ))
          (c : _root_.HypercubeRamsey.Lane_opus_s10_tagged.ID ($n) ($δ)),
          c ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates u v →
          c ∈ idDomain ($δ) v 1 (3 + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r) := by
        intro u v c hc
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates at hc
        exact candidate_domain_subset (fun s hs => (Finset.mem_filter.mp hs).1) hc
      have hsubid : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          ∀ c ∈ idDomain ($δ) q₀ 1 (3 + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r), c ∈ idDomain ($δ) q 3 B := by
        intro q₀ hq₀ c hc
        apply mem_idDomain.mpr
        have hc' := siteDomain_comp hq₀ (mem_idDomain.mp hc)
        exact siteDomain_mono (by omega) (by omega) hc'
      have hCand : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h' q₀ := by
        intro q₀ hq₀
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates
        exact candidates_congr_subset (fun s hs => (Finset.mem_filter.mp hs).1)
          (fun c hc => hP c (hsubid q₀ hq₀ c hc))
      have hLists : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q₀ := by
        intro q₀ hq₀
        simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists, hCand q₀ hq₀]
      have hFail : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          ∀ L ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀, _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q₀ L = _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h' q₀ L := by
        intro q₀ hq₀ L hL
        have hLs : L ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hL).1
        have htuples : (fun b => h.tup (L.equivFin.symm b).1) =
            (fun b => h'.tup (L.equivFin.symm b).1) := by
          funext b
          exact hW _ (hsubid q₀ hq₀ _ (hCandidateDomain h q₀ _ (hLs (L.equivFin.symm b).2)))
        have hm : h.mask q₀ = h'.mask q₀ :=
          hS q₀ (siteDomain_mono (by omega) (by omega) hq₀)
        simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails, hm, htuples]
      have hForbid : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h' q₀ := by
        intro q₀ hq₀
        have hfiltered : (_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀).filter (_root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q₀) =
            (_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q₀).filter (_root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h' q₀) := by
          rw [← hLists q₀ hq₀]
          exact Finset.filter_congr fun L hL => (hFail q₀ hq₀ L hL).to_iff
        simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden, hfiltered]
      have hIncident : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, s ∈ siteDomain q 1 3 := by
        intro s hs
        exact mem_siteDomain.mpr (envelope_dist (Finset.mem_filter.mp hs).1)
      have hSelect : ∀ s ∈ siteDomain q 1 3, _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected ($M) ($t) h s = _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected ($M) ($t) h' s := by
        intro s hs
        have hs' := hs
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected
        change (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).selection _ _ _ (eligibleFromForbidden ($δ) h.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h) s.1) _ s.2 =
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).selection _ _ _ (eligibleFromForbidden ($δ) h'.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h') s.1) _ s.2
        apply projected_selection_congr
        · intro c hc
          apply hP c
          apply mem_idDomain.mpr
          have hc' := siteDomain_comp hs' (mem_idDomain.mp hc)
          exact siteDomain_mono (by omega) (by dsimp [B, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hp, p10_1kHeightParams]; omega) hc'
        · intro c hc
          apply hA c
          apply mem_idDomain.mpr
          have hc' := siteDomain_comp hs' (mem_idDomain.mp hc)
          exact siteDomain_mono (by omega) (by dsimp [B, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hp, p10_1kHeightParams]; omega) hc'
        · intro q₀ hq₀
          apply hForbid q₀
          have hq₀' := siteDomain_comp hs' hq₀
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega) hq₀'
        · intro j
          apply hτ (s.1, (s.2, j))
          exact mem_idDomain.mpr (siteDomain_mono (by omega) (by omega) hs')
      have hElig : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, ∀ j, _root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h s.1 s.2 j = _root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h' s.1 s.2 j := by
        intro s hs j
        have hs' := hIncident s hs
        change eligibleFromForbidden ($δ) h.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h) s.1 s.2 j =
          eligibleFromForbidden ($δ) h'.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h') s.1 s.2 j
        apply eligibleFromForbidden_congr
        · intro u hu
          apply hP (s.1, (u, j))
          apply mem_idDomain.mpr
          have hv : (s.1, u) ∈ siteDomain s 0 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r :=
            mem_siteDomain.mpr ⟨by simp, by
              calc
                _root_.hammingDist s.2 u = _root_.hammingDist u s.2 := _root_.hammingDist_comm _ _
                _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu⟩
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' hv)
        · intro q₀ hq₀
          apply hForbid q₀
          have henv := envelope_dist ((p10_1kProjectedNeighborEnvelope_symm q₀ s).mp hq₀)
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' (mem_siteDomain.mpr henv))
      have hLegal : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q,
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Legal
            (fun ℓ => h.pos (s.1, ℓ)) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h s.1)
            ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).domBall
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.sliceSites ($δ) s.1) s.2
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong) =
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Legal
            (fun ℓ => h'.pos (s.1, ℓ)) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h' s.1)
            ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).domBall
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.sliceSites ($δ) s.1) s.2
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong) := by
        intro s hs
        apply propext
        apply projected_legal_congr
        · intro c hc
          apply hP c
          apply mem_idDomain.mpr
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega)
            (siteDomain_comp (hIncident s hs) (mem_idDomain.mp hc))
        · intro q₀ hq₀
          apply hForbid q₀
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega)
            (siteDomain_comp (hIncident s hs) hq₀)
      have hCount : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, ∀ j,
          p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (s.1, ℓ)) s.2 j =
            p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (s.1, ℓ)) s.2 j := by
        intro s hs j
        have he : p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (s.1, ℓ)) s.2 j =
            p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (s.1, ℓ)) s.2 j := by
          apply eligible_congr
          intro u hu
          apply hP (s.1, (u, j))
          apply mem_idDomain.mpr
          have hv : (s.1, u) ∈ siteDomain s 0 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r :=
            mem_siteDomain.mpr ⟨by simp, by
              calc
                _root_.hammingDist s.2 u = _root_.hammingDist u s.2 := _root_.hammingDist_comm _ _
                _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu⟩
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp (hIncident s hs) hv)
        exact (p10_1kHeightEligibleIds_card _ _ _ _).symm.trans
          ((congrArg Finset.card he).trans (p10_1kHeightEligibleIds_card _ _ _ _))
      have hReal : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h' q := by
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList
        apply Finset.biUnion_congr rfl
        intro s hs
        rw [hSelect s (hIncident s hs)]
      have hq₀ : q ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have hListq := hLists q hq₀
      have hfixed : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q →
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h' q) ∧
          (∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h q c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h' q c) ∧
          (∀ j, _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight ($M) ($t) h q j = _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight ($M) ($t) h' q j) := by
        intro hL
        have hLs : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hL).1
        have hw : ∀ c ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q, h.tup c = h'.tup c := by
          intro c hc
          exact hW c (hsubid q hq₀ c (hCandidateDomain h q _ (hLs hc)))
        have hhit : _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h' q := by
          apply Finset.ext
          intro y
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hReal]
          exact forall_congr' fun c => imp_congr_right fun hc => by rw [hw c hc]
        have hwithout : ∀ c', _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h q c' = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h' q c' := by
          intro c'
          apply Finset.ext
          intro y
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hReal]
          exact forall_congr' fun c => imp_congr_right fun hc => by rw [hw c hc]
        have hkept : _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltKept ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltKept ($M) ($t) h' q := by
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltKept, hReal, hmask, hhit, hwithout]
        exact ⟨hhit, hwithout, fun j => by simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight, hkept, hmask, hhit]⟩
      have hValid : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h' q := by
        apply propext
        by_cases hL : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q
        · obtain ⟨hhit, hwithout, hweight⟩ := hfixed hL
          have hfail : _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q (_root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q) ↔
              _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h' q (_root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h' q) := by
            rw [hFail q hq₀ _ hL, hReal]
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs => forall_congr' fun j => by rw [hCount s hs j]
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs =>
              and_congr (forall_congr' fun j => by rw [hElig s hs j]) (hLegal s hs).to_iff
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs => by rw [hSelect s (hIncident s hs)]
          apply and_congr
          · rw [hReal, hListq]
          apply and_congr (not_congr hfail)
          simp only [hweight]
        · have hL' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h' q ∉ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q := by rw [← hReal, ← hListq]; exact hL
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid]
          constructor
          · intro hv; exact (hL hv.2.2.2.1).elim
          · intro hv; exact (hL' hv.2.2.2.1).elim
      have hCluster : _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw ($M) ($t) h' q := by
        by_cases hv : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q
        · have hv' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h' q := hValid ▸ hv
          obtain ⟨hhit, hwithout, hweight⟩ := hfixed hv.2.2.2.1
          have hwfun : _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight ($M) ($t) h' q := funext hweight
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw
          rw [dif_pos ⟨hv, hv.2.2.2.2.2⟩, dif_pos ⟨hv', hv'.2.2.2.2.2⟩]
          congr 1
          apply FinProb.ext
          intro j
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.normalizeLaw, hweight]
        · have hv' : ¬ _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h' q := hValid ▸ hv
          simp [_root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw, hv, hv', hmask]
      refine ⟨hValid, hCluster, ?_, hListq, hSelect, ?_⟩
      · intro b hb c
        by_cases hv : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q
        · obtain ⟨hhit, hwithout, hweight⟩ := hfixed hv.2.2.2.1
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.labLaw, hb, hValid, hReal, hmask, hhit]
        · have hv' : ¬ _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h' q := hValid ▸ hv
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.labLaw, hb, hv, hv', false_and, ite_false, hmask]
      · intro c hc
        exact hW c (hsubid q hq₀ c (hCandidateDomain h q _ hc))
  )

set_option hygiene false in
macro "s10_d8_even_history_eq " n:term:max δ:term:max M:term:max t:term:max hgroup:term:max : tactic =>
  `(tactic| all_goals
      intro a h h' hP hW hS hA hτ
      let qₐ := _root_.HypercubeRamsey.Lane_opus_s10_tagged.evenSite ($δ) a
      have hR := common_radius_bound ($n) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.mS ($n) ($δ)) ($δ)
      change (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 12 ≤ _root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ) at hR
      have hInc : ∀ q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incGroups a, q ∈ siteDomain qₐ 1 3 := by
        intro q hq
        exact mem_siteDomain.mpr (envelope_dist (p10_1k_incidentOddGroups_subset_envelope (_root_.HypercubeRamsey.Lane_opus_s10_tagged.mS_le ($n) ($δ)) a hq))
      have hDom : ∀ q ∈ siteDomain qₐ 1 3,
          siteDomain q 3 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9) ⊆ siteDomain qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ)) := by
        intro q hq u hu
        exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hq hu)
      have hIDom : ∀ q ∈ siteDomain qₐ 1 3,
          idDomain ($δ) q 3 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9) ⊆ idDomain ($δ) qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ)) := by
        intro q hq c hc
        exact mem_idDomain.mpr (hDom q hq (mem_idDomain.mp hc))
      have hG (q) (hq : q ∈ siteDomain qₐ 1 3) := ($hgroup) q h h'
        (fun c hc => hP c (hIDom q hq hc)) (fun c hc => hW c (hIDom q hq hc))
        (fun u hu => hS u (hDom q hq hu)) (fun c hc => hA c (hIDom q hq hc))
        (fun c hc => hτ c (hIDom q hq hc))
      have hself : qₐ ∈ siteDomain qₐ 1 3 := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have hCenter : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h a = _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h' a := by
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf
        rw [(hG qₐ hself).2.2.2.2.1 qₐ hself]
      have hcount : ∀ j,
          p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (qₐ.1, ℓ)) qₐ.2 j =
            p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (qₐ.1, ℓ)) qₐ.2 j := by
        intro j
        have he : p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (qₐ.1, ℓ)) qₐ.2 j =
            p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (qₐ.1, ℓ)) qₐ.2 j := by
          apply eligible_congr
          intro u hu
          apply hP (qₐ.1, (u, j))
          apply mem_idDomain.mpr
          apply mem_siteDomain.mpr
          refine ⟨by simp [qₐ], ?_⟩
          have hur : _root_.hammingDist qₐ.2 u ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := by
            calc
              _root_.hammingDist qₐ.2 u = _root_.hammingDist u qₐ.2 := _root_.hammingDist_comm _ _
              _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu
          exact hur.trans (by omega)
        exact (p10_1kHeightEligibleIds_card _ _ _ _).symm.trans
          ((congrArg Finset.card he).trans (p10_1kHeightEligibleIds_card _ _ _ _))
      have hBounds (j) := congrArg (fun z : ℕ =>
        (998 / 1000 : ℝ) * (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).lam ≤ (z : ℝ) ∧
        (z : ℝ) ≤ (1002 / 1000 : ℝ) * (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).lam) (hcount j)
      have hgate : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) h a c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) h' a c := by
        intro c
        apply propext
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate
        apply and_congr
        · exact (congrArg (fun z => z = some c) hCenter).to_iff
        apply and_congr
        · exact forall_congr' fun j => (hBounds j).to_iff
        · exact forall_congr' fun q => imp_congr_right fun hq => (hG q (hInc q hq)).1.to_iff
      have hsub : ∀ c w ω ω', (∀ b ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.starOf a, ω b = ω' b) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik ($M) ($t) h a c w ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik ($M) ($t) h' a c w ω' := by
        intro c w ω ω' hω
        let u := h.setTuple c w
        let u' := h'.setTuple c w
        have hU := ($hgroup)
        have hGU (q) (hq : q ∈ siteDomain qₐ 1 3) := hU q u u'
          (fun d hd => hP d (hIDom q hq hd))
          (fun d hd => update_agree_on (idDomain ($δ) qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ))) hW c w d (hIDom q hq hd))
          (fun v hv => hS v (hDom q hq hv)) (fun d hd => hA d (hIDom q hq hd))
          (fun d hd => hτ d (hIDom q hq hd))
        have huCenter : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) u a = _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) u' a := by
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf
          rw [(hGU qₐ hself).2.2.2.2.1 qₐ hself]
        have huGate : _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u a c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u' a c := by
          apply propext
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate
          simp only [huCenter]
          apply and_congr Iff.rfl
          apply and_congr
          · exact forall_congr' fun j => (hBounds j).to_iff
          · exact forall_congr' fun q => imp_congr_right fun hq => (hGU q (hInc q hq)).1.to_iff
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik
        change (if _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u a c then _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik ($M) ($t) u a ω else 0) =
          (if _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u' a c then _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik ($M) ($t) u' a ω' else 0)
        rw [huGate]
        congr 1
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik
        apply Finset.prod_congr rfl
        intro q hq
        rw [(hGU q (hInc q hq)).2.1]
        apply congrArg (FinProb.expect _)
        funext j
        apply Finset.prod_congr rfl
        intro b hb
        obtain ⟨hb, hbq⟩ := Finset.mem_filter.mp hb
        rw [(hGU q (hInc q hq)).2.2.1 b hbq j, hω b hb]
      have href : ∀ c ω ω', (∀ b ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.starOf a, ω b = ω' b) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ ($M) ($t) h' a c ω' := by
        intro c ω ω' hω
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ
        apply Finset.prod_congr rfl
        intro q hq
        have H := hG q (hInc q hq)
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupRef
        rw [H.2.2.2.1]
        congr 1
        apply Finset.sum_congr rfl
        intro L hL
        have hLs : L ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q := by
          rw [← H.2.2.2.1] at hL
          exact Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1
        have hFm : (Finset.univ.filter fun y => ∀ d ∈ L, d ≠ c → ∀ i, Hits E G (h.tup d i) y) =
            (Finset.univ.filter fun y => ∀ d ∈ L, d ≠ c → ∀ i, Hits E G (h'.tup d i) y) := by
          apply Finset.ext
          intro y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact forall_congr' fun d => imp_congr_right fun hd => by rw [H.2.2.2.2.2 d (hLs hd)]
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.deletionRef
        rw [hFm, hS q (siteDomain_mono (by omega) (by omega) (hInc q hq))]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        apply Finset.prod_congr rfl
        intro b hb
        rw [hω b (Finset.mem_filter.mp hb).1]
      constructor
      · intro ω ω' hω x
        have hMass : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass ($M) ($t) h' a c ω' := by
          intro c
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass
          exact congrArg (FinProb.expect _) (funext fun w => hsub c w ω ω' hω)
        have hMarg : ∀ c x, _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal ($M) ($t) h a c ω x = _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal ($M) ($t) h' a c ω' x := by
          intro c x
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal _root_.HypercubeRamsey.Lane_opus_s10_tagged.posterior
          simp only [hMass c, hsub c _ ω ω' hω]
        have hHeavy : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy ($M) ($t) h' a c ω' := by
          intro c
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy, hMarg]
        have hLight : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass ($M) ($t) h' a c ω' := by
          intro c
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass, hHeavy, hMarg]
        have hOK : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK ($M) ($t) h' a c ω' := by
          intro c
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK, hgate, hMass, href c ω ω' hω, hLight]
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.evenRow
        rw [hCenter]
        cases _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h' a <;> simp only [hOK, hHeavy, hMarg, hLight]
      · intro q hq
        exact ⟨(hG q (hInc q hq)).2.1, (hG q (hInc q hq)).2.2.1⟩
  )

set_option hygiene false in
macro "s10_d8_group_tags_eq " n:term:max δ:term:max M:term:max t:term:max t2:term:max : tactic =>
  `(tactic| all_goals
      intro q h h' hP hW hS hA hτ hT
      let B := (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9
      have hcenter : q ∈ siteDomain q 2 B := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have htq : ($t) q.1 = ($t2) q.1 := hT q.1 (by simp)
      have hmask : h.mask q = h'.mask q := hS q hcenter
      have hCandidateDomain : ∀ (u : _root_.HypercubeRamsey.Lane_opus_s10_tagged.History ($n) N ($δ))
          (v : _root_.HypercubeRamsey.Lane_opus_s10_tagged.Site ($n) ($δ))
          (c : _root_.HypercubeRamsey.Lane_opus_s10_tagged.ID ($n) ($δ)),
          c ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates u v →
          c ∈ idDomain ($δ) v 1 (3 + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r) := by
        intro u v c hc
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates at hc
        exact candidate_domain_subset (fun s hs => (Finset.mem_filter.mp hs).1) hc
      have hsubid : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          ∀ c ∈ idDomain ($δ) q₀ 1 (3 + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r), c ∈ idDomain ($δ) q 3 B := by
        intro q₀ hq₀ c hc
        apply mem_idDomain.mpr
        have hc' := siteDomain_comp hq₀ (mem_idDomain.mp hc)
        exact siteDomain_mono (by omega) (by omega) hc'
      have hCand : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h' q₀ := by
        intro q₀ hq₀
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates
        exact candidates_congr_subset (fun s hs => (Finset.mem_filter.mp hs).1)
          (fun c hc => hP c (hsubid q₀ hq₀ c hc))
      have hLists : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q₀ := by
        intro q₀ hq₀
        simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists, hCand q₀ hq₀]
      have hFail : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          ∀ L ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀, _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q₀ L = _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t2) h' q₀ L := by
        intro q₀ hq₀ L hL
        have hLs : L ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hL).1
        have htuples : (fun b => h.tup (L.equivFin.symm b).1) =
            (fun b => h'.tup (L.equivFin.symm b).1) := by
          funext b
          exact hW _ (hsubid q₀ hq₀ _ (hCandidateDomain h q₀ _ (hLs (L.equivFin.symm b).2)))
        have hm : h.mask q₀ = h'.mask q₀ :=
          hS q₀ (siteDomain_mono (by omega) (by omega) hq₀)
        have htq₀ : ($t) q₀.1 = ($t2) q₀.1 := hT q₀.1 ((mem_siteDomain.mp hq₀).1.trans (by omega))
        have hμ : (fun b => ($M).μ (($t) (L.equivFin.symm b).1.1)) =
            (fun b => ($M).μ (($t2) (L.equivFin.symm b).1.1)) := by
          funext b
          apply congrArg ($M).μ
          apply hT
          exact (mem_siteDomain.mp (mem_idDomain.mp
            (hsubid q₀ hq₀ _ (hCandidateDomain h q₀ _ (hLs (L.equivFin.symm b).2))))).1
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails
        rw [htq₀]
        simp only [hm, htuples, hμ]
      have hForbid : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t2) h' q₀ := by
        intro q₀ hq₀
        have hfiltered : (_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q₀).filter (_root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q₀) =
            (_root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q₀).filter (_root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t2) h' q₀) := by
          rw [← hLists q₀ hq₀]
          exact Finset.filter_congr fun L hL => (hFail q₀ hq₀ L hL).to_iff
        simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden, hfiltered]
      have hIncident : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, s ∈ siteDomain q 1 3 := by
        intro s hs
        exact mem_siteDomain.mpr (envelope_dist (Finset.mem_filter.mp hs).1)
      have hSelect : ∀ s ∈ siteDomain q 1 3, _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected ($M) ($t) h s = _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected ($M) ($t2) h' s := by
        intro s hs
        have hs' := hs
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected
        change (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).selection _ _ _ (eligibleFromForbidden ($δ) h.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h) s.1) _ s.2 =
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).selection _ _ _ (eligibleFromForbidden ($δ) h'.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t2) h') s.1) _ s.2
        apply projected_selection_congr
        · intro c hc
          apply hP c
          apply mem_idDomain.mpr
          have hc' := siteDomain_comp hs' (mem_idDomain.mp hc)
          exact siteDomain_mono (by omega) (by dsimp [B, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hp, p10_1kHeightParams]; omega) hc'
        · intro c hc
          apply hA c
          apply mem_idDomain.mpr
          have hc' := siteDomain_comp hs' (mem_idDomain.mp hc)
          exact siteDomain_mono (by omega) (by dsimp [B, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hp, p10_1kHeightParams]; omega) hc'
        · intro q₀ hq₀
          apply hForbid q₀
          have hq₀' := siteDomain_comp hs' hq₀
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega) hq₀'
        · intro j
          apply hτ (s.1, (s.2, j))
          exact mem_idDomain.mpr (siteDomain_mono (by omega) (by omega) hs')
      have hElig : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, ∀ j, _root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h s.1 s.2 j = _root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t2) h' s.1 s.2 j := by
        intro s hs j
        have hs' := hIncident s hs
        change eligibleFromForbidden ($δ) h.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t) h) s.1 s.2 j =
          eligibleFromForbidden ($δ) h'.pos (_root_.HypercubeRamsey.Lane_opus_s10_tagged.forbidden ($M) ($t2) h') s.1 s.2 j
        apply eligibleFromForbidden_congr
        · intro u hu
          apply hP (s.1, (u, j))
          apply mem_idDomain.mpr
          have hv : (s.1, u) ∈ siteDomain s 0 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r :=
            mem_siteDomain.mpr ⟨by simp, by
              calc
                _root_.hammingDist s.2 u = _root_.hammingDist u s.2 := _root_.hammingDist_comm _ _
                _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu⟩
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' hv)
        · intro q₀ hq₀
          apply hForbid q₀
          have henv := envelope_dist ((p10_1kProjectedNeighborEnvelope_symm q₀ s).mp hq₀)
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' (mem_siteDomain.mpr henv))
      have hLegal : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q,
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Legal
            (fun ℓ => h.pos (s.1, ℓ)) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t) h s.1)
            ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).domBall
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.sliceSites ($δ) s.1) s.2
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong) =
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Legal
            (fun ℓ => h'.pos (s.1, ℓ)) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.elig ($M) ($t2) h' s.1)
            ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).domBall
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.sliceSites ($δ) s.1) s.2
              (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong) := by
        intro s hs
        apply propext
        apply projected_legal_congr
        · intro c hc
          apply hP c
          apply mem_idDomain.mpr
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega)
            (siteDomain_comp (hIncident s hs) (mem_idDomain.mp hc))
        · intro q₀ hq₀
          apply hForbid q₀
          exact siteDomain_mono (by omega) (by dsimp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp]; omega)
            (siteDomain_comp (hIncident s hs) hq₀)
      have hCount : ∀ s ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incidentSites ($δ) q, ∀ j,
          p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (s.1, ℓ)) s.2 j =
            p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (s.1, ℓ)) s.2 j := by
        intro s hs j
        have he : p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (s.1, ℓ)) s.2 j =
            p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (s.1, ℓ)) s.2 j := by
          apply eligible_congr
          intro u hu
          apply hP (s.1, (u, j))
          apply mem_idDomain.mpr
          have hv : (s.1, u) ∈ siteDomain s 0 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r :=
            mem_siteDomain.mpr ⟨by simp, by
              calc
                _root_.hammingDist s.2 u = _root_.hammingDist u s.2 := _root_.hammingDist_comm _ _
                _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu⟩
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp (hIncident s hs) hv)
        exact (p10_1kHeightEligibleIds_card _ _ _ _).symm.trans
          ((congrArg Finset.card he).trans (p10_1kHeightEligibleIds_card _ _ _ _))
      have hReal : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t2) h' q := by
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList
        apply Finset.biUnion_congr rfl
        intro s hs
        rw [hSelect s (hIncident s hs)]
      have hq₀ : q ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have hListq := hLists q hq₀
      have hfixed : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q →
          (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t2) h' q) ∧
          (∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h q c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t2) h' q c) := by
        intro hL
        have hLs : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hL).1
        have hw : ∀ c ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q, h.tup c = h'.tup c := by
          intro c hc
          exact hW c (hsubid q hq₀ c (hCandidateDomain h q _ (hLs hc)))
        have hhit : _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet ($M) ($t2) h' q := by
          apply Finset.ext
          intro y
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hReal]
          exact forall_congr' fun c => imp_congr_right fun hc => by rw [hw c hc]
        have hwithout : ∀ c', _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t) h q c' = _root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout ($M) ($t2) h' q c' := by
          intro c'
          apply Finset.ext
          intro y
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.hitSetWithout, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hReal]
          exact forall_congr' fun c => imp_congr_right fun hc => by rw [hw c hc]
        exact ⟨hhit, hwithout⟩
      have hValid : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t2) h' q := by
        apply propext
        by_cases hL : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h q
        · obtain ⟨hhit, hwithout⟩ := hfixed hL
          have hfail : _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t) h q (_root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t) h q) ↔
              _root_.HypercubeRamsey.Lane_opus_s10_tagged.listFails ($M) ($t2) h' q (_root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t2) h' q) := by
            rw [hFail q hq₀ _ hL, hReal]
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs => forall_congr' fun j => by rw [hCount s hs j]
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs =>
              and_congr (forall_congr' fun j => by rw [hElig s hs j]) (hLegal s hs).to_iff
          apply and_congr
          · exact forall_congr' fun s => imp_congr_right fun hs => by rw [hSelect s (hIncident s hs)]
          apply and_congr
          · rw [hReal, hListq]
          apply and_congr (not_congr hfail)
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight, _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltKept, hReal, hmask, hhit, hwithout]
          rw [htq]
          rfl
        · have hL' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.realizedList ($M) ($t2) h' q ∉ _root_.HypercubeRamsey.Lane_opus_s10_tagged.lists h' q := by rw [← hReal, ← hListq]; exact hL
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid]
          constructor
          · intro hv; exact (hL hv.2.2.2.1).elim
          · intro hv; exact (hL' hv.2.2.2.1).elim
      have hCluster : _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw ($M) ($t) h q = _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw ($M) ($t2) h' q := by
        by_cases hv : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q
        · have hv' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t2) h' q := hValid ▸ hv
          obtain ⟨hhit, hwithout⟩ := hfixed hv.2.2.2.1
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw
          rw [dif_pos ⟨hv, hv.2.2.2.2.2⟩, dif_pos ⟨hv', hv'.2.2.2.2.2⟩]
          apply FinProb.ext
          intro c
          simp only [FinProb.map, _root_.HypercubeRamsey.Lane_opus_s10_tagged.normalizeLaw, _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltWeight, _root_.HypercubeRamsey.Lane_opus_s10_tagged.tiltKept, hReal, hmask, hhit, hwithout]
          rw [htq]
          rfl
        · have hv' : ¬ _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t2) h' q := hValid ▸ hv
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.clusterLaw, hv, hv', false_and, dite_false, hmask]
          rw [htq]
      refine ⟨hValid, hCluster, ?_, hListq, hSelect, ?_⟩
      · intro b hb c
        by_cases hv : _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t) h q
        · obtain ⟨hhit, hwithout⟩ := hfixed hv.2.2.2.1
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.labLaw, hb, hValid, hReal, hmask, hhit]
        · have hv' : ¬ _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupValid ($M) ($t2) h' q := hValid ▸ hv
          simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.labLaw, hb, hv, hv', false_and, ite_false, hmask]
      · intro c hc
        exact hW c (hsubid q hq₀ c (hCandidateDomain h q _ hc))
  )

set_option hygiene false in
macro "s10_d8_even_tags_eq " n:term:max δ:term:max M:term:max t:term:max t2:term:max hgroup:term:max : tactic =>
  `(tactic| all_goals
      intro a h h' hP hW hS hA hτ hT
      let qₐ := _root_.HypercubeRamsey.Lane_opus_s10_tagged.evenSite ($δ) a
      have hR := common_radius_bound ($n) (_root_.HypercubeRamsey.Lane_opus_s10_tagged.mS ($n) ($δ)) ($δ)
      change (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 12 ≤ _root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ) at hR
      have hInc : ∀ q ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.incGroups a, q ∈ siteDomain qₐ 1 3 := by
        intro q hq
        exact mem_siteDomain.mpr (envelope_dist (p10_1k_incidentOddGroups_subset_envelope (_root_.HypercubeRamsey.Lane_opus_s10_tagged.mS_le ($n) ($δ)) a hq))
      have hDom : ∀ q ∈ siteDomain qₐ 1 3,
          siteDomain q 3 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9) ⊆ siteDomain qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ)) := by
        intro q hq u hu
        exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hq hu)
      have hIDom : ∀ q ∈ siteDomain qₐ 1 3,
          idDomain ($δ) q 3 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9) ⊆ idDomain ($δ) qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ)) := by
        intro q hq c hc
        exact mem_idDomain.mpr (hDom q hq (mem_idDomain.mp hc))
      have hMDom : ∀ q ∈ siteDomain qₐ 1 3,
          siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r + 9) ⊆ siteDomain qₐ 3 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ)) := by
        intro q hq u hu
        exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hq hu)
      have hTag (q) (hq : q ∈ siteDomain qₐ 1 3) :
          ∀ z, _root_.hammingDist q.1 z ≤ 3 → ($t) z = ($t2) z := by
        intro z hz
        apply hT
        have ht := _root_.hammingDist_triangle qₐ.1 q.1 z
        have hq' := (mem_siteDomain.mp hq).1
        dsimp only [qₐ] at ht hq'
        omega
      have hG (q) (hq : q ∈ siteDomain qₐ 1 3) := ($hgroup) ($t) ($t2) q h h'
        (fun c hc => hP c (hIDom q hq hc)) (fun c hc => hW c (hIDom q hq hc))
        (fun u hu => hS u (hMDom q hq hu)) (fun c hc => hA c (hIDom q hq hc))
        (fun c hc => hτ c (hIDom q hq hc)) (hTag q hq)
      have hself : qₐ ∈ siteDomain qₐ 1 3 := mem_siteDomain.mpr ⟨by simp, by simp⟩
      have hCenter : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h a = _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t2) h' a := by
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf
        rw [(hG qₐ hself).2.2.2.2.1 qₐ hself]
      have hcount : ∀ j,
          p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (qₐ.1, ℓ)) qₐ.2 j =
            p10_1kHeightPositionCount (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (qₐ.1, ℓ)) qₐ.2 j := by
        intro j
        have he : p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h.pos (qₐ.1, ℓ)) qₐ.2 j =
            p10_1kHeightEligibleIds (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)) (fun ℓ => h'.pos (qₐ.1, ℓ)) qₐ.2 j := by
          apply eligible_congr
          intro u hu
          apply hP (qₐ.1, (u, j))
          apply mem_idDomain.mpr
          apply mem_siteDomain.mpr
          refine ⟨by simp [qₐ], ?_⟩
          have hur : _root_.hammingDist qₐ.2 u ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := by
            calc
              _root_.hammingDist qₐ.2 u = _root_.hammingDist u qₐ.2 := _root_.hammingDist_comm _ _
              _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu
          exact hur.trans (by omega)
        exact (p10_1kHeightEligibleIds_card _ _ _ _).symm.trans
          ((congrArg Finset.card he).trans (p10_1kHeightEligibleIds_card _ _ _ _))
      have hBounds (j) := congrArg (fun z : ℕ =>
        (998 / 1000 : ℝ) * (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).lam ≤ (z : ℝ) ∧
        (z : ℝ) ≤ (1002 / 1000 : ℝ) * (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).lam) (hcount j)
      have hgate : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) h a c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t2) h' a c := by
        intro c
        apply propext
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate
        apply and_congr
        · exact (congrArg (fun z => z = some c) hCenter).to_iff
        apply and_congr
        · exact forall_congr' fun j => (hBounds j).to_iff
        · exact forall_congr' fun q => imp_congr_right fun hq => (hG q (hInc q hq)).1.to_iff
      have hsub : ∀ c w ω ω', (∀ b ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.starOf a, ω b = ω' b) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik ($M) ($t) h a c w ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik ($M) ($t2) h' a c w ω' := by
        intro c w ω ω' hω
        let u := h.setTuple c w
        let u' := h'.setTuple c w
        have hU := ($hgroup) ($t) ($t2)
        have hGU (q) (hq : q ∈ siteDomain qₐ 1 3) := hU q u u'
          (fun d hd => hP d (hIDom q hq hd))
          (fun d hd => update_agree_on (idDomain ($δ) qₐ 4 (_root_.HypercubeRamsey.Lane_opus_s10_tagged.Rloc ($n) ($δ))) hW c w d (hIDom q hq hd))
          (fun v hv => hS v (hMDom q hq hv)) (fun d hd => hA d (hIDom q hq hd))
          (fun d hd => hτ d (hIDom q hq hd)) (hTag q hq)
        have huCenter : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) u a = _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t2) u' a := by
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf
          rw [(hGU qₐ hself).2.2.2.2.1 qₐ hself]
        have huGate : _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u a c = _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t2) u' a c := by
          apply propext
          unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate
          simp only [huCenter]
          apply and_congr Iff.rfl
          apply and_congr
          · exact forall_congr' fun j => (hBounds j).to_iff
          · exact forall_congr' fun q => imp_congr_right fun hq => (hGU q (hInc q hq)).1.to_iff
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.subLik
        change (if _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t) u a c then _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik ($M) ($t) u a ω else 0) =
          (if _root_.HypercubeRamsey.Lane_opus_s10_tagged.gate ($M) ($t2) u' a c then _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik ($M) ($t2) u' a ω' else 0)
        rw [huGate]
        congr 1
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.starLik
        apply Finset.prod_congr rfl
        intro q hq
        rw [(hGU q (hInc q hq)).2.1]
        apply congrArg (FinProb.expect _)
        funext j
        apply Finset.prod_congr rfl
        intro b hb
        obtain ⟨hb, hbq⟩ := Finset.mem_filter.mp hb
        rw [(hGU q (hInc q hq)).2.2.1 b hbq j, hω b hb]
      have href : ∀ c ω ω', (∀ b ∈ _root_.HypercubeRamsey.Lane_opus_s10_tagged.starOf a, ω b = ω' b) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ ($M) ($t2) h' a c ω' := by
        intro c ω ω' hω
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.refQ
        apply Finset.prod_congr rfl
        intro q hq
        have H := hG q (hInc q hq)
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.groupRef
        rw [H.2.2.2.1]
        congr 1
        apply Finset.sum_congr rfl
        intro L hL
        have hLs : L ⊆ _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q := by
          rw [← H.2.2.2.1] at hL
          exact Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1
        have hFm : (Finset.univ.filter fun y => ∀ d ∈ L, d ≠ c → ∀ i, Hits E G (h.tup d i) y) =
            (Finset.univ.filter fun y => ∀ d ∈ L, d ≠ c → ∀ i, Hits E G (h'.tup d i) y) := by
          apply Finset.ext
          intro y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact forall_congr' fun d => imp_congr_right fun hd => by rw [H.2.2.2.2.2 d (hLs hd)]
        have htq : ($t) q.1 = ($t2) q.1 := hTag q (hInc q hq) q.1 (by simp)
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.deletionRef
        rw [hFm, htq, hS q (siteDomain_mono (by omega) (by omega) (hInc q hq))]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        apply Finset.prod_congr rfl
        intro b hb
        rw [hω b (Finset.mem_filter.mp hb).1]
      constructor
      · intro ω ω' hω x
        have hCtag : ∀ c, _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h a = some c → ($t) c.1 = ($t2) c.1 := by
          intro c hc
          have hSlice : c.1 = qₐ.1 := by
            cases hs : _root_.HypercubeRamsey.Lane_opus_s10_tagged.selected ($M) ($t) h qₐ with
            | none => simp [_root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf, qₐ, hs] at hc
            | some ℓ =>
              have he : (qₐ.1, ℓ) = c := by simpa [_root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf, qₐ, hs] using hc
              exact (congrArg Prod.fst he).symm
          rw [hSlice]
          exact hT qₐ.1 (by simp [qₐ])
        unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.evenRow
        cases hc : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t) h a with
        | none =>
          have hc' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t2) h' a = none := hCenter.symm.trans hc
          simp only [hc', hc]
        | some c =>
          have hc' : _root_.HypercubeRamsey.Lane_opus_s10_tagged.centerOf ($M) ($t2) h' a = some c := hCenter.symm.trans hc
          have htC := hCtag c hc
          have hMass : _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass ($M) ($t2) h' a c ω' := by
            unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.predMass _root_.HypercubeRamsey.Lane_opus_s10_tagged.tuplePrior
            rw [htC]
            exact congrArg (FinProb.expect _) (funext fun w => hsub c w ω ω' hω)
          have hMarg : ∀ x, _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal ($M) ($t) h a c ω x = _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal ($M) ($t2) h' a c ω' x := by
            intro x
            unfold _root_.HypercubeRamsey.Lane_opus_s10_tagged.avgMarginal _root_.HypercubeRamsey.Lane_opus_s10_tagged.posterior _root_.HypercubeRamsey.Lane_opus_s10_tagged.tuplePrior
            simp only [htC, hMass, hsub c _ ω ω' hω]
          have hHeavy : _root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy ($M) ($t2) h' a c ω' := by
            simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.heavy, hMarg]
          have hLight : _root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass ($M) ($t2) h' a c ω' := by
            simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.lightMass, hHeavy, hMarg]
          have hOK : _root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK ($M) ($t) h a c ω = _root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK ($M) ($t2) h' a c ω' := by
            simp only [_root_.HypercubeRamsey.Lane_opus_s10_tagged.predOK, hgate, hMass, href c ω ω' hω, hLight]
          simp only [hc', hc, hOK, hHeavy, hMarg, hLight]
      · intro q hq
        exact ⟨(hG q (hInc q hq)).2.1, (hG q (hInc q hq)).2.2.1⟩
  )

end HypercubeRamsey.Lane_sol_s10_d8
