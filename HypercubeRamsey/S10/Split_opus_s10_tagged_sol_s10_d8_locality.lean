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
      have hsubid : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          ∀ c ∈ idDomain ($δ) q₀ 1 (3 + (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r), c ∈ idDomain ($δ) q 3 B := by
        intro q₀ hq₀ c hc
        apply mem_idDomain.mpr
        have hc' := siteDomain_comp hq₀ (mem_idDomain.mp hc)
        exact siteDomain_mono (by omega) (by omega) hc'
      have hCand : ∀ q₀, q₀ ∈ siteDomain q 2 ((_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).Rlong + 6) →
          _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h q₀ = _root_.HypercubeRamsey.Lane_opus_s10_tagged.candidates h' q₀ := by
        intro q₀ hq₀
        exact candidates_congr fun c hc => hP c (hsubid q₀ hq₀ c hc)
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
          exact hW _ (hsubid q₀ hq₀ _ (candidate_domain (hLs (L.equivFin.symm b).2)))
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
                hammingDist s.2 u = hammingDist u s.2 := hammingDist_comm _ _
                _ ≤ (_root_.HypercubeRamsey.Lane_opus_s10_tagged.hp ($n) ($δ)).r := hu⟩
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' hv)
        · intro q₀ hq₀
          apply hForbid q₀
          have henv := envelope_dist ((p10_1kProjectedNeighborEnvelope_symm q₀ s).mp hq₀)
          exact siteDomain_mono (by omega) (by omega) (siteDomain_comp hs' (mem_siteDomain.mpr henv))
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
                hammingDist s.2 u = hammingDist u s.2 := hammingDist_comm _ _
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
          exact hW c (hsubid q hq₀ c (candidate_domain (hLs hc)))
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
          · exact forall_congr' fun s => imp_congr_right fun hs => forall_congr' fun j => by rw [hElig s hs j]
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
        exact hW c (hsubid q hq₀ c (candidate_domain hc))
  )

end HypercubeRamsey.Lane_sol_s10_d8
