import HypercubeRamsey.S18.PrefixBudget_sol_s18_n4
import HypercubeRamsey.S18.PrefixClosure_sol_s18_n4
import HypercubeRamsey.S18.ReplayScope_sol_s18_3a_perm

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical Filter
open scoped BigOperators

/-- Restore the unrestricted closure and integrate the restricted S17 tail
against permutation pools, including a possible zero-mass pin. -/
private theorem validPrefixClosureTail {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec →
      ∀ (F : S18.LateEvent D) (hvalid : D.prefixValid F.2) (pin : Option (S18.SlotPin D)),
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
      (initialPinnedLaw D pin).pr (fun x =>
        D.poolGate (D.lateRegion F) x ∧ replayClosure D X.criticalCells x) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) := by
  filter_upwards [restrictedLateClosureTapeBound hκ T] with k hrestricted
  intro PT hPT D hD F hvalid pin
  have htape := hrestricted D hD F hvalid (pin.map (fun p => p.1))
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
  have hbound := initialPinnedPoolTapeBound D (D.lateRegion F)
    (fun pools tapes => D.encoding.Ts <
      (backwardClosure (D := Lane_q_s18_n4.lateListContext D)
        D.encoding.events D.encoding.order (lateRestrictedEvents D F)
        pools tapes (replayTargets D X.criticalCells)).card)
    (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) htape pin
  convert hbound using 1
  congr 1
  funext x
  apply propext
  change (poolGateFor D (D.lateRegion F) x.1 ∧
    D.encoding.Ts < (replayBackwardClosure D X.criticalCells x).card) ↔ _
  rw [replayBackwardClosure_eq_restricted D F hvalid (pin.map (fun p => p.1)) X.fixed x]

/-- Compare the actual consulted permutation slots, with a globally pinned
cell omitted from the critical set, to the iid pool/tape fresh experiment. -/
theorem validPrefixPermutationReplay {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c : ℝ) (hK : 0 < K27) (hc : 0 < c) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → S18.TransitionData D →
      S18.LocalTransitionFacts D K27 → S18.TransferBound D c → S18.ReplayFacts D →
      ∀ (F : S18.LateEvent D), F.1.val = 1 → ∀ hvalid : D.prefixValid F.2,
      ∀ pin : Option (S18.SlotPin D),
      let X : S18.CriticalTransferData D :=
        ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
      ∀ W ∈ boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts,
        (initialPinnedLaw D pin).E (fun x =>
          if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
            forcedReplayRisk D X.criticalCells (occurrencePattern D W) F x else 0) ≤
              2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2] with k hn
  intro PT hPT D hD hTransition hLocal hTransfer hReplay F hkind hvalid pin
  dsimp only
  intro W hW
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
  let f := fun x : D.encoding.InitInput =>
    if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
      forcedReplayRisk D X.criticalCells (occurrencePattern D W) F x else 0
  have hcomparison : (initialPinnedLaw D pin).E f ≤
      2 * (Lane_sol_s18_3a_perm.iidPinnedLaw D pin).E f := by
    apply Lane_sol_s18_3a_perm.replayComparison_of_poolComparison D pin f
    have hlocal := Lane_sol_s18_3a_perm.replayPoolTest_local D hD hTransition F hkind hvalid
      (pin.map (fun p => p.1)) (occurrencePattern D W)
    -- Remaining: the pin-uniform patch-wise permutation-to-iid comparison
    -- on this deterministic region, and its total cost bound at most two.
    sorry
  exact hcomparison.trans (mul_le_mul_of_nonneg_left
    (Lane_sol_s18_3a_perm.iidPinnedReplayBound D hD hReplay c hTransfer F hkind hvalid pin
      (occurrencePattern D W)) (by norm_num))

/-- The valid-prefix branch reduces to the two exact analytic estimates
above. Pattern summation and the final exponent budget are proved helpers. -/
theorem validPrefixPinnedBound {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (K27 c δ : ℝ) (hK : 0 < K27) (hc : 0 < c) (hδ : δ < c) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → S18.TransitionData D →
      S18.LocalTransitionFacts D K27 → S18.TransferBound D c → S18.ReplayFacts D →
      ∀ (F : S18.LateEvent D), F.1.val = 1 → ∀ hvalid : D.prefixValid F.2,
      ∀ pin : Option (S18.SlotPin D),
        S18.initialProbability D pin (S18.terminalFailure D δ (.inr (.inr F))) ≤
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  filter_upwards [validPrefixClosureTail hκ T,
    validPrefixPermutationReplay hκ T K27 c hK hc,
    validPrefixReplayBudgetEventually hκ T c δ hc hδ] with k hclosure hpattern hbudget
  intro PT hPT D hD hTransition hLocal hTransfer hReplay F hkind hvalid pin
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
  exact validPrefixPinnedBoundFromEstimates D hD hReplay δ F hvalid pin
    (Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)))
    (2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c))
    (hclosure D hD F hvalid pin)
    (hpattern D hD hTransition hLocal hTransfer hReplay F hkind hvalid pin)
    (hbudget D hD X)

end HypercubeRamsey.Lane_sol_s18_n4
