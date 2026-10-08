import HypercubeRamsey.S17.Nodes

/-!
# Section 17 exports

The public lemma names are `independentPinnedList`, `uniformPoolListEstimate`
and `finiteResamplingComparison`, each assembled in
`Nodes.lean` from the named blueprint subnodes.  This module exports the
locality guarantee for the concrete `S_v` event.
-/

namespace HypercubeRamsey

/-- D17.R-loc for the concrete initial-list event and its cell scope. -/
theorem initialListResampleLocality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ)
    (order : Pos T k → ℕ) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    D.asListEvent.CellLocalitySpec Ts order pools tapes ∧
      D.asListEvent.EventTruthLocalitySpec Ts order pools tapes := by
  exact resampleLocality D.asListEvent Ts order pools tapes

end HypercubeRamsey
