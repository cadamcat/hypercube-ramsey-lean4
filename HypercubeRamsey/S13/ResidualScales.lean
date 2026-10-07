import HypercubeRamsey.PartC.Tiling

/-!
# Section 13.1: residual scale interfaces

The scales themselves are frozen in `PartC/Tiling.lean`. This file records the
specification facts used by the Section 13 proof nodes.
-/

namespace HypercubeRamsey.S13

open Filter

/-- D13.1: each measured scale is a dyadic integer. -/
theorem gScale_isDyadic (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : IsDyadic (gScale κ T k RX RY) := by
  sorry

theorem qScale_isDyadic (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) : IsDyadic (qScale κ T k RX RY) := by
  sorry

/-- D13.1: an empty finite witness set gives the prescribed scale `1`. -/
theorem gScale_eq_one_of_no_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : ∀ j, 1 ≤ j → ¬ BiasWitness κ T k RX RY (2 ^ j)) :
    gScale κ T k RX RY = 1 := by
  sorry

theorem qScale_eq_one_of_no_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : ∀ j, 1 ≤ j → ¬ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o) :
    qScale κ T k RX RY = 1 := by
  sorry

/-- D13.1(i): a nontrivial measured bias scale is itself witnessed. -/
theorem gScale_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : 2 ≤ gScale κ T k RX RY) :
    BiasWitness κ T k RX RY (gScale κ T k RX RY) := by
  sorry

/-- D13.1(i): a nontrivial measured cluster scale has a witness in some orientation. -/
theorem qScale_witness (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (h : 2 ≤ qScale κ T k RX RY) :
    ∃ o : Bool, CluScaleWitness κ T k RX RY (qScale κ T k RX RY) o := by
  sorry

/-- D13.1(ii): no larger in-range dyadic bias budget is witnessed. -/
theorem gScale_absent (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (hb : IsDyadic b) (hscale : gScale κ T k RX RY < b)
    (hrange : b ≤ 2 * T.S.n k + 1) :
    ¬ BiasWitness κ T k RX RY b := by
  sorry

/-- D13.1(ii): no larger in-range dyadic cluster budget is witnessed in either orientation. -/
theorem qScale_absent (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ)
    (hb : IsDyadic b) (hscale : qScale κ T k RX RY < b)
    (hrange : b ≤ T.S.N k + 1) :
    ¬ ∃ o : Bool, CluScaleWitness κ T k RX RY b o := by
  sorry

/-- D13.1(iii): both measured scales are monotone under enlarging the residual sides. -/
theorem residual_scales_mono (κ : CConsts) (T : Stage) (k : ℕ)
    {RX RX' RY RY' : Finset (Fin (T.S.N k))}
    (hX : RX ⊆ RX') (hY : RY ⊆ RY') :
    gScale κ T k RX RY ≤ gScale κ T k RX' RY' ∧
      qScale κ T k RX RY ≤ qScale κ T k RX' RY' := by
  sorry

/-- D13.1(iv): bias witnesses are invariant under swapping the stage and its two sides. -/
theorem biasWitness_swap_iff (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) :
    BiasWitness κ T.swap k RY RX b ↔ BiasWitness κ T k RX RY b := by
  sorry

/-- D13.1(iv): cluster witnesses transfer under swapping the stage, sides, and orientation. -/
theorem clusterWitness_swap_iff (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (b : ℕ) :
    (∃ o, CluScaleWitness κ T.swap k RY RX b o) ↔
      (∃ o, CluScaleWitness κ T k RX RY b o) := by
  sorry

/- D13.1's specification is kept as a named interface so downstream nodes can
consume all of its clauses together. -/
structure ResidualScaleSpec : Prop where
  g_dyadic : ∀ κ T k RX RY, IsDyadic (gScale κ T k RX RY)
  q_dyadic : ∀ κ T k RX RY, IsDyadic (qScale κ T k RX RY)
  g_empty : ∀ κ T k RX RY,
    (∀ j, 1 ≤ j → ¬ BiasWitness κ T k RX RY (2 ^ j)) →
      gScale κ T k RX RY = 1
  q_empty : ∀ κ T k RX RY,
    (∀ j, 1 ≤ j → ¬ ∃ o, CluScaleWitness κ T k RX RY (2 ^ j) o) →
      qScale κ T k RX RY = 1
  bias_witness : ∀ κ T k RX RY, 2 ≤ gScale κ T k RX RY →
    BiasWitness κ T k RX RY (gScale κ T k RX RY)
  cluster_witness : ∀ κ T k RX RY, 2 ≤ qScale κ T k RX RY →
    ∃ o, CluScaleWitness κ T k RX RY (qScale κ T k RX RY) o
  bias_absent : ∀ κ T k RX RY b, IsDyadic b → gScale κ T k RX RY < b →
    b ≤ 2 * T.S.n k + 1 → ¬ BiasWitness κ T k RX RY b
  cluster_absent : ∀ κ T k RX RY b, IsDyadic b → qScale κ T k RX RY < b →
    b ≤ T.S.N k + 1 → ¬ ∃ o, CluScaleWitness κ T k RX RY b o
  monotone : ∀ κ T k RX RX' RY RY', RX ⊆ RX' → RY ⊆ RY' →
    gScale κ T k RX RY ≤ gScale κ T k RX' RY' ∧
      qScale κ T k RX RY ≤ qScale κ T k RX' RY'
  bias_swap : ∀ κ T k RX RY b,
    BiasWitness κ T.swap k RY RX b ↔ BiasWitness κ T k RX RY b
  cluster_swap : ∀ κ T k RX RY b,
    (∃ o, CluScaleWitness κ T.swap k RY RX b o) ↔
      (∃ o, CluScaleWitness κ T k RX RY b o)

/-- D13.1: the specification assembly is proved from its six separate facts. -/
theorem d13_1_residual_scale_specification : ResidualScaleSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gScale_isDyadic
  · exact qScale_isDyadic
  · exact gScale_eq_one_of_no_witness
  · exact qScale_eq_one_of_no_witness
  · intro κ T k RX RY h
    exact gScale_witness κ T k RX RY h
  · intro κ T k RX RY h
    exact qScale_witness κ T k RX RY h
  · intro κ T k RX RY b hb hscale hrange
    exact gScale_absent κ T k RX RY b hb hscale hrange
  · intro κ T k RX RY b hb hscale hrange
    exact qScale_absent κ T k RX RY b hb hscale hrange
  · intro κ T k RX RX' RY RY' hX hY
    exact residual_scales_mono κ T k hX hY
  · exact biasWitness_swap_iff
  · exact clusterWitness_swap_iff

end HypercubeRamsey.S13
