import HypercubeRamsey.S06.Selection

/-!
Concrete counterexamples to the frozen L6.1i and L6.1j conclusions.
This file is kept standalone because the owned declarations precede the data
types needed to state these examples.
-/

namespace HypercubeRamsey.S06

open scoped BigOperators

private def singletonProb : FinProb PUnit where
  w _ := 1
  nonneg _ := by norm_num
  sum_eq_one := by simp

private def badHeight : HeightSetup6 1 PUnit PUnit PUnit PUnit PUnit where
  height := 0
  lambda := 1
  T := 1
  k := 0
  radius := 0
  rawLaw := singletonProb
  prospective := fun _ _ _ => {PUnit.unit}
  oddStar := fun _ => {PUnit.unit}
  descriptorIds := fun _ => ∅
  descriptorsAt := fun _ _ => {PUnit.unit}
  failsStep3 := fun _ _ _ => True
  failedIDSet := fun _ _ _ => True
  incidentInputsAgree := fun _ _ _ => True

private theorem badHeight_hypotheses : HeightHypotheses6 badHeight := by
  classical
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro s l
    simp [badHeight, singletonProb, FinProb.pr]
    positivity
  · intro b d
    simp [badHeight, singletonProb, FinProb.pr]
  · intro b
    norm_num [badHeight]
  · intro b D hD
    simp [badHeight, singletonProb, FinProb.pr]

private theorem badHeight_no_conclusion :
    ¬ ∃ o : HeightOutcome6 badHeight, ∃ c : ℝ, HeightConclusion6 badHeight o c := by
  classical
  rintro ⟨o, c, hc⟩
  rcases hc with ⟨_, hmarker, _, _, _, hmax, hcard, _⟩
  have hno : ¬ o.markerSuccess PUnit.unit := by
    intro hm
    have hfamily : o.markFamily PUnit.unit PUnit.unit (0, 0) = ∅ := by
      have hlt : (o.markFamily PUnit.unit PUnit.unit (0, 0)).card < 1 := by
        simpa [badHeight] using hcard PUnit.unit hm PUnit.unit (0, 0)
      have hzero : (o.markFamily PUnit.unit PUnit.unit (0, 0)).card = 0 :=
        Nat.lt_one_iff.mp hlt
      exact Finset.card_eq_zero.mp hzero
    have hcompl := hmax PUnit.unit hm PUnit.unit (0, 0)
      (∅ : Finset (ArrayIndex6 PUnit PUnit)) trivial
      (by simp [hfamily])
    simpa [hfamily] using hcompl
  have hz : badHeight.rawLaw.pr o.markerSuccess = 0 := by
    simp [FinProb.pr, singletonProb, hno]
  have hp := hmarker
  rw [hz] at hp
  have he : Real.exp (-(1 : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    norm_num
  have hp' : 0 ≥ 1 - Real.exp (-(1 : ℝ)) := by simpa using hp
  linarith

private noncomputable def singletonLaw : Law 1 := by
  classical
  exact Law.dirac 0

private def badTable : AdjustmentTable6 1 PUnit PUnit where
  likelihood := fun _ _ => 1
  adjustment := fun _ _ => 1
  referenceDensity := fun _ => 1
  targetExperiment := fun _ => singletonProb
  presented := fun _ _ => True
  adjustment_nonneg := by norm_num
  adjustment_le_one := by norm_num
  reference_nonneg := by norm_num
  density_identity := by
    intro r y
    simp [singletonProb, FinProb.pr]
  presentations_disjoint := by
    intro ω r r' _ _
    exact Subsingleton.elim _ _

private noncomputable def badOddInput : OddPosteriorInput6 1 1 0 0 PUnit PUnit PUnit where
  centerLaw := fun _ => singletonProb
  low := fun _ => False
  prior := fun _ => singletonLaw
  table := fun _ => badTable
  presentedRecord := fun _ _ => PUnit.unit
  valid := fun _ _ => True
  records := fun _ => {PUnit.unit}
  records_cover_presentations := by simp
  record_count_small := by
    intro b
    norm_num
  deletionReference := fun _ _ _ => -1
  sameModeAndPrimary := fun _ _ => True
  commonNeighbor := fun _ _ => True
  J := 0
  step3Failure := fun _ _ _ => False
  step3_failure_mass := by
    intro b r hr
    simp [FinProb.pr]
  likelihood_nonneg := by
    intro b r y hr
    norm_num [badTable]
  likelihood_mass_pos := by
    intro b r hr
    norm_num [likelihoodMass6, singletonLaw, Law.dirac, badTable]
  basePosterior := fun _ _ _ => 1
  basePosterior_exact := by
    intro b r y hr
    have hy : y = 0 := Subsingleton.elim _ _
    subst y
    norm_num [likelihoodMass6, singletonLaw, Law.dirac, badTable]
  basePosterior_deletion := by
    intro b r c y hr hlo
    exact False.elim hlo
  basePosterior_cap := by
    intro b r y hr
    norm_num [likelihoodMass6, singletonLaw, Law.dirac, badTable]
  basePosterior_common_support := by
    intro b r y hr hpos
    trivial

private theorem badOddInput_no_rows : ¬ Nonempty (SelectedOddRows6 badOddInput) := by
  classical
  rintro ⟨R⟩
  have hnonneg := R.row_nonneg PUnit.unit PUnit.unit 0
  have hdel := R.matching_deletion_bound PUnit.unit PUnit.unit PUnit.unit 0 (by trivial) (by trivial)
  norm_num [badOddInput] at hdel
  linarith

end HypercubeRamsey.S06
