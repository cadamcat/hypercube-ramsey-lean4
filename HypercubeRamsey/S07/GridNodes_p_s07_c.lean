import HypercubeRamsey.S07.GridNodes

open OAI.HypercubeRamsey
open HypercubeRamsey
open HypercubeRamsey.S07
open scoped BigOperators

private lemma dirac_width_of_cap {n N : ℕ} (x : Fin N) (hN : 0 < N)
    (hcap : (N : ℝ) ≤ Real.exp ((n : ℝ) ^ 2)) :
    (Law.dirac x).WidthLE ((n : ℝ) ^ 2) := by
  intro y
  change (if y = x then 1 else 0) ≤ Real.exp ((n : ℝ) ^ 2) / (N : ℝ)
  by_cases hy : y = x
  · simp [hy]
    exact (le_div_iff₀ (by exact_mod_cast hN)).2 (by simpa using hcap)
  · simp [hy]
    exact div_nonneg (Real.exp_nonneg _) (by positivity)

private lemma point_pair_pure {n N : ℕ} (E : Fin N → Fin N → Prop) (x y : Fin N)
    (hxy : E x y)
    (hμ : (Law.dirac x).WidthLE ((n : ℝ) ^ 2))
    (hν : (Law.dirac y).WidthLE ((n : ℝ) ^ 2)) :
    PGridPure true 4 0 n N E (Law.dirac x) (Law.dirac y) := by
  have hfour : (4 : ℝ) / 2 = 2 := by norm_num
  have hμ' : (Law.dirac x).WidthLE ((n : ℝ) ^ ((4 : ℝ) / 2)) := by simpa [hfour] using hμ
  have hν' : (Law.dirac y).WidthLE ((n : ℝ) ^ ((4 : ℝ) / 2)) := by simpa [hfour] using hν
  refine ⟨hμ', hν', ?_⟩
  intro z hz
  have hzy : z = y := by
    by_contra hne
    simp [Law.dirac, hne] at hz
  subst z
  have hdeg : colDeg E true (Law.dirac x) y = 1 := by
    unfold colDeg
    rw [Finset.sum_eq_single x]
    · simp [Law.dirac, Hits, hxy]
    · intro z hz hzx
      simp [Law.dirac, hzx]
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  rw [hdeg]
  simpa only [Real.rpow_zero] using (sub_le_self 1 (Real.exp_nonneg (-1 : ℝ)))

private noncomputable def closedGateProfiles {n N : ℕ} (E : Fin N → Fin N → Prop)
    (μ ν : Law N) (hμwidth : μ.WidthLE ((n : ℝ) ^ 2))
    (hνwidth : ν.WidthLE ((n : ℝ) ^ 2))
    (hpure : PGridPure true 4 0 n N E μ ν)
    (hcap : ∀ x, (N : ℝ) * μ.w x ≤ (N : ℝ)) :
    GridProfiles n N E true Finset.univ Finset.univ 4 0 Unit Unit := by
  have hfour : (4 : ℝ) / 2 = 2 := by norm_num
  have hμwidth' : μ.WidthLE ((n : ℝ) ^ ((4 : ℝ) / 2)) := by simpa [hfour] using hμwidth
  have hνwidth' : ν.WidthLE ((n : ℝ) ^ ((4 : ℝ) / 2)) := by simpa [hfour] using hνwidth
  let menu : TagMix N := {
    ι := Unit
    Λ := fun _ => 1
    Λ_nonneg := by intro i; norm_num
    Λ_sum := by simp
    μ := fun _ => μ
    ν := fun _ => ν
  }
  refine {
    menu := menu
    q := fun _ _ => 1
    K := (N : ℝ)
    Ktyp := (N : ℝ)
    vertexCell := fun _ => ((), ())
    menu_properties := ?_
    crossPass := fun _ _ _ _ => True
    ownPass := fun _ _ _ _ => False
    anchorNames := fun _ _ _ _ => []
    p := fun _ _ _ _ _ => 0
    p_eq := ?_
    q_nonneg := by intro g i; norm_num
    q_sum := by intro g; simp
    mu_mean_bound := ?_
    p_nonneg := by intro g t σ W y; norm_num
    p_subprob := by intro g t σ W; simp
    p_mean_bound := ?_
  }
  · intro i hi
    have hi' : i = () := Subsingleton.elim _ _
    subst i
    exact ⟨by intro x hx; exact (hx (Finset.mem_univ x)).elim,
      by intro y hy; exact (hy (Finset.mem_univ y)).elim,
      hμwidth', hνwidth', hpure⟩
  · intro g t σ W y
    simp
  · intro g x
    simpa using hcap x
  · intro g t y
    simp

private noncomputable def unitTagOutcome {n N : ℕ} {E : Fin N → Fin N → Prop}
    (P : GridProfiles n N E true Finset.univ Finset.univ 4 0 Unit Unit)
    (tag : P.menu.ι)
    (hcross : ∀ g t σ W, P.crossPass g t σ W)
    (htyp : ∀ σ : Unit → P.menu.ι, P.isTypicalTag σ)
    (hbound : 1 - (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n ≤ 1) :
    GridTagOutcome P 0 := by
  letI : DecidableEq Unit := fun a b => Classical.propDecidable (a = b)
  classical
  let τ : Unit → P.menu.ι := fun _ => tag
  refine ⟨{
    w := fun σ => if σ = τ then 1 else 0
    nonneg := by classical intro σ; split_ifs <;> norm_num
    sum_eq_one := by classical simp [τ]
  }, ?_, ?_⟩
  · intro σ hσ hbad
    rcases hbad with ⟨g, t, hgt⟩
    have hzero : P.crossFailureAtTags g t σ = 0 := by
      simp [GridProfiles.crossFailureAtTags, hcross g t σ]
    rw [hzero] at hgt
    norm_num at hgt
  · have hmass : (∑ σ : Unit → P.menu.ι,
        if P.isTypicalTag σ then (if σ = τ then (1 : ℝ) else 0) else 0) = 1 := by
      classical
      simp [htyp, τ]
    change (∑ σ : Unit → P.menu.ι,
      if P.isTypicalTag σ then (if σ = τ then (1 : ℝ) else 0) else 0) ≥
      1 - (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n
    calc
      (∑ σ : Unit → P.menu.ι,
        if P.isTypicalTag σ then (if σ = τ then 1 else 0) else 0) = 1 := hmass
      _ ≥ 1 - (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := hbound

private noncomputable def vacuousAnchorOutcome {N : ℕ} {E : Fin N → Fin N → Prop}
    (P : GridProfiles 2 N E true Finset.univ Finset.univ 4 0 Unit Unit)
    (tag : P.menu.ι) (hgate : ∀ σ W, ¬ P.valid () () σ W)
    (x₀ : Fin N) : GridAnchorOutcome P := by
  letI : DecidableEq Unit := fun a b => Classical.propDecidable (a = b)
  classical
  let ω₀ : (Unit → P.menu.ι) × ((Unit × Unit) → Fin N) := (fun _ => tag, fun _ => x₀)
  refine ⟨{
    w := fun ω => if ω = ω₀ then 1 else 0
    nonneg := by classical intro ω; split_ifs <;> norm_num
    sum_eq_one := by classical simp [ω₀]
  }, ?_, ?_⟩
  · have hmass : (∑ ω : (Unit → P.menu.ι) × ((Unit × Unit) → Fin N),
        if P.allValid ω.1 ω.2 then (if ω = ω₀ then (1 : ℝ) else 0) else 0) = 0 := by
      classical
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hv : P.allValid ω.1 ω.2
      · exact False.elim (hgate ω.1 ω.2 (hv () ()))
      · simp [hv]
    change (∑ ω : (Unit → P.menu.ι) × ((Unit × Unit) → Fin N),
      if P.allValid ω.1 ω.2 then (if ω = ω₀ then (1 : ℝ) else 0) else 0) ≥
      1 - 2 * (2 : ℝ) * (2 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2
    calc
      (∑ ω : (Unit → P.menu.ι) × ((Unit × Unit) → Fin N),
        if P.allValid ω.1 ω.2 then (if ω = ω₀ then 1 else 0) else 0) = 0 := hmass
      _ ≥ 1 - 2 * (2 : ℝ) * (2 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2 := by norm_num
  · intro ω y hall
    exact (hgate ω.1 ω.2 (hall () ())).elim

private lemma alarm_count_2 :
    (3 : ℝ) ^ (2 * 0 + 1) * Real.exp (-(1 / 50 : ℝ) * (500 : ℝ)) ≤
      Real.exp (-(1 / 100 : ℝ) * (500 : ℝ)) := by
  have h5 : 3 ≤ Real.exp (5 : ℝ) := by linarith [Real.add_one_le_exp (5 : ℝ)]
  have hmul : Real.exp (-10 : ℝ) * Real.exp (5 : ℝ) = Real.exp (-5 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  calc
    (3 : ℝ) ^ (2 * 0 + 1) * Real.exp (-(1 / 50 : ℝ) * (500 : ℝ))
        = 3 * Real.exp (-10 : ℝ) := by norm_num
    _ ≤ Real.exp (5 : ℝ) * Real.exp (-10 : ℝ) := by
      exact mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
    _ = Real.exp (-5 : ℝ) := by rw [mul_comm, hmul]
    _ = Real.exp (-(1 / 100 : ℝ) * (500 : ℝ)) := by norm_num

private lemma alarm_count_3 :
    (4 : ℝ) ^ (2 * 0 + 1) * Real.exp (-(1 / 50 : ℝ) * (500 : ℝ)) ≤
      Real.exp (-(1 / 100 : ℝ) * (500 : ℝ)) := by
  have h5 : 4 ≤ Real.exp (5 : ℝ) := by linarith [Real.add_one_le_exp (5 : ℝ)]
  have hmul : Real.exp (-10 : ℝ) * Real.exp (5 : ℝ) = Real.exp (-5 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  calc
    (4 : ℝ) ^ (2 * 0 + 1) * Real.exp (-(1 / 50 : ℝ) * (500 : ℝ))
        = 4 * Real.exp (-10 : ℝ) := by norm_num
    _ ≤ Real.exp (5 : ℝ) * Real.exp (-10 : ℝ) := by
      exact mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
    _ = Real.exp (-5 : ℝ) := by rw [mul_comm, hmul]
    _ = Real.exp (-(1 / 100 : ℝ) * (500 : ℝ)) := by norm_num

private noncomputable def zeroAlarm {n N s q : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (P : GridProfiles n N E G Finset.univ Finset.univ 4 0 Unit Unit)
    (hcount : (n + 1 : ℝ) ^ (2 * s + 1) * Real.exp (-(1 / 50 : ℝ) * (q : ℝ)) ≤
      Real.exp (-(1 / 100 : ℝ) * (q : ℝ))) : GridPredictiveAlarms P s q := {
  alarmRate := fun _ _ => 0
  alarm_bound := by intro g t; positivity
  multiplicity_count := hcount
}

private lemma closedGate_false {n N : ℕ} {E : Fin N → Fin N → Prop}
    (P : GridProfiles n N E true Finset.univ Finset.univ 4 0 Unit Unit)
    (hown : ∀ σ W, ¬ P.ownPass () () σ W) :
    ∀ σ W, ¬ P.valid () () σ W := by
  intro σ W h
  exact hown σ W h.2

private def E3 : Fin 1 → Fin 1 → Prop := fun _ _ => True
private noncomputable def P3 : GridProfiles 3 1 E3 true Finset.univ Finset.univ 4 0 Unit Unit := by
  have hcapExp : ((1 : ℕ) : ℝ) ≤ Real.exp ((3 : ℝ) ^ 2) := by
    rw [show (3 : ℝ) ^ 2 = 9 by norm_num]
    have h : (10 : ℝ) ≤ Real.exp 9 := by linarith [Real.add_one_le_exp (9 : ℝ)]
    exact le_trans (by norm_num) h
  have hw : (Law.dirac (0 : Fin 1)).WidthLE ((3 : ℝ) ^ 2) :=
    dirac_width_of_cap (n := 3) (N := 1) 0 (by norm_num) hcapExp
  have hp : PGridPure true 4 0 3 1 E3 (Law.dirac 0) (Law.dirac 0) :=
    point_pair_pure E3 0 0 trivial hw hw
  have hcap : ∀ y, ((1 : ℕ) : ℝ) * (Law.dirac (0 : Fin 1)).w y ≤ (1 : ℕ) := by
    intro y
    by_cases hy : y = 0
    · subst y; simp [Law.dirac]
    · simp [Law.dirac, hy]
  exact closedGateProfiles E3 _ _ hw hw hp (by simpa using hcap)

private lemma P3_typical : ∀ σ : Unit → P3.menu.ι, P3.isTypicalTag σ := by
  intro σ x
  by_cases hx : x = 0
  · subst x
    simp [P3, closedGateProfiles, Law.dirac]
  · simp [P3, closedGateProfiles, Law.dirac, hx]

private lemma P3_cross : ∀ g t σ W, P3.crossPass g t σ W := by
  intro g t σ W
  simp [P3, closedGateProfiles]
private noncomputable def T3 : GridTagOutcome P3 0 :=
  unitTagOutcome P3 (by change Unit; exact ()) P3_cross P3_typical (by norm_num)

private lemma no_anchor_outcome_P3 : ¬ Nonempty (GridAnchorOutcome P3) := by
  rintro ⟨W⟩
  have hgood := W.good_mass
  simp [GridProfiles.allValid, GridProfiles.valid, P3, closedGateProfiles] at hgood
  norm_num at hgood

private noncomputable def A3 : GridPredictiveAlarms P3 0 500 :=
  zeroAlarm P3 (by convert alarm_count_3 using 1 <;> norm_num)

private def E2one : Fin 1 → Fin 1 → Prop := fun _ _ => True
private noncomputable def P2one : GridProfiles 2 1 E2one true Finset.univ Finset.univ 4 0 Unit Unit := by
  have hcapExp : ((1 : ℕ) : ℝ) ≤ Real.exp ((2 : ℝ) ^ 2) := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    have h : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact le_trans (by norm_num) h
  have hw : (Law.dirac (0 : Fin 1)).WidthLE ((2 : ℝ) ^ 2) :=
    dirac_width_of_cap (n := 2) (N := 1) 0 (by norm_num) hcapExp
  have hp : PGridPure true 4 0 2 1 E2one (Law.dirac 0) (Law.dirac 0) :=
    point_pair_pure E2one 0 0 trivial hw hw
  have hcap : ∀ y, ((1 : ℕ) : ℝ) * (Law.dirac (0 : Fin 1)).w y ≤ (1 : ℕ) := by
    intro y
    by_cases hy : y = 0
    · subst y; simp [Law.dirac]
    · simp [Law.dirac, hy]
  exact closedGateProfiles E2one _ _ hw hw hp (by simpa using hcap)

private lemma P2one_typical : ∀ σ : Unit → P2one.menu.ι, P2one.isTypicalTag σ := by
  intro σ x
  by_cases hx : x = 0
  · subst x
    simp [P2one, closedGateProfiles, Law.dirac]
  · simp [P2one, closedGateProfiles, Law.dirac, hx]

private lemma P2one_cross : ∀ g t σ W, P2one.crossPass g t σ W := by
  intro g t σ W
  simp [P2one, closedGateProfiles]
private lemma P2one_gate : ∀ σ W, ¬ P2one.valid () () σ W :=
  closedGate_false P2one (by intro σ W; simp [P2one, closedGateProfiles])

private noncomputable def T2one : GridTagOutcome P2one 0 :=
  unitTagOutcome P2one (by change Unit; exact ()) P2one_cross P2one_typical (by norm_num)

private noncomputable def A2one : GridPredictiveAlarms P2one 0 500 :=
  zeroAlarm P2one (by convert alarm_count_2 using 1 <;> norm_num)

private noncomputable def W2one : GridAnchorOutcome P2one :=
  vacuousAnchorOutcome P2one (by change Unit; exact ()) P2one_gate 0

private def evenBase : CubeVertex 2 := fun _ => false

private lemma evenBase_even : IsEvenRole evenBase := by
  simp [IsEvenRole, evenBase]

private def odd2a : {v : CubeVertex 2 // ¬ IsEvenRole v} :=
  ⟨fun i => decide (i = 0), by
    classical
    change ¬ Even (Finset.univ.filter (fun i : Fin 2 => decide (i = 0))).card
    have hc : (Finset.univ.filter (fun i : Fin 2 => decide (i = 0))).card = 1 := by decide
    rw [hc]
    norm_num⟩

private def odd2b : {v : CubeVertex 2 // ¬ IsEvenRole v} :=
  ⟨fun i => decide (i = 1), by
    classical
    change ¬ Even (Finset.univ.filter (fun i : Fin 2 => decide (i = 1))).card
    have hc : (Finset.univ.filter (fun i : Fin 2 => decide (i = 1))).card = 1 := by decide
    rw [hc]
    norm_num⟩

private lemma odd2a_ne_odd2b : odd2a ≠ odd2b := by
  intro h
  have hv := congrArg Subtype.val h
  have h0 := congrFun hv (0 : Fin 2)
  have hfalse : true = false := by simpa [odd2a, odd2b] using h0
  cases hfalse

private lemma no_posterior_on_fin_one :
    ¬ Nonempty (GridPosteriorRows (n := 2) E2one true 500) := by
  rintro ⟨R⟩
  have hm : R.oddMap odd2a = R.oddMap odd2b := Subsingleton.elim _ _
  exact odd2a_ne_odd2b (R.odd_injective hm)

private def Eload : Fin 4 → Fin 4 → Prop := fun x _ => x = 0 ∨ x = 1
private noncomputable def Pload : GridProfiles 2 4 Eload true Finset.univ Finset.univ 4 0 Unit Unit := by
  have hcapExp : ((4 : ℕ) : ℝ) ≤ Real.exp ((2 : ℝ) ^ 2) := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    have h : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact le_trans (by norm_num) h
  have hw : (Law.dirac (0 : Fin 4)).WidthLE ((2 : ℝ) ^ 2) :=
    dirac_width_of_cap (n := 2) (N := 4) 0 (by norm_num) hcapExp
  have hp : PGridPure true 4 0 2 4 Eload (Law.dirac 0) (Law.dirac 0) :=
    point_pair_pure Eload 0 0 (Or.inl rfl) hw hw
  have hcap : ∀ y, ((4 : ℕ) : ℝ) * (Law.dirac (0 : Fin 4)).w y ≤ (4 : ℕ) := by
    intro y
    by_cases hy : y = 0
    · subst y; simp [Law.dirac]
    · simp [Law.dirac, hy]
  exact closedGateProfiles Eload _ _ hw hw hp (by simpa using hcap)

private lemma Pload_typical : ∀ σ : Unit → Pload.menu.ι, Pload.isTypicalTag σ := by
  intro σ x
  by_cases hx : x = 0
  · subst x
    simp [Pload, closedGateProfiles, Law.dirac]
  · simp [Pload, closedGateProfiles, Law.dirac, hx]

private lemma Pload_cross : ∀ g t σ W, Pload.crossPass g t σ W := by
  intro g t σ W
  simp [Pload, closedGateProfiles]
private lemma Pload_gate : ∀ σ W, ¬ Pload.valid () () σ W :=
  closedGate_false Pload (by intro σ W; simp [Pload, closedGateProfiles])

private noncomputable def Tload : GridTagOutcome Pload 0 :=
  unitTagOutcome Pload (by change Unit; exact ()) Pload_cross Pload_typical (by norm_num)

private noncomputable def Wload : GridAnchorOutcome Pload :=
  vacuousAnchorOutcome Pload (by change Unit; exact ()) Pload_gate 0

private noncomputable def cubeFinEquiv2 : CubeVertex 2 ≃ Fin 4 := by
  have hc : Fintype.card (CubeVertex 2) = 4 := by rw [card_cubeVertex]; norm_num
  exact (Fintype.equivFin (CubeVertex 2)).trans (finCongr hc)

private noncomputable def Rload : GridPosteriorRows (n := 2) Eload true 500 := by
  refine {
    oddMap := fun b => cubeFinEquiv2 b.1
    odd_injective := ?_
    evenRow := fun _ x => if x = 1 then 1 else 0
    row_nonneg := ?_
    row_sum := ?_
    common_neighbour := ?_
    row_cap := ?_
  }
  · intro b c h
    apply Subtype.ext
    exact cubeFinEquiv2.injective h
  · intro a x
    split_ifs <;> norm_num
  · intro a
    simp
  · intro a x hx b hab
    have h : x = (1 : Fin 4) := by
      by_contra hne
      simp [hne] at hx
    subst x
    simp [Eload, Hits]
  · intro a x
    by_cases hx : x = 1
    · subst x
      norm_num
      linarith [Real.add_one_le_exp (30 : ℝ)]
    · simp [hx]
      positivity

private def even00 : {v : CubeVertex 2 // IsEvenRole v} := ⟨evenBase, evenBase_even⟩

private def even11 : {v : CubeVertex 2 // IsEvenRole v} :=
  ⟨fun _ => true, by simp [IsEvenRole]⟩

private lemma even00_ne_even11 : even00 ≠ even11 := by
  intro h
  have hv := congrArg Subtype.val h
  have h0 := congrFun hv (0 : Fin 2)
  simp [even00, even11, evenBase] at h0

private lemma Rload_bad_load :
    ¬ (∀ x, ∑ a : {v : CubeVertex 2 // IsEvenRole v}, Rload.evenRow a x ≤ 1) := by
  intro h
  have hx := h (1 : Fin 4)
  let s : Finset {v : CubeVertex 2 // IsEvenRole v} := {even00, even11}
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  have hsmall : (∑ a ∈ s, Rload.evenRow a (1 : Fin 4)) = 2 := by
    have hs : s.card = 2 := by simp [s, even00_ne_even11]
    calc
      (∑ a ∈ s, Rload.evenRow a (1 : Fin 4)) = ∑ a ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [Rload]
      _ = (s.card : ℝ) := by simp
      _ = 2 := by rw [hs]; norm_num
  have hle : (∑ a ∈ s, Rload.evenRow a (1 : Fin 4)) ≤
      ∑ a : {v : CubeVertex 2 // IsEvenRole v}, Rload.evenRow a 1 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro a ha hna
      exact Rload.row_nonneg a 1)
  rw [hsmall] at hle
  linarith

private theorem anchor_countermodel :
    ∃ (T : GridTagOutcome P3 0) (A : GridPredictiveAlarms P3 0 500),
    ¬ Nonempty (GridAnchorOutcome P3) := ⟨T3, A3,
      no_anchor_outcome_P3⟩

private theorem posterior_countermodel :
    ∃ (T : GridTagOutcome P2one 0) (A : GridPredictiveAlarms P2one 0 500)
    (W : GridAnchorOutcome P2one),
    ¬ Nonempty (GridPosteriorRows (n := 2) E2one true 500) :=
  ⟨T2one, A2one, W2one, no_posterior_on_fin_one⟩

private theorem load_countermodel :
    ∃ (T : GridTagOutcome Pload 0) (W : GridAnchorOutcome Pload)
    (R : GridPosteriorRows (n := 2) Eload true 500),
    ¬ (∀ x, ∑ a : {v : CubeVertex 2 // IsEvenRole v}, R.evenRow a x ≤ 1) :=
  ⟨Tload, Wload, Rload, Rload_bad_load⟩
