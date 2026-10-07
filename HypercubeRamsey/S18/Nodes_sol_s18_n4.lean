import HypercubeRamsey.S17.Nodes
import HypercubeRamsey.S18.Nodes_q_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4

open Classical Filter
open scoped BigOperators

private theorem graphBall_mono
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} {F : FreshCell G} (E : ListEvent F)
    {A B : Finset (Pos T k)} (hAB : A ⊆ B) (t : ℕ) :
    E.graphBall A t ⊆ E.graphBall B t := by
  induction t with
  | zero => exact hAB
  | succ t ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union.mpr (Or.inl (ih hv))
    · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, ih hu, hadj⟩))

private theorem graphBall_seed
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} {F : FreshCell G} (E : ListEvent F)
    (A : Finset (Pos T k)) (t : ℕ) : A ⊆ E.graphBall A t := by
  induction t with
  | zero => exact Finset.Subset.refl _
  | succ t ih => exact fun _ hv => Finset.mem_union.mpr (Or.inl (ih hv))

noncomputable def poolGateFor
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (pools : ∀ C, D.fresh.Pool C) : Prop :=
  (∀ C ∈ region, D.fresh.typical C (pools C)) ∧
    ∀ v, D.encoding.events.scope v ⊆ region → D.poolListOK pools v

set_option maxHeartbeats 400000 in
theorem finalListTapeBound
    {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec →
      (∀ w, (Finset.univ.filter fun z => D.encoding.events.Adjacent w z).card ≤
        (T.S.n k) ^ (κ.Ac + 4)) →
      ∀ v pools, poolGateFor D (D.initialRegion v) pools →
      (tapeLaw D.fresh D.encoding.Ts).pr (fun tapes =>
        D.encoding.events.S v (D.encoding.initialState (pools, tapes))) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) := by
  filter_upwards [finiteResamplingRootTail κ hκ T,
    T.S.n_tendsto.eventually_ge_atTop 2] with k htail hn
  intro PT hPT D hD hdegree v pools hgate
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
  let E := D.encoding.events
  let Ts := initialResamplingRounds T k
  have hTs : D.encoding.Ts = Ts := D.encoding.Ts_eq
  let events := E.graphBall {v} (2 * Ts + 3)
  have hroot : v ∈ events := graphBall_seed E {v} (2 * Ts + 3) (by simp)
  have hseed : {v} ⊆ (E.scope v).biUnion E.incidentEvents := by
    intro w hw
    have hwv : w = v := by simpa using hw
    subst w
    apply Finset.mem_biUnion.mpr
    refine ⟨D.geom.cellOf v, ?_, ?_⟩
    · rw [hD.scope_eq]
      simp [S18.LateData.directCells]
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hD.scope_eq]
      simp [S18.LateData.directCells]
  have hscopes : events.biUnion E.scope ⊆ D.initialRegion v := by
    intro C hC
    obtain ⟨w, hw, hCw⟩ := Finset.mem_biUnion.mp hC
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, hCw⟩
    rw [hTs]
    exact graphBall_mono E hseed (2 * Ts + 3) hw
  have hinput : FiniteResamplingInput Ctx E events pools ∅ v := by
    refine ⟨hn, hroot, hdegree, by simp, ?_, ?_⟩
    · intro C hC
      apply hgate.1 C
      apply hscopes
      simpa only [Finset.empty_union] using hC
    · intro w hw
      exact hgate.2 w (fun C hC => hscopes
        (Finset.mem_biUnion.mpr ⟨w, hw, hC⟩))
  have hcover : ComponentWitnessCover (D := Ctx) (Ts := Ts) E D.encoding.order events pools v :=
    fun tapes hfinal => finiteResamplingComponent (D := Ctx) E Ts D.encoding.order events pools tapes
      v hroot hfinal
  have hcount : ComponentWitnessCountBound (D := Ctx) (Ts := Ts) E
      ((T.S.n k) ^ (κ.Ac + 4)) events v :=
    finiteResamplingWitnessCount (D := Ctx) E Ts _ events v hdegree
  have htests : WitnessTestBound (D := Ctx) (Ts := Ts) E events pools :=
    finiteResamplingWitnessTests (D := Ctx) E Ts hn events pools hinput.fresh_failure
  have hbound := htail PT Ctx E D.encoding.order events pools ∅ v hinput hcover hcount htests
  change (tapeLaw D.fresh D.encoding.Ts).pr (fun tapes =>
    E.S v (E.resample D.encoding.Ts D.encoding.order Finset.univ pools tapes.extend)) ≤ _
  rw [hTs]
  have heq : (fun tapes : Tapes D.fresh Ts =>
      E.S v (E.resample Ts D.encoding.order Finset.univ pools tapes.extend)) =
      (fun tapes => E.S v (E.resample Ts D.encoding.order events pools tapes.extend)) := by
    funext tapes
    exact propext ((resampleLocality (D := Ctx) E Ts D.encoding.order pools
      tapes.extend).2 v events (Finset.Subset.refl _))
  rw [heq]
  exact hbound

private theorem pr_bind
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P K).pr A = ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := by
  simp [FinLaw.pr, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_ite]

private theorem gated_joint_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A gate : α → Prop)
    (bad : α → β → Prop) (q : ℝ) (hq : 0 ≤ q)
    (hbad : ∀ a, gate a → Q.pr (bad a) ≤ q) :
    (FinLaw.bind P (fun _ => Q)).pr (fun x => A x.1 ∧ gate x.1 ∧ bad x.1 x.2) ≤
      q * P.pr A := by
  rw [pr_bind]
  have hpoint : ∀ a, Q.pr (fun b => A a ∧ gate a ∧ bad a b) ≤
      if A a then q else 0 := by
    intro a
    by_cases ha : A a
    · by_cases hg : gate a
      · simpa [ha, hg] using hbad a hg
      · simpa [FinLaw.pr, ha, hg] using hq
    · simp [FinLaw.pr, ha]
  calc
    (∑ a, P.w a * Q.pr (fun b => A a ∧ gate a ∧ bad a b)) ≤
        ∑ a, P.w a * (if A a then q else 0) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a))
    _ = q * P.pr A := by
      simp [FinLaw.pr, Finset.mul_sum, mul_ite, ite_mul, mul_comm]

private theorem pr_bind_first
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun x => A x.1) = P.pr A := by
  rw [pr_bind]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : A a
  · simp [h, Q.sum_one]
  · simp [h]

theorem finalListPinnedBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} {δ : ℝ} (D : S18.LateData hPT) (v : Pos T k)
    (hn : 1 ≤ T.S.n k)
    (hbad : ∀ pools, poolGateFor D (D.initialRegion v) pools →
      (tapeLaw D.fresh D.encoding.Ts).pr (fun tapes =>
        D.encoding.events.S v (D.encoding.initialState (pools, tapes))) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2))) :
    ∀ pin, S18.initialProbability D pin (S18.terminalFailure D δ (.inr (.inl v))) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  intro pin
  let P := D.encoding.poolLaw
  let Q := tapeLaw D.fresh D.encoding.Ts
  let gate := poolGateFor D (D.initialRegion v)
  let bad := fun pools tapes => D.encoding.events.S v (D.encoding.initialState (pools, tapes))
  let q := Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2))
  have hq : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hweak : q ≤ Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    have hmul : 0 ≤ (κ.P : ℝ) * D.encoding.Ts := by positivity
    nlinarith
  apply le_trans ?_ hweak
  cases pin with
  | none =>
    have h := gated_joint_bound P Q (fun _ => True) gate bad q hq hbad
    have ht : P.pr (fun _ => True) = 1 := by
      simp only [FinLaw.pr, ite_true]
      exact P.sum_one
    rw [ht, mul_one] at h
    change (FinLaw.bind P (fun _ => Q)).pr (fun x => gate x.1 ∧ bad x.1 x.2) ≤ q
    simpa only [true_and] using h
  | some pin =>
    let A := fun pools : ∀ C, D.fresh.Pool C => pools pin.1 pin.2.1 = pin.2.2
    have h := gated_joint_bound P Q A gate bad q hq hbad
    have hden : D.encoding.permLaw.pr (S18.pinEvent D pin) = P.pr A :=
      pr_bind_first P Q A
    change D.encoding.permLaw.pr (fun x => S18.pinEvent D pin x ∧
      S18.terminalFailure D δ (.inr (.inl v)) x) /
      D.encoding.permLaw.pr (S18.pinEvent D pin) ≤ q
    rw [hden]
    by_cases hd : 0 < P.pr A
    · apply (div_le_iff₀ hd).2
      exact h
    · have hzero : P.pr A = 0 := by
        have hnonneg : 0 ≤ P.pr A := by
          unfold FinLaw.pr
          exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [P.nonneg])
        linarith
      simp [hzero, hq]

private def star {n : ℕ} (v : CubePos n) : Finset (CubePos n) :=
  insert v (Finset.univ.image (flipPos v))

private theorem flip_twice {n : ℕ} (v : CubePos n) (a : Fin n) :
    flipPos (flipPos v a) a = v := by
  funext b
  by_cases hab : b = a
  · subst b
    simp [flipPos]
  · simp [flipPos, hab]

private theorem star_symm {n : ℕ} {v w : CubePos n} (hw : w ∈ star v) :
    v ∈ star w := by
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_insert_self _ _
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hw
    subst w
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, flip_twice v a⟩

private theorem star_card {n : ℕ} (v : CubePos n) : (star v).card ≤ n + 1 := by
  calc
    (star v).card ≤ (Finset.univ.image (flipPos v)).card + 1 := Finset.card_insert_le _ _
    _ ≤ n + 1 := by
      have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := flipPos v)
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.add_le_add_right h 1

theorem eventDegreeBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) :
    ∀ w, (Finset.univ.filter fun z => D.encoding.events.Adjacent w z).card ≤
      (T.S.n k) ^ (κ.Ac + 4) := by
  intro w
  let n := T.S.n k
  let cellPositions := fun C => Finset.univ.filter fun v : Pos T k => D.geom.cellOf v = C
  let incident := fun C => (cellPositions C).biUnion star
  have hscope (z : Pos T k) (C : D.geom.Cell)
      (hC : C ∈ D.encoding.events.scope z) :
      ∃ b ∈ star z, D.geom.cellOf b = C := by
    rw [hD.scope_eq] at hC
    rcases Finset.mem_union.mp hC with hown | hext
    · have hown' : D.geom.cellOf z = C := (Finset.mem_singleton.mp hown).symm
      exact ⟨z, Finset.mem_insert_self _ _, hown'⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hext
      exact ⟨flipPos z a, Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨a, Finset.mem_univ _, rfl⟩), rfl⟩
  have hincident (C : D.geom.Cell) : (incident C).card ≤ n ^ κ.Ac * (n + 1) := by
    calc
      (incident C).card ≤ (cellPositions C).card * (n + 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => star_card b)
      _ ≤ n ^ κ.Ac * (n + 1) := Nat.mul_le_mul_right _ (D.l16_valid.cell_size C)
  have hscopeCard : (D.encoding.events.scope w).card ≤ n + 1 := by
    rw [hD.scope_eq]
    calc
      (D.directCells w).card ≤ 1 + (D.externalEarly w).card := by
        apply le_trans (Finset.card_union_le _ _)
        simpa only [Finset.card_singleton] using Nat.add_le_add_left
          (Finset.card_image_le (s := D.externalEarly w)
            (f := fun a => D.geom.cellOf (flipPos w a))) 1
      _ ≤ n + 1 := by
        have hcard : (D.externalEarly w).card ≤ n := by
          simpa only [S18.LateData.externalEarly, Finset.card_univ, Fintype.card_fin] using
            Finset.card_le_card (Finset.filter_subset
            (fun a : Fin n => a ∉ PT.tiling.Icoord (D.geom.patchOf w) ∧
              D.geom.classOf (flipPos w a) = none) Finset.univ)
        omega
  have hsub : (Finset.univ.filter fun z => D.encoding.events.Adjacent w z) ⊆
      (D.encoding.events.scope w).biUnion incident := by
    intro z hz
    have hnot := (Finset.mem_filter.mp hz).2.2
    obtain ⟨C, hwC, hzC⟩ := Finset.not_disjoint_iff.mp hnot
    obtain ⟨b, hb, hbC⟩ := hscope z C hzC
    apply Finset.mem_biUnion.mpr
    refine ⟨C, hwC, Finset.mem_biUnion.mpr ⟨b, ?_, star_symm hb⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbC⟩
  have hpoly : (n + 1) * (n ^ κ.Ac * (n + 1)) ≤ n ^ (κ.Ac + 4) := by
    have hn1 : n + 1 ≤ n ^ 2 := by
      have h2 : 2 ≤ n := hn
      nlinarith
    calc
      (n + 1) * (n ^ κ.Ac * (n + 1)) = n ^ κ.Ac * ((n + 1) * (n + 1)) := by ring
      _ ≤ n ^ κ.Ac * (n ^ 2 * n ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hn1 hn1)
      _ = n ^ (κ.Ac + 4) := by rw [pow_add]; ring
  calc
    (Finset.univ.filter fun z => D.encoding.events.Adjacent w z).card ≤
        ((D.encoding.events.scope w).biUnion incident).card := Finset.card_le_card hsub
    _ ≤ (D.encoding.events.scope w).card * (n ^ κ.Ac * (n + 1)) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun C _ => hincident C)
    _ ≤ (n + 1) * (n ^ κ.Ac * (n + 1)) := Nat.mul_le_mul_right _ hscopeCard
    _ ≤ n ^ (κ.Ac + 4) := hpoly

end HypercubeRamsey.Lane_sol_s18_n4
