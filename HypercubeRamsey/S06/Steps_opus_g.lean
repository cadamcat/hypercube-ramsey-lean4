import HypercubeRamsey.S06.Steps_marginal_sol_s06_g

/-!
# High Step 3 raw tests: marginalizing the raw experiment onto the local joint model

L6.1g (tests), 06:386–426.  The raw true-gated failure probability of a high-target Step 3 test equals the
`π⁰`-mixture, over the target `ξ`, of the local joint model `jointActual` (the original local base and hidden
kernels of `H_loc` with the target substituted, then the observed tuples).  Unused exterior variables
(candidates outside the window, tags outside `locKeys`, hidden scalars outside `locHid`, tuples outside `D`)
are integrated out.  At a candidate target the target coordinate is split off the candidate product; at the
initial target the outer `V₀` integral is the prior itself.
-/

namespace HypercubeRamsey.S06.Lane_opus_g
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

/-! ### Generic finite-probability identities -/

theorem bind_expect' {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (K : α → FinProb β)
    (g : α × β → ℝ) :
    (FinProb.bind P K).expect g = ∑ a, P.w a * (K a).expect (fun b => g (a, b)) :=
  FinProb.bind_expect P K (fun a b => g (a, b))

theorem pr_congr' {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop} (h : ∀ ω, A ω ↔ B ω) :
    P.pr A = P.pr B := by
  have hAB : A = B := funext fun ω => propext (h ω)
  rw [hAB]

/-- Splitting one coordinate `u` off a product law and marginalizing all coordinates outside `insert u L`. -/
theorem pi_expect_window_subst {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (u : I) (L : Finset I) (hu : u ∉ L) (z₀ : I → Ω) (f : (I → Ω) → ℝ)
    (hf : FinProb.DependsOn f (insert u L)) :
    (FinProb.pi P).expect f =
      ∑ ξ, (P u).w ξ * (FinProb.pi (fun i : {i : I // i ∈ L} => P i.1)).expect
        (fun x => f (Function.update (Lane_sol_s06_steps1.fill L x z₀) u ξ)) := by
  have hg : FinProb.DependsOn
      (fun z : I → Ω => (P u).expect (fun i => f (Function.update z u i))) L := by
    intro z z' hz
    show (P u).expect (fun i => f (Function.update z u i)) = (P u).expect (fun i => f (Function.update z' u i))
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply hf
    intro j hj
    by_cases hju : j = u
    · subst hju
      simp
    · rw [Function.update_apply, Function.update_apply, if_neg hju, if_neg hju]
      exact hz j ((Finset.mem_insert.mp hj).resolve_left hju)
  rw [Lane_sol_s06_steps1.pi_expect_resample P u (z₀ u) f,
    Lane_sol_s06_steps1.pi_expect_fill _ L _ z₀ hg]
  have hR : (FinProb.pi fun i : {i : I // i ∈ L} =>
      (fun j => if j = u then pointMass6 (z₀ u) else P j) i.1) =
      FinProb.pi fun i : {i : I // i ∈ L} => P i.1 := by
    congr 1
    funext i
    have hne : i.1 ≠ u := fun h => hu (h ▸ i.2)
    simp only [hne, ite_false]
  rw [hR]
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro x _
  ring

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)
variable {Id : Type} [Fintype Id] [DecidableEq Id]

/-! ### Locality of the raw experiment around `H_loc` -/

/-- Agreement of every primitive observation read by the local model, and of the target value. -/
def RawLocal (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist) : Prop :=
  Lane_sol_s06_g.LocalAgree X nm D H H' ∧ (X.parOf H.1).val nm = (X.parOf H'.1).val nm

/-- The tag and hidden part of `H_loc` at fixed parents `(v, A)`, integrated against the original kernels. -/
def localInner (v : Fin N) (D : Finset (Id × X.Ty)) (F : X.Hist → ℝ) (A : X.Bin → Fin N) : ℝ :=
  (FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} => X.tagLawAt (v, A) s.1).expect (fun I =>
    (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} =>
      X.hidPost (v, A, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)) ℓ.1.1).expect
      (fun Z => F ((v, A, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)),
        Lane_sol_s06_steps1.fill (X.locHid D) Z (fun _ => X.y₀))))

theorem coarse_inner_eq (v : Fin N) (D : Finset (Id × X.Ty)) (F : X.Hist → ℝ)
    (hF : ∀ (A : X.Bin → Fin N) (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ s ∈ X.locKeys D, I s = I' s) → (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) →
      F ((v, A, I), Z) = F ((v, A, I'), Z')) :
    (X.coarseLaw v).expect (fun AI => (X.hidLaw (v, AI)).expect (fun Z => F ((v, AI), Z))) =
      (FinProb.pi fun _ : X.Bin => X.candLaw v).expect (localInner X v D F) := by
  have h := FinProb.bind_expect (FinProb.pi fun _ : X.Bin => X.candLaw v)
    (fun A => FinProb.pi (X.tagLawAt (v, A)))
    (fun A I => (X.hidLaw (v, A, I)).expect (fun Z => F ((v, A, I), Z)))
  calc (X.coarseLaw v).expect (fun AI => (X.hidLaw (v, AI)).expect (fun Z => F ((v, AI), Z)))
      = ∑ A, (FinProb.pi fun _ : X.Bin => X.candLaw v).w A *
          (FinProb.pi (X.tagLawAt (v, A))).expect
            (fun I => (X.hidLaw (v, A, I)).expect (fun Z => F ((v, A, I), Z))) := h
    _ = ∑ A, (FinProb.pi fun _ : X.Bin => X.candLaw v).w A * localInner X v D F A := by
        apply Finset.sum_congr rfl
        intro A _
        exact congrArg (fun t => (FinProb.pi fun _ : X.Bin => X.candLaw v).w A * t)
          (Lane_sol_s06_g.fixed_parent_marginal X (v, A) D F
            (fun I I' Z Z' hI hZ => hF A I I' Z Z' hI hZ))
    _ = _ := rfl

theorem localInner_dep (v : Fin N) (D : Finset (Id × X.Ty)) (S : Finset X.Bin)
    (hS : X.binsOf (X.locKeys D) ⊆ S) (F : X.Hist → ℝ)
    (hF : ∀ (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ w ∈ S, A w = A' w) → (∀ s ∈ X.locKeys D, I s = I' s) → (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) →
      F ((v, A, I), Z) = F ((v, A', I'), Z')) :
    FinProb.DependsOn (localInner X v D F) S := by
  intro A A' hA
  have htags : (FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} => X.tagLawAt (v, A) s.1) =
      FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} => X.tagLawAt (v, A') s.1 := by
    congr 1
    funext s
    have hbin := hA s.1.1 (hS (Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩))
    cases hf : s.1.2 <;> simp only [Ctx6.tagLawAt, primaryName6, otherPrimaryName6, hf, Par6.val, hbin]
  have hhid (I : {s : X.Key // s ∈ X.locKeys D} → X.ι) :
      (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} =>
        X.hidPost (v, A, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)) ℓ.1.1) =
      FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} =>
        X.hidPost (v, A', Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)) ℓ.1.1 := by
    congr 1
    funext ℓ
    unfold Ctx6.hidPost
    congr 1
    funext y
    have hC : X.C ℓ.1.1 ⊆ X.locKeys D := by
      intro s hs
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ.1, ℓ.2, hs⟩)
    have hCB : X.binsOf (X.C ℓ.1.1) ⊆ S := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨s, hs, rfl⟩
      exact hS (Finset.mem_image.mpr ⟨s, hC hs, rfl⟩)
    exact Lane_sol_s06_steps1.hidWeight_local X ℓ.1.1 (X.C ℓ.1.1) (Finset.Subset.refl _)
      (v, A, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀))
      (v, A', Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀))
      (fun _ => rfl) (fun _ w hw => hA w (hCB hw)) (fun s hs => rfl) y
  unfold localInner
  rw [htags]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  beta_reduce
  rw [hhid I]
  apply Finset.sum_congr rfl
  intro Z _
  congr 1
  exact hF A A' _ _ _ _ hA (fun s hs => rfl) (fun ℓ hℓ => rfl)

/-- Candidate target `A_u` (06:370–373, 06:386–389): split `A_u` off the candidate product; the remaining
candidates, tags and hidden scalars outside `H_loc` integrate out. -/
theorem candidate_marginal (v : Fin N) (nm : ParentName6 X.Bin) (u : X.Bin) (hnm : nm = .candidate u)
    (D : Finset (Id × X.Ty)) (F : X.Hist → ℝ) (hF : ∀ H H', RawLocal X nm D H H' → F H = F H') :
    (X.coarseLaw v).expect (fun AI => (X.hidLaw (v, AI)).expect (fun Z => F ((v, AI), Z))) =
      ∑ ξ, (X.candLaw v).w ξ * (Lane_sol_s06_g.localLaw X v nm D ξ).expect
        (fun l => F (X.withParH (Lane_sol_s06_g.assembleLocal X v nm D l) nm ξ)) := by
  subst hnm
  have huL : u ∉ X.locBins D (.candidate u) := by simp [Ctx6.locBins]
  have hS : X.binsOf (X.locKeys D) ⊆ insert u (X.locBins D (.candidate u)) := by
    intro w hw
    by_cases h : w = u
    · rw [h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw, by simpa using h⟩)
  have hFw : ∀ (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ w ∈ insert u (X.locBins D (.candidate u)), A w = A' w) → (∀ s ∈ X.locKeys D, I s = I' s) →
      (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) → F ((v, A, I), Z) = F ((v, A', I'), Z') := by
    intro A A' I I' Z Z' hA hI hZ
    exact hF _ _ ⟨⟨fun _ => rfl, fun w hw => hA w (Finset.mem_insert_of_mem hw), hI, hZ⟩,
      hA u (Finset.mem_insert_self _ _)⟩
  rw [coarse_inner_eq X v D F (fun A I I' Z Z' hI hZ => hFw A A I I' Z Z' (fun _ _ => rfl) hI hZ),
    pi_expect_window_subst (fun _ => X.candLaw v) u (X.locBins D (.candidate u)) huL (fun _ => X.y₀)
      (localInner X v D F) (localInner_dep X v D _ hS F hFw)]
  apply Finset.sum_congr rfl
  intro ξ _
  congr 1
  dsimp only [Lane_sol_s06_g.localLaw]
  simp only [bind_expect']
  rfl

/-- Initial target `V₀` (06:370–373): the target is the first raw variable, so only the window integrates. -/
theorem initial_marginal (v ξ : Fin N) (nm : ParentName6 X.Bin) (hnm : nm = .initial)
    (D : Finset (Id × X.Ty)) (F : X.Hist → ℝ) (hF : ∀ H H', RawLocal X nm D H H' → F H = F H') :
    (X.coarseLaw ξ).expect (fun AI => (X.hidLaw (ξ, AI)).expect (fun Z => F ((ξ, AI), Z))) =
      (Lane_sol_s06_g.localLaw X v nm D ξ).expect
        (fun l => F (X.withParH (Lane_sol_s06_g.assembleLocal X v nm D l) nm ξ)) := by
  subst hnm
  have hS : X.binsOf (X.locKeys D) ⊆ X.locBins D .initial := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hw, by simp⟩
  have hFw : ∀ (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ w ∈ X.locBins D .initial, A w = A' w) → (∀ s ∈ X.locKeys D, I s = I' s) →
      (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) → F ((ξ, A, I), Z) = F ((ξ, A', I'), Z') := by
    intro A A' I I' Z Z' hA hI hZ
    exact hF _ _ ⟨⟨fun h => absurd rfl h, hA, hI, hZ⟩, rfl⟩
  rw [coarse_inner_eq X ξ D F (fun A I I' Z Z' hI hZ => hFw A A I I' Z Z' (fun _ _ => rfl) hI hZ),
    Lane_sol_s06_steps1.pi_expect_fill (fun _ => X.candLaw ξ) (X.locBins D .initial) (localInner X ξ D F)
      (fun _ => X.y₀) (localInner_dep X ξ D _ hS F hFw)]
  dsimp only [Lane_sol_s06_g.localLaw]
  simp only [bind_expect']
  rfl

/-! ### The raw failure event and its local form -/

/-- The raw failure indicator at a history, integrated over the observed tuples. -/
def eventFn (b : X.State) (D : Finset (Id × X.Ty)) (Pm : (Option (Id × X.Ty) → ℝ) → Prop) (H : X.Hist) : ℝ :=
  (FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.tupleLaw H e.1.2).pr
    (fun a => X.S3TrueGate H b D ∧ Pm (fun d => X.s3Mass H b D (Lane_sol_s06_g.completeTupleData X D a) d))

theorem s3TrueGate_high (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty)) (H : X.Hist) :
    X.S3TrueGate H b D ↔ X.HighGate H b D ((X.parOf H.1).val (X.tgtName b)) := by
  simp only [Ctx6.S3TrueGate, Ctx6.trueTarget, hm]

theorem s3Mass_data_local (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty)) (H : X.Hist)
    (o o' : X.Data Id) (h : ∀ e ∈ D, o e = o' e) (d : Option (Id × X.Ty)) :
    X.s3Mass H b D o d = X.s3Mass H b D o' d := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ _
  simp only [Ctx6.s3Weight, hm, Ctx6.highWeight]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  rw [h e he]

/-- Only the tuples of `D` are read (06:141–144). -/
theorem data_marginal (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty))
    (Pm : (Option (Id × X.Ty) → ℝ) → Prop) (H : X.Hist) :
    (X.dataLaw Id H).pr (fun o => X.S3TrueGate H b D ∧ Pm (fun d => X.s3Mass H b D o d)) =
      eventFn X b D Pm H := by
  have hA : ∀ o o' : X.Data Id, (∀ e ∈ D, o e = o' e) →
      ((X.S3TrueGate H b D ∧ Pm (fun d => X.s3Mass H b D o d)) ↔
        (X.S3TrueGate H b D ∧ Pm (fun d => X.s3Mass H b D o' d))) := by
    intro o o' h
    have hfun : (fun d => X.s3Mass H b D o d) = fun d => X.s3Mass H b D o' d :=
      funext fun d => s3Mass_data_local X b hm D H o o' h d
    rw [hfun]
  rw [Lane_q_s06_steps2.dataLaw_pr_depends6 X H D _ hA (fun _ => (X.i₀, fun _ => X.y₀))]
  unfold eventFn
  apply pr_congr'
  intro a
  apply hA
  intro e he
  rw [Lane_sol_s06_g.completeTupleData_at X D a e he]
  simp [Equiv.piEquivPiSubtypeProd_symm_apply, he]

theorem eventFn_local (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty))
    (Pm : (Option (Id × X.Ty) → ℝ) → Prop) (H H' : X.Hist) (h : RawLocal X (X.tgtName b) D H H') :
    eventFn X b D Pm H = eventFn X b D Pm H' := by
  have hlaw : (FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.tupleLaw H e.1.2) =
      FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.tupleLaw H' e.1.2 := by
    congr 1
    funext e
    exact Lane_sol_s06_g.tuple_law_actual_local_eq X (X.tgtName b) D H H' h.1 h.2 e.1 e.2
  unfold eventFn
  rw [hlaw]
  apply pr_congr'
  intro a
  have hg : X.S3TrueGate H b D ↔ X.S3TrueGate H' b D := by
    rw [s3TrueGate_high X b hm D H, s3TrueGate_high X b hm D H', h.2]
    exact Lane_sol_s06_g.high_gate_local_iff X b D H H' h.1 _
  exact and_congr hg (iff_of_eq (congrArg Pm
    (funext fun d => Lane_sol_s06_g.high_mass_local_eq X b D H H' h.1 _ d hm)))

theorem localAgree_withParH (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H : X.Hist) (ξ : Fin N) :
    Lane_sol_s06_g.LocalAgree X nm D (X.withParH H nm ξ) H := by
  refine ⟨?_, ?_, fun s _ => rfl, fun ℓ _ => rfl⟩
  · intro hnm
    cases nm with
    | initial => exact absurd rfl hnm
    | candidate u => rfl
  · intro w hw
    cases nm with
    | initial => rfl
    | candidate u =>
      have hwu : w ≠ u := by
        intro hwu
        subst hwu
        simp [Ctx6.locBins] at hw
      simp [Ctx6.withParH, Ctx6.withPar, Ctx6.parOf, Par6.set, hwu]

theorem withParH_val (H : X.Hist) (nm : ParentName6 X.Bin) (ξ : Fin N) :
    (X.parOf (X.withParH H nm ξ).1).val nm = ξ := by
  cases nm <;> simp [Ctx6.withParH, Ctx6.withPar, Ctx6.parOf, Par6.set, Par6.val]

/-- At the substituted local history the raw event is the joint-model event (06:391–417). -/
theorem joint_identify (v ξ : Fin N) (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty))
    (Pm : (Option (Id × X.Ty) → ℝ) → Prop) :
    (Lane_sol_s06_g.localLaw X v (X.tgtName b) D ξ).expect (fun l =>
      eventFn X b D Pm (X.withParH (Lane_sol_s06_g.assembleLocal X v (X.tgtName b) D l) (X.tgtName b) ξ)) =
    (Lane_sol_s06_g.jointActual X v b D ξ).pr (fun ω =>
      Lane_sol_s06_g.jointGate X v b D ξ ω ∧ Pm (fun d => Lane_sol_s06_g.jointMass X v b D d ω)) := by
  refine Eq.trans ?_ (Lane_q_s06_steps2.bind_pr6 _ _ (fun l a =>
    Lane_sol_s06_g.jointGate X v b D ξ (l, a) ∧ Pm (fun d => Lane_sol_s06_g.jointMass X v b D d (l, a)))).symm
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  beta_reduce
  unfold eventFn
  apply pr_congr'
  intro a
  have hLA := localAgree_withParH X (X.tgtName b) D (Lane_sol_s06_g.assembleLocal X v (X.tgtName b) D l) ξ
  have hg : X.S3TrueGate (X.withParH (Lane_sol_s06_g.assembleLocal X v (X.tgtName b) D l) (X.tgtName b) ξ) b D ↔
      Lane_sol_s06_g.jointGate X v b D ξ (l, a) := by
    rw [s3TrueGate_high X b hm D, withParH_val]
    exact Lane_sol_s06_g.high_gate_local_iff X b D _ _ hLA ξ
  exact and_congr hg (iff_of_eq (congrArg Pm
    (funext fun d => Lane_sol_s06_g.high_mass_local_eq X b D _ _ hLA _ d hm)))

/-- The raw base law splits as the initial law followed by the coarse law. -/
theorem baseLaw_sum (G : X.Base → ℝ) :
    ∑ base : X.Base, X.baseLaw.w base * G base =
      ∑ v, X.initLaw.w v * (X.coarseLaw v).expect (fun AI => G (v, AI)) :=
  FinProb.bind_expect X.initLaw X.coarseLaw (fun v AI => G (v, AI))

/-- L6.1g (tests, 06:418–426), raw form: conditional local bounds for every admissible `V₀` give the raw
true-gated bound.  At an initial target `V₀` is itself the target, so one fixed fallback `v = y₀` is used. -/
theorem raw_high_bound (b : X.State) (hm : X.stMode b = .high) (D : Finset (Id × X.Ty))
    (Pm : (Option (Id × X.Ty) → ℝ) → Prop)
    (hJ : ∀ v, (X.tgtName b ≠ .initial → 0 < X.initLaw.w v) →
      ∑ ξ, (Lane_sol_s06_g.localPrior X v b).w ξ * (Lane_sol_s06_g.jointActual X v b D ξ).pr
        (fun ω => Lane_sol_s06_g.jointGate X v b D ξ ω ∧
          Pm (fun d => Lane_sol_s06_g.jointMass X v b D d ω)) ≤ X.s3Thr) :
    (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧ Pm (fun d => X.s3Mass ω.1 b D ω.2 d)) ≤
      X.s3Thr := by
  have hloc : ∀ H H', RawLocal X (X.tgtName b) D H H' → eventFn X b D Pm H = eventFn X b D Pm H' :=
    fun H H' h => eventFn_local X b hm D Pm H H' h
  have hraw : (X.rawHistData Id).pr
      (fun ω => X.S3TrueGate ω.1 b D ∧ Pm (fun d => X.s3Mass ω.1 b D ω.2 d)) =
      ∑ v, X.initLaw.w v * (X.coarseLaw v).expect
        (fun AI => (X.hidLaw (v, AI)).expect (fun Z => eventFn X b D Pm ((v, AI), Z))) := by
    rw [Lane_q_s06_steps2.rawHistData_pr_expand6 X
      (fun H o => X.S3TrueGate H b D ∧ Pm (fun d => X.s3Mass H b D o d))]
    simp only [data_marginal X b hm D Pm]
    exact baseLaw_sum X (fun base => (X.hidLaw base).expect (fun Z => eventFn X b D Pm (base, Z)))
  rw [hraw]
  obtain hT | ⟨u, hT⟩ : X.tgtName b = .initial ∨ ∃ u, X.tgtName b = .candidate u := by
    cases X.tgtName b with
    | initial => exact Or.inl rfl
    | candidate u => exact Or.inr ⟨u, rfl⟩
  · have hprior : Lane_sol_s06_g.localPrior X X.y₀ b = X.initLaw := by
      simp only [Lane_sol_s06_g.localPrior, hT]
    calc ∑ v, X.initLaw.w v * (X.coarseLaw v).expect
          (fun AI => (X.hidLaw (v, AI)).expect (fun Z => eventFn X b D Pm ((v, AI), Z)))
        = ∑ ξ, (Lane_sol_s06_g.localPrior X X.y₀ b).w ξ * (Lane_sol_s06_g.jointActual X X.y₀ b D ξ).pr
            (fun ω => Lane_sol_s06_g.jointGate X X.y₀ b D ξ ω ∧
              Pm (fun d => Lane_sol_s06_g.jointMass X X.y₀ b D d ω)) := by
          rw [hprior]
          apply Finset.sum_congr rfl
          intro ξ _
          rw [initial_marginal X X.y₀ ξ (X.tgtName b) hT D _ hloc, joint_identify X X.y₀ ξ b hm D Pm]
      _ ≤ X.s3Thr := hJ X.y₀ (fun h => absurd hT h)
  · calc ∑ v, X.initLaw.w v * (X.coarseLaw v).expect
          (fun AI => (X.hidLaw (v, AI)).expect (fun Z => eventFn X b D Pm ((v, AI), Z)))
        ≤ ∑ v, X.initLaw.w v * X.s3Thr := by
          apply Finset.sum_le_sum
          intro v _
          by_cases hv : X.initLaw.w v = 0
          · simp [hv]
          have hvpos : 0 < X.initLaw.w v := lt_of_le_of_ne (X.initLaw.nonneg v) (Ne.symm hv)
          refine mul_le_mul_of_nonneg_left ?_ (X.initLaw.nonneg v)
          have hprior : Lane_sol_s06_g.localPrior X v b = X.candLaw v := by
            simp only [Lane_sol_s06_g.localPrior, hT]
          rw [candidate_marginal X v (X.tgtName b) u hT D _ hloc]
          calc _ = ∑ ξ, (Lane_sol_s06_g.localPrior X v b).w ξ * (Lane_sol_s06_g.jointActual X v b D ξ).pr
                (fun ω => Lane_sol_s06_g.jointGate X v b D ξ ω ∧
                  Pm (fun d => Lane_sol_s06_g.jointMass X v b D d ω)) := by
                rw [hprior]
                apply Finset.sum_congr rfl
                intro ξ _
                rw [joint_identify X v ξ b hm D Pm]
            _ ≤ X.s3Thr := hJ v (fun _ => hvpos)
      _ = X.s3Thr := by rw [← Finset.sum_mul, X.initLaw.sum_eq_one, one_mul]

end
end HypercubeRamsey.S06.Lane_opus_g
