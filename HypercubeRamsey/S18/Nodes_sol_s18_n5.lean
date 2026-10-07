import HypercubeRamsey.S18.Defs
import HypercubeRamsey.S17.Nodes

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem rowDeg_nonneg (D : LateData hPT) (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) :
    0 ≤ rowDeg (T.S.E k) PT.tiling.c x (PT.π i) := by
  apply Finset.sum_nonneg
  intro y _
  by_cases h : Hits (T.S.E k) PT.tiling.c x y <;> simp [h, (PT.π i).nonneg y]

theorem initialWeight_nonneg (D : LateData hPT) (v : Pos T k) (s : Config D.fresh)
    (x : Fin (T.S.N k)) : 0 ≤ D.initialWeight v s x := by
  obtain ⟨valid, permitted, hF⟩ := D.l16_valid.fresh_spec
  apply mul_nonneg (hF.prior_nonneg _ _ _ _)
  apply Finset.prod_nonneg
  intro a _
  apply div_nonneg
  · split_ifs <;> norm_num
  · exact rowDeg_nonneg D _ _

theorem phi_nonneg (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (s : Config D.fresh) : 0 ≤ A.phi assignment s := by
  unfold InitialPairData.phi
  split_ifs
  · apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro v _
    split_ifs
    · exact mul_nonneg (initialWeight_nonneg D _ _ _) (initialWeight_nonneg D _ _ _)
    · exact le_rfl
  · exact le_rfl

private theorem internal_cell (D : LateData hPT) (v : Pos T k)
    (a : Fin (T.S.n k)) (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf v)) :
    D.geom.cellOf (flipPos v a) = D.geom.cellOf v := by
  have hlen : (PT.tiling.P (D.geom.patchOf v)).ℓ +
      (PT.tiling.P (D.geom.patchOf v)).h ≤ T.S.n k :=
    le_trans (Nat.add_le_add
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ) (Finset.mem_univ _))
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h) (Finset.mem_univ _)))
      hPT.tiling_valid.prefix_internal_length
  have ha' : T.S.n k - (PT.tiling.P (D.geom.patchOf v)).h ≤ a.val := by
    simpa [Tiling.Icoord, topCoordinates] using ha
  have hp := HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix
    D.geom hPT v a (by omega)
  apply D.l16_valid.whole_slices (flipPos v a) v hp
  intro b hb
  rw [hp] at hb
  have hba : b ≠ a := by intro heq; subst b; exact hb ha
  simp [flipPos, hba]

theorem initialValid_local (D : LateData hPT) (hD : D.Spec) (v : Pos T k)
    (s s' : Config D.fresh) (hs : ∀ C ∈ D.directCells v, s C = s' C) :
    D.initialValid v s ↔ D.initialValid v s' := by
  have hown : s (D.geom.cellOf v) = s' (D.geom.cellOf v) := hs _ (by simp [LateData.directCells])
  have hσ : D.sigma v s = D.sigma v s' := by funext x; simp [LateData.sigma, hown]
  have hU := hD.prior_local v s s' hs
  have hEarly : ∀ a ∈ D.externalEarly v,
      D.earlyLabel s (flipPos v a) = D.earlyLabel s' (flipPos v a) := by
    intro a ha
    unfold LateData.earlyLabel
    rw [hs _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))]
  have hInternal : ∀ a ∈ PT.tiling.Icoord (D.geom.patchOf v),
      D.earlyLabel s (flipPos v a) = D.earlyLabel s' (flipPos v a) := by
    intro a ha
    have heq : s (D.geom.cellOf (flipPos v a)) = s' (D.geom.cellOf (flipPos v a)) := by
      have hrestrict : ∀ C, C = D.geom.cellOf v → s C = s' C := by
        intro C hC
        subst C
        exact hown
      exact hrestrict _ (internal_cell D v a ha)
    exact congrArg (fun t => D.fresh.label (D.geom.cellOf (flipPos v a)) t (flipPos v a)) heq
  have hIV : D.internalValid v s ↔ D.internalValid v s' := by
    unfold LateData.internalValid
    rw [hσ]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
    apply forall_congr'
    intro a
    apply imp_congr_right
    intro ha
    rw [hInternal a ha]
  have hL : D.listFailure v s ↔ D.listFailure v s' := by
    have hW : ∀ J, D.withheldList v s J = D.withheldList v s' J := by
      intro J
      ext x
      simp only [LateData.withheldList, Finset.mem_filter]
      apply and_congr_right
      intro _
      apply forall_congr'
      intro a
      apply imp_congr_right
      intro ha
      rw [hEarly a (Finset.mem_sdiff.mp ha).1]
    simp only [LateData.listFailure, hU, hW]
  simp only [LateData.initialValid, hIV, hL, hU]

theorem phi_local (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (assignment : PairAssignment T k) (s s' : Config D.fresh)
    (hs : ∀ C ∈ A.scope, s C = s' C) : A.phi assignment s = A.phi assignment s' := by
  have hscope (v : Pos T k) (hv : v ∈ A.rows) :
      ∀ C ∈ D.directCells v, s C = s' C :=
    fun C hC => hs C (Finset.mem_biUnion.mpr ⟨v, hv, hC⟩)
  have hV : (∀ v ∈ A.rows, D.initialValid v s) ↔
      (∀ v ∈ A.rows, D.initialValid v s') := by
    apply forall_congr'
    intro v
    apply imp_congr_right
    intro hv
    exact initialValid_local D hD v s s' (hscope v hv)
  unfold InitialPairData.phi
  simp only [hV]
  split_ifs with hgood
  · congr 1
    apply Finset.prod_congr rfl
    intro v hv
    have hU := hD.prior_local v s s' (hscope v hv)
    have hPrior : D.initialPrior v s = D.initialPrior v s' := by
      simp only [LateData.initialPrior, initialValid_local D hD v s s' (hscope v hv), hU]
    rw [hPrior, hU]
  · rfl

theorem scope_card (D : LateData hPT) (A : InitialPairData D) :
    A.scope.card ≤ T.S.n k * (T.S.n k + 1) := by
  calc
    A.scope.card ≤ ∑ v ∈ A.rows, (D.directCells v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A.rows, (T.S.n k + 1) := by
      apply Finset.sum_le_sum
      intro v _
      calc
        (D.directCells v).card ≤ ({D.geom.cellOf v} : Finset D.geom.Cell).card +
            ((D.externalEarly v).image fun a => D.geom.cellOf (flipPos v a)).card :=
          Finset.card_union_le _ _
        _ ≤ 1 + (D.externalEarly v).card := by
          simp only [Finset.card_singleton]
          exact Nat.add_le_add_left (Finset.card_image_le) 1
        _ ≤ T.S.n k + 1 := by
          have h : (D.externalEarly v).card ≤ T.S.n k :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
          omega
    _ = A.rows.card * (T.S.n k + 1) := by simp
    _ ≤ T.S.n k * (T.S.n k + 1) := Nat.mul_le_mul_right _ A.small

set_option maxHeartbeats 400000 in
theorem pi_E_project {I : Type*} {Ω : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) (S : Finset I)
    (f : (∀ i, Ω i) → ℝ) (d : ∀ i, Ω i)
    (hf : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) :
    (FinLaw.pi P).E f =
      (FinLaw.pi fun i : {i : I // i ∈ S} => P i.1).E
        (fun x => f (fun i => if hi : i ∈ S then x ⟨i, hi⟩ else d i)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω
  let z : ∀ i : {i : I // i ∉ S}, Ω i.1 := fun i => d i.1
  change (FinLaw.pi P).E f =
    ∑ x : ∀ i : {i : I // i ∈ S}, Ω i.1,
      (∏ i : {i : I // i ∈ S}, (P i.1).w (x i)) * f (e.symm (x, z))
  have hfactor (xy : (∀ i : {i : I // i ∈ S}, Ω i.1) × (∀ i : {i : I // i ∉ S}, Ω i.1)) :
      (FinLaw.pi P).w (e.symm xy) =
        (∏ i : {i : I // i ∈ S}, (P i.1).w (xy.1 i)) *
        (∏ i : {i : I // i ∉ S}, (P i.1).w (xy.2 i)) := by
    change (∏ i, (P i).w ((e.symm xy) i)) = _
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
    congr 1
    · apply Finset.prod_congr (by ext i; simp)
      intro i _
      change (P i.1).w (if h : i.1 ∈ S then xy.1 ⟨i.1, h⟩ else xy.2 ⟨i.1, h⟩) = _
      rw [dif_pos i.2]
    · apply Finset.prod_congr rfl
      intro i _
      change (P i.1).w (if h : i.1 ∈ S then xy.1 ⟨i.1, h⟩ else xy.2 ⟨i.1, h⟩) = _
      rw [dif_neg i.2]
  calc
    (FinLaw.pi P).E f = ∑ xy, (FinLaw.pi P).w (e.symm xy) * f (e.symm xy) := by
      exact (e.symm.sum_comp (fun x => (FinLaw.pi P).w x * f x)).symm
    _ = ∑ x : ∀ i : {i : I // i ∈ S}, Ω i.1, ∑ y : ∀ i : {i : I // i ∉ S}, Ω i.1,
        ((∏ i : {i : I // i ∈ S}, (P i.1).w (x i)) *
        (∏ i : {i : I // i ∉ S}, (P i.1).w (y i))) * f (e.symm (x, z)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [hfactor]
      have heq : f (e.symm (x, y)) = f (e.symm (x, z)) := by
        apply hf
        intro i hi
        change (show Ω i from if h : i ∈ S then x ⟨i, h⟩ else y ⟨i, h⟩) =
          (show Ω i from if h : i ∈ S then x ⟨i, h⟩ else z ⟨i, h⟩)
        rw [dif_pos hi, dif_pos hi]
      rw [heq]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        (∑ y : ∀ i : {i : I // i ∉ S}, Ω i.1, ((∏ i : {i : I // i ∈ S}, (P i.1).w (x i)) *
            (∏ i : {i : I // i ∉ S}, (P i.1).w (y i))) * f (e.symm (x, z))) =
            ((∏ i : {i : I // i ∈ S}, (P i.1).w (x i)) * f (e.symm (x, z))) *
              (∑ y : ∀ i : {i : I // i ∉ S}, Ω i.1, ∏ i : {i : I // i ∉ S}, (P i.1).w (y i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = _ := by
          have hnorm := (FinLaw.pi (fun i : {i : I // i ∉ S} => P i.1)).sum_one
          change (∑ y : ∀ i : {i : I // i ∉ S}, Ω i.1, ∏ i : {i : I // i ∉ S}, (P i.1).w (y i)) = 1 at hnorm
          rw [hnorm, mul_one]

theorem pi_E_local {I : Type*} {Ω : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (P Q : ∀ i, FinLaw (Ω i)) (S : Finset I) (f : (∀ i, Ω i) → ℝ)
    (hf : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hPQ : ∀ i ∈ S, P i = Q i) : (FinLaw.pi P).E f = (FinLaw.pi Q).E f := by
  let d : ∀ i, Ω i := fun _ => Classical.choice inferInstance
  rw [pi_E_project P S f d hf, pi_E_project Q S f d hf]
  have hL : (fun i : {i : I // i ∈ S} => P i.1) = (fun i : {i : I // i ∈ S} => Q i.1) := by
    funext i
    exact hPQ i.1 i.2
  rw [hL]


theorem poolListOK_local (D : LateData hPT) (v : Pos T k)
    (P Q : ∀ C, D.fresh.Pool C)
    (hPQ : ∀ C ∈ D.encoding.events.scope v, P C = Q C) :
    D.poolListOK P v ↔ D.poolListOK Q v := by
  letI : ∀ C, Nonempty (D.fresh.State C) := fun C => ⟨D.fresh.fallback C⟩
  have h := pi_E_local (fun C => D.fresh.fresh C (P C))
    (fun C => D.fresh.fresh C (Q C)) (D.encoding.events.scope v)
    (fun s => if D.encoding.events.S v s then (1 : ℝ) else 0)
    (fun s s' hs => if_congr (D.encoding.events.scope_ok v s s' hs) rfl rfl)
    (fun C hC => congrArg (D.fresh.fresh C) (hPQ C hC))
  have hpr : (D.freshConfigLaw P).pr (D.encoding.events.S v) =
      (D.freshConfigLaw Q).pr (D.encoding.events.S v) := by
    simpa only [FinLaw.E, LateData.freshConfigLaw, FinLaw.pr, mul_ite,
      mul_one, mul_zero] using h
  simp only [LateData.poolListOK, hpr]

theorem poolGate_local (D : LateData hPT) (region : Finset D.geom.Cell)
    (x x' : D.encoding.InitInput) (hpool : ∀ C ∈ region, x.1 C = x'.1 C) :
    D.poolGate region x ↔ D.poolGate region x' := by
  have ht : (∀ C ∈ region, D.fresh.typical C (x.1 C)) ↔
      (∀ C ∈ region, D.fresh.typical C (x'.1 C)) := by
    apply forall_congr'
    intro C
    apply imp_congr_right
    intro hC
    rw [hpool C hC]
  have hl : (∀ v, D.encoding.events.scope v ⊆ region → D.poolListOK x.1 v) ↔
      (∀ v, D.encoding.events.scope v ⊆ region → D.poolListOK x'.1 v) := by
    apply forall_congr'
    intro v
    apply imp_congr_right
    intro hv
    exact poolListOK_local D v x.1 x'.1 (fun C hC => hpool C (hv hC))
  exact and_congr ht hl

private noncomputable def listContext (D : LateData hPT) : ListGateContext κ T k PT :=
  { tiling_valid := hPT
    mode_low := D.low_mode
    G := D.geom
    F := D.fresh
    stateValid := D.l16_valid.fresh_spec.choose
    permittedLabels := D.l16_valid.fresh_spec.choose_spec.choose
    slotFactor := fun _ => 1
    fresh_spec := D.l16_valid.fresh_spec.choose_spec.choose_spec }

private theorem graphBall_mono (D : LateData hPT) (U V : Finset (Pos T k))
    (hUV : U ⊆ V) (r : ℕ) :
    D.encoding.events.graphBall U r ⊆ D.encoding.events.graphBall V r := by
  induction r with
  | zero => exact hUV
  | succ r ih =>
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union.mpr (Or.inl (ih hw))
    · obtain ⟨_, v, hv, hadj⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, ih hv, hadj⟩))

private theorem restrictedRun_local (D : LateData hPT) (region : Finset D.geom.Cell)
    (events : Finset (Pos T k))
    (hevents : ∀ v ∈ events, D.encoding.events.scope v ⊆ region)
    (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ region, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) (m : ℕ) :
    (∀ C ∈ region,
      (D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).1 C =
      (D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).1 C) ∧
    (∀ C ∈ region,
      (D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).2 C =
      (D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).2 C) := by
  induction m with
  | zero =>
    constructor
    · intro C hC
      change x.2.extend C 0 (x.1 C) = x'.2.extend C 0 (x'.1 C)
      simp only [Tapes.extend]
      rw [(hx C hC).1, (hx C hC).2]
    · intro C _; rfl
  | succ m ih =>
    let s := (D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).1
    let s' := (D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).1
    have htruth : ∀ v ∈ events, D.encoding.events.S v s ↔ D.encoding.events.S v s' := by
      intro v hv
      exact D.encoding.events.scope_ok v s s' (fun C hC => ih.1 C (hevents v hv hC))
    have hactive : D.encoding.events.active D.encoding.order events s =
        D.encoding.events.active D.encoding.order events s' := by
      ext v
      simp only [ListEvent.active, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hv, hS, havoid⟩
        refine ⟨hv, (htruth v hv).mp hS, ?_⟩
        intro u hu hbefore hadj hSu
        exact havoid u hu hbefore hadj ((htruth u hu).mpr hSu)
      · rintro ⟨hv, hS, havoid⟩
        refine ⟨hv, (htruth v hv).mpr hS, ?_⟩
        intro u hu hbefore hadj hSu
        exact havoid u hu hbefore hadj ((htruth u hu).mp hSu)
    constructor
    · intro C hC
      change (if ∃ v ∈ D.encoding.events.active D.encoding.order events s,
          C ∈ D.encoding.events.scope v then
        x.2.extend C ((D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).2 C + 1)
          (x.1 C) else s C) =
        (if ∃ v ∈ D.encoding.events.active D.encoding.order events s',
          C ∈ D.encoding.events.scope v then
        x'.2.extend C ((D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).2 C + 1)
          (x'.1 C) else s' C)
      rw [hactive]
      split_ifs
      · simp only [Tapes.extend]
        rw [(hx C hC).1, (hx C hC).2, ih.2 C hC]
      · exact ih.1 C hC
    · intro C hC
      change (if ∃ v ∈ D.encoding.events.active D.encoding.order events s,
          C ∈ D.encoding.events.scope v then
        (D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).2 C + 1
          else (D.encoding.events.runRounds m D.encoding.order events x.1 x.2.extend).2 C) =
        (if ∃ v ∈ D.encoding.events.active D.encoding.order events s',
          C ∈ D.encoding.events.scope v then
        (D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).2 C + 1
          else (D.encoding.events.runRounds m D.encoding.order events x'.1 x'.2.extend).2 C)
      rw [hactive]
      split_ifs <;> rw [ih.2 C hC]

theorem initialState_local (D : LateData hPT) (seed : Finset D.geom.Cell)
    (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ D.expandCells seed, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    ∀ C ∈ seed, D.encoding.initialState x C = D.encoding.initialState x' C := by
  let events := D.encoding.events.graphBall
    (seed.biUnion D.encoding.events.incidentEvents) (2 * D.encoding.Ts + 3)
  have hlocal (y : D.encoding.InitInput) :=
    (resampleLocality (D := listContext D) D.encoding.events D.encoding.Ts
      D.encoding.order y.1 y.2.extend).1
  have hrun := restrictedRun_local D (D.expandCells seed) events
    (fun v hv C hC => Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨v, hv, hC⟩)))
    x x' hx D.encoding.Ts
  intro C hC
  have hball : D.encoding.events.graphBall (D.encoding.events.incidentEvents C)
      (2 * D.encoding.Ts + 3) ⊆ events :=
    graphBall_mono D _ _ (fun v hv => Finset.mem_biUnion.mpr ⟨C, hC, hv⟩) _
  change (D.encoding.events.resample D.encoding.Ts D.encoding.order Finset.univ x.1 x.2.extend) C =
    (D.encoding.events.resample D.encoding.Ts D.encoding.order Finset.univ x'.1 x'.2.extend) C
  exact (hlocal x C events hball).trans
    ((hrun.1 C (Finset.mem_union.mpr (Or.inl hC))).trans (hlocal x' C events hball).symm)

theorem terminal_comparison (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    {δ ε : ℝ} (C : TerminalCertificate D δ ε) (assignment : PairAssignment T k)
    (hsize : (A.scope.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    A.termTest C assignment ≤ (1 + ε) * A.permTest assignment := by
  apply C.comparison A.scope hsize
  · intro x
    split_ifs
    · exact phi_nonneg D A assignment _
    · exact le_rfl
  · intro x x' hx
    simp only [poolGate_local D (D.expandCells A.scope) x x' (fun C hC => (hx C hC).1)]
    split_ifs
    · exact phi_local D hD A assignment _ _ (initialState_local D A.scope x x' hx)
    · rfl

theorem eventually_scope_size (T : Stage) :
    ∀ᶠ k in atTop, ∀ {κ : CConsts} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT) (A : InitialPairData D),
      (A.scope.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 2
  filter_upwards [hlog, T.S.n_tendsto.eventually_ge_atTop 1] with k hk hn
  change 2 ≤ Real.log (T.S.n k) at hk
  intro κ PT hPT D A
  have hpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have ht : Real.log 2 + 2 * Real.log (T.S.n k) ≤ Real.log (T.S.n k) ^ 3 := by
    have hsq : 4 ≤ Real.log (T.S.n k) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ Real.log (T.S.n k) by linarith)
    nlinarith
  calc
    (A.scope.card : ℝ) ≤ (T.S.n k : ℝ) * ((T.S.n k : ℝ) + 1) := by
      exact_mod_cast scope_card D A
    _ ≤ 2 * (T.S.n k : ℝ) ^ 2 := by
      have hcast : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
      nlinarith
    _ = Real.exp (Real.log 2 + 2 * Real.log (T.S.n k)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hpos]
    _ ≤ Real.exp (Real.log (T.S.n k) ^ 3) := Real.exp_le_exp.mpr ht

noncomputable def finalWeight (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (x : Fin (T.S.N k)) : ℝ :=
  (D.initialPrior v h.1).w x * ∏ b : D.encoding.base.ProcessedRole (Fin.last D.geom.r),
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
    else 1

theorem finalWeight_nonneg (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k) (x : Fin (T.S.N k)) :
    0 ≤ finalWeight D h v x := by
  apply mul_nonneg ((D.initialPrior v h.1).nonneg x)
  apply Finset.prod_nonneg
  intro b _
  split_ifs <;> norm_num

theorem initialPrior_support (D : LateData hPT) (v : Pos T k) (s : Config D.fresh)
    (hv : D.initialValid v s) (x : Fin (T.S.N k)) (hx : (D.initialPrior v s).w x ≠ 0) :
    x ∈ D.palette v ∧ D.initialWeight v s x ≠ 0 := by
  have hnonneg : ∀ y, 0 ≤ (if y ∈ D.palette v then D.initialWeight v s y else 0) := by
    intro y
    split_ifs
    · exact initialWeight_nonneg D v s y
    · exact le_rfl
  have hχ : (0 : ℝ) < D.chi (D.geom.patchOf v) := by exact_mod_cast D.chi_pos _
  have hsum : 0 < ∑ y, if y ∈ D.palette v then D.initialWeight v s y else 0 := by
    have hmass := hv.2.2
    rw [← Finset.sum_filter] at ⊢
    simpa using lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * (D.chi (D.geom.patchOf v) : ℝ))) hmass
  simp only [LateData.initialPrior, if_pos hv, LateData.normalize,
    dif_pos (show (∀ y, 0 ≤ (if y ∈ D.palette v then D.initialWeight v s y else 0)) ∧
      0 < ∑ y, if y ∈ D.palette v then D.initialWeight v s y else 0 from ⟨hnonneg, hsum⟩)] at hx
  by_cases hp : x ∈ D.palette v
  · refine ⟨hp, ?_⟩
    intro hz
    exact hx (by simp [hp, hz])
  · exact False.elim (hx (by simp [hp]))

private theorem adjacent_flip {n : ℕ} (v w : CubePos n)
    (h : (OAI.HypercubeRamsey.cube n).Adj v w) : ∃ a, w = flipPos v a := by
  let S := Finset.univ.filter fun a : Fin n => v a ≠ w a
  have hcard : S.card = 1 := h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b
    have hne : v a ≠ w a := by
      have hm : a ∈ S := by rw [ha]; simp
      exact (Finset.mem_filter.mp hm).2
    cases hv : v a <;> cases hw : w a <;> simp_all [flipPos]
  · have heq : v b = w b := by
      by_contra hne
      have hm : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [ha] at hm
      exact hb (Finset.mem_singleton.mp hm)
    simp [flipPos, hb, heq]

theorem nonconflict_distinct (hκ : κ.Admissible) (D : LateData hPT)
    (v : Pos T k) (x z : Fin (T.S.N k)) (h : D.nonconflict v x z) : x ≠ z := by
  have hξ : κ.ξ < 1 := by
    have hpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have hu : (0 : ℝ) ≤ κ.u := Nat.cast_nonneg _
        linarith)
    have hbound := mul_le_mul_of_nonneg_left hpow hκ.α_rng.1.le
    linarith [hκ.ξ_rng.2, hκ.α_rng.2]
  intro heq
  subst z
  have hc : pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) x x = 1 := by
    unfold pairCorr corr
    simp only [ite_true]
    calc
      (∑ y, (PT.π (D.geom.patchOf v)).w y * fv (T.S.E k) true x y * fv (T.S.E k) true x y) =
          ∑ y, (PT.π (D.geom.patchOf v)).w y := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hh : Hits (T.S.E k) true x y <;> simp [fv, hit, hh] <;> ring
      _ = 1 := (PT.π (D.geom.patchOf v)).sum_eq_one
  have h1 : (1 : ℝ) ≤ κ.ξ := by simpa only [LateData.nonconflict, hc, abs_one] using h
  linarith

theorem finalPrior_support (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (hv : D.initialValid v h.1) (hmass : 0 < ∑ y, finalWeight D h v y)
    (x : Fin (T.S.N k)) (hx : (D.finalPrior h v).w x ≠ 0) :
    x ∈ D.palette v ∧
      ∀ b : {b : Pos T k // ¬ IsEvenRole b}, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
        Hits (T.S.E k) PT.tiling.c x (D.oddAt h b) := by
  have hnonneg := finalWeight_nonneg D h v
  have hraw : finalWeight D h v x ≠ 0 := by
    intro hzero
    apply hx
    simp only [LateData.finalPrior, LateData.priorAt, if_pos hv]
    change (D.normalize (finalWeight D h v)).w x = 0
    simp only [LateData.normalize,
      dif_pos (show (∀ y, 0 ≤ finalWeight D h v y) ∧ 0 < ∑ y, finalWeight D h v y from ⟨hnonneg, hmass⟩),
      hzero, zero_div]
  have hinit : (D.initialPrior v h.1).w x ≠ 0 := (mul_ne_zero_iff.mp hraw).1
  obtain ⟨hp, hU⟩ := initialPrior_support D v h.1 hv x hinit
  refine ⟨hp, ?_⟩
  intro b hadj
  by_cases hb : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r)
  · have hprod := (mul_ne_zero_iff.mp hraw).2
    have hfactor := (Finset.prod_ne_zero_iff.mp hprod) ⟨b.1, hb⟩ (Finset.mem_univ _)
    have hhit : Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 ⟨b.1, hb⟩)) := by
      by_contra hbad
      exact hfactor (by simp [hadj, hbad])
    simpa only [LateData.oddAt, dif_pos hb] using hhit
  · have hnclass : D.geom.classOf b.1 = none := by
      cases hclass : D.geom.classOf b.1 with
      | none => rfl
      | some j =>
        exact False.elim (hb (by rw [D.encoding.base.processed_last]; simp [hclass]))
    obtain ⟨a, ha⟩ := adjacent_flip v b.1 hadj
    have hhit : Hits (T.S.E k) PT.tiling.c x (D.earlyLabel h.1 b.1) := by
      by_cases hi : a ∈ PT.tiling.Icoord (D.geom.patchOf v)
      · have hσ : D.sigma v h.1 x ≠ 0 := (mul_ne_zero_iff.mp hU).1
        rw [ha]
        exact hv.1.2.2.2.2 a hi x hσ
      · have he : a ∈ D.externalEarly v := by
          simp only [LateData.externalEarly, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hi, by rw [← ha]; exact hnclass⟩
        have hprod := (mul_ne_zero_iff.mp hU).2
        have hfactor := Finset.prod_ne_zero_iff.mp hprod a he
        rw [ha]
        by_contra hbad
        exact hfactor (by simp [hbad])
    simpa only [LateData.oddAt, dif_neg hb] using hhit

theorem pairLaw_support (hκ : κ.Admissible) (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (hv : D.initialValid v h.1) (hmass : 0 < ∑ y, finalWeight D h v y)
    (hZ : (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0)
    (p : Fin (T.S.N k) × Fin (T.S.N k)) (hp : 0 < (D.pairLaw h v).w p) :
    p.1 ≠ p.2 ∧ p.1 ∈ D.palette v ∧ p.2 ∈ D.palette v ∧
      ∀ b : {b : Pos T k // ¬ IsEvenRole b}, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
        Hits (T.S.E k) PT.tiling.c p.1 (D.oddAt h b) ∧
        Hits (T.S.E k) PT.tiling.c p.2 (D.oddAt h b) := by
  have hgood : 0 < ∑ p ∈ Finset.univ.filter (fun p : Fin (T.S.N k) × Fin (T.S.N k) =>
      D.nonconflict v p.1 p.2), (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 := by
    rw [Finset.sum_filter]
    linarith
  have hp' : 0 <
      (if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) /
        (∑ q ∈ Finset.univ.filter (fun q : Fin (T.S.N k) × Fin (T.S.N k) => D.nonconflict v q.1 q.2),
          (D.finalPrior h v).w q.1 * (D.finalPrior h v).w q.2) := by
    simpa [LateData.pairLaw, FinLaw.bind, FinLaw.cond, hgood] using hp
  clear hp
  have hnc : D.nonconflict v p.1 p.2 := by
    by_contra hbad
    simpa [hbad] using hp'
  have hprod : (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 ≠ 0 := by
    intro hzero
    simp [hnc, hzero] at hp'
  obtain ⟨hx, hz⟩ := mul_ne_zero_iff.mp hprod
  obtain ⟨hxpal, hxhit⟩ := finalPrior_support D h v hv hmass p.1 hx
  obtain ⟨hzpal, hzhit⟩ := finalPrior_support D h v hv hmass p.2 hz
  exact ⟨nonconflict_distinct hκ D v p.1 p.2 hnc, hxpal, hzpal,
    fun b hb => ⟨hxhit b hb, hzhit b hb⟩⟩

private theorem flipPos_involutive (v : Pos T k) (a : Fin (T.S.n k)) :
    flipPos (flipPos v a) a = v := by
  funext j
  by_cases hj : j = a
  · subst j
    simp [flipPos]
  · simp [flipPos, hj]

private def oneNeighborhood (b : Pos T k) : Finset (Pos T k) :=
  insert b ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a))

private theorem oneNeighborhood_card (b : Pos T k) :
    (oneNeighborhood b).card ≤ T.S.n k + 1 := by
  classical
  unfold oneNeighborhood
  calc
    _ ≤ ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a)).card + 1 :=
      Finset.card_insert_le b _
    _ ≤ (Finset.univ : Finset (Fin (T.S.n k))).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = T.S.n k + 1 := by simp

private def cellSources (D : LateData hPT) (C : D.geom.Cell) : Finset (Pos T k) :=
  Finset.univ.filter fun b => D.geom.cellOf b = C

private def cellReach (D : LateData hPT) (C : D.geom.Cell) : Finset (Pos T k) :=
  (cellSources D C).biUnion oneNeighborhood

private theorem mem_cellReach_of_mem_directCells (D : LateData hPT) {C : D.geom.Cell}
    {w : Pos T k} (hC : C ∈ D.directCells w) : w ∈ cellReach D C := by
  classical
  simp only [LateData.directCells, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hC
  rcases hC with hC | ⟨a, ha, hcell⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, ?_⟩
    · simp [cellSources, hC]
    · simp [oneNeighborhood]
  · let b := flipPos w a
    have hcell' : D.geom.cellOf b = C := by simpa [b] using hcell
    have hflip : flipPos b a = w := by simpa [b] using flipPos_involutive w a
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [cellSources, hcell']
    · change w ∈ insert b ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a))
      rw [← hflip]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_univ _, rfl⟩

private theorem cellSources_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (C : D.geom.Cell) : (cellSources D C).card ≤ T.S.n k ^ 200 := by
  simpa [cellSources, hκ.Ac_eq] using D.l16_valid.cell_size C

private theorem cellReach_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (C : D.geom.Cell) : (cellReach D C).card ≤ T.S.n k ^ 200 * (T.S.n k + 1) := by
  classical
  calc
    (cellReach D C).card ≤ ∑ b ∈ cellSources D C, (oneNeighborhood b).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ b ∈ cellSources D C, (T.S.n k + 1) := by
      apply Finset.sum_le_sum
      intro b hb
      exact oneNeighborhood_card b
    _ = (cellSources D C).card * (T.S.n k + 1) := by simp
    _ ≤ (T.S.n k ^ 200) * (T.S.n k + 1) :=
      Nat.mul_le_mul_right _ (cellSources_card_le hκ D C)

private theorem directCells_card_le (D : LateData hPT) (v : Pos T k) :
    (D.directCells v).card ≤ T.S.n k + 1 := by
  classical
  have hext : (D.externalEarly v).card ≤ T.S.n k := by
    simpa using (Finset.card_le_univ (D.externalEarly v))
  calc
    (D.directCells v).card ≤ 1 + ((D.externalEarly v).image
        (fun a => D.geom.cellOf (flipPos v a))).card := by
      simpa [LateData.directCells] using
        (Finset.card_union_le ({D.geom.cellOf v})
          ((D.externalEarly v).image (fun a => D.geom.cellOf (flipPos v a))))
    _ ≤ 1 + (D.externalEarly v).card := Nat.add_le_add_left Finset.card_image_le 1
    _ ≤ T.S.n k + 1 := by omega

private noncomputable def directPartnerSet (D : LateData hPT) (v : Pos T k) : Finset (Pos T k) :=
  Finset.univ.filter fun w => ¬ Disjoint (D.directCells v) (D.directCells w)

private noncomputable def directCandidates (D : LateData hPT) (v : Pos T k) : Finset (Pos T k) :=
  (D.directCells v).biUnion (cellReach D)

private theorem directPartner_subset_candidates (D : LateData hPT) (v : Pos T k) :
    directPartnerSet D v ⊆ directCandidates D v := by
  classical
  intro w hw
  have hnd : ¬ Disjoint (D.directCells v) (D.directCells w) :=
    (Finset.mem_filter.mp hw).2
  have hcommon : ∃ C, C ∈ D.directCells v ∧ C ∈ D.directCells w := by
    by_contra hn
    apply hnd
    apply Finset.disjoint_left.mpr
    intro C hCv hCw
    exact hn ⟨C, hCv, hCw⟩
  obtain ⟨C, hCv, hCw⟩ := hcommon
  apply Finset.mem_biUnion.mpr
  exact ⟨C, hCv, mem_cellReach_of_mem_directCells D hCw⟩

private theorem directCandidates_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (v : Pos T k) :
    (directCandidates D v).card ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) := by
  classical
  calc
    (directCandidates D v).card ≤
        ∑ C ∈ D.directCells v, (cellReach D C).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ D.directCells v, (T.S.n k ^ 200 * (T.S.n k + 1)) := by
      apply Finset.sum_le_sum
      intro C hC
      exact cellReach_card_le hκ D C
    _ = (D.directCells v).card * (T.S.n k ^ 200 * (T.S.n k + 1)) := by simp
    _ ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) :=
      Nat.mul_le_mul_right _ (directCells_card_le D v)


theorem event_degree (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (v : Pos T k) :
    (Finset.univ.filter fun w => D.encoding.events.Adjacent v w).card ≤
      T.S.n k ^ (κ.Ac + 4) := by
  have hsub : (Finset.univ.filter fun w => D.encoding.events.Adjacent v w) ⊆
      directPartnerSet D v := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := (Finset.mem_filter.mp hw).2.2
    simpa only [hD.scope_eq] using h
  have hn1 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  calc
    _ ≤ (directPartnerSet D v).card := Finset.card_le_card hsub
    _ ≤ (directCandidates D v).card := Finset.card_le_card (directPartner_subset_candidates D v)
    _ ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) := directCandidates_card_le hκ D v
    _ ≤ (T.S.n k ^ 2) * (T.S.n k ^ 200 * (T.S.n k ^ 2)) :=
      Nat.mul_le_mul hn1 (Nat.mul_le_mul_left _ hn1)
    _ = T.S.n k ^ (κ.Ac + 4) := by rw [hκ.Ac_eq]; ring

private theorem graphBall_contains (D : LateData hPT) (U : Finset (Pos T k)) (r : ℕ) :
    U ⊆ D.encoding.events.graphBall U r := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact fun _ hv => Finset.mem_union.mpr (Or.inl (ih hv))

noncomputable def restore (D : LateData hPT) (targets : Finset D.geom.Cell)
    (s : ∀ C : {C : D.geom.Cell // C ∈ targets}, D.fresh.State C.1) : Config D.fresh :=
  fun C => if hC : C ∈ targets then s ⟨C, hC⟩ else D.fresh.fallback C

private theorem phi_restore (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (assignment : PairAssignment T k) (s : Config D.fresh) :
    A.phi assignment s = A.phi assignment (restore D A.scope (fun C => s C.1)) := by
  apply phi_local D hD A assignment
  intro C hC
  simp only [restore, dif_pos hC]

theorem fixed_pool_comparison (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (D : LateData hPT), D.Spec → ∀ (A : InitialPairData D) (assignment : PairAssignment T k)
      (x : D.encoding.InitInput), D.poolGate (D.expandCells A.scope) x →
        (tapeLaw D.fresh D.encoding.Ts).E (fun t => A.phi assignment (D.encoding.initialState (x.1, t))) ≤
          2 * (D.freshConfigLaw x.1).E (A.phi assignment) := by
  filter_upwards [finiteResamplingTerminalComparison κ hκ T,
    T.S.n_tendsto.eventually_ge_atTop 2] with k hcomp hn
  intro PT hPT D hD A assignment x hgate
  by_cases hrows : A.rows = ∅
  · have hphi : ∀ s, A.phi assignment s = 1 := by simp [InitialPairData.phi, hrows]
    simp only [hphi, FinLaw.E, mul_one, FinLaw.sum_one]
    norm_num
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hrows
  let ctx := listContext D
  let events := D.encoding.events.graphBall
    (A.scope.biUnion D.encoding.events.incidentEvents) (2 * D.encoding.Ts + 3)
  have hevents : ∀ w ∈ events, D.encoding.events.scope w ⊆ D.expandCells A.scope :=
    fun w hw C hC => Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨w, hw, hC⟩))
  have hroot : v ∈ events := by
    apply graphBall_contains D
    apply Finset.mem_biUnion.mpr
    refine ⟨D.geom.cellOf v, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv, by simp [LateData.directCells]⟩
    · simp only [ListEvent.incidentEvents, Finset.mem_filter, Finset.mem_univ, true_and,
        hD.scope_eq]
      simp [LateData.directCells]
  have htargets : A.scope.card ≤ T.S.n k ^ (10 * (κ.Ac + 10)) := by
    have hn1 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
    calc
      A.scope.card ≤ T.S.n k * (T.S.n k + 1) := scope_card D A
      _ ≤ T.S.n k * T.S.n k ^ 2 := Nat.mul_le_mul_left _ hn1
      _ = T.S.n k ^ 3 := by ring
      _ ≤ T.S.n k ^ (10 * (κ.Ac + 10)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hdegree := event_degree hκ D hD hn
  have hfailure : ∀ w ∈ events, (ctx.freshConfigLaw x.1).pr (D.encoding.events.S w) ≤
      Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) := by
    intro w hw
    exact hgate.2 w (hevents w hw)
  have hinput : FiniteResamplingInput ctx D.encoding.events events x.1 A.scope v := by
    refine ⟨hn, hroot, hdegree, htargets, ?_, hfailure⟩
    intro C hC
    apply hgate.1 C
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Finset.mem_union.mpr (Or.inl hC)
    · obtain ⟨w, hw, hC⟩ := Finset.mem_biUnion.mp hC
      exact hevents w hw hC
  have hcover : TargetWitnessCover (Ts := initialResamplingRounds T k)
      (D := ctx) D.encoding.events D.encoding.order events x.1 A.scope :=
    fun tapes => finiteResamplingTargetWitness (D := ctx) D.encoding.events
      D.encoding.order events x.1 A.scope tapes
  have hcount : TargetWitnessCountBound (Ts := initialResamplingRounds T k)
      (D := ctx) D.encoding.events ((T.S.n k) ^ (κ.Ac + 4)) events A.scope :=
    finiteResamplingTargetCount (D := ctx) D.encoding.events _ events A.scope hdegree
  have hseparate : TerminalTestBound (Ts := initialResamplingRounds T k)
      (D := ctx) D.encoding.events events x.1 A.scope :=
    finiteResamplingTerminalSeparation (D := ctx) D.encoding.events hn events x.1 hfailure A.scope
  let Ψ := fun s => A.phi assignment (restore D A.scope s)
  have hbound := hcomp PT ctx D.encoding.events D.encoding.order events x.1 A.scope v
    hinput hcover hcount hseparate Ψ (fun s => phi_nonneg D A assignment _)
  have hbound' : (tapeLaw D.fresh D.encoding.Ts).E (fun t => Ψ
      (fun C : {C : D.geom.Cell // C ∈ A.scope} =>
        (D.encoding.events.resample D.encoding.Ts D.encoding.order events x.1 t.extend) C.1)) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
        (FinLaw.pi fun C : {C : D.geom.Cell // C ∈ A.scope} => D.fresh.fresh C.1 (x.1 C.1)).E Ψ := by
    have hTs : initialResamplingRounds T k = D.encoding.Ts := by
      simpa only [initialResamplingRounds] using D.encoding.Ts_eq.symm
    change (tapeLaw D.fresh (initialResamplingRounds T k)).E
      (fun t => Ψ (fun C : {C : D.geom.Cell // C ∈ A.scope} =>
        (D.encoding.events.resample (initialResamplingRounds T k) D.encoding.order events x.1 t.extend) C.1)) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
        (FinLaw.pi fun C : {C : D.geom.Cell // C ∈ A.scope} => D.fresh.fresh C.1 (x.1 C.1)).E Ψ at hbound
    have htransport : ∀ m : ℕ, m = initialResamplingRounds T k →
        (tapeLaw D.fresh m).E (fun t => Ψ
          (fun C : {C : D.geom.Cell // C ∈ A.scope} =>
            (D.encoding.events.resample m D.encoding.order events x.1 t.extend) C.1)) ≤
          (1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2)) *
            (FinLaw.pi fun C : {C : D.geom.Cell // C ∈ A.scope} => D.fresh.fresh C.1 (x.1 C.1)).E Ψ := by
      intro m hm
      subst m
      exact hbound
    exact htransport D.encoding.Ts hTs.symm
  have hfresh : (D.freshConfigLaw x.1).E (A.phi assignment) =
      (FinLaw.pi fun C : {C : D.geom.Cell // C ∈ A.scope} => D.fresh.fresh C.1 (x.1 C.1)).E Ψ :=
    pi_E_project _ A.scope (A.phi assignment) D.fresh.fallback (phi_local D hD A assignment)
  have hleft : (tapeLaw D.fresh D.encoding.Ts).E
      (fun t => A.phi assignment (D.encoding.initialState (x.1, t))) =
      (tapeLaw D.fresh D.encoding.Ts).E (fun t => Ψ
        (fun C : {C : D.geom.Cell // C ∈ A.scope} =>
          (D.encoding.events.resample D.encoding.Ts D.encoding.order events x.1 t.extend) C.1)) := by
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    apply (phi_restore D hD A assignment _).trans
    apply congrArg (fun s => A.phi assignment (restore D A.scope s))
    funext C
    have hball : D.encoding.events.graphBall (D.encoding.events.incidentEvents C.1)
        (2 * D.encoding.Ts + 3) ⊆ events :=
      graphBall_mono D _ _ (fun w hw => Finset.mem_biUnion.mpr ⟨C.1, C.2, hw⟩) _
    exact (resampleLocality (D := ctx) D.encoding.events D.encoding.Ts D.encoding.order x.1 t.extend).1
      C.1 events hball
  have hfactor : 1 + Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) ≤ 2 := by
    have h : Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (show 1 ≤ (T.S.n k : ℝ) by exact_mod_cast (show 1 ≤ T.S.n k by omega))
      (show -(κ.P : ℝ) / 2 ≤ 0 by
        have hP : (0 : ℝ) ≤ κ.P := Nat.cast_nonneg _
        linarith)
    linarith
  rw [hleft, hfresh]
  exact hbound'.trans (mul_le_mul_of_nonneg_right hfactor (by
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg ((FinLaw.pi _).nonneg s) (phi_nonneg D A assignment _)))

theorem bind_E {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (f : α × β → ℝ) :
    (FinLaw.bind P K).E f = P.E (fun a => (K a).E (fun b => f (a, b))) := by
  simp only [FinLaw.E, FinLaw.bind, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem E_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp only [FinLaw.E, ← Finset.sum_mul, P.sum_one, one_mul]

theorem perm_resampling_comparison (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (D : LateData hPT), D.Spec → ∀ (A : InitialPairData D) (assignment : PairAssignment T k),
        A.permTest assignment ≤ 2 * A.permFreshTest assignment := by
  filter_upwards [fixed_pool_comparison hκ T] with k hcomp
  intro PT hPT D hD A assignment
  let t0 : Tapes D.fresh D.encoding.Ts := fun C _ _ => D.fresh.fallback C
  simp only [InitialPairData.permTest, InitialPairData.permFreshTest,
    LateEncoding.permLaw, LateEncoding.initialLaw, bind_E]
  rw [FinLaw.E, FinLaw.E, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pools _
  have hgate : ∀ t : Tapes D.fresh D.encoding.Ts,
      D.poolGate (D.expandCells A.scope) (pools, t) ↔
      D.poolGate (D.expandCells A.scope) (pools, t0) := fun _ => Iff.rfl
  simp only [hgate]
  by_cases hp : D.poolGate (D.expandCells A.scope) (pools, t0)
  · simp only [if_pos hp, E_const]
    have h := hcomp PT hPT D hD A assignment (pools, t0) hp
    have hmul := mul_le_mul_of_nonneg_left h (D.encoding.poolLaw.nonneg pools)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  · simp only [if_neg hp, E_const, mul_zero]
    exact le_rfl

noncomputable def weightAt (D : LateData hPT) (j : Fin (D.geom.r + 1))
    (h : D.encoding.base.History j) (v : Pos T k) (x : Fin (T.S.N k)) : ℝ :=
  (D.initialPrior v h.1).w x * ∏ b : D.encoding.base.ProcessedRole j,
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
    else 1

private theorem weightAt_nonneg (D : LateData hPT) (j : Fin (D.geom.r + 1))
    (h : D.encoding.base.History j) (v : Pos T k) (x : Fin (T.S.N k)) :
    0 ≤ weightAt D j h v x := by
  apply mul_nonneg ((D.initialPrior v h.1).nonneg x)
  apply Finset.prod_nonneg
  intro b _
  split_ifs <;> norm_num

theorem full_finalWeight_pos (D : LateData hPT) (δ : ℝ)
    (input : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
    (hfull : D.full δ input h) (v : Pos T k) (hv : IsEvenRole v)
    (hcap : ∀ j : Fin D.geom.r, (∃ b ∈ D.encoding.base.classes j,
        (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b) →
      (D.currentPrior j v (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))).w D.fallback < 1)
    (herr : ∀ j : Fin D.geom.r, D.error v j < 1 / 6) :
    0 < ∑ y, finalWeight D h v y := by
  let J := Finset.univ.filter fun j : Fin D.geom.r => ∃ b ∈ D.encoding.base.classes j,
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b
  have hvalid : D.initialValid v h.1 := hfull.2.2.2.2.1 v hv
  have hExists : ∃ x, finalWeight D h v x ≠ 0 := by
    by_cases hJ : J.Nonempty
    · let j := J.max' hJ
      have hj : j ∈ J := Finset.max'_mem J hJ
      obtain ⟨b, hb, hab⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨a, ha⟩ := adjacent_flip v b hab
      have hflip : flipPos b a = v := by rw [ha]; exact flipPos_involutive v a
      let pre := D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)
      have hprevalid : D.initialValid v pre.1 := hvalid
      have hCap := hcap j ⟨b, hb, hab⟩
      have hpositive : 0 < ∑ x, weightAt D j.castSucc pre v x := by
        by_contra hnot
        have hbad : ¬ ((∀ x, 0 ≤ weightAt D j.castSucc pre v x) ∧
            0 < ∑ x, weightAt D j.castSucc pre v x) := fun H => hnot H.2
        change (D.priorAt j.castSucc v pre).w D.fallback < 1 at hCap
        simp only [LateData.priorAt, if_pos hprevalid] at hCap
        change (D.normalize (weightAt D j.castSucc pre v)).w D.fallback < 1 at hCap
        simp only [LateData.normalize, dif_neg hbad, Law.dirac, if_pos rfl] at hCap
        exact (lt_irrefl (1 : ℝ)) hCap
      have hR := (hfull.2.2.2.2.2.2 j).2.2.2.2 ⟨b, hb⟩
      have hhitMass : 0 < colDeg (T.S.E k) PT.tiling.c (D.currentPrior j v pre)
          (D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨b, hb⟩)) := by
        have hlow : 0 < (1 / 2 : ℝ) - 3 * D.error v j := by linarith [herr j]
        have hR3 := hR.2.1 a
        have hR3' : (1 / 2 : ℝ) - 3 * D.error v j ≤
            colDeg (T.S.E k) PT.tiling.c (D.currentPrior j v pre)
              (D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨b, hb⟩)) := by
          simpa only [Subtype.coe_mk, hflip] using hR3
        exact lt_of_lt_of_le hlow hR3'
      obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => by
        apply mul_nonneg ((D.currentPrior j v pre).nonneg x)
        split_ifs <;> norm_num)).mp hhitMass
      have hhit : Hits (T.S.E k) PT.tiling.c x
          (D.encoding.base.rowLabel (D.pastRows h j j.isLt ⟨b, hb⟩)) := by
        by_contra hnot
        simp [hnot] at hx
      have hcurr : (D.currentPrior j v pre).w x ≠ 0 := by
        intro hzero
        simp [hzero] at hx
      have hraw : weightAt D j.castSucc pre v x ≠ 0 := by
        intro hzero
        apply hcurr
        simp only [LateData.currentPrior, LateData.priorAt, if_pos hprevalid]
        change (D.normalize (weightAt D j.castSucc pre v)).w x = 0
        simp only [LateData.normalize,
          dif_pos (show (∀ y, 0 ≤ weightAt D j.castSucc pre v y) ∧
            0 < ∑ y, weightAt D j.castSucc pre v y from ⟨weightAt_nonneg D _ _ _, hpositive⟩),
          hzero, zero_div]
      have hxinit := (mul_ne_zero_iff.mp hraw).1
      have hxpast := (mul_ne_zero_iff.mp hraw).2
      refine ⟨x, mul_ne_zero hxinit ?_⟩
      apply Finset.prod_ne_zero_iff.mpr
      intro w _
      by_cases hw : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v w.1
      · have hwclass : ∃ s, D.geom.classOf w.1 = some s := by
          have hm := Eq.mp (congrArg (fun S : Finset (Pos T k) => w.1 ∈ S)
            D.encoding.base.processed_last) w.2
          exact (Finset.mem_filter.mp hm).2
        obtain ⟨s, hs⟩ := hwclass
        have hsclass : w.1 ∈ D.encoding.base.classes s :=
          (D.encoding.base.class_of_spec w.1 s).mpr hs
        have hsJ : s ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.1, hsclass, hw⟩
        have hsle : s ≤ j := Finset.le_max' J s hsJ
        by_cases hsj : s = j
        · have hwb : w.1 = b := by
            obtain ⟨a', ha'⟩ := adjacent_flip v w.1 hw
            have hba : D.geom.classOf (flipPos v a) = some j := by
              rw [← ha]; exact (D.encoding.base.class_of_spec b j).mp hb
            have hwa : D.geom.classOf (flipPos v a') = some j := by rw [← ha', ← hsj]; exact hs
            have heq := D.l16_valid.one_per_class v j a' a hwa hba
            rw [ha', heq, ← ha]
          have hf : Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 w)) := by
            rcases w with ⟨w, hwmem⟩
            dsimp only at hwb ⊢
            subst w
            exact hhit
          simp [hw, hf]
        · have hlt : s.val < j.val := by
            have hlt : s < j := lt_of_le_of_ne hsle hsj
            exact hlt
          have hwpre : w.1 ∈ D.encoding.base.processed j.castSucc :=
            D.class_before s j.castSucc hlt hsclass
          have hfactor := Finset.prod_ne_zero_iff.mp hxpast ⟨w.1, hwpre⟩ (Finset.mem_univ _)
          simpa only [pre, LateData.beforeHistory] using hfactor
      · simp [hw]
    · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      have hsome : ∃ x, 0 < (D.initialPrior v h.1).w x := by
        have hpos : 0 < ∑ x, (D.initialPrior v h.1).w x := by
          rw [(D.initialPrior v h.1).sum_eq_one]
          norm_num
        obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg
          (fun x _ => (D.initialPrior v h.1).nonneg x)).mp hpos
        exact ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hsome
      refine ⟨x, mul_ne_zero (ne_of_gt hx) ?_⟩
      apply Finset.prod_ne_zero_iff.mpr
      intro w _
      have hn : ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v w.1 := by
        intro hw
        have hm := Eq.mp (congrArg (fun S : Finset (Pos T k) => w.1 ∈ S)
          D.encoding.base.processed_last) w.2
        obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hm).2
        have hsclass := (D.encoding.base.class_of_spec w.1 s).mpr hs
        have hsJ : s ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.1, hsclass, hw⟩
        simpa [hJempty] using hsJ
      simp [hn]
  obtain ⟨x, hx⟩ := hExists
  apply (Finset.sum_pos_iff_of_nonneg (fun y _ => finalWeight_nonneg D h v y)).mpr
  exact ⟨x, Finset.mem_univ _, lt_of_le_of_ne (finalWeight_nonneg D h v x) hx.symm⟩

theorem smallErrors_error_le (D : LateData hPT) (ε : ℝ)
    (hsmall : SmallErrors κ T k PT D.geom ε) (v : Pos T k) (j : Fin D.geom.r) :
    D.error v j ≤ ε := by
  have hnonneg : ∀ s : Fin D.geom.r,
      0 ≤ lateError κ T k PT (D.geom.patchOf v) (D.geom.r - s.val) := by
    intro s
    unfold lateError
    have hd : 0 ≤ densityScale T k := by unfold densityScale; positivity
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hd _) (Real.exp_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hsum0 : 0 ≤ ∑ s : Fin D.geom.r,
      lateError κ T k PT (D.geom.patchOf v) (D.geom.r - s.val) :=
    Finset.sum_nonneg (fun s _ => hnonneg s)
  have hsum := hsmall (D.geom.patchOf v)
  have hheight : (1 : ℝ) ≤ max 1 ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) := le_max_left _ _
  have hle : (∑ s : Fin D.geom.r,
      lateError κ T k PT (D.geom.patchOf v) (D.geom.r - s.val)) ≤ ε := by
    nlinarith
  exact (Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ j)).trans hle

theorem currentCap_lt_one (hκ : κ.Admissible) (D : LateData hPT)
    (hC : CurrentListCapFacts D) (hscale : 8 * κ.KB < densityScale T k)
    (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hfull : D.full δ input h)
    (v : Pos T k) (j : Fin D.geom.r)
    (hneighbor : ∃ b ∈ D.encoding.base.classes j,
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b) :
    (D.currentPrior j v (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))).w D.fallback < 1 := by
  obtain ⟨b, hb, hadj⟩ := hneighbor
  obtain ⟨a, ha⟩ := adjacent_flip v b hadj
  have hflip : flipPos b a = v := by rw [ha]; exact flipPos_involutive v a
  have hgate := ((hfull.2.2.2.2.2.2 j).2.2.2.2 ⟨b, hb⟩).1
  have hcap := hC j b (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) hgate hb a D.fallback
  rw [hflip] at hcap
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hgain : 0 ≤ PT.tiling.gain (D.geom.patchOf v) := by
    cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Tiling.gain] <;> positivity
  have hbase0 : 0 ≤ 8 * κ.KB / densityScale T k := by
    have hKB : 0 ≤ κ.KB := by nlinarith [hκ.KB_big]
    unfold densityScale
    positivity
  have hexp : Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hpow : Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hscalePos : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  calc
    _ ≤ 8 * κ.KB / densityScale T k *
        Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) := hcap
    _ ≤ 8 * κ.KB / densityScale T k := by
      have h1 : 8 * κ.KB / densityScale T k *
          Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) ≤ 8 * κ.KB / densityScale T k := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hbase0
      have hpow0 : 0 ≤ Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have h2 := mul_le_mul_of_nonneg_right h1 hpow0
      have h3 : 8 * κ.KB / densityScale T k * Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) ≤
          8 * κ.KB / densityScale T k := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hbase0
      exact h2.trans h3
    _ < 1 := (div_lt_one hscalePos).mpr hscale

end HypercubeRamsey.S18.Lane_sol_s18_n5
