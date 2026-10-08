import HypercubeRamsey.S18.Prefix_sol_s18_n4
import HypercubeRamsey.S18.Pools_sol_s18_n5

namespace HypercubeRamsey.Lane_sol_s18_3a_perm
open Classical
open scoped BigOperators

/-- Refreshing any deterministic subset of independent coordinates preserves
the product law. The remaining coordinates can therefore be fixed first. -/
theorem pi_refresh_expect {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset I) (f : (∀ i, Ω i) → ℝ) :
    (FinLaw.pi P).E f = (FinLaw.pi P).E (fun x =>
      (FinLaw.pi fun i => if i ∈ S then P i else FinLaw.dirac (x i)).E f) := by
  classical
  symm
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  change (∑ x : ∀ i, Ω i, (∏ i, (P i).w (x i)) *
    ∏ i, (if i ∈ S then P i else FinLaw.dirac (x i)).w (y i)) = ∏ i, (P i).w (y i)
  simp_rw [← Finset.prod_mul_distrib]
  rw [show (∑ x : ∀ i, Ω i, ∏ i, (P i).w (x i) *
      (if i ∈ S then P i else FinLaw.dirac (x i)).w (y i)) =
      ∏ i, ∑ a : Ω i, (P i).w a * (if i ∈ S then P i else FinLaw.dirac a).w (y i)
    from (Fintype.prod_sum (fun i (a : Ω i) =>
      (P i).w a * (if i ∈ S then P i else FinLaw.dirac a).w (y i))).symm]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp only [if_pos hi, ← Finset.sum_mul, (P i).sum_one, one_mul]
  · simp only [if_neg hi, FinLaw.dirac, mul_ite, mul_one, mul_zero]
    simp

/-- Group independent pools and their independent lookup tapes by cell. -/
theorem pi_bind_expect {I : Type*} [Fintype I] [DecidableEq I]
    {Ω Λ : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Λ i)]
    (P : ∀ i, FinLaw (Ω i)) (Q : ∀ i, FinLaw (Λ i))
    (f : (∀ i, Ω i) × (∀ i, Λ i) → ℝ) :
    (FinLaw.bind (FinLaw.pi P) (fun _ => FinLaw.pi Q)).E f =
      (FinLaw.pi fun i => FinLaw.bind (P i) (fun _ => Q i)).E
        (fun x => f (fun i => (x i).1, fun i => (x i).2)) := by
  classical
  let e : ((∀ i, Ω i) × (∀ i, Λ i)) ≃ (∀ i, Ω i × Λ i) := {
    toFun x i := (x.1 i, x.2 i)
    invFun x := (fun i => (x i).1, fun i => (x i).2)
    left_inv _ := rfl
    right_inv _ := rfl }
  unfold FinLaw.E
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, (P i).w (x i).1) * ∏ i, (Q i).w (x i).2) * _ =
    (∏ i, (P i).w (x i).1 * (Q i).w (x i).2) * _
  rw [Finset.prod_mul_distrib]
  rfl

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid}

abbrev CellInput (D : S18.LateData hPT) (C : D.geom.Cell) :=
  D.fresh.Pool C × (Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C)

noncomputable def cellInputLaw (D : S18.LateData hPT) (C : D.geom.Cell) :
    FinLaw (CellInput D C) :=
  FinLaw.bind (D.cellPoolLaw C) (fun _ => Lane_sol_s18_n4.cellTapeLaw D C)

def collectInput (D : S18.LateData hPT) (x : ∀ C, CellInput D C) : D.encoding.InitInput :=
  (fun C => (x C).1, fun C => (x C).2)

theorem iidPoolLaw_pi (D : S18.LateData hPT) :
    D.encoding.iidLaw = FinLaw.pi (fun C => D.cellPoolLaw C) := by
  classical
  let P := fun C : D.geom.Cell => FinLaw.uniform
    (Finset.univ : Finset (D.fresh.Pool C))
    ⟨D.l16_valid.pools_nonempty.choose C, Finset.mem_univ _⟩
  have hpi : D.encoding.iidLaw = FinLaw.pi P := by
    have h := S18.Lane_sol_s18_n5.uniform_pi_sets
      (fun C : D.geom.Cell => (Finset.univ : Finset (D.fresh.Pool C)))
      (fun C => ⟨D.l16_valid.pools_nonempty.choose C, Finset.mem_univ _⟩)
    simpa only [Finset.mem_univ, implies_true, Finset.filter_true, LateEncoding.iidLaw,
      iidPoolLaw, P] using h
  have hcell (C : D.geom.Cell) : D.cellPoolLaw C = P C := by
    letI : DecidableEq (D.fresh.Pool C) := Classical.decEq _
    unfold S18.LateData.cellPoolLaw
    rw [hpi]
    apply S16.Lane_q_s16_comp2.finLaw_ext
    intro q
    calc
      _ = (FinLaw.map (FinLaw.pi P) (fun x => x C)).w q := by
        unfold FinLaw.map
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x C = q <;> simp [hx]
      _ = _ := congrArg (fun L => L.w q) (Lane_q_s17_res1.pi_map_coordinate_law P C)
  simp_rw [hcell]
  exact hpi

theorem iidInitial_expect (D : S18.LateData hPT) (f : D.encoding.InitInput → ℝ) :
    (D.encoding.initialLaw D.encoding.iidLaw).E f =
      (FinLaw.pi (cellInputLaw D)).E (fun x => f (collectInput D x)) := by
  rw [LateEncoding.initialLaw, iidPoolLaw_pi]
  exact pi_bind_expect _ _ f

noncomputable def prescribedIndex (D : S18.LateData hPT) (critical : Finset D.geom.Cell)
    (pattern : ℕ → Finset (Pos T k)) (C : D.geom.Cell) : Fin (D.encoding.Ts + 2) :=
  ⟨∑ j ∈ Finset.range D.encoding.Ts,
    if ∃ v ∈ pattern j ∩ S18.replayMarked D critical, C ∈ D.encoding.events.scope v then 1 else 0,
    by
      have h : (∑ j ∈ Finset.range D.encoding.Ts,
          if ∃ v ∈ pattern j ∩ S18.replayMarked D critical,
            C ∈ D.encoding.events.scope v then 1 else 0) ≤ D.encoding.Ts := by
        calc
          _ ≤ ∑ _j ∈ Finset.range D.encoding.Ts, 1 :=
            Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
          _ = _ := by simp
      omega⟩

theorem criticalState_prescribed (D : S18.LateData hPT) (hReplay : S18.ReplayFacts D)
    (critical : Finset D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (x : D.encoding.InitInput) (C : D.geom.Cell) (hC : C ∈ critical) :
    (S18.replayRounds D (S18.replayMarked D critical) pattern x D.encoding.Ts).1 C =
      x.2 C (prescribedIndex D critical pattern C) (x.1 C) := by
  rw [Lane_sol_s18_n4.replayState_entry]
  have hle := Lane_sol_s18_n4.replayCounter_le D (S18.replayMarked D critical)
    pattern x D.encoding.Ts C
  have hind := hReplay.2.2 critical pattern x D.encoding.Ts C hC
  unfold Tapes.extend
  apply congrArg (fun i => x.2 C i (x.1 C))
  apply Fin.ext
  exact (Nat.min_eq_left (by omega)).trans hind

theorem pi_refresh_support {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset I) (outside x : ∀ i, Ω i)
    (hx : 0 < (FinLaw.pi fun i => if i ∈ S then P i else FinLaw.dirac (outside i)).w x)
    (i : I) (hi : i ∉ S) : x i = outside i := by
  by_contra hne
  have hz : (if i ∈ S then P i else FinLaw.dirac (outside i)).w (x i) = 0 := by
    simp [hi, FinLaw.dirac, hne]
  have hzero : (FinLaw.pi fun j => if j ∈ S then P j else FinLaw.dirac (outside j)).w x = 0 :=
    Finset.prod_eq_zero (f := fun j => (if j ∈ S then P j else FinLaw.dirac (outside j)).w (x j))
      (Finset.mem_univ i) hz
  exact (ne_of_gt hx) hzero

theorem map_dirac {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (f : α → β) :
    FinLaw.map (FinLaw.dirac a) f = FinLaw.dirac (f a) := by
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro b
  simp only [FinLaw.map, FinLaw.dirac]
  rw [Finset.sum_eq_single a]
  · simp [eq_comm]
  · intro x _ hx
    by_cases hfx : f x = b <;> simp [hfx, hx]
  · simp

private theorem map_decidable_eq {α β : Type*} [Fintype α] [Fintype β]
    (d e : DecidableEq β) (P : FinLaw α) (f : α → β) :
    @FinLaw.map α β _ _ d P f = @FinLaw.map α β _ _ e P f := by
  have hd : d = e := Subsingleton.elim _ _
  rw [hd]

/-- For fixed outside inputs, refresh the critical pool/tape coordinates.
The typicality gate is retained until comparison with the normalized law. -/
theorem criticalRefreshReplayBound (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (c : ℝ) (hTransfer : S18.TransferBound D c)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (omitted : Option D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (outside : ∀ C, CellInput D C) :
    let X₀ : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
    (FinLaw.pi fun C => if C ∈ X₀.criticalCells then cellInputLaw D C
      else FinLaw.dirac (outside C)).E (fun x =>
        if ∀ C ∈ X₀.criticalCells, D.fresh.typical C (x C).1 then
          Lane_sol_s18_n4.forcedReplayRisk D X₀.criticalCells pattern F (collectInput D x)
        else 0) ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  classical
  let X₀ : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  let fixed := (S18.replayRounds D (S18.replayMarked D X₀.criticalCells)
    pattern (collectInput D outside) D.encoding.Ts).1
  let X : S18.CriticalTransferData D := ⟨F.2, hvalid, omitted, fixed⟩
  let L := FinLaw.pi fun C => if C ∈ X.criticalCells then cellInputLaw D C
    else FinLaw.dirac (outside C)
  let read : ∀ C, CellInput D C → D.fresh.Pool C × D.fresh.State C := fun C x =>
    if C ∈ X.criticalCells then
      (x.1, x.2 (prescribedIndex D X.criticalCells pattern C) x.1)
    else (D.l16_valid.pools_nonempty.choose C, fixed C)
  let Q := FinLaw.pi fun C => if C ∈ X.criticalCells then
    FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C)
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  letI : DecidableEq X.Raw := Classical.decEq _
  have hmap : FinLaw.map L (fun x C => read C (x C)) = Q := by
    have h0 := Lane_q_s17_res1.pi_map_law
      (fun C => if C ∈ X.criticalCells then cellInputLaw D C else FinLaw.dirac (outside C)) read
    have hread (C : D.geom.Cell) :
        FinLaw.map (if C ∈ X.criticalCells then cellInputLaw D C else FinLaw.dirac (outside C))
          (read C) = if C ∈ X.criticalCells then
            FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C) else
            FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C) := by
      by_cases hC : C ∈ X.criticalCells
      · simp only [if_pos hC, read]
        exact Lane_sol_s18_n4.prescribedPoolTapeLaw D C _
      · simp only [if_neg hC, read]
        exact map_dirac _ _
    have hread' (C : D.geom.Cell) :
        @FinLaw.map _ _ _ _ (Classical.decEq _)
          (if C ∈ X.criticalCells then cellInputLaw D C else FinLaw.dirac (outside C))
          (read C) = if C ∈ X.criticalCells then
            FinLaw.bind (D.cellPoolLaw C) (D.fresh.fresh C) else
            FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C) := by
      exact (map_decidable_eq _ _ _ _).trans (hread C)
    simp_rw [hread'] at h0
    exact (map_decidable_eq _ _ L (fun x C => read C (x C))).trans h0
  let f := fun raw : X.Raw => Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F
    (Lane_sol_s18_n4.criticalReplayInput D X.criticalCells (collectInput D outside) raw)
  have hf : ∀ raw, 0 ≤ f raw := by
    intro raw
    exact Lane_q_s17_res1.finLaw_pr_nonneg _ _
  have hstate (x : ∀ C, CellInput D C) (hx : 0 < L.w x) :
      (S18.replayRounds D (S18.replayMarked D X.criticalCells)
        pattern (collectInput D x) D.encoding.Ts).1 =
      (S18.replayRounds D (S18.replayMarked D X.criticalCells) pattern
        (Lane_sol_s18_n4.criticalReplayInput D X.criticalCells (collectInput D outside)
          (fun C => read C (x C))) D.encoding.Ts).1 := by
    funext C
    rw [Lane_sol_s18_n4.criticalReplayState D hReplay]
    by_cases hC : C ∈ X.criticalCells
    · rw [if_pos hC, criticalState_prescribed D hReplay _ _ _ C hC]
      simp only [read, if_pos hC, collectInput]
    · rw [if_neg hC]
      apply (hReplay.2.1 X.criticalCells pattern (collectInput D x) (collectInput D outside)
        D.encoding.Ts _ C hC).1
      intro C hC
      have heq := pi_refresh_support (cellInputLaw D) X.criticalCells outside x hx C hC
      exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  have heq : L.E (fun x =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (x C).1 then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (collectInput D x) else 0) =
      Q.E (fun raw => if ∀ C ∈ X.criticalCells, D.fresh.typical C (raw C).1 then f raw else 0) := by
    rw [← hmap, S16.Lane_q_s16_comp2.map_expect]
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    by_cases hx : 0 < L.w x
    · have ht : (∀ C ∈ X.criticalCells, D.fresh.typical C (read C (x C)).1) ↔
          ∀ C ∈ X.criticalCells, D.fresh.typical C (x C).1 := by
        apply forall_congr'; intro C
        apply imp_congr_right; intro hC
        simp only [read, if_pos hC]
      simp only [ht]
      congr 1
      split_ifs
      · unfold Lane_sol_s18_n4.forcedReplayRisk f
        rw [hstate x hx]
        rfl
      · rfl
    · have hz : L.w x = 0 := le_antisymm (le_of_not_gt hx) (L.nonneg x)
      simp [hz]
  change L.E (fun x => if ∀ C ∈ X.criticalCells, D.fresh.typical C (x C).1 then
    Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F (collectInput D x) else 0) ≤ _
  rw [heq]
  exact (Lane_sol_s18_n4.criticalTypicalIntegral_le D hD X f hf).trans
    (Lane_sol_s18_n4.criticalFreshReplayBound D hReplay c hTransfer F hkind hvalid omitted
      pattern (collectInput D outside))

/-- The unpinned iid enlarged replay integral has the transfer bound, for
every total forced pattern; no pattern-consistency condition is needed. -/
theorem iidReplayBound (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (c : ℝ) (hTransfer : S18.TransferBound D c)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (omitted : Option D.geom.Cell) (pattern : ℕ → Finset (Pos T k)) :
    let X : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
    (D.encoding.initialLaw D.encoding.iidLaw).E (fun x =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F x else 0) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  classical
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, omitted, fun C => D.fresh.fallback C⟩
  dsimp only
  rw [iidInitial_expect, pi_refresh_expect (cellInputLaw D) X.criticalCells]
  calc
    _ ≤ (FinLaw.pi (cellInputLaw D)).E
        (fun _ => Real.exp (-Real.rpow (T.S.n k : ℝ) c)) :=
      S16.Lane_q_s16_comp2.expect_le _ _ _ (fun outside =>
        criticalRefreshReplayBound D hD hReplay c hTransfer F hkind hvalid omitted pattern outside)
    _ = _ := S18.Lane_sol_s18_n5.E_const _ _

/-- An event determined by the fixed outside coordinates survives the
critical refresh, so the transfer estimate also controls its joint mass. -/
theorem pi_refresh_gated_bound {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset I) (f : (∀ i, Ω i) → ℝ)
    (A : (∀ i, Ω i) → Prop) (q : ℝ) (hq : 0 ≤ q)
    (hA : ∀ x y, (∀ i, i ∉ S → x i = y i) → (A x ↔ A y))
    (hbound : ∀ (outside : ∀ i, Ω i),
      (FinLaw.pi fun i => if i ∈ S then P i else FinLaw.dirac (outside i)).E f ≤ q) :
    (FinLaw.pi P).E (fun x => if A x then f x else 0) ≤ q * (FinLaw.pi P).pr A := by
  classical
  rw [pi_refresh_expect P S]
  have hinner (outside : ∀ i, Ω i) :
      (FinLaw.pi fun i => if i ∈ S then P i else FinLaw.dirac (outside i)).E
        (fun x => if A x then f x else 0) ≤ if A outside then q else 0 := by
    let L := FinLaw.pi fun i => if i ∈ S then P i else FinLaw.dirac (outside i)
    have heq : L.E (fun x => if A x then f x else 0) =
        if A outside then L.E f else 0 := by
      unfold FinLaw.E
      split_ifs with ha
      · apply Finset.sum_congr rfl
        intro x _
        by_cases hx : 0 < L.w x
        · have hax := (hA x outside (pi_refresh_support P S outside x hx)).mpr ha
          simp only [if_pos hax]
        · have hz : L.w x = 0 := le_antisymm (le_of_not_gt hx) (L.nonneg x)
          simp [hz]
      · apply Finset.sum_eq_zero
        intro x _
        by_cases hx : 0 < L.w x
        · have hax := (hA x outside (pi_refresh_support P S outside x hx)).not.mpr ha
          simp only [if_neg hax, mul_zero]
        · have hz : L.w x = 0 := le_antisymm (le_of_not_gt hx) (L.nonneg x)
          simp [hz]
    change L.E _ ≤ _
    rw [heq]
    split_ifs
    · exact hbound outside
    · exact le_rfl
  calc
    _ ≤ (FinLaw.pi P).E (fun x => if A x then q else 0) :=
      S16.Lane_q_s16_comp2.expect_le _ _ _ hinner
    _ = q * (FinLaw.pi P).pr A := by
      unfold FinLaw.E FinLaw.pr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases ha : A x <;> simp [ha, mul_comm]

theorem iidReplayPinnedJointBound (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (c : ℝ) (hTransfer : S18.TransferBound D c)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (pin : S18.SlotPin D) (pattern : ℕ → Finset (Pos T k)) :
    let X : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, some pin.1, fun C => D.fresh.fallback C⟩
    (D.encoding.initialLaw D.encoding.iidLaw).E (fun x =>
      if S18.pinEvent D pin x then
        if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
          Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F x else 0
      else 0) ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) c) *
        (D.encoding.initialLaw D.encoding.iidLaw).pr (S18.pinEvent D pin) := by
  classical
  let X : S18.CriticalTransferData D :=
    ⟨F.2, hvalid, some pin.1, fun C => D.fresh.fallback C⟩
  have hpin : pin.1 ∉ X.criticalCells := Lane_sol_s18_n4.omitted_not_critical D X pin.1 rfl
  have hpr : (D.encoding.initialLaw D.encoding.iidLaw).pr (S18.pinEvent D pin) =
      (FinLaw.pi (cellInputLaw D)).pr (fun x => S18.pinEvent D pin (collectInput D x)) := by
    have h := iidInitial_expect D (fun x => if S18.pinEvent D pin x then 1 else 0)
    simpa only [FinLaw.E, FinLaw.pr, mul_ite, mul_one, mul_zero] using h
  dsimp only
  rw [iidInitial_expect, hpr]
  apply pi_refresh_gated_bound (cellInputLaw D) X.criticalCells _ _ _ (Real.exp_pos _).le
  · intro x y hxy
    unfold S18.pinEvent collectInput
    dsimp only
    rw [hxy pin.1 hpin]
  · intro outside
    exact criticalRefreshReplayBound D hD hReplay c hTransfer F hkind hvalid
      (some pin.1) pattern outside

noncomputable def iidPinnedLaw (D : S18.LateData hPT) (pin : Option (S18.SlotPin D)) :
    FinLaw D.encoding.InitInput :=
  let P := D.encoding.initialLaw D.encoding.iidLaw
  match pin with
  | none => P
  | some p =>
    let A := Finset.univ.filter (S18.pinEvent D p)
    if h : 0 < ∑ x ∈ A, P.w x then FinLaw.cond P A h else P

theorem cond_expect_gated {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Finset Ω) (hA : 0 < ∑ x ∈ A, P.w x) (f : Ω → ℝ) :
    (FinLaw.cond P A hA).E f = P.E (fun x => if x ∈ A then f x else 0) /
      (∑ x ∈ A, P.w x) := by
  unfold FinLaw.E FinLaw.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ A <;> simp [hx, div_mul_eq_mul_div]

/-- The iid replay estimate is uniform under the same global slot pin.
The pinned cell remains an outside coordinate throughout the disintegration. -/
theorem iidPinnedReplayBound (D : S18.LateData hPT) (hD : D.Spec)
    (hReplay : S18.ReplayFacts D) (c : ℝ) (hTransfer : S18.TransferBound D c)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : D.prefixValid F.2)
    (pin : Option (S18.SlotPin D)) (pattern : ℕ → Finset (Pos T k)) :
    let X : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, pin.map (fun p => p.1), fun C => D.fresh.fallback C⟩
    (iidPinnedLaw D pin).E (fun x =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F x else 0) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) c) := by
  classical
  cases pin with
  | none => exact iidReplayBound D hD hReplay c hTransfer F hkind hvalid none pattern
  | some p =>
    let P := D.encoding.initialLaw D.encoding.iidLaw
    let A := Finset.univ.filter (S18.pinEvent D p)
    let X : S18.CriticalTransferData D :=
      ⟨F.2, hvalid, some p.1, fun C => D.fresh.fallback C⟩
    let f := fun x : D.encoding.InitInput =>
      if ∀ C ∈ X.criticalCells, D.fresh.typical C (x.1 C) then
        Lane_sol_s18_n4.forcedReplayRisk D X.criticalCells pattern F x else 0
    change (if h : 0 < ∑ x ∈ A, P.w x then FinLaw.cond P A h else P).E f ≤ _
    by_cases hA : 0 < ∑ x ∈ A, P.w x
    · rw [dif_pos hA, cond_expect_gated]
      apply (div_le_iff₀ hA).2
      have hmass : (∑ x ∈ A, P.w x) = P.pr (S18.pinEvent D p) := by
        simp only [A, FinLaw.pr, Finset.sum_filter]
      rw [hmass]
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
        iidReplayPinnedJointBound D hD hReplay c hTransfer F hkind hvalid p pattern
    · rw [dif_neg hA]
      exact iidReplayBound D hD hReplay c hTransfer F hkind hvalid (some p.1) pattern

theorem bind_first_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun x => A x.1) = P.pr A := by
  classical
  unfold FinLaw.pr
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : A a
  · simp only [if_pos ha, FinLaw.bind, ← Finset.mul_sum, Q.sum_one, mul_one]
  · simp only [if_neg ha, Finset.sum_const_zero]

theorem cond_bind_first {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (P : FinLaw α) (Q : FinLaw β)
    (A : α → Prop) (hA : 0 < ∑ a ∈ Finset.univ.filter A, P.w a)
    (hjoint : 0 < ∑ x ∈ Finset.univ.filter (fun x : α × β => A x.1),
      (FinLaw.bind P (fun _ => Q)).w x) :
    FinLaw.cond (FinLaw.bind P (fun _ => Q))
        (Finset.univ.filter (fun x => A x.1)) hjoint =
      FinLaw.bind (FinLaw.cond P (Finset.univ.filter A) hA) (fun _ => Q) := by
  classical
  have hmass : (∑ x ∈ Finset.univ.filter (fun x : α × β => A x.1),
      (FinLaw.bind P (fun _ => Q)).w x) = ∑ a ∈ Finset.univ.filter A, P.w a := by
    simpa only [FinLaw.pr, Finset.sum_filter] using bind_first_pr P Q A
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro x
  unfold FinLaw.cond
  simp only [hmass]
  simp only [FinLaw.bind, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : A x.1 <;> simp [ha, div_mul_eq_mul_div]

noncomputable def poolPinnedLaw (D : S18.LateData hPT)
    (P : FinLaw (∀ C, D.fresh.Pool C)) (pin : Option (S18.SlotPin D)) :
    FinLaw (∀ C, D.fresh.Pool C) :=
  match pin with
  | none => P
  | some p =>
    let A := Finset.univ.filter (fun pools => pools p.1 p.2.1 = p.2.2)
    if h : 0 < ∑ x ∈ A, P.w x then FinLaw.cond P A h else P

theorem initialPinnedLaw_eq (D : S18.LateData hPT) (pin : Option (S18.SlotPin D)) :
    Lane_sol_s18_n4.initialPinnedLaw D pin = D.encoding.initialLaw (poolPinnedLaw D D.encoding.poolLaw pin) := by
  classical
  cases pin with
  | none => rfl
  | some p =>
    let P := D.encoding.poolLaw
    let Q := tapeLaw D.fresh D.encoding.Ts
    let A := Finset.univ.filter (fun pools : ∀ C, D.fresh.Pool C => pools p.1 p.2.1 = p.2.2)
    let B := Finset.univ.filter (S18.pinEvent D p)
    have hm : (∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x) = ∑ pools ∈ A, P.w pools := by
      simp only [B, A, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro pools _
      by_cases hp : pools p.1 p.2.1 = p.2.2
      · simp only [S18.pinEvent, hp, if_true, FinLaw.bind, ← Finset.mul_sum, Q.sum_one, mul_one]
      · simp only [S18.pinEvent, hp, if_false, Finset.sum_const_zero]
    change (if h : 0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x then
        FinLaw.cond (FinLaw.bind P (fun _ => Q)) B h else FinLaw.bind P (fun _ => Q)) =
      FinLaw.bind (if h : 0 < ∑ x ∈ A, P.w x then FinLaw.cond P A h else P) (fun _ => Q)
    by_cases hA : 0 < ∑ x ∈ A, P.w x
    · have hB : 0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x := hm.symm ▸ hA
      rw [dif_pos hB, dif_pos hA]
      apply S16.Lane_q_s16_comp2.finLaw_ext
      intro x
      have hm' : (∑ x ∈ B, P.w x.1 * Q.w x.2) = ∑ pools ∈ A, P.w pools := hm
      simp only [FinLaw.cond, FinLaw.bind, hm']
      have hx : x ∈ B ↔ x.1 ∈ A := by simp [B, A, S18.pinEvent]
      by_cases ha : x.1 ∈ A <;> simp [hx, ha, div_mul_eq_mul_div]
    · have hB : ¬0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x := by rwa [hm]
      rw [dif_neg hB, dif_neg hA]

theorem iidPinnedLaw_eq (D : S18.LateData hPT) (pin : Option (S18.SlotPin D)) :
    iidPinnedLaw D pin = D.encoding.initialLaw (poolPinnedLaw D D.encoding.iidLaw pin) := by
  classical
  cases pin with
  | none => rfl
  | some p =>
    let P := D.encoding.iidLaw
    let Q := tapeLaw D.fresh D.encoding.Ts
    let A := Finset.univ.filter (fun pools : ∀ C, D.fresh.Pool C => pools p.1 p.2.1 = p.2.2)
    let B := Finset.univ.filter (S18.pinEvent D p)
    have hm : (∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x) = ∑ pools ∈ A, P.w pools := by
      simp only [B, A, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro pools _
      by_cases hp : pools p.1 p.2.1 = p.2.2
      · simp only [S18.pinEvent, hp, if_true, FinLaw.bind, ← Finset.mul_sum, Q.sum_one, mul_one]
      · simp only [S18.pinEvent, hp, if_false, Finset.sum_const_zero]
    change (if h : 0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x then
        FinLaw.cond (FinLaw.bind P (fun _ => Q)) B h else FinLaw.bind P (fun _ => Q)) =
      FinLaw.bind (if h : 0 < ∑ x ∈ A, P.w x then FinLaw.cond P A h else P) (fun _ => Q)
    by_cases hA : 0 < ∑ x ∈ A, P.w x
    · have hB : 0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x := hm.symm ▸ hA
      rw [dif_pos hB, dif_pos hA]
      apply S16.Lane_q_s16_comp2.finLaw_ext
      intro x
      have hm' : (∑ x ∈ B, P.w x.1 * Q.w x.2) = ∑ pools ∈ A, P.w pools := hm
      simp only [FinLaw.cond, FinLaw.bind, hm']
      have hx : x ∈ B ↔ x.1 ∈ A := by simp [B, A, S18.pinEvent]
      by_cases ha : x.1 ∈ A <;> simp [hx, ha, div_mul_eq_mul_div]
    · have hB : ¬0 < ∑ x ∈ B, (FinLaw.bind P (fun _ => Q)).w x := by rwa [hm]
      rw [dif_neg hB, dif_neg hA]

/-- The remaining comparison can be proved entirely on pool assignments;
the independent tapes have already been integrated in the local test. -/
theorem replayComparison_of_poolComparison (D : S18.LateData hPT)
    (pin : Option (S18.SlotPin D)) (f : D.encoding.InitInput → ℝ)
    (hcomp : (poolPinnedLaw D D.encoding.poolLaw pin).E
      (fun pools => (tapeLaw D.fresh D.encoding.Ts).E (fun tapes => f (pools, tapes))) ≤
        2 * (poolPinnedLaw D D.encoding.iidLaw pin).E
          (fun pools => (tapeLaw D.fresh D.encoding.Ts).E (fun tapes => f (pools, tapes)))) :
    (Lane_sol_s18_n4.initialPinnedLaw D pin).E f ≤ 2 * (iidPinnedLaw D pin).E f := by
  rw [initialPinnedLaw_eq, iidPinnedLaw_eq]
  simpa only [LateEncoding.initialLaw, S18.Lane_sol_s18_n5.bind_E] using hcomp

end HypercubeRamsey.Lane_sol_s18_3a_perm
