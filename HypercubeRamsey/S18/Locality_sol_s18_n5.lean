import HypercubeRamsey.S18.Comparisons_sol_s18_n5
import HypercubeRamsey.S18.Sampler_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- A filtered current prior reads the initial direct cells and only the
labels of previously processed neighbors, even on invalid histories. -/
theorem currentPrior_local (D : LateData hPT) (hD : D.Spec) (j : Fin D.geom.r)
    (v : Pos T k) (h h' : D.encoding.base.History j.castSucc)
    (hcell : ∀ C ∈ D.directCells v, h.1 C = h'.1 C)
    (hrow : ∀ b : D.encoding.base.ProcessedRole j.castSucc,
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
      D.encoding.base.rowLabel (h.2 b) = D.encoding.base.rowLabel (h'.2 b)) :
    D.currentPrior j v h = D.currentPrior j v h' := by
  have hvalid := initialValid_local D hD v h.1 h'.1 hcell
  have hweight := hD.prior_local v h.1 h'.1 hcell
  have hprior : D.initialPrior v h.1 = D.initialPrior v h'.1 := by
    simp only [LateData.initialPrior, hvalid, hweight]
  have hfiltered : (fun x => (D.initialPrior v h.1).w x *
      ∏ b : D.encoding.base.ProcessedRole j.castSucc,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
        else 1) =
      (fun x => (D.initialPrior v h'.1).w x *
      ∏ b : D.encoding.base.ProcessedRole j.castSucc,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h'.2 b)) then 1 else 0)
        else 1) := by
    funext x
    rw [hprior]
    congr 1
    apply Finset.prod_congr rfl
    intro b _
    by_cases hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1
    · rw [hrow b hb]
    · simp [hb]
  unfold LateData.currentPrior LateData.priorAt
  simp only [hvalid, hfiltered]

noncomputable def rowInitialCells (D : LateData hPT) (b : Pos T k) : Finset D.geom.Cell :=
  Finset.univ.biUnion fun a : Fin (T.S.n k) => D.directCells (flipPos b a)

noncomputable def rowPredecessors (D : LateData hPT) (j : Fin D.geom.r) (b : Pos T k) :
    Finset (D.encoding.base.ProcessedRole j.castSucc) :=
  Finset.univ.filter fun u => ∃ a : Fin (T.S.n k),
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj (flipPos b a) u.1

theorem rowInitialCells_card (D : LateData hPT) (b : Pos T k) :
    (rowInitialCells D b).card ≤ T.S.n k * (T.S.n k + 1) := by
  calc
    (rowInitialCells D b).card ≤ ∑ a : Fin (T.S.n k), (D.directCells (flipPos b a)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin (T.S.n k), (T.S.n k + 1) := by
      apply Finset.sum_le_sum
      intro a _
      calc
        (D.directCells (flipPos b a)).card ≤ 1 + (D.externalEarly (flipPos b a)).card := by
          exact (Finset.card_union_le _ _).trans
            (by simp only [Finset.card_singleton]; exact Nat.add_le_add_left Finset.card_image_le 1)
        _ ≤ T.S.n k + 1 := by
          have hc : (D.externalEarly (flipPos b a)).card ≤ T.S.n k :=
            (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
          omega
    _ = T.S.n k * (T.S.n k + 1) := by simp

theorem referenceRow_weight_local (D : LateData hPT) (hD : D.Spec)
    (hT : TransitionData D) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h h' : D.encoding.base.History j.castSucc)
    (hcell : ∀ C ∈ rowInitialCells D b.1, h.1 C = h'.1 C)
    (hrow : ∀ u ∈ rowPredecessors D j b.1,
      D.encoding.base.rowLabel (h.2 u) = D.encoding.base.rowLabel (h'.2 u))
    (out : D.encoding.base.RowOut b.1) :
    (D.encoding.kernels.refK j b h).w out = (D.encoding.kernels.refK j b h').w out := by
  rw [hT.reference_formula, hT.reference_formula]
  have hp : ∀ a : Fin (T.S.n k),
      D.currentPrior j (flipPos b.1 a) h = D.currentPrior j (flipPos b.1 a) h' := by
    intro a
    apply currentPrior_local D hD
    · intro C hC
      exact hcell C (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hC⟩)
    · intro u hu
      exact hrow u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, hu⟩)
  simp only [hp]

theorem referenceRow_label_local (D : LateData hPT) (hD : D.Spec)
    (hT : TransitionData D) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h h' : D.encoding.base.History j.castSucc)
    (hcell : ∀ C ∈ rowInitialCells D b.1, h.1 C = h'.1 C)
    (hrow : ∀ u ∈ rowPredecessors D j b.1,
      D.encoding.base.rowLabel (h.2 u) = D.encoding.base.rowLabel (h'.2 u))
    (y : Fin (T.S.N k)) :
    (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y) =
      (D.encoding.kernels.refK j b h').pr (fun out => D.encoding.base.rowLabel out = y) := by
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro out _
  rw [referenceRow_weight_local D hD hT j b h h' hcell hrow out]

theorem referenceRow_label_cap (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (y : Fin (T.S.N k)) :
    (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y) ≤
      2 / ((D.encoding.base.latePool j).card : ℝ) *
        Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) := by
  classical
  let cap : ℝ := 2 / ((D.encoding.base.latePool j).card : ℝ) *
    Real.exp ((κ.α / 100) * (T.S.n k : ℝ))
  let sketchLaw := FinLaw.pi fun a : Fin (T.S.n k) =>
    FinLaw.pi fun _t : Fin (sketchLength T k) =>
      (⟨(D.currentPrior j (flipPos b.1 a) h).w,
        (D.currentPrior j (flipPos b.1 a) h).nonneg,
        (D.currentPrior j (flipPos b.1 a) h).sum_eq_one⟩ : FinLaw (Fin (T.S.N k)))
  have hlabel (mask : D.encoding.base.AllowedMask b.1)
      (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :
      (∑ label : {z : Fin (T.S.N k) // z ∈ D.encoding.base.latePoolOf b.1},
        if label.1 = y then (D.encoding.kernels.refK j b h).w (mask, sketch, label) else 0) ≤
      (D.encoding.kernels.maskProfile b.1).w mask * sketchLaw.w sketch * cap := by
    by_cases hy : y ∈ D.encoding.base.latePoolOf b.1
    · let label : {z : Fin (T.S.N k) // z ∈ D.encoding.base.latePoolOf b.1} := ⟨y, hy⟩
      have hsum : (∑ z : {z : Fin (T.S.N k) // z ∈ D.encoding.base.latePoolOf b.1},
          if z.1 = y then (D.encoding.kernels.refK j b h).w (mask, sketch, z) else 0) =
          (D.encoding.kernels.refK j b h).w (mask, sketch, label) := by
        calc
          _ = (if label.1 = y then (D.encoding.kernels.refK j b h).w (mask, sketch, label) else 0) := by
            apply Finset.sum_eq_single label
            · intro z _ hz
              have hzy : z.1 ≠ y := by
                intro heq
                exact hz (Subtype.ext heq)
              simp [hzy]
            · simp
          _ = _ := by simp [label]
      rw [hsum, hT.reference_formula]
      exact mul_le_mul_of_nonneg_left
        (HypercubeRamsey.Lane_sol_s18_n4.labelWeightCap D j b (mask, sketch, label) _ y)
        (mul_nonneg ((D.encoding.kernels.maskProfile b.1).nonneg mask) (sketchLaw.nonneg sketch))
    · have hnone : ∀ z : {z : Fin (T.S.N k) // z ∈ D.encoding.base.latePoolOf b.1}, z.1 ≠ y := by
        intro z heq
        exact hy (heq ▸ z.2)
      simp only [hnone, if_false, Finset.sum_const_zero]
      exact mul_nonneg
        (mul_nonneg ((D.encoding.kernels.maskProfile b.1).nonneg mask) (sketchLaw.nonneg sketch))
        (by dsimp [cap]; positivity)
  have hprSum : (D.encoding.kernels.refK j b h).pr
      (fun out => D.encoding.base.rowLabel out = y) =
      (∑ mask, ∑ sketch, ∑ label : {z : Fin (T.S.N k) // z ∈ D.encoding.base.latePoolOf b.1},
        if label.1 = y then (D.encoding.kernels.refK j b h).w (mask, sketch, label) else 0) := by
    unfold FinLaw.pr
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro mask _
    apply Finset.sum_congr rfl
    intro sketch _
    apply Finset.sum_congr rfl
    intro label _
    by_cases hl : label.1 = y <;> simp [LateProcessBase.rowLabel, hl]
  rw [hprSum]
  calc
    _ ≤ ∑ mask, ∑ sketch, (D.encoding.kernels.maskProfile b.1).w mask * sketchLaw.w sketch * cap :=
      Finset.sum_le_sum fun mask _ => Finset.sum_le_sum fun sketch _ => hlabel mask sketch
    _ = cap := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sketchLaw.sum_one, mul_one]
      rw [(D.encoding.kernels.maskProfile b.1).sum_one, one_mul]

theorem columnSum_cap (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) (y : Fin (T.S.N k)) :
    D.columnSum j h y ≤ (D.encoding.base.classes j).card *
      (2 / ((D.encoding.base.latePool j).card : ℝ) *
        Real.exp ((κ.α / 100) * (T.S.n k : ℝ))) := by
  unfold LateData.columnSum
  calc
    _ ≤ ∑ _b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      (2 / ((D.encoding.base.latePool j).card : ℝ) *
        Real.exp ((κ.α / 100) * (T.S.n k : ℝ))) :=
      Finset.sum_le_sum fun b _ => referenceRow_label_cap D hT j b h y
    _ = _ := by simp [Fintype.card_coe]

private theorem flip_twice (v : Pos T k) (a : Fin (T.S.n k)) :
    flipPos (flipPos v a) a = v := by
  funext t
  by_cases ht : t = a
  · subst t; simp [flipPos]
  · simp [flipPos, ht]

/-- The one-neighbor-per-class property bounds each class even without a
surjectivity hypothesis on the syndrome map. -/
theorem class_card_times_dimension (D : LateData hPT) (j : Fin D.geom.r) :
    (D.encoding.base.classes j).card * T.S.n k ≤ 2 ^ T.S.n k := by
  let f : {b : Pos T k // b ∈ D.encoding.base.classes j} × Fin (T.S.n k) → Pos T k :=
    fun p => flipPos p.1.1 p.2
  have hf : Function.Injective f := by
    intro p q hpq
    have hp : D.geom.classOf (flipPos (f p) p.2) = some j := by
      simpa only [f, flip_twice] using (D.encoding.base.class_of_spec p.1.1 j).mp p.1.2
    have hq : D.geom.classOf (flipPos (f p) q.2) = some j := by
      rw [hpq]
      simpa only [f, flip_twice] using (D.encoding.base.class_of_spec q.1.1 j).mp q.1.2
    have ha := D.l16_valid.one_per_class (f p) j p.2 q.2 hp hq
    have hb : p.1.1 = q.1.1 := by
      have he := congrArg (fun v => flipPos v p.2) hpq
      simpa only [f, ← ha, flip_twice] using he
    exact Prod.ext (Subtype.ext hb) ha
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    Pos, CubePos, Fintype.card_fun, Fintype.card_bool] using hc

end HypercubeRamsey.S18.Lane_sol_s18_n5
