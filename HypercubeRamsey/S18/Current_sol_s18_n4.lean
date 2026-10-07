import HypercubeRamsey.S18.Tower_sol_s18_n4
import HypercubeRamsey.S18.Sampler_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

theorem testOrders_indexBound (b : Pos T k) :
    (D.testOrders b).length ≤ T.S.n k + 1 ∧
      ∀ order ∈ D.testOrders b, order.length ≤ T.S.n k + 1 := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := (Finset.univ : Finset (Fin (T.S.n k))) \ intern
  let base := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
    (if intern = ∅ then [] else [intern])
  have hicard : intern.card ≤ T.S.n k := by
    simpa using Finset.card_le_card (Finset.subset_univ intern)
  have hecard : extern.card = T.S.n k - intern.card := by
    simp [extern, Finset.card_sdiff]
  have hbase : base.length ≤ T.S.n k := by
    by_cases hi : intern = ∅
    · simp [base, hi, extern]
    · have hi0 : 0 < intern.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hi)
      have hb : base.length = extern.card + 1 := by simp [base, hi]
      omega
  constructor
  · change (base :: extern.toList.map _).length ≤ _
    simp only [List.length_cons, List.length_map, Finset.length_toList]
    omega
  · intro order horder
    change order ∈ base :: extern.toList.map _ at horder
    rcases List.mem_cons.mp horder with rfl | horder
    · omega
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp horder
      calc
        _ = (base.filter (fun B => B ≠ {a})).length + 1 := by
          change (base.filter (fun B => B ≠ {a}) ++ [{a}]).length = _
          rw [List.length_append, List.length_singleton]
        _ ≤ base.length + 1 := Nat.add_le_add_right (List.length_filter_le _ _) 1
        _ ≤ _ := Nat.add_le_add_right hbase 1

/-- The finite frozen prefix index includes every genuine Requirement-2 failure. -/
theorem R2_failure_hasIndex (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (side : D.encoding.base.RowOut b.1) (hbad : ¬ D.R2 j h side) :
    ∃ oi qi : Fin (T.S.n k + 1), ∃ a : Fin (T.S.n k),
      let f : S18.PrefixIndex D := ⟨j, b, oi, qi, a⟩
      D.prefixValid f ∧ ¬ D.prefixMoments j h side (D.prefixOrder f) qi.val a := by
  unfold S18.LateData.R2 at hbad
  push_neg at hbad
  obtain ⟨order, horder, q, hq, a, ha, hbad⟩ := hbad
  obtain ⟨i, hi, hio⟩ := List.mem_iff_getElem.mp horder
  obtain ⟨holen, hlen⟩ := testOrders_indexBound D b.1
  let oi : Fin (T.S.n k + 1) := ⟨i, hi.trans_le holen⟩
  let qi : Fin (T.S.n k + 1) := ⟨q, hq.trans_le (hlen order horder)⟩
  let f : S18.PrefixIndex D := ⟨j, b, oi, qi, a⟩
  have ho : D.prefixOrder f = order := by
    unfold S18.LateData.prefixOrder
    exact (List.getD_eq_getElem (D.testOrders b.1) [] hi).trans hio
  refine ⟨oi, qi, a, ?_⟩
  change D.prefixValid f ∧ ¬ D.prefixMoments j h side (D.prefixOrder f) q a
  rw [S18.LateData.prefixValid, ho]
  exact ⟨⟨hi, hq, ha⟩, hbad⟩

noncomputable def currentIndexedFailure (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (kind : Fin 3)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (oi qi : Fin (T.S.n k + 1)) (a : Fin (T.S.n k))
    (out : D.encoding.base.ClassRows j) : Prop :=
  let f : S18.PrefixIndex D := ⟨j, b, oi, qi, a⟩
  D.gate j b.1 h ∧
    (if kind.val = 0 then ¬ D.R1 j (out b) else if kind.val = 1 then
      D.prefixValid f ∧ D.gate j b.1 h ∧
        ¬ D.prefixMoments j h (out b) (D.prefixOrder f) qi.val a
    else D.R1 j (out b) ∧ D.R2 j h (out b) ∧ ¬ D.R3 j h (out b))

/-- Incoming future-risk bounds control each indexed bad event in the current
product class experiment through the actual conditional law. -/
theorem currentIndexedFailureBound (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (kind : Fin 3) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (oi qi : Fin (T.S.n k + 1)) (a : Fin (T.S.n k)) :
    (D.encoding.kernels.referenceTransition j h).pr
      (currentIndexedFailure D j h kind b oi qi a) ≤ D.threshold δ j.val := by
  let f : S18.LateEvent D := (kind, ⟨j, b, oi, qi, a⟩)
  have hevent : (fun full : D.encoding.base.History (Fin.last D.geom.r) =>
      D.agreesWithHistory h full ∧ S18.lateFailure D f full) =
      (fun full => D.agreesWithHistory h full ∧
        currentIndexedFailure D j h kind b oi qi a (D.pastRows full j j.isLt)) := by
    funext full
    apply propext
    by_cases hb : D.agreesWithHistory h full
    · have hh : D.beforeHistory full j.castSucc (Nat.le_of_lt j.isLt) = h := hb
      simp only [hb, true_and]
      simp only [S18.lateFailure, S18.LateData.prefixFailure, currentIndexedFailure, f, hh]
    · simp [hb]
  have hc := referenceConditionalClassTest D j h he.1
    (currentIndexedFailure D j h kind b oi qi a)
  have hr : D.futureRisk f h = (D.encoding.kernels.referenceTransition j h).pr
      (currentIndexedFailure D j h kind b oi qi a) := by
    unfold S18.LateData.futureRisk
    rw [hevent]
    exact hc
  rw [← hr]
  exact he.2.1 f le_rfl

theorem classCurrentBadBound (δ : ℝ) (hn : 0 < T.S.n k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    (D.encoding.kernels.referenceTransition j h).pr (classFailure D δ j h (.inl b)) ≤
      (3 * (T.S.n k + 1) ^ 2 * T.S.n k : ℕ) * D.threshold δ j.val := by
  let I := Fin 3 × Fin (T.S.n k + 1) × Fin (T.S.n k + 1) × Fin (T.S.n k)
  let A := fun i : I => currentIndexedFailure D j h i.1 b i.2.1 i.2.2.1 i.2.2.2
  have hcover : ∀ out, classFailure D δ j h (.inl b) out → ∃ i, A i out := by
    intro out hbad
    rcases hbad with ⟨hg, h1 | h2 | h3⟩
    · refine ⟨(0, 0, 0, ⟨0, hn⟩), ?_⟩
      simpa [A, currentIndexedFailure] using And.intro hg h1
    · obtain ⟨oi, qi, a, hv, hm⟩ := R2_failure_hasIndex D j h b (out b) h2
      refine ⟨(1, oi, qi, a), ?_⟩
      simpa [A, currentIndexedFailure] using And.intro hg (And.intro hv (And.intro hg hm))
    · refine ⟨(2, 0, 0, ⟨0, hn⟩), ?_⟩
      simpa [A, currentIndexedFailure] using And.intro hg h3
  have hunion : (D.encoding.kernels.referenceTransition j h).pr
      (classFailure D δ j h (.inl b)) ≤
      ∑ i : I, (D.encoding.kernels.referenceTransition j h).pr (A i) := by
    have hmono : (D.encoding.kernels.referenceTransition j h).pr
        (classFailure D δ j h (.inl b)) ≤
        (D.encoding.kernels.referenceTransition j h).pr (fun out => ∃ i, A i out) := by
      unfold FinLaw.pr
      apply Finset.sum_le_sum
      intro out hout
      by_cases hb : classFailure D δ j h (.inl b) out
      · simp [hb, hcover out hb]
      · by_cases hi : ∃ i, A i out <;> simp [hb, hi, FinLaw.nonneg]
    exact hmono.trans (Lane_q_s16_comp1.finlaw_union_le _ A)
  calc
    _ ≤ ∑ i : I, (D.encoding.kernels.referenceTransition j h).pr (A i) := hunion
    _ ≤ ∑ i : I, D.threshold δ j.val := by
      apply Finset.sum_le_sum
      intro i hi
      exact currentIndexedFailureBound D δ j h he i.1 b i.2.1 i.2.2.1 i.2.2.2
    _ = _ := by
      simp [I, Fintype.card_prod, mul_assoc, pow_two, Nat.cast_mul, Nat.cast_add]

theorem classFutureAlarmBound (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (f : S18.LateEvent D) :
    (D.encoding.kernels.referenceTransition j h).pr (classFailure D δ j h (.inr f)) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) δ / (2 * D.geom.r)) :=
  futureAlarmProbabilityBound D δ j h he f

theorem threshold_le_last (δ : ℝ) (q : ℕ) (hq : q ≤ D.geom.r) :
    D.threshold δ q ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) δ / 2) := by
  have hr : 0 < (D.geom.r : ℝ) := by exact_mod_cast D.l16_valid.r_pos
  have hqr : (q : ℝ) ≤ D.geom.r := by exact_mod_cast hq
  have hz : 0 ≤ Real.rpow (T.S.n k : ℝ) δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold S18.LateData.threshold
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hqr hz
  have hquot : (q : ℝ) * Real.rpow (T.S.n k : ℝ) δ / (2 * D.geom.r) ≤
      Real.rpow (T.S.n k : ℝ) δ / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D.geom.r)).2
    nlinarith
  linarith

theorem classCurrentBadUniformBound (δ : ℝ) (hn : 0 < T.S.n k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    (D.encoding.kernels.referenceTransition j h).pr (classFailure D δ j h (.inl b)) ≤
      (3 * (T.S.n k + 1) ^ 2 * T.S.n k : ℕ) *
        Real.exp (-Real.rpow (T.S.n k : ℝ) δ / 2) := by
  exact (classCurrentBadBound D δ hn j h he b).trans
    (mul_le_mul_of_nonneg_left (threshold_le_last D δ j.val j.isLt.le) (by positivity))

end HypercubeRamsey.Lane_sol_s18_n4
