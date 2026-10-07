import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_sol_s18_n1_caps
open Classical
open scoped BigOperators
open S18
set_option backward.isDefEq.respectTransparency false
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

noncomputable def rawWeight (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (x : Fin (T.S.N k)) : ℝ :=
  (D.initialPrior v h.1).w x * ∏ b : D.encoding.base.ProcessedRole t,
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
    else 1

theorem rawWeight_nonneg (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (x : Fin (T.S.N k)) :
    0 ≤ rawWeight D h v x := by
  apply mul_nonneg ((D.initialPrior v h.1).nonneg x)
  apply Finset.prod_nonneg
  intro b _
  split_ifs <;> norm_num

noncomputable def rowHit (D : LateData hPT) (v : Pos T k)
    {b : Pos T k} (out : D.encoding.base.RowOut b) (x : Fin (T.S.N k)) : ℝ :=
  if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b then
    (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel out) then 1 else 0)
  else 1

private noncomputable def historyHit (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (b : Pos T k) (x : Fin (T.S.N k)) : ℝ :=
  if hb : b ∈ D.encoding.base.processed t then rowHit D v (h.2 ⟨b,hb⟩) x else 1

private theorem rawWeight_finset (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (x : Fin (T.S.N k)) :
    rawWeight D h v x = (D.initialPrior v h.1).w x *
      ∏ b ∈ D.encoding.base.processed t, historyHit D h v b x := by
  unfold rawWeight
  congr 1
  rw [Finset.prod_subtype (D.encoding.base.processed t) (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro b _
  simp only [historyHit, dif_pos b.2, rowHit]

/-- Exact product decomposition across one class, including the full side data. -/
theorem rawWeight_step (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (v : Pos T k) (x : Fin (T.S.N k)) :
    rawWeight D (D.encoding.base.extend j h out) v x = rawWeight D h v x *
      ∏ b : {b : Pos T k // b ∈ D.encoding.base.classes j}, rowHit D v (out b) x := by
  rw [rawWeight_finset, rawWeight_finset]
  have hdis := (D.encoding.base.class_fresh j).symm
  have hunion := congrArg (fun S : Finset (Pos T k) =>
      ∏ b ∈ S, historyHit D (D.encoding.base.extend j h out) v b x)
    (D.encoding.base.processed_step j).symm
  rw [Finset.prod_union hdis] at hunion
  rw [hunion, Finset.prod_subtype (D.encoding.base.classes j) (fun _ => Iff.rfl)]
  have hpast : (∏ b ∈ D.encoding.base.processed j.castSucc,
      historyHit D (D.encoding.base.extend j h out) v b x) =
        ∏ b ∈ D.encoding.base.processed j.castSucc, historyHit D h v b x := by
    apply Finset.prod_congr rfl
    intro b hb
    have hb' : b ∈ D.encoding.base.processed j.succ := by
      rw [← D.encoding.base.processed_step j]
      exact Finset.mem_union_left _ hb
    simp only [historyHit, dif_pos hb', dif_pos hb, LateProcessBase.extend]
  have hnew : (∏ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      historyHit D (D.encoding.base.extend j h out) v b.1 x) =
        ∏ b : {b : Pos T k // b ∈ D.encoding.base.classes j}, rowHit D v (out b) x := by
    apply Finset.prod_congr rfl
    intro b _
    have hb' : b.1 ∈ D.encoding.base.processed j.succ := by
      rw [← D.encoding.base.processed_step j]
      exact Finset.mem_union_right _ b.2
    have hnot : b.1 ∉ D.encoding.base.processed j.castSucc :=
      fun hb => Finset.disjoint_left.mp (D.encoding.base.class_fresh j) b.2 hb
    simp only [historyHit, dif_pos hb', LateProcessBase.extend, dif_neg hnot]
  rw [hpast, hnew]
  simp only [LateProcessBase.extend, mul_assoc]

/-- A positive cumulative weight has the intended probability normalization. -/
theorem priorAt_weight (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (hv : D.initialValid v h.1)
    (hmass : 0 < ∑ x, rawWeight D h v x) (x : Fin (T.S.N k)) :
    (D.priorAt t v h).w x = rawWeight D h v x / ∑ y, rawWeight D h v y := by
  simp only [LateData.priorAt, if_pos hv]
  change (D.normalize (rawWeight D h v)).w x = _
  have hbranch : (∀ x, 0 ≤ rawWeight D h v x) ∧ 0 < ∑ x, rawWeight D h v x :=
    ⟨rawWeight_nonneg D h v, hmass⟩
  simp only [LateData.normalize, dif_pos hbranch]


private theorem adjacent_flip {n : ℕ} (v w : CubePos n)
    (h : (OAI.HypercubeRamsey.cube n).Adj v w) : ∃ a, w = flipPos v a := by
  let S := Finset.univ.filter fun a : Fin n => v a ≠ w a
  have hcard : S.card = 1 := h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b
    have hne : v a ≠ w a := (Finset.mem_filter.mp (show a ∈ S by rw [ha]; simp)).2
    cases hv : v a <;> cases hw : w a <;> simp_all [flipPos]
  · have heq : v b = w b := by
      by_contra hne
      have hm : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [ha] at hm
      exact hb (Finset.mem_singleton.mp hm)
    simp [flipPos, hb, heq]

theorem one_adjacent_per_class (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r)
    (b b' : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1)
    (hb' : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b'.1) : b = b' := by
  obtain ⟨a, ha⟩ := adjacent_flip v b.1 hb
  obtain ⟨a', ha'⟩ := adjacent_flip v b'.1 hb'
  have hclass := (D.encoding.base.class_of_spec b.1 j).mp b.2
  have hclass' := (D.encoding.base.class_of_spec b'.1 j).mp b'.2
  rw [ha] at hclass
  rw [ha'] at hclass'
  have he := D.l16_valid.one_per_class v j a a' hclass hclass'
  apply Subtype.ext
  rw [ha, ha', he]

/-- The new class contributes precisely one hit indicator when it has a neighbour. -/
theorem class_hit_factor (D : LateData hPT) (j : Fin D.geom.r)
    (out : D.encoding.base.ClassRows j) (v : Pos T k) (x : Fin (T.S.N k))
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    (∏ c, rowHit D v (out c) x) =
      if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (out b)) then 1 else 0 := by
  rw [Fintype.prod_eq_single b]
  · simp only [rowHit, if_pos hb]
  · intro c hc
    have hnot : ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v c.1 :=
      fun hh => hc (one_adjacent_per_class D v j c b hh hb)
    simp [rowHit, hnot]

/-- Reconstruct a prefix from its previous history and actual class outputs. -/
theorem beforeHistory_step (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (j : Fin D.geom.r) (hj : j.val < t.val) :
    D.beforeHistory h j.succ (Nat.succ_le_of_lt hj) =
      D.encoding.base.extend j (D.beforeHistory h j.castSucc (Nat.le_of_lt hj))
        (D.pastRows h j hj) := by
  apply Prod.ext
  · rfl
  · funext b
    dsimp [LateData.beforeHistory, LateProcessBase.extend, LateData.pastRows]
    split_ifs <;> rfl

/-- Exact survival-mass identity for the one new neighbouring hit. -/
theorem rawMass_step_hit (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (v : Pos T k) (hv : D.initialValid v h.1)
    (hmass : 0 < ∑ x, rawWeight D h v x)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    (∑ x, rawWeight D (D.encoding.base.extend j h out) v x) =
      (∑ x, rawWeight D h v x) *
        colDeg (T.S.E k) PT.tiling.c (D.currentPrior j v h) (D.encoding.base.rowLabel (out b)) := by
  simp_rw [rawWeight_step, class_hit_factor D j out v _ b hb]
  unfold colDeg
  simp_rw [LateData.currentPrior, priorAt_weight D h v hv hmass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hhit : Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (out b))
  · simp only [if_pos hhit, mul_one]
    field_simp [hmass.ne']
  · simp [hhit]


noncomputable def pastAxes (D : LateData hPT) (v : Pos T k) (m : ℕ) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => ∃ s : Fin D.geom.r, s.val < m ∧ D.geom.classOf (flipPos v a) = some s

private theorem flip_adj {n : ℕ} (v : CubePos n) (a : Fin n) :
    (OAI.HypercubeRamsey.cube n).Adj v (flipPos v a) := by
  change (Finset.univ.filter fun b : Fin n => v b ≠ flipPos v a b).card = 1
  have he : (Finset.univ.filter fun b : Fin n => v b ≠ flipPos v a b) = {a} := by
    ext b
    by_cases hb : b = a
    · subst b
      cases hv : v a <;> simp [flipPos, hv]
    · simp [flipPos, hb]
  rw [he]
  simp

private theorem pastAxes_step (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    pastAxes D v (j.val+1) = pastAxes D v j.val ∪
      (Finset.univ.filter fun a => D.geom.classOf (flipPos v a) = some j) := by
  ext a
  simp only [pastAxes, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s,hs,hc⟩
    by_cases hsj : s.val < j.val
    · exact Or.inl ⟨s,hsj,hc⟩
    · have he : s = j := Fin.ext (by omega)
      exact Or.inr (he ▸ hc)
  · rintro (⟨s,hs,hc⟩ | hc)
    · exact ⟨s,by omega,hc⟩
    · exact ⟨j,by omega,hc⟩

private theorem pastAxes_count_hit (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    (pastAxes D v (j.val+1)).card = (pastAxes D v j.val).card + 1 := by
  obtain ⟨a,ha⟩ := adjacent_flip v b.1 hb
  have hc : D.geom.classOf (flipPos v a) = some j := by
    rw [← ha]
    exact (D.encoding.base.class_of_spec b.1 j).mp b.2
  have hset : (Finset.univ.filter fun a' => D.geom.classOf (flipPos v a') = some j) = {a} := by
    ext a'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hc'
      exact D.l16_valid.one_per_class v j a' a hc' hc
    · rintro rfl
      exact hc
  have hnot : a ∉ pastAxes D v j.val := by
    simp only [pastAxes, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨s,hs,hc'⟩
    have he : s = j := Option.some.inj (hc'.symm.trans hc)
    subst s
    omega
  rw [pastAxes_step, hset, Finset.union_singleton, Finset.card_insert_of_notMem hnot]

private theorem pastAxes_count_nohit (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r)
    (hno : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    pastAxes D v (j.val+1) = pastAxes D v j.val := by
  rw [pastAxes_step]
  have hset : (Finset.univ.filter fun a => D.geom.classOf (flipPos v a) = some j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hc := (Finset.mem_filter.mp ha).2
    exact hno ⟨flipPos v a, (D.encoding.base.class_of_spec _ j).mpr hc⟩ (flip_adj v a)
  rw [hset, Finset.union_empty]

private theorem rawMass_step_nohit (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (v : Pos T k)
    (hno : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    rawWeight D (D.encoding.base.extend j h out) v = rawWeight D h v := by
  funext x
  rw [rawWeight_step]
  have he : (∏ b, rowHit D v (out b) x) = 1 := by
    apply Finset.prod_eq_one
    intro b _
    simp [rowHit, hno b]
  rw [he, mul_one]

noncomputable def errorBefore (D : LateData hPT) (v : Pos T k) (m : ℕ) : ℝ :=
  ∑ s : Fin D.geom.r, if s.val < m then D.error v s else 0

private theorem errorBefore_step (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    errorBefore D v (j.val+1) = errorBefore D v j.val + D.error v j := by
  have he (s : Fin D.geom.r) :
      (if s.val < j.val+1 then D.error v s else 0) =
      (if s.val < j.val then D.error v s else 0) + (if s = j then D.error v s else 0) := by
    by_cases hs : s.val < j.val
    · have hs' : s.val < j.val+1 := by omega
      have hne : s ≠ j := fun hh => by subst s; omega
      simp [hs,hs',hne]
    · by_cases hsj : s = j
      · subst s
        simp
      · have hs' : ¬ s.val < j.val+1 := by
          have hne : s.val ≠ j.val := fun hh => hsj (Fin.ext hh)
          omega
        simp [hs,hs',hsj]
  unfold errorBefore
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

private theorem survival_factor (e : ℝ) (he0 : 0 ≤ e) (he12 : e ≤ 1/12) :
    1 ≤ (1/2 - 3*e) * (2 * Real.exp (12*e)) := by
  have hd : 0 ≤ 1-6*e := by linarith
  have hp := mul_nonneg he0 (show 0 ≤ 1-12*e by linarith)
  have he := Real.add_one_le_exp (12*e)
  have hh := mul_le_mul_of_nonneg_left he hd
  nlinarith

noncomputable def budget (D : LateData hPT) (v : Pos T k) (m : ℕ) : ℝ :=
  (2:ℝ) ^ (pastAxes D v m).card * Real.exp (12 * errorBefore D v m)

private theorem budget_pos (D : LateData hPT) (v : Pos T k) (m : ℕ) : 0 < budget D v m := by
  unfold budget
  positivity

private theorem budget_step_hit (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    budget D v (j.val+1) = budget D v j.val * (2 * Real.exp (12 * D.error v j)) := by
  unfold budget
  rw [pastAxes_count_hit D v j b hb, errorBefore_step, pow_succ]
  rw [mul_add, Real.exp_add]
  ring

private theorem budget_step_nohit (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r)
    (hno : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) :
    budget D v (j.val+1) = budget D v j.val * Real.exp (12 * D.error v j) := by
  unfold budget
  rw [pastAxes_count_nohit D v j hno, errorBefore_step, mul_add, Real.exp_add]
  ring


/-- Positive normalizers and the exact number of imposed neighbouring hits. -/
theorem prefix_mass_bound (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (hv : D.initialValid v h.1)
    (he0 : ∀ s, 0 ≤ D.error v s) (he12 : ∀ s, D.error v s ≤ 1/12)
    (htrue : ∀ (s : Fin D.geom.r) (hs : s.val < t.val)
      (b : {b : Pos T k // b ∈ D.encoding.base.classes s}),
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
      1/2 - 3 * D.error v s ≤
        colDeg (T.S.E k) PT.tiling.c
          (D.currentPrior s v (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)))
          (D.encoding.base.rowLabel (D.pastRows h s hs b))) :
    ∀ m (hm : m ≤ t.val),
      let pre := D.beforeHistory h ⟨m, by omega⟩ hm
      (0 < ∑ x, rawWeight D pre v x) ∧
        1 ≤ (∑ x, rawWeight D pre v x) * budget D v m := by
  intro m
  induction m with
  | zero =>
    intro hm
    have hz (x : Fin (T.S.N k)) :
        rawWeight D (D.beforeHistory h ⟨0,by omega⟩ hm) v x = (D.initialPrior v h.1).w x := by
      rw [rawWeight_finset]
      simp [LateData.beforeHistory, D.encoding.base.processed_zero]
    have hb : budget D v 0 = 1 := by simp [budget,pastAxes,errorBefore]
    simp only [hz, (D.initialPrior v h.1).sum_eq_one, hb, mul_one]
    constructor <;> norm_num
  | succ m ih =>
    intro hm
    obtain ⟨hpos,hbound⟩ := ih (Nat.le_of_succ_le hm)
    let s : Fin D.geom.r := ⟨m,by omega⟩
    have hs : s.val < t.val := by dsimp [s]; omega
    let pre := D.beforeHistory h s.castSucc (Nat.le_of_lt hs)
    let out := D.pastRows h s hs
    change 0 < ∑ x, rawWeight D pre v x at hpos
    change 1 ≤ (∑ x, rawWeight D pre v x) * budget D v s.val at hbound
    have hprevalid : D.initialValid v pre.1 := hv
    have hrepr := beforeHistory_step D h s hs
    change 0 < ∑ x, rawWeight D (D.beforeHistory h s.succ (Nat.succ_le_of_lt hs)) v x ∧
      1 ≤ (∑ x, rawWeight D (D.beforeHistory h s.succ (Nat.succ_le_of_lt hs)) v x) * budget D v (s.val+1)
    rw [hrepr]
    by_cases hex : ∃ b : {b : Pos T k // b ∈ D.encoding.base.classes s},
        (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1
    · obtain ⟨b,hb⟩ := hex
      have hmass := rawMass_step_hit D s pre out v hprevalid hpos b hb
      have hd := htrue s hs b hb
      have hdpos : 0 < colDeg (T.S.E k) PT.tiling.c (D.currentPrior s v pre)
          (D.encoding.base.rowLabel (out b)) := by
        have he := he12 s
        change 1/2 - 3 * D.error v s ≤ _ at hd
        linarith
      have hc : 0 ≤ 2 * Real.exp (12 * D.error v s) := by positivity
      have hloss : 1 ≤ colDeg (T.S.E k) PT.tiling.c (D.currentPrior s v pre)
          (D.encoding.base.rowLabel (out b)) * (2 * Real.exp (12 * D.error v s)) :=
        (survival_factor _ (he0 s) (he12 s)).trans (mul_le_mul_of_nonneg_right hd hc)
      refine ⟨?_, ?_⟩
      · rw [hmass]
        exact mul_pos hpos hdpos
      · calc
          1 ≤ (∑ x, rawWeight D pre v x) * budget D v s.val := hbound
          _ ≤ ((∑ x, rawWeight D pre v x) * budget D v s.val) *
                (colDeg (T.S.E k) PT.tiling.c (D.currentPrior s v pre)
                  (D.encoding.base.rowLabel (out b)) * (2 * Real.exp (12 * D.error v s))) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hloss
              (mul_nonneg hpos.le (budget_pos D v s.val).le)
          _ = (∑ x, rawWeight D (D.encoding.base.extend s pre out) v x) * budget D v (s.val+1) := by
            rw [hmass, budget_step_hit D v s b hb]
            ring
    · have hno : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes s},
          ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 := by
        simpa only [not_exists] using hex
      rw [rawMass_step_nohit D s pre out v hno, budget_step_nohit D v s hno]
      refine ⟨hpos, ?_⟩
      have hexp : 1 ≤ Real.exp (12 * D.error v s) := Real.one_le_exp_iff.mpr (by nlinarith [he0 s])
      calc
        1 ≤ (∑ x, rawWeight D pre v x) * budget D v s.val := hbound
        _ ≤ ((∑ x, rawWeight D pre v x) * budget D v s.val) * Real.exp (12 * D.error v s) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
            (mul_nonneg hpos.le (budget_pos D v s.val).le)
        _ = (∑ x, rawWeight D pre v x) * (budget D v s.val * Real.exp (12 * D.error v s)) := by ring

private theorem beforeHistory_self (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) : D.beforeHistory h t le_rfl = h := by
  apply Prod.ext
  · rfl
  · funext b
    rfl

private theorem rawWeight_le (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (x : Fin (T.S.N k)) :
    rawWeight D h v x ≤ (D.initialPrior v h.1).w x := by
  unfold rawWeight
  apply mul_le_of_le_one_right ((D.initialPrior v h.1).nonneg x)
  apply Finset.prod_le_one₀
  · intro b _
    split_ifs <;> norm_num
  · intro b _
    split_ifs <;> norm_num

theorem posterior_cap (D : LateData hPT) {t : Fin (D.geom.r+1)}
    (h : D.encoding.base.History t) (v : Pos T k) (hv : D.initialValid v h.1)
    (he0 : ∀ s, 0 ≤ D.error v s) (he12 : ∀ s, D.error v s ≤ 1/12)
    (htrue : ∀ (s : Fin D.geom.r) (hs : s.val < t.val)
      (b : {b : Pos T k // b ∈ D.encoding.base.classes s}),
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
      1/2 - 3 * D.error v s ≤
        colDeg (T.S.E k) PT.tiling.c
          (D.currentPrior s v (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)))
          (D.encoding.base.rowLabel (D.pastRows h s hs b))) :
    (0 < ∑ x, rawWeight D h v x) ∧
      ∀ x, (D.priorAt t v h).w x ≤ (D.initialPrior v h.1).w x * budget D v t.val := by
  obtain ⟨hpos,hbound⟩ := prefix_mass_bound D h v hv he0 he12 htrue t.val le_rfl
  have ht : (⟨t.val,by omega⟩ : Fin (D.geom.r+1)) = t := Fin.ext rfl
  simp only [ht, beforeHistory_self] at hpos hbound
  refine ⟨hpos, ?_⟩
  intro x
  rw [priorAt_weight D h v hv hpos]
  apply (div_le_iff₀ hpos).mpr
  calc
    rawWeight D h v x ≤ (D.initialPrior v h.1).w x := rawWeight_le D h v x
    _ ≤ (D.initialPrior v h.1).w x * ((∑ y, rawWeight D h v y) * budget D v t.val) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbound ((D.initialPrior v h.1).nonneg x)
    _ = ((D.initialPrior v h.1).w x * budget D v t.val) * ∑ y, rawWeight D h v y := by ring


private theorem error_pos (D : LateData hPT) (v : Pos T k) (s : Fin D.geom.r) : 0 < D.error v s := by
  have hscale : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold LateData.error lateError
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hscale _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)

private theorem errors_small (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) (v : Pos T k) :
    (∑ s, D.error v s) ≤ Real.log 2 / 1000 ∧ ∀ s, D.error v s ≤ 1/12 := by
  have hsum0 : 0 ≤ ∑ s, D.error v s := Finset.sum_nonneg fun s _ => (error_pos D v s).le
  have hsmall' := hsmall (D.geom.patchOf v)
  change (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * (∑ s, D.error v s) ≤ Real.log 2 / 1000 at hsmall'
  have hmax : (1:ℝ) ≤ max (1:ℝ) ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) := le_max_left _ _
  have hsum : (∑ s, D.error v s) ≤ Real.log 2 / 1000 := by nlinarith
  refine ⟨hsum, ?_⟩
  intro s
  have hsingle := Finset.single_le_sum (fun s _ => (error_pos D v s).le) (Finset.mem_univ s)
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    exact hh
  linarith

private theorem budget_le (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) (v : Pos T k) (m : ℕ) :
    budget D v m ≤ 2 * (2:ℝ) ^ (pastAxes D v m).card := by
  have hbefore : errorBefore D v m ≤ ∑ s, D.error v s := by
    apply Finset.sum_le_sum
    intro s _
    split_ifs
    · rfl
    · exact (error_pos D v s).le
  have hsum := (errors_small D hsmall v).1
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexp : Real.exp (12 * errorBefore D v m) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_le_exp]
    linarith
  unfold budget
  calc
    _ ≤ (2:ℝ) ^ (pastAxes D v m).card * 2 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

private theorem neighbor_count_partition (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    (pastAxes D v j.val).card + D.remainingNeighbors v j =
      D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ := by
  let rem := Finset.univ.filter fun a : Fin (T.S.n k) =>
    ∃ s : Fin D.geom.r, j.val ≤ s.val ∧ D.geom.classOf (flipPos v a) = some s
  let all := Finset.univ.filter fun a : Fin (T.S.n k) =>
    ∃ s : Fin D.geom.r, D.geom.classOf (flipPos v a) = some s
  have hdis : Disjoint (pastAxes D v j.val) rem := by
    apply Finset.disjoint_left.mpr
    intro a ha hr
    obtain ⟨s,hs,hc⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨s',hs',hc'⟩ := (Finset.mem_filter.mp hr).2
    have he : s = s' := Option.some.inj (hc.symm.trans hc')
    subst s'
    omega
  have hunion : pastAxes D v j.val ∪ rem = all := by
    ext a
    simp only [pastAxes,rem,all,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨s,hs,hc⟩ | ⟨s,hs,hc⟩) <;> exact ⟨s,hc⟩
    · rintro ⟨s,hc⟩
      by_cases hs : s.val < j.val
      · exact Or.inl ⟨s,hs,hc⟩
      · exact Or.inr ⟨s,by omega,hc⟩
  have hc := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdis] at hc
  simpa only [LateData.remainingNeighbors, rem, all, Fin.val_zero, Nat.zero_le, true_and] using hc

private theorem class_odd (D : LateData hPT) (j : Fin D.geom.r) (b : Pos T k)
    (hb : b ∈ D.encoding.base.classes j) : ¬ IsEvenRole b := by
  have hc := (D.encoding.base.class_of_spec b j).mp hb
  unfold LowGeom.classOf at hc
  split_ifs at hc with hx
  · exact hx.1

private theorem gate_true_hits (D : LateData hPT) (j : Fin D.geom.r)
    (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hg : D.gate j b h) (a : Fin (T.S.n k)) :
    ∀ (s : Fin D.geom.r) (hs : s.val < j.val)
      (b' : {b' : Pos T k // b' ∈ D.encoding.base.classes s}),
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj (flipPos b a) b'.1 →
      1/2 - 3 * D.error (flipPos b a) s ≤
        colDeg (T.S.E k) PT.tiling.c
          (D.currentPrior s (flipPos b a) (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)))
          (D.encoding.base.rowLabel (D.pastRows h s hs b')) := by
  intro s hs b' hadj
  have h₁ : _root_.hammingDist b (flipPos b a) = 1 := by
    simpa [OAI.HypercubeRamsey.cube] using flip_adj b a
  have h₂ : _root_.hammingDist (flipPos b a) b'.1 = 1 := by
    simpa [OAI.HypercubeRamsey.cube] using hadj
  have hdist := _root_.hammingDist_triangle b (flipPos b a) b'.1
  have hball : b'.1 ∈ cubeBall b (6 * D.geom.r) := by
    simp only [cubeBall,Finset.mem_filter,Finset.mem_univ,true_and]
    have hr := D.l16_valid.r_pos
    omega
  obtain ⟨a',ha'⟩ := adjacent_flip b'.1 (flipPos b a)
    ((OAI.HypercubeRamsey.cube (T.S.n k)).adj_comm _ _ |>.mp hadj)
  have htrue := (hg.2 s hs b' hball).1 a'
  rw [← ha'] at htrue
  exact htrue

/-- Gated conditioning propagates the initial atom cap with at most a factor two loss. -/
theorem gated_current_cap (D : LateData hPT) (hD : D.Spec)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) : CurrentListCapFacts D := by
  intro j b h hg hb a x
  let v := flipPos b a
  have heven : IsEvenRole v := by
    exact (cubeFlip_parity b a).mpr (class_odd D j b hb)
  have hdist : _root_.hammingDist b v = 1 := by
    simpa [OAI.HypercubeRamsey.cube, v] using flip_adj b a
  have hvball : v ∈ cubeBall b (6 * D.geom.r) := by
    simp only [cubeBall,Finset.mem_filter,Finset.mem_univ,true_and]
    have hr := D.l16_valid.r_pos
    omega
  have hv : D.initialValid v h.1 := hg.1 v hvball heven
  have hcap := (posterior_cap D h v hv (fun s => (error_pos D v s).le)
    (errors_small D hsmall v).2 (gate_true_hits D j b h hg a)).2 x
  have hinit := hD.initial_cap v h.1 heven hv x
  have hbudget := budget_le D hsmall v j.val
  have hcount := neighbor_count_partition D v j
  have hpow : Real.rpow 2 (-(D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ)) *
      (2:ℝ) ^ (pastAxes D v j.val).card =
      Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    have he : ((pastAxes D v j.val).card : ℝ) + (D.remainingNeighbors v j : ℝ) =
        (D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ) := by exact_mod_cast hcount
    linarith
  have hcoefficient : 0 ≤ 4 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) := by
    have hKB : 0 ≤ κ.KB := by nlinarith [D.constants.KB_big]
    unfold densityScale
    positivity
  calc
    (D.currentPrior j v h).w x ≤ (D.initialPrior v h.1).w x * budget D v j.val := hcap
    _ ≤ (4 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ))) * budget D v j.val :=
      mul_le_mul_of_nonneg_right hinit (budget_pos D v j.val).le
    _ ≤ (4 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ))) *
        (2 * (2:ℝ) ^ (pastAxes D v j.val).card) :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg hcoefficient (Real.rpow_nonneg (by norm_num) _))
    _ = 8 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v j : ℝ)) := by
      rw [show (4 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
        Real.rpow 2 (-(D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ))) *
        (2 * (2:ℝ) ^ (pastAxes D v j.val).card) =
          (8 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v))) *
          (Real.rpow 2 (-(D.remainingNeighbors v ⟨0,D.l16_valid.r_pos⟩ : ℝ)) *
            (2:ℝ) ^ (pastAxes D v j.val).card) by ring]
      rw [hpow]


/-- On the gate the current prior uses its positive normalization branch. -/
theorem gated_current_mass (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hg : D.gate j b h) (hb : b ∈ D.encoding.base.classes j) (a : Fin (T.S.n k)) :
    D.initialValid (flipPos b a) h.1 ∧ 0 < ∑ x, rawWeight D h (flipPos b a) x := by
  have heven := (cubeFlip_parity b a).mpr (class_odd D j b hb)
  have hdist : _root_.hammingDist b (flipPos b a) = 1 := by
    simpa [OAI.HypercubeRamsey.cube] using flip_adj b a
  have hball : flipPos b a ∈ cubeBall b (6 * D.geom.r) := by
    simp only [cubeBall,Finset.mem_filter,Finset.mem_univ,true_and]
    have hr := D.l16_valid.r_pos
    omega
  have hv := hg.1 _ hball heven
  exact ⟨hv, (posterior_cap D h _ hv (fun s => (error_pos D _ s).le)
    (errors_small D hsmall _).2 (gate_true_hits D j b h hg a)).1⟩

end HypercubeRamsey.Lane_sol_s18_n1_caps
