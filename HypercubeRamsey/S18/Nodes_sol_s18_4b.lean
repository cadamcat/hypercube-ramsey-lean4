import HypercubeRamsey.S18.Locality_sol_s18_n4
import HypercubeRamsey.S18.Current_sol_s18_n4
import HypercubeRamsey.S18.Terminal_sol_s18_n4
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_s18_4b
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

private theorem mapE {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

private theorem bindE {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (g : α × β → ℝ) :
    (FinLaw.bind P K).E g = P.E (fun x => (K x).E (fun y => g (x, y))) := by
  simp only [FinLaw.E, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Forward continuation evaluated backwards. It is defined even off support. -/
noncomputable def continuation
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (q : Fin (D.geom.r + 1)) (h : D.encoding.base.History q) : ℝ :=
  if hq : q.val < D.geom.r then
    (D.encoding.kernels.referenceTransition ⟨q.val, hq⟩ h).E
      (fun out => continuation g ⟨q.val + 1, by omega⟩
        (D.encoding.base.extend ⟨q.val, hq⟩ h out))
  else
    g ((show q = Fin.last D.geom.r from Fin.ext (by simp; omega)) ▸ h)
termination_by D.geom.r - q.val

theorem continuation_last
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (h : D.encoding.base.History (Fin.last D.geom.r)) :
    continuation D g (Fin.last D.geom.r) h = g h := by
  rw [continuation]
  simp

theorem continuation_step
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) :
    continuation D g j.castSucc h =
      (D.encoding.kernels.referenceTransition j h).E
        (fun out => continuation D g j.succ (D.encoding.base.extend j h out)) := by
  rw [continuation]
  simp only [Fin.val_castSucc, j.isLt, dif_pos]
  rfl

private theorem continuation_run
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (s : Config D.fresh) :
    ∀ m (hm : m ≤ D.geom.r),
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s m hm).E
        (continuation D g ⟨m, Nat.lt_succ_of_le hm⟩) =
      continuation D g 0 (D.encoding.base.initialHistory s) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [LateProcessBase.runFrom, FinLaw.dirac, FinLaw.E, ite_mul, one_mul, zero_mul]
      erw [Finset.sum_eq_single (D.encoding.base.initialHistory s)]
      · simp
      · intro x _ hx; simp [hx]
      · intro hx; exact False.elim (hx (Finset.mem_univ _))
  | succ m ih =>
      intro hm
      rw [LateProcessBase.runFrom, mapE, bindE]
      have heq : (fun h : D.encoding.base.History ⟨m, by omega⟩ =>
          (D.encoding.kernels.referenceTransition ⟨m, hm⟩ h).E
            (fun out => continuation D g ⟨m + 1, by omega⟩
              (D.encoding.base.extend ⟨m, hm⟩ h out))) =
          continuation D g ⟨m, by omega⟩ := by
        funext h
        exact (continuation_step D g ⟨m, hm⟩ h).symm
      rw [heq]
      exact ih (by omega)

theorem continuation_disintegration
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ) (s : Config D.fresh)
    (q : Fin (D.geom.r + 1)) :
    (D.encoding.kernels.refRun s).E g =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s q.val
        (Nat.le_of_lt_succ q.isLt)).E (continuation D g q) := by
  have hlast := continuation_run D g s D.geom.r le_rfl
  have heq : continuation D g (Fin.last D.geom.r) = g := funext (continuation_last D g)
  change (D.encoding.kernels.refRun s).E (continuation D g (Fin.last D.geom.r)) = _ at hlast
  rw [heq] at hlast
  exact hlast.trans (continuation_run D g s q.val (Nat.le_of_lt_succ q.isLt)).symm

private theorem continuation_indicator
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (i : Fin (D.geom.r + 1)) (h : D.encoding.base.History i)
    (m : Fin (D.geom.r + 1)) (him : i.val ≤ m.val)
    (x : D.encoding.base.History m) :
    continuation D (fun full => if D.agreesWithHistory h full then g full else 0) m x =
      if D.beforeHistory x i him = h then continuation D g m x else 0 := by
  by_cases hm : m.val < D.geom.r
  · change continuation D (fun full => if D.agreesWithHistory h full then g full else 0)
      (⟨m.val, hm⟩ : Fin D.geom.r).castSucc x =
      if D.beforeHistory x i him = h then
        continuation D g (⟨m.val, hm⟩ : Fin D.geom.r).castSucc x else 0
    rw [continuation_step, continuation_step]
    have ih : ∀ out : D.encoding.base.ClassRows ⟨m.val, hm⟩,
        continuation D (fun full => if D.agreesWithHistory h full then g full else 0)
          (⟨m.val, hm⟩ : Fin D.geom.r).succ (D.encoding.base.extend ⟨m.val, hm⟩ x out) =
        if D.beforeHistory x i him = h then
          continuation D g (⟨m.val, hm⟩ : Fin D.geom.r).succ
            (D.encoding.base.extend ⟨m.val, hm⟩ x out) else 0 := by
      intro out
      rw [continuation_indicator g i h (⟨m.val, hm⟩ : Fin D.geom.r).succ
        (by simp; omega), Lane_sol_s18_n4.beforeHistory_extend]
    simp_rw [ih]
    by_cases hx : D.beforeHistory x i him = h
    · simp [hx]
    · simp [hx, FinLaw.E]
  · have hml : m = Fin.last D.geom.r := Fin.ext (by simp; omega)
    subst m
    simp only [continuation_last, S18.LateData.agreesWithHistory]
    by_cases hx : D.beforeHistory x i him = h <;> simp [hx]
termination_by D.geom.r - m.val

theorem futureRisk_eq_continuation (f : S18.LateEvent D)
    (q : Fin (D.geom.r + 1)) (h : D.encoding.base.History q)
    (hpos : 0 < (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h)) :
    D.futureRisk f h = continuation D
      (fun full => if S18.lateFailure D f full then 1 else 0) q h := by
  let g := fun full => if S18.lateFailure D f full then (1 : ℝ) else 0
  have hnum : (D.encoding.kernels.refRun h.1).pr
      (fun full => D.agreesWithHistory h full ∧ S18.lateFailure D f full) =
      (D.encoding.kernels.refRun h.1).E
        (fun full => if D.agreesWithHistory h full then g full else 0) := by
    unfold FinLaw.pr FinLaw.E
    apply Finset.sum_congr rfl
    intro full _
    by_cases ha : D.agreesWithHistory h full <;>
      by_cases hf : S18.lateFailure D f full <;> simp [ha, hf, g]
  rw [S18.LateData.futureRisk, hnum, continuation_disintegration D _ h.1 q]
  have hfun : (continuation D (fun full => if D.agreesWithHistory h full then g full else 0) q) =
      (fun x => if x = h then continuation D g q h else 0) := by
    funext x
    rw [continuation_indicator D g q h q le_rfl x, Lane_sol_s18_n4.beforeHistory_self]
    by_cases hx : x = h <;> simp [hx]
  rw [hfun]
  simp only [FinLaw.E, mul_ite, mul_zero]
  have hsum : (∑ x : D.encoding.base.History q,
      if x = h then
        (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 q.val
          (Nat.le_of_lt_succ q.isLt)).w x * continuation D g q h else 0) =
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition h.1 q.val
        (Nat.le_of_lt_succ q.isLt)).w h * continuation D g q h := by simp
  rw [hsum, ← Lane_sol_s18_n4.refRunHistoryMass D q h]
  exact mul_div_cancel_left₀ _ (ne_of_gt hpos)

/-- Equality of the fixed initial configuration and nearby processed row outputs. -/
def HistoryAgree (q : Fin (D.geom.r + 1)) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History q) : Prop :=
  h.1 = h'.1 ∧ ∀ b : D.encoding.base.ProcessedRole q,
    _root_.hammingDist v b.1 ≤ R → h.2 b = h'.2 b

private theorem flip_distance (v : Pos T k) (a : Fin (T.S.n k)) :
    _root_.hammingDist v (flipPos v a) = 1 := by
  have heq : (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j) = {a} := by
    ext j
    by_cases hj : j = a
    · subst j; cases hv : v a <;> simp [flipPos, hv]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [show flipPos v a j = v j from Function.update_of_ne hj _ _]
      simp [hj]
  change (Finset.univ.filter fun j : Fin (T.S.n k) => v j ≠ flipPos v a j).card = 1
  rw [heq, Finset.card_singleton]

private theorem rowOut_nonempty (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    Nonempty (D.encoding.base.RowOut b.1) := by
  by_contra hn
  haveI := not_nonempty_iff.mp hn
  have hs := (D.encoding.kernels.refK j b h).sum_one
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
  norm_num at hs

private theorem historyAgree_mono {q : Fin (D.geom.r + 1)} {v : Pos T k}
    {R R' : ℕ} {h h' : D.encoding.base.History q}
    (ha : HistoryAgree D q v R h h') (hR : R' ≤ R) : HistoryAgree D q v R' h h' :=
  ⟨ha.1, fun b hb => ha.2 b (hb.trans hR)⟩

private theorem historyAgree_extend (j : Fin D.geom.r) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History j.castSucc)
    (out out' : D.encoding.base.ClassRows j)
    (ha : HistoryAgree D j.castSucc v R h h')
    (ho : ∀ b, _root_.hammingDist v b.1 ≤ R → out b = out' b) :
    HistoryAgree D j.succ v R (D.encoding.base.extend j h out)
      (D.encoding.base.extend j h' out') := by
  refine ⟨ha.1, ?_⟩
  intro b hb
  dsimp [LateProcessBase.extend]
  split_ifs with hmem
  · exact ha.2 ⟨b.1, hmem⟩ hb
  · exact ho _ hb

private theorem rowKernel_spatial (hD : D.Spec) (H : S18.TransitionData D)
    (j : Fin D.geom.r) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History j.castSucc)
    (ha : HistoryAgree D j.castSucc v (R + 2) h h')
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (hb : _root_.hammingDist v b.1 ≤ R) :
    D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h' := by
  apply Lane_sol_s18_n4.referenceRow_local D H
  intro a
  apply Lane_sol_s18_n4.priorAt_local D hD
  · intro C _
    exact congrFun ha.1 C
  · intro c hc
    apply congrArg D.encoding.base.rowLabel
    apply ha.2
    have h1 := _root_.hammingDist_triangle v b.1 (flipPos b.1 a)
    have h2 := _root_.hammingDist_triangle v (flipPos b.1 a) c.1
    have hf := flip_distance b.1 a
    change _root_.hammingDist (flipPos b.1 a) c.1 = 1 at hc
    omega

/-- A continuation expands a terminal spatial scope by two per remaining class. -/
theorem continuation_local (hD : D.Spec) (H : S18.TransitionData D)
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (v : Pos T k) (R : ℕ)
    (hg : ∀ h h', HistoryAgree D (Fin.last D.geom.r) v R h h' → g h = g h')
    (q : Fin (D.geom.r + 1)) (h h' : D.encoding.base.History q)
    (ha : HistoryAgree D q v (R + 2 * (D.geom.r - q.val)) h h') :
    continuation D g q h = continuation D g q h' := by
  by_cases hq : q.val < D.geom.r
  · let j : Fin D.geom.r := ⟨q.val, hq⟩
    have hqj : q = j.castSucc := rfl
    change continuation D g j.castSucc h = continuation D g j.castSucc h'
    let R' := R + 2 * (D.geom.r - j.succ.val)
    have hR : R + 2 * (D.geom.r - j.val) = R' + 2 := by
      dsimp [R']; omega
    have ha' : HistoryAgree D j.castSucc v (R' + 2) h h' := by
      change HistoryAgree D j.castSucc v (R + 2 * (D.geom.r - j.val)) h h' at ha
      rwa [hR] at ha
    let S := Finset.univ.filter fun b : {v : Pos T k // v ∈ D.encoding.base.classes j} =>
      _root_.hammingDist v b.1 ≤ R'
    let f := fun out => continuation D g j.succ (D.encoding.base.extend j h out)
    have hf : ∀ out out', (∀ b ∈ S, out b = out' b) → f out = f out' := by
      intro out out' ho
      apply continuation_local hD H g v R hg
      apply historyAgree_extend
      · exact ⟨rfl, fun _ _ => rfl⟩
      · intro b hb
        exact ho b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    have hfun : f = fun out => continuation D g j.succ
        (D.encoding.base.extend j h' out) := by
      funext out
      apply continuation_local hD H g v R hg
      apply historyAgree_extend
      · exact historyAgree_mono D ha' (by omega)
      · intro _ _; rfl
    letI : ∀ b : {v : Pos T k // v ∈ D.encoding.base.classes j},
        Nonempty (D.encoding.base.RowOut b.1) := rowOut_nonempty D j h
    rw [continuation_step, continuation_step]
    change (FinLaw.pi (fun b => D.encoding.kernels.refK j b h)).E f = _
    rw [S18.Lane_sol_s18_n5.pi_E_local
      (fun b => D.encoding.kernels.refK j b h)
      (fun b => D.encoding.kernels.refK j b h') S f hf
      (fun b hb => rowKernel_spatial D hD H j v R' h h' ha' b
        (Finset.mem_filter.mp hb).2), hfun]
    rfl
  · have hql : q = Fin.last D.geom.r := Fin.ext (by simp; omega)
    subst q
    rw [continuation_last, continuation_last]
    apply hg
    simpa [HistoryAgree] using ha
termination_by D.geom.r - q.val

private theorem historyAgree_before {q : Fin (D.geom.r + 1)}
    (i : Fin (D.geom.r + 1)) (hi : i.val ≤ q.val) (v : Pos T k) (R : ℕ)
    (h h' : D.encoding.base.History q) (ha : HistoryAgree D q v R h h') :
    HistoryAgree D i v R (D.beforeHistory h i hi) (D.beforeHistory h' i hi) :=
  ⟨ha.1, fun b hb => ha.2 ⟨b.1, D.processed_mono i q hi b.2⟩ hb⟩

private theorem priorAt_spatial (hD : D.Spec) (q : Fin (D.geom.r + 1))
    (v w : Pos T k) (R : ℕ) (h h' : D.encoding.base.History q)
    (ha : HistoryAgree D q v R h h') (hw : _root_.hammingDist v w + 1 ≤ R) :
    D.priorAt q w h = D.priorAt q w h' := by
  apply Lane_sol_s18_n4.priorAt_local D hD
  · intro C _; exact congrFun ha.1 C
  · intro b hb
    apply congrArg D.encoding.base.rowLabel
    apply ha.2
    have ht := _root_.hammingDist_triangle v w b.1
    change _root_.hammingDist w b.1 = 1 at hb
    omega

private theorem R3_spatial (hD : D.Spec) (j : Fin D.geom.r)
    (v b : Pos T k) (R : ℕ) (h h' : D.encoding.base.History j.castSucc)
    (ha : HistoryAgree D j.castSucc v R h h') (hb : _root_.hammingDist v b + 2 ≤ R)
    (out : D.encoding.base.RowOut b) : D.R3 j h out ↔ D.R3 j h' out := by
  have hp : ∀ a, D.currentPrior j (flipPos b a) h = D.currentPrior j (flipPos b a) h' := by
    intro a
    apply priorAt_spatial D hD j.castSucc v (flipPos b a) R h h' ha
    have ht := _root_.hammingDist_triangle v b (flipPos b a)
    have hf := flip_distance b a
    omega
  simp only [S18.LateData.R3, hp]

private theorem gate_spatial (hD : D.Spec) (j : Fin D.geom.r) (b : Pos T k)
    (h h' : D.encoding.base.History j.castSucc)
    (ha : HistoryAgree D j.castSucc b (6 * D.geom.r + 2) h h') :
    D.gate j b h ↔ D.gate j b h' := by
  have hrows : ∀ (s : Fin D.geom.r) (hs : s.val < j.val)
      (c : {x : Pos T k // x ∈ D.encoding.base.classes s}),
      c.1 ∈ cubeBall b (6 * D.geom.r) → D.pastRows h s hs c = D.pastRows h' s hs c := by
    intro s hs c hc
    exact ha.2 ⟨c.1, D.class_before s j.castSucc hs c.2⟩
      (by
        change _root_.hammingDist b c.1 ≤ 6 * D.geom.r + 2
        have hd := (Finset.mem_filter.mp hc).2
        omega)
  have hR3 : ∀ (s : Fin D.geom.r) (hs : s.val < j.val)
      (c : {x : Pos T k // x ∈ D.encoding.base.classes s}),
      c.1 ∈ cubeBall b (6 * D.geom.r) →
      (D.R3 s (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)) (D.pastRows h s hs c) ↔
        D.R3 s (D.beforeHistory h' s.castSucc (Nat.le_of_lt hs)) (D.pastRows h' s hs c)) := by
    intro s hs c hc
    rw [hrows s hs c hc]
    apply R3_spatial D hD s b c.1 (6 * D.geom.r + 2)
    · exact historyAgree_before D (q := j.castSucc) s.castSucc (Nat.le_of_lt hs) b _ h h' ha
    · have hd := (Finset.mem_filter.mp hc).2
      omega
  unfold S18.LateData.gate
  rw [ha.1]
  apply and_congr_right
  intro _
  apply forall_congr'; intro s
  apply forall_congr'; intro hs
  apply forall_congr'; intro c
  apply imp_congr_right; intro hc
  exact and_congr (hR3 s hs c hc) (by rw [hrows s hs c hc])

/-- The gate's history checks are included in the spatial terminal scope. -/
theorem lateFailure_local (hD : D.Spec) (f : S18.LateEvent D)
    (h h' : D.encoding.base.History (Fin.last D.geom.r))
    (ha : HistoryAgree D (Fin.last D.geom.r) f.2.2.1.1 (6 * D.geom.r + 2) h h') :
    S18.lateFailure D f h ↔ S18.lateFailure D f h' := by
  let p := f.2
  let before := D.beforeHistory h p.1.castSucc (Nat.le_of_lt p.1.isLt)
  let before' := D.beforeHistory h' p.1.castSucc (Nat.le_of_lt p.1.isLt)
  have hab : HistoryAgree D p.1.castSucc p.2.1.1 (6 * D.geom.r + 2) before before' :=
    historyAgree_before D _ _ _ _ h h' ha
  have hout : D.pastRows h p.1 p.1.isLt p.2.1 = D.pastRows h' p.1 p.1.isLt p.2.1 := by
    apply ha.2
    simp [p, HypercubeRamsey.hammingDist]
  have hgate := gate_spatial D hD p.1 p.2.1.1 before before' hab
  have hR2 : D.R2 p.1 before (D.pastRows h' p.1 p.1.isLt p.2.1) ↔
      D.R2 p.1 before' (D.pastRows h' p.1 p.1.isLt p.2.1) := by
    simp only [S18.LateData.R2, S18.LateData.prefixMoments, hab.1]
  have hR3 := R3_spatial D hD p.1 p.2.1.1 p.2.1.1 _ before before' hab
    (by simp [HypercubeRamsey.hammingDist]) (D.pastRows h' p.1 p.1.isLt p.2.1)
  have hprefix : D.prefixFailure p h ↔ D.prefixFailure p h' := by
    simp only [S18.LateData.prefixFailure, hout]
    change (_ ∧ D.gate p.1 p.2.1.1 before ∧ _) ↔ (_ ∧ D.gate p.1 p.2.1.1 before' ∧ _)
    simp only [hgate, S18.LateData.prefixMoments, S18.LateData.beforeHistory, ha.1]
  unfold S18.lateFailure
  change (D.gate p.1 p.2.1.1 before ∧
    (if f.1.val = 0 then ¬ D.R1 p.1 (D.pastRows h p.1 p.1.isLt p.2.1)
     else if f.1.val = 1 then D.prefixFailure p h else
       D.R1 p.1 (D.pastRows h p.1 p.1.isLt p.2.1) ∧
       D.R2 p.1 before (D.pastRows h p.1 p.1.isLt p.2.1) ∧
       ¬ D.R3 p.1 before (D.pastRows h p.1 p.1.isLt p.2.1))) ↔ _
  simp only [hout, hgate]
  split_ifs <;> (try simp only [hprefix, hR2, hR3]) <;> rfl

noncomputable def localRisk (f : S18.LateEvent D) (q : Fin (D.geom.r + 1))
    (h : D.encoding.base.History q) : ℝ :=
  continuation D (fun full => if S18.lateFailure D f full then 1 else 0) q h

theorem localRisk_local (hD : D.Spec) (H : S18.TransitionData D)
    (f : S18.LateEvent D) (q : Fin (D.geom.r + 1))
    (h h' : D.encoding.base.History q)
    (ha : HistoryAgree D q f.2.2.1.1 (8 * D.geom.r + 2) h h') :
    localRisk D f q h = localRisk D f q h' := by
  apply continuation_local D hD H _ f.2.2.1.1 (6 * D.geom.r + 2)
  · intro x y hxy
    rw [lateFailure_local D hD f x y hxy]
  · exact historyAgree_mono D ha (by omega)

noncomputable def localClassFailure (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) :
    ({v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) →
      D.encoding.base.ClassRows j → Prop
  | .inl b, out => Lane_sol_s18_n4.classFailure D δ j h (.inl b) out
  | .inr f, out => j.val < f.2.1.val ∧
      D.threshold δ (j.val + 1) < localRisk D f j.succ (D.encoding.base.extend j h out)

noncomputable def localScope (j : Fin D.geom.r) :
    ({v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) →
      Finset {v : Pos T k // v ∈ D.encoding.base.classes j}
  | .inl b => {b}
  | .inr f => Finset.univ.filter fun b => _root_.hammingDist f.2.2.1.1 b.1 ≤ 8 * D.geom.r + 2

theorem localClassFailure_depends (hD : D.Spec) (H : S18.TransitionData D)
    (δ : ℝ) (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc)
    (f : {v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) :
    FinProb.DependsOn (localClassFailure D δ j h f) (localScope D j f) := by
  intro out out' ho
  cases f with
  | inl b =>
      have hb : out b = out' b := ho b (Finset.mem_singleton_self b)
      simp only [localClassFailure, Lane_sol_s18_n4.classFailure, hb]
  | inr f =>
      have hr : localRisk D f j.succ (D.encoding.base.extend j h out) =
          localRisk D f j.succ (D.encoding.base.extend j h out') := by
        apply localRisk_local D hD H
        apply historyAgree_extend
        · exact ⟨rfl, fun _ _ => rfl⟩
        · intro b hb
          exact ho b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      simp only [localClassFailure, hr]

private theorem localRisk_extension_eq (f : S18.LateEvent D) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (hpos : 0 < (D.encoding.kernels.refRun h.1).pr (D.agreesWithHistory h))
    (out : D.encoding.base.ClassRows j)
    (hw : (D.encoding.kernels.referenceTransition j h).w out ≠ 0) :
    D.futureRisk f (D.encoding.base.extend j h out) =
      localRisk D f j.succ (D.encoding.base.extend j h out) := by
  apply futureRisk_eq_continuation
  change 0 < (D.encoding.kernels.refRun h.1).pr
    (D.agreesWithHistory (D.encoding.base.extend j h out))
  rw [Lane_sol_s18_n4.refRunExtendedHistoryMass D j h out]
  exact mul_pos hpos (lt_of_le_of_ne
    ((D.encoding.kernels.referenceTransition j h).nonneg out) (Ne.symm hw))

theorem localClassFailure_probability (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (he : D.enter δ j h)
    (f : {v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) :
    (D.encoding.kernels.referenceTransition j h).pr (localClassFailure D δ j h f) =
      (D.encoding.kernels.referenceTransition j h).pr (Lane_sol_s18_n4.classFailure D δ j h f) := by
  cases f with
  | inl b => rfl
  | inr f =>
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro out _
      by_cases hw : (D.encoding.kernels.referenceTransition j h).w out = 0
      · simp [hw]
      · simp only [localClassFailure, Lane_sol_s18_n4.classFailure,
          localRisk_extension_eq D f j h he.1 out hw]
        by_cases hf : j.val < f.2.1.val ∧
            D.threshold δ (j.val + 1) < localRisk D f j.succ (D.encoding.base.extend j h out) <;> simp [hf]

theorem classFailure_implies_local (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (f : {v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D)
    (out : D.encoding.base.ClassRows j) :
    Lane_sol_s18_n4.classFailure D δ j h f out → localClassFailure D δ j h f out := by
  cases f with
  | inl b => exact id
  | inr f =>
      intro hf
      change j.val < f.2.1.val ∧ D.threshold δ (j.val + 1) <
        D.futureRisk f (D.encoding.base.extend j h out) at hf
      by_cases hp : 0 < (D.encoding.kernels.refRun h.1).pr
          (D.agreesWithHistory (D.encoding.base.extend j h out))
      · have heq := futureRisk_eq_continuation D f j.succ (D.encoding.base.extend j h out) hp
        exact ⟨hf.1, by simpa only [localRisk, ← heq] using hf.2⟩
      · have hn : 0 ≤ (D.encoding.kernels.refRun h.1).pr
            (D.agreesWithHistory (D.encoding.base.extend j h out)) := by
          unfold FinLaw.pr
          apply Finset.sum_nonneg
          intro full _
          split_ifs <;> simp [FinLaw.nonneg]
        have hz : (D.encoding.kernels.refRun h.1).pr
            (D.agreesWithHistory (D.encoding.base.extend j h out)) = 0 := by linarith
        have hr : D.futureRisk f (D.encoding.base.extend j h out) = 0 := by
          change _ / (D.encoding.kernels.refRun h.1).pr
            (D.agreesWithHistory (D.encoding.base.extend j h out)) = 0
          rw [hz, div_zero]
        have ht : 0 < D.threshold δ (j.val + 1) := Real.exp_pos _
        rw [hr] at hf
        exact False.elim (by linarith [hf.2])

private theorem ball_step (v w : Pos T k) (R : ℕ)
    (hw : _root_.hammingDist v w ≤ R + 1) :
    w ∈ cubeBall v R ∪ (cubeBall v R).biUnion (fun z => Finset.univ.image (flipPos z)) := by
  by_cases hR : _root_.hammingDist v w ≤ R
  · exact Finset.mem_union.mpr (.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩))
  · have hpos : 0 < (Finset.univ.filter fun a : Fin (T.S.n k) => v a ≠ w a).card := by
      change 0 < _root_.hammingDist v w
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have hne := (Finset.mem_filter.mp ha).2
    let z := flipPos w a
    have hset : (Finset.univ.filter fun b : Fin (T.S.n k) => v b ≠ z b) =
        (Finset.univ.filter fun b : Fin (T.S.n k) => v b ≠ w b).erase a := by
      ext b
      by_cases hb : b = a
      · subst b
        cases hv : v a <;> cases hw : w a <;> simp_all [z, flipPos]
      · simp [z, flipPos, hb, Ne.symm hb]
    have hd : _root_.hammingDist v z + 1 = _root_.hammingDist v w := by
      change (Finset.univ.filter fun b : Fin (T.S.n k) => v b ≠ z b).card + 1 = _
      rw [hset, Finset.card_erase_of_mem ha]
      change (_root_.hammingDist v w - 1) + 1 = _root_.hammingDist v w
      omega
    have hz : z ∈ cubeBall v R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hback : flipPos z a = w := by
      funext b
      by_cases hb : b = a
      · subst b; simp [z, flipPos]
      · simp [z, flipPos, hb]
    exact Finset.mem_union.mpr (.inr (Finset.mem_biUnion.mpr
      ⟨z, hz, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hback⟩⟩))

theorem cubeBall_card (v : Pos T k) (R : ℕ) :
    (cubeBall v R).card ≤ (T.S.n k + 1) ^ R := by
  induction R with
  | zero =>
      have heq : cubeBall v 0 = {v} := by
        ext w
        simp only [cubeBall, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Nat.le_zero]
        exact (hammingDist_eq_zero).trans eq_comm
      simp [heq]
  | succ R ih =>
      have hsub : cubeBall v (R + 1) ⊆
          cubeBall v R ∪ (cubeBall v R).biUnion (fun z => Finset.univ.image (flipPos z)) := by
        intro w hw
        exact ball_step v w R (Finset.mem_filter.mp hw).2
      have hsum : (∑ z ∈ cubeBall v R,
          (Finset.univ.image (flipPos z)).card) ≤ (cubeBall v R).card * T.S.n k := by
        calc
          _ ≤ ∑ z ∈ cubeBall v R, T.S.n k := by
            apply Finset.sum_le_sum
            intro z _
            simpa using (Finset.card_image_le (s := Finset.univ) (f := flipPos z))
          _ = _ := by simp
      calc
        _ ≤ (cubeBall v R ∪ (cubeBall v R).biUnion
            (fun z => Finset.univ.image (flipPos z))).card := Finset.card_le_card hsub
        _ ≤ (cubeBall v R).card + ((cubeBall v R).biUnion
            (fun z => Finset.univ.image (flipPos z))).card := Finset.card_union_le _ _
        _ ≤ (cubeBall v R).card + ∑ z ∈ cubeBall v R,
            (Finset.univ.image (flipPos z)).card := Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ (cubeBall v R).card * (T.S.n k + 1) := by nlinarith [hsum]
        _ ≤ (T.S.n k + 1) ^ R * (T.S.n k + 1) := Nat.mul_le_mul_right _ ih
        _ = _ := (pow_succ _ _).symm

private theorem classBall_card (j : Fin D.geom.r) (v : Pos T k) (R : ℕ) :
    (Finset.univ.filter fun b : {x : Pos T k // x ∈ D.encoding.base.classes j} =>
      _root_.hammingDist v b.1 ≤ R).card ≤ (T.S.n k + 1) ^ R := by
  let S := Finset.univ.filter fun b : {x : Pos T k // x ∈ D.encoding.base.classes j} =>
    _root_.hammingDist v b.1 ≤ R
  have hi : S.image Subtype.val ⊆ cubeBall v R := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective S Subtype.val_injective).symm
    _ ≤ (cubeBall v R).card := Finset.card_le_card hi
    _ ≤ _ := cubeBall_card v R

theorem localScope_card (j : Fin D.geom.r)
    (f : {v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) :
    (localScope D j f).card ≤ (T.S.n k + 1) ^ (8 * D.geom.r + 2) := by
  cases f with
  | inl b =>
      simp only [localScope, Finset.card_singleton]
      exact Nat.one_le_pow _ _ (by omega)
  | inr f => exact classBall_card D j f.2.2.1.1 _

theorem localScope_incidence (j : Fin D.geom.r)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    (Finset.univ.filter fun f => b ∈ localScope D j f).card ≤
      1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
        (T.S.n k + 1) ^ (8 * D.geom.r + 2) := by
  let I := {f : {v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D //
    b ∈ localScope D j f}
  let Near := fun s : Fin D.geom.r =>
    {c : {v : Pos T k // v ∈ D.encoding.base.classes s} //
      _root_.hammingDist b.1 c.1 ≤ 8 * D.geom.r + 2}
  let J := Unit ⊕ (Fin 3 × Σ s : Fin D.geom.r,
    Near s × Fin (T.S.n k + 1) × Fin (T.S.n k + 1) × Fin (T.S.n k))
  let toJ : I → J := fun f => match f with
    | ⟨.inl _, _⟩ => .inl ()
    | ⟨.inr f, hf⟩ => .inr (f.1, ⟨f.2.1, (⟨f.2.2.1, by
        have hh := (Finset.mem_filter.mp hf).2
        rwa [hammingDist_comm] at hh⟩, f.2.2.2)⟩)
  let fromJ : J → ({v : Pos T k // v ∈ D.encoding.base.classes j} ⊕ S18.LateEvent D) :=
    fun f => match f with
    | .inl _ => .inl b
    | .inr f => .inr (f.1, ⟨f.2.1, (f.2.2.1.1, f.2.2.2)⟩)
  have hback : ∀ f : I, fromJ (toJ f) = f.1 := by
    rintro ⟨f, hf⟩
    cases f with
    | inl c =>
        have heq : b = c := by simpa only [localScope, Finset.mem_singleton] using hf
        simp only [toJ, fromJ, heq]
    | inr f => rfl
  have hinj : Function.Injective toJ := by
    intro x y hxy
    apply Subtype.ext
    rw [← hback x, ← hback y, hxy]
  have hnear : ∀ s, Fintype.card (Near s) ≤ (T.S.n k + 1) ^ (8 * D.geom.r + 2) := by
    intro s
    rw [Fintype.card_subtype]
    exact classBall_card D s b.1 _
  have hcount : Fintype.card J ≤
      1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
        (T.S.n k + 1) ^ (8 * D.geom.r + 2) := by
    simp only [J, Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_sigma]
    have hsum : (∑ s : Fin D.geom.r,
        Fintype.card (Near s) * ((T.S.n k + 1) * ((T.S.n k + 1) * T.S.n k))) ≤
        D.geom.r * ((T.S.n k + 1) ^ (8 * D.geom.r + 2) *
          ((T.S.n k + 1) * ((T.S.n k + 1) * T.S.n k))) := by
      calc
        _ ≤ ∑ _s : Fin D.geom.r,
            (T.S.n k + 1) ^ (8 * D.geom.r + 2) *
              ((T.S.n k + 1) * ((T.S.n k + 1) * T.S.n k)) :=
          Finset.sum_le_sum (fun s _ => Nat.mul_le_mul_right _ (hnear s))
        _ = _ := by simp
    have hh := Nat.mul_le_mul_left 3 hsum
    nlinarith [hh]
  calc
    _ = Fintype.card I := (Fintype.card_subtype _).symm
    _ ≤ Fintype.card J := Fintype.card_le_of_injective toJ hinj
    _ ≤ _ := hcount

/-- The clock can use local versions of conditional alarms; support-zero
extensions do not alter their reference probabilities or avoidance implication. -/
theorem localEnteringClockReduction {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ ρ : ℕ → ℝ, Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ nclock : ℕ, n₀ ≤ nclock → 1 ≤ nclock → 1 + ρ nclock ≤ 2 →
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
        (D : S18.LateData hPT) (δ : ℝ) (j : Fin D.geom.r)
        (h : D.encoding.base.History j.castSucc), D.Spec → S18.TransitionData D → D.enter δ j h →
        Real.log (T.S.N k : ℝ) ≤ 2 * (nclock : ℝ) →
        Real.exp (Real.log (T.S.n k) ^ 3) ≤ (nclock : ℝ) ^ (5 : ℝ) →
        (∀ b y, (D.encoding.kernels.refK j b h).pr
          (fun out => D.encoding.base.rowLabel out = y) ≤ (nclock : ℝ) ^ (-(κ.Astar : ℝ))) →
        (T.S.n k + 1 : ℝ) ^ (8 * D.geom.r + 2 : ℕ) ≤ (nclock : ℝ) ^ (5 : ℝ) →
        (1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
          (T.S.n k + 1) ^ (8 * D.geom.r + 2) : ℕ) ≤ (nclock : ℝ) ^ (5 : ℝ) →
        (∀ f, (D.encoding.kernels.referenceTransition j h).pr
          (Lane_sol_s18_n4.classFailure D δ j h f) ≤ (nclock : ℝ) ^ (-(κ.Pstar : ℝ))) →
        ∃ J : FinProb (D.encoding.base.ClassRows j),
          (∀ out, J.w out ≠ 0 → Function.Injective (fun b => D.encoding.base.rowLabel (out b)) ∧
            out ∉ D.bad j h ∧ out ∉ D.alarm δ j h) ∧
          ∀ (S : Finset {v : Pos T k // v ∈ D.encoding.base.classes j})
            (out : D.encoding.base.ClassRows j),
            (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
            J.pr (fun ω => ∀ b ∈ S, ω b = out b) ≤
              2 * ∏ b ∈ S, (D.encoding.kernels.refK j b h).w (out b) := by
  rcases hκ.clock with ⟨_, _, A', P', n₀, ρ, hApos, hPpos, hA, hP, hn₀, hρ, hclock⟩
  refine ⟨n₀, ρ, hρ, ?_⟩
  intro nclock hlarge hn hcost T k PT hPT D δ j h hD H he hlabels htests hatom hscope hinc hbad
  let p : ∀ b : {v : Pos T k // v ∈ D.encoding.base.classes j},
      FinProb (D.encoding.base.RowOut b.1) := fun b =>
    ⟨(D.encoding.kernels.refK j b h).w, (D.encoding.kernels.refK j b h).nonneg,
      (D.encoding.kernels.refK j b h).sum_one⟩
  have hnreal : 1 ≤ (nclock : ℝ) := by exact_mod_cast hn
  have hmarg : ∀ b y, labMarg (p b) D.encoding.base.rowLabel y =
      (D.encoding.kernels.refK j b h).pr (fun out => D.encoding.base.rowLabel out = y) := by
    intro b y
    unfold labMarg FinLaw.pr
    apply Finset.sum_congr rfl
    intro out _
    by_cases heq : D.encoding.base.rowLabel out = y <;> simp [heq, p]
  have ha' : ∀ b y, labMarg (p b) D.encoding.base.rowLabel y ≤ (nclock : ℝ) ^ (-A') := by
    intro b y
    rw [hmarg]
    exact (hatom b y).trans (Real.rpow_le_rpow_of_exponent_le hnreal (by linarith))
  have hb' : ∀ f, (FinProb.pi p).pr (localClassFailure D δ j h f) ≤ (nclock : ℝ) ^ (-P') := by
    intro f
    change (D.encoding.kernels.referenceTransition j h).pr (localClassFailure D δ j h f) ≤ _
    rw [localClassFailure_probability D δ j h he]
    exact (hbad f).trans (Real.rpow_le_rpow_of_exponent_le hnreal (by linarith))
  have hload : ∀ y, ∑ b, labMarg (p b) D.encoding.base.rowLabel y ≤ κ.θ0 := by
    intro y
    simp_rw [hmarg]
    exact he.2.2 y
  obtain ⟨J, hJ, hcyl⟩ := hclock nclock hlarge (T.S.N k) hlabels
    (fun b => D.encoding.base.rowLabel) p (localClassFailure D δ j h) (localScope D j)
    hload ha' (localClassFailure_depends D hD H δ j h)
    (fun f => le_trans (show ((localScope D j f).card : ℝ) ≤
        (T.S.n k + 1 : ℝ) ^ (8 * D.geom.r + 2 : ℕ) by
          exact_mod_cast localScope_card D j f) hscope)
    (fun b => le_trans (show ((Finset.univ.filter fun f => b ∈ localScope D j f).card : ℝ) ≤
        ((1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
          (T.S.n k + 1) ^ (8 * D.geom.r + 2) : ℕ) : ℝ) by
          exact_mod_cast localScope_incidence D j b) hinc) hb'
  refine ⟨J, ?_, ?_⟩
  · intro out hout
    have hj := hJ out hout
    refine ⟨hj.1, (Lane_sol_s18_n4.avoidsClassFailure D δ j h out).1 ?_⟩
    intro f hf
    exact hj.2 f (classFailure_implies_local D δ j h f out hf)
  · intro S out hS
    exact (hcyl S out (hS.trans htests)).trans
      (mul_le_mul_of_nonneg_right hcost (Finset.prod_nonneg (fun b _ =>
        (D.encoding.kernels.refK j b h).nonneg _)))

open Filter

private theorem logPowerEventually (T : Stage) (m : ℕ) (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ k in atTop, C * Real.log (T.S.n k) ^ m ≤ (T.S.n k : ℝ) ^ a := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (m : ℝ) ha).const_mul_left C
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [hn.eventually (hsmall.eventuallyLE),
    T.S.n_tendsto.eventually_ge_atTop 1] with k hk hn1
  have hL : 0 ≤ Real.log (T.S.n k) := Real.log_nonneg (by exact_mod_cast hn1)
  have hR : 0 ≤ (T.S.n k : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_of_nonneg hR] at hk
  exact (le_abs_self _).trans hk

noncomputable def clockSize (T : Stage) (k : ℕ) : ℕ :=
  ⌈Real.exp (Real.log (T.S.n k) ^ 4)⌉₊

private theorem clockSize_bounds (hn : 48 ≤ Real.log (T.S.n k)) :
    Real.exp (Real.log (T.S.n k) ^ 4) ≤ (clockSize T k : ℝ) ∧
      (clockSize T k : ℝ) ≤ Real.exp (2 * Real.log (T.S.n k) ^ 4) ∧
      (T.S.n k : ℝ) ≤ clockSize T k := by
  let L := Real.log (T.S.n k)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hpow : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hx : 2 ≤ Real.exp (L ^ 4) := by
    have h := Real.add_one_le_exp (L ^ 4)
    linarith
  have hlo : Real.exp (L ^ 4) ≤ (clockSize T k : ℝ) := Nat.le_ceil _
  have hup : (clockSize T k : ℝ) ≤ Real.exp (L ^ 4) + 1 :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hup' : (clockSize T k : ℝ) ≤ Real.exp (2 * L ^ 4) := by
    rw [show 2 * L ^ 4 = L ^ 4 + L ^ 4 by ring, Real.exp_add]
    nlinarith
  have hnpos : 0 < (T.S.n k : ℝ) := by
    have hlog : 0 < Real.log (T.S.n k) := by linarith
    exact lt_trans (by norm_num : (0 : ℝ) < 1) ((Real.log_pos_iff (Nat.cast_nonneg _)).1 hlog)
  have hLp : L ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hnclock : (T.S.n k : ℝ) ≤ clockSize T k := by
    calc
      _ = Real.exp L := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L ^ 4) := Real.exp_le_exp.mpr hLp
      _ ≤ _ := hlo
  exact ⟨hlo, hup', hnclock⟩

theorem clockSize_tendsto (T : Stage) : Tendsto (clockSize T) atTop atTop := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hL := Real.tendsto_log_atTop.comp hn
  apply tendsto_atTop_mono' _ _ T.S.n_tendsto
  filter_upwards [hL.eventually_ge_atTop 48] with k hk
  exact_mod_cast (clockSize_bounds (T := T) (k := k) hk).2.2

private theorem latePool_inverse_bound (j : Fin D.geom.r) :
    2 / ((D.encoding.base.latePool j).card : ℝ) ≤ 12 * (D.geom.r : ℝ) / T.S.N k := by
  let M := (D.encoding.base.latePool j).card
  have hM : 0 < M := D.late_pool_pos j
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hden : 0 < 3 * D.geom.r := by nlinarith [D.l16_valid.r_pos]
  have hMeq : M = T.S.N k / (3 * D.geom.r) := by
    dsimp [M]
    rw [D.encoding.base.latePool_card, Nat.div_div_eq_div_mul]
  have hmod := Nat.mod_lt (T.S.N k) hden
  have heq := Nat.mod_add_div (T.S.N k) (3 * D.geom.r)
  rw [← hMeq] at heq
  have hbound : T.S.N k ≤ 6 * D.geom.r * M := by nlinarith
  apply (div_le_div_iff₀ (by exact_mod_cast hM) hN).2
  have hb : (T.S.N k : ℝ) ≤ 6 * D.geom.r * M := by exact_mod_cast hbound
  nlinarith

private theorem spatialBudget (n r : ℕ) (hn : 2 ≤ n)
    (hL : 48 ≤ Real.log (n : ℝ)) (hr : (r : ℝ) ≤ 2 * Real.log (n : ℝ) ^ 2) :
    (n + 1 : ℝ) ^ (8 * r + 8 : ℕ) ≤ Real.exp (Real.log (n : ℝ) ^ 4) := by
  let L := Real.log (n : ℝ)
  have hn2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) ≤ 2 * L := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have he : ((8 * r + 8 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤ L ^ 4 := by
    have hc := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (8 * r + 8))
    have hrr := mul_le_mul_of_nonneg_right hr hL0
    have hLp : 48 * L ^ 3 ≤ L ^ 4 := by
      have hL48 : 48 ≤ L := hL
      nlinarith [mul_nonneg (sub_nonneg.mpr hL48) (pow_nonneg hL0 3)]
    have hs := mul_nonneg (sub_nonneg.mpr (show 1 ≤ L ^ 2 by nlinarith)) hL0
    push_cast at hc ⊢
    dsimp [L] at *
    nlinarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm, L] using he

private theorem incidenceBudget (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ n) :
    1 + 3 * r * (n + 1) ^ 2 * n * (n + 1) ^ (8 * r + 2) ≤ (n + 1) ^ (8 * r + 8) := by
  have hbase : 1 ≤ (n + 1) ^ (8 * r + 6) := Nat.one_le_pow _ _ (by omega)
  have hmain : 3 * r * (n + 1) ^ 2 * n * (n + 1) ^ (8 * r + 2) ≤
      3 * (n + 1) ^ (8 * r + 6) := by
    calc
      _ ≤ 3 * (n + 1) * (n + 1) ^ 2 * (n + 1) * (n + 1) ^ (8 * r + 2) := by
        gcongr <;> omega
      _ = 3 * (n + 1) ^ 4 * (n + 1) ^ (8 * r + 2) := by ring
      _ = _ := by rw [mul_assoc, ← pow_add, show 4 + (8 * r + 2) = 8 * r + 6 by omega]
  have h4 : 4 ≤ (n + 1) ^ 2 := by nlinarith
  calc
    _ ≤ 4 * (n + 1) ^ (8 * r + 6) := by omega
    _ ≤ (n + 1) ^ 2 * (n + 1) ^ (8 * r + 6) := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add, show 2 + (8 * r + 6) = 8 * r + 8 by omega]

private theorem clockNegativeBudget (hn : 48 ≤ Real.log (T.S.n k)) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-2 * a * Real.log (T.S.n k) ^ 4) ≤ (clockSize T k : ℝ) ^ (-a) := by
  obtain ⟨hlo, hup, _⟩ := clockSize_bounds hn
  have hc : 0 < (clockSize T k : ℝ) := (Real.exp_pos _).trans_le hlo
  calc
    _ = (Real.exp (2 * Real.log (T.S.n k) ^ 4)) ^ (-a) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hc hup (neg_nonpos.mpr ha)

/-- Scalar hypotheses used uniformly for all histories and all valid late data. -/
structure ClockBudget (δ : ℝ) : Prop where
  n_pos : 1 ≤ T.S.n k
  clock_pos : 1 ≤ clockSize T k
  labels : Real.log (T.S.N k : ℝ) ≤ 2 * (clockSize T k : ℝ)
  tests : Real.exp (Real.log (T.S.n k) ^ 3) ≤ (clockSize T k : ℝ) ^ (5 : ℝ)
  scope : (T.S.n k + 1 : ℝ) ^ (8 * D.geom.r + 2 : ℕ) ≤ (clockSize T k : ℝ) ^ (5 : ℝ)
  incidence : (1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
    (T.S.n k + 1) ^ (8 * D.geom.r + 2) : ℕ) ≤ (clockSize T k : ℝ) ^ (5 : ℝ)
  atom : ∀ j : Fin D.geom.r,
    2 / ((D.encoding.base.latePool j).card : ℝ) * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) ≤
      (clockSize T k : ℝ) ^ (-(κ.Astar : ℝ))
  current : (3 * (T.S.n k + 1) ^ 2 * T.S.n k : ℕ) *
    Real.exp (-(T.S.n k : ℝ) ^ δ / 2) ≤ (clockSize T k : ℝ) ^ (-(κ.Pstar : ℝ))
  alarm : Real.exp (-(T.S.n k : ℝ) ^ δ / (2 * D.geom.r)) ≤
    (clockSize T k : ℝ) ^ (-(κ.Pstar : ℝ))

set_option maxHeartbeats 600000 in
private theorem clockBudget_of_scalars (hκ : κ.Admissible) (δ : ℝ)
    (hn : 2 ≤ T.S.n k) (hL : 48 ≤ Real.log (T.S.n k))
    (hr : (D.geom.r : ℝ) ≤ 2 * Real.log (T.S.n k) ^ 2)
    (hN : (2 : ℝ) ^ T.S.n k ≤ T.S.N k)
    (ha : (100 + 16 * (κ.Astar : ℝ)) * Real.log (T.S.n k) ^ 4 ≤ T.S.n k)
    (hp : (100 + 8 * (κ.Pstar : ℝ)) * Real.log (T.S.n k) ^ 6 ≤ (T.S.n k : ℝ) ^ δ) :
    ClockBudget D δ := by
  let n : ℝ := T.S.n k
  let L := Real.log n
  let z : ℝ := n ^ δ
  change (D.geom.r : ℝ) ≤ 2 * L ^ 2 at hr
  change (100 + 16 * (κ.Astar : ℝ)) * L ^ 4 ≤ n at ha
  change (100 + 8 * (κ.Pstar : ℝ)) * L ^ 6 ≤ z at hp
  have hn2 : 2 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hL48 : 48 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hA0 : 0 ≤ (κ.Astar : ℝ) := Nat.cast_nonneg _
  have hP0 : 0 ≤ (κ.Pstar : ℝ) := Nat.cast_nonneg _
  have hL4 : L ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hL24 : L ^ 2 ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hL46 : L ^ 4 ≤ L ^ 6 := by
    nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 1 by nlinarith) (pow_nonneg hL0 4)]
  have hL6 : L ≤ L ^ 6 := hL4.trans hL46
  have hnlarge : 100 * L ^ 4 ≤ n := by
    have hmul := mul_nonneg hA0 (pow_nonneg hL0 4)
    nlinarith only [ha, hmul]
  have hrn : (D.geom.r : ℝ) ≤ n := by nlinarith only [hr, hL24, hnlarge, sq_nonneg L]
  have hrnNat : D.geom.r ≤ T.S.n k := by
    change (D.geom.r : ℝ) ≤ (T.S.n k : ℝ) at hrn
    exact_mod_cast hrn
  obtain ⟨hclo, hcup, hnclock⟩ := clockSize_bounds hL
  have hc1 : 1 ≤ (clockSize T k : ℝ) := by linarith
  have hcfive : (clockSize T k : ℝ) ≤ (clockSize T k : ℝ) ^ (5 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (1 : ℝ) ≤ 5)
  have hs : (T.S.n k + 1 : ℝ) ^ (8 * D.geom.r + 8 : ℕ) ≤ (clockSize T k : ℝ) ^ (5 : ℝ) :=
    (spatialBudget (T.S.n k) D.geom.r hn hL hr).trans (hclo.trans hcfive)
  have hnegP := clockNegativeBudget hL (κ.Pstar : ℝ) hP0
  have hnegA := clockNegativeBudget hL (κ.Astar : ℝ) hA0
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith only [hh]
  have hNexp : Real.exp (n / 2) ≤ (T.S.N k : ℝ) := by
    calc
      _ ≤ Real.exp (Real.log 2 * n) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (2 : ℝ) ^ T.S.n k := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      _ ≤ _ := hN
  have hn12 : 12 * n ≤ Real.exp (n / 4) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 12 * n)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hn0.ne']
    have hlog12 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
    change Real.log 12 + L ≤ n / 4
    nlinarith only [hlog12, hL4, hnlarge, hL48]
  refine {
    n_pos := by omega
    clock_pos := by exact_mod_cast hc1
    labels := ?_
    tests := ?_
    scope := ?_
    incidence := ?_
    atom := ?_
    current := ?_
    alarm := ?_ }
  · have hNle : (T.S.N k : ℝ) ≤ n * (2 : ℝ) ^ T.S.n k := by
      dsimp [n]
      exact_mod_cast T.S.N_le k
    have hlogN := Real.log_le_log (by exact_mod_cast T.S.N_pos k) hNle
    rw [Real.log_mul hn0.ne' (by positivity), Real.log_pow] at hlogN
    have hlog2up := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlognup := Real.log_le_sub_one_of_pos hn0
    change Real.log (T.S.N k : ℝ) ≤ 2 * (clockSize T k : ℝ)
    change Real.log (T.S.N k : ℝ) ≤ L + n * Real.log 2 at hlogN
    change L ≤ n - 1 at hlognup
    nlinarith only [hlogN, hlog2up, hlognup, hnclock, hn0.le]
  · have hL34 : L ^ 3 ≤ L ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (pow_nonneg hL0 3)]
    exact (Real.exp_le_exp.mpr hL34).trans (hclo.trans hcfive)
  · exact (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ T.S.n k + 1) (by omega)).trans hs
  · have hi := incidenceBudget (T.S.n k) D.geom.r (by omega) hrnNat
    have hic : ((1 + 3 * D.geom.r * (T.S.n k + 1) ^ 2 * T.S.n k *
        (T.S.n k + 1) ^ (8 * D.geom.r + 2) : ℕ) : ℝ) ≤
        (T.S.n k + 1 : ℝ) ^ (8 * D.geom.r + 8 : ℕ) := by exact_mod_cast hi
    exact hic.trans hs
  · intro j
    have hN0 : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
    calc
      _ ≤ (12 * n / (T.S.N k : ℝ)) * Real.exp ((κ.α / 100) * n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact (latePool_inverse_bound D j).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrn (by norm_num)) hN0.le)
      _ ≤ (Real.exp (n / 4) / Real.exp (n / 2)) * Real.exp ((κ.α / 100) * n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact div_le_div₀ (by positivity) hn12 (Real.exp_pos _) hNexp
      _ = Real.exp (n / 4 - n / 2 + (κ.α / 100) * n) := by
        rw [← Real.exp_sub, ← Real.exp_add]
      _ ≤ Real.exp (-n / 8) := Real.exp_le_exp.mpr (by nlinarith only [hκ.α_rng.2, hn0.le])
      _ ≤ Real.exp (-2 * (κ.Astar : ℝ) * L ^ 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [ha, pow_nonneg hL0 4]
      _ ≤ _ := hnegA
  · have hpoly : ((3 * (T.S.n k + 1) ^ 2 * T.S.n k : ℕ) : ℝ) ≤ Real.exp (6 * L) := by
      have he : 12 * n ^ 3 ≤ Real.exp (6 * L) := by
        have h12 : 12 ≤ Real.exp (3 * L) := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 12)]
          apply Real.exp_le_exp.mpr
          have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
          linarith
        calc
          _ ≤ Real.exp (3 * L) * n ^ 3 := mul_le_mul_of_nonneg_right h12 (by positivity)
          _ = Real.exp (6 * L) := by
            rw [show n = Real.exp L from (Real.exp_log hn0).symm, ← Real.exp_nat_mul,
              ← Real.exp_add]
            congr 1; ring
      push_cast
      change 3 * (n + 1) ^ 2 * n ≤ Real.exp (6 * L)
      have hnp : n + 1 ≤ 2 * n := by linarith only [hn2]
      have hsq : (n + 1) ^ 2 ≤ (2 * n) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnp 2
      have hh := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 3 * n)
      exact (show 3 * (n + 1) ^ 2 * n ≤ 12 * n ^ 3 by nlinarith only [hh]).trans he
    calc
      _ ≤ Real.exp (6 * L) * Real.exp (-z / 2) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = Real.exp (6 * L - z / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-2 * (κ.Pstar : ℝ) * L ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hL46 hP0
        nlinarith only [hp, hL6, hh, pow_nonneg hL0 6]
      _ ≤ _ := hnegP
  · have hr0 : 0 < (D.geom.r : ℝ) := by exact_mod_cast D.l16_valid.r_pos
    apply le_trans _ hnegP
    apply Real.exp_le_exp.mpr
    have hz : 2 * (κ.Pstar : ℝ) * L ^ 4 ≤ z / (2 * D.geom.r) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * D.geom.r)).2
      have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4 * (κ.Pstar : ℝ) * L ^ 4)
      nlinarith only [hp, hh, pow_nonneg hL0 6]
    change -z / (2 * D.geom.r) ≤ -2 * (κ.Pstar : ℝ) * L ^ 4
    convert neg_le_neg hz using 1 <;> ring

theorem clockBudgetsEventually (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), ClockBudget D δ := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 48,
    Lane_sol_s18_n4.terminalScaleEventually κ T,
    T.S.ratio_tendsto.eventually_ge_atTop 1,
    logPowerEventually T 4 1 (100 + 16 * (κ.Astar : ℝ)) (by norm_num),
    logPowerEventually T 6 δ (100 + 8 * (κ.Pstar : ℝ)) hδ]
    with k hn2 hL hscale hratio ha hp
  intro PT hPT D
  change 48 ≤ Real.log (T.S.n k : ℝ) at hL
  obtain ⟨_, _, hrTs⟩ := hscale D
  have hTs : (D.encoding.Ts : ℝ) ≤ Real.log (T.S.n k) ^ 2 + 1 := by
    rw [D.encoding.Ts_eq]
    exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hr : (D.geom.r : ℝ) ≤ 2 * Real.log (T.S.n k) ^ 2 := by
    nlinarith only [hrTs, hTs, hL]
  have hN : (2 : ℝ) ^ T.S.n k ≤ T.S.N k := by
    have hpow : (0 : ℝ) < (2 : ℝ) ^ T.S.n k := by positivity
    simpa using (le_div_iff₀ hpow).mp hratio
  apply clockBudget_of_scalars D hκ δ hn2 hL hr hN
  · simpa using ha
  · exact hp

theorem classSamplerEventually (hκ : κ.Admissible) (T : Stage) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → S18.TransitionData D →
        Nonempty (S18.ClassSamplerData D δ) := by
  obtain ⟨n₀, ρ, hρ, hclock⟩ := localEnteringClockReduction hκ
  have hcost : ∀ᶠ k in atTop, 1 + ρ (clockSize T k) ≤ 2 := by
    filter_upwards [(hρ.comp (clockSize_tendsto T)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
    change ρ (clockSize T k) < 1 at hk
    linarith only [hk]
  filter_upwards [clockBudgetsEventually hκ T δ hδ,
    (clockSize_tendsto T).eventually_ge_atTop n₀, hcost] with k hbudget hlarge hcost
  intro PT hPT D hD H
  have B := hbudget D
  apply Lane_sol_s18_n4.classSamplerOfEnteringLaws D δ B.n_pos
  intro j h he
  apply hclock (clockSize T k) hlarge B.clock_pos hcost D δ j h hD H he
    B.labels B.tests
  · intro b y
    exact (Lane_sol_s18_n4.referenceLabelMarginalCap D H j b h y).trans (B.atom j)
  · exact B.scope
  · exact B.incidence
  · intro f
    cases f with
    | inl b =>
        exact (Lane_sol_s18_n4.classCurrentBadUniformBound D δ
          (Nat.lt_of_lt_of_le Nat.zero_lt_one B.n_pos) j h he b).trans B.current
    | inr f =>
        exact (Lane_sol_s18_n4.classFutureAlarmBound D δ j h he f).trans B.alarm

end HypercubeRamsey.Lane_sol_s18_4b
