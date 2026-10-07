import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S18.Sampler_sol_s18_n4
import HypercubeRamsey.S17.Nodes_q_s17_pool
import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.S18.Nodes_sol_s18_n5
import HypercubeRamsey.S18.Nodes_q_s18_n2
import HypercubeRamsey.S18.Locality_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_1c
open Classical Filter
open scoped BigOperators
open S18
set_option backward.isDefEq.respectTransparency false

private theorem uniformWeight_total {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) :
    (∑ y, if y ∈ S then (1 / (S.card : ℝ)) else 0) = 1 := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  field_simp

private theorem labelWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    0 ≤ D.labelWeight j side tests y := by
  unfold LateData.labelWeight
  split_ifs with hmass hpass
  · apply div_nonneg
    · unfold LateData.maskWeight
      split_ifs <;> positivity
    · exact (Real.exp_pos _).le.trans hmass
  · simp
  · unfold LateData.maskWeight
    split_ifs <;> positivity

private theorem labelWeight_total {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    (∑ y, D.labelWeight j side tests y) = 1 := by
  classical
  unfold LateData.labelWeight
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side tests
  · simp_rw [if_pos hmass]
    have hden : 0 < D.retainedMass j side tests :=
      (Real.exp_pos _).trans_le hmass
    calc
      (∑ y, if D.passes j side tests y then
          D.maskWeight side y / D.retainedMass j side tests else 0) =
          (∑ y, if D.passes j side tests y then D.maskWeight side y else 0) /
            D.retainedMass j side tests := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro y hy
              split_ifs <;> simp
      _ = D.retainedMass j side tests / D.retainedMass j side tests := by
        simp [LateData.retainedMass]
      _ = 1 := div_self (ne_of_gt hden)
  · simp_rw [if_neg hmass]
    have hmasktotal := uniformWeight_total side.1.1 hmask
    simpa [LateData.maskWeight] using hmasktotal

private theorem labelWeight_zero_of_not_mask {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k))
    (hy : y ∉ side.1.1) : D.labelWeight j side tests y = 0 := by
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side tests
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]

private noncomputable def lateLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    FinLaw {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} where
  w y := D.labelWeight j side tests y.1
  nonneg y := labelWeight_nonneg D j side tests y.1
  sum_one := by
    classical
    let pool := D.encoding.base.latePoolOf b
    have hzero (y : Fin (T.S.N k)) (hy : y ∉ pool) :
        D.labelWeight j side tests y = 0 := by
      apply labelWeight_zero_of_not_mask D j side tests y
      intro hmem
      exact hy (side.1.2.1 hmem)
    have hsubtype :
        (∑ y : {y : Fin (T.S.N k) // y ∈ pool}, D.labelWeight j side tests y.1) =
          ∑ y ∈ pool, D.labelWeight j side tests y := by
      simpa [pool] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Fin (T.S.N k))))
          (p := fun y => y ∈ pool) (f := fun y => D.labelWeight j side tests y))
    have hpoolSum : (∑ y ∈ pool, D.labelWeight j side tests y) =
        ∑ y, D.labelWeight j side tests y := by
      have hcomp : (∑ y ∈ Finset.univ \ pool, D.labelWeight j side tests y) = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact hzero y (Finset.mem_sdiff.mp hy).2
      calc
        (∑ y ∈ pool, D.labelWeight j side tests y) =
            (∑ y ∈ pool, D.labelWeight j side tests y) + 0 := by ring
        _ = ∑ y, D.labelWeight j side tests y := by
          rw [← Finset.sum_sdiff pool.subset_univ, hcomp]
          ring
    rw [hsubtype, hpoolSum]
    exact labelWeight_total D j side tests hmask

private theorem allowedMask_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b) : mask.1.Nonempty := by
  have hclass : D.geom.classOf b = some j := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
    simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hmaskpos : 0 < mask.1.card := by omega
  exact Finset.card_pos.mp hmaskpos

private noncomputable def rowSide {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b)
    (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :
    D.encoding.base.RowOut b := by
  let hclass : D.geom.classOf b = some j := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
    simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hpool : Nonempty {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} := by
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpoolpos
    exact ⟨⟨y, hy⟩⟩
  let y₀ : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} := Classical.choice hpool
  exact ⟨mask, (sketch, y₀)⟩

private noncomputable def asFinLaw {N : ℕ} (P : Law N) : FinLaw (Fin N) :=
  ⟨P.w, P.nonneg, P.sum_eq_one⟩

private noncomputable def rowSketchLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k)
    (h : D.encoding.base.History j.castSucc) :
    FinLaw (Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :=
  FinLaw.pi (fun a : Fin (T.S.n k) =>
    FinLaw.pi (fun t : Fin (sketchLength T k) =>
      asFinLaw (D.currentPrior j (flipPos b a) h)))

private theorem E_const {A : Type*} [Fintype A] (P : FinLaw A) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

private theorem pr_eq_E {A : Type*} [Fintype A] (P : FinLaw A) (A' : A → Prop) :
    P.pr A' = P.E (fun a => if A' a then 1 else 0) := by
  classical
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : A' a <;> simp [h]

private theorem E_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (P : ∀ i, FinLaw (A i))
    (i : I) (g : A i → ℝ) : (FinLaw.pi P).E (fun z => g (z i)) = (P i).E g := by
  let Q : ∀ i, FinProb (A i) := fun i => ⟨(P i).w, (P i).nonneg, (P i).sum_one⟩
  -- Use the singleton marginal via independence of the remaining coordinates.
  have hm := FinProb.pi_marginal_expect Q {i} (fun z => g (z ⟨i, by simp⟩))
  change (FinProb.pi Q).expect (fun z => g (z i)) = (Q i).expect g
  rw [hm]
  unfold FinProb.expect FinProb.pi
  -- A direct singleton-product sum avoids introducing an arbitrary inhabitant of A i.
  have hprod (z : ∀ j : {j : I // j ∈ ({i} : Finset I)}, A j.1) :
      (∏ j, (Q j.1).w (z j)) = (Q i).w (z ⟨i, by simp⟩) := by
    rw [Fintype.prod_eq_single ⟨i, by simp⟩]
    intro j hj
    have : j = ⟨i, by simp⟩ := Subtype.ext (by simpa only [Finset.mem_singleton] using j.2)
    exact (hj this).elim
  simp_rw [hprod]
  let ev : (∀ j : {j : I // j ∈ ({i} : Finset I)}, A j.1) ≃ A i :=
    { toFun := fun z => z ⟨i, by simp⟩
      invFun := fun a j => by
        have hji : j.1 = i := Finset.mem_singleton.mp j.2
        exact Eq.mp (congrArg A hji.symm) a
      left_inv := by intro z; funext j; have hj : j = ⟨i, by simp⟩ := Subtype.ext (by simpa only [Finset.mem_singleton] using j.2); subst j; rfl
      right_inv := by intro a; rfl }
  exact ev.sum_comp (fun a => (Q i).w a * g a)

private theorem E_sum {A I : Type*} [Fintype A] [Fintype I] (P : FinLaw A) (g : I → A → ℝ) :
    P.E (fun a => ∑ i, g i a) = ∑ i, P.E (g i) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem E_mul_const {A : Type*} [Fintype A] (P : FinLaw A) (g : A → ℝ) (c : ℝ) :
    P.E (fun a => g a * c) = P.E g * c := by
  unfold FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem E_div {A : Type*} [Fintype A] (P : FinLaw A) (g : A → ℝ) (c : ℝ) :
    P.E (fun a => g a / c) = P.E g / c := by
  simp only [div_eq_mul_inv, E_mul_const]

private theorem E_mono {A : Type*} [Fintype A] (P : FinLaw A) {f g : A → ℝ}
    (hfg : ∀ a, f a ≤ g a) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hfg a) (P.nonneg a)

private theorem E_mono_support {A : Type*} [Fintype A] (P : FinLaw A) {f g : A → ℝ}
    (hfg : ∀ a, P.w a ≠ 0 → f a ≤ g a) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.w a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (hfg a ha) (P.nonneg a)

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- A sketch of positive iid weight lies in the initial-prior support on the gate. -/
private theorem supported_rowSketch (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hg : D.gate j b h) (hb : b ∈ D.encoding.base.classes j)
    (s : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k))
    (hs : (rowSketchLaw D j b h).w s ≠ 0) (side : D.encoding.base.RowOut b)
    (hside : side.2.1 = s) : InitialSketchSupport D j h side := by
  intro a t
  rw [hside]
  have hx : (D.currentPrior j (flipPos b a) h).w (s a t) ≠ 0 := by
    have hp : (∏ a, ∏ t, (D.currentPrior j (flipPos b a) h).w (s a t)) ≠ 0 := hs
    exact (Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp a (Finset.mem_univ a)))
      t (Finset.mem_univ t)
  obtain ⟨hv, hm⟩ := Lane_sol_s18_n1_caps.gated_current_mass D hsmall j b h hg hb a
  intro hz
  apply hx
  rw [LateData.currentPrior, Lane_sol_s18_n1_caps.priorAt_weight D h _ hv hm]
  simp [Lane_sol_s18_n1_caps.rawWeight, hz]

private theorem labelWeight_side_congr (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} {side side' : D.encoding.base.RowOut b}
    (hm : side.1 = side'.1) (hs : side.2.1 = side'.2.1)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    D.labelWeight j side tests y = D.labelWeight j side' tests y := by
  cases side with
  | mk m r =>
    cases r with
    | mk s l =>
      cases side' with
      | mk m' r' =>
        cases r' with
        | mk s' l' =>
          dsimp at hm hs
          subst m'
          subst s'
          rfl

private theorem mem_foldl_union {A : Type*} [DecidableEq A] (L : List (Finset A))
    (S : Finset A) (a : A) :
    a ∈ L.foldl (fun S B => S ∪ B) S ↔ a ∈ S ∨ ∃ B ∈ L, a ∈ B := by
  induction L generalizing S with
  | nil => simp
  | cons B L ih => simp [ih, or_assoc, or_left_comm, or_comm]

/-- The base order ends with every coordinate tested. -/
theorem full_prefix (D : LateData hPT) (b : Pos T k) :
    ∃ order ∈ D.testOrders b, D.prefixTests order order.length = Finset.univ := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let base := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
    (if intern = ∅ then [] else [intern])
  refine ⟨base, ?_, ?_⟩
  · simp [LateData.testOrders, base, intern, extern]
  · ext a
    simp only [LateData.prefixTests, List.take_length, mem_foldl_union,
      Finset.notMem_empty, false_or, Finset.mem_univ, iff_true]
    dsimp [base]
    by_cases ha : a ∈ intern
    · have hi : intern ≠ ∅ := by intro he; simp [he] at ha
      exact ⟨intern, by simp [hi], ha⟩
    · have hae : a ∈ extern := by simp [extern, ha]
      exact ⟨{a}, List.mem_append_left _ (List.mem_map.mpr ⟨a, by simpa using hae, rfl⟩), by simp⟩

private theorem labelWeight_depends (D : LateData hPT) (j : Fin D.geom.r)
    (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b) (tests : Finset (Fin (T.S.n k)))
    (y : Fin (T.S.N k)) :
    FinProb.DependsOn (fun s => D.labelWeight j (rowSide D j b hb mask s) tests y) tests := by
  intro s s' heq
  have hpass (y : Fin (T.S.N k)) :
      D.passes j (rowSide D j b hb mask s) tests y ↔
      D.passes j (rowSide D j b hb mask s') tests y := by
    unfold LateData.passes
    constructor <;> intro hp a ha <;> simpa [LateData.sketchHit, rowSide, heq a ha] using hp a ha
  have hmass : D.retainedMass j (rowSide D j b hb mask s) tests =
      D.retainedMass j (rowSide D j b hb mask s') tests := by
    unfold LateData.retainedMass
    simp_rw [hpass]
    rfl
  change D.labelWeight j (rowSide D j b hb mask s) tests y = D.labelWeight j (rowSide D j b hb mask s') tests y
  unfold LateData.labelWeight
  rw [hmass, hpass]
  rfl

private noncomputable def empirical {A : Type*} {m : ℕ} (R : A → Prop) (s : Fin m → A) : ℝ :=
  (∑ t, if R (s t) then (1 : ℝ) else 0) / m

/-- A fixed low-mean label passes an independent target sketch with exponentially small mass. -/
theorem empirical_upper_tail {A : Type*} [Fintype A] (P : FinLaw A)
    (R : A → Prop) (m : ℕ) (hm : 0 < m) (e : ℝ) (he : 0 < e)
    (hmean : P.pr R < 1 / 2 - 3 * e) :
    (FinLaw.pi fun _ : Fin m => P).pr (fun s => 1 / 2 - e ≤ empirical R s) ≤
      2 * Real.exp (-2 * (m : ℝ) * e ^ 2) := by
  let Q : FinProb A := ⟨P.w, P.nonneg, P.sum_one⟩
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmeanEq : (FinLaw.pi fun _ : Fin m => P).E (empirical R) = P.pr R := by
    unfold empirical
    rw [E_div, E_sum]
    have heval (t : Fin m) : (FinLaw.pi fun _ : Fin m => P).E (fun s => if R (s t) then (1 : ℝ) else 0) = P.E (fun x => if R x then 1 else 0) := E_pi_eval (fun _ : Fin m => P) t (fun x => if R x then (1 : ℝ) else 0)
    simp_rw [heval]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← pr_eq_E]
    field_simp
  have hlip (i : Fin m) (s s' : Fin m → A) (hs : ∀ t, t ≠ i → s t = s' t) :
      |empirical R s - empirical R s'| ≤ 1 / (m : ℝ) := by
    have hbound (t : Fin m) :
        |(if R (s t) then (1 : ℝ) else 0) - (if R (s' t) then 1 else 0)| ≤
          if t = i then 1 else 0 := by
      by_cases ht : t = i
      · simp only [if_pos ht]; split_ifs <;> norm_num
      · simp [hs t ht, ht]
    unfold empirical
    rw [← sub_div, abs_div, abs_of_pos hm']
    apply div_le_div_of_nonneg_right _ hm'.le
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc
        _ ≤ ∑ t : Fin m, if t = i then (1 : ℝ) else 0 := Finset.sum_le_sum fun t _ => hbound t
        _ = 1 := by simp)
  have hwidth : (∑ t : Fin m, (1 / (m : ℝ)) ^ 2) = 1 / (m : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have htail := xMcDiarmid (fun _ : Fin m => Q) (empirical R) (fun _ => 1 / (m : ℝ))
    (fun _ => by positivity) hlip (by rw [hwidth]; positivity) e he
  change (FinLaw.pi fun _ : Fin m => P).pr
    (fun s => e ≤ |empirical R s - (FinLaw.pi fun _ : Fin m => P).E (empirical R)|) ≤ _ at htail
  have hmono : (FinLaw.pi fun _ : Fin m => P).pr (fun s => 1 / 2 - e ≤ empirical R s) ≤
      (FinLaw.pi fun _ : Fin m => P).pr
        (fun s => e ≤ |empirical R s - (FinLaw.pi fun _ : Fin m => P).E (empirical R)|) := by
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : 1 / 2 - e ≤ empirical R s
    · have hg : e ≤ |empirical R s - (FinLaw.pi fun _ : Fin m => P).E (empirical R)| := by
        rw [hmeanEq]
        exact (show e ≤ empirical R s - P.pr R by linarith).trans (le_abs_self _)
      simp only [if_pos hs, if_pos hg, le_refl]
    · simp only [if_neg hs]
      split_ifs <;> simp [P.nonneg, (FinLaw.pi fun _ : Fin m => P).nonneg s]
  apply hmono.trans
  rw [hwidth] at htail
  convert htail using 1
  congr 2
  field_simp

private theorem deleted_integral_le (D : LateData hPT) (j : Fin D.geom.r)
    (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (h : D.encoding.base.History j.castSucc) (mask : D.encoding.base.AllowedMask b)
    (tests : Finset (Fin (T.S.n k))) (a : Fin (T.S.n k)) (ha : a ∉ tests)
    (hm : 0 < sketchLength T k) (he : 0 < D.error (flipPos b a) j) :
    (rowSketchLaw D j b h).E (fun s =>
      (lateLabelLaw D j (rowSide D j b hb mask s) tests (allowedMask_nonempty D j b hb mask)).E
        (fun y => if colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b a) h) y.1 <
            1 / 2 - 3 * D.error (flipPos b a) j ∧
          1 / 2 - D.error (flipPos b a) j ≤ D.sketchHit (rowSide D j b hb mask s) a y.1
          then 1 else 0)) ≤
      2 * Real.exp (-2 * (sketchLength T k : ℝ) * D.error (flipPos b a) j ^ 2) := by
  classical
  let P := rowSketchLaw D j b h
  let tail := 2 * Real.exp (-2 * (sketchLength T k : ℝ) * D.error (flipPos b a) j ^ 2)
  let weights := fun (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) s =>
    D.labelWeight j (rowSide D j b hb mask s) tests y.1
  let bad := fun (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) s =>
    if colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b a) h) y.1 <
        1 / 2 - 3 * D.error (flipPos b a) j ∧
      1 / 2 - D.error (flipPos b a) j ≤ D.sketchHit (rowSide D j b hb mask s) a y.1 then (1 : ℝ) else 0
  have hind (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) :
      P.E (fun s => weights y s * bad y s) = P.E (weights y) * P.E (bad y) := by
    let Q := fun a => (⟨(FinLaw.pi fun _ : Fin (sketchLength T k) =>
      asFinLaw (D.currentPrior j (flipPos b a) h)).w,
      (FinLaw.pi fun _ : Fin (sketchLength T k) => asFinLaw (D.currentPrior j (flipPos b a) h)).nonneg,
      (FinLaw.pi fun _ : Fin (sketchLength T k) => asFinLaw (D.currentPrior j (flipPos b a) h)).sum_one⟩ :
      FinProb (Fin (sketchLength T k) → Fin (T.S.N k)))
    exact FinProb.pi_expect_mul_of_disjoint Q (weights y) (bad y) tests {a}
      (labelWeight_depends D j b hb mask tests y.1)
      (by intro s s' hs; have hsa := hs a (by simp); simp [bad, LateData.sketchHit, rowSide, hsa])
      (by simp [ha])
  have hbad (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) : P.E (bad y) ≤ tail := by
    by_cases hy : colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b a) h) y.1 <
        1 / 2 - 3 * D.error (flipPos b a) j
    · have hmean : (asFinLaw (D.currentPrior j (flipPos b a) h)).pr
          (fun x => Hits (T.S.E k) PT.tiling.c x y.1) < 1 / 2 - 3 * D.error (flipPos b a) j := by
        convert hy using 1
        unfold FinLaw.pr colDeg
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp [asFinLaw]
      have hh := empirical_upper_tail (asFinLaw (D.currentPrior j (flipPos b a) h))
        (fun x => Hits (T.S.E k) PT.tiling.c x y.1) (sketchLength T k) hm
        (D.error (flipPos b a) j) he hmean
      have heq : P.E (bad y) =
          (FinLaw.pi fun _ : Fin (sketchLength T k) => asFinLaw (D.currentPrior j (flipPos b a) h)).pr
            (fun s => 1 / 2 - D.error (flipPos b a) j ≤ empirical
              (fun x => Hits (T.S.E k) PT.tiling.c x y.1) s) := by
        simp only [bad, hy, true_and, LateData.sketchHit, rowSide, empirical]
        rw [pr_eq_E]
        exact E_pi_eval
          (fun a : Fin (T.S.n k) => FinLaw.pi fun _ : Fin (sketchLength T k) =>
            asFinLaw (D.currentPrior j (flipPos b a) h)) a
          (fun sketch => if 1 / 2 - D.error (flipPos b a) j ≤ empirical
            (fun x => Hits (T.S.E k) PT.tiling.c x y.1) sketch then (1 : ℝ) else 0)
      rw [heq]
      exact hh
    · simp only [bad, hy, false_and, if_false]
      rw [E_const]
      positivity
  have hweights0 (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) : 0 ≤ P.E (weights y) := by
    unfold FinLaw.E
    exact Finset.sum_nonneg fun s _ => mul_nonneg (P.nonneg s) (labelWeight_nonneg D j _ _ _)
  have htotal : (∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}, P.E (weights y)) = 1 := by
    rw [← E_sum]
    have heq : (fun s => ∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}, weights y s) =
        fun _ => (1 : ℝ) := by
      funext s
      exact (lateLabelLaw D j (rowSide D j b hb mask s) tests (allowedMask_nonempty D j b hb mask)).sum_one
    rw [heq, E_const]
  change _ ≤ tail
  calc
    _ = ∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}, P.E (fun s => weights y s * bad y s) := by
      change P.E (fun s => ∑ y, weights y s * bad y s) = _
      exact E_sum _ _
    _ = ∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}, P.E (weights y) * P.E (bad y) :=
      Finset.sum_congr rfl fun y _ => hind y
    _ ≤ ∑ y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}, P.E (weights y) * tail :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hbad y) (hweights0 y)
    _ = tail := by rw [← Finset.sum_mul, htotal, one_mul]

private theorem refK_integral (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (F : D.encoding.base.RowOut b.1 → ℝ) :
    (D.encoding.kernels.refK j b h).E F =
      (D.encoding.kernels.maskProfile b.1).E (fun mask =>
        (rowSketchLaw D j b.1 h).E (fun sketch =>
          (lateLabelLaw D j (rowSide D j b.1 b.2 mask sketch) Finset.univ
            (allowedMask_nonempty D j b.1 b.2 mask)).E (fun y => F (mask, sketch, y)))) := by
  unfold FinLaw.E
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro mask _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sketch _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [hT.reference_formula]
  have heq := labelWeight_side_congr D j
    (side := rowSide D j b.1 b.2 mask sketch) (side' := (mask, sketch, y)) rfl rfl Finset.univ y.1
  simp only [lateLabelLaw, rowSketchLaw, FinLaw.pi, asFinLaw]
  rw [heq]
  simp only [LateProcessBase.rowLabel]
  ring

private theorem error_pos (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) : 0 < D.error v j := by
  have hd : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold LateData.error lateError
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hd _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)

private theorem internal_patch (D : LateData hPT) (b : Pos T k) (a : Fin (T.S.n k))
    (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf b)) :
    D.geom.patchOf (flipPos b a) = D.geom.patchOf b := by
  have ha' : (PT.tiling.P (D.geom.patchOf b)).ℓ ≤ a.val := by
    let i := D.geom.patchOf b
    have hell : (PT.tiling.P i).ℓ ≤ Finset.univ.sup (fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) :=
      Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
    have hh : (PT.tiling.P i).h ≤ Finset.univ.sup (fun j : Fin PT.tiling.m => (PT.tiling.P j).h) :=
      Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
    have hlen := hPT.tiling_valid.prefix_internal_length
    have hat : T.S.n k - (PT.tiling.P i).h ≤ a.val := (Finset.mem_filter.mp ha).2
    dsimp [i] at hell hh hat
    omega
  have hleaf : flipPos b a ∈ PT.tiling.leaf (D.geom.patchOf b) := by
    intro t ht
    have hta : t ≠ a := by intro heq; subst t; omega
    simpa [flipPos, hta] using D.geom.patchOf_leaf b t ht
  obtain ⟨i, hi, hu⟩ := hPT.tiling_valid.prefix_complete (flipPos b a)
  exact (hu _ (D.geom.patchOf_leaf _)).trans (hu _ hleaf).symm

private theorem deletion_multiplier_le_two (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (a : Fin (T.S.n k)) :
    Real.exp (1000 * ((if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then
      (PT.tiling.P (D.geom.patchOf b)).h else 1 : ℕ) : ℝ) * D.error (flipPos b a) j) ≤ 2 := by
  let v := flipPos b a
  let l : ℕ := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
  have hl : (l : ℝ) ≤ (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) := by
    dsimp [l, v]
    split_ifs with ha
    · rw [internal_patch D b a ha]
      exact_mod_cast le_max_right 1 (PT.tiling.P (D.geom.patchOf b)).h
    · exact_mod_cast le_max_left 1 (PT.tiling.P (D.geom.patchOf (flipPos b a))).h
  have he : D.error v j ≤ ∑ i : Fin D.geom.r, D.error v i :=
    Finset.single_le_sum (fun i _ => (error_pos D v i).le) (Finset.mem_univ j)
  have hbound : (l : ℝ) * D.error v j ≤ Real.log 2 / 1000 := by
    calc
      _ ≤ (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * D.error v j :=
        mul_le_mul_of_nonneg_right hl (error_pos D v j).le
      _ ≤ (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * ∑ i : Fin D.geom.r, D.error v i :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := hsmall _
  change Real.exp (1000 * (l : ℝ) * D.error v j) ≤ 2
  calc
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- Delete the target test before integrating its independent sketch. -/
theorem coordinate_trueHit_tail (D : LateData hPT) (hT : TransitionData D) (K27 : ℝ)
    (hB : BroadDeletionFacts D K27)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hg : D.gate j b.1 h)
    (hm : 0 < sketchLength T k) (a : Fin (T.S.n k)) :
    (D.encoding.kernels.refK j b h).pr (fun out => D.R1 j out ∧ D.R2 j h out ∧
      colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h)
        (D.encoding.base.rowLabel out) < 1 / 2 - 3 * D.error (flipPos b.1 a) j) ≤
      4 * Real.exp (-2 * (sketchLength T k : ℝ) * D.error (flipPos b.1 a) j ^ 2) := by
  let omitted := if a ∈ PT.tiling.Icoord (D.geom.patchOf b.1) then
    PT.tiling.Icoord (D.geom.patchOf b.1) else {a}
  let tests := Finset.univ \ omitted
  have ha : a ∉ tests := by dsimp [tests, omitted]; split_ifs <;> simp_all
  rw [pr_eq_E, refK_integral D hT]
  have hpoint (mask : D.encoding.base.AllowedMask b.1)
      (s : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k))
      (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1})
      (hs : (rowSketchLaw D j b.1 h).w s ≠ 0) :
      D.labelWeight j (rowSide D j b.1 b.2 mask s) Finset.univ y.1 *
        (if D.R1 j (mask, s, y) ∧ D.R2 j h (mask, s, y) ∧
          colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h) y.1 <
            1 / 2 - 3 * D.error (flipPos b.1 a) j then 1 else 0) ≤
      2 * (D.labelWeight j (rowSide D j b.1 b.2 mask s) tests y.1 *
        (if colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h) y.1 <
            1 / 2 - 3 * D.error (flipPos b.1 a) j ∧
          1 / 2 - D.error (flipPos b.1 a) j ≤ D.sketchHit (rowSide D j b.1 b.2 mask s) a y.1
          then 1 else 0)) := by
    have hnonneg := labelWeight_nonneg D j (rowSide D j b.1 b.2 mask s) tests y.1
    by_cases hgood : D.R1 j (mask, s, y) ∧ D.R2 j h (mask, s, y) ∧
      colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h) y.1 <
        1 / 2 - 3 * D.error (flipPos b.1 a) j
    · obtain ⟨hprefix, hdelete, _⟩ := hB j b.1 h (mask, s, y) b.2 hg
        (supported_rowSketch D hsmall j b.1 h hg b.2 s hs _ rfl) hgood.1 hgood.2.1
      obtain ⟨order, ho, hfull⟩ := full_prefix D b.1
      have hbroad := hprefix order ho order.length le_rfl
      rw [hfull] at hbroad
      by_cases hp : D.passes j (mask, s, y) Finset.univ y.1
      · have hpa : 1 / 2 - D.error (flipPos b.1 a) j ≤ D.sketchHit (rowSide D j b.1 b.2 mask s) a y.1 :=
          hp a (Finset.mem_univ a)
        have hbadpass : colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h) y.1 <
            1 / 2 - 3 * D.error (flipPos b.1 a) j ∧
          1 / 2 - D.error (flipPos b.1 a) j ≤ D.sketchHit (rowSide D j b.1 b.2 mask s) a y.1 := ⟨hgood.2.2, hpa⟩
        simp only [if_pos hgood, if_pos hbadpass, mul_one]
        have hd := hdelete a y.1
        have hside := labelWeight_side_congr D j
          (side := (mask, s, y)) (side' := rowSide D j b.1 b.2 mask s) rfl rfl
        rw [hside Finset.univ y.1, hside tests y.1] at hd
        exact hd.trans (mul_le_mul_of_nonneg_right
          (deletion_multiplier_le_two D hsmall j b.1 a) (labelWeight_nonneg D j _ _ _))
      · have hz : D.labelWeight j (rowSide D j b.1 b.2 mask s) Finset.univ y.1 = 0 := by
          rw [labelWeight_side_congr D j (side := rowSide D j b.1 b.2 mask s) (side' := (mask, s, y)) rfl rfl Finset.univ y.1]
          simp only [LateData.labelWeight, if_pos hbroad, if_neg hp]
        simp only [hz, zero_mul]
        positivity
    · simp only [if_neg hgood, mul_zero]
      positivity
  calc
    _ ≤ (D.encoding.kernels.maskProfile b.1).E (fun mask =>
        (rowSketchLaw D j b.1 h).E (fun s => 2 *
          (lateLabelLaw D j (rowSide D j b.1 b.2 mask s) tests
            (allowedMask_nonempty D j b.1 b.2 mask)).E
            (fun y => if colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h) y.1 <
                1 / 2 - 3 * D.error (flipPos b.1 a) j ∧
              1 / 2 - D.error (flipPos b.1 a) j ≤ D.sketchHit (rowSide D j b.1 b.2 mask s) a y.1
              then 1 else 0))) := by
      apply E_mono
      intro mask
      apply E_mono_support
      intro s hs
      unfold FinLaw.E
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      convert hpoint mask s y hs using 1 <;> congr 1
      dsimp only [LateProcessBase.rowLabel]
      split_ifs <;> rfl
    _ ≤ (D.encoding.kernels.maskProfile b.1).E (fun _ =>
        4 * Real.exp (-2 * (sketchLength T k : ℝ) * D.error (flipPos b.1 a) j ^ 2)) := by
      apply E_mono
      intro mask
      have hh := deleted_integral_le D j b.1 b.2 h mask tests a ha hm (error_pos D _ _)
      have htwo := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 by norm_num)
      convert htwo using 1
      · unfold FinLaw.E
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      · ring
    _ = _ := E_const _ _

private theorem pr_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (P : FinLaw A) (B : I → A → Prop) : P.pr (fun a => ∃ i, B i a) ≤ ∑ i, P.pr (B i) := by
  simp only [pr_eq_E]
  rw [← E_sum]
  apply E_mono
  intro a
  by_cases hex : ∃ i, B i a
  · obtain ⟨i, hi⟩ := hex
    simp only [if_pos (show ∃ i, B i a from ⟨i, hi⟩)]
    calc
      (1 : ℝ) = if B i a then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if B j a then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if B j a then (1 : ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · simp only [if_neg hex]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

/-- The coordinate estimates retain R1 and R2 and are summed without conditioning on them. -/
theorem trueHit_tail (D : LateData hPT) (hT : TransitionData D) (K27 : ℝ)
    (hB : BroadDeletionFacts D K27)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (hn : 0 < (T.S.n k : ℝ))
    (hlower : ∀ i (j : Fin D.geom.r), Real.rpow (T.S.n k : ℝ) (-0.02) ≤
      lateError κ T k PT i (D.geom.r - j.val))
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hg : D.gate j b.1 h) :
    (D.encoding.kernels.refK j b h).pr (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out) ≤
      4 * (T.S.n k : ℝ) * Real.exp (-2 * Real.rpow (T.S.n k : ℝ) 0.21) := by
  let n : ℝ := T.S.n k
  let m := sketchLength T k
  have hmc : Real.rpow n 0.25 ≤ (m : ℝ) := Nat.le_ceil _
  have hm' : 0 < (m : ℝ) := (Real.rpow_pos_of_pos hn _).trans_le hmc
  have hm : 0 < m := by exact_mod_cast hm'
  have hprod (a : Fin (T.S.n k)) : Real.rpow n 0.21 ≤ (m : ℝ) * D.error (flipPos b.1 a) j ^ 2 := by
    have he := hlower (D.geom.patchOf (flipPos b.1 a)) j
    change Real.rpow n (-0.02) ≤ D.error (flipPos b.1 a) j at he
    have hpowid : Real.rpow n 0.25 * (Real.rpow n (-0.02)) ^ 2 = Real.rpow n 0.21 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      norm_num
      rfl
    rw [← hpowid]
    exact mul_le_mul hmc (pow_le_pow_left₀ (Real.rpow_nonneg hn.le _) he 2)
      (sq_nonneg _) hm'.le
  have hmono : (D.encoding.kernels.refK j b h).pr (fun out => D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out) ≤
      (D.encoding.kernels.refK j b h).pr (fun out => ∃ a : Fin (T.S.n k),
        D.R1 j out ∧ D.R2 j h out ∧
        colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h)
          (D.encoding.base.rowLabel out) < 1 / 2 - 3 * D.error (flipPos b.1 a) j) := by
    unfold FinLaw.pr
    apply Finset.sum_le_sum
    intro out _
    by_cases hs : D.R1 j out ∧ D.R2 j h out ∧ ¬ D.R3 j h out
    · have hex : ∃ a : Fin (T.S.n k), D.R1 j out ∧ D.R2 j h out ∧
          colDeg (T.S.E k) PT.tiling.c (D.currentPrior j (flipPos b.1 a) h)
            (D.encoding.base.rowLabel out) < 1 / 2 - 3 * D.error (flipPos b.1 a) j := by
        obtain ⟨a, ha⟩ := not_forall.mp hs.2.2
        exact ⟨a, hs.1, hs.2.1, lt_of_not_ge ha⟩
      simp only [if_pos hs, if_pos hex, le_refl]
    · simp only [if_neg hs]
      split_ifs <;> simp [(D.encoding.kernels.refK j b h).nonneg]
  apply hmono.trans
  apply (pr_exists_le _ _).trans
  calc
    _ ≤ ∑ a : Fin (T.S.n k), 4 * Real.exp (-2 * (m : ℝ) * D.error (flipPos b.1 a) j ^ 2) :=
      Finset.sum_le_sum fun a _ => coordinate_trueHit_tail D hT K27 hB hsmall j b h hg hm a
    _ ≤ ∑ a : Fin (T.S.n k), 4 * Real.exp (-2 * Real.rpow n 0.21) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hprod a])) (by norm_num)
    _ = _ := by simp [n]; ring

/-- The fixed .04 exponent absorbs the union over targets and the deletion multiplier. -/
theorem numerical_cutoff (T : Stage) :
    ∀ᶠ k in atTop, 4 * (T.S.n k : ℝ) * Real.exp (-2 * Real.rpow (T.S.n k : ℝ) 0.21) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hslow := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.17)).comp hn).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hx := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.21)).comp hn
  have hfast0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 0.21 : ℝ) 1 (by norm_num)).comp hx
  have hfast : Tendsto (fun k => 4 * (T.S.n k : ℝ) * Real.exp (-Real.rpow (T.S.n k : ℝ) 0.21)) atTop (nhds 0) := by
    have hh := hfast0.const_mul 4
    apply (show Tendsto (fun k => 4 * (Real.rpow (Real.rpow (T.S.n k : ℝ) 0.21) (1 / 0.21) *
      Real.exp (-(1 : ℝ) * Real.rpow (T.S.n k : ℝ) 0.21))) atTop (nhds 0) from by simpa using hh).congr'
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hk.le]
    norm_num
    ring
  have hfastEvent := hfast.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hslow, hfastEvent, hn.eventually_gt_atTop 0] with k hs hf hp
  let n : ℝ := T.S.n k
  have hsmallpow : Real.rpow n 0.04 ≤ Real.rpow n 0.21 := by
    have heq : Real.rpow n 0.04 = Real.rpow n (-0.17) * Real.rpow n 0.21 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hp]
      norm_num
      rfl
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hp.le _)).trans_eq (one_mul _)
  calc
    _ = (4 * n * Real.exp (-Real.rpow n 0.21)) * Real.exp (-Real.rpow n 0.21) := by
      change 4 * n * Real.exp (-2 * Real.rpow n 0.21) = _
      rw [mul_assoc (4 * n), ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-Real.rpow n 0.21) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hf.le (Real.exp_nonneg (-Real.rpow n 0.21))
    _ ≤ Real.exp (-Real.rpow n 0.04) := Real.exp_le_exp.mpr (by linarith)

/-- A finite seed table implements every conditional finite law. The table's law
is fixed before an input is selected; evaluation has the required marginal. -/
theorem independent_kernel_seeds {A B : Type*} [Fintype A] [Fintype B]
    (K : A → FinLaw B) :
    ∃ seedLaw : FinLaw (A → B), ∀ a, FinLaw.map seedLaw (fun seed => seed a) = K a := by
  refine ⟨FinLaw.pi K, ?_⟩
  intro a
  have hw (y : B) : (FinLaw.map (FinLaw.pi K) (fun seed => seed a)).w y = (K a).w y := by
    have heq := E_pi_eval K a (fun b => if b = y then (1 : ℝ) else 0)
    unfold FinLaw.E at heq
    have hr : (∑ b, (K a).w b * (if b = y then (1 : ℝ) else 0)) = (K a).w y := by simp
    rw [hr] at heq
    change (∑ seed, if seed a = y then (FinLaw.pi K).w seed else 0) = _
    convert heq using 1
    apply Finset.sum_congr rfl
    intro seed _
    by_cases hs : seed a = y <;> simp only [hs, ite_true, ite_false, mul_one, mul_zero]
  generalize hP : FinLaw.map (FinLaw.pi K) (fun seed => seed a) = P at *
  generalize hQ : K a = Q at *
  cases P
  cases Q
  congr 1
  exact funext hw

/-- The total prefix draw, including the mandated mask fallback. -/
noncomputable def prefixLabelLaw (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k)))
    (hmask : side.1.1.Nonempty) : Law (T.S.N k) where
  w := D.labelWeight j side tests
  nonneg := labelWeight_nonneg D j side tests
  sum_eq_one := labelWeight_total D j side tests hmask

/-- A scalar late-pool cutoff suffices for broadness of every protocol output,
including an abort output obtained by using the empty test set. -/
theorem prefixLabelLaw_broad (D : LateData hPT) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (side : D.encoding.base.RowOut b.1) (tests : Finset (Fin (T.S.n k)))
    (hcutoff : 2 / ((D.encoding.base.latePool j).card : ℝ) *
      Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) ≤ Real.exp (κ.α * T.S.n k / 2) / T.S.N k) :
    (prefixLabelLaw D j side tests (allowedMask_nonempty D j b.1 b.2 side.1)).WidthLE
      (κ.α * T.S.n k / 2) := by
  intro y
  exact (Lane_sol_s18_n4.labelWeightCap D j b side tests y).trans hcutoff

private theorem pool_ratio_le (D : LateData hPT) (j : Fin D.geom.r) :
    2 * (T.S.N k : ℝ) / (D.encoding.base.latePool j).card ≤ 12 * (D.geom.r : ℝ) := by
  have hpool := D.encoding.base.latePool_card j
  rw [Nat.div_div_eq_div_mul] at hpool
  have hmod := Nat.mod_lt (T.S.N k) (show 0 < 3 * D.geom.r by have hr := D.l16_valid.r_pos; omega)
  have heq := Nat.mod_add_div (T.S.N k) (3 * D.geom.r)
  have hpoolpos := D.late_pool_pos j
  have hN : T.S.N k ≤ 6 * D.geom.r * (D.encoding.base.latePool j).card := by
    rw [← hpool] at heq
    have hm := Nat.mul_le_mul_left (3 * D.geom.r)
      (show 1 ≤ (D.encoding.base.latePool j).card by omega)
    nlinarith
  have hcast : (T.S.N k : ℝ) ≤ 6 * (D.geom.r : ℝ) * (D.encoding.base.latePool j).card := by
    exact_mod_cast hN
  apply (div_le_iff₀ (Nat.cast_pos.mpr hpoolpos)).mpr
  nlinarith

/-- The paper's broad-output cutoff is uniform over the late pool and all histories. -/
theorem eventually_prefixLabelLaw_broad (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
        (side : D.encoding.base.RowOut b.1) (tests : Finset (Fin (T.S.n k))),
      (prefixLabelLaw D j side tests (allowedMask_nonempty D j b.1 b.2 side.1)).WidthLE
        (κ.α * T.S.n k / 2) := by
  let R : ℝ := 2 * κ.A0 / Real.log 2
  let δ : ℝ := 49 * κ.α / 100
  have hA0 : 0 < κ.A0 := by
    have hP : 0 < κ.P := by have hbig := hκ.P_big.2; omega
    have hRpos : 0 < κ.R := by rw [hκ.R_eq]; positivity
    have hbound := hκ.A0_big
    norm_num at hbound
    have hRreal : 0 < (κ.R : ℝ) := by exact_mod_cast hRpos
    linarith
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (by positivity) (Real.log_pos (by norm_num))
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (by norm_num) hκ.α_rng.1) (by norm_num)
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hfast : Tendsto (fun k => 12 * R * (T.S.n k : ℝ) * Real.exp (-δ * T.S.n k)) atTop (nhds 0) := by
    have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) δ hδ).comp hn).const_mul (12 * R)
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero, mul_assoc] using hh
  have he := hfast.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he, T.S.n_tendsto.eventually_ge_atTop 1] with k he hn
  intro PT hPT D j b side tests
  apply prefixLabelLaw_broad D j b side tests
  have hn' : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hr : (D.geom.r : ℝ) ≤ R * T.S.n k := by
    have hlog : Real.log (T.S.n k : ℝ) ≤ T.S.n k :=
      (Real.log_le_sub_one_of_pos hn').trans (by linarith)
    have hh := D.l16_valid.r_upper
    have hb : (D.geom.r : ℝ) * Real.log 2 ≤ 2 * κ.A0 * T.S.n k :=
      hh.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    dsimp [R]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
    nlinarith
  have hnum : 12 * R * (T.S.n k : ℝ) ≤ Real.exp (δ * T.S.n k) := by
    have hm := mul_le_mul_of_nonneg_right he.le (Real.exp_nonneg (δ * T.S.n k))
    have hx : Real.exp (-δ * T.S.n k) * Real.exp (δ * T.S.n k) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    simpa only [mul_assoc, hx, mul_one, one_mul] using hm
  apply (le_div_iff₀ hN).mpr
  calc
    _ = (2 * (T.S.N k : ℝ) / (D.encoding.base.latePool j).card) *
        Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) := by ring
    _ ≤ 12 * (D.geom.r : ℝ) * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) :=
      mul_le_mul_of_nonneg_right (pool_ratio_le D j) (Real.exp_nonneg _)
    _ ≤ (12 * R * (T.S.n k : ℝ)) * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith
    _ ≤ Real.exp (δ * T.S.n k) * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) :=
      mul_le_mul_of_nonneg_right hnum (Real.exp_nonneg _)
    _ = Real.exp (κ.α * T.S.n k / 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [δ]
      ring

/-- Every retained critical coordinate is an external early input to the target. -/
theorem criticalCoords_externalEarly (D : LateData hPT) (X : CriticalTransferData D) :
    X.criticalCoords ⊆ D.externalEarly X.target := by
  intro a ha
  have hbulk := (Finset.mem_filter.mp ha).1
  have hnot := (Finset.mem_filter.mp ha).2.1
  have hneg : -(D.geom.syndrome X.target) = D.geom.syndrome X.target := by
    have hz : D.geom.syndrome X.target + D.geom.syndrome X.target = 0 := by
      ext t
      change D.geom.syndrome X.target t + D.geom.syndrome X.target t = 0
      rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
    calc
      -(D.geom.syndrome X.target) = -(D.geom.syndrome X.target) +
          (D.geom.syndrome X.target + D.geom.syndrome X.target) := by rw [hz, add_zero]
      _ = D.geom.syndrome X.target := by abel
  have hsynd : D.geom.syndrome (flipPos X.target a) ∉ D.geom.Lsub := by
    rw [Lane_q_s17_pool.lowGeom_syndrome_flip]
    have heq : D.geom.ids a - D.geom.syndrome X.target = D.geom.syndrome X.target + D.geom.ids a := by
      rw [sub_eq_add_neg, hneg, add_comm]
    simpa only [heq] using hnot
  have hearly : D.geom.classOf (flipPos X.target a) = none := by
    simp [LowGeom.classOf, hsynd]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hbulk).2.2, hearly⟩

/-- An initial-list witness necessarily survives every retained critical hit. -/
theorem initialWeight_critical_hits (D : LateData hPT) (X : CriticalTransferData D)
    (s : X.Raw) (x : Fin (T.S.N k))
    (hx : D.initialWeight X.target (X.state s) x ≠ 0) :
    X.survives s x none := by
  intro a ha
  refine ⟨?_, by simp⟩
  have hearly := criticalCoords_externalEarly D X ha
  have hprod : ∏ a ∈ D.externalEarly X.target,
      (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel (X.state s) (flipPos X.target a)) then 1 else 0) /
        rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos X.target a))) ≠ 0 := by
    intro hz
    apply hx
    simp [LateData.initialWeight, hz]
  have hf := Finset.prod_ne_zero_iff.mp hprod a hearly
  by_contra hno
  exact hf (by simp only [CriticalTransferData.criticalLabel] at hno; simp [hno])

/-- The normalized prefix law has exactly the moments appearing in Requirement 2. -/
theorem prefixLabelLaw_rowDeg (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k)))
    (hm : side.1.1.Nonempty)
    (hbroad : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests)
    (x : Fin (T.S.N k)) :
    rowDeg (T.S.E k) PT.tiling.c x (prefixLabelLaw D j side tests hm) =
      (∑ y, if D.passes j side tests y ∧ Hits (T.S.E k) PT.tiling.c x y
        then D.maskWeight side y else 0) / D.retainedMass j side tests := by
  unfold rowDeg prefixLabelLaw
  simp only [LateData.labelWeight, if_pos hbroad]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp : D.passes j side tests y <;>
    by_cases hh : Hits (T.S.E k) PT.tiling.c x y <;> simp [hp, hh]

private theorem prefixLabelLaw_pair (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k)))
    (hm : side.1.1.Nonempty)
    (hbroad : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests)
    (x z : Fin (T.S.N k)) :
    (∑ y, (prefixLabelLaw D j side tests hm).w y *
      (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y then 1 else 0)) =
      (∑ y, if D.passes j side tests y ∧ Hits (T.S.E k) PT.tiling.c x y ∧
        Hits (T.S.E k) PT.tiling.c z y then D.maskWeight side y else 0) / D.retainedMass j side tests := by
  unfold prefixLabelLaw
  simp only [LateData.labelWeight, if_pos hbroad]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp : D.passes j side tests y <;>
    by_cases hx : Hits (T.S.E k) PT.tiling.c x y <;>
    by_cases hz : Hits (T.S.E k) PT.tiling.c z y <;> simp [hp, hx, hz]

/-- A genuine prefix failure supplies a supported singleton or nonconflicting
pair witness for the actual normalized prefix law. -/
theorem prefixFailure_witness (D : LateData hPT) (X : CriticalTransferData D)
    (H : D.encoding.base.History (Fin.last D.geom.r)) (hbad : D.prefixFailure X.failure H) :
    let side := D.pastRows H X.failure.1 X.failure.1.isLt X.failure.2.1
    let tests := D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val
    let U := prefixLabelLaw D X.failure.1 side tests
      (allowedMask_nonempty D X.failure.1 X.failure.2.1.1 X.failure.2.1.2 side.1)
    ∃ x z, (D.initialPrior X.target H.1).w x ≠ 0 ∧
      (∀ y, z = some y → (D.initialPrior X.target H.1).w y ≠ 0 ∧ D.nonconflict X.target x y) ∧
      X.deviates U x z := by
  classical
  let side := D.pastRows H X.failure.1 X.failure.1.isLt X.failure.2.1
  let tests := D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val
  let hm := allowedMask_nonempty D X.failure.1 X.failure.2.1.1 X.failure.2.1.2 side.1
  have hf := hbad.2.2
  simp only [LateData.prefixMoments, not_imp, not_and_or, not_forall, not_le] at hf
  rcases hf with ⟨hbroad, hsingle | hpair⟩
  · obtain ⟨x, hx, hd⟩ := hsingle
    refine ⟨x, none, hx, by simp, ?_⟩
    change 10 * bstar T k < |rowDeg (T.S.E k) PT.tiling.c x (prefixLabelLaw D X.failure.1 side tests hm) - 1 / 2|
    rw [prefixLabelLaw_rowDeg D X.failure.1 side tests hm hbroad]
    exact hd
  · obtain ⟨x, z, hx, hz, hnc, hd⟩ := hpair
    refine ⟨x, some z, hx, ?_, ?_⟩
    · intro y hy
      cases Option.some.inj hy
      exact ⟨hz, hnc⟩
    · change 10 * bstar T k < |(∑ y, (prefixLabelLaw D X.failure.1 side tests hm).w y *
        (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y then 1 else 0)) - 1 / 4|
      rw [prefixLabelLaw_pair D X.failure.1 side tests hm hbroad]
      exact hd

private theorem initialWeight_envelope (D : LateData hPT) (v : Pos T k) (s : Config D.fresh)
    (hv : D.initialValid v s) (x : Fin (T.S.N k)) (hx : D.initialWeight v s x ≠ 0) :
    x ∈ PT.envelope (D.geom.patchOf v) := by
  obtain ⟨q, hq, hs⟩ := hv.1.2.2.2.1
  have hσ : D.sigma v s x ≠ 0 := by
    intro hz
    apply hx
    simp [LateData.initialWeight, hz]
  have hc : x ∈ PT.mesh.corner q (D.geom.patchOf v) := by
    by_contra hn
    exact hσ (hs x hn)
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨q, hq, hc⟩

/-- Before history erasure, the actual failure supplies the allowed witness and
all critical survival indicators used in the transfer reduction. -/
theorem prefixFailure_surviving_witness (D : LateData hPT) (X : CriticalTransferData D)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (s : X.Raw) (H : D.encoding.base.History (Fin.last D.geom.r))
    (hs : H.1 = X.state s) (hbad : D.prefixFailure X.failure H) :
    let side := D.pastRows H X.failure.1 X.failure.1.isLt X.failure.2.1
    let tests := D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val
    let U := prefixLabelLaw D X.failure.1 side tests
      (allowedMask_nonempty D X.failure.1 X.failure.2.1.1 X.failure.2.1.2 side.1)
    ∃ x z, X.allowed x z ∧ X.survives s x z ∧ X.deviates U x z := by
  obtain ⟨x, z, hx, hz, hd⟩ := prefixFailure_witness D X H hbad
  have hv : D.initialValid X.target H.1 := by
    exact (Lane_sol_s18_n1_caps.gated_current_mass D hsmall X.failure.1 X.failure.2.1.1
      (D.beforeHistory H X.failure.1.castSucc (Nat.le_of_lt X.failure.1.isLt))
      hbad.2.1 X.failure.2.1.2 X.failure.2.2.2.2).1
  have hweight := (S18.Lane_sol_s18_n5.initialPrior_support D X.target H.1 hv x hx).2
  have hex := initialWeight_envelope D X.target H.1 hv x hweight
  have hhits := initialWeight_critical_hits D X s x (by simpa only [hs] using hweight)
  refine ⟨x, z, ⟨hex, ?_⟩, ?_, hd⟩
  · intro y hy
    obtain ⟨hys, hnc⟩ := hz y hy
    have hyweight := (S18.Lane_sol_s18_n5.initialPrior_support D X.target H.1 hv y hys).2
    exact ⟨initialWeight_envelope D X.target H.1 hv y hyweight, hnc⟩
  · intro a ha
    refine ⟨(hhits a ha).1, ?_⟩
    intro y hy
    obtain ⟨hys, hnc⟩ := hz y hy
    have hyweight := (S18.Lane_sol_s18_n5.initialPrior_support D X.target H.1 hv y hys).2
    exact (initialWeight_critical_hits D X s y (by simpa only [hs] using hyweight) a ha).1

/-- Every positive-weight reference history keeps its starting configuration. -/
theorem runFrom_initial_support (D : LateData hPT)
    (step : ∀ j : Fin D.geom.r, D.encoding.base.History j.castSucc → FinLaw (D.encoding.base.ClassRows j))
    (s : Config D.fresh) (m : ℕ) (hm : m ≤ D.geom.r)
    (H : D.encoding.base.History ⟨m, Nat.lt_succ_of_le hm⟩)
    (hH : (D.encoding.base.runFrom step s m hm).w H ≠ 0) : H.1 = s := by
  induction m with
  | zero =>
    have h : H = D.encoding.base.initialHistory s := by
      by_contra hne
      apply hH
      simp [LateProcessBase.runFrom, FinLaw.dirac, hne]
    rw [h]
    rfl
  | succ m ih =>
    by_contra hne
    apply hH
    unfold LateProcessBase.runFrom FinLaw.map
    apply Finset.sum_eq_zero
    intro pair _
    by_cases heq : D.encoding.base.extend ⟨m, hm⟩ pair.1 pair.2 = H
    · by_cases hw : (D.encoding.base.runFrom step s m (Nat.le_of_succ_le hm)).w pair.1 = 0
      · simp [heq, FinLaw.bind, hw]
      · have hstart := ih (Nat.le_of_succ_le hm) pair.1 hw
        have hfst := congrArg Prod.fst heq
        exact False.elim (hne (hfst.symm.trans hstart))
    · simp [heq]

/-- The experiment's prefix-failure mass is bounded by its actual surviving
witness event. History deletion is still needed to turn this into a local protocol. -/
theorem experiment_failure_le_surviving_witness (D : LateData hPT) (X : CriticalTransferData D)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) :
    X.experiment.pr (fun z => D.prefixFailure X.failure z.2) ≤
      X.experiment.pr (fun z =>
        let side := D.pastRows z.2 X.failure.1 X.failure.1.isLt X.failure.2.1
        let tests := D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val
        let U := prefixLabelLaw D X.failure.1 side tests
          (allowedMask_nonempty D X.failure.1 X.failure.2.1.1 X.failure.2.1.2 side.1)
        ∃ x y, X.allowed x y ∧ X.survives z.1 x y ∧ X.deviates U x y) := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro z _
  by_cases hb : D.prefixFailure X.failure z.2
  · by_cases hw : X.experiment.w z = 0
    · simp [hw]
    · have hrun : (D.encoding.kernels.refRun (X.state z.1)).w z.2 ≠ 0 := by
        intro hz
        exact hw (by simp [CriticalTransferData.experiment, FinLaw.bind, hz])
      have hs : z.2.1 = X.state z.1 :=
        runFrom_initial_support D D.encoding.kernels.referenceTransition (X.state z.1)
          D.geom.r le_rfl z.2 hrun
      have he := prefixFailure_surviving_witness D X hsmall z.1 z.2 hs hb
      simp only [if_pos hb, if_pos he, le_refl]
  · simp only [if_neg hb]
    split_ifs <;> simp [X.experiment.nonneg]

variable {D : LateData hPT} {X : CriticalTransferData D}

private def nearInternal (a : Fin (T.S.n k)) : Prop :=
  ∃ t ∈ PT.tiling.Icoord (D.geom.patchOf X.target),
    D.geom.ids a - D.geom.ids t ∈ D.geom.Lsub

private def sameIdCoset (D : LateData hPT) (a b : Fin (T.S.n k)) : Prop :=
  D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub

private noncomputable def idCosetClass (D : LateData hPT) (c : Fin (T.S.n k)) :
    Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => sameIdCoset D a c

private noncomputable def cosetParity (D : LateData hPT) (v : Pos T k)
    (c : Fin (T.S.n k)) : ZMod 2 :=
  ∑ a ∈ idCosetClass D c, if v a = true then 1 else 0

private theorem zmodTwo_double (x : ZMod 2) : x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : ZMod 2) * x := (two_mul x).symm
    _ = 0 := by rw [htwo]; simp

private theorem syndrome_flip (v : Pos T k) (a : Fin (T.S.n k)) :
    D.geom.syndrome (flipPos v a) = D.geom.syndrome v + D.geom.ids a := by
  classical
  let f : Fin (T.S.n k) → (Fin D.geom.Hdim → ZMod 2) := fun j =>
    if v j = true then D.geom.ids j else 0
  let f' : Fin (T.S.n k) → (Fin D.geom.Hdim → ZMod 2) := fun j =>
    if flipPos v a j = true then D.geom.ids j else 0
  have ha : f' a = f a + D.geom.ids a := by
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    have hxx (x : ZMod 2) : x + x = 0 := by
      calc
        x + x = (2 : ZMod 2) * x := (two_mul x).symm
        _ = 0 := by rw [htwo]; simp
    cases hv : v a with
    | false => simp [f, f', flipPos, hv]
    | true =>
        ext j
        simp [f, f', flipPos, hv]
        exact (hxx (D.geom.ids a j)).symm
  have hother : ∀ j, j ≠ a → f' j = f j := by
    intro j hja
    simp [f, f', flipPos, hja]
  change ∑ j, f' j = (∑ j, f j) + D.geom.ids a
  calc
    ∑ j, f' j = f' a + ∑ j ∈ (Finset.univ.erase a), f' j := by
      rw [← Finset.add_sum_erase (s := Finset.univ) (f := f') (Finset.mem_univ a)]
    _ = (f a + D.geom.ids a) + ∑ j ∈ (Finset.univ.erase a), f j := by
      rw [ha]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hother j (Finset.ne_of_mem_erase hj)
    _ = (∑ j, f j) + D.geom.ids a := by
      rw [← Finset.add_sum_erase (s := Finset.univ) (f := f) (Finset.mem_univ a)]
      abel

private theorem cosetParity_flip (D : LateData hPT) (v : Pos T k)
    (a c : Fin (T.S.n k)) :
    cosetParity D (flipPos v a) c = cosetParity D v c +
      if sameIdCoset D a c then 1 else 0 := by
  classical
  let S := idCosetClass D c
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hpoint (t : Fin (T.S.n k)) (ht : t ∈ S) :
      (if flipPos v a t = true then (1 : ZMod 2) else 0) =
        (if v t = true then 1 else 0) + (if t = a then 1 else 0) := by
    by_cases hta : t = a
    · subst t
      cases hv : v a
      · simp [flipPos, hv]
      · simp [flipPos, hv]
        rw [← two_mul (1 : ZMod 2), htwo]
        simp
    · cases hv : v t <;> simp [flipPos, hta, hv]
  have hsum :
      S.sum (fun t => if flipPos v a t = true then (1 : ZMod 2) else 0) =
      S.sum (fun t => if v t = true then (1 : ZMod 2) else 0) +
        S.sum (fun t => if t = a then (1 : ZMod 2) else 0) := by
    calc
      S.sum (fun t => if flipPos v a t = true then (1 : ZMod 2) else 0) =
          S.sum (fun t => (if v t = true then (1 : ZMod 2) else 0) +
            (if t = a then (1 : ZMod 2) else 0)) := by
              apply Finset.sum_congr rfl
              intro t ht
              exact hpoint t ht
      _ = S.sum (fun t => if v t = true then (1 : ZMod 2) else 0) +
            S.sum (fun t => if t = a then (1 : ZMod 2) else 0) := by rw [Finset.sum_add_distrib]
  by_cases hclass : sameIdCoset D a c
  · have hmem : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclass⟩
    have hone : (∑ t ∈ S, if t = a then (1 : ZMod 2) else 0) = 1 := by
      simp [Finset.sum_ite_eq', hmem]
    dsimp [cosetParity, S] at hsum ⊢
    rw [hsum, hone]
    simp [hclass]
  · have hnot : a ∉ S := by
      intro h
      exact hclass (Finset.mem_filter.mp h).2
    have hsum' :
        (∑ t ∈ S, if flipPos v a t = true then (1 : ZMod 2) else 0) =
          (∑ t ∈ S, if v t = true then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hta : t ≠ a := by intro he; exact hnot (he ▸ ht)
      simp [flipPos, hta]
    dsimp [cosetParity, S] at hsum' ⊢
    rw [hsum']
    simp [hclass]

private theorem sameIdCoset_symm (D : LateData hPT) {a b : Fin (T.S.n k)}
    (h : sameIdCoset D a b) : sameIdCoset D b a := by
  change D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub at h
  change D.geom.ids b - D.geom.ids a ∈ D.geom.Lsub
  have heq : D.geom.ids b - D.geom.ids a = -(D.geom.ids a - D.geom.ids b) := by abel
  rw [heq]
  exact D.geom.Lsub.neg_mem h

private theorem sameIdCoset_trans (D : LateData hPT) {a b c : Fin (T.S.n k)}
    (hab : sameIdCoset D a b)
    (hbc : sameIdCoset D b c) :
    sameIdCoset D a c := by
  change D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub at hab
  change D.geom.ids b - D.geom.ids c ∈ D.geom.Lsub at hbc
  change D.geom.ids a - D.geom.ids c ∈ D.geom.Lsub
  have heq : D.geom.ids a - D.geom.ids c =
      (D.geom.ids a - D.geom.ids b) + (D.geom.ids b - D.geom.ids c) := by abel
  rw [heq]
  exact D.geom.Lsub.add_mem hab hbc

private theorem syndrome_mem_of_class (D : LateData hPT) (b : Pos T k) (j : Fin D.geom.r)
    (h : D.geom.classOf b = some j) : D.geom.syndrome b ∈ D.geom.Lsub := by
  unfold LowGeom.classOf at h
  split_ifs at h with hmem
  · exact hmem.2

private theorem sameIdCoset_of_late_two_flip (D : LateData hPT)
    (b b' : Pos T k) (j j' : Fin D.geom.r) (a a' : Fin (T.S.n k))
    (hb : D.geom.classOf b = some j) (hb' : D.geom.classOf b' = some j')
    (hflip : flipPos b a = flipPos b' a') : sameIdCoset D a a' := by
  have hsyndrome := congrArg D.geom.syndrome hflip
  rw [syndrome_flip (D := D) b a, syndrome_flip (D := D) b' a'] at hsyndrome
  have hdiff : D.geom.ids a - D.geom.ids a' =
      D.geom.syndrome b' - D.geom.syndrome b := by
    calc
      D.geom.ids a - D.geom.ids a' =
          (D.geom.syndrome b + D.geom.ids a) -
            (D.geom.syndrome b + D.geom.ids a') := by abel
      _ = (D.geom.syndrome b' + D.geom.ids a') -
            (D.geom.syndrome b + D.geom.ids a') := by rw [hsyndrome]
      _ = D.geom.syndrome b' - D.geom.syndrome b := by abel
  change D.geom.ids a - D.geom.ids a' ∈ D.geom.Lsub
  rw [hdiff]
  exact D.geom.Lsub.sub_mem (syndrome_mem_of_class D b' j' hb')
    (syndrome_mem_of_class D b j hb)

private theorem flipPos_involutive {n : ℕ} (v : CubePos n) (a : Fin n) :
    flipPos (flipPos v a) a = v := by
  funext j
  by_cases hja : j = a
  · subst j
    simp [flipPos]
  · simp [flipPos, hja]

private theorem cosetParity_flip_pair (D : LateData hPT) (v : Pos T k)
    (a a' c : Fin (T.S.n k)) (haa' : sameIdCoset D a a') :
    cosetParity D (flipPos (flipPos v a) a') c = cosetParity D v c := by
  rw [cosetParity_flip D (flipPos v a) a' c, cosetParity_flip D v a c]
  have hclass : sameIdCoset D a c ↔ sameIdCoset D a' c := by
    constructor
    · intro hac
      exact sameIdCoset_trans D (sameIdCoset_symm D haa') hac
    · intro ha'c
      exact sameIdCoset_trans D haa' ha'c
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hone : (1 : ZMod 2) + 1 = 0 := by
    calc
      (1 : ZMod 2) + 1 = 2 := by norm_num
      _ = 0 := htwo
  by_cases hA : sameIdCoset D a c
  · have hA' : sameIdCoset D a' c := hclass.mp hA
    simp [hA, hA', hone, add_assoc]
  · have hA' : ¬ sameIdCoset D a' c := fun h' => hA (hclass.mpr h')
    simp [hA, hA', add_assoc]

private theorem predecessors_cosetParity_eq (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ n (b : Pos T k), b ∈ X.predecessors n →
      ∀ c, cosetParity D b c = cosetParity D X.failure.2.1.1 c := by
  intro n
  induction n with
  | zero =>
      intro b hb c
      simp [CriticalTransferData.predecessors] at hb
      subst b
      rfl
  | succ n ih =>
      intro b hb c
      simp only [CriticalTransferData.predecessors] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact ih b hb c
      · rcases Finset.mem_filter.mp hb with ⟨_, hex⟩
        rcases hex with ⟨b₀, hb₀, j, j', hj, hj', hlt, hflipExists⟩
        rcases hflipExists with ⟨a, a', hflip⟩
        have hsame := sameIdCoset_of_late_two_flip D b₀ b j j' a a' hj hj' hflip
        have hbEq : b = flipPos (flipPos b₀ a) a' := by
          have hcon := congrArg (fun w : Pos T k => flipPos w a') hflip
          rw [flipPos_involutive] at hcon
          exact hcon.symm
        rw [hbEq, cosetParity_flip_pair D b₀ a a' c hsame]
        exact ih b₀ hb₀ c

private theorem class_some_of_predecessor (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ n (b : Pos T k), b ∈ X.predecessors n → ∃ j, D.geom.classOf b = some j := by
  intro n
  induction n with
  | zero =>
      intro b hb
      simp [CriticalTransferData.predecessors] at hb
      subst b
      refine ⟨X.failure.1, ?_⟩
      exact (D.encoding.base.class_of_spec X.failure.2.1.1 X.failure.1).mp X.failure.2.1.2
  | succ n ih =>
      intro b hb
      simp only [CriticalTransferData.predecessors] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact ih b hb
      · rcases Finset.mem_filter.mp hb with ⟨_, hex⟩
        rcases hex with ⟨_, _, _, j', _, hj', _, _⟩
        exact ⟨j', hj'⟩

private theorem notEven_of_class_some (D : LateData hPT) (b : Pos T k)
    (j : Fin D.geom.r) (h : D.geom.classOf b = some j) : ¬ IsEvenRole b := by
  unfold LowGeom.classOf at h
  split_ifs at h with hcond
  · exact hcond.1

private theorem cosetParity_mismatch_of_internal (D : LateData hPT) (X : CriticalTransferData D)
    {s t : Pos T k} (q : Fin (T.S.n k))
    (hq : q ∈ PT.tiling.Icoord (D.geom.patchOf X.target))
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → s a = t a) :
    cosetParity D s q + cosetParity D t q = if s q = t q then 0 else 1 := by
  classical
  let i := D.geom.patchOf X.target
  let S := idCosetClass D q
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hdouble (x : ZMod 2) : x + x = 0 := by
    calc
      x + x = (2 : ZMod 2) * x := (two_mul x).symm
      _ = 0 := by rw [htwo]; simp
  have hpoint (a : Fin (T.S.n k)) (ha : a ∈ S) :
      (if s a = true then (1 : ZMod 2) else 0) +
        (if t a = true then 1 else 0) =
          if a = q then (if s q = t q then 0 else 1) else 0 := by
    by_cases haq : a = q
    · subst a
      cases hs : s q <;> cases htBool : t q <;> simp [hs, htBool, hdouble]
    · have haCoset : sameIdCoset D a q := (Finset.mem_filter.mp ha).2
      have haNotI : a ∉ PT.tiling.Icoord i := by
        intro haI
        have heq : a = q :=
          D.l16_valid.internal_cosets i a q haI hq haCoset
        exact haq heq
      have hEq := houter a haNotI
      cases htBool : t a <;> simp [haq, hEq, htBool, hdouble]
  have hsum :
      S.sum (fun a => if s a = true then (1 : ZMod 2) else 0) +
        S.sum (fun a => if t a = true then (1 : ZMod 2) else 0) =
      S.sum (fun a => if a = q then (if s q = t q then 0 else 1) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpoint
  have hmem : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change D.geom.ids q - D.geom.ids q ∈ D.geom.Lsub
    simp⟩
  have hsingle :
      S.sum (fun a => if a = q then (if s q = t q then (0 : ZMod 2) else 1) else 0) =
        (if s q = t q then 0 else 1) := by
    simp [Finset.sum_ite_eq', hmem]
  simpa [cosetParity, S] using hsum.trans (by rw [hsingle])

private theorem cosetParity_eq_on_noInternalClass (D : LateData hPT) (s t : Pos T k)
    (q : Fin (T.S.n k))
    (hNo : ∀ a, a ∈ PT.tiling.Icoord (D.geom.patchOf X.target) →
      ¬ sameIdCoset D a q)
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → s a = t a) :
    cosetParity D s q = cosetParity D t q := by
  classical
  unfold cosetParity idCosetClass
  apply Finset.sum_congr rfl
  intro a ha
  have haClass : sameIdCoset D a q := (Finset.mem_filter.mp ha).2
  have haI : a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
    intro hI
    exact hNo a hI haClass
  simpa [houter a haI]


private theorem directEven_representation (D : LateData hPT) (X : CriticalTransferData D)
    (w : Pos T k) (hw : w ∈ X.directEven) :
    ∃ b ∈ X.predecessors D.geom.r, ∃ a : Fin (T.S.n k), w = flipPos b a := by
  obtain ⟨b, hb, h⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
  exact ⟨b, hb, a, heq.symm⟩

/-- Global coset parity permits at most h+1 direct even sites with any fixed
outer word. This is the slice count used in the bounded-response simulation. -/
theorem directEven_outerWord_card (D : LateData hPT) (X : CriticalTransferData D)
    (t : Pos T k) :
    (X.directEven.filter fun w => ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = t a).card ≤
      (PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1 := by
  classical
  let S := X.directEven.filter fun w => ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = t a
  let W := {w : Pos T k // w ∈ S}
  let I := {q : Fin (T.S.n k) // q ∈ PT.tiling.Icoord (D.geom.patchOf X.target)}
  have hrep (w : W) := directEven_representation D X w.1 (Finset.mem_filter.mp w.2).1
  let bOf (w : W) := (hrep w).choose
  let dOf (w : W) := (hrep w).choose_spec.2.choose
  have hb (w : W) : bOf w ∈ X.predecessors D.geom.r := (hrep w).choose_spec.1
  have hd (w : W) : w.1 = flipPos (bOf w) (dOf w) := (hrep w).choose_spec.2.choose_spec
  let code (w : W) : Option I := if hn : nearInternal (D := D) (X := X) (dOf w) then
    some ⟨hn.choose, hn.choose_spec.1⟩ else none
  have hpar (w : W) (q : Fin (T.S.n k)) : cosetParity D w.1 q =
      cosetParity D X.failure.2.1.1 q + (if sameIdCoset D (dOf w) q then 1 else 0) := by
    rw [hd w, cosetParity_flip, predecessors_cosetParity_eq D X D.geom.r (bOf w) (hb w)]
  have hcode : Function.Injective code := by
    intro w w' heq
    have houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w.1 a = w'.1 a := by
      intro a ha
      exact ((Finset.mem_filter.mp w.2).2 a ha).trans ((Finset.mem_filter.mp w'.2).2 a ha).symm
    have hsame (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord (D.geom.patchOf X.target)) :
        sameIdCoset D (dOf w) q ↔ sameIdCoset D (dOf w') q := by
      by_cases hw : nearInternal (D := D) (X := X) (dOf w)
      · by_cases hw' : nearInternal (D := D) (X := X) (dOf w')
        · have heq' := heq
          dsimp [code] at heq'
          simp only [dif_pos hw, dif_pos hw'] at heq'
          have hqq : hw.choose = hw'.choose := congrArg Subtype.val (Option.some.inj heq')
          have hwd : sameIdCoset D (dOf w) hw.choose := hw.choose_spec.2
          have hw'd : sameIdCoset D (dOf w') hw'.choose := hw'.choose_spec.2
          rw [← hqq] at hw'd
          have hww : sameIdCoset D (dOf w) (dOf w') := sameIdCoset_trans D hwd (sameIdCoset_symm D hw'd)
          exact ⟨fun hh => sameIdCoset_trans D (sameIdCoset_symm D hww) hh,
            fun hh => sameIdCoset_trans D hww hh⟩
        · simp [code, hw, hw'] at heq
      · by_cases hw' : nearInternal (D := D) (X := X) (dOf w')
        · simp [code, hw, hw'] at heq
        · have hn : ¬ sameIdCoset D (dOf w) q := fun h => hw ⟨q, hq, h⟩
          have hn' : ¬ sameIdCoset D (dOf w') q := fun h => hw' ⟨q, hq, h⟩
          simp [hn, hn']
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ PT.tiling.Icoord (D.geom.patchOf X.target)
    · have hp : cosetParity D w.1 q = cosetParity D w'.1 q := by
        rw [hpar, hpar, hsame q hq]
      have hm := cosetParity_mismatch_of_internal D X q hq houter
      rw [hp, zmodTwo_double] at hm
      by_contra hn
      simp [hn] at hm
    · exact houter q hq
  have hcard := Fintype.card_le_of_injective code hcode
  simpa only [W, I, Fintype.card_coe, Fintype.card_option] using hcard
private theorem cosetParity_doubleFlip (D : LateData hPT) (v : Pos T k)
    (a b q : Fin (T.S.n k)) :
    cosetParity D (flipPos (flipPos v a) b) q =
      cosetParity D v q + (if sameIdCoset D a q then (1 : ZMod 2) else 0) +
        (if sameIdCoset D b q then 1 else 0) := by
  rw [cosetParity_flip D (flipPos v a) b q, cosetParity_flip D v a q]

private theorem externalEarly_not_sameIdCoset (D : LateData hPT)
    (b : Pos T k) (d j : Fin (T.S.n k))
    (hb : ∃ i, D.geom.classOf b = some i)
    (hj : j ∈ D.externalEarly (flipPos b d)) :
    ¬ sameIdCoset D d j := by
  classical
  rcases hb with ⟨i, hclass⟩
  have hbOdd := notEven_of_class_some D b i hclass
  have hwEven : IsEvenRole (flipPos b d) := by
    exact (HypercubeRamsey.S15.evenRole_flipPos b d).mpr hbOdd
  have hvOdd : ¬ IsEvenRole (flipPos (flipPos b d) j) := by
    intro hvEven
    exact ((HypercubeRamsey.S15.evenRole_flipPos (flipPos b d) j).mp hvEven) hwEven
  have hnone : D.geom.classOf (flipPos (flipPos b d) j) = none :=
    (Finset.mem_filter.mp hj).2.2
  have hnotSyndrome : D.geom.syndrome (flipPos (flipPos b d) j) ∉ D.geom.Lsub := by
    by_contra hs
    unfold LowGeom.classOf at hnone
    have hcond : ¬ IsEvenRole (flipPos (flipPos b d) j) ∧
        D.geom.syndrome (flipPos (flipPos b d) j) ∈ D.geom.Lsub := ⟨hvOdd, hs⟩
    simp [hcond] at hnone
  have hbSyndrome : D.geom.syndrome b ∈ D.geom.Lsub := syndrome_mem_of_class D b i hclass
  intro hdj
  have hneg (x : ZMod 2) : -x = x := by
    calc
      -x = -x + (x + x) := by rw [zmodTwo_double]; simp
      _ = x := by abel
  have hid : D.geom.ids d + D.geom.ids j ∈ D.geom.Lsub := by
    have heq : D.geom.ids d + D.geom.ids j = D.geom.ids d - D.geom.ids j := by
      ext q
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [sub_eq_add_neg, hneg]
    rw [heq]
    exact hdj
  have hsum : D.geom.syndrome b + D.geom.ids d + D.geom.ids j ∈ D.geom.Lsub := by
    have htemp : D.geom.syndrome b + (D.geom.ids d + D.geom.ids j) ∈ D.geom.Lsub :=
      D.geom.Lsub.add_mem hbSyndrome hid
    simpa only [add_assoc] using htemp
  have hformula : D.geom.syndrome (flipPos (flipPos b d) j) =
      D.geom.syndrome b + D.geom.ids d + D.geom.ids j := by
    rw [syndrome_flip, syndrome_flip]
  exact hnotSyndrome (hformula ▸ hsum)

private theorem cosetParity_doubleFlip_sum (D : LateData hPT)
    (b b₀ : Pos T k) (d j a₀ c q : Fin (T.S.n k))
    (hparity : cosetParity D b q = cosetParity D b₀ q) :
    cosetParity D (flipPos (flipPos b d) j) q +
        cosetParity D (flipPos (flipPos b₀ a₀) c) q =
      (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
        (if sameIdCoset D j q then 1 else 0) +
        (if sameIdCoset D a₀ q then 1 else 0) +
        (if sameIdCoset D c q then 1 else 0) := by
  rw [cosetParity_doubleFlip D b d j q, cosetParity_doubleFlip D b₀ a₀ c q,
    hparity]
  calc
    _ = (cosetParity D b₀ q + cosetParity D b₀ q) +
        ((if sameIdCoset D d q then (1 : ZMod 2) else 0) +
          (if sameIdCoset D j q then 1 else 0) +
          (if sameIdCoset D a₀ q then 1 else 0) +
          (if sameIdCoset D c q then 1 else 0)) := by abel
    _ = _ := by rw [zmodTwo_double]; simp


/-- A critical external observation restricts its coordinate to the internal
cosets, the observed critical coset, or the target coset. -/
theorem external_observation_coordinate (D : LateData hPT) (X : CriticalTransferData D)
    (w : Pos T k) (hw : w ∈ X.directEven) (j c : Fin (T.S.n k))
    (hj : j ∈ D.externalEarly w)
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
      flipPos w j a = flipPos X.target c a) :
    nearInternal (D := D) (X := X) j ∨ sameIdCoset D j c ∨ sameIdCoset D j X.failure.2.2.2.2 := by
  obtain ⟨b, hb, d, hwd⟩ := directEven_representation D X w hw
  have hnotdj : ¬ sameIdCoset D d j := by
    apply externalEarly_not_sameIdCoset D b d j (class_some_of_predecessor D X D.geom.r b hb)
    simpa only [hwd] using hj
  by_contra hn
  simp only [not_or] at hn
  have hNo : ∀ a, a ∈ PT.tiling.Icoord (D.geom.patchOf X.target) → ¬ sameIdCoset D a j := by
    intro a ha h
    exact hn.1 ⟨a, ha, sameIdCoset_symm D h⟩
  have hp := cosetParity_eq_on_noInternalClass D (flipPos w j) (flipPos X.target c) j hNo houter
  have hs := cosetParity_doubleFlip_sum D b X.failure.2.1.1 d j X.failure.2.2.2.2 c j
    (predecessors_cosetParity_eq D X D.geom.r b hb j)
  have htarget : X.target = flipPos X.failure.2.1.1 X.failure.2.2.2.2 := rfl
  rw [← hwd, ← htarget, hp, zmodTwo_double] at hs
  have hjj : sameIdCoset D j j := by unfold sameIdCoset; simp
  have hcj : ¬ sameIdCoset D c j := fun h => hn.2.1 (sameIdCoset_symm D h)
  have haj : ¬ sameIdCoset D X.failure.2.2.2.2 j := fun h => hn.2.2 (sameIdCoset_symm D h)
  simp [hnotdj, hjj, hcj, haj] at hs
private theorem cosetCoords_card_le (a : Fin (T.S.n k)) :
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
      D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub).card ≤ D.geom.r := by
  classical
  let C := {b : Fin (T.S.n k) // D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub}
  let code : C → D.geom.Lsub := fun b => ⟨D.geom.ids a - D.geom.ids b.1, b.2⟩
  have hcode : Function.Injective code := by
    intro b c h
    apply Subtype.ext
    apply D.l16_valid.ids_distinct
    have hval : D.geom.ids a - D.geom.ids b.1 = D.geom.ids a - D.geom.ids c.1 :=
      congrArg Subtype.val h
    simpa only [sub_right_inj] using hval
  have hcard : Fintype.card D.geom.Lsub = D.geom.r := by
    simpa using (Fintype.card_congr D.geom.classEnum).symm
  calc
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
        D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub).card = Fintype.card C := by
          simp [C, Fintype.card_subtype]
    _ ≤ Fintype.card D.geom.Lsub := Fintype.card_le_of_injective code hcode
    _ = D.geom.r := hcard

private theorem nearInternalCoords_card_le :
    (Finset.univ.filter fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b).card ≤
      (PT.tiling.Icoord (D.geom.patchOf X.target)).card * D.geom.r := by
  classical
  let i := D.geom.patchOf X.target
  let C := {b : Fin (T.S.n k) // nearInternal (D := D) (X := X) b}
  let I := {t : Fin (T.S.n k) // t ∈ PT.tiling.Icoord i}
  let tOf (b : C) : I := ⟨Classical.choose b.2, (Classical.choose_spec b.2).1⟩
  have hdiff (b : C) : D.geom.ids b.1 - D.geom.ids (tOf b).1 ∈ D.geom.Lsub :=
    (Classical.choose_spec b.2).2
  let code : C → I × D.geom.Lsub := fun b =>
    (tOf b, ⟨D.geom.ids b.1 - D.geom.ids (tOf b).1, hdiff b⟩)
  have hcode : Function.Injective code := by
    intro b c hbc
    apply Subtype.ext
    have ht : (tOf b).1 = (tOf c).1 := congrArg (fun z => z.1.1) hbc
    have hidsDiff : D.geom.ids b.1 - D.geom.ids (tOf b).1 =
        D.geom.ids c.1 - D.geom.ids (tOf c).1 :=
      congrArg (fun z => z.2.1) hbc
    have hids : D.geom.ids b.1 = D.geom.ids c.1 := by
      rw [ht] at hidsDiff
      simpa only [sub_left_inj] using hidsDiff
    exact D.l16_valid.ids_distinct hids
  have hcardL : Fintype.card D.geom.Lsub = D.geom.r := by
    simpa using (Fintype.card_congr D.geom.classEnum).symm
  calc
    (Finset.univ.filter fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b).card =
        Fintype.card C := by simp [C, Fintype.card_subtype]
    _ ≤ Fintype.card (I × D.geom.Lsub) := Fintype.card_le_of_injective code hcode
    _ = (PT.tiling.Icoord i).card * D.geom.r := by
      rw [Fintype.card_prod, hcardL]
      simp only [I, Fintype.card_coe]


private noncomputable def observationCoords (D : LateData hPT) (X : CriticalTransferData D)
    (c : Fin (T.S.n k)) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun j => nearInternal (D := D) (X := X) j ∨
    sameIdCoset D c j ∨ sameIdCoset D X.failure.2.2.2.2 j

private theorem observationCoords_card (D : LateData hPT) (X : CriticalTransferData D)
    (c : Fin (T.S.n k)) : (observationCoords D X c).card ≤
      ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r := by
  let N := Finset.univ.filter fun j => nearInternal (D := D) (X := X) j
  let C := Finset.univ.filter fun j => sameIdCoset D c j
  let A := Finset.univ.filter fun j => sameIdCoset D X.failure.2.2.2.2 j
  have hsub : observationCoords D X c ⊆ N ∪ (C ∪ A) := by
    intro j hj
    simpa [observationCoords, N, C, A] using hj
  have hn := nearInternalCoords_card_le (D := D) (X := X)
  have hc := cosetCoords_card_le (D := D) c
  have ha := cosetCoords_card_le (D := D) X.failure.2.2.2.2
  change N.card ≤ (PT.tiling.Icoord (D.geom.patchOf X.target)).card * D.geom.r at hn
  change C.card ≤ D.geom.r at hc
  change A.card ≤ D.geom.r at ha
  calc
    _ ≤ (N ∪ (C ∪ A)).card := Finset.card_le_card hsub
    _ ≤ N.card + (C.card + A.card) := (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤ ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r := by nlinarith

private theorem hammingDist_flip_le_one (v : Pos T k) (a : Fin (T.S.n k)) :
    hammingDist v (flipPos v a) ≤ 1 := by
  classical
  change (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ flipPos v a j)).card ≤ 1
  have hsub :
      (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ flipPos v a j)) ⊆ {a} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hja
    have hjne : j ≠ a := by simpa using hja
    apply hj
    simp [flipPos, hjne]
  calc
    _ ≤ ({a} : Finset (Fin (T.S.n k))).card := Finset.card_le_card hsub
    _ ≤ 1 := by simp

private theorem hammingDist_comm_lane (v w : Pos T k) :
    hammingDist v w = hammingDist w v := by
  classical
  change (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ w j)).card =
    (Finset.univ.filter (fun j : Fin (T.S.n k) => w j ≠ v j)).card
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

private theorem directObservation_distance (hG : TransferGeometry X) (b : Pos T k) (d : Fin (T.S.n k))
    (hb : b ∈ X.predecessors D.geom.r) (w v : Pos T k)
    (hwd : w = flipPos b d) (hvw : v = w ∨ ∃ j, v = flipPos w j)
    (c : Fin (T.S.n k)) :
    hammingDist v (flipPos X.target c) ≤ 2 * D.geom.r + 4 := by
  let b₀ := X.failure.2.1.1
  let a₀ := X.failure.2.2.2.2
  have htarget : X.target = flipPos b₀ a₀ := rfl
  have hb₀b : hammingDist b₀ b ≤ 2 * D.geom.r := by
    exact (Finset.mem_filter.mp (hG.predecessor_radius b hb)).2
  have hbb₀ : hammingDist b b₀ ≤ 2 * D.geom.r := by
    rw [hammingDist_comm_lane b b₀]
    exact hb₀b
  have hb₀t : hammingDist b₀ X.target ≤ 1 := by
    rw [htarget]
    exact hammingDist_flip_le_one b₀ a₀
  have httc : hammingDist X.target (flipPos X.target c) ≤ 1 :=
    hammingDist_flip_le_one X.target c
  have hwb : hammingDist w b ≤ 1 := by
    rw [hwd, hammingDist_comm_lane (flipPos b d) b]
    exact hammingDist_flip_le_one b d
  have hvw' : hammingDist v w ≤ 1 := by
    rcases hvw with rfl | ⟨j, rfl⟩
    · simp [hammingDist]
    · rw [hammingDist_comm_lane (flipPos w j) w]
      exact hammingDist_flip_le_one w j
  have hbT : hammingDist b (flipPos X.target c) ≤ 2 * D.geom.r + 2 := by
    have h₁ := hammingDist_triangle b b₀ (flipPos X.target c)
    have h₂ := hammingDist_triangle b₀ X.target (flipPos X.target c)
    omega
  have hwT : hammingDist w (flipPos X.target c) ≤ 2 * D.geom.r + 3 := by
    have h := hammingDist_triangle w b (flipPos X.target c)
    omega
  have hvT := hammingDist_triangle v w (flipPos X.target c)
  omega


private theorem criticalCell_outer_words (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (c : Fin (T.S.n k)) (hc : c ∈ X.criticalCoords)
    (w : Pos T k) (hw : w ∈ X.directEven)
    (hcell : D.geom.cellOf (flipPos X.target c) ∈ D.directCells w) :
    (∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = flipPos X.target c a) ∨
    ∃ j ∈ observationCoords D X c,
      ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = flipPos (flipPos X.target c) j a := by
  obtain ⟨b, hb, d, hwd⟩ := directEven_representation D X w hw
  rcases Finset.mem_union.mp hcell with hown | hext
  · have heq : D.geom.cellOf w = D.geom.cellOf (flipPos X.target c) := (Finset.mem_singleton.mp hown).symm
    left
    apply S18.Lane_q_s18_n2.sameCell_outer_eq (D := D) (X := X) w c hc heq hmargin
    exact_mod_cast directObservation_distance hG b d hb w w hwd (Or.inl rfl) c
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hext
    have houter := S18.Lane_q_s18_n2.sameCell_outer_eq (D := D) (X := X) (flipPos w j) c hc heq hmargin
      (by exact_mod_cast directObservation_distance hG b d hb w (flipPos w j) hwd (Or.inr ⟨j, rfl⟩) c)
    have hcoord := external_observation_coordinate D X w hw j c hj houter
    have hmem : j ∈ observationCoords D X c := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hcoord with hn | hcos | htarget
      · exact Or.inl hn
      · exact Or.inr (Or.inl (sameIdCoset_symm D hcos))
      · exact Or.inr (Or.inr (sameIdCoset_symm D htarget))
    refine Or.inr ⟨j, hmem, ?_⟩
    intro a ha
    have ho := houter a ha
    by_cases haj : a = j
    · subst a
      simp only [flipPos, Function.update_self] at ho ⊢
      simpa only [Bool.not_not] using congrArg Bool.not ho
    · simpa [flipPos, haj] using ho

/-- Each critical whole cell affects only a polynomial number of direct sites
in h and r; the bound counts their actual spatial scopes. -/
theorem criticalCell_affected_card (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (c : Fin (T.S.n k)) (hc : c ∈ X.criticalCoords) :
    (X.directEven.filter fun w => D.geom.cellOf (flipPos X.target c) ∈ D.directCells w).card ≤
      (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) := by
  let sites (t : Pos T k) := X.directEven.filter fun w =>
    ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = t a
  let J := observationCoords D X c
  let S := X.directEven.filter fun w => D.geom.cellOf (flipPos X.target c) ∈ D.directCells w
  have hsub : S ⊆ sites (flipPos X.target c) ∪ J.biUnion (fun j => sites (flipPos (flipPos X.target c) j)) := by
    intro w hw
    obtain ⟨hw, hcell⟩ := Finset.mem_filter.mp hw
    rcases criticalCell_outer_words D X hG hmargin c hc w hw hcell with hown | ⟨j, hj, hword⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hw, hown⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hw, hword⟩⟩))
  have hs (t : Pos T k) : (sites t).card ≤ (PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1 :=
    directEven_outerWord_card D X t
  have hj := observationCoords_card D X c
  calc
    _ ≤ (sites (flipPos X.target c) ∪ J.biUnion (fun j => sites (flipPos (flipPos X.target c) j))).card := Finset.card_le_card hsub
    _ ≤ (sites (flipPos X.target c)).card + ∑ j ∈ J, (sites (flipPos (flipPos X.target c) j)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    _ ≤ ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) +
        ∑ _j ∈ J, ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) :=
      Nat.add_le_add (hs _) (Finset.sum_le_sum (fun j _ => hs _))
    _ = (1 + J.card) * ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_left hj 1)

/-- Summing the whole-cell scope count gives the per-block direct-site budget. -/
theorem block_affectedSites_card (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (a : Fin (T.S.n k)) :
    (X.directEven.filter fun w => (D.directCells w ∩ X.blockCells a).Nonempty).card ≤
      (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
        (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) := by
  let J := X.criticalCoords.filter (X.sameBlock a)
  let sites := fun c => X.directEven.filter fun w => D.geom.cellOf (flipPos X.target c) ∈ D.directCells w
  let S := X.directEven.filter fun w => (D.directCells w ∩ X.blockCells a).Nonempty
  have hsub : S ⊆ J.biUnion sites := by
    intro w hw
    obtain ⟨hw, C, hC⟩ := Finset.mem_filter.mp hw
    obtain ⟨hscope, hblock⟩ := Finset.mem_inter.mp hC
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hblock
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hw, by simpa only [heq] using hscope⟩⟩
  have hsite (c : Fin (T.S.n k)) (hc : c ∈ J) : (sites c).card ≤
      (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) :=
    criticalCell_affected_card D X hG hmargin c (Finset.mem_filter.mp hc).1
  calc
    _ ≤ (J.biUnion sites).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ J, (sites c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ J, (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1) := Finset.sum_le_sum fun c hc => hsite c hc
    _ = J.card * ((1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1)) := by simp
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right
        ((1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
          ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1)) (hG.block_size a)
      simpa only [Nat.mul_assoc] using hh

private theorem predecessors_mono (D : LateData hPT) (X : CriticalTransferData D) :
    Monotone X.predecessors := by
  apply monotone_nat_of_le_succ
  intro n b hb
  exact Finset.mem_union.mpr (Or.inl hb)

private theorem predecessor_rank (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ n b, b ∈ X.predecessors n → ∀ j : Fin D.geom.r, D.geom.classOf b = some j →
      j.val ≤ X.failure.1.val ∧ b ∈ X.predecessors (X.failure.1.val - j.val) := by
  intro n
  induction n with
  | zero =>
    intro b hb j hj
    have heq : b = X.failure.2.1.1 := by simpa only [CriticalTransferData.predecessors, Finset.mem_singleton] using hb
    subst b
    have hroot := (D.encoding.base.class_of_spec X.failure.2.1.1 X.failure.1).mp X.failure.2.1.2
    have hjroot : j = X.failure.1 := Option.some.inj (hj.symm.trans hroot)
    subst j
    simp [CriticalTransferData.predecessors]
  | succ n ih =>
    intro b hb j hj
    rcases Finset.mem_union.mp hb with hb | hb
    · exact ih b hb j hj
    · obtain ⟨b0, hb0, j0, j1, hj0, hj1, hlt, a, a', hflip⟩ := (Finset.mem_filter.mp hb).2
      have hjj : j1 = j := Option.some.inj (hj1.symm.trans hj)
      subst j1
      obtain ⟨hrank, hsmall⟩ := ih b0 hb0 j0 hj0
      have hnew : b ∈ X.predecessors ((X.failure.1.val - j0.val) + 1) := by
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b0, hsmall, j0, j, hj0, hj, hlt, a, a', hflip⟩
      refine ⟨by omega, predecessors_mono D X (by omega) hnew⟩

/-- The r-step predecessor set is closed under every strictly earlier two-edge
label dependency. The strict class rank makes the finite closure exact. -/
theorem predecessors_closed (D : LateData hPT) (X : CriticalTransferData D)
    (b b' : Pos T k) (hb : b ∈ X.predecessors D.geom.r)
    (j j' : Fin D.geom.r) (hj : D.geom.classOf b = some j) (hj' : D.geom.classOf b' = some j')
    (hlt : j'.val < j.val) (a a' : Fin (T.S.n k)) (hflip : flipPos b a = flipPos b' a') :
    b' ∈ X.predecessors D.geom.r := by
  obtain ⟨hrank, hsmall⟩ := predecessor_rank D X D.geom.r b hb j hj
  have hnew : b' ∈ X.predecessors ((X.failure.1.val - j.val) + 1) := by
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hsmall, j, j', hj, hj', hlt, a, a', hflip⟩
  exact predecessors_mono D X (by have hroot := X.failure.1.isLt; omega) hnew

/-- The finite call plan includes one coordinate sketch for each predecessor
role in its class. A later restriction will omit erased or unaffected calls. -/
abbrev SketchCall (D : LateData hPT) (X : CriticalTransferData D) :=
  Σ j : Fin D.geom.r, {b : Pos T k // b ∈ D.encoding.base.classes j ∧ b ∈ X.predecessors D.geom.r} × Fin (T.S.n k)

noncomputable instance (D : LateData hPT) (X : CriticalTransferData D) : Fintype (SketchCall D X) := inferInstance

private noncomputable def callSite (D : LateData hPT) (X : CriticalTransferData D) (c : SketchCall D X) : Pos T k :=
  flipPos c.2.1.1 c.2.2

/-- A site is queried at most once in each class in the actual finite call plan. -/
theorem callSite_key_injective (D : LateData hPT) (X : CriticalTransferData D) :
    Function.Injective (fun c : SketchCall D X => (c.1, callSite D X c)) := by
  intro c c' heq
  rcases c with ⟨j, b, a⟩
  rcases c' with ⟨j', b', a'⟩
  have hj : j = j' := congrArg Prod.fst heq
  subst j'
  have hs : flipPos b.1 a = flipPos b'.1 a' := congrArg Prod.snd heq
  let w := flipPos b.1 a
  have hb : D.geom.classOf b.1 = some j := (D.encoding.base.class_of_spec b.1 j).mp b.2.1
  have hb' : D.geom.classOf b'.1 = some j := (D.encoding.base.class_of_spec b'.1 j).mp b'.2.1
  have ha : D.geom.classOf (flipPos w a) = some j := by simpa only [w, flipPos_involutive] using hb
  have ha' : D.geom.classOf (flipPos w a') = some j := by rw [show w = flipPos b'.1 a' from hs, flipPos_involutive]; exact hb'
  have haa : a = a' := D.l16_valid.one_per_class w j a a' ha ha'
  subst a'
  have hbb : b = b' := Subtype.ext (by simpa only [flipPos_involutive] using congrArg (fun v => flipPos v a) hs)
  subst b'
  rfl

/-- The whole-cell site budget translates to a sketch-call budget by the exact
site/class injection; no sampling of roles is used in this count. -/
theorem block_sketchCalls_card (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (a : Fin (T.S.n k)) :
    (Finset.univ.filter fun c : SketchCall D X =>
      (D.directCells (callSite D X c) ∩ X.blockCells a).Nonempty).card ≤
      D.geom.r * ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) *
        (1 + ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 2) * D.geom.r) *
        ((PT.tiling.Icoord (D.geom.patchOf X.target)).card + 1)) := by
  classical
  let S := X.directEven.filter fun w => (D.directCells w ∩ X.blockCells a).Nonempty
  let C := {c : SketchCall D X // (D.directCells (callSite D X c) ∩ X.blockCells a).Nonempty}
  let code (c : C) : Fin D.geom.r × {w : Pos T k // w ∈ S} :=
    (c.1.1, ⟨callSite D X c.1, Finset.mem_filter.mpr ⟨
      Finset.mem_biUnion.mpr ⟨c.1.2.1.1, c.1.2.1.2.2,
        Finset.mem_image.mpr ⟨c.1.2.2, Finset.mem_univ _, rfl⟩⟩, c.2⟩⟩)
  have hi : Function.Injective code := by
    intro c c' heq
    apply Subtype.ext
    apply callSite_key_injective D X
    exact congrArg (fun z => (z.1, z.2.1)) heq
  have hcard := Fintype.card_le_of_injective code hi
  have hraw : (Finset.univ.filter fun c : SketchCall D X =>
      (D.directCells (callSite D X c) ∩ X.blockCells a).Nonempty).card ≤ D.geom.r * S.card := by
    rw [Fintype.card_prod, Fintype.card_fin] at hcard
    have hS : Fintype.card {w : Pos T k // w ∈ S} = S.card := Fintype.card_coe S
    rw [hS] at hcard
    simpa only [C, Fintype.card_subtype] using hcard
  exact hraw.trans (Nat.mul_le_mul_left D.geom.r (block_affectedSites_card D X hG hmargin a))

private noncomputable def criticalExternalInputs (D : LateData hPT) (X : CriticalTransferData D)
    (w : Pos T k) : Finset (Fin (T.S.n k)) :=
  (D.externalEarly w).filter fun j => D.geom.cellOf (flipPos w j) ∈ X.criticalCells

private theorem criticalObservation_outside_internal (D : LateData hPT) (X : CriticalTransferData D)
    (w : Pos T k) (j : Fin (T.S.n k)) (hj : j ∈ criticalExternalInputs D X w) :
    j ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
  obtain ⟨hj, hcrit⟩ := Finset.mem_filter.mp hj
  obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hcrit
  have hp : D.geom.patchOf (flipPos w j) = D.geom.patchOf X.target := by
    calc
      _ = D.geom.cellPatch (D.geom.cellOf (flipPos w j)) := (D.geom.cellOf_patch _).symm
      _ = D.geom.cellPatch (D.geom.cellOf (flipPos X.target c)) := by rw [heq]
      _ = D.geom.patchOf (flipPos X.target c) := D.geom.cellOf_patch _
      _ = _ := S18.Lane_q_s18_n2.patchOf_flip_bulk (D := D) (X := X) c (Finset.mem_filter.mp hc).1
  intro hI
  have hIp : j ∈ PT.tiling.Icoord (D.geom.patchOf (flipPos w j)) := by simpa only [hp] using hI
  have hw := internal_patch D (flipPos w j) j hIp
  rw [flipPos_involutive, hp] at hw
  exact (Finset.mem_filter.mp hj).2.1 (by simpa only [hw] using hI)

private theorem criticalObservation_cells_injective (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (w : Pos T k) (hw : w ∈ X.directEven)
    (j j' : Fin (T.S.n k)) (hj : j ∈ criticalExternalInputs D X w)
    (hj' : j' ∈ criticalExternalInputs D X w)
    (heq : D.geom.cellOf (flipPos w j) = D.geom.cellOf (flipPos w j')) : j = j' := by
  obtain ⟨b, hb, d, hwd⟩ := directEven_representation D X w hw
  obtain ⟨c, hc, hcell⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).2
  have ho := S18.Lane_q_s18_n2.sameCell_outer_eq (D := D) (X := X) (flipPos w j) c hc hcell.symm hmargin
    (by exact_mod_cast directObservation_distance hG b d hb w (flipPos w j) hwd (Or.inr ⟨j, rfl⟩) c)
  have ho' := S18.Lane_q_s18_n2.sameCell_outer_eq (D := D) (X := X) (flipPos w j') c hc (heq.symm.trans hcell.symm) hmargin
    (by exact_mod_cast directObservation_distance hG b d hb w (flipPos w j') hwd (Or.inr ⟨j', rfl⟩) c)
  have hnotI := criticalObservation_outside_internal D X w j hj
  have hv := (ho j hnotI).trans (ho' j hnotI).symm
  by_contra hn
  cases hwj : w j <;> simp [flipPos, hn, hwj] at hv

/-- Omitting the one responding block removes no more early inputs than its
critical-coordinate count, as required by the masked-list gate. -/
theorem criticalExternalInputs_card (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (w : Pos T k) (hw : w ∈ X.directEven \ X.erased) :
    (criticalExternalInputs D X w).card ≤ max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r := by
  obtain ⟨a, ha⟩ := hG.one_block w hw
  let J := criticalExternalInputs D X w
  let code (j : {j : Fin (T.S.n k) // j ∈ J}) : {C : D.geom.Cell // C ∈ X.blockCells a} :=
    ⟨D.geom.cellOf (flipPos w j.1), ha (Finset.mem_inter.mpr ⟨
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j.1, (Finset.mem_filter.mp j.2).1, rfl⟩)),
      (Finset.mem_filter.mp j.2).2⟩)⟩
  have hi : Function.Injective code := by
    intro j j' heq
    apply Subtype.ext
    exact criticalObservation_cells_injective D X hG hmargin w (Finset.mem_sdiff.mp hw).1 j.1 j'.1 j.2 j'.2
      (congrArg Subtype.val heq)
  have hcard := Fintype.card_le_of_injective code hi
  have hb : (X.blockCells a).card ≤ max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r :=
    Finset.card_image_le.trans (hG.block_size a)
  have hJ : J.card ≤ (X.blockCells a).card := by simpa only [Fintype.card_coe] using hcard
  exact hJ.trans hb

/-- The raw experiment fixes every noncritical state, including on each
positive-weight fiber used in the witness reduction. -/
theorem rawLaw_noncritical_fixed (D : LateData hPT) (X : CriticalTransferData D)
    (s : X.Raw) (hs : X.rawLaw.w s ≠ 0) :
    ∀ C, C ∉ X.criticalCells → X.state s C = X.fixed C := by
  intro C hC
  change (∏ C, (if C ∈ X.criticalCells then D.typicalFresh C else
    FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)).w (s C)) ≠ 0 at hs
  have hf := Finset.prod_ne_zero_iff.mp hs C (Finset.mem_univ C)
  have heq : s C = (D.l16_valid.pools_nonempty.choose C, X.fixed C) := by
    by_contra hn
    exact hf (by simp only [if_neg hC, FinLaw.dirac, if_neg hn])
  exact congrArg Prod.snd heq

/-- After removing the critical inputs, the withheld list depends on the fixed
noncritical configuration alone. -/
theorem withheldList_noncritical_fixed (D : LateData hPT) (X : CriticalTransferData D)
    (s : X.Raw) (hfixed : ∀ C, C ∉ X.criticalCells → X.state s C = X.fixed C) (w : Pos T k) :
    D.withheldList w (X.state s) (criticalExternalInputs D X w) =
      D.withheldList w X.fixed (criticalExternalInputs D X w) := by
  have hlab (j : Fin (T.S.n k)) (hj : j ∈ D.externalEarly w \ criticalExternalInputs D X w) :
      D.earlyLabel (X.state s) (flipPos w j) = D.earlyLabel X.fixed (flipPos w j) := by
    have hnot : D.geom.cellOf (flipPos w j) ∉ X.criticalCells := by
      intro hC
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hC⟩)
    unfold LateData.earlyLabel
    rw [hfixed _ hnot]
  ext x
  simp only [LateData.withheldList, Finset.mem_filter]
  constructor
  · intro hx
    exact ⟨hx.1, fun j hj => by rw [← hlab j hj]; exact hx.2 j hj⟩
  · intro hx
    exact ⟨hx.1, fun j hj => by rw [hlab j hj]; exact hx.2 j hj⟩

/-- The original masked-list gate supplies the short fixed lists that a local
block response encodes; no success condition is placed on erased sketches. -/
theorem fixedWithheldList_card (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hcount : ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℕ) : ℝ) ≤
      Real.log (T.S.n k : ℝ) ^ 4)
    (w : Pos T k) (hw : w ∈ X.directEven \ X.erased)
    (s : X.Raw) (hfixed : ∀ C, C ∉ X.criticalCells → X.state s C = X.fixed C)
    (hv : D.initialValid w (X.state s)) :
    (D.withheldList w X.fixed (criticalExternalInputs D X w)).card ≤
      Real.exp (Real.log (T.S.n k : ℝ) ^ 8) := by
  have hJ : ((criticalExternalInputs D X w).card : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 4 := by
    have hh : ((criticalExternalInputs D X w).card : ℝ) ≤
        ((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r : ℕ) : ℝ) := by
      exact_mod_cast criticalExternalInputs_card D X hG hmargin w hw
    exact hh.trans hcount
  apply le_of_not_gt
  intro hbad
  apply hv.2.1
  right
  refine ⟨criticalExternalInputs D X w, Finset.filter_subset _ _, hJ, ?_⟩
  rw [withheldList_noncritical_fixed D X s hfixed w]
  exact hbad

/-- The prerequisite gate covers initial validity at every direct even site,
which lies within 2r+1 of the current role. -/
theorem gate_directEven_initialValid (D : LateData hPT) (X : CriticalTransferData D)
    (hG : TransferGeometry X)
    (H : D.encoding.base.History X.failure.1.castSucc) (hg : D.gate X.failure.1 X.failure.2.1.1 H)
    (w : Pos T k) (hw : w ∈ X.directEven) : D.initialValid w H.1 := by
  obtain ⟨b, hb, d, hwd⟩ := directEven_representation D X w hw
  obtain ⟨j, hj⟩ := class_some_of_predecessor D X D.geom.r b hb
  have heven : IsEvenRole w := by
    rw [hwd]
    exact (S15.evenRole_flipPos b d).mpr (notEven_of_class_some D b j hj)
  have hball : w ∈ cubeBall X.failure.2.1.1 (6 * D.geom.r) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hdist := (Finset.mem_filter.mp (hG.predecessor_radius b hb)).2
    have hflip : hammingDist b w ≤ 1 := by rw [hwd]; exact hammingDist_flip_le_one b d
    have htri := hammingDist_triangle X.failure.2.1.1 b w
    have hr := D.l16_valid.r_pos
    change hammingDist X.failure.2.1.1 b ≤ 2 * D.geom.r at hdist
    change hammingDist X.failure.2.1.1 w ≤ 6 * D.geom.r
    omega
  exact hg.1 w hball heven
private theorem internalCoords_card_le (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    Fintype.card {a : Fin (T.S.n k) // a ∈ PT.tiling.Icoord i} ≤ (PT.tiling.P i).h := by
  classical
  let h := (PT.tiling.P i).h
  have hhn : h ≤ T.S.n k := by
    have hmax := Tiling.Valid.prefix_internal_length hPT.tiling_valid
    have hhmax : (PT.tiling.P i).h ≤
        Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
      Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
        (Finset.mem_univ i)
    omega
  let ix : {a : Fin (T.S.n k) // a ∈ PT.tiling.Icoord i} → Fin h := fun a =>
    ⟨a.1.val - (T.S.n k - h), by
      have hmem : T.S.n k - h ≤ a.1.val := by
        simpa [Tiling.Icoord, topCoordinates, h] using a.2
      omega⟩
  have hinj : Function.Injective ix := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [ix] at hv
    have haI : T.S.n k - h ≤ a.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using a.2
    have hbI : T.S.n k - h ≤ b.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using b.2
    exact (tsub_left_inj haI hbI).mp hv
  simpa using Fintype.card_le_of_injective ix hinj

private theorem twice_rpow_five_hundredths_le_self {L : ℝ} (hL : 4 ≤ L) :
    2 * Real.rpow L (1 / 20 : ℝ) ≤ L := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt (by positivity)
  have hsqrt : 2 ≤ Real.sqrt L := by nlinarith [hsqrtSq, Real.sqrt_nonneg L]
  have hpow : Real.rpow L (1 / 20 : ℝ) ≤ Real.rpow L (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  calc
    2 * Real.rpow L (1 / 20 : ℝ) ≤ 2 * Real.sqrt L := by
      rw [Real.sqrt_eq_rpow]
      exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ L := by nlinarith [hsqrtSq, hsqrt]


private theorem height_le_log (hκ : κ.Admissible) (D : LateData hPT) (i : Fin PT.tiling.m)
    (hL4 : 4 ≤ Real.log (T.S.n k : ℝ)) : (PT.tiling.P i).h ≤ Real.log (T.S.n k : ℝ) := by
  let n : ℝ := T.S.n k
  let L := Real.log n
  have hLpos : 0 < L := by dsimp [L, n]; linarith
  have hCb : 100 < κ.Cb := by
    have hratio : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith [hκ.Cb_big]
  have hMlo : 0 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big, hCb]
  have hcm : κ.cq * (κ.Mlo : ℝ) < 1 / 20 := by
    have hden' : 0 < 20 * (κ.Mlo : ℝ) := by positivity
    have hmul := (lt_div_iff₀ hden').mp hκ.cq_rng.2
    nlinarith
  have hHeight : ((PT.tiling.P i).h : ℝ) ≤ L := by
    cases hm : PT.tiling.mode with
    | bounded =>
        obtain ⟨_, hall⟩ := hPT.tiling_valid.bounded_data hm
        obtain ⟨_, hheight, _, _, _⟩ := hall i
        simpa [hheight] using (show (0 : ℝ) ≤ L from le_of_lt hLpos)
    | lowDirect =>
        obtain ⟨_, _, _, _, hheight, _, _⟩ := hPT.tiling_valid.direct_data (Or.inl hm) i
        simpa [hheight] using (show (0 : ℝ) ≤ L from le_of_lt hLpos)
    | lowCluster =>
        obtain ⟨_, _, _, _, _, _, _, _, hheight, hlowQ, _, _⟩ :=
          hPT.tiling_valid.cluster_data (Or.inl hm) i
        have hq : ((PT.tiling.P i).q : ℝ) ≤ Real.rpow L κ.cq := by
          simpa [L, n] using hlowQ.mp hm
        have hqpow : Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) ≤
            Real.rpow L (κ.cq * (κ.Mlo : ℝ)) := by
          calc
            Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) ≤
                Real.rpow (Real.rpow L κ.cq) (κ.Mlo : ℝ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hq (Nat.cast_nonneg _)
            _ = Real.rpow L (κ.cq * (κ.Mlo : ℝ)) := by
              exact (Real.rpow_mul (le_of_lt hLpos) κ.cq (κ.Mlo : ℝ)).symm
        have hqExp : Real.rpow L (κ.cq * (κ.Mlo : ℝ)) ≤ Real.rpow L (1 / 20 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [hL4]) hcm.le
        have hheightQ : ((PT.tiling.P i).h : ℝ) <
            2 * Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) := by
          simpa [hm] using hheight
        have hheightL : ((PT.tiling.P i).h : ℝ) < 2 * Real.rpow L (1 / 20 : ℝ) := by
          calc
            ((PT.tiling.P i).h : ℝ) <
                2 * Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) := hheightQ
            _ ≤ 2 * Real.rpow L (1 / 20 : ℝ) :=
              mul_le_mul_of_nonneg_left (hqpow.trans hqExp) (by norm_num)
        exact hheightL.le.trans (twice_rpow_five_hundredths_le_self hL4)
    | highDirect =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
    | highSmall =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
    | highLarge =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
  exact hHeight


/-- Uniform scalar cutoffs pay cell spacing, masked-list omissions, and the
complete per-block sketch-call budget in the protocol contract. -/
theorem protocol_scalar_cutoffs (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ i : Fin PT.tiling.m,
      ((2 * D.geom.r + 4 : ℕ) : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 3 ∧
      ((max 1 (PT.tiling.P i).h * D.geom.r : ℕ) : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 4 ∧
      ((D.geom.r * (max 1 (PT.tiling.P i).h * D.geom.r) *
        (1 + ((PT.tiling.Icoord i).card + 2) * D.geom.r) * ((PT.tiling.Icoord i).card + 1) : ℕ) : ℝ) ≤
        Real.log (T.S.n k : ℝ) ^ 20 := by
  let C : ℝ := max 1 (4 * κ.A0)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := Real.tendsto_log_atTop.comp hn
  filter_upwards [hlog.eventually_ge_atTop (max 4 (max (4 * C) (8 * C ^ 3)))] with k hk
  intro PT hPT D i
  let L := Real.log (T.S.n k : ℝ)
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hk
  have hLC : 4 * C ≤ L := (le_max_right _ _).trans hk |>.trans' (le_max_left _ _)
  have hLC3 : 8 * C ^ 3 ≤ L := (le_max_right _ _).trans hk |>.trans' (le_max_right _ _)
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hHeight := height_le_log hκ D i hL4
  have hI : ((PT.tiling.Icoord i).card : ℝ) ≤ L := by
    have hi : (PT.tiling.Icoord i).card ≤ (PT.tiling.P i).h := by
      simpa only [Fintype.card_coe] using internalCoords_card_le hPT i
    exact (show ((PT.tiling.Icoord i).card : ℝ) ≤ (PT.tiling.P i).h from by exact_mod_cast hi).trans hHeight
  have hM : ((max 1 (PT.tiling.P i).h : ℕ) : ℝ) ≤ L := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hL1 hHeight
  have hr : (D.geom.r : ℝ) ≤ C * L := by
    have hlog2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hscale : (D.geom.r : ℝ) ≤ 2 * ((D.geom.r : ℝ) * Real.log 2) := by
      nlinarith [show (0 : ℝ) ≤ D.geom.r from Nat.cast_nonneg _]
    have hupper : (D.geom.r : ℝ) * Real.log 2 ≤ 2 * κ.A0 * L := D.l16_valid.r_upper
    have hh : (D.geom.r : ℝ) ≤ (4 * κ.A0) * L := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL0.le)
  have hhr : ((max 1 (PT.tiling.P i).h * D.geom.r : ℕ) : ℝ) ≤ C * L ^ 2 := by
    rw [Nat.cast_mul]
    calc
      _ ≤ L * (C * L) := mul_le_mul hM hr (Nat.cast_nonneg _) hL0.le
      _ = _ := by ring
  have hi2 : ((PT.tiling.Icoord i).card : ℝ) + 1 ≤ 2 * L := by linarith
  have hi3 : ((PT.tiling.Icoord i).card : ℝ) + 2 ≤ 3 * L := by linarith
  have hbig : 1 + (((PT.tiling.Icoord i).card : ℝ) + 2) * D.geom.r ≤ 4 * C * L ^ 2 := by
    have hm := mul_le_mul hi3 hr (Nat.cast_nonneg D.geom.r) (by positivity : (0 : ℝ) ≤ 3 * L)
    have hu : 1 ≤ C * L ^ 2 := by
      have hsq : 1 ≤ L ^ 2 := by nlinarith
      simpa using mul_le_mul hC1 hsq (by norm_num : (0 : ℝ) ≤ 1) hC0.le
    nlinarith
  have hmargin : (2 * D.geom.r + 4 : ℕ) ≤ L ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hLC (sq_nonneg L)
    have hpow := mul_le_mul_of_nonneg_right hL4 (sq_nonneg L)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have homit : ((max 1 (PT.tiling.P i).h * D.geom.r : ℕ) : ℝ) ≤ L ^ 4 := by
    apply hhr.trans
    calc
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right (show C ≤ L by linarith) (sq_nonneg L)
      _ = L ^ 3 := by ring
      _ ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hhr' : ((max 1 (PT.tiling.P i).h : ℕ) : ℝ) * (D.geom.r : ℝ) ≤ C * L ^ 2 := by
    simpa only [Nat.cast_mul] using hhr
  have hcalls : ((D.geom.r * (max 1 (PT.tiling.P i).h * D.geom.r) *
      (1 + ((PT.tiling.Icoord i).card + 2) * D.geom.r) * ((PT.tiling.Icoord i).card + 1) : ℕ) : ℝ) ≤ L ^ 20 := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    calc
      _ ≤ (C * L) * (C * L ^ 2) * (4 * C * L ^ 2) * (2 * L) := by
        exact mul_le_mul (mul_le_mul (mul_le_mul hr hhr' (by positivity) (by positivity)) hbig
          (by positivity) (by positivity)) hi2 (by positivity) (by positivity)
      _ = (8 * C ^ 3) * L ^ 6 := by ring
      _ ≤ L * L ^ 6 := mul_le_mul_of_nonneg_right hLC3 (by positivity)
      _ = L ^ 7 := by ring
      _ ≤ L ^ 20 := pow_le_pow_right₀ hL1 (by norm_num)
  exact ⟨hmargin, homit, hcalls⟩

private theorem singleton_batches_pairwise {A : Type*} [DecidableEq A]
    (L : List A) (hL : L.Nodup) :
    (L.map fun a => ({a} : Finset A)).Pairwise Disjoint := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hL⟩
    intro B hB
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    rw [Finset.disjoint_singleton]
    intro heq
    exact ha (heq.symm ▸ hb)

private theorem base_batch_type (D : LateData hPT) (b : Pos T k)
    (B : Finset (Fin (T.S.n k)))
    (hB : B ∈ (Finset.univ \ PT.tiling.Icoord (D.geom.patchOf b)).toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
      (if PT.tiling.Icoord (D.geom.patchOf b) = ∅ then [] else [PT.tiling.Icoord (D.geom.patchOf b)])) :
    B = PT.tiling.Icoord (D.geom.patchOf b) ∨
      ∃ a ∈ Finset.univ \ PT.tiling.Icoord (D.geom.patchOf b), B = {a} := by
  rcases List.mem_append.mp hB with hB | hB
  · obtain ⟨a, ha, heq⟩ := List.mem_map.mp hB
    exact Or.inr ⟨a, by simpa using ha, heq.symm⟩
  · by_cases hi : PT.tiling.Icoord (D.geom.patchOf b) = ∅
    · simp [hi] at hB
    · exact Or.inl (by simpa [hi] using hB)

/-- Every batch in the frozen test orders is the internal batch or one external
singleton, and batches in one order are pairwise disjoint. -/
theorem testOrders_disjoint_batches (D : LateData hPT) (b : Pos T k) :
    ∀ order ∈ D.testOrders b, order.Pairwise Disjoint ∧
      ∀ B ∈ order, B = PT.tiling.Icoord (D.geom.patchOf b) ∨
        ∃ a ∈ Finset.univ \ PT.tiling.Icoord (D.geom.patchOf b), B = {a} := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let base := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
    (if intern = ∅ then [] else [intern])
  have hExt : (extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k))))).Pairwise Disjoint :=
    singleton_batches_pairwise _ extern.nodup_toList
  have hBase : base.Pairwise Disjoint := by
    dsimp [base]
    by_cases hi : intern = ∅
    · simpa only [if_pos hi, List.append_nil] using hExt
    · rw [if_neg hi, List.pairwise_append]
      refine ⟨hExt, by simp, ?_⟩
      intro A hA B hB
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
      have heq : B = intern := by simpa using hB
      subst B
      rw [Finset.disjoint_singleton_left]
      exact (Finset.mem_sdiff.mp (show a ∈ extern from by simpa using ha)).2
  have hType (B : Finset (Fin (T.S.n k))) (hB : B ∈ base) :
      B = intern ∨ ∃ a ∈ extern, B = {a} := base_batch_type D b B hB
  intro order ho
  change order ∈ base :: extern.toList.map _ at ho
  rcases List.mem_cons.mp ho with rfl | ho
  · exact ⟨hBase, hType⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    have haext : a ∈ extern := by simpa using ha
    have hPair : (base.filter (fun B => B ≠ {a}) ++ [{a}]).Pairwise Disjoint := by
      rw [List.pairwise_append]
      refine ⟨hBase.sublist List.filter_sublist, by simp, ?_⟩
      intro B hB C hC
      have hBe : B ∈ base := (List.mem_filter.mp hB).1
      have hne : B ≠ {a} := by simpa using (List.mem_filter.mp hB).2
      have hCa : C = {a} := by simpa using hC
      subst C
      rcases hType B hBe with heq | ⟨t, ht, heq⟩
      · subst B
        rw [Finset.disjoint_singleton_right]
        exact (Finset.mem_sdiff.mp haext).2
      · subst B
        rw [Finset.disjoint_singleton]
        intro heq
        exact hne (congrArg (fun x => ({x} : Finset (Fin (T.S.n k)))) heq)
    refine ⟨hPair, ?_⟩
    intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact hType B (List.mem_filter.mp hB).1
    · exact Or.inr ⟨a, haext, by simpa using hB⟩

/-- A tested prefix is disjoint from the current batch. -/
theorem prefix_disjoint_current_batch (D : LateData hPT) (b : Pos T k)
    (order : List (Finset (Fin (T.S.n k)))) (ho : order ∈ D.testOrders b)
    (q : ℕ) (hq : q < order.length) :
    Disjoint (D.prefixTests order q) (order.getD q ∅) := by
  have hPw := (testOrders_disjoint_batches D b order ho).1
  apply Finset.disjoint_left.mpr
  intro a ha hcur
  have hm : ∃ B ∈ order.take q, a ∈ B := by
    simpa only [LateData.prefixTests, mem_foldl_union, Finset.notMem_empty, false_or] using ha
  obtain ⟨B, hB, hab⟩ := hm
  obtain ⟨p, hp, hBp⟩ := List.mem_iff_getElem.mp hB
  have hpmin : p < min q order.length := by simpa only [List.length_take] using hp
  have hpq : p < q := hpmin.trans_le (Nat.min_le_left _ _)
  have hpl : p < order.length := hpmin.trans_le (Nat.min_le_right _ _)
  have hBi : order[p] = B := by simpa only [List.getElem_take] using hBp
  have hd := List.pairwise_iff_getElem.mp hPw p q hpl hq hpq
  have hcur' : a ∈ order[q] := by
    rw [List.getD_eq_getElem order ∅ hq] at hcur
    exact hcur
  exact Finset.disjoint_left.mp hd (by rw [hBi]; exact hab) hcur'

/-- The current tested prefix already omits all sketches in the erased word. -/
theorem prefix_tests_exclude_erased (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ a ∈ D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val,
      flipPos X.failure.2.1.1 a ∉ X.erased := by
  let b := X.failure.2.1.1
  let a0 := X.failure.2.2.2.2
  let order := D.prefixOrder X.failure
  let q := X.failure.2.2.2.1.val
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  have ho : order ∈ D.testOrders b := by
    have heq := List.getD_eq_getElem (D.testOrders b) [] X.valid.1
    change (D.testOrders b).getD X.failure.2.2.1.val [] ∈ D.testOrders b
    rw [heq]
    exact List.getElem_mem X.valid.1
  have hq : q < order.length := X.valid.2.1
  have ha0 : a0 ∈ order.getD q ∅ := X.valid.2.2
  have hDisj := prefix_disjoint_current_batch D b order ho q hq
  have htarget : X.target = flipPos b a0 := rfl
  intro a ha hErased
  have haa0 : a ≠ a0 := by
    intro heq
    subst a
    exact Finset.disjoint_left.mp hDisj ha ha0
  have hOuter := (Finset.mem_filter.mp hErased).2
  by_cases ha0I : a0 ∈ intern
  · have hp : D.geom.patchOf X.target = D.geom.patchOf b := by
      rw [htarget]
      exact internal_patch D b a0 ha0I
    have hbatch : order.getD q ∅ = intern := by
      have hm := List.getD_eq_getElem order ∅ hq
      have hbmem : order.getD q ∅ ∈ order := by rw [hm]; exact List.getElem_mem hq
      rcases (testOrders_disjoint_batches D b order ho).2 _ hbmem with hB | ⟨t, ht, hB⟩
      · exact hB
      · have hat : a0 = t := by simpa only [hB, Finset.mem_singleton] using ha0
        subst t
        exact False.elim ((Finset.mem_sdiff.mp ht).2 ha0I)
    have haI : a ∉ intern := fun hi => Finset.disjoint_left.mp hDisj ha (by simpa only [hbatch] using hi)
    have haTarget : a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by simpa only [hp] using haI
    have hv := hOuter a haTarget
    rw [htarget] at hv
    change flipPos b a a = flipPos b a0 a at hv
    cases hbval : b a <;> simp [flipPos, haa0, hbval] at hv
  · have ha0Target : a0 ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
      intro hI
      have hp := internal_patch D X.target a0 hI
      rw [htarget, flipPos_involutive] at hp
      apply ha0I
      change a0 ∈ PT.tiling.Icoord (D.geom.patchOf b)
      rw [hp]
      exact hI
    have hv := hOuter a0 ha0Target
    rw [htarget] at hv
    change flipPos b a a0 = flipPos b a0 a0 at hv
    cases hbval : b a0 <;> simp [flipPos, haa0.symm, hbval] at hv

/-- Changing erased sketch coordinates leaves the current prefix label law
unchanged at the same mask. This is an identity before any seed is fixed. -/
theorem prefixLabelWeight_erased_invariant (D : LateData hPT) (X : CriticalTransferData D)
    (out out' : D.encoding.base.RowOut X.failure.2.1.1)
    (hmask : out.1 = out'.1)
    (hsketch : ∀ a, flipPos X.failure.2.1.1 a ∉ X.erased → out.2.1 a = out'.2.1 a)
    (y : Fin (T.S.N k)) :
    D.labelWeight X.failure.1 out (D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val) y =
      D.labelWeight X.failure.1 out' (D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val) y := by
  let tests := D.prefixTests (D.prefixOrder X.failure) X.failure.2.2.2.1.val
  have hp (u : Fin (T.S.N k)) : D.passes X.failure.1 out tests u ↔ D.passes X.failure.1 out' tests u := by
    constructor <;> intro h a ha <;>
      simpa only [LateData.sketchHit, hsketch a (prefix_tests_exclude_erased D X a ha)] using h a ha
  have hm (u : Fin (T.S.N k)) : D.maskWeight out u = D.maskWeight out' u := by
    unfold LateData.maskWeight
    rw [hmask]
  have hmass : D.retainedMass X.failure.1 out tests = D.retainedMass X.failure.1 out' tests := by
    unfold LateData.retainedMass
    simp_rw [hp, hm]
  change D.labelWeight X.failure.1 out tests y = D.labelWeight X.failure.1 out' tests y
  unfold LateData.labelWeight
  rw [hmass, hp, hm]

/-- A responding block fills its own cells from the raw input and uses the fixed
configuration everywhere else, giving a total computation off the sampled path. -/
noncomputable def blockConfig (D : LateData hPT) (X : CriticalTransferData D)
    (a : Fin (T.S.n k)) (s : X.Raw) : Config D.fresh :=
  fun C => if C ∈ X.blockCells a then X.state s C else X.fixed C

/-- The block computation reads only the requested whole-cell input. -/
theorem blockConfig_local (D : LateData hPT) (X : CriticalTransferData D)
    (a : Fin (T.S.n k)) (s s' : X.Raw)
    (hs : ∀ C ∈ X.blockCells a, s C = s' C) : blockConfig D X a s = blockConfig D X a s' := by
  funext C
  unfold blockConfig
  by_cases hC : C ∈ X.blockCells a
  · simp only [if_pos hC]
    exact congrArg Prod.snd (hs C hC)
  · simp only [if_neg hC]

/-- On a raw-law support point, replacing other cells by fixed inputs preserves
all direct data of a site assigned to this block. -/
theorem blockConfig_agrees (D : LateData hPT) (X : CriticalTransferData D)
    (a : Fin (T.S.n k)) (s : X.Raw) (hs : X.rawLaw.w s ≠ 0) (w : Pos T k)
    (hscope : D.directCells w ∩ X.criticalCells ⊆ X.blockCells a) :
    ∀ C ∈ D.directCells w, X.state s C = blockConfig D X a s C := by
  have hfixed := rawLaw_noncritical_fixed D X s hs
  intro C hC
  unfold blockConfig
  by_cases hblock : C ∈ X.blockCells a
  · simp only [if_pos hblock]
  · simp only [if_neg hblock]
    apply hfixed
    intro hcrit
    exact hblock (hscope (Finset.mem_inter.mpr ⟨hC, hcrit⟩))

/-- The local block history produces exactly the original current prior on the
supported path and keeps the fixed fallback on invalid or zero computations. -/
theorem block_currentPrior_eq (D : LateData hPT) (X : CriticalTransferData D) (hD : D.Spec)
    (a : Fin (T.S.n k)) (s : X.Raw) (hs : X.rawLaw.w s ≠ 0)
    (j : Fin D.geom.r) (w : Pos T k) (H : D.encoding.base.History j.castSucc)
    (hinit : H.1 = X.state s) (hscope : D.directCells w ∩ X.criticalCells ⊆ X.blockCells a) :
    D.currentPrior j w H = D.currentPrior j w (blockConfig D X a s, H.2) := by
  apply Lane_sol_s18_n4.priorAt_local D hD j.castSucc w
  · intro C hC
    rw [hinit]
    exact blockConfig_agrees D X a s hs w hscope C hC
  · intro b hb
    rfl

/-- Arbitrary off-path raw inputs agreeing on one block produce the same local
prior when the preceding row labels are supplied by the transcript. -/
theorem block_currentPrior_local (D : LateData hPT) (X : CriticalTransferData D)
    (a : Fin (T.S.n k)) (s s' : X.Raw)
    (hs : ∀ C ∈ X.blockCells a, s C = s' C)
    (j : Fin D.geom.r) (w : Pos T k)
    (rows : ∀ b : D.encoding.base.ProcessedRole j.castSucc, D.encoding.base.RowOut b.1) :
    D.currentPrior j w (blockConfig D X a s, rows) =
      D.currentPrior j w (blockConfig D X a s', rows) := by
  rw [blockConfig_local D X a s s' hs]

end HypercubeRamsey.Lane_sol_s18_1c
