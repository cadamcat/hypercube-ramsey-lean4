import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S18.Sampler_sol_s18_n4
import HypercubeRamsey.S17.Nodes_q_s17_pool
import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.S18.Nodes_sol_s18_n5

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

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

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
      (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1}) :
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
    · obtain ⟨hprefix, hdelete, _⟩ := hB j b.1 h (mask, s, y) b.2 hg hgood.1 hgood.2.1
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
      apply E_mono
      intro s
      unfold FinLaw.E
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      convert hpoint mask s y using 1 <;> congr 1
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

end HypercubeRamsey.Lane_sol_s18_1c
