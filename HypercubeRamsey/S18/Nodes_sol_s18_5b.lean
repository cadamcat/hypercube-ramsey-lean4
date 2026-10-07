import HypercubeRamsey.S18.Comparisons_sol_s18_n5
import HypercubeRamsey.S18.Nodes_q_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_5b
set_option maxHeartbeats 400000
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem labelWeight_nonneg (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (out : D.encoding.base.RowOut b) (y : Fin (T.S.N k)) :
    0 ≤ D.labelWeight j out Finset.univ y := by
  have hmask : 0 ≤ D.maskWeight out y := by
    unfold LateData.maskWeight
    split_ifs <;> positivity
  unfold LateData.labelWeight
  split_ifs with hmass hpass
  · exact div_nonneg hmask (le_trans (Real.exp_pos _).le hmass)
  · exact le_rfl
  · exact hmask

private theorem sum_subtype_le {Ω : Type*} [Fintype Ω] (S : Finset Ω)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x : {x // x ∈ S}, f x.1) ≤ ∑ x, f x := by
  classical
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)

/-- The side predicate remains inside the reference integral until the
conditional label sum has used the pair part of equation (27). -/
theorem reference_pair_hit (D : LateData hPT) (hTransition : TransitionData D)
    {K27 : ℝ} (hBroad : BroadDeletionFacts D K27) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (a : Fin (T.S.n k))
    (x z : Fin (T.S.N k))
    (hx : (D.initialPrior (flipPos b.1 a) h.1).w x ≠ 0)
    (hz : (D.initialPrior (flipPos b.1 a) h.1).w z ≠ 0)
    (hnc : D.nonconflict (flipPos b.1 a) x z) :
    (D.encoding.kernels.refK j b h).E (fun out =>
      if D.gate j b.1 h ∧ D.R1 j out ∧ D.R2 j h out then
        if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel out) ∧
          Hits (T.S.E k) PT.tiling.c z (D.encoding.base.rowLabel out) then (4 : ℝ) else 0
      else 0) ≤
    Real.exp (K27 * (if a ∈ PT.tiling.Icoord (D.geom.patchOf b.1) then
      ((PT.tiling.P (D.geom.patchOf b.1)).h : ℝ) else 1) * D.error (flipPos b.1 a) j) := by
  classical
  let cost := Real.exp (K27 * (if a ∈ PT.tiling.Icoord (D.geom.patchOf b.1) then
    ((PT.tiling.P (D.geom.patchOf b.1)).h : ℝ) else 1) * D.error (flipPos b.1 a) j)
  have hc : 0 ≤ cost := (Real.exp_pos _).le
  let hit := fun y : Fin (T.S.N k) =>
    Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
  have hside (M : D.encoding.base.AllowedMask b.1)
      (sk : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :
      (∑ y : {y // y ∈ D.encoding.base.latePoolOf b.1},
        D.labelWeight j (M, sk, y) Finset.univ y.1 *
          (if D.gate j b.1 h ∧ D.R1 j (M, sk, y) ∧ D.R2 j h (M, sk, y) then
            if hit y.1 then (4 : ℝ) else 0 else 0)) ≤ cost := by
    by_cases hg : D.gate j b.1 h
    · have hpool : (D.encoding.base.latePoolOf b.1).Nonempty := by
        simpa only [LateProcessBase.latePoolOf,
          (D.encoding.base.class_of_spec b.1 j).mp b.2]
          using (Finset.card_pos.mp (D.late_pool_pos j))
      let y₀ : {y // y ∈ D.encoding.base.latePoolOf b.1} :=
        ⟨hpool.choose, hpool.choose_spec⟩
      by_cases hR : D.R1 j (M, sk, y₀) ∧ D.R2 j h (M, sk, y₀)
      · -- Obligation from the `InitialSketchSupport` guard added to `BroadDeletionFacts` (main 1e2cca1): either the
        -- sketch `sk` is supported, or its reference weight vanishes. Owner: lane sol-s18-supp.
        have hSupp : InitialSketchSupport D j h (M, sk, y₀) := by
          sorry
        have hp := (hBroad j b.1 h (M, sk, y₀) b.2 hg hSupp hR.1 hR.2).2.2.2 a x z hx hz hnc
        have heq (y : {y // y ∈ D.encoding.base.latePoolOf b.1}) :
            D.labelWeight j (M, sk, y) Finset.univ y.1 =
              D.labelWeight j (M, sk, y₀) Finset.univ y.1 := rfl
        have hR' (y : {y // y ∈ D.encoding.base.latePoolOf b.1}) :
            D.R1 j (M, sk, y) ∧ D.R2 j h (M, sk, y) := hR
        simp only [hg, true_and, hR', if_true]
        simp only [heq]
        have hs := sum_subtype_le (D.encoding.base.latePoolOf b.1)
          (fun y => D.labelWeight j (M, sk, y₀) Finset.univ y * (if hit y then 4 else 0))
          (fun y => mul_nonneg (labelWeight_nonneg D j _ _) (by split_ifs <;> norm_num))
        apply hs.trans
        have hs' : (∑ y, D.labelWeight j (M, sk, y₀) Finset.univ y *
            (if hit y then (4 : ℝ) else 0)) =
            4 * (∑ y, if hit y then D.labelWeight j (M, sk, y₀) Finset.univ y else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : hit y <;> simp [hy, mul_comm]
        rw [hs']
        simp only [Nat.cast_ite, Nat.cast_one] at hp
        change (∑ y, if hit y then D.labelWeight j (M, sk, y₀) Finset.univ y else 0) ≤ (1 / 4) * cost at hp
        linarith
      · have hR' (y : {y // y ∈ D.encoding.base.latePoolOf b.1}) :
            ¬ (D.R1 j (M, sk, y) ∧ D.R2 j h (M, sk, y)) := hR
        simp only [hg, true_and, hR', if_false, mul_zero, Finset.sum_const_zero]
        exact hc
    · simp only [hg, false_and, if_false, mul_zero, Finset.sum_const_zero]
      exact hc
  unfold FinLaw.E
  simp_rw [hTransition.reference_formula]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hsum :
      (∑ sk : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k),
        ∏ c, ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (sk c t)) = 1 := by
    calc
      _ = ∏ c, ∑ skc : Fin (sketchLength T k) → Fin (T.S.N k),
          ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (skc t) :=
        (Fintype.prod_sum (fun c (skc : Fin (sketchLength T k) → Fin (T.S.N k)) =>
          ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (skc t))).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro c _
        rw [← Fintype.prod_sum]
        simp [(D.currentPrior j (flipPos b.1 c) h).sum_eq_one]
  calc
    _ ≤ ∑ M : D.encoding.base.AllowedMask b.1,
        ∑ sk : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k),
        ((D.encoding.kernels.maskProfile b.1).w M *
          ∏ c, ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (sk c t)) * cost := by
      apply Finset.sum_le_sum
      intro M _
      apply Finset.sum_le_sum
      intro sk _
      change (∑ y, (((D.encoding.kernels.maskProfile b.1).w M *
          ∏ c, ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (sk c t)) *
        D.labelWeight j (M, sk, y) Finset.univ y.1) *
        (if D.gate j b.1 h ∧ D.R1 j (M, sk, y) ∧ D.R2 j h (M, sk, y) then
          if hit y.1 then (4 : ℝ) else 0 else 0)) ≤ _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hcoef : 0 ≤ (D.encoding.kernels.maskProfile b.1).w M *
          ∏ c, ∏ t, (D.currentPrior j (flipPos b.1 c) h).w (sk c t) := by
        apply mul_nonneg ((D.encoding.kernels.maskProfile b.1).nonneg M)
        apply Finset.prod_nonneg
        intro c _
        apply Finset.prod_nonneg
        intro t _
        exact (D.currentPrior j (flipPos b.1 c) h).nonneg _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hside M sk) hcoef
    _ = cost := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hsum, one_mul, (D.encoding.kernels.maskProfile b.1).sum_one, one_mul]


private theorem E_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hfg x) (P.nonneg x)

private theorem E_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.E f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

/-- Independent reference rows factor even when the selected side tests
retain their own masks and sketches. -/
theorem pi_E_prod {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun out => ∏ i, f i (out i)) = ∏ i, (P i).E (f i) := by
  change (∑ out : ∀ i, Ω i, (∏ i, (P i).w (out i)) * (∏ i, f i (out i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (P i).w x * f i x)).symm

/-- The sampler comparison applies to the selected row set, leaving the
entering-history predicate in force until it has been used. -/
theorem selected_actual_product (D : LateData hPT) {δ : ℝ}
    (A : ClassSamplerData D δ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (henter : D.enter δ j h)
    (S : Finset {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hsmall : (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3))
    (f : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      D.encoding.base.RowOut b.1 → ℝ)
    (hf : ∀ b out, 0 ≤ f b out)
    (cost : {b : Pos T k // b ∈ D.encoding.base.classes j} → ℝ)
    (hcost : ∀ b ∈ S, (D.encoding.kernels.refK j b h).E (f b) ≤ cost b) :
    (A.act j h).E (fun out => ∏ b ∈ S, f b (out b)) ≤ 2 * ∏ b ∈ S, cost b := by
  classical
  have hn : ∀ out : D.encoding.base.ClassRows j, 0 ≤ ∏ b ∈ S, f b (out b) :=
    fun out => Finset.prod_nonneg (fun b _ => hf b (out b))
  have hlocal : DependsOn (fun out : D.encoding.base.ClassRows j => ∏ b ∈ S, f b (out b))
      (S : Set _) := by
    intro out out' heq
    apply Finset.prod_congr rfl
    intro b hb
    rw [heq b hb]
  apply ((A.sampler j h henter).2 S hsmall _ hn hlocal).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let g : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      D.encoding.base.RowOut b.1 → ℝ := fun b out => if b ∈ S then f b out else 1
  have hprod (out : D.encoding.base.ClassRows j) :
      (∏ b ∈ S, f b (out b)) = ∏ b, g b (out b) := by
    simp only [g]
    rw [← Finset.prod_filter]
    congr 1
    ext b
    simp
  simp_rw [hprod]
  change (FinLaw.pi (fun b => D.encoding.kernels.refK j b h)).E
    (fun out => ∏ b, g b (out b)) ≤ _
  rw [pi_E_prod]
  have hmean b : (D.encoding.kernels.refK j b h).E (g b) =
      if b ∈ S then (D.encoding.kernels.refK j b h).E (f b) else 1 := by
    by_cases hb : b ∈ S
    · simp only [g, hb, if_true]
    · simp only [g, hb, if_false]
      exact Lane_sol_s18_n5.E_const _ 1
  simp_rw [hmean]
  rw [← Finset.prod_filter]
  have hfilter : Finset.univ.filter (fun b => b ∈ S) = S := by ext b; simp
  rw [hfilter]
  exact Finset.prod_le_prod₀ (fun b hb => E_nonneg _ (hf b)) hcost

/-- Exact normalized restriction, including the proof that the second
normalizer is positive. This is the algebra needed at every late incidence. -/
theorem normalize_restrict (D : LateData hPT) (f : Fin (T.S.N k) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ x, f x) (R : Fin (T.S.N k) → Prop)
    (hm : 0 < ∑ x, if R x then (D.normalize f).w x else 0) :
    ∀ x, (D.normalize (fun y => f y * (if R y then 1 else 0))).w x =
      (D.normalize f).w x * (if R x then 1 else 0) /
        (∑ y, if R y then (D.normalize f).w y else 0) := by
  classical
  have hfn : (∀ x, 0 ≤ f x) ∧ 0 < ∑ x, f x := ⟨hf, hpos⟩
  have heq : (∑ y, if R y then (D.normalize f).w y else 0) =
      (∑ y, f y * (if R y then 1 else 0)) / (∑ y, f y) := by
    simp only [LateData.normalize, dif_pos hfn]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : R y <;> simp [hy]
  have hp : 0 < ∑ y, f y * (if R y then 1 else 0) := by
    rw [heq] at hm
    exact (div_pos_iff_of_pos_right hpos).mp hm
  have hfp : (∀ y, 0 ≤ f y * (if R y then 1 else 0)) ∧
      0 < ∑ y, f y * (if R y then 1 else 0) := by
    refine ⟨?_, hp⟩
    intro y
    split_ifs <;> simp [hf y]
  intro x
  rw [heq]
  simp only [LateData.normalize, dif_pos hfp, dif_pos hfn]
  field_simp [hpos.ne', hp.ne']

/-- The squared true-hit denominator costs four times an exponential in
its error, uniformly for an error at most one twelfth. -/
theorem squared_hit_cost (e m : ℝ) (he : 0 ≤ e) (hsmall : e ≤ 1 / 12)
    (hm : (1 / 2 : ℝ) - 3 * e ≤ m) :
    m⁻¹ ^ 2 ≤ 4 * Real.exp (24 * e) := by
  have hd : 0 < (1 / 2 : ℝ) - 3 * e := by linarith
  have hmp : 0 < m := hd.trans_le hm
  have hexp : 1 + 12 * e ≤ Real.exp (12 * e) := by simpa only [add_comm] using Real.add_one_le_exp (12 * e)
  have hprod : 1 ≤ ((1 / 2 : ℝ) - 3 * e) * (2 * Real.exp (12 * e)) := by
    have hmul := mul_le_mul_of_nonneg_left hexp hd.le
    have hquad : 72 * e ^ 2 ≤ 6 * e := by nlinarith
    nlinarith
  have hinv : m⁻¹ ≤ 2 * Real.exp (12 * e) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hmp).mpr
    rw [mul_comm]
    calc
      1 ≤ ((1 / 2 : ℝ) - 3 * e) * (2 * Real.exp (12 * e)) := hprod
      _ ≤ m * (2 * Real.exp (12 * e)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
  calc
    m⁻¹ ^ 2 ≤ (2 * Real.exp (12 * e)) ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2
    _ = 4 * Real.exp (24 * e) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have heq : (2 : ℝ) * (12 * e) = 24 * e := by ring
      norm_num only [Nat.cast_ofNat]
      rw [heq]


/-- Prefix histories and current outputs of an extension are the original
objects. These identities retain the actual reach predicates in the run. -/
theorem before_extend (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (t : Fin (D.geom.r + 1)) (ht : t.val ≤ j.val) :
    D.beforeHistory (D.encoding.base.extend j h out) t (by simpa using ht.trans (Nat.le_succ j.val)) =
      D.beforeHistory h t ht := by
  apply Prod.ext
  · rfl
  · funext b
    have hb : b.1 ∈ D.encoding.base.processed j.castSucc :=
      D.processed_mono t j.castSucc ht b.2
    simp only [LateData.beforeHistory, LateProcessBase.extend, dif_pos hb]

theorem past_extend (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    D.pastRows (D.encoding.base.extend j h out) j (by simp) = out := by
  funext b
  have hb : b.1 ∉ D.encoding.base.processed j.castSucc :=
    fun hh => Finset.disjoint_left.mp (D.encoding.base.class_fresh j) b.2 hh
  simp only [LateData.pastRows, LateProcessBase.extend, dif_neg hb]

noncomputable def prefixGate (D : LateData hPT) (δ : ℝ)
    (t : Fin (D.geom.r + 1)) (h : D.encoding.base.History t) : Prop :=
  ∀ j : Fin D.geom.r, ∀ hj : j.val < t.val,
    let pre := D.beforeHistory h j.castSucc (Nat.le_of_lt hj)
    let out := D.pastRows h j hj
    D.enter δ j pre ∧ ∀ b, D.gate j b.1 pre ∧ D.R1 j (out b) ∧ D.R2 j pre (out b)

theorem full_prefixGate (D : LateData hPT) (δ : ℝ) (x : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ x h) :
    prefixGate D δ (Fin.last D.geom.r) h := by
  intro j hj
  refine ⟨(hf.2.2.2.2.2.2 j).1, ?_⟩
  intro b
  have hs := Lane_sol_s18_n5.full_side_requirements D δ x h hf j b
  exact ⟨((hf.2.2.2.2.2.2 j).2.2.2.2 b).1, hs.1, hs.2.1⟩

theorem prefixGate_extend (D : LateData hPT) (δ : ℝ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    prefixGate D δ j.succ (D.encoding.base.extend j h out) ↔
      prefixGate D δ j.castSucc h ∧ D.enter δ j h ∧
        ∀ b, D.gate j b.1 h ∧ D.R1 j (out b) ∧ D.R2 j h (out b) := by
  have hpre : D.beforeHistory (D.encoding.base.extend j h out) j.castSucc (by simp) = h := by
    rw [before_extend D j h out j.castSucc (Nat.le_refl j.val)]
    apply Prod.ext
    · rfl
    · funext b
      rfl
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · intro i hi
      have hp := hg i (by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega)
      have he := before_extend D j h out i.castSucc (Nat.le_of_lt hi)
      have ho : D.pastRows (D.encoding.base.extend j h out) i (by
          simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega) = D.pastRows h i hi := by
        funext b
        have hb : b.1 ∈ D.encoding.base.processed j.castSucc :=
          D.class_before i j.castSucc hi b.2
        simp only [LateData.pastRows, LateProcessBase.extend, dif_pos hb]
      simpa only [he, ho] using hp
    · have hp := hg j (by simp)
      simpa only [hpre, past_extend] using hp
  · rintro ⟨hg, henter, hs⟩ i hi
    by_cases hij : i = j
    · subst i
      simpa only [hpre, past_extend] using And.intro henter hs
    · have hi' : i.val < j.val := by
        have hn : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
        simp only [Fin.val_succ] at hi
        omega
      have hp := hg i hi'
      have he := before_extend D j h out i.castSucc (Nat.le_of_lt hi')
      have ho : D.pastRows (D.encoding.base.extend j h out) i hi = D.pastRows h i hi' := by
        funext b
        have hb : b.1 ∈ D.encoding.base.processed j.castSucc :=
          D.class_before i j.castSucc hi' b.2
        simp only [LateData.pastRows, LateProcessBase.extend, dif_pos hb]
      simpa only [he, ho] using hp


private theorem map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

private theorem E_mul_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (c : ℝ) (f : Ω → ℝ) : P.E (fun x => c * f x) = c * P.E f := by
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem dirac_E {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (a : Ω) (f : Ω → ℝ) : (FinLaw.dirac a).E f = f a := by
  unfold FinLaw.E FinLaw.dirac
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

/-- Backward integration of the actual run. The one-step premise still
contains that class's reach and side gates; the recurrence removes them
only after its conditional sampler estimate. -/
theorem backward_run (D : LateData hPT) {δ : ℝ} (A : ClassSamplerData D δ)
    (s : Config D.fresh)
    (ψ : ∀ t : Fin (D.geom.r + 1), D.encoding.base.History t → ℝ)
    (cost : Fin D.geom.r → ℝ) (hcost : ∀ j, 0 ≤ cost j)
    (hstep : ∀ (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc),
      (A.act j h).E (fun out =>
        if prefixGate D δ j.succ (D.encoding.base.extend j h out) then
          ψ j.succ (D.encoding.base.extend j h out) else 0) ≤
        cost j * (if prefixGate D δ j.castSucc h then ψ j.castSucc h else 0)) :
    ∀ m (hm : m ≤ D.geom.r),
      (D.encoding.base.runFrom A.act s m hm).E (fun h =>
        if prefixGate D δ ⟨m, Nat.lt_succ_of_le hm⟩ h then
          ψ ⟨m, Nat.lt_succ_of_le hm⟩ h else 0) ≤
      (∏ j : Fin D.geom.r, if j.val < m then cost j else 1) *
        ψ 0 (D.encoding.base.initialHistory s) := by
  intro m
  induction m with
  | zero =>
      intro hm
      change (FinLaw.dirac (D.encoding.base.initialHistory s)).E
        (fun h : D.encoding.base.History 0 => if prefixGate D δ 0 h then ψ 0 h else 0) ≤ _
      rw [dirac_E]
      have hg : prefixGate D δ 0 (D.encoding.base.initialHistory s) := by
        intro j hj
        exact False.elim (by simpa using hj)
      simp [hg]
  | succ m ih =>
      intro hm
      let j : Fin D.geom.r := ⟨m, hm⟩
      rw [LateProcessBase.runFrom, map_E, Lane_sol_s18_n5.bind_E]
      have hp :
          (∏ i : Fin D.geom.r, if i.val < m + 1 then cost i else 1) =
            cost j * (∏ i : Fin D.geom.r, if i.val < m then cost i else 1) := by
        have heq : (fun i : Fin D.geom.r => if i.val < m + 1 then cost i else 1) =
            fun i => (if i = j then cost j else 1) * (if i.val < m then cost i else 1) := by
          funext i
          by_cases hij : i = j
          · subst i
            simp [j]
          · have hn : i.val ≠ m := fun hh => hij (Fin.ext hh)
            by_cases hi : i.val < m <;> simp [hij, hi, show (i.val < m + 1) ↔ i.val < m by omega]
        rw [heq, Finset.prod_mul_distrib]
        simp
      calc
        _ ≤ cost j * (D.encoding.base.runFrom A.act s m (Nat.le_of_succ_le hm)).E
            (fun h => if prefixGate D δ j.castSucc h then ψ j.castSucc h else 0) := by
          rw [← E_mul_const]
          apply E_mono
          intro h
          exact hstep j h
        _ ≤ cost j * ((∏ i : Fin D.geom.r, if i.val < m then cost i else 1) *
            ψ 0 (D.encoding.base.initialHistory s)) :=
          mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hm)) (hcost j)
        _ = _ := by rw [hp]; ring

/-- A local product estimate supplies the backward step without a global
comparison of class outputs. -/
theorem backward_step (D : LateData hPT) {δ : ℝ} (A : ClassSamplerData D δ)
    (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc)
    (ψ : ∀ t : Fin (D.geom.r + 1), D.encoding.base.History t → ℝ)
    (hψ : 0 ≤ ψ j.castSucc h) (f : D.encoding.base.ClassRows j → ℝ)
    (hf : ∀ out, 0 ≤ f out) (c : ℝ) (hc : 0 ≤ c)
    (hlocal : D.enter δ j h → (A.act j h).E f ≤ c)
    (hfactor : ∀ out, prefixGate D δ j.succ (D.encoding.base.extend j h out) →
      ψ j.succ (D.encoding.base.extend j h out) ≤ ψ j.castSucc h * f out) :
    (A.act j h).E (fun out =>
      if prefixGate D δ j.succ (D.encoding.base.extend j h out) then
        ψ j.succ (D.encoding.base.extend j h out) else 0) ≤
      c * (if prefixGate D δ j.castSucc h then ψ j.castSucc h else 0) := by
  by_cases hg : prefixGate D δ j.castSucc h
  · by_cases he : D.enter δ j h
    · calc
        _ ≤ (A.act j h).E (fun out => ψ j.castSucc h * f out) := by
          apply E_mono
          intro out
          split_ifs with ho
          · exact hfactor out ho
          · exact mul_nonneg hψ (hf out)
        _ = ψ j.castSucc h * (A.act j h).E f := E_mul_const _ _ _
        _ ≤ ψ j.castSucc h * c := mul_le_mul_of_nonneg_left (hlocal he) hψ
        _ = _ := by simp only [hg, if_true]; ring
    · have hn out : ¬ prefixGate D δ j.succ (D.encoding.base.extend j h out) := by
        intro ho
        exact he ((prefixGate_extend D δ j h out).mp ho).2.1
      simp only [hn, if_false]
      rw [Lane_sol_s18_n5.E_const]
      simp only [hg, if_true]
      exact mul_nonneg hc hψ
  · have hn out : ¬ prefixGate D δ j.succ (D.encoding.base.extend j h out) := by
      intro ho
      exact hg ((prefixGate_extend D δ j h out).mp ho).1
    simp only [hn, hg, if_false, mul_zero]
    exact le_of_eq (Lane_sol_s18_n5.E_const _ 0)


noncomputable def classHit (D : LateData hPT) (j : Fin D.geom.r)
    (out : D.encoding.base.ClassRows j) (v : Pos T k) (x : Fin (T.S.N k)) : ℝ :=
  ∏ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (out b)) then 1 else 0)
    else 1

/-- The raw restriction factors across the disjoint processed/current
class partition, using the actual labels in the extended history. -/
theorem weightAt_extend (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (v : Pos T k) (x : Fin (T.S.N k)) :
    Lane_sol_s18_n5.weightAt D j.succ (D.encoding.base.extend j h out) v x =
      Lane_sol_s18_n5.weightAt D j.castSucc h v x * classHit D j out v x := by
  let B : Finset (D.encoding.base.ProcessedRole j.succ) :=
    Finset.univ.filter fun b => b.1 ∈ D.encoding.base.processed j.castSucc
  let f := fun b : D.encoding.base.ProcessedRole j.succ =>
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x
        (D.encoding.base.rowLabel ((D.encoding.base.extend j h out).2 b)) then (1 : ℝ) else 0)
    else 1
  have hpast : (∏ b ∈ B, f b) =
      ∏ b : D.encoding.base.ProcessedRole j.castSucc,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
        else 1 := by
    symm
    apply Finset.prod_bij
      (fun b _ => (⟨b.1, D.processed_mono j.castSucc j.succ (by simp) b.2⟩ :
        D.encoding.base.ProcessedRole j.succ))
    · intro b _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩
    · intro b _ b' _ heq
      exact Subtype.ext (congrArg (fun z : D.encoding.base.ProcessedRole j.succ => z.1) heq)
    · intro b hb
      exact ⟨⟨b.1, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro b _
      simp only [f, LateProcessBase.extend, dif_pos b.2]
  have hcurrent : (∏ b ∈ Finset.univ \ B, f b) = classHit D j out v x := by
    symm
    unfold classHit
    apply Finset.prod_bij
      (fun b _ => (⟨b.1, D.class_before j j.succ (by simp) b.2⟩ :
        D.encoding.base.ProcessedRole j.succ))
    · intro b _
      have hn : b.1 ∉ D.encoding.base.processed j.castSucc :=
        fun hh => Finset.disjoint_left.mp (D.encoding.base.class_fresh j) b.2 hh
      simp [B, hn]
    · intro b _ b' _ heq
      exact Subtype.ext (congrArg (fun z : D.encoding.base.ProcessedRole j.succ => z.1) heq)
    · intro b hb
      have hn : b.1 ∉ D.encoding.base.processed j.castSucc := by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and]
          using (Finset.mem_sdiff.mp hb).2
      have hmem : b.1 ∈ D.encoding.base.classes j := by
        have hh : b.1 ∈ D.encoding.base.processed j.castSucc ∪ D.encoding.base.classes j :=
          Eq.mpr (congrArg (fun S : Finset (Pos T k) => b.1 ∈ S)
            (D.encoding.base.processed_step j)) b.2
        exact (Finset.mem_union.mp hh).resolve_left hn
      exact ⟨⟨b.1, hmem⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro b _
      have hn : b.1 ∉ D.encoding.base.processed j.castSucc :=
        fun hh => Finset.disjoint_left.mp (D.encoding.base.class_fresh j) b.2 hh
      simp only [f, LateProcessBase.extend, dif_neg hn]
  have hh := Finset.prod_sdiff (f := f) (Finset.subset_univ B)
  rw [hcurrent, hpast] at hh
  unfold Lane_sol_s18_n5.weightAt
  change (D.initialPrior v h.1).w x * (∏ b, f b) = _
  rw [← hh]
  ring

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

/-- Geometry makes a nontrivial class restriction a single true-hit test. -/
theorem classHit_single (D : LateData hPT) (j : Fin D.geom.r)
    (out : D.encoding.base.ClassRows j) (v : Pos T k)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (hadj : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1) (x : Fin (T.S.N k)) :
    classHit D j out v x =
      if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (out b)) then 1 else 0 := by
  obtain ⟨a, ha⟩ := adjacent_flip v b.1 hadj
  unfold classHit
  rw [Finset.prod_eq_single b]
  · simp [hadj]
  · intro b' _ hne
    have hn : ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b'.1 := by
      intro hh
      obtain ⟨a', ha'⟩ := adjacent_flip v b'.1 hh
      have hba : D.geom.classOf (flipPos v a) = some j := by
        rw [← ha]
        exact (D.encoding.base.class_of_spec b.1 j).mp b.2
      have hb'a : D.geom.classOf (flipPos v a') = some j := by
        rw [← ha']
        exact (D.encoding.base.class_of_spec b'.1 j).mp b'.2
      have heq := D.l16_valid.one_per_class v j a' a hb'a hba
      apply hne
      apply Subtype.ext
      rw [ha', heq, ← ha]
    simp [hn]
  · simp


theorem reconstruct_history (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.succ) :
    D.encoding.base.extend j (D.beforeHistory h j.castSucc (by simp))
      (D.pastRows h j (by simp)) = h := by
  apply Prod.ext
  · rfl
  · funext b
    by_cases hb : b.1 ∈ D.encoding.base.processed j.castSucc
    · simp only [LateProcessBase.extend, LateData.beforeHistory, LateData.pastRows, dif_pos hb]
    · simp only [LateProcessBase.extend, LateData.beforeHistory, LateData.pastRows, dif_neg hb]

private theorem weightAt_nonneg (D : LateData hPT) (t : Fin (D.geom.r + 1))
    (h : D.encoding.base.History t) (v : Pos T k) (x : Fin (T.S.N k)) :
    0 ≤ Lane_sol_s18_n5.weightAt D t h v x := by
  apply mul_nonneg ((D.initialPrior v h.1).nonneg x)
  apply Finset.prod_nonneg
  intro b _
  split_ifs <;> norm_num

/-- Positivity of the terminal raw restriction gives positivity at every
prefix; no fallback normalization is used in the telescoping argument. -/
theorem prefix_weight_pos (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (hp : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (t : Fin (D.geom.r + 1)) :
    0 < ∑ x, Lane_sol_s18_n5.weightAt D t
      (D.beforeHistory h t (Nat.le_of_lt_succ t.isLt)) v x := by
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x _ => Lane_sol_s18_n5.finalWeight_nonneg D h v x)).mp hp
  have hraw : Lane_sol_s18_n5.finalWeight D h v x ≠ 0 := ne_of_gt hx
  have hi := (mul_ne_zero_iff.mp hraw).1
  have hh := (mul_ne_zero_iff.mp hraw).2
  have hprefix : Lane_sol_s18_n5.weightAt D t
      (D.beforeHistory h t (Nat.le_of_lt_succ t.isLt)) v x ≠ 0 := by
    apply mul_ne_zero hi
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    have hb : b.1 ∈ D.encoding.base.processed (Fin.last D.geom.r) :=
      D.processed_mono t (Fin.last D.geom.r) (Nat.le_of_lt_succ t.isLt) b.2
    exact Finset.prod_ne_zero_iff.mp hh ⟨b.1, hb⟩ (Finset.mem_univ _)
  exact (Finset.sum_pos_iff_of_nonneg (fun x _ => weightAt_nonneg D _ _ v x)).mpr
    ⟨x, Finset.mem_univ _, lt_of_le_of_ne (weightAt_nonneg D _ _ v x) hprefix.symm⟩

noncomputable def adjacentClass (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) : Prop :=
  ∃ b ∈ D.encoding.base.classes j, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b

noncomputable def lowerHit (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) : ℝ :=
  if adjacentClass D v j then 1 / 2 - 3 * D.error v j else 1

/-- One class normalizer is controlled by its actual Requirement-3 hit
mass. The no-incidence branch changes no weights. -/
theorem raw_mass_step (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (v : Pos T k) (hv : IsEvenRole v)
    (hp : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x) (j : Fin D.geom.r) :
    lowerHit D v j * (∑ x, Lane_sol_s18_n5.weightAt D j.castSucc
      (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) v x) ≤
    ∑ x, Lane_sol_s18_n5.weightAt D j.succ
      (D.beforeHistory h j.succ (Nat.le_of_lt_succ j.succ.isLt)) v x := by
  let pre := D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)
  let suc := D.beforeHistory h j.succ (Nat.le_of_lt_succ j.succ.isLt)
  let out := D.pastRows h j j.isLt
  have hsuc : D.encoding.base.extend j pre out = suc := by
    apply Prod.ext
    · rfl
    · funext b
      by_cases hb : b.1 ∈ D.encoding.base.processed j.castSucc
      · simp only [LateProcessBase.extend, pre, suc, out, LateData.beforeHistory,
          LateData.pastRows, dif_pos hb]
      · simp only [LateProcessBase.extend, pre, suc, out, LateData.beforeHistory,
          LateData.pastRows, dif_neg hb]
  have hsplit (x : Fin (T.S.N k)) :
      Lane_sol_s18_n5.weightAt D j.succ suc v x =
        Lane_sol_s18_n5.weightAt D j.castSucc pre v x * classHit D j out v x := by
    rw [← hsuc, weightAt_extend]
  have hvalid : D.initialValid v pre.1 := hf.2.2.2.2.1 v hv
  have hmass := prefix_weight_pos D h v hp j.castSucc
  have hnorm : D.currentPrior j v pre =
      D.normalize (Lane_sol_s18_n5.weightAt D j.castSucc pre v) := by
    simp only [LateData.currentPrior, LateData.priorAt, if_pos hvalid]
    rfl
  by_cases ha : adjacentClass D v j
  · obtain ⟨b, hb, hadj⟩ := ha
    obtain ⟨a, hab⟩ := adjacent_flip b v hadj.symm
    have hR3 := (((hf.2.2.2.2.2.2 j).2.2.2.2 ⟨b, hb⟩).2.1 a)
    rw [← hab] at hR3
    change (1 / 2 : ℝ) - 3 * D.error v j ≤
      colDeg (T.S.E k) PT.tiling.c (D.currentPrior j v pre)
        (D.encoding.base.rowLabel (out ⟨b, hb⟩)) at hR3
    have hh : (1 / 2 : ℝ) - 3 * D.error v j ≤
        (∑ x, Lane_sol_s18_n5.weightAt D j.castSucc pre v x * classHit D j out v x) /
          (∑ x, Lane_sol_s18_n5.weightAt D j.castSucc pre v x) := by
      simpa only [hnorm, LateData.normalize,
        dif_pos (show (∀ x, 0 ≤ Lane_sol_s18_n5.weightAt D j.castSucc pre v x) ∧
          0 < ∑ x, Lane_sol_s18_n5.weightAt D j.castSucc pre v x from
            ⟨weightAt_nonneg D _ _ _, hmass⟩),
        colDeg, classHit_single D j out v ⟨b, hb⟩ hadj, Finset.sum_div, div_mul_eq_mul_div]
        using hR3
    change lowerHit D v j * _ ≤ _
    rw [lowerHit, if_pos ⟨b, hb, hadj⟩]
    change _ ≤ ∑ x, Lane_sol_s18_n5.weightAt D j.succ suc v x
    simp_rw [hsplit]
    exact (le_div_iff₀ hmass).mp hh
  · have hh (x : Fin (T.S.N k)) : classHit D j out v x = 1 := by
      apply Finset.prod_eq_one
      intro b _
      have hn : ¬ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 :=
        fun hbb => ha ⟨b.1, b.2, hbb⟩
      simp [hn]
    simp only [lowerHit, if_neg ha, one_mul]
    change _ ≤ ∑ x, Lane_sol_s18_n5.weightAt D j.succ suc v x
    simp_rw [hsplit, hh, mul_one]
    exact le_rfl


/-- The two common neighbors of distinct cube vertices are the only
possible shared late roles; the estimate does not use a coloring. -/
theorem common_neighbors_card {n : ℕ} (v w : CubePos n) (hne : v ≠ w) :
    (Finset.univ.filter fun b : CubePos n =>
      (OAI.HypercubeRamsey.cube n).Adj v b ∧ (OAI.HypercubeRamsey.cube n).Adj w b).card ≤ 2 := by
  classical
  let B := Finset.univ.filter fun b : CubePos n =>
    (OAI.HypercubeRamsey.cube n).Adj v b ∧ (OAI.HypercubeRamsey.cube n).Adj w b
  let S := Finset.univ.filter fun a : Fin n => v a ≠ w a
  by_cases hB : B.Nonempty
  · obtain ⟨b₀, hb₀⟩ := hB
    have hd : S.card ≤ 2 := by
      have hvb : hammingDist v b₀ = 1 := (Finset.mem_filter.mp hb₀).2.1
      have hbw : hammingDist b₀ w = 1 := (Finset.mem_filter.mp hb₀).2.2.symm
      have hh := hammingDist_triangle v b₀ w
      rw [hvb, hbw] at hh
      exact hh
    have hsubset : B ⊆ S.image (fun a => flipPos v a) := by
      intro b hb
      obtain ⟨hv, hw⟩ := (Finset.mem_filter.mp hb).2
      obtain ⟨a, ha⟩ := adjacent_flip v b hv
      obtain ⟨a', ha'⟩ := adjacent_flip w b hw
      have haa : a ≠ a' := by
        intro heq
        subst a'
        apply hne
        funext i
        have hh : flipPos v a i = flipPos w a i := by rw [← ha, ← ha']
        by_cases hi : i = a
        · subst i
          simpa [flipPos] using hh
        · simpa [flipPos, hi] using hh
      have hdiff : v a ≠ w a := by
        have hh : (!v a) = w a := by
          have hh := congrArg (fun u : CubePos n => u a) (ha.symm.trans ha')
          simpa [flipPos, haa] using hh
        cases hv : v a <;> cases hw : w a <;> simp_all
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩, ha.symm⟩
    exact (Finset.card_le_card hsubset).trans (Finset.card_image_le.trans hd)
  · change B.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    norm_num

noncomputable def lateNeighbors (D : LateData hPT) (v : Pos T k) : Finset (Pos T k) :=
  Finset.univ.filter fun b => (∃ j, D.geom.classOf b = some j) ∧
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b

noncomputable def retainedBy (D : LateData hPT) (S : Finset (Pos T k))
    (b : Pos T k) : Pos T k :=
  if h : (S.filter fun v => (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b).Nonempty then
    h.choose
  else b

noncomputable def omittedNeighbors (D : LateData hPT) (S : Finset (Pos T k))
    (v : Pos T k) := (lateNeighbors D v).filter fun b => retainedBy D S b ≠ v

theorem retainedBy_mem (D : LateData hPT) (S : Finset (Pos T k)) (b : Pos T k)
    (hb : ∃ v ∈ S, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b) :
    retainedBy D S b ∈ S ∧
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj (retainedBy D S b) b := by
  have hn : (S.filter fun v => (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b).Nonempty := by
    obtain ⟨v, hv, h⟩ := hb
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩⟩
  simp only [retainedBy, dif_pos hn]
  exact Finset.mem_filter.mp hn.choose_spec

/-- Omitted incidences can occur only at nonisolates, and each other row
accounts for at most two of them. -/
theorem omitted_neighbors_card (D : LateData hPT) (S : Finset (Pos T k))
    (v : Pos T k) (hv : v ∈ S) :
    (omittedNeighbors D S v).card ≤
      if v ∈ D.nonisolates S then 2 * S.card else 0 := by
  let B := (S.erase v).biUnion fun w => Finset.univ.filter fun b : Pos T k =>
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b ∧
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj w b
  have hsubset : omittedNeighbors D S v ⊆ B := by
    intro b hb
    obtain ⟨hlate, hne⟩ := Finset.mem_filter.mp hb
    obtain ⟨hclass, hvb⟩ := (Finset.mem_filter.mp hlate).2
    have hw := retainedBy_mem D S b ⟨v, hv, hvb⟩
    exact Finset.mem_biUnion.mpr ⟨retainedBy D S b,
      Finset.mem_erase.mpr ⟨hne, hw.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvb, hw.2⟩⟩
  have hnonempty : (omittedNeighbors D S v).Nonempty → v ∈ D.nonisolates S := by
    rintro ⟨b, hb⟩
    obtain ⟨hlate, hne⟩ := Finset.mem_filter.mp hb
    obtain ⟨hclass, hvb⟩ := (Finset.mem_filter.mp hlate).2
    have hw := retainedBy_mem D S b ⟨v, hv, hvb⟩
    exact Finset.mem_filter.mpr ⟨hv, retainedBy D S b, hw.1,
      hne.symm, Or.inr ⟨b, hclass, hvb, hw.2⟩⟩
  by_cases hi : v ∈ D.nonisolates S
  · rw [if_pos hi]
    calc
      _ ≤ B.card := Finset.card_le_card hsubset
      _ ≤ ∑ w ∈ S.erase v, (Finset.univ.filter fun b : Pos T k =>
          (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b ∧
            (OAI.HypercubeRamsey.cube (T.S.n k)).Adj w b).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ S.erase v, 2 := by
        apply Finset.sum_le_sum
        intro w hw
        exact common_neighbors_card v w (Finset.mem_erase.mp hw).1.symm
      _ ≤ 2 * S.card := by
        simp only [Finset.sum_const_nat]
        rw [mul_comm]
        exact Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.erase_subset _ _))
  · have he : omittedNeighbors D S v = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun hh => hi (hnonempty hh))
    simp [hi, he]

theorem omitted_incidence_budget (D : LateData hPT) (S : Finset (Pos T k)) :
    (∑ v ∈ S, (omittedNeighbors D S v).card) ≤ 4 * S.card * D.rank S := by
  have hb : (∑ v ∈ S, (omittedNeighbors D S v).card) ≤
      ∑ v ∈ S, if v ∈ D.nonisolates S then 2 * S.card else 0 := by
    apply Finset.sum_le_sum
    exact fun v hv => omitted_neighbors_card D S v hv
  have hsum : (∑ v ∈ S, if v ∈ D.nonisolates S then 2 * S.card else 0) =
      (D.nonisolates S).card * (2 * S.card) := by
    rw [← Finset.sum_filter]
    have he : S.filter (fun v => v ∈ D.nonisolates S) = D.nonisolates S := by
      ext v
      simp only [LateData.nonisolates, Finset.mem_filter]
      tauto
    rw [he]
    simp
  rw [hsum] at hb
  calc
    _ ≤ (D.nonisolates S).card * (2 * S.card) := hb
    _ ≤ (2 * D.rank S) * (2 * S.card) :=
      Nat.mul_le_mul_right _ (Lane_q_s18_n5.nonisolates_le_twice_rank D S)
    _ = 4 * S.card * D.rank S := by ring


private theorem prefix_prod_step {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    (∏ i, if i.val < j.val + 1 then f i else 1) =
      f j * (∏ i, if i.val < j.val then f i else 1) := by
  have heq : (fun i : Fin r => if i.val < j.val + 1 then f i else 1) =
      fun i => (if i = j then f j else 1) * (if i.val < j.val then f i else 1) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · have hn : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
      by_cases hi : i.val < j.val <;>
        simp [hij, hi, show (i.val < j.val + 1) ↔ i.val < j.val by omega]
  rw [heq, Finset.prod_mul_distrib]
  simp

theorem error_nonneg (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    0 ≤ D.error v j := by
  unfold LateData.error lateError
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (by unfold densityScale; positivity) _) (Real.exp_pos _).le)
    (Real.rpow_nonneg (by norm_num) _)

theorem lowerHit_pos (D : LateData hPT) (v : Pos T k)
    (herr : ∀ j, D.error v j ≤ 1 / 12) (j : Fin D.geom.r) : 0 < lowerHit D v j := by
  unfold lowerHit
  split_ifs
  · linarith [herr j]
  · norm_num

/-- Telescope all actual class normalizers. Its initial value is one,
not an extra freely supplied normalization estimate. -/
theorem raw_mass_lower (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (v : Pos T k) (hv : IsEvenRole v)
    (hp : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (herr : ∀ j, D.error v j ≤ 1 / 12) :
    (∏ j, lowerHit D v j) ≤ ∑ x, Lane_sol_s18_n5.finalWeight D h v x := by
  have ht : ∀ m (hm : m ≤ D.geom.r),
      (∏ j : Fin D.geom.r, if j.val < m then lowerHit D v j else 1) ≤
        ∑ x, Lane_sol_s18_n5.weightAt D ⟨m, Nat.lt_succ_of_le hm⟩
          (D.beforeHistory h ⟨m, Nat.lt_succ_of_le hm⟩ hm) v x := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp only [Nat.not_lt_zero, if_false, Finset.prod_const_one]
        change 1 ≤ ∑ x, Lane_sol_s18_n5.weightAt D 0
          (D.beforeHistory h 0 hm) v x
        have hw (x : Fin (T.S.N k)) :
            Lane_sol_s18_n5.weightAt D 0 (D.beforeHistory h 0 hm) v x =
              (D.initialPrior v h.1).w x := by
          unfold Lane_sol_s18_n5.weightAt
          have hprod : (∏ b : D.encoding.base.ProcessedRole 0,
              if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
                (if Hits (T.S.E k) PT.tiling.c x
                  (D.encoding.base.rowLabel ((D.beforeHistory h 0 hm).2 b)) then (1 : ℝ) else 0)
              else 1) = 1 := by
            apply Finset.prod_eq_one
            intro b _
            have hb := b.2
            simp only [D.encoding.base.processed_zero, Finset.notMem_empty] at hb
          rw [hprod, mul_one]
          rfl
        simp_rw [hw]
        rw [(D.initialPrior v h.1).sum_eq_one]
    | succ m ih =>
        intro hm
        let j : Fin D.geom.r := ⟨m, hm⟩
        have hstep := raw_mass_step D δ input h hf v hv hp j
        calc
          _ = lowerHit D v j *
              (∏ i : Fin D.geom.r, if i.val < m then lowerHit D v i else 1) :=
            prefix_prod_step _ j
          _ ≤ lowerHit D v j * (∑ x, Lane_sol_s18_n5.weightAt D j.castSucc
              (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) v x) :=
            mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hm)) (lowerHit_pos D v herr j).le
          _ ≤ _ := hstep
  have hh := ht D.geom.r le_rfl
  have hpre : D.beforeHistory h (Fin.last D.geom.r) le_rfl = h := by
    apply Prod.ext
    · rfl
    · funext b
      rfl
  change (∏ j : Fin D.geom.r, if j.val < D.geom.r then lowerHit D v j else 1) ≤
    ∑ x, Lane_sol_s18_n5.weightAt D (Fin.last D.geom.r)
      (D.beforeHistory h (Fin.last D.geom.r) le_rfl) v x at hh
  rw [hpre] at hh
  simpa only [Fin.is_lt, if_true, Lane_sol_s18_n5.weightAt, Lane_sol_s18_n5.finalWeight] using hh

noncomputable def incidenceCost (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) : ℝ :=
  if adjacentClass D v j then 4 * Real.exp (24 * D.error v j) else 1

/-- The product of denominator costs follows from the telescoped raw mass. -/
theorem raw_inverse_cost (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (v : Pos T k) (hv : IsEvenRole v)
    (hp : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (herr : ∀ j, D.error v j ≤ 1 / 12) :
    (∑ x, Lane_sol_s18_n5.finalWeight D h v x)⁻¹ ^ 2 ≤ ∏ j, incidenceCost D v j := by
  have hprod : 0 < ∏ j, lowerHit D v j :=
    Finset.prod_pos (fun j _ => lowerHit_pos D v herr j)
  have hinv := inv_anti₀ hprod (raw_mass_lower D δ input h hf v hv hp herr)
  calc
    _ ≤ (∏ j, lowerHit D v j)⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hinv 2
    _ = ∏ j, (lowerHit D v j)⁻¹ ^ 2 := by rw [← Finset.prod_inv_distrib, Finset.prod_pow]
    _ ≤ ∏ j, incidenceCost D v j := by
      apply Finset.prod_le_prod₀
      · intro j _
        positivity
      · intro j _
        unfold incidenceCost lowerHit
        split_ifs
        · exact squared_hit_cost (D.error v j) (1 / 2 - 3 * D.error v j)
            (error_nonneg D v j) (herr j) le_rfl
        · norm_num


theorem initialPrior_le_weight (D : LateData hPT) (v : Pos T k) (s : Config D.fresh)
    (hv : D.initialValid v s) (x : Fin (T.S.N k)) :
    (D.initialPrior v s).w x ≤ 4 * (D.chi (D.geom.patchOf v) : ℝ) * D.initialWeight v s x := by
  let f := fun y => if y ∈ D.palette v then D.initialWeight v s y else 0
  have hχ : (0 : ℝ) < D.chi (D.geom.patchOf v) := by exact_mod_cast D.chi_pos _
  have hnonneg : ∀ y, 0 ≤ f y := by
    intro y
    dsimp only [f]
    split_ifs
    · exact Lane_sol_s18_n5.initialWeight_nonneg D v s y
    · exact le_rfl
  have hlow : 1 / (4 * (D.chi (D.geom.patchOf v) : ℝ)) ≤ ∑ y, f y := by
    simpa only [f, ← Finset.sum_filter, Finset.filter_univ_mem] using hv.2.2
  have hpos : 0 < ∑ y, f y := (by positivity : 0 < 1 / (4 * (D.chi (D.geom.patchOf v) : ℝ))).trans_le hlow
  simp only [LateData.initialPrior, if_pos hv]
  change (D.normalize f).w x ≤ _
  simp only [LateData.normalize, dif_pos (And.intro hnonneg hpos)]
  by_cases hx : x ∈ D.palette v
  · simp only [f, hx, if_true]
    apply (div_le_iff₀ hpos).mpr
    have hmass : 1 ≤ (4 * (D.chi (D.geom.patchOf v) : ℝ)) * ∑ y, f y := by
      have hh := (div_le_iff₀ (show 0 < 4 * (D.chi (D.geom.patchOf v) : ℝ) by positivity)).mp hlow
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hmass (Lane_sol_s18_n5.initialWeight_nonneg D v s x)]
  · simp only [f, hx, if_false, zero_div]
    exact mul_nonneg (by positivity) (Lane_sol_s18_n5.initialWeight_nonneg D v s x)

theorem initialPrior_envelope (D : LateData hPT) (v : Pos T k) (s : Config D.fresh)
    (hv : D.initialValid v s) (x : Fin (T.S.N k))
    (hx : (D.initialPrior v s).w x ≠ 0) : x ∈ PT.envelope (D.geom.patchOf v) := by
  have hU := (Lane_sol_s18_n5.initialPrior_support D v s hv x hx).2
  have hσ : D.sigma v s x ≠ 0 := (mul_ne_zero_iff.mp hU).1
  obtain ⟨q, hq, hs⟩ := hv.1.2.2.2.1
  have hcorner : x ∈ PT.mesh.corner q (D.geom.patchOf v) := by
    by_contra hn
    exact hσ (hs x hn)
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨q, hq, hcorner⟩

theorem pairLaw_le_product (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (hZ : (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0)
    (p : Fin (T.S.N k) × Fin (T.S.N k)) :
    (D.pairLaw h v).w p ≤ 2 * ((D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2) := by
  have hgood : 0 < ∑ p ∈ Finset.univ.filter (fun p : Fin (T.S.N k) × Fin (T.S.N k) =>
      D.nonconflict v p.1 p.2), (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 := by
    rw [Finset.sum_filter]
    linarith
  have hw : (D.pairLaw h v).w p =
      (if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) /
        (∑ q ∈ Finset.univ.filter (fun q : Fin (T.S.N k) × Fin (T.S.N k) => D.nonconflict v q.1 q.2),
          (D.finalPrior h v).w q.1 * (D.finalPrior h v).w q.2) := by
    simp [LateData.pairLaw, FinLaw.bind, FinLaw.cond, hgood]
  rw [hw]
  have hprod : 0 ≤ (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 :=
    mul_nonneg ((D.finalPrior h v).nonneg _) ((D.finalPrior h v).nonneg _)
  by_cases hnc : D.nonconflict v p.1 p.2
  · rw [if_pos hnc]
    apply (div_le_iff₀ hgood).mpr
    rw [Finset.sum_filter]
    nlinarith
  · simp only [hnc, if_false, zero_div]
    positivity

noncomputable def rowLateHits (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (x z : Fin (T.S.N k)) : ℝ :=
  ∏ b : D.encoding.base.ProcessedRole (Fin.last D.geom.r),
    if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
      (if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) ∧
        Hits (T.S.E k) PT.tiling.c z (D.encoding.base.rowLabel (h.2 b)) then 1 else 0)
    else 1

theorem finalWeight_pair (D : LateData hPT)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (x z : Fin (T.S.N k)) :
    Lane_sol_s18_n5.finalWeight D h v x * Lane_sol_s18_n5.finalWeight D h v z =
      ((D.initialPrior v h.1).w x * (D.initialPrior v h.1).w z) * rowLateHits D h v x z := by
  unfold Lane_sol_s18_n5.finalWeight rowLateHits
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  split_ifs <;> norm_num <;> tauto

/-- All incidence denominators and the final pair normalizer are accounted
for in this bound; `incidenceCost` is an explicit product over actual classes. -/
theorem pairLaw_raw_bound (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (v : Pos T k) (hv : IsEvenRole v)
    (hp : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (herr : ∀ j, D.error v j ≤ 1 / 12)
    (hZ : (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0)
    (p : Fin (T.S.N k) × Fin (T.S.N k)) :
    (D.pairLaw h v).w p ≤ 32 * (D.chi (D.geom.patchOf v) : ℝ) ^ 2 *
      (D.initialWeight v h.1 p.1 * D.initialWeight v h.1 p.2) *
      (∏ j, incidenceCost D v j) * rowLateHits D h v p.1 p.2 := by
  let M := ∑ x, Lane_sol_s18_n5.finalWeight D h v x
  have hvalid : D.initialValid v h.1 := hf.2.2.2.2.1 v hv
  have hnorm : ∀ x, (D.finalPrior h v).w x = Lane_sol_s18_n5.finalWeight D h v x / M := by
    intro x
    simp only [LateData.finalPrior, LateData.priorAt, if_pos hvalid]
    change (D.normalize (Lane_sol_s18_n5.finalWeight D h v)).w x = _
    simp only [LateData.normalize, dif_pos (show (∀ x, 0 ≤ Lane_sol_s18_n5.finalWeight D h v x) ∧
      0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x from
        ⟨Lane_sol_s18_n5.finalWeight_nonneg D h v, hp⟩)]
    rfl
  have hraw : 0 ≤ Lane_sol_s18_n5.finalWeight D h v p.1 *
      Lane_sol_s18_n5.finalWeight D h v p.2 :=
    mul_nonneg (Lane_sol_s18_n5.finalWeight_nonneg D h v p.1)
      (Lane_sol_s18_n5.finalWeight_nonneg D h v p.2)
  have hhit : 0 ≤ rowLateHits D h v p.1 p.2 := by
    apply Finset.prod_nonneg
    intro b _
    split_ifs <;> norm_num
  have hprice : 0 ≤ ∏ j, incidenceCost D v j := by
    apply Finset.prod_nonneg
    intro j _
    unfold incidenceCost
    split_ifs <;> positivity
  have hinit := mul_le_mul
    (initialPrior_le_weight D v h.1 hvalid p.1)
    (initialPrior_le_weight D v h.1 hvalid p.2)
    ((D.initialPrior v h.1).nonneg p.2)
    (mul_nonneg (by positivity) (Lane_sol_s18_n5.initialWeight_nonneg D v h.1 p.1))
  calc
    _ ≤ 2 * ((D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2) :=
      pairLaw_le_product D h v hZ p
    _ = 2 * (Lane_sol_s18_n5.finalWeight D h v p.1 * Lane_sol_s18_n5.finalWeight D h v p.2) * M⁻¹ ^ 2 := by
      rw [hnorm, hnorm]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ 2 * (Lane_sol_s18_n5.finalWeight D h v p.1 * Lane_sol_s18_n5.finalWeight D h v p.2) *
        (∏ j, incidenceCost D v j) :=
      mul_le_mul_of_nonneg_left (raw_inverse_cost D δ input h hf v hv hp herr) (by positivity)
    _ = 2 * ((D.initialPrior v h.1).w p.1 * (D.initialPrior v h.1).w p.2) *
        (∏ j, incidenceCost D v j) * rowLateHits D h v p.1 p.2 := by
      rw [finalWeight_pair]
      ring
    _ ≤ 2 * ((4 * (D.chi (D.geom.patchOf v) : ℝ) * D.initialWeight v h.1 p.1) *
          (4 * (D.chi (D.geom.patchOf v) : ℝ) * D.initialWeight v h.1 p.2)) *
        (∏ j, incidenceCost D v j) * rowLateHits D h v p.1 p.2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinit (by norm_num)) hprice) hhit
    _ = _ := by ring


theorem class_neighbor_unique (D : LateData hPT) (j : Fin D.geom.r)
    (v b b' : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (hb' : b' ∈ D.encoding.base.classes j)
    (hvb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b)
    (hvb' : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b') : b = b' := by
  obtain ⟨a, ha⟩ := adjacent_flip v b hvb
  obtain ⟨a', ha'⟩ := adjacent_flip v b' hvb'
  have hba : D.geom.classOf (flipPos v a) = some j := by
    rw [← ha]
    exact (D.encoding.base.class_of_spec b j).mp hb
  have hb'a : D.geom.classOf (flipPos v a') = some j := by
    rw [← ha']
    exact (D.encoding.base.class_of_spec b' j).mp hb'
  rw [ha, ha', D.l16_valid.one_per_class v j a a' hba hb'a]

noncomputable def queryRows (D : LateData hPT) (S : Finset (Pos T k)) (j : Fin D.geom.r) :
    Finset {b : Pos T k // b ∈ D.encoding.base.classes j} :=
  Finset.univ.filter fun b => ∃ v ∈ S, (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1

theorem queryRows_card (D : LateData hPT) (S : Finset (Pos T k)) (j : Fin D.geom.r) :
    (queryRows D S j).card ≤ S.card := by
  let f := fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => retainedBy D S b.1
  have hinj : Set.InjOn f (queryRows D S j : Set _) := by
    intro b hb b' hb' heq
    have hv := retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2
    have hv' := retainedBy_mem D S b'.1 (Finset.mem_filter.mp hb').2
    apply Subtype.ext
    apply class_neighbor_unique D j (f b) b.1 b'.1 b.2 b'.2 hv.2
    simpa only [f, heq] using hv'.2
  have hsub : (queryRows D S j).image f ⊆ S := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact (retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2).1
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

noncomputable def queryCoordinate (D : LateData hPT) (S : Finset (Pos T k)) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (hb : b ∈ queryRows D S j) :
    Fin (T.S.n k) :=
  (adjacent_flip b.1 (retainedBy D S b.1)
    (retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2).2.symm).choose

theorem queryCoordinate_spec (D : LateData hPT) (S : Finset (Pos T k)) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (hb : b ∈ queryRows D S j) :
    retainedBy D S b.1 = flipPos b.1 (queryCoordinate D S j b hb) :=
  (adjacent_flip b.1 (retainedBy D S b.1)
    (retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2).2.symm).choose_spec

noncomputable def queryFactor (D : LateData hPT) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (out : D.encoding.base.RowOut b.1) : ℝ :=
  if b ∈ queryRows D S j then
    let v := retainedBy D S b.1
    if (D.initialPrior v h.1).w (assignment v).1 ≠ 0 ∧
        (D.initialPrior v h.1).w (assignment v).2 ≠ 0 ∧
        D.nonconflict v (assignment v).1 (assignment v).2 then
      if D.gate j b.1 h ∧ D.R1 j out ∧ D.R2 j h out then
        if Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.encoding.base.rowLabel out) ∧
          Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.encoding.base.rowLabel out) then 4 else 0
      else 0
    else 0
  else 1

noncomputable def queryCost (D : LateData hPT) (S : Finset (Pos T k)) (K27 : ℝ)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) : ℝ :=
  if hb : b ∈ queryRows D S j then
    Real.exp (K27 * (if queryCoordinate D S j b hb ∈ PT.tiling.Icoord (D.geom.patchOf b.1) then
      ((PT.tiling.P (D.geom.patchOf b.1)).h : ℝ) else 1) * D.error (retainedBy D S b.1) j)
  else 1

theorem queryFactor_nonneg (D : LateData hPT) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (out : D.encoding.base.RowOut b.1) :
    0 ≤ queryFactor D S assignment j h b out := by
  dsimp only [queryFactor]
  split_ifs <;> norm_num

theorem queryFactor_ref (D : LateData hPT) (hTransition : TransitionData D)
    {K27 : ℝ} (hBroad : BroadDeletionFacts D K27) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) :
    (D.encoding.kernels.refK j b h).E (queryFactor D S assignment j h b) ≤ queryCost D S K27 j b := by
  change (D.encoding.kernels.refK j b h).E (fun out => queryFactor D S assignment j h b out) ≤ _
  by_cases hb : b ∈ queryRows D S j
  · rw [queryCost, dif_pos hb]
    let v := retainedBy D S b.1
    by_cases hv : (D.initialPrior v h.1).w (assignment v).1 ≠ 0 ∧
        (D.initialPrior v h.1).w (assignment v).2 ≠ 0 ∧ D.nonconflict v (assignment v).1 (assignment v).2
    · have hq := queryCoordinate_spec D S j b hb
      have hc := reference_pair_hit D hTransition hBroad j b h (queryCoordinate D S j b hb)
        (assignment v).1 (assignment v).2
        (by simpa only [← hq] using hv.1)
        (by simpa only [← hq] using hv.2.1)
        (by simpa only [← hq] using hv.2.2)
      have hv' : (D.initialPrior (retainedBy D S b.1) h.1).w (assignment (retainedBy D S b.1)).1 ≠ 0 ∧
          (D.initialPrior (retainedBy D S b.1) h.1).w (assignment (retainedBy D S b.1)).2 ≠ 0 ∧
          D.nonconflict (retainedBy D S b.1) (assignment (retainedBy D S b.1)).1
            (assignment (retainedBy D S b.1)).2 := hv
      simp only [queryFactor, if_pos hb, if_pos hv']
      simpa only [← hq] using hc
    · simp only [queryFactor, if_pos hb, show ¬ ((D.initialPrior (retainedBy D S b.1) h.1).w
          (assignment (retainedBy D S b.1)).1 ≠ 0 ∧
          (D.initialPrior (retainedBy D S b.1) h.1).w (assignment (retainedBy D S b.1)).2 ≠ 0 ∧
          D.nonconflict (retainedBy D S b.1) (assignment (retainedBy D S b.1)).1
            (assignment (retainedBy D S b.1)).2) from hv, if_false]
      rw [Lane_sol_s18_n5.E_const]
      exact (Real.exp_pos _).le
  · simp only [queryFactor, queryCost, if_neg hb, dif_neg hb]
    exact le_of_eq (Lane_sol_s18_n5.E_const _ 1)

theorem query_class_actual (D : LateData hPT) (hTransition : TransitionData D)
    {K27 δ : ℝ} (hBroad : BroadDeletionFacts D K27) (A : ClassSamplerData D δ)
    (S : Finset (Pos T k)) (assignment : PairAssignment T k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (henter : D.enter δ j h)
    (hsmall : (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    (A.act j h).E (fun out => ∏ b ∈ queryRows D S j, queryFactor D S assignment j h b (out b)) ≤
      2 * ∏ b ∈ queryRows D S j, queryCost D S K27 j b := by
  have hcard : ((queryRows D S j).card : ℝ) ≤ S.card := by
    exact_mod_cast queryRows_card D S j
  apply selected_actual_product D A j h henter (queryRows D S j)
    (hcard.trans hsmall)
    (queryFactor D S assignment j h) (queryFactor_nonneg D S assignment j h)
    (queryCost D S K27 j)
  intro b _
  exact queryFactor_ref D hTransition hBroad S assignment j h b


theorem past_extend_before (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (i : Fin D.geom.r) (hi : i.val < j.val) :
    D.pastRows (D.encoding.base.extend j h out) i (by simp only [Fin.val_succ]; omega) =
      D.pastRows h i hi := by
  funext b
  have hb : b.1 ∈ D.encoding.base.processed j.castSucc :=
    D.class_before i j.castSucc hi b.2
  simp only [LateData.pastRows, LateProcessBase.extend, dif_pos hb]

noncomputable def queryProductAt (D : LateData hPT) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (t : Fin (D.geom.r + 1))
    (h : D.encoding.base.History t) : ℝ :=
  ∏ i : Fin D.geom.r, if hi : i.val < t.val then
    ∏ b ∈ queryRows D S i,
      queryFactor D S assignment i (D.beforeHistory h i.castSucc (Nat.le_of_lt hi)) b
        (D.pastRows h i hi b)
    else 1

theorem queryProductAt_nonneg (D : LateData hPT) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (t : Fin (D.geom.r + 1))
    (h : D.encoding.base.History t) : 0 ≤ queryProductAt D S assignment t h := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact Finset.prod_nonneg (fun b _ => queryFactor_nonneg D S assignment i _ b _)
  · norm_num

theorem queryProductAt_extend (D : LateData hPT) (S : Finset (Pos T k))
    (assignment : PairAssignment T k) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
    queryProductAt D S assignment j.succ (D.encoding.base.extend j h out) =
      queryProductAt D S assignment j.castSucc h *
        (∏ b ∈ queryRows D S j, queryFactor D S assignment j h b (out b)) := by
  let f := fun i : Fin D.geom.r => if hi : i.val < j.val then
    ∏ b ∈ queryRows D S i,
      queryFactor D S assignment i (D.beforeHistory h i.castSucc (Nat.le_of_lt hi)) b
        (D.pastRows h i hi b)
    else 1
  let cur := ∏ b ∈ queryRows D S j, queryFactor D S assignment j h b (out b)
  have hself : D.beforeHistory (D.encoding.base.extend j h out) j.castSucc (by simp) = h := by
    rw [before_extend D j h out j.castSucc (Nat.le_refl j.val)]
    apply Prod.ext
    · rfl
    · funext b
      rfl
  have heq (i : Fin D.geom.r) :
      (if hi : i.val < j.succ.val then
        ∏ b ∈ queryRows D S i, queryFactor D S assignment i
          (D.beforeHistory (D.encoding.base.extend j h out) i.castSucc (Nat.le_of_lt hi)) b
          (D.pastRows (D.encoding.base.extend j h out) i hi b)
       else 1) = (if i = j then cur else 1) * f i := by
    by_cases hij : i = j
    · subst i
      simp only [Fin.val_succ, Nat.lt_succ_self, dif_pos, hself, past_extend,
        if_pos rfl, f, Nat.lt_irrefl, dif_neg, mul_one]
      simp only [ite_true, dite_false, mul_one, cur]
    · by_cases hi : i.val < j.val
      · have his : i.val < j.succ.val := by simp only [Fin.val_succ]; omega
        simp only [dif_pos his, if_neg hij, f, dif_pos hi, one_mul]
        rw [before_extend D j h out i.castSucc (Nat.le_of_lt hi), past_extend_before D j h out i hi]
      · have his : ¬ i.val < j.succ.val := by
          have hn : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
          simp only [Fin.val_succ]
          omega
        simp only [dif_neg his, if_neg hij, f, dif_neg hi, one_mul]
  unfold queryProductAt
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm]
  rfl

/-- The late query product is integrated against the actual history law,
with the full prefix gates kept until each class comparison. -/
theorem query_run_bound (D : LateData hPT) (hTransition : TransitionData D)
    {K27 δ : ℝ} (hBroad : BroadDeletionFacts D K27) (samplers : ClassSamplerData D δ)
    (A : InitialPairData D) (assignment : PairAssignment T k) (s : Config D.fresh)
    (hsmall : (A.rows.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    (D.encoding.base.runFull samplers.act s).E (fun h =>
      if prefixGate D δ (Fin.last D.geom.r) h then
        A.phi assignment h.1 * queryProductAt D A.rows assignment (Fin.last D.geom.r) h else 0) ≤
    (∏ j, 2 * ∏ b ∈ queryRows D A.rows j, queryCost D A.rows K27 j b) * A.phi assignment s := by
  let ψ := fun t (h : D.encoding.base.History t) => A.phi assignment h.1 * queryProductAt D A.rows assignment t h
  let cost := fun j => 2 * ∏ b ∈ queryRows D A.rows j, queryCost D A.rows K27 j b
  have hc : ∀ j, 0 ≤ cost j := by
    intro j
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro b _
    unfold queryCost
    split_ifs <;> positivity
  have hs (j : Fin D.geom.r) (h : D.encoding.base.History j.castSucc) :
      (samplers.act j h).E (fun out => if prefixGate D δ j.succ (D.encoding.base.extend j h out) then
        ψ j.succ (D.encoding.base.extend j h out) else 0) ≤
      cost j * (if prefixGate D δ j.castSucc h then ψ j.castSucc h else 0) := by
    apply backward_step D samplers j h ψ
      (mul_nonneg (Lane_sol_s18_n5.phi_nonneg D A assignment h.1)
        (queryProductAt_nonneg D A.rows assignment _ h))
      (fun out => ∏ b ∈ queryRows D A.rows j, queryFactor D A.rows assignment j h b (out b))
      (fun out => Finset.prod_nonneg (fun b _ => queryFactor_nonneg D A.rows assignment j h b (out b)))
      (cost j) (hc j)
    · intro he
      exact query_class_actual D hTransition hBroad samplers A.rows assignment j h he hsmall
    · intro out _
      dsimp only [ψ]
      rw [queryProductAt_extend]
      change _ ≤ _
      exact le_of_eq (mul_assoc _ _ _).symm
  have hh := backward_run D samplers s ψ cost hc hs D.geom.r le_rfl
  have hz : queryProductAt D A.rows assignment 0 (D.encoding.base.initialHistory s) = 1 := by
    unfold queryProductAt
    apply Finset.prod_eq_one
    intro i _
    rw [dif_neg (by simp only [Fin.val_zero]; omega)]
  simp only [ψ, cost, Fin.is_lt, if_true] at hh
  rw [hz] at hh
  simpa only [LateProcessBase.runFull, Fin.last, LateProcessBase.initialHistory, mul_one] using hh

/-- The terminal certificate supplies the pool gate on its own support,
so the initial test after backward integration is exactly termTest. -/
theorem termTest_eq_phi (D : LateData hPT) {δ ε : ℝ} (C : TerminalCertificate D δ ε)
    (A : InitialPairData D) (assignment : PairAssignment T k) :
    A.termTest C assignment = (D.encoding.terminalLaw (terminalSet D δ) C.positive).E
      (fun x => A.phi assignment (D.encoding.initialState x)) := by
  unfold InitialPairData.termTest FinLaw.E
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ terminalSet D δ
  · have hp := C.pools x hx
    have hg : D.poolGate (D.expandCells A.scope) x :=
      ⟨fun C _ => hp.1 C, fun v _ => hp.2 v⟩
    simp only [hg, if_true]
  · simp only [LateEncoding.terminalLaw, FinLaw.cond, hx, if_false, zero_div, zero_mul]


/-- Positive final pair atoms retain the actual initial pair gates and
both true-hit factors at every processed adjacent role. -/
theorem pairLaw_initial_gates (D : LateData hPT) (A : InitialPairData D)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (v : Pos T k)
    (hv : D.initialValid v h.1) (hmass : 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (hZ : (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0)
    (p : Fin (T.S.N k) × Fin (T.S.N k)) (hp : 0 < (D.pairLaw h v).w p) :
    (A.validPair v p.1 p.2 ∧ (D.initialPrior v h.1).w p.1 ≠ 0 ∧ (D.initialPrior v h.1).w p.2 ≠ 0) ∧
      ∀ b : D.encoding.base.ProcessedRole (Fin.last D.geom.r),
        (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
        Hits (T.S.E k) PT.tiling.c p.1 (D.encoding.base.rowLabel (h.2 b)) ∧
        Hits (T.S.E k) PT.tiling.c p.2 (D.encoding.base.rowLabel (h.2 b)) := by
  have hgood : 0 < ∑ p ∈ Finset.univ.filter (fun p : Fin (T.S.N k) × Fin (T.S.N k) =>
      D.nonconflict v p.1 p.2), (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 := by
    rw [Finset.sum_filter]
    linarith
  have hw : 0 <
      (if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) /
        (∑ q ∈ Finset.univ.filter (fun q : Fin (T.S.N k) × Fin (T.S.N k) => D.nonconflict v q.1 q.2),
          (D.finalPrior h v).w q.1 * (D.finalPrior h v).w q.2) := by
    simpa [LateData.pairLaw, FinLaw.bind, FinLaw.cond, hgood] using hp
  have hnc : D.nonconflict v p.1 p.2 := by
    by_contra hn
    simp [hn] at hw
  have hq : (D.finalPrior h v).w p.1 ≠ 0 ∧ (D.finalPrior h v).w p.2 ≠ 0 := by
    apply mul_ne_zero_iff.mp
    intro hz
    simp [hnc, hz] at hw
  have hraw (x : Fin (T.S.N k)) (hx : (D.finalPrior h v).w x ≠ 0) :
      Lane_sol_s18_n5.finalWeight D h v x ≠ 0 := by
    intro hz
    apply hx
    simp only [LateData.finalPrior, LateData.priorAt, if_pos hv]
    change (D.normalize (Lane_sol_s18_n5.finalWeight D h v)).w x = 0
    simp only [LateData.normalize, dif_pos (And.intro
      (Lane_sol_s18_n5.finalWeight_nonneg D h v) hmass), hz, zero_div]
  have hrawx := hraw p.1 hq.1
  have hrawz := hraw p.2 hq.2
  have hx := (mul_ne_zero_iff.mp hrawx).1
  have hz := (mul_ne_zero_iff.mp hrawz).1
  have hpalx := (Lane_sol_s18_n5.initialPrior_support D v h.1 hv p.1 hx).1
  have hpalz := (Lane_sol_s18_n5.initialPrior_support D v h.1 hv p.2 hz).1
  refine ⟨⟨⟨hpalx, hpalz, initialPrior_envelope D v h.1 hv p.1 hx,
    initialPrior_envelope D v h.1 hv p.2 hz, hnc⟩, hx, hz⟩, ?_⟩
  intro b hb
  have hfx := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hrawx).2 b (Finset.mem_univ _)
  have hfz := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hrawz).2 b (Finset.mem_univ _)
  constructor
  · by_contra hn
    simp [hb, hn] at hfx
  · by_contra hn
    simp [hb, hn] at hfz

theorem full_queryProduct (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hg : ∀ v ∈ A.rows,
      (A.validPair v (assignment v).1 (assignment v).2 ∧
        (D.initialPrior v h.1).w (assignment v).1 ≠ 0 ∧ (D.initialPrior v h.1).w (assignment v).2 ≠ 0) ∧
      ∀ b : D.encoding.base.ProcessedRole (Fin.last D.geom.r),
        (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
        Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.encoding.base.rowLabel (h.2 b)) ∧
        Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.encoding.base.rowLabel (h.2 b))) :
    queryProductAt D A.rows assignment (Fin.last D.geom.r) h =
      (4 : ℝ) ^ (∑ j, (queryRows D A.rows j).card) := by
  have hfactor (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
      (hb : b ∈ queryRows D A.rows j) :
      queryFactor D A.rows assignment j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
        b (D.pastRows h j j.isLt b) = 4 := by
    let v := retainedBy D A.rows b.1
    have hv := retainedBy_mem D A.rows b.1 (Finset.mem_filter.mp hb).2
    have hx := hg v hv.1
    have hs := Lane_sol_s18_n5.full_side_requirements D δ input h hf j b
    have hgate := ((hf.2.2.2.2.2.2 j).2.2.2.2 b).1
    have hhit := hx.2 ⟨b.1, D.class_before j (Fin.last D.geom.r) j.isLt b.2⟩ hv.2
    simp only [queryFactor, if_pos hb]
    change (if (D.initialPrior v h.1).w (assignment v).1 ≠ 0 ∧
        (D.initialPrior v h.1).w (assignment v).2 ≠ 0 ∧ D.nonconflict v (assignment v).1 (assignment v).2 then
      if D.gate j b.1 (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) ∧
          D.R1 j (D.pastRows h j j.isLt b) ∧
          D.R2 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows h j j.isLt b) then
        if Hits (T.S.E k) PT.tiling.c (assignment v).1 (D.encoding.base.rowLabel (D.pastRows h j j.isLt b)) ∧
          Hits (T.S.E k) PT.tiling.c (assignment v).2 (D.encoding.base.rowLabel (D.pastRows h j j.isLt b)) then 4 else 0
      else 0 else 0) = 4
    have hhit' : Hits (T.S.E k) PT.tiling.c (assignment v).1
        (D.encoding.base.rowLabel (D.pastRows h j j.isLt b)) ∧
        Hits (T.S.E k) PT.tiling.c (assignment v).2
          (D.encoding.base.rowLabel (D.pastRows h j j.isLt b)) := hhit
    rw [if_pos ⟨hx.1.2.1, hx.1.2.2, hx.1.1.2.2.2.2⟩,
      if_pos ⟨hgate, hs.1, hs.2.1⟩, if_pos hhit']
  unfold queryProductAt
  simp only [Fin.last, Fin.is_lt, dif_pos]
  have heq : (∏ j, ∏ b ∈ queryRows D A.rows j,
      queryFactor D A.rows assignment j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
        b (D.pastRows h j j.isLt b)) = ∏ j, (4 : ℝ) ^ (queryRows D A.rows j).card := by
    apply Finset.prod_congr rfl
    intro j _
    calc
      _ = ∏ b ∈ queryRows D A.rows j, (4 : ℝ) := by
        apply Finset.prod_congr rfl
        intro b hb
        exact hfactor j b hb
      _ = _ := by simp
  rw [heq, ← Finset.prod_pow_eq_pow_sum]


/-- The one-neighbor-per-class fact identifies incidence classes with
actual adjacent late roles. -/
theorem incidence_classes_card (D : LateData hPT) (v : Pos T k) :
    (Finset.univ.filter fun j : Fin D.geom.r => adjacentClass D v j).card = (lateNeighbors D v).card := by
  classical
  apply Finset.card_bij (fun j hj => ((Finset.mem_filter.mp hj).2 : adjacentClass D v j).choose)
  · intro j hj
    have hb := ((Finset.mem_filter.mp hj).2 : adjacentClass D v j).choose_spec
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨j, (D.encoding.base.class_of_spec _ j).mp hb.1⟩, hb.2⟩
  · intro j hj j' hj' heq
    have hb := ((Finset.mem_filter.mp hj).2 : adjacentClass D v j).choose_spec
    have hb' := ((Finset.mem_filter.mp hj').2 : adjacentClass D v j').choose_spec
    have hc := (D.encoding.base.class_of_spec _ j).mp hb.1
    have hc' := (D.encoding.base.class_of_spec _ j').mp hb'.1
    rw [heq] at hc
    exact Option.some.inj (hc.symm.trans hc')
  · intro b hb
    obtain ⟨⟨j, hj⟩, hadj⟩ := (Finset.mem_filter.mp hb).2
    have hclass := (D.encoding.base.class_of_spec b j).mpr hj
    have hmem : j ∈ Finset.univ.filter (fun j : Fin D.geom.r => adjacentClass D v j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hclass, hadj⟩
    refine ⟨j, hmem, ?_⟩
    have hc := ((Finset.mem_filter.mp hmem).2 : adjacentClass D v j).choose_spec
    exact class_neighbor_unique D j v _ b hc.1 hclass hc.2 hadj

/-- Double counting separates each incidence into one position-only
retained query or one of the omitted incidences charged to overlap rank. -/
theorem incidence_count (D : LateData hPT) (S : Finset (Pos T k)) :
    (∑ v ∈ S, (lateNeighbors D v).card) =
      (∑ j, (queryRows D S j).card) + ∑ v ∈ S, (omittedNeighbors D S v).card := by
  classical
  let N := S.biUnion (lateNeighbors D)
  have hchoose (b : Pos T k) (hb : b ∈ N) :
      retainedBy D S b ∈ S ∧ (OAI.HypercubeRamsey.cube (T.S.n k)).Adj (retainedBy D S b) b := by
    obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hb
    exact retainedBy_mem D S b ⟨v, hv, (Finset.mem_filter.mp hbv).2.2⟩
  have hfiber (v : Pos T k) (hv : v ∈ S) :
      N.filter (fun b => retainedBy D S b = v) =
        (lateNeighbors D v).filter (fun b => retainedBy D S b = v) := by
    ext b
    constructor
    · intro hb
      obtain ⟨hbN, heq⟩ := Finset.mem_filter.mp hb
      obtain ⟨w, hw, hbW⟩ := Finset.mem_biUnion.mp hbN
      have hc := (Finset.mem_filter.mp hbW).2.1
      have ha := (hchoose b hbN).2
      rw [heq] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, ha⟩, heq⟩
    · intro hb
      obtain ⟨hbv, heq⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨v, hv, hbv⟩, heq⟩
  have hsum : (∑ v ∈ S, ((lateNeighbors D v).filter fun b => retainedBy D S b = v).card) = N.card := by
    have hh := Finset.card_eq_sum_card_fiberwise (f := retainedBy D S) (s := N) (t := S)
      (fun b hb => (hchoose b hb).1)
    rw [hh]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hfiber v hv]
  have hcard (j : Fin D.geom.r) : (queryRows D S j).card =
      (N.filter fun b => b ∈ D.encoding.base.classes j).card := by
    apply Finset.card_bij (fun b _ => b.1)
    · intro b hb
      obtain ⟨v, hv, ha⟩ := (Finset.mem_filter.mp hb).2
      have hbv : b.1 ∈ lateNeighbors D v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨j, (D.encoding.base.class_of_spec b.1 j).mp b.2⟩, ha⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨v, hv, hbv⟩, b.2⟩
    · intro b _ b' _ heq
      exact Subtype.ext heq
    · intro b hb
      obtain ⟨hbN, hbj⟩ := Finset.mem_filter.mp hb
      obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hbN
      exact ⟨⟨b, hbj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv,
        (Finset.mem_filter.mp hbv).2.2⟩, rfl⟩
  have hN : N = Finset.univ.biUnion (fun j : Fin D.geom.r => N.filter fun b => b ∈ D.encoding.base.classes j) := by
    ext b
    constructor
    · intro hb
      obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hbv).2.1
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨hb, (D.encoding.base.class_of_spec b j).mpr hj⟩⟩
    · intro hb
      obtain ⟨j, _, hb⟩ := Finset.mem_biUnion.mp hb
      exact (Finset.mem_filter.mp hb).1
  have hNcard : N.card = ∑ j, (queryRows D S j).card := by
    conv_lhs => rw [hN]
    rw [Finset.card_biUnion]
    · simp_rw [← hcard]
    · intro j _ j' _ hne
      apply Finset.disjoint_left.mpr
      intro b hb hb'
      exact Finset.disjoint_left.mp (D.encoding.base.class_disjoint j j' hne)
        (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2
  calc
    _ = (∑ v ∈ S, ((lateNeighbors D v).filter fun b => retainedBy D S b = v).card) +
        ∑ v ∈ S, (omittedNeighbors D S v).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      exact (Finset.card_filter_add_card_filter_not
        (s := lateNeighbors D v) (fun b => retainedBy D S b = v)).symm
    _ = _ := by rw [hsum, hNcard]


theorem error_sum_le (D : LateData hPT) (hsmall : SmallErrors κ T k PT D.geom 1)
    (v : Pos T k) : (∑ j, D.error v j) ≤ 1 := by
  have hh := hsmall (D.geom.patchOf v)
  change (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * (∑ j, D.error v j) ≤ 1 at hh
  have hheight : (1 : ℝ) ≤ (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) := by
    exact_mod_cast le_max_left 1 (PT.tiling.P (D.geom.patchOf v)).h
  have hsum : 0 ≤ ∑ j, D.error v j := Finset.sum_nonneg (fun j _ => error_nonneg D v j)
  nlinarith

theorem incidenceCost_row_bound (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom 1) (v : Pos T k) :
    (∏ j, incidenceCost D v j) ≤ Real.exp 24 * (4 : ℝ) ^ (lateNeighbors D v).card := by
  have heq (j : Fin D.geom.r) : incidenceCost D v j =
      (if adjacentClass D v j then (4 : ℝ) else 1) *
        Real.exp (24 * (if adjacentClass D v j then D.error v j else 0)) := by
    unfold incidenceCost
    split_ifs <;> simp
  have hsum : (∑ j, if adjacentClass D v j then D.error v j else 0) ≤ 1 := by
    apply le_trans _ (error_sum_le D hsmall v)
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact le_rfl
    · exact error_nonneg D v j
  simp_rw [heq]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.prod_filter]
  rw [Finset.prod_const, incidence_classes_card]
  have hh : Real.exp (24 * (∑ j, if adjacentClass D v j then D.error v j else 0)) ≤ Real.exp 24 :=
    Real.exp_le_exp.mpr (by linarith)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (4 : ℝ) ^ (lateNeighbors D v).card)

theorem incidenceCost_total_bound (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom 1) (S : Finset (Pos T k)) :
    (∏ v ∈ S, ∏ j, incidenceCost D v j) ≤
      Real.exp (24 * (S.card : ℝ)) * (4 : ℝ) ^ (∑ v ∈ S, (lateNeighbors D v).card) := by
  calc
    _ ≤ ∏ v ∈ S, (Real.exp 24 * (4 : ℝ) ^ (lateNeighbors D v).card) := by
      apply Finset.prod_le_prod₀
      · intro v _
        apply Finset.prod_nonneg
        intro j _
        unfold incidenceCost
        split_ifs <;> positivity
      · intro v _
        exact incidenceCost_row_bound D hsmall v
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
        ← Real.exp_nat_mul]
      congr 2
      ring

private theorem internal_flip_patch (D : LateData hPT) (b : Pos T k)
    (a : Fin (T.S.n k)) (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf b)) :
    D.geom.patchOf (flipPos b a) = D.geom.patchOf b := by
  have hlen : (PT.tiling.P (D.geom.patchOf b)).ℓ +
      (PT.tiling.P (D.geom.patchOf b)).h ≤ T.S.n k :=
    le_trans (Nat.add_le_add
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ) (Finset.mem_univ _))
      (Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h) (Finset.mem_univ _)))
      hPT.tiling_valid.prefix_internal_length
  have ha' : T.S.n k - (PT.tiling.P (D.geom.patchOf b)).h ≤ a.val := by
    simpa [Tiling.Icoord, topCoordinates] using ha
  exact HypercubeRamsey.Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix D.geom hPT b a (by omega)

noncomputable def rowErrorCost (D : LateData hPT) (K27 : ℝ) (v : Pos T k) (j : Fin D.geom.r) : ℝ :=
  K27 * (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * D.error v j

theorem queryCost_le (D : LateData hPT) {K27 : ℝ} (hK : 0 ≤ K27)
    (S : Finset (Pos T k)) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (hb : b ∈ queryRows D S j) :
    queryCost D S K27 j b ≤ Real.exp (rowErrorCost D K27 (retainedBy D S b.1) j) := by
  rw [queryCost, dif_pos hb]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (error_nonneg D _ j)
  apply mul_le_mul_of_nonneg_left _ hK
  by_cases ha : queryCoordinate D S j b hb ∈ PT.tiling.Icoord (D.geom.patchOf b.1)
  · rw [if_pos ha]
    have hp : D.geom.patchOf (retainedBy D S b.1) = D.geom.patchOf b.1 := by
      rw [queryCoordinate_spec D S j b hb]
      exact internal_flip_patch D b.1 _ ha
    rw [hp]
    exact_mod_cast le_max_right 1 (PT.tiling.P (D.geom.patchOf b.1)).h
  · rw [if_neg ha]
    exact_mod_cast le_max_left 1 (PT.tiling.P (D.geom.patchOf (retainedBy D S b.1))).h

theorem queryCost_class_bound (D : LateData hPT) {K27 : ℝ} (hK : 0 ≤ K27)
    (S : Finset (Pos T k)) (j : Fin D.geom.r) :
    (∏ b ∈ queryRows D S j, queryCost D S K27 j b) ≤
      Real.exp (∑ v ∈ S, rowErrorCost D K27 v j) := by
  let f := fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => retainedBy D S b.1
  have hinj : Set.InjOn f (queryRows D S j : Set _) := by
    intro b hb b' hb' heq
    have hv := retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2
    have hv' := retainedBy_mem D S b'.1 (Finset.mem_filter.mp hb').2
    apply Subtype.ext
    apply class_neighbor_unique D j (f b) b.1 b'.1 b.2 b'.2 hv.2
    simpa only [f, heq] using hv'.2
  have hsub : (queryRows D S j).image f ⊆ S := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact (retainedBy_mem D S b.1 (Finset.mem_filter.mp hb).2).1
  calc
    _ ≤ ∏ b ∈ queryRows D S j, Real.exp (rowErrorCost D K27 (f b) j) := by
      apply Finset.prod_le_prod₀
      · intro b _
        unfold queryCost
        split_ifs <;> positivity
      · intro b hb
        exact queryCost_le D hK S j b hb
    _ = Real.exp (∑ b ∈ queryRows D S j, rowErrorCost D K27 (f b) j) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have heq : (∑ v ∈ (queryRows D S j).image f, rowErrorCost D K27 v j) =
          ∑ b ∈ queryRows D S j, rowErrorCost D K27 (f b) j := Finset.sum_image hinj
      rw [← heq]
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact mul_nonneg (mul_nonneg hK (by positivity)) (error_nonneg D v j)

theorem queryCost_total_bound (D : LateData hPT) {K27 : ℝ} (hK : 0 ≤ K27)
    (hsmall : SmallErrors κ T k PT D.geom 1) (S : Finset (Pos T k)) :
    (∏ j, ∏ b ∈ queryRows D S j, queryCost D S K27 j b) ≤ Real.exp (K27 * (S.card : ℝ)) := by
  calc
    _ ≤ ∏ j, Real.exp (∑ v ∈ S, rowErrorCost D K27 v j) := by
      apply Finset.prod_le_prod₀
      · intro j _
        apply Finset.prod_nonneg
        intro b _
        unfold queryCost
        split_ifs <;> positivity
      · intro j _
        exact queryCost_class_bound D hK S j
    _ = Real.exp (∑ j, ∑ v ∈ S, rowErrorCost D K27 v j) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_comm]
      apply le_trans (Finset.sum_le_sum (fun v hv => show (∑ j, rowErrorCost D K27 v j) ≤ K27 from ?_))
        (by simp [mul_comm])
      unfold rowErrorCost
      rw [← Finset.mul_sum]
      have hh := hsmall (D.geom.patchOf v)
      change (max 1 (PT.tiling.P (D.geom.patchOf v)).h : ℝ) * (∑ j, D.error v j) ≤ 1 at hh
      simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hh hK


theorem four_pow_le_exp (m : ℕ) : (4 : ℝ) ^ m ≤ Real.exp (2 * (m : ℝ)) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ (Real.exp 2) ^ m := pow_le_pow_left₀ (by norm_num) hfour m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The pointwise late reduction accounts for every normalized row,
retains one pair query per shared odd role, and charges omitted incidences
by the actual geometric overlap rank. -/
theorem pair_product_pointwise (D : LateData hPT) (δ : ℝ) (input : D.encoding.InitInput)
    (h : D.encoding.base.History (Fin.last D.geom.r)) (hf : D.full δ input h)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hsmall : SmallErrors κ T k PT D.geom 1)
    (herr : ∀ v ∈ A.rows, ∀ j, D.error v j ≤ 1 / 12)
    (hmass : ∀ v ∈ A.rows, 0 < ∑ x, Lane_sol_s18_n5.finalWeight D h v x)
    (hZ : ∀ v ∈ A.rows, (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
      if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) :
    (∏ v ∈ A.rows, (D.pairLaw h v).w (assignment v)) ≤
      (32 : ℝ) ^ A.rows.card * Real.exp (24 * (A.rows.card : ℝ)) *
        Real.exp (8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) *
        A.phi assignment h.1 * queryProductAt D A.rows assignment (Fin.last D.geom.r) h := by
  have hnonneg : 0 ≤ A.phi assignment h.1 := Lane_sol_s18_n5.phi_nonneg D A assignment h.1
  have hqnonneg := queryProductAt_nonneg D A.rows assignment (Fin.last D.geom.r) h
  by_cases hzero : (∏ v ∈ A.rows, (D.pairLaw h v).w (assignment v)) = 0
  · rw [hzero]
    positivity
  have heven (v : Pos T k) (hv : v ∈ A.rows) : IsEvenRole v :=
    (Finset.mem_filter.mp (A.rows_subset hv)).2.1
  have hvalid (v : Pos T k) (hv : v ∈ A.rows) : D.initialValid v h.1 :=
    hf.2.2.2.2.1 v (heven v hv)
  have hpos (v : Pos T k) (hv : v ∈ A.rows) : 0 < (D.pairLaw h v).w (assignment v) := by
    have hn := Finset.prod_ne_zero_iff.mp hzero v hv
    exact lt_of_le_of_ne ((D.pairLaw h v).nonneg _) hn.symm
  have hg (v : Pos T k) (hv : v ∈ A.rows) :=
    pairLaw_initial_gates D A h v (hvalid v hv) (hmass v hv) (hZ v hv) (assignment v) (hpos v hv)
  have hphi : A.phi assignment h.1 = (D.chi A.paletteIndex.1 : ℝ) ^ (2 * A.rows.card) *
      ∏ v ∈ A.rows, (D.initialWeight v h.1 (assignment v).1 * D.initialWeight v h.1 (assignment v).2) := by
    unfold InitialPairData.phi
    rw [if_pos hvalid]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [if_pos (hg v hv).1]
  have hrow (v : Pos T k) (hv : v ∈ A.rows) :
      (D.pairLaw h v).w (assignment v) ≤
      (32 * (D.chi A.paletteIndex.1 : ℝ) ^ 2 *
        (D.initialWeight v h.1 (assignment v).1 * D.initialWeight v h.1 (assignment v).2)) *
        (∏ j, incidenceCost D v j) := by
    have hh := pairLaw_raw_bound D δ input h hf v (heven v hv) (hmass v hv) (herr v hv) (hZ v hv) (assignment v)
    have hhit : rowLateHits D h v (assignment v).1 (assignment v).2 = 1 := by
      apply Finset.prod_eq_one
      intro b _
      by_cases hb : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1
      · simp only [hb, if_true, (hg v hv).2 b hb, and_self, if_true]
      · simp only [hb, if_false]
    have hp : D.geom.patchOf v = A.paletteIndex.1 :=
      congrArg Sigma.fst (Finset.mem_filter.mp (A.rows_subset hv)).2.2
    simpa only [hhit, hp, mul_one] using hh
  have hcoef : (∏ v ∈ A.rows, 32 * (D.chi A.paletteIndex.1 : ℝ) ^ 2 *
      (D.initialWeight v h.1 (assignment v).1 * D.initialWeight v h.1 (assignment v).2)) =
      (32 : ℝ) ^ A.rows.card * A.phi assignment h.1 := by
    rw [hphi, Finset.prod_mul_distrib, Finset.prod_const, mul_pow, ← pow_mul]
    ring
  have hprice : (∏ v ∈ A.rows, ∏ j, incidenceCost D v j) ≤
      Real.exp (24 * (A.rows.card : ℝ)) * Real.exp (8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) *
        queryProductAt D A.rows assignment (Fin.last D.geom.r) h := by
    have hbudget := omitted_incidence_budget D A.rows
    have homit : (4 : ℝ) ^ (∑ v ∈ A.rows, (omittedNeighbors D A.rows v).card) ≤
        Real.exp (8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) := by
      apply (four_pow_le_exp _).trans
      apply Real.exp_le_exp.mpr
      have hh : ((∑ v ∈ A.rows, (omittedNeighbors D A.rows v).card) : ℝ) ≤
          4 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ) := by exact_mod_cast hbudget
      push_cast
      nlinarith
    calc
      _ ≤ Real.exp (24 * (A.rows.card : ℝ)) * (4 : ℝ) ^
          (∑ v ∈ A.rows, (lateNeighbors D v).card) := incidenceCost_total_bound D hsmall A.rows
      _ = Real.exp (24 * (A.rows.card : ℝ)) *
          (4 : ℝ) ^ (∑ v ∈ A.rows, (omittedNeighbors D A.rows v).card) *
          queryProductAt D A.rows assignment (Fin.last D.geom.r) h := by
        rw [incidence_count, pow_add, full_queryProduct D δ input h hf A assignment hg]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left homit (Real.exp_pos _).le) hqnonneg
  calc
    _ ≤ ∏ v ∈ A.rows, (32 * (D.chi A.paletteIndex.1 : ℝ) ^ 2 *
        (D.initialWeight v h.1 (assignment v).1 * D.initialWeight v h.1 (assignment v).2)) *
        (∏ j, incidenceCost D v j) :=
      Finset.prod_le_prod₀ (fun v _ => (D.pairLaw h v).nonneg _) hrow
    _ = ((32 : ℝ) ^ A.rows.card * A.phi assignment h.1) *
        (∏ v ∈ A.rows, ∏ j, incidenceCost D v j) := by rw [Finset.prod_mul_distrib, hcoef]
    _ ≤ ((32 : ℝ) ^ A.rows.card * A.phi assignment h.1) *
        (Real.exp (24 * (A.rows.card : ℝ)) * Real.exp (8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) *
          queryProductAt D A.rows assignment (Fin.last D.geom.r) h) :=
      mul_le_mul_of_nonneg_left hprice (by positivity)
    _ = _ := by ring


theorem stage_query_cost_bound (D : LateData hPT) {K27 : ℝ} (hK : 0 ≤ K27)
    (hsmall : SmallErrors κ T k PT D.geom 1) (S : Finset (Pos T k)) :
    (∏ j, 2 * ∏ b ∈ queryRows D S j, queryCost D S K27 j b) ≤
      Real.exp (D.geom.r : ℝ) * Real.exp (K27 * (S.card : ℝ)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have htwo : (2 : ℝ) ^ D.geom.r ≤ Real.exp (D.geom.r : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ (Real.exp 1) ^ D.geom.r := pow_le_pow_left₀ (by norm_num) he _
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  exact mul_le_mul htwo (queryCost_total_bound D hK hsmall S)
    (Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun b _ => by
      unfold queryCost
      split_ifs <;> positivity))) (Real.exp_pos _).le

/-- Uniform endpoint comparison after the initial-law integral. All late
normalizers, retained side gates, actual samplers and overlap charges occur
in the checked hypotheses of the preceding helper lemmas. -/
theorem endpoint_comparison (D : LateData hPT) (hTransition : TransitionData D)
    {K27 δ εterm εrun : ℝ} (hK : 0 ≤ K27) (hBroad : BroadDeletionFacts D K27)
    (hsmall : SmallErrors κ T k PT D.geom 1)
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (A : InitialPairData D) (assignment : PairAssignment T k)
    (hquery : (A.rows.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3))
    (herr : ∀ v ∈ A.rows, ∀ j, D.error v j ≤ 1 / 12)
    (hmass : ∀ x h, D.full δ x h → ∀ v ∈ A.rows, 0 < ∑ y, Lane_sol_s18_n5.finalWeight D h v y)
    (hZ : ∀ x h, D.full δ x h → ∀ v ∈ A.rows,
      (1 / 2 : ℝ) ≤ ∑ p : Fin (T.S.N k) × Fin (T.S.N k),
        if D.nonconflict v p.1 p.2 then (D.finalPrior h v).w p.1 * (D.finalPrior h v).w p.2 else 0) :
    endpointProbability D C H A assignment ≤
      Real.exp ((D.geom.r : ℝ) + 8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) *
        (32 * Real.exp (24 + K27)) ^ A.rows.card * A.termTest C assignment := by
  let c₀ := (32 : ℝ) ^ A.rows.card * Real.exp (24 * (A.rows.card : ℝ)) *
    Real.exp (8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ))
  let c := Real.exp ((D.geom.r : ℝ) + 8 * (A.rows.card : ℝ) * (D.rank A.rows : ℝ)) *
    (32 * Real.exp (24 + K27)) ^ A.rows.card
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hcoef : c₀ * (Real.exp (D.geom.r : ℝ) * Real.exp (K27 * (A.rows.card : ℝ))) = c := by
    dsimp only [c₀, c]
    rw [mul_pow, ← Real.exp_nat_mul]
    have heq : (A.rows.card : ℝ) * (24 + K27) =
        24 * (A.rows.card : ℝ) + K27 * (A.rows.card : ℝ) := by ring
    rw [heq]
    simp only [Real.exp_add]
    ring
  rw [Lane_sol_s18_n5.endpoint_integral]
  calc
    _ ≤ (D.encoding.terminalLaw (terminalSet D δ) C.positive).E
        (fun x => c * A.phi assignment (D.encoding.initialState x)) := by
      apply E_mono
      intro x
      calc
        _ ≤ c₀ * (D.encoding.base.runFull H.samplers.act (D.encoding.initialState x)).E (fun h =>
            if prefixGate D δ (Fin.last D.geom.r) h then
              A.phi assignment h.1 * queryProductAt D A.rows assignment (Fin.last D.geom.r) h else 0) := by
          rw [← E_mul_const]
          apply E_mono
          intro h
          by_cases hf : D.full δ x h
          · rw [if_pos hf, if_pos (full_prefixGate D δ x h hf)]
            exact (pair_product_pointwise D δ x h hf A assignment hsmall herr
              (hmass x h hf) (hZ x h hf)).trans_eq (by dsimp only [c₀]; ring)
          · rw [if_neg hf]
            apply mul_nonneg hc₀
            split_ifs
            · exact mul_nonneg (Lane_sol_s18_n5.phi_nonneg D A assignment h.1)
                (queryProductAt_nonneg D A.rows assignment _ h)
            · exact le_rfl
        _ ≤ c₀ * ((∏ j, 2 * ∏ b ∈ queryRows D A.rows j, queryCost D A.rows K27 j b) *
            A.phi assignment (D.encoding.initialState x)) :=
          mul_le_mul_of_nonneg_left (query_run_bound D hTransition hBroad H.samplers A assignment
            (D.encoding.initialState x) hquery) hc₀
        _ ≤ c₀ * ((Real.exp (D.geom.r : ℝ) * Real.exp (K27 * (A.rows.card : ℝ))) *
            A.phi assignment (D.encoding.initialState x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (stage_query_cost_bound D hK hsmall A.rows)
            (Lane_sol_s18_n5.phi_nonneg D A assignment _)) hc₀
        _ = _ := by rw [← mul_assoc, hcoef]
    _ = c * A.termTest C assignment := by rw [E_mul_const, termTest_eq_phi]


theorem eventually_query_size (T : Stage) :
    ∀ᶠ k in atTop, (T.S.n k : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 2
  filter_upwards [hlog, T.S.n_tendsto.eventually_ge_atTop 1] with k hk hn
  change 2 ≤ Real.log (T.S.n k) at hk
  have hpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hsq : 1 ≤ Real.log (T.S.n k) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ Real.log (T.S.n k) by linarith)
  calc
    (T.S.n k : ℝ) = Real.exp (Real.log (T.S.n k)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log (T.S.n k) ^ 3) := Real.exp_le_exp.mpr (by nlinarith)

end HypercubeRamsey.S18.Lane_sol_s18_5b
