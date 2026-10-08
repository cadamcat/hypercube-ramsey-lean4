import HypercubeRamsey.S18.Variance_sol_s18_1b
import HypercubeRamsey.S18.Orders_sol_s18_1b

namespace HypercubeRamsey.Lane_sol_s18_1b
open Classical S18
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem error_pos (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    0 < D.error v j := by
  have hc : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold LateData.error lateError
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)

theorem error_small (D : LateData hPT) (ε : ℝ) (hsmall : SmallErrors κ T k PT D.geom ε)
    (v : Pos T k) (j : Fin D.geom.r) :
    D.error v j ≤ ε ∧ ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) * D.error v j ≤ ε := by
  have hs : D.error v j ≤ ∑ s, D.error v s :=
    Finset.single_le_sum (fun s _ => (error_pos D v s).le) (Finset.mem_univ j)
  have h := hsmall (D.geom.patchOf v)
  change (max (1 : ℝ) ((PT.tiling.P (D.geom.patchOf v)).h : ℝ)) *
    (∑ s, D.error v s) ≤ ε at h
  have hmax1 : 1 ≤ max (1 : ℝ) ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) := le_max_left _ _
  have hmaxh : ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) ≤
      max (1 : ℝ) ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) := le_max_right _ _
  have hsum0 : 0 ≤ ∑ s, D.error v s := Finset.sum_nonneg fun s _ => (error_pos D v s).le
  have hsum : (∑ s, D.error v s) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right hmax1 hsum0
    simp only [one_mul] at hh
    exact hh.trans h
  constructor
  · exact hs.trans hsum
  · calc
      _ ≤ ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) * (∑ s, D.error v s) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ ≤ max (1 : ℝ) ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) * (∑ s, D.error v s) :=
        mul_le_mul_of_nonneg_right hmaxh hsum0
      _ ≤ ε := h

theorem patchOf_flip_internal (D : LateData hPT) (b : Pos T k)
    (a : Fin (T.S.n k)) (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf b)) :
    D.geom.patchOf (flipPos b a) = D.geom.patchOf b := by
  have hlength := hPT.tiling_valid.prefix_internal_length
  have hℓ := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).ℓ)
    (Finset.mem_univ (D.geom.patchOf b))
  have hh := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h)
    (Finset.mem_univ (D.geom.patchOf b))
  have ha' : T.S.n k - (PT.tiling.P (D.geom.patchOf b)).h ≤ a.val := by
    simpa [Tiling.Icoord, topCoordinates] using ha
  have hleaf : flipPos b a ∈ PT.tiling.leaf (D.geom.patchOf b) := by
    intro t ht
    have hne : t ≠ a := by intro h; subst t; omega
    simpa [flipPos, hne] using D.geom.patchOf_leaf b t ht
  obtain ⟨i, _, huniq⟩ := hPT.tiling_valid.prefix_complete (flipPos b a)
  exact (huniq _ (D.geom.patchOf_leaf _)).trans (huniq _ hleaf).symm

theorem internal_card_le (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (PT.tiling.Icoord i).card ≤ (PT.tiling.P i).h := by
  let h := (PT.tiling.P i).h
  have hh := Finset.le_sup (f := fun i : Fin PT.tiling.m => (PT.tiling.P i).h)
    (Finset.mem_univ i)
  have hhn : h ≤ T.S.n k := by have := hPT.tiling_valid.prefix_internal_length; omega
  let ix : {a : Fin (T.S.n k) // a ∈ PT.tiling.Icoord i} → Fin h := fun a =>
    ⟨a.1.val - (T.S.n k - h), by
      have hm : T.S.n k - h ≤ a.1.val := by
        simpa [Tiling.Icoord, topCoordinates, h] using a.2
      omega⟩
  have hinj : Function.Injective ix := by
    intro a b heq
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val heq
    have ha : T.S.n k - h ≤ a.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using a.2
    have hb : T.S.n k - h ≤ b.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using b.2
    exact (tsub_left_inj ha hb).mp hv
  simpa using Fintype.card_le_of_injective ix hinj

theorem batch_error_small (D : LateData hPT) (b : Pos T k) (j : Fin D.geom.r)
    (ε : ℝ) (hsmall : SmallErrors κ T k PT D.geom ε)
    (B : Finset (Fin (T.S.n k)))
    (hB : B = PT.tiling.Icoord (D.geom.patchOf b) ∨ ∃ a, B = {a}) :
    (∑ a ∈ B, D.error (flipPos b a) j) ≤ ε := by
  rcases hB with rfl | ⟨a, rfl⟩
  · have heq (a : Fin (T.S.n k)) (ha : a ∈ PT.tiling.Icoord (D.geom.patchOf b)) :
        D.error (flipPos b a) j = D.error b j := by
      unfold LateData.error
      rw [patchOf_flip_internal D b a ha]
    calc
      _ = (PT.tiling.Icoord (D.geom.patchOf b)).card * D.error b j := by
        rw [Finset.sum_congr rfl (fun a ha => heq a ha)]; simp
      _ ≤ ((PT.tiling.P (D.geom.patchOf b)).h : ℝ) * D.error b j :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast internal_card_le (hPT := hPT) _)
          (error_pos D b j).le
      _ ≤ ε := (error_small D ε hsmall b j).2
  · simpa using (error_small D ε hsmall (flipPos b a) j).1

theorem exp_neg_le_retention (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 100) :
    Real.exp (-1000 * s) ≤ 1 - s := by
  have hlinear : 1 + 1000 * s ≤ Real.exp (1000 * s) := by
    simpa [add_comm] using Real.add_one_le_exp (1000 * s)
  have hfactor : 0 ≤ 1 - s := by linarith
  have hmult : 1 ≤ (1 - s) * Real.exp (1000 * s) := by
    have h := mul_le_mul_of_nonneg_left hlinear hfactor
    have hp := mul_nonneg hs0 (show 0 ≤ 999 - 1000 * s by linarith)
    nlinarith
  have hid : Real.exp (1000 * s) * Real.exp (-1000 * s) = 1 := by
    rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_right hmult (Real.exp_pos (-1000 * s)).le
  nlinarith

theorem mask_nonempty (D : LateData hPT) {b : Pos T k} (side : D.encoding.base.RowOut b) :
    side.1.1.Nonempty := by
  have hp : 0 < (D.encoding.base.latePoolOf b).card :=
    Finset.card_pos.mpr ⟨side.2.2.1, side.2.2.2⟩
  have hm := side.1.2.2
  exact Finset.card_pos.mp (by omega)

theorem retained_empty (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) :
    D.retainedMass j side ∅ = 1 := by
  have h := (FinProb.uniform side.1.1 (mask_nonempty D side)).sum_eq_one
  simpa [LateData.retainedMass, LateData.passes, LateData.maskWeight,
    FinProb.uniform, one_div] using h

theorem batch_step_cost (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests B : Finset (Fin (T.S.n k))) (hmass : 0 < D.retainedMass j side tests)
    (htail : ∀ a ∈ B, (prefixLaw D j side tests hmass).pr
      (fun y => D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j) ≤
        22 * D.error (flipPos b a) j ^ 2)
    (he : ∀ a ∈ B, D.error (flipPos b a) j ≤ 1 / 100)
    (hs : (∑ a ∈ B, D.error (flipPos b a) j) ≤ 1 / 100) :
    Real.exp (-1000 * ∑ a ∈ B, D.error (flipPos b a) j) * D.retainedMass j side tests ≤
      D.retainedMass j side (tests ∪ B) := by
  have hret := prefix_batch_retention D j side tests B hmass htail
  have hloss : (∑ a ∈ B, 22 * D.error (flipPos b a) j ^ 2) ≤
      ∑ a ∈ B, D.error (flipPos b a) j := by
    apply Finset.sum_le_sum
    intro a ha
    have hh := he a ha
    have he0 := error_pos D (flipPos b a) j
    have hsquare := mul_le_mul_of_nonneg_left hh he0.le
    nlinarith
  have hf : Real.exp (-1000 * ∑ a ∈ B, D.error (flipPos b a) j) ≤
      1 - ∑ a ∈ B, 22 * D.error (flipPos b a) j ^ 2 := by
    calc
      _ ≤ 1 - ∑ a ∈ B, D.error (flipPos b a) j :=
        exp_neg_le_retention _ (Finset.sum_nonneg fun a _ => (error_pos D _ j).le) hs
      _ ≤ _ := by linarith
  exact le_trans (mul_le_mul_of_nonneg_right hf hmass.le) hret

theorem batch_step (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b) (hsupport : S18.InitialSketchSupport D j h side)
    (hR1 : D.R1 j side) (hR2 : D.R2 j h side)
    (hm : 0 < sketchLength T k)
    (hB : ∀ a, bstar T k ≤ D.error (flipPos b a) j ^ 4)
    (ε : ℝ) (hε : ε ≤ 1 / 100) (hsmall : SmallErrors κ T k PT D.geom ε)
    (order : List (Finset (Fin (T.S.n k)))) (horder : order ∈ D.testOrders b)
    (q : ℕ) (hq : q < order.length)
    (hcut : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side (D.prefixTests order q)) :
    Real.exp (-1000 * ε) * D.retainedMass j side (D.prefixTests order q) ≤
      D.retainedMass j side (D.prefixTests order (q + 1)) := by
  let B := order.getD q ∅
  let s : ℝ := ∑ a ∈ B, D.error (flipPos b a) j
  have hshape := order_batch D b order horder B
    (getD_mem order q ∅ hq)
  have hs : s ≤ ε := batch_error_small D b j ε hsmall B hshape
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun a _ => (error_pos D _ j).le
  have hmass := (Real.exp_pos _).trans_le hcut
  have hret := prefix_batch_retention D j side (D.prefixTests order q) B hmass
    (fun a ha => prefix_sketch_failure D j h side hsupport order q a hcut
      (hR2 order horder q hq a ha) hR1 hm (error_pos D _ j) (hB a))
  have hloss : (∑ a ∈ B, 22 * D.error (flipPos b a) j ^ 2) ≤ s := by
    apply Finset.sum_le_sum
    intro a ha
    have he := (error_small D ε hsmall (flipPos b a) j).1
    have he0 := error_pos D (flipPos b a) j
    have hsquare := mul_le_mul_of_nonneg_left (he.trans hε) he0.le
    nlinarith
  have hf : Real.exp (-1000 * ε) ≤ 1 - ∑ a ∈ B, 22 * D.error (flipPos b a) j ^ 2 := by
    calc
      Real.exp (-1000 * ε) ≤ Real.exp (-1000 * s) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 - s := exp_neg_le_retention s hs0 (hs.trans hε)
      _ ≤ _ := by linarith
  rw [prefix_step D order q hq]
  exact le_trans (mul_le_mul_of_nonneg_right hf hmass.le) hret

theorem broad_prefixes (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b) (hsupport : S18.InitialSketchSupport D j h side)
    (hR1 : D.R1 j side) (hR2 : D.R2 j h side)
    (hm : 0 < sketchLength T k) (hn : 1 ≤ T.S.n k)
    (hB : ∀ a, bstar T k ≤ D.error (flipPos b a) j ^ 4)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 100)
    (hεα : ε ≤ κ.α / 300000) (hsmall : SmallErrors κ T k PT D.geom ε) :
    ∀ order ∈ D.testOrders b, ∀ q, q ≤ order.length →
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
        D.retainedMass j side (D.prefixTests order q) := by
  intro order horder
  have hlen := order_length D b order horder
  have hscalar (q : ℕ) (hq : q ≤ order.length) :
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ Real.exp (-1000 * ε * q) := by
    have hq3 : (q : ℝ) ≤ 3 * (T.S.n k : ℝ) := by exact_mod_cast (show q ≤ 3 * T.S.n k by omega)
    have hn0 : 0 ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
    have hqε := mul_le_mul_of_nonneg_left hq3 hε0.le
    have hαn := mul_le_mul_of_nonneg_right hεα hn0
    apply Real.exp_le_exp.mpr
    nlinarith
  have hind : ∀ q, q ≤ order.length →
      Real.exp (-1000 * ε * q) ≤ D.retainedMass j side (D.prefixTests order q) := by
    intro q
    induction q with
    | zero => intro _; simp [LateData.prefixTests, retained_empty]
    | succ q ih =>
      intro hq
      have hp : q ≤ order.length := by omega
      have hi := ih hp
      have hb := (hscalar q hp).trans hi
      have hstep := batch_step D j h side hsupport hR1 hR2 hm hB ε hε hsmall
        order horder q (by omega) hb
      have hmul := mul_le_mul_of_nonneg_left hi (Real.exp_pos (-1000 * ε)).le
      have hid : Real.exp (-1000 * ε * (q + 1 : ℕ)) =
          Real.exp (-1000 * ε) * Real.exp (-1000 * ε * q) := by
        rw [← Real.exp_add]
        congr 1
        push_cast; ring
      rw [hid]
      exact hmul.trans hstep
  intro q hq
  exact (hscalar q hq).trans (hind q hq)

end HypercubeRamsey.Lane_sol_s18_1b
