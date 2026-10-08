import HypercubeRamsey.S18.Retention_sol_s18_1b

namespace HypercubeRamsey.Lane_sol_s18_1b
open Classical S18
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem pointwise_compare (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (omitted : Finset (Fin (T.S.n k)))
    (c : ℝ)
    (hfull : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side Finset.univ)
    (hleave : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side (Finset.univ \ omitted))
    (hcompare : Real.exp (-c) * D.retainedMass j side (Finset.univ \ omitted) ≤
      D.retainedMass j side Finset.univ) :
    ∀ y, D.labelWeight j side Finset.univ y ≤
      Real.exp c * D.labelWeight j side (Finset.univ \ omitted) y := by
  have hfullPos := (Real.exp_pos _).trans_le hfull
  have hleavePos := (Real.exp_pos _).trans_le hleave
  have hden : D.retainedMass j side (Finset.univ \ omitted) ≤
      Real.exp c * D.retainedMass j side Finset.univ := by
    have hh := mul_le_mul_of_nonneg_left hcompare (Real.exp_pos c).le
    have heq : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    simpa [← mul_assoc, heq] using hh
  intro y
  have hw : 0 ≤ D.maskWeight side y := by
    unfold LateData.maskWeight; split_ifs <;> positivity
  by_cases hp : D.passes j side Finset.univ y
  · have hl : D.passes j side (Finset.univ \ omitted) y :=
      fun a _ => hp a (Finset.mem_univ a)
    simp only [LateData.labelWeight, if_pos hfull, if_pos hleave, if_pos hp, if_pos hl]
    apply (div_le_iff₀ hfullPos).2
    have hh := mul_le_mul_of_nonneg_left hden
      (div_nonneg hw hleavePos.le)
    have hid : (D.maskWeight side y / D.retainedMass j side (Finset.univ \ omitted)) *
        D.retainedMass j side (Finset.univ \ omitted) = D.maskWeight side y :=
      div_mul_cancel₀ _ hleavePos.ne'
    rw [hid] at hh
    nlinarith
  · simp only [LateData.labelWeight, if_pos hfull, if_neg hp, if_pos hleave]
    split_ifs <;> positivity

theorem deletion_compare (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b) (hsupport : S18.InitialSketchSupport D j h side)
    (hR1 : D.R1 j side) (hR2 : D.R2 j h side)
    (hm : 0 < sketchLength T k)
    (hB : ∀ a, bstar T k ≤ D.error (flipPos b a) j ^ 4)
    (ε : ℝ) (hε : ε ≤ 1 / 100) (hsmall : SmallErrors κ T k PT D.geom ε)
    (hbroad : ∀ order ∈ D.testOrders b, ∀ q, q ≤ order.length →
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side (D.prefixTests order q)) :
    D.deletionConclusion j side := by
  intro a
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let B := if a ∈ intern then intern else {a}
  let l := if a ∈ intern then (PT.tiling.P (D.geom.patchOf b)).h else 1
  obtain ⟨pre, horder, hpre, hfull⟩ := deletion_order D b a
  change pre ++ [B] ∈ D.testOrders b at horder
  change D.prefixTests (pre ++ [B]) pre.length = Finset.univ \ B at hpre
  change D.prefixTests (pre ++ [B]) (pre.length + 1) = Finset.univ at hfull
  have hcut := hbroad (pre ++ [B]) horder pre.length (by simp)
  have hcutfull := hbroad (pre ++ [B]) horder (pre.length + 1) (by simp)
  have hmass := (Real.exp_pos _).trans_le hcut
  have hshape : B = intern ∨ ∃ a, B = {a} := by unfold B; split_ifs <;> aesop
  have hcost := batch_error_small D b j ε hsmall B hshape
  have htail (a' : Fin (T.S.n k)) (ha' : a' ∈ B) :=
    prefix_sketch_failure D j h side hsupport (pre ++ [B]) pre.length a' hcut
      (hR2 _ horder _ (by simp) a' (by simpa only [getD_append_last] using ha')) hR1 hm
      (error_pos D _ j) (hB a')
  have hstep := batch_step_cost D j side (D.prefixTests (pre ++ [B]) pre.length)
    B hmass htail (fun a' _ => (error_small D ε hsmall _ j).1.trans hε) (hcost.trans hε)
  have hstepTests : D.prefixTests (pre ++ [B]) pre.length ∪ B = Finset.univ := by
    calc
      _ = D.prefixTests (pre ++ [B]) (pre.length + 1) := by
        simpa only [getD_append_last] using (prefix_step D (pre ++ [B]) pre.length (by simp)).symm
      _ = Finset.univ := hfull
  rw [hstepTests, hpre] at hstep
  have hcostl : (∑ a' ∈ B, D.error (flipPos b a') j) ≤
      (l : ℝ) * D.error (flipPos b a) j := by
    by_cases ha : a ∈ intern
    · have heq (a' : Fin (T.S.n k)) (ha' : a' ∈ intern) :
          D.error (flipPos b a') j = D.error (flipPos b a) j := by
        unfold LateData.error
        rw [patchOf_flip_internal D b a' ha', patchOf_flip_internal D b a ha]
      simp only [B, l, if_pos ha]
      calc
        _ = intern.card * D.error (flipPos b a) j := by
          rw [Finset.sum_congr rfl (fun a' ha' => heq a' ha')]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast internal_card_le (hPT := hPT) (D.geom.patchOf b))
          (error_pos D _ j).le
    · simp [B, l, ha]
  have hratio : Real.exp (-(1000 * (l : ℝ) * D.error (flipPos b a) j)) *
      D.retainedMass j side (Finset.univ \ B) ≤ D.retainedMass j side Finset.univ := by
    apply le_trans _ hstep
    apply mul_le_mul_of_nonneg_right _ ((Real.exp_pos _).trans_le (hpre ▸ hcut)).le
    apply Real.exp_le_exp.mpr
    nlinarith
  exact pointwise_compare D j side B (1000 * (l : ℝ) * D.error (flipPos b a) j)
    (hfull ▸ hcutfull) (hpre ▸ hcut) hratio

theorem label_event_prefix (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k)))
    (hcut : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side tests)
    (A : Fin (T.S.N k) → Prop) :
    (∑ y, if A y then D.labelWeight j side tests y else 0) =
      (prefixLaw D j side tests ((Real.exp_pos _).trans_le hcut)).pr A := by
  rw [prefixLaw_pr, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  simp only [LateData.labelWeight, if_pos hcut]
  by_cases hp : D.passes j side tests y <;> by_cases hA : A y <;>
    simp [hp, hA]

theorem integrate_comparison (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b) (tests : Finset (Fin (T.S.n k)))
    (c : ℝ) (hcompare : ∀ y, D.labelWeight j side Finset.univ y ≤
      Real.exp c * D.labelWeight j side tests y)
    (A : Fin (T.S.N k) → Prop) (u : ℝ)
    (hmoment : (∑ y, if A y then D.labelWeight j side tests y else 0) ≤ u) :
    (∑ y, if A y then D.labelWeight j side Finset.univ y else 0) ≤ Real.exp c * u := by
  calc
    _ ≤ ∑ y, Real.exp c * (if A y then D.labelWeight j side tests y else 0) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hA : A y
      · simpa only [if_pos hA] using hcompare y
      · simp only [if_neg hA, mul_zero, le_refl]
    _ = Real.exp c * (∑ y, if A y then D.labelWeight j side tests y else 0) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (Real.exp_pos c).le

theorem moment_exp (e B l u : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 100)
    (hB : B ≤ e ^ 4) (hl : 1 ≤ l) (hu : 1 / 4 ≤ u) :
    u + 10 * B ≤ u * Real.exp (100 * l * e) := by
  have he2 : e ^ 2 ≤ e := by
    have h := mul_le_mul_of_nonneg_left he1 he.le
    nlinarith
  have he4 : e ^ 4 ≤ e ^ 2 := by
    have h := mul_nonneg (sq_nonneg e) (show 0 ≤ 1 - e ^ 2 by nlinarith)
    nlinarith
  have hlin : 1 + 100 * l * e ≤ Real.exp (100 * l * e) := by
    simpa [add_comm] using Real.add_one_le_exp (100 * l * e)
  have hmul := mul_le_mul_of_nonneg_left hlin (show 0 ≤ u by linarith)
  have hl0 : 0 ≤ l := by linarith
  have hle : e ≤ l * e := by simpa using mul_le_mul_of_nonneg_right hl he.le
  have hue : 25 * (l * e) ≤ u * (100 * l * e) := by
    have h := mul_le_mul_of_nonneg_right hu (show 0 ≤ 100 * l * e by positivity)
    nlinarith
  nlinarith

theorem hit_bounds (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b) (hR2 : D.R2 j h side)
    (hdel : D.deletionConclusion j side)
    (hB : ∀ a, bstar T k ≤ D.error (flipPos b a) j ^ 4)
    (he : ∀ a, D.error (flipPos b a) j ≤ 1 / 100)
    (hbroad : ∀ order ∈ D.testOrders b, ∀ q, q ≤ order.length →
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side (D.prefixTests order q)) :
    (∀ a x, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y then D.labelWeight j side Finset.univ y else 0) ≤
        (1 / 2) * Real.exp (1100 * l * D.error (flipPos b a) j)) ∧
    (∀ a x z, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      (D.initialPrior (flipPos b a) h.1).w z ≠ 0 → D.nonconflict (flipPos b a) x z →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
        then D.labelWeight j side Finset.univ y else 0) ≤
          (1 / 4) * Real.exp (1100 * l * D.error (flipPos b a) j)) := by
  have hlocal (a : Fin (T.S.n k)) :
      let intern := PT.tiling.Icoord (D.geom.patchOf b)
      let B := if a ∈ intern then intern else {a}
      let l := if a ∈ intern then (PT.tiling.P (D.geom.patchOf b)).h else 1
      ∃ pre : List (Finset (Fin (T.S.n k))),
        pre ++ [B] ∈ D.testOrders b ∧
        D.prefixTests (pre ++ [B]) pre.length = Finset.univ \ B ∧
        a ∈ B ∧ (1 : ℝ) ≤ l := by
    obtain ⟨pre, ho, hp, _⟩ := deletion_order D b a
    refine ⟨pre, ho, hp, ?_, ?_⟩
    · split_ifs with ha <;> simp [ha]
    · split_ifs with ha
      · have hh : 0 < (PT.tiling.Icoord (D.geom.patchOf b)).card := Finset.card_pos.mpr ⟨a, ha⟩
        have hcard := internal_card_le (hPT := hPT) (D.geom.patchOf b)
        exact_mod_cast (show 1 ≤ (PT.tiling.P (D.geom.patchOf b)).h by omega)
      · norm_num
  have hfinish (a : Fin (T.S.n k)) (A : Fin (T.S.N k) → Prop) (u : ℝ)
      (hu : 1 / 4 ≤ u)
      (hM : ∀ order, ∀ (ho : order ∈ D.testOrders b), ∀ q, ∀ (hq : q < order.length),
        a ∈ order.getD q ∅ →
        (prefixLaw D j side (D.prefixTests order q)
          ((Real.exp_pos _).trans_le (hbroad order ho q (Nat.le_of_lt hq)))).pr A ≤ u + 10 * bstar T k) :
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if A y then D.labelWeight j side Finset.univ y else 0) ≤
        u * Real.exp (1100 * l * D.error (flipPos b a) j) := by
    let intern := PT.tiling.Icoord (D.geom.patchOf b)
    let B := if a ∈ intern then intern else {a}
    let l := if a ∈ intern then (PT.tiling.P (D.geom.patchOf b)).h else 1
    obtain ⟨pre, ho, hp, ha, hl⟩ := hlocal a
    have hc := hbroad (pre ++ [B]) ho pre.length (by simp)
    have hmoment := hM (pre ++ [B]) ho pre.length (by simp) (by simpa only [getD_append_last] using ha)
    rw [← label_event_prefix D j side _ hc A] at hmoment
    rw [hp] at hmoment
    have hsum := integrate_comparison D j side (Finset.univ \ B)
      (1000 * (l : ℝ) * D.error (flipPos b a) j) (hdel a)
      A (u + 10 * bstar T k) hmoment
    have hmexp := moment_exp (D.error (flipPos b a) j) (bstar T k) l u
      (error_pos D _ j) (he a) (hB a) hl hu
    calc
      _ ≤ Real.exp (1000 * (l : ℝ) * D.error (flipPos b a) j) * (u + 10 * bstar T k) := hsum
      _ ≤ Real.exp (1000 * (l : ℝ) * D.error (flipPos b a) j) *
          (u * Real.exp (100 * l * D.error (flipPos b a) j)) :=
        mul_le_mul_of_nonneg_left hmexp (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  constructor
  · intro a x hx
    apply hfinish a (fun y => Hits (T.S.E k) PT.tiling.c x y) (1 / 2) (by norm_num)
    intro order ho q hq ha
    have hc := hbroad order ho q (Nat.le_of_lt hq)
    have hh := ((hR2 order ho q hq a ha) hc).1 x hx
    rw [prefixLaw_pr]
    have hh' := (abs_le.mp hh).2
    linarith
  · intro a x z hx hz hnc
    have hf := hfinish a
      (fun y => Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y)
      (1 / 4) (by norm_num) (by
        intro order ho q hq ha
        have hc := hbroad order ho q (Nat.le_of_lt hq)
        have hh := ((hR2 order ho q hq a ha) hc).2 x z hx hz hnc
        rw [prefixLaw_pr]
        have hh' := (abs_le.mp hh).2
        have hbound :
            (∑ y, if D.passes j side (D.prefixTests order q) y ∧
              Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
              then D.maskWeight side y else 0) /
              D.retainedMass j side (D.prefixTests order q) ≤ 1 / 4 + 10 * bstar T k := by
          linarith
        convert hbound using 1
        congr 8
        funext y
        by_cases hp : D.passes j side (D.prefixTests order q) y <;>
          by_cases ht : Hits (T.S.E k) PT.tiling.c x y <;>
          by_cases hu : Hits (T.S.E k) PT.tiling.c z y <;> simp [hp, ht, hu])
    dsimp only at hf ⊢
    convert hf using 1
    congr 8
    funext y
    by_cases ht : Hits (T.S.E k) PT.tiling.c x y <;>
      by_cases hu : Hits (T.S.E k) PT.tiling.c z y <;> simp [ht, hu]

theorem broadDeletion_of_small (D : LateData hPT)
    (hn : 1 ≤ T.S.n k) (hm : 0 < sketchLength T k)
    (hB : ∀ v j, bstar T k ≤ D.error v j ^ 4)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 100) (hεα : ε ≤ κ.α / 300000)
    (hsmall : SmallErrors κ T k PT D.geom ε) : BroadDeletionFacts D 1100 := by
  intro j b h side _ _ hs h1 h2
  have hb := broad_prefixes D j h side hs h1 h2 hm hn (fun a => hB _ j)
    ε hε0 hε hεα hsmall
  have hd := deletion_compare D j h side hs h1 h2 hm (fun a => hB _ j) ε hε hsmall hb
  have hh := hit_bounds D j h side h2 hd (fun a => hB _ j)
    (fun a => (error_small D ε hsmall _ j).1.trans hε) hb
  exact ⟨hb, hd, hh⟩

end HypercubeRamsey.Lane_sol_s18_1b
