import HypercubeRamsey.S18.Completion
import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.S18.Nodes_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_supp
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- The precise prior-support premise needed when restricting the sketch sum. -/
def CurrentSupportInInitial (D : LateData hPT) (j : Fin D.geom.r)
    (b : Pos T k) (h : D.encoding.base.History j.castSucc) : Prop :=
  ∀ a x, (D.currentPrior j (flipPos b a) h).w x ≠ 0 →
    (D.initialPrior (flipPos b a) h.1).w x ≠ 0

/-- Copied from lane sol-s18-1b into this lane's namespace. The formula is
an explicit premise; the mask marginal alone does not specify sketches. -/
theorem reference_current_support (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b.1)
    (hside : (D.encoding.kernels.refK j b h).w side ≠ 0) :
    ∀ a t, (D.currentPrior j (flipPos b.1 a) h).w (side.2.1 a t) ≠ 0 := by
  rw [hT.reference_formula] at hside
  have hprod := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hside).1).2
  intro a t
  exact Finset.prod_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hprod a (Finset.mem_univ a)) t (Finset.mem_univ t)

/-- Actual class support gives current sketch support for each realized row. -/
theorem actual_current_sketch_support (D : LateData hPT) (hT : TransitionData D)
    {δ : ℝ} (A : ClassSamplerData D δ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (henter : D.enter δ j h) (hout : (A.act j h).w out ≠ 0)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j}) :
    ∀ a t, (D.currentPrior j (flipPos b.1 a) h).w ((out b).2.1 a t) ≠ 0 := by
  have href := A.reference_support j h out henter hout
  change (∏ c, (D.encoding.kernels.refK j c h).w (out c)) ≠ 0 at href
  exact reference_current_support D hT j b h (out b)
    (Finset.prod_ne_zero_iff.mp href b (Finset.mem_univ b))

/-- Small errors exclude the posterior fallback on a gated row. -/
theorem gated_current_support_in_initial (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hb : b ∈ D.encoding.base.classes j) (hg : D.gate j b h) :
    CurrentSupportInInitial D j b h := by
  intro a x hx hzero
  obtain ⟨hv, hmass⟩ := Lane_sol_s18_n1_caps.gated_current_mass D hsmall j b h hg hb a
  apply hx
  rw [LateData.currentPrior, Lane_sol_s18_n1_caps.priorAt_weight D h _ hv hmass]
  simp [Lane_sol_s18_n1_caps.rawWeight, hzero]

theorem reference_initial_sketch_support (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc)
    (hprior : CurrentSupportInInitial D j b.1 h) (side : D.encoding.base.RowOut b.1)
    (hside : (D.encoding.kernels.refK j b h).w side ≠ 0) :
    InitialSketchSupport D j h side := by
  intro a t
  exact hprior a _ (reference_current_support D hT j b h side hside a t)

/-- Reference support of the whole actual class gives reference support
of each row, but initial support still needs the formula and prior premise. -/
theorem actual_initial_sketch_support (D : LateData hPT) (hT : TransitionData D)
    {δ : ℝ} (A : ClassSamplerData D δ) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j)
    (henter : D.enter δ j h) (hout : (A.act j h).w out ≠ 0)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (hprior : CurrentSupportInInitial D j b.1 h) :
    InitialSketchSupport D j h (out b) := by
  have href := A.reference_support j h out henter hout
  change (∏ c, (D.encoding.kernels.refK j c h).w (out c)) ≠ 0 at href
  exact reference_initial_sketch_support D hT j b h hprior (out b)
    (Finset.prod_ne_zero_iff.mp href b (Finset.mem_univ b))

/-- Unsupported sketches have zero coefficient before the label sum,
provided that the current prior is supported in the initial prior. -/
theorem sketch_coefficient_zero_of_unsupported (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hprior : CurrentSupportInInitial D j b h) (side : D.encoding.base.RowOut b)
    (hunsupported : ¬ InitialSketchSupport D j h side) :
    (∏ a, ∏ t, (D.currentPrior j (flipPos b a) h).w (side.2.1 a t)) = 0 := by
  by_contra hprod
  apply hunsupported
  intro a t
  exact hprior a _ (Finset.prod_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hprod a (Finset.mem_univ a)) t (Finset.mem_univ t))

/-- Exact obstruction in the existing definitions: a zero survival weight
activates fallback, even when that label has zero initial weight. This is
conditional evidence about the fallback branch, not a full LateData counterexample. -/
theorem zero_survival_fallback (D : LateData hPT) (j : Fin D.geom.r)
    (h : D.encoding.base.History j.castSucc) (v : Pos T k)
    (hv : D.initialValid v h.1)
    (hzero : ∀ x, Lane_sol_s18_n1_caps.rawWeight D h v x = 0)
    (houtside : (D.initialPrior v h.1).w D.fallback = 0) :
    (D.currentPrior j v h).w D.fallback = 1 ∧
      (D.initialPrior v h.1).w D.fallback = 0 := by
  refine ⟨?_, houtside⟩
  have hfun : Lane_sol_s18_n1_caps.rawWeight D h v = fun _ => 0 := funext hzero
  simp only [LateData.currentPrior, LateData.priorAt, if_pos hv]
  change (D.normalize (Lane_sol_s18_n1_caps.rawWeight D h v)).w D.fallback = 1
  rw [hfun]
  simp [LateData.normalize, Law.dirac]

/-- Without a mass bound, the only other posterior branch is point mass fallback. -/
theorem current_support_or_dirac (D : LateData hPT) (j : Fin D.geom.r)
    (v : Pos T k) (h : D.encoding.base.History j.castSucc) :
    (∀ x, (D.currentPrior j v h).w x ≠ 0 → (D.initialPrior v h.1).w x ≠ 0) ∨
      D.currentPrior j v h = Law.dirac D.fallback := by
  unfold LateData.currentPrior LateData.priorAt
  split_ifs with hv
  · unfold LateData.normalize
    split_ifs with hm
    · left
      intro x hx hz
      apply hx
      simp [hz]
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem sketchHit_nonneg (D : LateData hPT) {b : Pos T k}
    (side : D.encoding.base.RowOut b) (a : Fin (T.S.n k)) (y : Fin (T.S.N k)) :
    0 ≤ D.sketchHit side a y := by
  unfold LateData.sketchHit
  positivity

private theorem error_nonneg (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    0 ≤ D.error v j := by
  have hscale : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold LateData.error lateError
  exact (mul_pos (mul_pos (Real.rpow_pos_of_pos hscale _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).le

/-- An unsupported fallback sketch that passes R1 can be replaced by a
supported constant sketch: its error makes its deletion test automatic. -/
theorem supported_replacement (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b)
    (hcurrent : ∀ a t, (D.currentPrior j (flipPos b a) h).w (side.2.1 a t) ≠ 0)
    (hR1 : D.R1 j side) (hR2 : D.R2 j h side) :
    ∃ repaired : D.encoding.base.RowOut b,
      InitialSketchSupport D j h repaired ∧ D.R1 j repaired ∧ D.R2 j h repaired ∧
        ∀ tests y, D.labelWeight j repaired tests y = D.labelWeight j side tests y := by
  classical
  let supported := fun a => ∀ t, (D.initialPrior (flipPos b a) h.1).w (side.2.1 a t) ≠ 0
  have hchoose (a : Fin (T.S.n k)) : ∃ x, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 := by
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ x, (D.initialPrior (flipPos b a) h.1).w x) ≠ 0 by
        rw [(D.initialPrior (flipPos b a) h.1).sum_eq_one]; norm_num)
    exact ⟨x, hx⟩
  let sk := fun a t => if supported a then side.2.1 a t else (hchoose a).choose
  let repaired : D.encoding.base.RowOut b := (side.1, sk, side.2.2)
  have hself (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) :
      ¬ D.nonconflict (flipPos b a) x x := by
    intro hn
    exact Lane_sol_s18_n5.nonconflict_distinct D.constants D _ x x hn rfl
  have hbad (a : Fin (T.S.n k)) (ha : ¬ supported a) :
      (∀ t, side.2.1 a t = D.fallback) ∧ 0 < sketchLength T k := by
    have hn := ha
    change ¬ ∀ t, (D.initialPrior (flipPos b a) h.1).w (side.2.1 a t) ≠ 0 at hn
    obtain ⟨t, _⟩ := not_forall.mp hn
    refine ⟨?_, lt_of_le_of_lt (Nat.zero_le t.val) t.isLt⟩
    rcases current_support_or_dirac D j (flipPos b a) h with hs | hd
    · exact False.elim (ha (fun t => hs _ (hcurrent a t)))
    · intro t
      have hx := hcurrent a t
      rw [hd] at hx
      by_contra hn
      exact hx (by simp [Law.dirac, hn])
  have hconst (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (hm : 0 < sketchLength T k) :
      (∑ _t : Fin (sketchLength T k), ∑ _u : Fin (sketchLength T k),
        if ¬ D.nonconflict (flipPos b a) x x then (1 : ℝ) else 0) /
          (sketchLength T k : ℝ) ^ 2 = 1 := by
    have hm0 : (sketchLength T k : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [hself, pow_two, hm0]
  have hbound (a : Fin (T.S.n k)) (ha : ¬ supported a) :
      1 ≤ 2 * D.error (flipPos b a) j ^ 4 := by
    have hr := hR1 a
    simp only [(hbad a ha).1] at hr
    rw [hconst a D.fallback (hbad a ha).2] at hr
    exact hr
  have hhalf (a : Fin (T.S.n k)) (ha : ¬ supported a) :
      1 / 2 ≤ D.error (flipPos b a) j := by
    by_contra hn
    have he := lt_of_not_ge hn
    have hp := pow_le_pow_left₀ (error_nonneg D _ j) he.le 4
    norm_num at hp
    nlinarith [hbound a ha]
  have hpass (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
      D.passes j repaired tests y ↔ D.passes j side tests y := by
    unfold LateData.passes
    apply forall_congr'
    intro a
    apply imp_congr_right
    intro _
    by_cases ha : supported a
    · simp only [LateData.sketchHit, repaired, sk, if_pos ha]
    · have he := sub_nonpos.mpr (hhalf a ha)
      exact iff_of_true (he.trans (sketchHit_nonneg D repaired a y))
        (he.trans (sketchHit_nonneg D side a y))
  have hmask (y : Fin (T.S.N k)) : D.maskWeight repaired y = D.maskWeight side y := rfl
  have hmass (tests : Finset (Fin (T.S.n k))) :
      D.retainedMass j repaired tests = D.retainedMass j side tests := by
    unfold LateData.retainedMass
    simp_rw [hpass, hmask]
  refine ⟨repaired, ?_, ?_, ?_, ?_⟩
  · intro a t
    by_cases ha : supported a
    · simpa only [repaired, sk, if_pos ha] using ha t
    · simpa only [repaired, sk, if_neg ha] using (hchoose a).choose_spec
  · intro a
    by_cases ha : supported a
    · simpa only [repaired, sk, if_pos ha] using hR1 a
    · simpa only [repaired, sk, if_neg ha, hconst a _ (hbad a ha).2] using hbound a ha
  · simpa only [LateData.R2, LateData.prefixMoments, hmass, hpass, hmask] using hR2
  · intro tests y
    simp only [LateData.labelWeight, hmass, hpass, hmask]

/-- Replacement preserves the deletion conclusion through every label weight. -/
theorem deletion_of_current_support (D : LateData hPT) {K27 : ℝ}
    (hBroad : BroadDeletionFacts D K27) (j : Fin D.geom.r)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b.1)
    (hg : D.gate j b.1 h)
    (hcurrent : ∀ a t, (D.currentPrior j (flipPos b.1 a) h).w (side.2.1 a t) ≠ 0)
    (hR1 : D.R1 j side) (hR2 : D.R2 j h side) : D.deletionConclusion j side := by
  obtain ⟨repaired, hSupp, hR1', hR2', hlabel⟩ :=
    supported_replacement D j h side hcurrent hR1 hR2
  have hd := (hBroad j b.1 h repaired b.2 hg hSupp hR1' hR2').2.1
  simpa only [LateData.deletionConclusion, hlabel] using hd

end HypercubeRamsey.S18.Lane_sol_s18_supp
