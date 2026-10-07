import HypercubeRamsey.S08.L81.PosteriorNodes_q_s08_post

/-!
# Lemma 8.1, Steps 6–8: selection adjustment, posterior truncation, the ordinary-anchor hit test

Source: `sections/08-…tex`, lines 227–300 (L8.1g, L8.1h).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

set_option maxHeartbeats 1000000
/-- L8.1g(i) (08:230–234): in the raw experiment at candidate `ξ`, the listed centres (distinct IDs: internal ones in
slice `g`, one per cross slice) first need the observed independent tags (laws `S_g`, `S_u`); selection and
validity only reduce the probability; given the selections the cross anchors are independent with laws
`U_{u,i}`; validity includes the candidate's gates.  Dividing by `Q` gives `F_ξ a_ξ ≤ F_ξ` (both sides vanish
where a reference vanishes). -/
theorem gsel_le_f (D : Ctx η₀ β p h) : D.GselLeF := by
  classical
  intro Θ P c ξ π
  let Θc : D.Hist := Function.update Θ c.1 ξ
  let qOf : D.TAT → D.Pre := fun z => ((Θc, P), z)
  let Ev : D.TAT → D.Anch → Prop := fun z W =>
    D.PresValid (qOf z) W c ∧ D.presOf (qOf z) W c = π
  have hTagNe : Nonempty D.M.ι := by
    by_contra hne
    haveI : IsEmpty D.M.ι := ⟨fun i => hne ⟨i⟩⟩
    have hsum : (∑ i, D.M.Λ i) = 0 := by simp
    rw [D.M.Λ_sum] at hsum
    norm_num at hsum
  letI : Nonempty D.M.ι := hTagNe
  let dflt : D.M.ι := Classical.choice hTagNe
  let BTag' : D.Tags → Prop := fun t =>
    ∀ x ∈ Lane_q_s08_post.observedTagCoords D c π,
      t x.1 x.2 = Lane_q_s08_post.observedTagValue D c π dflt x
  by_cases hgate : ¬ D.CandGate Θc c.1
  · have hnum0 : (D.rawLaw Θc P).pr (fun z => Ev z.1 z.2) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro z hz
      by_cases he : Ev z.1 z.2
      · exfalso
        exact hgate he.1.1
      · simp [he]
    unfold Ctx.Gsel Ctx.Fcand
    simp [Θc, qOf, Ev, hnum0, hgate]
  · have hFcandNonneg := D.Fcand_nonneg Θ c.1 ξ (D.obsOf π)
    by_cases hQ0 : D.Qref Θ c.1 (D.obsOf π) = 0
    · simp [Ctx.Gsel, hQ0]
      exact hFcandNonneg
    · have hQnonneg : 0 ≤ D.Qref Θ c.1 (D.obsOf π) := D.Qref_nonneg Θ c.1 (D.obsOf π)
      have hQpos : 0 < D.Qref Θ c.1 (D.obsOf π) := lt_of_le_of_ne hQnonneg (Ne.symm hQ0)
      have hCandGate : D.CandGate Θc c.1 := by
        by_contra hfalse
        exact hgate hfalse
      let Iref : ℝ := ∏ j, (π.1 j).elim 1 (fun i => (D.refInt Θ c.1).w i)
      let Cref : ℝ := ∏ u : D.CrossSub c.1,
        (D.refCross Θ c.1 u.1).w ((π.2 u).2.1, (π.2 u).2.2)
      have hQdecomp : D.Qref Θ c.1 (D.obsOf π) = Iref * Cref := rfl
      have hQprodPos : 0 < Iref * Cref := by rw [← hQdecomp]; exact hQpos
      have hCrefNonneg : 0 ≤ Cref := by
        dsimp [Cref]
        exact Finset.prod_nonneg fun u hu => (D.refCross Θ c.1 u.1).nonneg _
      have hIrefPos : 0 < Iref := by
        by_contra hnot
        have hle : Iref ≤ 0 := le_of_not_gt hnot
        have hmul : Iref * Cref ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hCrefNonneg
        exact (not_le_of_gt hQprodPos) hmul
      have hIrefNonneg : 0 ≤ Iref := by
        dsimp [Iref]
        apply Finset.prod_nonneg
        intro j hj
        cases hopt : π.1 j with
        | none => simp [hopt]
        | some i => simp [hopt]; exact (D.refInt Θ c.1).nonneg i
      have hCrefPos : 0 < Cref := by
        by_contra hnot
        have hle : Cref ≤ 0 := le_of_not_gt hnot
        have hmul : Iref * Cref ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hIrefNonneg hle
        exact (not_le_of_gt hQprodPos) hmul
      have hRefInt (j : D.Loc) (i : D.M.ι) (hSome : π.1 j = some i) :
          (D.refInt Θ c.1).w i ≠ 0 := by
        intro hz
        have hzero : Iref = 0 := by
          dsimp [Iref]
          apply Finset.prod_eq_zero (Finset.mem_univ j)
          simp [hSome, hz]
        exact (ne_of_gt hIrefPos) hzero
      have hRefCross (u : D.CrossSub c.1) :
          (D.refCross Θ c.1 u.1).w ((π.2 u).2.1, (π.2 u).2.2) ≠ 0 := by
        intro hz
        have hzero : Cref = 0 := by
          dsimp [Cref]
          apply Finset.prod_eq_zero (Finset.mem_univ u)
          simp [hz]
        exact (ne_of_gt hCrefPos) hzero
      let Iobs : ℝ := ∏ j, (π.1 j).elim 1 (fun i => (D.tilt Θc c.1).w i)
      let Ctag : ℝ := ∏ u : D.CrossSub c.1,
        (D.tilt Θc u.1).w ((π.2 u).2.1)
      let Ptag : D.KeyT → D.Loc → FinProb D.M.ι := fun g _ => D.tilt Θc g
      have hTagCylinder : (D.tagLawAll Θc).pr BTag' ≤
          ∏ x ∈ Lane_q_s08_post.observedTagCoords D c π,
            (D.tilt Θc x.1).w (Lane_q_s08_post.observedTagValue D c π dflt x) := by
        simpa [Ctx.tagLawAll] using
          Lane_q_s08_post.pi_pi_pr_le_fixed Ptag
            (Lane_q_s08_post.observedTagCoords D c π)
            (Lane_q_s08_post.observedTagValue D c π dflt) BTag'
            (fun t ht x hx => by
              change ∀ x ∈ Lane_q_s08_post.observedTagCoords D c π,
                t x.1 x.2 = Lane_q_s08_post.observedTagValue D c π dflt x at ht
              exact ht x hx)
      have hTagRaw : (D.rawTAT Θc).pr (fun z => BTag' z.1.1) ≤
          (D.tagLawAll Θc).pr BTag' :=
        Lane_q_s08_post.rawTAT_pr_le_tags D Θc (fun z => BTag' z.1.1) BTag'
          (fun z hz => hz)
      have hTagProbIndicator :
          (D.rawTAT Θc).pr (fun z => BTag' z.1.1) =
            ∑ z, (D.rawTAT Θc).w z *
              (@ite ℝ ((fun z => BTag' z.1.1) z)
                (Classical.propDecidable _) (1 : ℝ) 0) :=
        Lane_q_s08_post.pr_eq_weighted_indicator (D.rawTAT Θc)
          (fun z => BTag' z.1.1)
      have hEventTag (z : D.TAT) (W : D.Anch) (hE : Ev z W) : BTag' z.1.1 :=
        by
          change ∀ x ∈ Lane_q_s08_post.observedTagCoords D c π,
            z.1.1 x.1 x.2 = Lane_q_s08_post.observedTagValue D c π dflt x
          exact Lane_q_s08_post.pres_tag_spec D (qOf z) W c π dflt hE.2
      let Aprod : ℝ := ∏ u : D.CrossSub c.1,
        (D.anchorU Θc u.1 (π.2 u).2.1).w (π.2 u).2.2
      have hAprod : 0 ≤ Aprod := by
        dsimp [Aprod]
        exact Finset.prod_nonneg fun u hu => (D.anchorU Θc u.1 (π.2 u).2.1).nonneg _
      have hAnchor (z : D.TAT) :
          (D.rawAnchors (qOf z)).pr (fun W => Ev z W) ≤
            (if BTag' z.1.1 then Aprod else 0) := by
        by_cases htag : BTag' z.1.1
        · have hbound := Lane_q_s08_post.raw_anchors_cross_presentation_le D (qOf z) c π
            (fun W => Ev z W) (fun W hE => hE.2) (fun W hE => hE.1)
          simpa [Aprod, htag] using hbound
        · have hnone : ∀ W, ¬ Ev z W := by
            intro W hE
            exact htag (hEventTag z W hE)
          have hzero : (D.rawAnchors (qOf z)).pr (fun W => Ev z W) = 0 := by
            unfold FinProb.pr
            apply Finset.sum_eq_zero
            intro W hW
            simp [hnone W]
          simp [htag, hzero]
      have hBind :
          (D.rawLaw Θc P).pr (fun z => Ev z.1 z.2) =
            ∑ z, (D.rawTAT Θc).w z * (D.rawAnchors (qOf z)).pr (fun W => Ev z W) := by
        simpa [Ctx.rawLaw, qOf] using
          Lane_q_s08_post.bind_pr_eq_sum (D.rawTAT Θc)
            (fun z => D.rawAnchors ((Θc, P), z)) (fun zW => Ev zW.1 zW.2)
      have hrawBound : (D.rawLaw Θc P).pr (fun z => Ev z.1 z.2) ≤
          Aprod * (D.rawTAT Θc).pr (fun z => BTag' z.1.1) := by
        calc
          _ = ∑ z, (D.rawTAT Θc).w z * (D.rawAnchors (qOf z)).pr (fun W => Ev z W) := hBind
          _ ≤ ∑ z, (D.rawTAT Θc).w z *
                (if BTag' z.1.1 then Aprod else 0) := by
                  apply Finset.sum_le_sum
                  intro z hz
                  exact mul_le_mul_of_nonneg_left (hAnchor z) ((D.rawTAT Θc).nonneg z)
          _ = Aprod * (D.rawTAT Θc).pr (fun z => BTag' z.1.1) := by
                calc
                  _ = ∑ z, Aprod * ((D.rawTAT Θc).w z *
                        (@ite ℝ ((fun z => BTag' z.1.1) z)
                          (Classical.propDecidable _) (1 : ℝ) 0)) := by
                        apply Finset.sum_congr rfl
                        intro z hz
                        by_cases hb : BTag' z.1.1 <;> simp [hb] <;> ring
                  _ = Aprod * ∑ z, (D.rawTAT Θc).w z *
                        (@ite ℝ ((fun z => BTag' z.1.1) z)
                          (Classical.propDecidable _) (1 : ℝ) 0) := by
                        rw [← Finset.mul_sum]
                  _ = Aprod * (D.rawTAT Θc).pr (fun z => BTag' z.1.1) := by
                        rw [← hTagProbIndicator]
      have hrawBoundTag : (D.rawLaw Θc P).pr (fun z => Ev z.1 z.2) ≤
          Aprod * ∏ x ∈ Lane_q_s08_post.observedTagCoords D c π,
            (D.tilt Θc x.1).w (Lane_q_s08_post.observedTagValue D c π dflt x) :=
        hrawBound.trans (mul_le_mul_of_nonneg_left (hTagRaw.trans hTagCylinder) hAprod)
      have hobsProd := Lane_q_s08_post.observed_tag_weight_product D Θc c π dflt
      have hIntCancel :
          (∏ j, D.intRatio Θ c.1 ξ (π.1 j)) * Iref = Iobs := by
        dsimp [Iref, Iobs]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j hj
        cases hSome : π.1 j with
        | none => simp [Ctx.intRatio, hSome]
        | some i =>
            simpa [Ctx.intRatio, hSome] using
              (div_mul_cancel₀ ((D.tilt Θc c.1).w i) (hRefInt j i hSome))
      have hCrossCancel :
          (∏ u : D.CrossSub c.1,
            D.crossRatio Θ c.1 ξ u ((π.2 u).2.1, (π.2 u).2.2)) * Cref =
            ∏ u : D.CrossSub c.1,
              (D.tilt Θc u.1).w ((π.2 u).2.1) *
                (D.anchorU Θc u.1 (π.2 u).2.1).w (π.2 u).2.2 := by
        dsimp [Cref]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro u hu
        simpa [Ctx.crossRatio, Θc] using
          (div_mul_cancel₀
            ((D.tilt Θc u.1).w ((π.2 u).2.1) *
              (D.anchorU Θc u.1 (π.2 u).2.1).w (π.2 u).2.2)
            (hRefCross u))
      have hCrossTagAnchor :
          (∏ u : D.CrossSub c.1,
            (D.tilt Θc u.1).w ((π.2 u).2.1) *
              (D.anchorU Θc u.1 (π.2 u).2.1).w (π.2 u).2.2) = Ctag * Aprod := by
        dsimp [Ctag, Aprod]
        rw [Finset.prod_mul_distrib]
      have hFcQ :
          D.Fcand Θ c.1 ξ (D.obsOf π) * D.Qref Θ c.1 (D.obsOf π) = Aprod *
            (∏ x ∈ Lane_q_s08_post.observedTagCoords D c π,
              (D.tilt Θc x.1).w (Lane_q_s08_post.observedTagValue D c π dflt x)) := by
        unfold Ctx.Fcand Ctx.Qref
        rw [if_pos hCandGate]
        simp only [Ctx.obsOf]
        calc
          _ = ((∏ j, D.intRatio Θ c.1 ξ (π.1 j)) * Iref) *
                ((∏ u : D.CrossSub c.1,
                  D.crossRatio Θ c.1 ξ u ((π.2 u).2.1, (π.2 u).2.2)) * Cref) := by
                  dsimp [Iref, Cref]
                  ring
          _ = Iobs * (Ctag * Aprod) := by rw [hIntCancel, hCrossCancel, hCrossTagAnchor]
          _ = Aprod *
                (∏ x ∈ Lane_q_s08_post.observedTagCoords D c π,
                  (D.tilt Θc x.1).w (Lane_q_s08_post.observedTagValue D c π dflt x)) := by
                  rw [hobsProd]
                  ring
      have hnum : (D.rawLaw Θc P).pr (fun z => Ev z.1 z.2) ≤
          D.Fcand Θ c.1 ξ (D.obsOf π) * D.Qref Θ c.1 (D.obsOf π) := by
        calc
          _ ≤ Aprod * ∏ x ∈ Lane_q_s08_post.observedTagCoords D c π,
                (D.tilt Θc x.1).w (Lane_q_s08_post.observedTagValue D c π dflt x) := hrawBoundTag
          _ = D.Fcand Θ c.1 ξ (D.obsOf π) * D.Qref Θ c.1 (D.obsOf π) := hFcQ.symm
      unfold Ctx.Gsel
      exact (div_le_iff₀ hQpos).2 hnum

set_option maxHeartbeats 200000

/-- L8.1g(ii) (08:245–254): on a valid presentation (`M ≥ ε₀`, at most `T` internal IDs), the base posterior has
density at most `e^{1.5δhs log n}`; the selected posterior `F_ξ a_ξ dR'/M^a` with `M^a ≥ ε₀ M` is at most `ε₀^{-1}`
times the base posterior (`a_ξ ≤ 1`); `2.5δ ≤ .003`. -/
theorem sel_post_cap (hh : 1 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → D.PostCap → D.GselLeF → D.SelPostCap := by
  classical
  refine ⟨1, ?_⟩
  intro D hn hPost hG
  have hlogn : 0 ≤ Real.log D.n := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hx : 0 ≤ (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg h) (Nat.cast_nonneg _)) hlogn
  have hepspos : 0 < D.eps0 := Real.exp_pos _
  have hepsinv : D.eps0⁻¹ =
      Real.exp ((1 / 10000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := by
    simp [Ctx.eps0, Real.exp_neg]
  have hcoeff :
      (15 / 100000 : ℝ) * (h : ℝ) * sC η₀ D.n * Real.log D.n +
          (1 / 10000 : ℝ) * h * sC η₀ D.n * Real.log D.n ≤
        (3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n := by
    nlinarith [hx]
  intro q W c hvalid ξ
  let π : D.Pres c.1 := D.presOf q W c
  have hpv : D.PresValid q W c := hvalid
  have hden : D.eps0 ≤ D.Mden q.1.1 c.1 (D.obsOf π) := hpv.2.2.2.2.2
  have hMpos : 0 < D.Mden q.1.1 c.1 (D.obsOf π) := lt_of_lt_of_le hepspos hden
  have hcardInt : (D.intIds q c).card ≤ TC η₀ D.n := hpv.2.2.2.1
  have hfilter :
      (Finset.univ.filter fun ℓ : D.Loc => ((D.obsOf π).1 ℓ).isSome) = D.intIds q c := by
    ext ℓ
    simp [π, Ctx.obsOf, Ctx.presOf]
  have hobsCard :
      (Finset.univ.filter fun ℓ : D.Loc => ((D.obsOf π).1 ℓ).isSome).card ≤ TC η₀ D.n := by
    rw [hfilter]
    exact hcardInt
  have hbasecap : (D.N : ℝ) ^ h * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ ≤
      Real.exp ((15 / 100000 : ℝ) * h * sC η₀ D.n * Real.log D.n) :=
    hPost q.1.1 c.1 (D.obsOf π) hobsCard hden ξ
  have hbaseEq : (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ =
      D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π) /
        D.Mden q.1.1 c.1 (D.obsOf π) := by
    have hsumpos : 0 < ∑ ξ', D.R'.w ξ' * D.Fcand q.1.1 c.1 ξ' (D.obsOf π) := by
      simpa [Ctx.Mden] using hMpos
    change (if ∑ ξ', D.R'.w ξ' * D.Fcand q.1.1 c.1 ξ' (D.obsOf π) = 0 then
        D.R'.w ξ else
        D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π) /
          ∑ ξ', D.R'.w ξ' * D.Fcand q.1.1 c.1 ξ' (D.obsOf π)) = _
    rw [if_neg (ne_of_gt hsumpos)]
    rfl
  by_cases hadj : D.eps0 * D.Mden q.1.1 c.1 (D.obsOf π) ≤ D.Mad q.1.1 q.1.2 c π
  · have hMadpos : 0 < D.Mad q.1.1 q.1.2 c π := lt_of_lt_of_le (mul_pos hepspos hMpos) hadj
    have hsumMadPos : 0 < ∑ ξ', D.R'.w ξ' * D.Gsel q.1.1 q.1.2 c ξ' π := by
      simpa [Ctx.Mad] using hMadpos
    have hGξ : D.Gsel q.1.1 q.1.2 c ξ π ≤ D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
      hG q.1.1 q.1.2 c ξ π
    have hnumle : D.R'.w ξ * D.Gsel q.1.1 q.1.2 c ξ π ≤
        D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
      mul_le_mul_of_nonneg_left hGξ (D.R'.nonneg ξ)
    have hnumNonneg : 0 ≤ D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
      mul_nonneg (D.R'.nonneg ξ) (D.Fcand_nonneg q.1.1 c.1 ξ (D.obsOf π))
    have hselEq : (D.selPost q.1.1 q.1.2 c π).w ξ =
        (D.R'.w ξ * D.Gsel q.1.1 q.1.2 c ξ π) / D.Mad q.1.1 q.1.2 c π := by
      unfold Ctx.selPost
      rw [if_pos hadj]
      change (if ∑ ξ', D.R'.w ξ' * D.Gsel q.1.1 q.1.2 c ξ' π = 0 then
          (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ else
          D.R'.w ξ * D.Gsel q.1.1 q.1.2 c ξ π /
            ∑ ξ', D.R'.w ξ' * D.Gsel q.1.1 q.1.2 c ξ' π) = _
      rw [if_neg (ne_of_gt hsumMadPos)]
      rfl
    have hselbase : (D.selPost q.1.1 q.1.2 c π).w ξ ≤
        D.eps0⁻¹ * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ := by
      calc
        (D.selPost q.1.1 q.1.2 c π).w ξ =
            (D.R'.w ξ * D.Gsel q.1.1 q.1.2 c ξ π) / D.Mad q.1.1 q.1.2 c π := hselEq
        _ ≤ (D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π)) / D.Mad q.1.1 q.1.2 c π :=
            div_le_div_of_nonneg_right hnumle hMadpos.le
        _ ≤ (D.R'.w ξ * D.Fcand q.1.1 c.1 ξ (D.obsOf π)) /
            (D.eps0 * D.Mden q.1.1 c.1 (D.obsOf π)) :=
              div_le_div_of_nonneg_left hnumNonneg (mul_pos hepspos hMpos) hadj
        _ = D.eps0⁻¹ * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ := by
              rw [hbaseEq]
              field_simp [ne_of_gt hepspos, ne_of_gt hMpos]
    calc
      (D.N : ℝ) ^ h * (D.selPost q.1.1 q.1.2 c π).w ξ ≤
          (D.N : ℝ) ^ h * (D.eps0⁻¹ * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ) :=
            mul_le_mul_of_nonneg_left hselbase (by positivity)
      _ = D.eps0⁻¹ * ((D.N : ℝ) ^ h * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ) := by ring
      _ ≤ D.eps0⁻¹ * Real.exp ((15 / 100000 : ℝ) * h * sC η₀ D.n * Real.log D.n) :=
            mul_le_mul_of_nonneg_left hbasecap (inv_nonneg.mpr hepspos.le)
      _ = Real.exp ((1 / 10000 : ℝ) * h * sC η₀ D.n * Real.log D.n +
            (15 / 100000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := by
            rw [hepsinv, ← Real.exp_add]
      _ ≤ Real.exp ((3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hcoeff]
  · have hselEq : (D.selPost q.1.1 q.1.2 c π).w ξ =
        (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ := by
      unfold Ctx.selPost
      rw [if_neg hadj]
    calc
      (D.N : ℝ) ^ h * (D.selPost q.1.1 q.1.2 c π).w ξ =
          (D.N : ℝ) ^ h * (D.basePost q.1.1 c.1 (D.obsOf π)).w ξ := by rw [hselEq]
      _ ≤ Real.exp ((15 / 100000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := hbasecap
      _ ≤ Real.exp ((3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hx]

/-- L8.1g(iii) (08:256–264): with `q` the average coordinate marginal of the selected posterior and
`𝓗 = {y : Nq(y) > e^{.01 s log n}}`, `F-HeavyTrunc` (`heavyTruncation` with `A = .003hs log n`,
`B = .01 s log n`, `⌈h/2⌉` coordinates) gives `q(𝓗) ≤ 1/2 + 1/(2h) + o(1) ≤ .6`, so the light mass is at least
`.4`; `p⁰` is `q` off `𝓗` normalized. -/
theorem p0_law (hh : 10 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.SelPostCap → D.P0Law := by
  classical
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (Real.exp (10000 : ℝ))
  refine ⟨n₀, ?_⟩
  intro D hn hGrid hSel
  have htag : Nonempty D.M.ι := by
    by_contra htag
    haveI : IsEmpty D.M.ι := ⟨fun i => htag ⟨i⟩⟩
    have hsum : (∑ i, D.M.Λ i) = 0 := by simp
    rw [D.M.Λ_sum] at hsum
    norm_num at hsum
  have hNpos : 0 < D.N := by
    obtain ⟨i⟩ := htag
    have hNnonempty : Nonempty (Fin D.N) := by
      by_contra hN
      haveI : IsEmpty (Fin D.N) := ⟨fun x => hN ⟨x⟩⟩
      have hsum : (∑ x, (D.M.μ i).w x) = 0 := by simp
      rw [(D.M.μ i).sum_eq_one] at hsum
      norm_num at hsum
    obtain ⟨x⟩ := hNnonempty
    apply Nat.pos_of_ne_zero
    intro hzero
    have hxlt : x.val < 0 := by simpa [hzero] using x.isLt
    exact Nat.not_lt_zero _ hxlt
  have hn₀pos : 1 ≤ n₀ := by
    have hpos : (0 : ℝ) < (n₀ : ℝ) := lt_trans (Real.exp_pos _) hn₀
    exact_mod_cast hpos
  have hnpos : 1 ≤ D.n := le_trans hn₀pos hn
  have hlarge : Real.exp (10000 : ℝ) ≤ (D.n : ℝ) :=
    le_of_lt (lt_of_lt_of_le hn₀ (by exact_mod_cast hn))
  have hlogn : 10000 ≤ Real.log D.n := by
    have := Real.log_le_log (Real.exp_pos (10000 : ℝ)) hlarge
    simpa using this
  have hs : 1 ≤ sC η₀ D.n := hGrid.pos.2.2
  have hsReal : 1 ≤ (sC η₀ D.n : ℝ) := by exact_mod_cast hs
  have hhpos : 0 < h := by omega
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow : (2 : ℝ) ^ h ≤ Real.exp (h : ℝ) := by
    calc
      (2 : ℝ) ^ h ≤ (Real.exp 1) ^ h := by gcongr
      _ = Real.exp (h : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
  have hheavy_bound (Q : FinProb D.Tup)
      (hcap : ∀ ξ, (D.N : ℝ) ^ h * Q.w ξ ≤
        Real.exp ((3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n)) :
      ∑ y ∈ heavyCoordinateSet Q D.heavyB, averageCoordinateMarginal Q y ≤ 3 / 5 := by
    let A : ℝ := (3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n
    let B : ℝ := D.heavyB
    let q : ℕ := h / 2
    let H : Finset (Fin D.N) := heavyCoordinateSet Q B
    let x : ℝ := (sC η₀ D.n : ℝ) * Real.log D.n
    have hqle : q ≤ h := by dsimp [q]; omega
    have hqNat : h - 1 ≤ 2 * q := by dsimp [q]; omega
    have hhReal : 10 ≤ (h : ℝ) := by exact_mod_cast hh
    have hqNatLower : 45 * h ≤ 100 * q := by dsimp [q]; omega
    have hqLower : (45 / 100 : ℝ) * (h : ℝ) ≤ (q : ℝ) := by
      have hcast : (45 : ℝ) * (h : ℝ) ≤ 100 * (q : ℝ) := by exact_mod_cast hqNatLower
      nlinarith [hcast]
    have hx : 10000 ≤ x := by
      dsimp [x]
      calc
        (10000 : ℝ) ≤ 1 * Real.log D.n := by nlinarith [hlogn]
        _ ≤ (sC η₀ D.n : ℝ) * Real.log D.n :=
          mul_le_mul_of_nonneg_right hsReal (by linarith [hlogn])
    have hxnonneg : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 10000) hx
    have hqX : (45 / 100 : ℝ) * (h : ℝ) * x ≤ (q : ℝ) * x :=
      mul_le_mul_of_nonneg_right hqLower hxnonneg
    have hHx : 10000 * (h : ℝ) ≤ (h : ℝ) * x := by
      calc
        10000 * (h : ℝ) = (h : ℝ) * 10000 := by ring
        _ ≤ (h : ℝ) * x := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg h)
    have hErrExp : (h : ℝ) + (3 / 1000 : ℝ) * (h : ℝ) * x -
        (1 / 100 : ℝ) * x * (q : ℝ) ≤ -140 := by
      calc
        (h : ℝ) + (3 / 1000 : ℝ) * (h : ℝ) * x -
            (1 / 100 : ℝ) * x * (q : ℝ) ≤
        (h : ℝ) + (3 / 1000 : ℝ) * (h : ℝ) * x -
            (45 / 10000 : ℝ) * (h : ℝ) * x := by nlinarith [hqX]
        _ = (h : ℝ) - (15 / 10000 : ℝ) * (h : ℝ) * x := by ring
        _ ≤ (h : ℝ) - 15 * (h : ℝ) := by nlinarith [hHx]
        _ ≤ -140 := by nlinarith [hhReal]
    have hcap' : ∀ ξ, (D.N : ℝ) ^ h * Q.w ξ ≤ Real.exp A := by simpa [A] using hcap
    have htr := heavyTruncation hNpos hhpos Q A B hcap'
    have hErr : (2 : ℝ) ^ h * Real.exp A * Real.exp (-B * (q : ℝ)) ≤ Real.exp (-140) := by
      calc
        (2 : ℝ) ^ h * Real.exp A * Real.exp (-B * (q : ℝ)) ≤
            Real.exp (h : ℝ) * Real.exp A * Real.exp (-B * (q : ℝ)) := by gcongr
        _ = Real.exp ((h : ℝ) + A - B * (q : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1 <;> ring
        _ ≤ Real.exp (-140) := by
            apply Real.exp_le_exp.mpr
            have hexp : (h : ℝ) + A - B * (q : ℝ) =
                (h : ℝ) + (3 / 1000 : ℝ) * (h : ℝ) * x -
                  (1 / 100 : ℝ) * x * (q : ℝ) := by
              dsimp [A, B, x, Ctx.heavyB]
              ring
            rw [hexp]
            exact hErrExp
    have h141 : (141 : ℝ) ≤ Real.exp 140 := by
      have := Real.add_one_le_exp (140 : ℝ)
      linarith
    have hErrSmall : Real.exp (-140) ≤ 1 / 10 := by
      have hinv : (Real.exp 140)⁻¹ ≤ (141 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h141
      calc
        Real.exp (-140) = (Real.exp 140)⁻¹ := by rw [Real.exp_neg]
        _ ≤ (141 : ℝ)⁻¹ := hinv
        _ ≤ 1 / 10 := by norm_num
    have hratio : (q : ℝ) / (h : ℝ) ≤ 1 / 2 := by
      have hhRpos : 0 < (h : ℝ) := by exact_mod_cast hhpos
      have hqNat' : 2 * q ≤ h := by dsimp [q]; omega
      have hqCast' : 2 * (q : ℝ) ≤ (h : ℝ) := by exact_mod_cast hqNat'
      apply (div_le_iff₀ hhRpos).2
      nlinarith [hqCast']
    have hmassH : ∑ y ∈ H, averageCoordinateMarginal Q y ≤
        (q : ℝ) / h + (2 : ℝ) ^ h * Real.exp A * Real.exp (-B * (q : ℝ)) := by
      simpa [H] using htr.2 q hqle
    have hmassH' : (∑ y ∈ H, averageCoordinateMarginal Q y) ≤ 3 / 5 := by
      calc
        (∑ y ∈ H, averageCoordinateMarginal Q y) ≤
            (q : ℝ) / h + (2 : ℝ) ^ h * Real.exp A * Real.exp (-B * (q : ℝ)) := hmassH
        _ ≤ 1 / 2 + 1 / 10 := add_le_add hratio (le_trans hErr hErrSmall)
        _ = 3 / 5 := by norm_num
    exact hmassH'
  have hlight_nonneg (Q : FinProb D.Tup) : 0 ≤ D.lightMass Q := by
    unfold Ctx.lightMass
    apply Finset.sum_nonneg
    intro y hy
    have hI : 0 ≤ (if y ∈ heavyCoordinateSet Q D.heavyB then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    exact mul_nonneg (avgMarg_nonneg Q y) hI
  intro q W c
  refine ⟨?_, ?_⟩
  · intro y
    by_cases hv : D.PresValid q W c
    · let Q : FinProb D.Tup := D.selPost q.1.1 q.1.2 c (D.presOf q W c)
      have hm : 0 ≤ D.lightMass Q := hlight_nonneg Q
      unfold Ctx.p0
      simp only [if_pos hv]
      by_cases hz : D.lightMass Q = 0
      · simp [Ctx.p0w, Q, hz]
      · have hmpos : 0 < D.lightMass Q := lt_of_le_of_ne hm (Ne.symm hz)
        have hI : 0 ≤ (if y ∈ heavyCoordinateSet Q D.heavyB then (0 : ℝ) else 1) := by
          split_ifs <;> norm_num
        simpa [Ctx.p0w, Q, hz] using
          (div_nonneg (mul_nonneg (avgMarg_nonneg Q y) hI) hmpos.le)
    · simp [Ctx.p0, hv]
  · intro hv
    let π : D.Pres c.1 := D.presOf q W c
    let Q : FinProb D.Tup := D.selPost q.1.1 q.1.2 c π
    have hcap : ∀ ξ, (D.N : ℝ) ^ h * Q.w ξ ≤
        Real.exp ((3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n) := by
      intro ξ
      exact hSel q W c hv ξ
    have hheavy := hheavy_bound Q hcap
    have hLightLower : (2 / 5 : ℝ) ≤ D.lightMass Q := by
      have htotal : ∑ y : Fin D.N, averageCoordinateMarginal Q y = 1 := avgMarg_sum_one Q hhpos
      have hlightEq : D.lightMass Q = ∑ y ∈ (heavyCoordinateSet Q D.heavyB)ᶜ,
          averageCoordinateMarginal Q y := by
        unfold Ctx.lightMass
        calc
          ∑ y, averageCoordinateMarginal Q y *
              (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1) =
            ∑ y, if y ∈ (heavyCoordinateSet Q D.heavyB)ᶜ then averageCoordinateMarginal Q y else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyH : y ∈ heavyCoordinateSet Q D.heavyB <;> simp [hyH]
          _ = ∑ y ∈ (heavyCoordinateSet Q D.heavyB)ᶜ, averageCoordinateMarginal Q y := by
              rw [Finset.sum_ite_mem_eq]
      have hparts : (∑ y ∈ heavyCoordinateSet Q D.heavyB, averageCoordinateMarginal Q y) +
          D.lightMass Q = 1 := by
        calc
          _ = (∑ y ∈ heavyCoordinateSet Q D.heavyB, averageCoordinateMarginal Q y) +
              (∑ y ∈ (heavyCoordinateSet Q D.heavyB)ᶜ, averageCoordinateMarginal Q y) := by rw [hlightEq]
          _ = ∑ y, averageCoordinateMarginal Q y := by rw [Finset.sum_add_sum_compl]
          _ = 1 := htotal
      linarith [hparts, hheavy]
    have hLightPos : 0 < D.lightMass Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 5) hLightLower
    have hrow (y : Fin D.N) : D.p0 q W c y =
        averageCoordinateMarginal Q y *
          (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1) / D.lightMass Q := by
      simp [Ctx.p0, hv, Ctx.p0w, Q, π, ne_of_gt hLightPos]
    have hnumerSum :
        (∑ y, averageCoordinateMarginal Q y *
          (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1)) = D.lightMass Q := by
      unfold Ctx.lightMass
      rfl
    have hMargBound (y : Fin D.N) : D.p0 q W c y ≤ (5 / 2 : ℝ) * averageCoordinateMarginal Q y := by
      have hind : (if y ∈ heavyCoordinateSet Q D.heavyB then (0 : ℝ) else 1) ≤ 1 := by
        split_ifs <;> norm_num
      have hnum : averageCoordinateMarginal Q y *
          (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1) ≤ averageCoordinateMarginal Q y := by
        calc
          _ ≤ averageCoordinateMarginal Q y * 1 :=
            mul_le_mul_of_nonneg_left hind (avgMarg_nonneg Q y)
          _ = averageCoordinateMarginal Q y := by ring
      calc
        D.p0 q W c y =
            averageCoordinateMarginal Q y *
              (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1) / D.lightMass Q := hrow y
        _ ≤ averageCoordinateMarginal Q y / D.lightMass Q :=
            div_le_div_of_nonneg_right hnum hLightPos.le
        _ ≤ averageCoordinateMarginal Q y / (2 / 5 : ℝ) :=
            div_le_div_of_nonneg_left (avgMarg_nonneg Q y) (by norm_num) hLightLower
        _ = (5 / 2 : ℝ) * averageCoordinateMarginal Q y := by field_simp <;> ring
    refine ⟨?_, ?_, ?_⟩
    · calc
        ∑ y, D.p0 q W c y =
            ∑ y, averageCoordinateMarginal Q y *
              (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1) / D.lightMass Q := by
                apply Finset.sum_congr rfl
                intro y hy
                exact hrow y
        _ = (∑ y, averageCoordinateMarginal Q y *
              (if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1)) / D.lightMass Q := by
                rw [← Finset.sum_div]
        _ = 1 := by rw [hnumerSum, div_self (ne_of_gt hLightPos)]
    · exact hMargBound
    · intro y
      by_cases hy : y ∈ heavyCoordinateSet Q D.heavyB
      · have hzero : D.p0 q W c y = 0 := by rw [hrow y]; simp [hy]
        rw [hzero]
        have hnonneg : 0 ≤ (3 : ℝ) * Real.exp D.heavyB :=
          mul_nonneg (by norm_num) (Real.exp_nonneg _)
        simpa using hnonneg
      · have hcapLight : (D.N : ℝ) * averageCoordinateMarginal Q y ≤ Real.exp D.heavyB := by
          by_contra hnot
          have hlt : Real.exp D.heavyB < (D.N : ℝ) * averageCoordinateMarginal Q y := lt_of_not_ge hnot
          apply hy
          simp [heavyCoordinateSet, hlt]
        calc
          (D.N : ℝ) * D.p0 q W c y ≤
              (D.N : ℝ) * ((5 / 2 : ℝ) * averageCoordinateMarginal Q y) :=
                mul_le_mul_of_nonneg_left (hMargBound y) (Nat.cast_nonneg D.N)
          _ = (5 / 2 : ℝ) * ((D.N : ℝ) * averageCoordinateMarginal Q y) := by ring
          _ ≤ (5 / 2 : ℝ) * Real.exp D.heavyB :=
                mul_le_mul_of_nonneg_left hcapLight (by norm_num)
          _ ≤ 3 * Real.exp D.heavyB :=
                mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)

/-- L8.1g(iv) (08:171–176, 293): a label in the support of `p⁰` is a coordinate of a candidate with positive
selected posterior, hence with `F_ξ > 0` (directly, or through `F_ξ a_ξ ≤ F_ξ`), hence hitting every observed cross
anchor. -/
theorem p0_support (D : Ctx η₀ β p h) (hF : D.FSupport) (hG : D.GselLeF) : D.P0Support := by
  classical
  unfold Ctx.P0Support
  intro q W c y hp0 u hu
  have hvalid : D.PresValid q W c := by
    by_contra hnot
    apply hp0
    simp [Ctx.p0, hnot]
  have hden : D.eps0 ≤ D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c)) :=
    hvalid.2.2.2.2.2
  have hM : 0 < D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c)) :=
    lt_of_lt_of_le (Real.exp_pos _) hden
  have hp0w : D.p0w q.1.1 q.1.2 c (D.presOf q W c) y ≠ 0 := by
    intro hz
    apply hp0
    simp [Ctx.p0, hvalid, hz]
  let π : D.Pres c.1 := D.presOf q W c
  let Q : FinProb D.Tup := D.selPost q.1.1 q.1.2 c π
  have hlight : D.lightMass Q ≠ 0 := by
    intro hz
    apply hp0w
    simp [Ctx.p0w, π, Q, hz]
  have hMarg : averageCoordinateMarginal Q y ≠ 0 := by
    intro hz
    apply hp0w
    simp [Ctx.p0w, π, Q, hlight, hz]
  obtain ⟨ξ, j, hξ, hcoord⟩ := avgMarg_ne_zero_support Q y hMarg
  have hQpos : 0 < Q.w ξ := lt_of_le_of_ne (Q.nonneg ξ) (Ne.symm hξ)
  have hGξ : D.Gsel q.1.1 q.1.2 c ξ π ≤ D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
    hG q.1.1 q.1.2 c ξ π
  have hFcand : 0 < D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
    selPost_pos_fcand_pos D q.1.1 q.1.2 c π ξ hM hGξ (by simpa [Q] using hQpos)
  have hfs := hF q.1.1 c.1 ξ (D.obsOf π) (ne_of_gt hFcand)
  have hh := hfs.1 ⟨u, hu⟩ j
  change Hits D.E D.G (W (u, c.2)) (ξ j) at hh
  rw [hcoord] at hh
  exact hh

/-- L8.1g(v) (08:266–283): valid data for a presentation `π` have subdensity `M^a_π` against `Q_π`; on the
selected-posterior cases cancellation gives at most `dR'(ξ) Σ_π ∫ F_ξ a_ξ dQ_π ≤ dR'(ξ)`; on the other cases
`M^a < ε₀ M` bounds the contribution by `ε₀ L_n dR'(ξ) = o(dR'(ξ))` (validly presentable lists are candidate lists
at positions with incident counts `≤ 2λ`, `h ≥ 10⁸`).  Taking average coordinate marginals,
`E_{R'}` of a coordinate is `E_Λ ν_i` (`N max ≤ 4K`), and the truncation costs `5/2`.  The density bounds make
the valid-presentation probability vanish wherever the reference `Q_π` does, so it equals `F_ξ a_ξ Q_π`. -/
theorem p0_raw_mean (hη₀ : 0 < η₀) (hK : 0 < K) (hh : 10 ^ 8 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.DensityBounds → D.ListCount → D.P0Law → D.GselLeF → D.P0RawMean K := by
  sorry

/-- L8.1g(vi) (08:285–290): `p⁰_{g,a}` reads the selections at its incident even cells (`SelLocal`, keys within one
of `g`), the tags of the selected IDs, the position gate, the gates and references (hidden keys within two), the
selection adjustment (the raw experiment at fixed positions and non-target tuples, whose relevant marginals read
hidden keys within four and positions within three) and the cross anchors. -/
theorem p0_local (D : Ctx η₀ β p h) (hS : D.SelLocal) : D.P0Local := by
  classical
  unfold Ctx.P0Local
  intro q q' W W' c hHidden hPosTag hActTie hCrossAnchor
  have hSelEq (e : D.CellT) (hkey : keyDist c.1 e.1 ≤ 1) :
      D.sel q e = D.sel q' e := by
    apply hS q q' e
    · intro g hg
      have hEg := (Finset.mem_filter.mp hg).2
      have hCg : keyDist c.1 g ≤ 4 := by
        have htri := Lane_q_s08_post.keyDist_triangle c.1 e.1 g
        omega
      have hg4 : g ∈ keyBall c.1 4 := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ g, hCg⟩
      exact hHidden g hg4
    · intro g hg ℓ hℓ
      have hEg := (Finset.mem_filter.mp hg).2
      have hCg : keyDist c.1 g ≤ 3 := by
        have htri := Lane_q_s08_post.keyDist_triangle c.1 e.1 g
        omega
      have hg3 : g ∈ keyBall c.1 3 := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ g, hCg⟩
      have hpt := hPosTag g hg3
      exact ⟨congrFun hpt.1 ℓ, congrFun hpt.2 ℓ⟩
    · intro ℓ hℓ
      have he1 : e.1 ∈ keyBall c.1 1 := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ e.1
        · exact hkey
      have hat := hActTie e.1 he1
      exact ⟨congrFun hat.1 ℓ, congrFun hat.2 ℓ⟩
  have hOrdSel (b : Res η₀ D.n) (hb : b ∈ ordNbrs c.2) :
      D.sel q (c.1, b) = D.sel q' (c.1, b) := by
    apply hSelEq (c.1, b)
    simp [keyDist]
  have hCrossSel (u : D.CrossSub c.1) :
      D.sel q (u.1, c.2) = D.sel q' (u.1, c.2) := by
    apply hSelEq (u.1, c.2)
    have hu : keyDist c.1 u.1 = 1 := by
      simpa [crossKeys] using (Finset.mem_filter.mp u.2).2
    change keyDist c.1 u.1 ≤ 1
    rw [hu]
  have hIntIds : D.intIds q c = D.intIds q' c := by
    unfold Ctx.intIds
    ext ℓ
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨b, hb, hℓ⟩
      refine ⟨b, hb, ?_⟩
      rw [hOrdSel b hb] at hℓ
      exact hℓ
    · rintro ⟨b, hb, hℓ⟩
      refine ⟨b, hb, ?_⟩
      rw [← hOrdSel b hb] at hℓ
      exact hℓ
  have hCrossId (u : D.CrossSub c.1) : D.crossId q c u = D.crossId q' c u := by
    unfold Ctx.crossId
    rw [hCrossSel u]
  have hKeyBall3 : c.1 ∈ keyBall c.1 3 := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · simp [keyDist]
  have hTagKey : q.2.1.1 c.1 = q'.2.1.1 c.1 := (hPosTag c.1 hKeyBall3).2
  have hPres : D.presOf q W c = D.presOf q' W' c := by
    apply Prod.ext
    · funext ℓ
      simp only [Ctx.presOf]
      by_cases hℓ : ℓ ∈ D.intIds q c
      · have hℓ' : ℓ ∈ D.intIds q' c := by rw [← hIntIds]; exact hℓ
        simp [hℓ, hℓ', congrFun hTagKey ℓ]
      · have hℓ' : ℓ ∉ D.intIds q' c := by rw [← hIntIds]; exact hℓ
        simp [hℓ, hℓ']
    · funext u
      simp only [Ctx.presOf]
      have hKey : u.1 ∈ keyBall c.1 3 := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ u.1
        · have hu : keyDist c.1 u.1 = 1 := by
            simpa [crossKeys] using (Finset.mem_filter.mp u.2).2
          omega
      have hTagU := (hPosTag u.1 hKey).2
      have hAnchor := hCrossAnchor u.1 u.2
      change (D.crossId q c u, q.2.1.1 u.1 (D.crossId q c u), W (u.1, c.2)) =
        (D.crossId q' c u, q'.2.1.1 u.1 (D.crossId q' c u), W' (u.1, c.2))
      rw [hCrossId u, congrFun hTagU (D.crossId q' c u), hAnchor]
  have hHidden2 : ∀ g ∈ keyBall c.1 2, q.1.1 g = q'.1.1 g := by
    intro g hg
    have hdist := (Finset.mem_filter.mp hg).2
    have hg4 : g ∈ keyBall c.1 4 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hdist.trans (by omega)⟩
    exact hHidden g hg4
  have hCandGateEq :=
    Lane_q_s08_post.candGate_congr_of_radius_two D q.1.1 q'.1.1 c.1 hHidden2
  have hPadKey3 (e : D.CellT) (he : PadNbr c e) : e.1 ∈ keyBall c.1 3 := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ e.1
    · rcases he with ⟨hek, hOrd⟩ | ⟨hres, hCross⟩
      · rw [hek]
        simp [keyDist]
      · have hdist := (Finset.mem_filter.mp hCross).2
        exact hdist.le.trans (by omega)
  have hPosCountEq : D.PosCountOK q.1.2 c = D.PosCountOK q'.1.2 c := by
    apply propext
    constructor <;> intro hPos e he j
    · have hp := (hPosTag e.1 (hPadKey3 e he)).1
      have hcount : D.ballCount q'.1.2 e.1 e.2 j = D.ballCount q.1.2 e.1 e.2 j := by
        unfold Ctx.ballCount
        rw [hp]
      rw [hcount]
      exact hPos e he j
    · have hp := (hPosTag e.1 (hPadKey3 e he)).1
      have hcount : D.ballCount q.1.2 e.1 e.2 j = D.ballCount q'.1.2 e.1 e.2 j := by
        unfold Ctx.ballCount
        rw [hp]
      rw [hcount]
      exact hPos e he j
  have hHist2 : ∀ g, keyDist c.1 g ≤ 2 → q.1.1 g = q'.1.1 g := by
    intro g hg
    have hg4 : keyDist c.1 g ≤ 4 := hg.trans (by omega)
    have hmem : g ∈ keyBall c.1 4 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg4⟩
    exact hHidden g hmem
  have hObs : D.obsOf (D.presOf q W c) = D.obsOf (D.presOf q' W' c) :=
    congrArg D.obsOf hPres
  have hMdenEq :
      D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c)) =
        D.Mden q'.1.1 c.1 (D.obsOf (D.presOf q' W' c)) := by
    rw [hObs]
    exact Lane_q_s08_post.mden_congr_radius_two D q.1.1 q'.1.1 c.1
      (D.obsOf (D.presOf q' W' c)) hHist2
  have hOrdValid :
      (∀ b ∈ ordNbrs c.2, (D.sel q (c.1, b)).isSome) ↔
        (∀ b ∈ ordNbrs c.2, (D.sel q' (c.1, b)).isSome) := by
    constructor
    · intro hh b hb
      rw [← hOrdSel b hb]
      exact hh b hb
    · intro hh b hb
      rw [hOrdSel b hb]
      exact hh b hb
  have hCrossValid :
      (∀ u : D.CrossSub c.1, (D.sel q (u.1, c.2)).isSome) ↔
        (∀ u : D.CrossSub c.1, (D.sel q' (u.1, c.2)).isSome) := by
    constructor
    · intro hh u
      rw [← hCrossSel u]
      exact hh u
    · intro hh u
      rw [hCrossSel u]
      exact hh u
  have hPresValidEq : D.PresValid q W c = D.PresValid q' W' c := by
    apply propext
    unfold Ctx.PresValid
    rw [hCandGateEq, hOrdValid, hCrossValid, hIntIds, hPosCountEq, hMdenEq]
  sorry

set_option maxHeartbeats 1000000
/-- L8.1h(i) (08:295–297): fix the valid presentation and cross anchors.  A label of `p⁰` is a coordinate of a
supported candidate `ξ`; for an observed internal tag `i`, the cutoff under `ξ` gives
`μ_i{misses ξ | hits Θ_{E(g)}} ≤ Δ`, and the true cutoff (the tag has positive probability under `S_g`, `Z_g > 0`)
gives `d_i^+ ≥ (1-Δ)d_i^-`, so under `U_{g,i}` the miss probability is at most `Δ/(1-Δ)`.  Summing over the at most
`n+1` ordinary anchors and Markov at `.02` (with `Σ p⁰ = 1`, `P0Law`) gives the bound. -/
theorem hit_tail (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) (hF : D.FSupport) (hG : D.GselLeF) (hL : D.P0Law) :
    D.HitTail := by
  classical
  intro q W c hSupp hvalid
  let P : ∀ e : D.ordCells c, FinProb (Fin D.N) := fun e => D.Usel q e.1
  let Pa : FinProb (∀ e : D.ordCells c, Fin D.N) := FinProb.pi P
  let anchorMiss : (∀ e : D.ordCells c, Fin D.N) → Fin D.N → Prop := fun a y =>
    ¬ D.OrdHit (glue (D.ordCells c) W a) c y
  let missMass : (∀ e : D.ordCells c, Fin D.N) → ℝ := fun a =>
    ∑ y, D.p0 q W c y *
      (@ite ℝ (anchorMiss a y)
        (Classical.propDecidable _) (1 : ℝ) 0)
  have hLvalid := hL q W c
  have hP0nonneg (y : Fin D.N) : 0 ≤ D.p0 q W c y := hLvalid.1 y
  have hP0sum : ∑ y, D.p0 q W c y = 1 := (hLvalid.2 hvalid).1
  have hOrd (a : ∀ e : D.ordCells c, Fin D.N) (y : Fin D.N) :=
    Lane_q_s08_post.ordHit_iff_product D c W a y
  have hcross (a : ∀ e : D.ordCells c, Fin D.N) :
      ∀ u : D.CrossSub c.1, W (u.1, c.2) = (glue (D.ordCells c) W a) (u.1, c.2) := by
    intro u
    exact (Lane_q_s08_post.glue_ordCells_eq_on_cross D c W a u).symm
  have hvalidGlue (a : ∀ e : D.ordCells c, Fin D.N) :
      D.PresValid q (glue (D.ordCells c) W a) c :=
    (Lane_q_s08_post.presValid_iff_cross_anchors_eq D q W
      (glue (D.ordCells c) W a) c (hcross a)).mp hvalid
  have hp0Glue (a : ∀ e : D.ordCells c, Fin D.N) (y : Fin D.N) :
      D.p0 q W c y = D.p0 q (glue (D.ordCells c) W a) c y :=
    Lane_q_s08_post.p0_eq_of_cross_anchors_eq D q W
      (glue (D.ordCells c) W a) c (hcross a) y
  have hP0sumGlue (a : ∀ e : D.ordCells c, Fin D.N) :
      ∑ y, D.p0 q (glue (D.ordCells c) W a) c y = 1 :=
    ((hL q (glue (D.ordCells c) W a) c).2 (hvalidGlue a)).1
  have hmissEq (a : ∀ e : D.ordCells c, Fin D.N) :
      missMass a = 1 - D.ordRet q (glue (D.ordCells c) W a) c := by
    unfold missMass Ctx.ordRet
    calc
      (∑ y, D.p0 q W c y *
          (@ite ℝ (anchorMiss a y) (Classical.propDecidable _) (1 : ℝ) 0)) =
          ∑ y, (D.p0 q (glue (D.ordCells c) W a) c y -
            D.p0 q (glue (D.ordCells c) W a) c y *
            (if D.OrdHit (glue (D.ordCells c) W a) c y then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hp0Glue a y]
              by_cases ho : D.OrdHit (glue (D.ordCells c) W a) c y <;>
                simp [anchorMiss, ho] <;> ring
      _ = (∑ y, D.p0 q (glue (D.ordCells c) W a) c y) -
            ∑ y, D.p0 q (glue (D.ordCells c) W a) c y *
              (if D.OrdHit (glue (D.ordCells c) W a) c y then 1 else 0) := by
              rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ y, D.p0 q (glue (D.ordCells c) W a) c y *
            (if D.OrdHit (glue (D.ordCells c) W a) c y then 1 else 0) := by
              rw [hP0sumGlue a]
  have hmissNonneg (a : ∀ e : D.ordCells c, Fin D.N) : 0 ≤ missMass a := by
    apply Finset.sum_nonneg
    intro y hy
    have hind : 0 ≤
        (@ite ℝ (anchorMiss a y)
          (Classical.propDecidable _) (1 : ℝ) 0) := by
      split_ifs <;> norm_num
    exact mul_nonneg (hP0nonneg y) hind
  have hhitPoint (a : ∀ e : D.ordCells c, Fin D.N) :
      (if D.HitFail q (glue (D.ordCells c) W a) c then 1 else 0) ≤ 50 * missMass a := by
    by_cases hfail : D.HitFail q (glue (D.ordCells c) W a) c
    · have hmiss : (1 / 50 : ℝ) < missMass a := by
        rw [hmissEq]
        unfold Ctx.HitFail at hfail
        linarith
      rw [if_pos hfail]
      nlinarith
    · rw [if_neg hfail]
      exact mul_nonneg (by norm_num) (hmissNonneg a)
  have hdelta : D.Δ < 1 := by
    have hnR : 0 < (D.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
    have hpow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
    unfold Ctx.Δ
    have hlt : Real.exp (-((D.n : ℝ) ^ (p / 2))) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (neg_neg_of_pos hpow)
    simpa using hlt
  have hdenpos : 0 < 1 - D.Δ := sub_pos.mpr hdelta
  let rate : ℝ := D.Δ / (1 - D.Δ)
  have hrateNonneg : 0 ≤ rate := by
    dsimp [rate]
    exact div_nonneg (le_of_lt (Real.exp_pos _)) hdenpos.le
  have hmissProb (y : Fin D.N) :
      Pa.pr (fun a => anchorMiss a y) =
        ∑ a, Pa.w a * (@ite ℝ (anchorMiss a y)
          (Classical.propDecidable _) (1 : ℝ) 0) := by
    exact Lane_q_s08_post.pr_eq_weighted_indicator Pa (fun a => anchorMiss a y)
  have hmissExpectation :
      ∑ a, Pa.w a * missMass a =
        ∑ y, D.p0 q W c y * Pa.pr
          (fun a => anchorMiss a y) := by
    unfold missMass
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      ∑ a, Pa.w a * (D.p0 q W c y *
          (@ite ℝ (anchorMiss a y) (Classical.propDecidable _) (1 : ℝ) 0)) =
          ∑ a, D.p0 q W c y * (Pa.w a *
            (@ite ℝ (anchorMiss a y) (Classical.propDecidable _) (1 : ℝ) 0)) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = D.p0 q W c y * ∑ a, Pa.w a *
            (@ite ℝ (anchorMiss a y) (Classical.propDecidable _) (1 : ℝ) 0) := by
              rw [Finset.mul_sum]
      _ = D.p0 q W c y * Pa.pr
            (fun a => anchorMiss a y) := by
              rw [← hmissProb y]
  have hmissExpectation_le :
      ∑ a, Pa.w a * missMass a ≤
        (Fintype.card (D.ordCells c) : ℝ) * rate := by
    have hunion (y : Fin D.N) :
        Pa.pr (fun a => anchorMiss a y) ≤
          ∑ e : D.ordCells c, (P e).pr (fun x => ¬ Hits D.E D.G x y) := by
      have hmono := Lane_q_s08_post.pr_mono Pa
        (fun a => anchorMiss a y)
        (fun a => ¬ ∀ e : D.ordCells c, Hits D.E D.G (a e) y)
        (fun a hmiss hhit => by
          change ¬ D.OrdHit (glue (D.ordCells c) W a) c y at hmiss
          exact hmiss ((hOrd a y).mpr hhit))
      exact hmono.trans (Lane_q_s08_post.pi_pr_not_forall_le_sum P
        (fun _ x => Hits D.E D.G x y))
    calc
      ∑ a, Pa.w a * missMass a =
          ∑ y, D.p0 q W c y * Pa.pr
            (fun a => anchorMiss a y) := hmissExpectation
      _ ≤ ∑ y, D.p0 q W c y *
            ∑ e : D.ordCells c, (P e).pr (fun x => ¬ Hits D.E D.G x y) := by
              apply Finset.sum_le_sum
              intro y hy
              exact mul_le_mul_of_nonneg_left (hunion y) (hP0nonneg y)
      _ ≤ ∑ y, D.p0 q W c y * ((Fintype.card (D.ordCells c) : ℝ) * rate) := by
              apply Finset.sum_le_sum
              intro y hy
              by_cases hp0 : D.p0 q W c y = 0
              · simp [hp0]
              · have honeach (e : D.ordCells c) :
                    (P e).pr (fun x => ¬ Hits D.E D.G x y) ≤ rate := by
                  change (D.Usel q e.1).pr (fun x => ¬ Hits D.E D.G x y) ≤ rate
                  exact Lane_q_s08_post.selected_anchor_miss_bound D hn hF hG q W c hSupp hvalid e y hp0
                have hsum :
                    (∑ e : D.ordCells c, (P e).pr (fun x => ¬ Hits D.E D.G x y)) ≤
                      (Fintype.card (D.ordCells c) : ℝ) * rate := by
                  calc
                    _ ≤ ∑ e : D.ordCells c, rate := Finset.sum_le_sum fun e he => honeach e
                    _ = (Fintype.card (D.ordCells c) : ℝ) * rate :=
                      Lane_q_s08_post.sum_subtype_const (D.ordCells c) rate
                exact mul_le_mul_of_nonneg_left hsum (hP0nonneg y)
      _ = (Fintype.card (D.ordCells c) : ℝ) * rate := by
            rw [← Finset.sum_mul, hP0sum]
            ring
  have hcard : Fintype.card (D.ordCells c) ≤ D.n + 1 := by
    simpa using Lane_q_s08_post.ordCells_card_le_n_add_one D c
  have hcardReal : (Fintype.card (D.ordCells c) : ℝ) ≤ (D.n : ℝ) + 1 := by
    exact_mod_cast hcard
  have hweighted :
      ∑ a, Pa.w a * (if D.HitFail q (glue (D.ordCells c) W a) c then 1 else 0) ≤
        50 * ((Fintype.card (D.ordCells c) : ℝ) * rate) := by
    calc
      _ ≤ ∑ a, Pa.w a * (50 * missMass a) := by
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (hhitPoint a) (Pa.nonneg a)
      _ = 50 * ∑ a, Pa.w a * missMass a := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ ≤ 50 * ((Fintype.card (D.ordCells c) : ℝ) * rate) :=
            mul_le_mul_of_nonneg_left hmissExpectation_le (by norm_num)
  change (∑ a : (∀ e : D.ordCells c, Fin D.N),
      (∏ e : D.ordCells c, (D.Usel q e.1).w (a e)) *
        (if D.HitFail q (glue (D.ordCells c) W a) c then 1 else 0)) ≤ _
  calc
    _ = ∑ a, Pa.w a *
          (if D.HitFail q (glue (D.ordCells c) W a) c then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            rfl
    _ ≤ 50 * ((Fintype.card (D.ordCells c) : ℝ) * rate) := hweighted
    _ ≤ 50 * ((D.n : ℝ) + 1) * rate := by
          have hinner : ((Fintype.card (D.ordCells c) : ℝ) * rate) ≤
              ((D.n : ℝ) + 1) * rate := mul_le_mul_of_nonneg_right hcardReal hrateNonneg
          calc
            50 * ((Fintype.card (D.ordCells c) : ℝ) * rate) ≤
                50 * (((D.n : ℝ) + 1) * rate) := mul_le_mul_of_nonneg_left hinner (by norm_num)
            _ = 50 * ((D.n : ℝ) + 1) * rate := by ring
    _ = 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
          dsimp [rate]
          ring

set_option maxHeartbeats 200000

/-- L8.1h(ii) (08:293–300): the odd row restricts `p⁰` (cross hits) to ordinary hits, normalized by a retained mass
`≥ .98`, so `p ≤ p⁰/.98`, `N max p ≤ 3e^{.01 s log n}/.98 ≤ e^{.02 s log n}` for large `n`, and `p` hits every
padded even anchor. -/
theorem prow_facts :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → D.P0Law → D.P0Support → D.PRowFacts := by
  classical
  let C : ℝ := 3 / (98 / 100)
  have hC : 0 < C := by norm_num [C]
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (Real.exp (100 * Real.log C))
  refine ⟨n₀, ?_⟩
  intro D hn hL hS
  have hn₀pos : 1 ≤ n₀ := by
    have hpos : (0 : ℝ) < (n₀ : ℝ) := lt_trans (Real.exp_pos _) hn₀
    exact_mod_cast hpos
  have hnpos : 1 ≤ D.n := le_trans hn₀pos hn
  have hlarge : Real.exp (100 * Real.log C) ≤ (D.n : ℝ) := by
    exact le_of_lt (lt_of_lt_of_le hn₀ (by exact_mod_cast hn))
  have hloglarge : 100 * Real.log C ≤ Real.log D.n := by
    have := Real.log_le_log (Real.exp_pos _) hlarge
    simpa using this
  have hlogn : 0 ≤ Real.log D.n := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hnpos)
  have hs : 1 ≤ sC η₀ D.n := by
    unfold sC
    apply Nat.one_le_ceil_iff.mpr
    exact Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
  have hsreal : 1 ≤ (sC η₀ D.n : ℝ) := by exact_mod_cast hs
  have hlogC : Real.log C ≤ (1 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n := by
    have hlogsmall : Real.log C ≤ (1 / 100 : ℝ) * Real.log D.n := by
      calc
        Real.log C = (1 / 100 : ℝ) * (100 * Real.log C) := by ring
        _ ≤ (1 / 100 : ℝ) * Real.log D.n := mul_le_mul_of_nonneg_left hloglarge (by norm_num)
    have hmul : (1 / 100 : ℝ) * Real.log D.n ≤
        (1 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n := by
      have hnonneg : 0 ≤ (1 / 100 : ℝ) * Real.log D.n := mul_nonneg (by norm_num) hlogn
      calc
        (1 / 100 : ℝ) * Real.log D.n = 1 * ((1 / 100 : ℝ) * Real.log D.n) := by ring
        _ ≤ (sC η₀ D.n : ℝ) * ((1 / 100 : ℝ) * Real.log D.n) :=
          mul_le_mul_of_nonneg_right hsreal hnonneg
        _ = (1 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n := by ring
    exact le_trans hlogsmall hmul
  have hCexp : C ≤ Real.exp D.heavyB := by
    rw [← Real.exp_log hC]
    apply Real.exp_le_exp.mpr
    change Real.log C ≤ (1 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n
    exact hlogC
  have hExp : C * Real.exp D.heavyB ≤
      Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) := by
    calc
      C * Real.exp D.heavyB ≤ Real.exp D.heavyB * Real.exp D.heavyB :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_nonneg _)
      _ = Real.exp (D.heavyB + D.heavyB) := by rw [← Real.exp_add]
      _ = Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) := by
        congr 1 <;> dsimp [Ctx.heavyB] <;> ring
  intro q W c
  refine ⟨?_, ?_, ?_⟩
  · intro y
    by_cases hv : D.Valid8 q W c
    · have hret : 0 < D.ordRet q W c :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 98 / 100) hv.2
      have hnum : 0 ≤ D.p0 q W c y * if D.OrdHit W c y then 1 else 0 :=
        mul_nonneg ((hL q W c).1 y) (ind_nonneg _)
      unfold Ctx.prow
      simp only [if_pos hv]
      exact div_nonneg hnum hret.le
    · simp [Ctx.prow, hv]
  · intro y hp e he
    have hv : D.Valid8 q W c := by
      by_contra hnot
      apply hp
      simp [Ctx.prow, hnot]
    have hp0 : D.p0 q W c y ≠ 0 := by
      intro hz
      apply hp
      simp [Ctx.prow, hv, hz]
    have hord : D.OrdHit W c y := by
      by_contra hnot
      apply hp
      simp [Ctx.prow, hv, hnot]
    rcases he with ⟨hek, hOrd⟩ | ⟨hek, hCross⟩
    · change Hits D.E D.G (W (e.1, e.2)) y
      rw [hek]
      exact hord e.2 hOrd
    · change Hits D.E D.G (W (e.1, e.2)) y
      rw [hek]
      exact hS q W c y hp0 e.1 hCross
  · intro hv
    have hret : 0 < D.ordRet q W c :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 98 / 100) hv.2
    have hretne : D.ordRet q W c ≠ 0 := ne_of_gt hret
    have hp0nonneg (y : Fin D.N) : 0 ≤ D.p0 q W c y := (hL q W c).1 y
    have hrow (y : Fin D.N) :
        D.prow q W c y =
          (D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) / D.ordRet q W c := by
      simp [Ctx.prow, hv]
    have hrowBound (y : Fin D.N) : D.prow q W c y ≤ D.p0 q W c y / (98 / 100 : ℝ) := by
      have hindicator : (if D.OrdHit W c y then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have hnum : D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) ≤ D.p0 q W c y := by
        calc
          D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) ≤ D.p0 q W c y * 1 :=
            mul_le_mul_of_nonneg_left hindicator (hp0nonneg y)
          _ = D.p0 q W c y := by ring
      calc
        D.prow q W c y =
            (D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) / D.ordRet q W c := hrow y
        _ ≤ D.p0 q W c y / D.ordRet q W c := div_le_div_of_nonneg_right hnum hret.le
        _ ≤ D.p0 q W c y / (98 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (hp0nonneg y) (by norm_num) hv.2
    refine ⟨?_, ?_, ?_⟩
    · calc
        ∑ y, D.prow q W c y =
            ∑ y, (D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) / D.ordRet q W c := by
              apply Finset.sum_congr rfl
              intro y hy
              exact hrow y
        _ = (∑ y, D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) / D.ordRet q W c := by
              rw [← Finset.sum_div]
        _ = 1 := by
              have hsumne : (∑ y, D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) ≠ 0 := by
                simpa [Ctx.ordRet] using hretne
              rw [Ctx.ordRet]
              exact div_self hsumne
    · intro y
      have hindicator : (if D.OrdHit W c y then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have hnum : D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) ≤ D.p0 q W c y := by
        calc
          D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) ≤ D.p0 q W c y * 1 :=
            mul_le_mul_of_nonneg_left hindicator (hp0nonneg y)
          _ = D.p0 q W c y := by ring
      calc
        D.prow q W c y =
            (D.p0 q W c y * (if D.OrdHit W c y then 1 else 0)) / D.ordRet q W c := hrow y
        _ ≤ D.p0 q W c y / D.ordRet q W c := div_le_div_of_nonneg_right hnum hret.le
        _ ≤ D.p0 q W c y / (98 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (hp0nonneg y) (by norm_num) hv.2
    · intro y
      have hnum : (D.N : ℝ) * D.p0 q W c y ≤ 3 * Real.exp D.heavyB :=
        ((hL q W c).2 hv.1).2.2 y
      calc
        (D.N : ℝ) * D.prow q W c y ≤ (D.N : ℝ) * (D.p0 q W c y / (98 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hrowBound y) (Nat.cast_nonneg D.N)
        _ = ((D.N : ℝ) * D.p0 q W c y) / (98 / 100 : ℝ) := by ring
        _ ≤ (3 * Real.exp D.heavyB) / (98 / 100 : ℝ) :=
          div_le_div_of_nonneg_right hnum (by norm_num)
        _ = C * Real.exp D.heavyB := by dsimp [C]; ring
        _ ≤ Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) := hExp

end Nodes

end HypercubeRamsey.S08
