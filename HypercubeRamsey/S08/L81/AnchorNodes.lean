import HypercubeRamsey.S08.L81.LoadNodes
import HypercubeRamsey.S08.L81.AnchorNodes_q_s08_anchor

/-!
# Lemma 8.1, Step 10: anchor avoidance and predictive alarms

Source: `sections/08-…tex`, lines 365–393 (L8.1j).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1j(i) (08:366): on a successful history the presentation of `c` other than its cross anchors is fixed and
legitimate, the gates hold, and the cross anchors are independent with laws `U_{u,i}` of the selected cross tags;
so the raw probability of `M < ε₀` is `q_L` of the used list, at most `ε₀^{1/4}` (`SelConseq`). -/
theorem den_fail_prob (D : Ctx η₀ β p h) (hS : D.SelConseq) : D.DenFailProb := by
  classical
  intro q hGood c
  rcases hGood with ⟨hSupp, hSel⟩
  rcases hSupp with ⟨hHidden, hTagSupp⟩
  have hSuppGood : D.Supp q := ⟨hHidden, hTagSupp⟩
  rcases hS q hSel with ⟨hSelected, hConsequences⟩
  rcases hConsequences c with ⟨hCount, hPosCount, hqL, hLegal⟩
  have hBase (g : D.KeyT) : D.BaseGates q.1.1 g := by
    by_contra hb
    exact hHidden g (Or.inl hb)
  have hCand : D.CandGate q.1.1 c.1 := by
    refine ⟨hBase c.1, ?_⟩
    intro u hu
    exact hBase u
  let oi : D.Loc → Option D.M.ι := fun ℓ =>
    if ℓ ∈ D.intIds q c then some (q.2.1.1 c.1 ℓ) else none
  let ct : D.CrossSub c.1 → D.M.ι := fun u =>
    q.2.1.1 u.1 (D.crossId q c u)
  have hUsel (u : D.CrossSub c.1) :
      D.Usel q (u.1, c.2) = D.anchorU q.1.1 u.1 (ct u) := by
    have hsome := hSelected (u.1, c.2)
    cases hselu : D.sel q (u.1, c.2) with
    | none => simp [hselu] at hsome
    | some ℓ => simp [Ctx.Usel, Ctx.selTag, Ctx.crossId, ct, hselu]
  let S : Finset D.CellT := D.crossCells c
  let SCoord := {t : D.CellT // t ∈ S}
  let Pcoord : SCoord → FinProb (Fin D.N) := fun t => D.Usel q t.1
  let Q : FinProb (∀ t : SCoord, Fin D.N) := FinProb.pi Pcoord
  let Wbase : D.Anch := Classical.choice (finProb_nonempty (D.rawAnchors q))
  let splitEquiv := Equiv.piEquivPiSubtypeProd (fun t : D.CellT => t ∈ S)
    (fun _ : D.CellT => Fin D.N)
  let rebuild (a : ∀ t : SCoord, Fin D.N) : D.Anch :=
    splitEquiv.symm (a, fun t : {t : D.CellT // t ∉ S} => Wbase t.1)
  have hdep : FinProb.DependsOn (fun W : D.Anch => D.DenFail q W c) S := by
    intro W W' hW
    exact D.denFail_eq_of_crossCells q W W' c hW
  have hraw : (D.rawAnchors q).pr (fun W => D.DenFail q W c) =
      Q.pr (fun a => D.DenFail q (rebuild a) c) := by
    simpa [Ctx.rawAnchors, Pcoord, Q, S, rebuild, splitEquiv] using
      (pi_pr_depends_eq (fun t : D.CellT => D.Usel q t) S
        (fun W : D.Anch => D.DenFail q W c) Wbase hdep)
  let E : (∀ t : SCoord, Fin D.N) ≃ (D.CrossSub c.1 → Fin D.N) :=
    Equiv.piCongrLeft' (fun _ : SCoord => Fin D.N) (D.crossCellEquiv c).symm
  have hfullCross (x : D.CrossSub c.1 → Fin D.N) (u : D.CrossSub c.1) :
      rebuild (E.symm x) (u.1, c.2) = x u := by
    have hmem : (u.1, c.2) ∈ S := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    simp [rebuild, E, splitEquiv, hmem, Equiv.piEquivPiSubtypeProd_symm_apply,
      Ctx.crossCellEquiv]
  have hobs (x : D.CrossSub c.1 → Fin D.N) :
      D.obsOf (D.presOf q (rebuild (E.symm x)) c) = (oi, fun u => (ct u, x u)) := by
    apply Prod.ext
    · rfl
    · funext u
      simp [Ctx.obsOf, Ctx.presOf, oi, ct, hfullCross]
  have hden (x : D.CrossSub c.1 → Fin D.N) :
      D.DenFail q (rebuild (E.symm x)) c =
        (D.Mden q.1.1 c.1 (J := D.Loc) (oi, fun u => (ct u, x u)) < D.eps0) := by
    simp [Ctx.DenFail, hobs]
  have hsumProb : Q.pr (fun a => D.DenFail q (rebuild a) c) =
      ∑ x : D.CrossSub c.1 → Fin D.N,
        (∏ u, (D.anchorU q.1.1 u.1 (ct u)).w (x u)) *
          (if D.Mden q.1.1 c.1 (J := D.Loc) (oi, fun u => (ct u, x u)) < D.eps0 then 1 else 0) := by
    have hpr : Q.pr (fun a => D.DenFail q (rebuild a) c) =
        ∑ a : ∀ t : SCoord, Fin D.N,
          Q.w a * (if D.DenFail q (rebuild a) c then 1 else 0) := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hbad : D.DenFail q (rebuild a) c <;> simp [hbad]
    rw [hpr, ← Equiv.sum_comp E.symm]
    apply Finset.sum_congr rfl
    intro x hx
    have hweight : Q.w (E.symm x) =
        ∏ u : D.CrossSub c.1, (D.anchorU q.1.1 u.1 (ct u)).w (x u) := by
      unfold Q Pcoord FinProb.pi
      change (∏ t : SCoord, (D.Usel q t.1).w ((E.symm x) t)) = _
      apply Fintype.prod_equiv (D.crossCellEquiv c).symm
      intro t
      let u : D.CrossSub c.1 := (D.crossCellEquiv c).symm t
      have hcell : (u.1, c.2) = t.1 :=
        congrArg Subtype.val (Equiv.apply_symm_apply (D.crossCellEquiv c) t)
      have hassign : (E.symm x) t = x u := by
        simp [E, u, Equiv.piCongrLeft']
      rw [hassign, ← hcell, hUsel]
    rw [hweight, hden]
  have hqLbound : D.qL q.1.1 c.1 oi ct ≤ Real.sqrt (Real.sqrt D.eps0) := by
    simpa [oi, ct] using hqL
  have hcrossEq :
      (∑ x : D.CrossSub c.1 → Fin D.N,
        (∏ u, (D.anchorU q.1.1 u.1 (ct u)).w (x u)) *
          (if D.Mden q.1.1 c.1 (J := D.Loc) (oi, fun u => (ct u, x u)) < D.eps0 then 1 else 0)) =
        D.qL q.1.1 c.1 oi ct := by
    unfold Ctx.qL
    simp [hCand, oi, ct]
  calc
    (D.rawAnchors q).pr (fun W => D.DenFail q W c) =
        Q.pr (fun a => D.DenFail q (rebuild a) c) := hraw
    _ = D.qL q.1.1 c.1 oi ct := by rw [hsumProb, hcrossEq]
    _ ≤ Real.sqrt (Real.sqrt D.eps0) := hqLbound

/-- L8.1j(ii) (08:366, 295–297): when the denominator test passes on a successful history the presentation is
valid; integrating the ordinary anchors (independent of the cross anchors and of validity) by `HitTail` bounds the
hit-test failure. -/
theorem hit_fail_prob (D : Ctx η₀ β p h) (hS : D.SelConseq) (hT : D.HitTail) : D.HitFailProb := by
  classical
  intro q hGood
  rcases hGood with ⟨hSupp, hSel⟩
  rcases hSupp with ⟨hHidden, hTagSupp⟩
  have hSuppGood : D.Supp q := ⟨hHidden, hTagSupp⟩
  rcases hS q hSel with ⟨hSelected, hConsequences⟩
  intro c
  rcases hConsequences c with ⟨hCount, hPosCount, hqL, hLegal⟩
  have hBase (g : D.KeyT) : D.BaseGates q.1.1 g := by
    by_contra hb
    exact hHidden g (Or.inl hb)
  have hCand : D.CandGate q.1.1 c.1 := by
    refine ⟨hBase c.1, ?_⟩
    intro u hu
    exact hBase u
  let A : Finset D.CellT := D.ordCells c
  let ACoord := {t : D.CellT // t ∈ A}
  let BCoord := {t : D.CellT // t ∉ A}
  let PA : FinProb (∀ t : ACoord, Fin D.N) := FinProb.pi fun t => D.Usel q t.1
  let PB : FinProb (∀ t : BCoord, Fin D.N) := FinProb.pi fun t => D.Usel q t.1
  let splitEquiv := Equiv.piEquivPiSubtypeProd (fun t : D.CellT => t ∈ A)
    (fun _ : D.CellT => Fin D.N)
  let Wbase : D.Anch := Classical.choice (finProb_nonempty (D.rawAnchors q))
  let Wout (b : ∀ t : BCoord, Fin D.N) : D.Anch := fun t =>
    if ht : t ∈ A then Wbase t else b ⟨t, ht⟩
  let whole (a : ∀ t : ACoord, Fin D.N) (b : ∀ t : BCoord, Fin D.N) : D.Anch :=
    splitEquiv.symm (a, b)
  have hglue (a : ∀ t : ACoord, Fin D.N) (b : ∀ t : BCoord, Fin D.N) :
      whole a b = glue A (Wout b) a := by
    funext t
    by_cases ht : t ∈ A <;>
      simp [whole, Wout, splitEquiv, glue, ht,
        Equiv.piEquivPiSubtypeProd_symm_apply]
  have hCrossOrd : Disjoint (D.crossCells c) A := by
    apply Finset.disjoint_left.mpr
    intro t htC htA
    rcases Finset.mem_image.mp htC with ⟨u, hu, huc⟩
    rcases Finset.mem_image.mp htA with ⟨b, hb, hbt⟩
    have hpair : (u.1, c.2) = (c.1, b) := huc.trans hbt.symm
    have hkey : u.1 = c.1 := congrArg Prod.fst hpair
    have huDist : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    have hbad : keyDist c.1 c.1 = 1 := by simpa [hkey] using huDist
    rw [D.keyDist_self] at hbad
    omega
  have hPresValid (W : D.Anch) (hnd : ¬ D.DenFail q W c) : D.PresValid q W c := by
    refine ⟨hCand, ?_, ?_, hCount, hPosCount, ?_⟩
    · intro b hb
      exact hSelected (c.1, b)
    · intro u
      exact hSelected (u.1, c.2)
    · have hM : ¬ D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c)) < D.eps0 := by
        simpa [Ctx.DenFail] using hnd
      exact le_of_not_gt hM
  have hDelta0 : 0 ≤ D.Δ := Real.exp_nonneg _
  have hDeltaLe : D.Δ ≤ 1 := by
    unfold Ctx.Δ
    apply Real.exp_le_one_iff.mpr
    have hrpow : 0 ≤ (D.n : ℝ) ^ (p / 2) :=
      Real.rpow_nonneg (by positivity : 0 ≤ (D.n : ℝ)) (p / 2)
    exact neg_nonpos.mpr hrpow
  have hC0 : 0 ≤ 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
    apply div_nonneg
    · positivity
    · linarith
  let Indicator : D.Anch → ℝ := fun W =>
    if ¬ D.DenFail q W c ∧ D.HitFail q W c then 1 else 0
  have hprIndicator : (D.rawAnchors q).pr (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) =
      (D.rawAnchors q).expect Indicator := by
    unfold FinProb.pr FinProb.expect Indicator
    apply Finset.sum_congr rfl
    intro W hW
    by_cases he : ¬ D.DenFail q W c ∧ D.HitFail q W c <;> simp [he]
  have hsplitProb : (D.rawAnchors q).pr
      (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) =
      ∑ a : ∀ t : ACoord, Fin D.N, ∑ b : ∀ t : BCoord, Fin D.N,
        (FinProb.pi (fun t : ACoord => D.Usel q t.1)).w a *
          (FinProb.pi (fun t : BCoord => D.Usel q t.1)).w b * Indicator (whole a b) := by
    rw [hprIndicator, Ctx.rawAnchors]
    simpa [Indicator, whole, splitEquiv] using
      (pi_expect_split_full (fun t : D.CellT => D.Usel q t) A Indicator)
  have hdenAgree (b : ∀ t : BCoord, Fin D.N) (a : ∀ t : ACoord, Fin D.N) :
      D.DenFail q (Wout b) c = D.DenFail q (glue A (Wout b) a) c := by
    apply D.denFail_eq_of_crossCells q (Wout b) (glue A (Wout b) a) c
    intro t ht
    have hnot : t ∉ A := by
      intro hmem
      exact (Finset.disjoint_left.mp hCrossOrd) ht hmem
    simp [glue, hnot, Wout]
  have hInner (b : ∀ t : BCoord, Fin D.N) :
      ∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b) ≤
        50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
    by_cases hnd : ¬ D.DenFail q (Wout b) c
    · have htail := hT q (Wout b) c hSuppGood (hPresValid (Wout b) hnd)
      have heq :
          (∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b)) =
            ∑ a : ∀ t : ACoord, Fin D.N,
              PA.w a * (if D.HitFail q (glue A (Wout b) a) c then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hnoGlue : ¬ D.DenFail q (glue A (Wout b) a) c := by
          intro hfail
          have hfail' : D.DenFail q (Wout b) c := by
            rw [hdenAgree b a]
            exact hfail
          exact hnd hfail'
        simp [Indicator, hglue a b, hnoGlue]
      rw [heq]
      have hPAw (a : ∀ t : ACoord, Fin D.N) :
          PA.w a = ∏ e : D.ordCells c, (D.Usel q e.1).w (a e) := by
        change (∏ t : ACoord, (D.Usel q t.1).w (a t)) = _
        rw [Finset.univ_eq_attach]
      have htail' :
          (∑ a : ∀ t : ACoord, Fin D.N,
            (∏ e : D.ordCells c, (D.Usel q e.1).w (a e)) *
              (if D.HitFail q (glue A (Wout b) a) c then 1 else 0)) ≤
            50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
        simpa [A] using htail
      calc
        (∑ a : ∀ t : ACoord, Fin D.N,
            PA.w a * (if D.HitFail q (glue A (Wout b) a) c then 1 else 0))
            = ∑ a : ∀ t : ACoord, Fin D.N,
                (∏ e : D.ordCells c, (D.Usel q e.1).w (a e)) *
                  (if D.HitFail q (glue A (Wout b) a) c then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [hPAw]
        _ ≤ 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := htail'
    · have hbad : D.DenFail q (Wout b) c := Classical.not_not.mp hnd
      have hzero : (∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b)) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hno : ¬ (¬ D.DenFail q (whole a b) c ∧ D.HitFail q (whole a b) c) := by
          intro he
          have hbad' : D.DenFail q (glue A (Wout b) a) c := by
            rw [← hdenAgree b a]
            exact hbad
          have hbadWhole : D.DenFail q (whole a b) c := by
            rw [hglue a b]
            exact hbad'
          exact he.1 hbadWhole
        simp [Indicator, hno]
      rw [hzero]
      exact hC0
  have houter : (∑ a : ∀ t : ACoord, Fin D.N, ∑ b : ∀ t : BCoord, Fin D.N,
      PA.w a * PB.w b * Indicator (whole a b)) =
      ∑ b : ∀ t : BCoord, Fin D.N, PB.w b *
        ∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ a : ∀ t : ACoord, Fin D.N, PA.w a * PB.w b * Indicator (whole a b)) =
          ∑ a, PB.w b * (PA.w a * Indicator (whole a b)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = PB.w b * ∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b) := by
            rw [← Finset.mul_sum]
  calc
    (D.rawAnchors q).pr (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) =
        ∑ b : ∀ t : BCoord, Fin D.N, PB.w b *
          ∑ a : ∀ t : ACoord, Fin D.N, PA.w a * Indicator (whole a b) := by
            rw [hsplitProb, houter]
    _ ≤ ∑ b : ∀ t : BCoord, Fin D.N, PB.w b *
          (50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ)) := by
            apply Finset.sum_le_sum
            intro b hb
            exact mul_le_mul_of_nonneg_left (hInner b) (PB.nonneg b)
    _ = 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
            calc
              (∑ b : ∀ t : BCoord, Fin D.N, PB.w b *
                  (50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ))) =
                  (∑ b : ∀ t : BCoord, Fin D.N, PB.w b) *
                    (50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ)) := by rw [Finset.sum_mul]
              _ = 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by rw [PB.sum_eq_one, one_mul]

/-- L8.1j(iii) (08:377–381): at a neighbour of the same key `p ≤ p⁰/.98` with `p⁰` the reference factor (`p⁰` there
does not read `v`'s anchor, an ordinary anchor of that cell); at the at most `m` other neighbours
`p ≤ e^{.02 s log n}/N`; so `F_z ≤ .98^{-n} e^{.02 s log n · m} Q_v ≤ e^{.03n} Q_v` (`ms log n = o(n)`). -/
theorem starLik_bound (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.PRowFacts → D.StarLikBound := by
  obtain ⟨n₀, hms⟩ := Ctx.eventually_m_s_log_le_quarter η₀
  refine ⟨n₀, ?_⟩
  intro D hn hG hP q W v z y
  let e : D.CellT := cellOf η₀ v
  let B : ℝ := (2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n
  let cSame : ℝ := (98 / 100 : ℝ)⁻¹
  let cCross : ℝ := Real.exp B
  let same : Fin D.n → Prop := fun j => (cellOf η₀ (cubeFlip v j)).1 = e.1
  let A : Fin D.n → ℝ := fun j => if same j then cSame else cCross
  have hfactor (j : Fin D.n) :
      D.prow q (Function.update W e z) (cellOf η₀ (cubeFlip v j)) (y j) ≤
        A j * D.refRow q W e (cellOf η₀ (cubeFlip v j)) (y j) := by
    simpa [A, B, cSame, cCross, same, e] using
      D.starLik_factor_le hG hP q W v z y j
  have hrow0 (j : Fin D.n) :
      0 ≤ D.prow q (Function.update W e z) (cellOf η₀ (cubeFlip v j)) (y j) :=
    (hP q (Function.update W e z) (cellOf η₀ (cubeFlip v j))).1 (y j)
  have hprod :
      (∏ j : Fin D.n, D.prow q (Function.update W e z)
        (cellOf η₀ (cubeFlip v j)) (y j)) ≤
        ∏ j : Fin D.n, A j * D.refRow q W e (cellOf η₀ (cubeFlip v j)) (y j) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      exact hrow0 j
    · intro j hj
      exact hfactor j
  have hlik : D.starLik q W v z y ≤ (∏ j : Fin D.n, A j) * D.starRef q W v y := by
    unfold Ctx.starLik
    calc
      (∏ j : Fin D.n, D.prow q (Function.update W e z)
          (cellOf η₀ (cubeFlip v j)) (y j)) ≤
        ∏ j : Fin D.n, A j * D.refRow q W e (cellOf η₀ (cubeFlip v j)) (y j) := hprod
      _ = (∏ j : Fin D.n, A j) * D.starRef q W v y := by
        unfold Ctx.starRef
        rw [Finset.prod_mul_distrib]
  have hsameCard : (Finset.univ.filter same).card ≤ D.n := by
    exact (Finset.card_filter_le Finset.univ same).trans_eq (by simp)
  have hcrossCard : (Finset.univ.filter fun j : Fin D.n => ¬ same j).card ≤ mC η₀ D.n := by
    have hEq : Finset.univ.filter (fun j : Fin D.n => ¬ same j) =
        Finset.univ.filter (fun j : Fin D.n =>
          keyOf η₀ (cubeFlip v j) ≠ keyOf η₀ v) := by
      ext j
      simp [same, e, cellOf, ne_comm]
    rw [hEq]
    exact D.keyFlip_card_le_m v
  have hsplit : (∏ j : Fin D.n, A j) =
      cSame ^ (Finset.univ.filter same).card *
        cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card := by
    calc
      (∏ j : Fin D.n, A j) =
          (Finset.univ.filter same).prod A *
            (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).prod A :=
        (Finset.prod_filter_mul_prod_filter_not Finset.univ same A).symm
      _ = cSame ^ (Finset.univ.filter same).card *
            cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card := by
        congr 1
        · calc
            (Finset.univ.filter same).prod A =
                (Finset.univ.filter same).prod (fun _ => cSame) := by
              apply Finset.prod_congr rfl
              intro j hj
              have hsame : same j := (Finset.mem_filter.mp hj).2
              simp [A, hsame]
            _ = cSame ^ (Finset.univ.filter same).card := by simp
        · calc
            (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).prod A =
                (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).prod (fun _ => cCross) := by
              apply Finset.prod_congr rfl
              intro j hj
              have hnsame : ¬ same j := (Finset.mem_filter.mp hj).2
              simp [A, hnsame]
            _ = cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card := by simp
  have hSameOne : 1 ≤ cSame := by norm_num [cSame]
  have hSameSmall : cSame ≤ Real.exp (21 / 1000 : ℝ) := by
    have hrat : cSame ≤ 1 + (21 / 1000 : ℝ) := by norm_num [cSame]
    exact hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (21 / 1000 : ℝ))
  have hnR : 1 ≤ (D.n : ℝ) := by exact_mod_cast hG.pos.1
  have hlog0 : 0 ≤ Real.log (D.n : ℝ) := Real.log_nonneg hnR
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCrossOne : 1 ≤ cCross := by
    dsimp [cCross]
    exact (Real.one_le_exp_iff).2 hB0
  have hsamePow : cSame ^ (Finset.univ.filter same).card ≤ cSame ^ D.n :=
    pow_le_pow_right₀ hSameOne hsameCard
  have hcrossPow : cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card ≤
      cCross ^ mC η₀ D.n := pow_le_pow_right₀ hCrossOne hcrossCard
  have hbasePow : cSame ^ D.n ≤ Real.exp (21 / 1000 : ℝ) ^ D.n :=
    pow_le_pow_left₀ (by positivity) hSameSmall D.n
  have hconstProd : cSame ^ (Finset.univ.filter same).card *
      cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card ≤
      Real.exp (21 / 1000 : ℝ) ^ D.n * cCross ^ mC η₀ D.n := by
    calc
      _ ≤ cSame ^ D.n * cCross ^ mC η₀ D.n :=
        mul_le_mul hsamePow hcrossPow (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
      _ ≤ Real.exp (21 / 1000 : ℝ) ^ D.n * cCross ^ mC η₀ D.n :=
        mul_le_mul_of_nonneg_right hbasePow (pow_nonneg (by positivity) _)
  have hexpNat (a : ℝ) (k : ℕ) : Real.exp a ^ k = Real.exp ((k : ℝ) * a) := by
    rw [← Real.exp_nat_mul]
  have hAprod : (∏ j : Fin D.n, A j) ≤
      Real.exp ((21 / 1000 : ℝ) * D.n + B * mC η₀ D.n) := by
    rw [hsplit]
    calc
      cSame ^ (Finset.univ.filter same).card *
          cCross ^ (Finset.univ.filter (fun j : Fin D.n => ¬ same j)).card ≤
        Real.exp (21 / 1000 : ℝ) ^ D.n * cCross ^ mC η₀ D.n := hconstProd
      _ = Real.exp ((21 / 1000 : ℝ) * D.n + B * mC η₀ D.n) := by
        dsimp [cCross]
        rw [hexpNat (21 / 1000 : ℝ) D.n, hexpNat B (mC η₀ D.n), ← Real.exp_add]
        congr 1 <;> ring
  have hsmall := hms D.n hn
  have hBbound : B * mC η₀ D.n ≤ (2 / 100 : ℝ) * ((D.n : ℝ) / 4) := by
    dsimp [B]
    calc
      (2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n * mC η₀ D.n =
          (2 / 100 : ℝ) * ((mC η₀ D.n : ℝ) * sC η₀ D.n * Real.log D.n) := by ring
      _ ≤ (2 / 100 : ℝ) * ((D.n : ℝ) / 4) := by
          exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hexponent : (21 / 1000 : ℝ) * D.n + B * mC η₀ D.n ≤ (3 / 100 : ℝ) * D.n := by
    have hsmall' : (2 / 100 : ℝ) * ((D.n : ℝ) / 4) = (1 / 200 : ℝ) * D.n := by ring
    nlinarith
  have hAexp : (∏ j : Fin D.n, A j) ≤ Real.exp ((3 / 100 : ℝ) * D.n) :=
    hAprod.trans (Real.exp_le_exp.mpr hexponent)
  calc
    D.starLik q W v z y ≤ (∏ j : Fin D.n, A j) * D.starRef q W v y := hlik
    _ ≤ Real.exp ((3 / 100 : ℝ) * D.n) * D.starRef q W v y :=
      mul_le_mul_of_nonneg_right hAexp (D.starRef_nonneg q W v y)

/-- L8.1j(iv) (08:377–378): each factor of `Q_v` is `p⁰` (with its validity) at a neighbour cell of the same key,
which reads only that cell's cross anchors, not the anchor of `v`'s cell; the other factors are constant. -/
theorem starRef_update (D : Ctx η₀ β p h) : D.StarRefUpdate := by
  unfold Ctx.StarRefUpdate
  intro q W v z
  funext y
  unfold Ctx.starRef
  apply Finset.prod_congr rfl
  intro j hj
  let e : D.CellT := cellOf η₀ v
  let c : D.CellT := cellOf η₀ (cubeFlip v j)
  by_cases hk : c.1 = e.1
  · have hcross : ∀ u : D.CrossSub c.1, (u.1, c.2) ≠ e := by
      intro u heq
      have hfst : u.1 = c.1 := by
        have h := congrArg Prod.fst heq
        simpa [e, c, hk] using h
      exact D.crossKey_ne_self c u hfst
    have hpv := D.presValid_update_eq q W e z c hcross
    have hp0 := D.p0_update_eq q W e z c hcross (y j)
    simp [Ctx.refRow, c, e, hk, hpv, hp0]
  · simp [Ctx.refRow, c, e, hk]

/-- L8.1j(v) (08:383–385): predictive failure does not depend on `z` (`M_v` integrates it, `Q_v` does not read it);
the joint probability of failure under the raw target anchor and product neighbour sampling is
`Σ_y M_v(y) 1[fail] ≤ e^{-.04n} Σ_y Q_v(y) ≤ e^{-.04n}` (Lemma 3.7, first assertion). -/
theorem alarm_mean (D : Ctx η₀ β p h) (hU : D.StarRefUpdate) : D.AlarmMean := by
  classical
  intro q W a
  let v : CubeVertex D.n := a.1
  let t : D.CellT := cellOf η₀ v
  have hmarg (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      D.starMarg q (Function.update W t z) v y = D.starMarg q W v y := by
    exact D.starMarg_update_eq q W v z y
  have href (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      D.starRef q (Function.update W t z) v y = D.starRef q W v y := by
    exact congrFun (hU q W v z) y
  have hfail (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      D.PredFail q (Function.update W t z) v y = D.PredFail q W v y := by
    unfold Ctx.PredFail
    rw [hmarg, href]
  have hrate (z : Fin D.N) :
      D.alarmRate q (Function.update W t z) v =
        ∑ y : Fin D.n → Fin D.N,
          D.starLik q W v z y * (if D.PredFail q W v y then 1 else 0) := by
    unfold Ctx.alarmRate
    apply Finset.sum_congr rfl
    intro y hy
    rw [hfail]
    rfl
  calc
    ∑ z, (D.Usel q t).w z * D.alarmRate q (Function.update W t z) v =
        ∑ z, (D.Usel q t).w z *
          ∑ y : Fin D.n → Fin D.N,
            D.starLik q W v z y * (if D.PredFail q W v y then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hrate]
    _ = ∑ y : Fin D.n → Fin D.N,
          (∑ z, (D.Usel q t).w z * D.starLik q W v z y) *
            (if D.PredFail q W v y then 1 else 0) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          calc
            (∑ z, (D.Usel q t).w z *
                (D.starLik q W v z y * (if D.PredFail q W v y then 1 else 0))) =
                ∑ z, ((D.Usel q t).w z * D.starLik q W v z y) *
                  (if D.PredFail q W v y then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
            _ = (∑ z, (D.Usel q t).w z * D.starLik q W v z y) *
                  (if D.PredFail q W v y then 1 else 0) := by rw [Finset.sum_mul]
    _ = ∑ y : Fin D.n → Fin D.N,
          D.starMarg q W v y * (if D.PredFail q W v y then 1 else 0) := by
          rfl
    _ ≤ ∑ y : Fin D.n → Fin D.N,
          Real.exp (-(4 / 100 : ℝ) * D.n) * D.starRef q W v y := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases hf : D.PredFail q W v y
          · unfold Ctx.PredFail at hf
            rcases hf with hmzero | hm
            · have hpf : D.PredFail q W v y := by
                unfold Ctx.PredFail
                exact Or.inl hmzero
              simpa [hpf, hmzero] using
                mul_nonneg (Real.exp_pos _).le (D.starRef_nonneg q W v y)
            · have hpf : D.PredFail q W v y := by
                unfold Ctx.PredFail
                exact Or.inr hm
              rw [if_pos hpf]
              simpa using le_of_lt hm
          · simpa [hf] using
              mul_nonneg (Real.exp_pos _).le (D.starRef_nonneg q W v y)
    _ = Real.exp (-(4 / 100 : ℝ) * D.n) *
          ∑ y : Fin D.n → Fin D.N, D.starRef q W v y := by
          rw [Finset.mul_sum]
    _ ≤ Real.exp (-(4 / 100 : ℝ) * D.n) * 1 :=
          mul_le_mul_of_nonneg_left (D.starRef_sum_le_one q W v) (Real.exp_pos _).le
    _ = Real.exp (-(4 / 100 : ℝ) * D.n) := by ring

/-- L8.1j(vi) (08:385–389): Markov bounds by `e^{-.02n}` the anchor probability of one vertex's alarm; the alarm
rate of an even vertex depends on the vertex only through its neighbour-cell multiplicity profile (the number of
special-bit neighbours in each cross bin or the own bin, at most `(n+1)^{2s+1}` profiles per cell), so the
grouped alarm of a cell has probability at most `(n+1)^{2s+1} e^{-.02n}`. -/
theorem alarm_prob (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) (hA : D.AlarmMean) : D.AlarmProb := by
  classical
  intro q W c
  let profiles := Lane_q_s08_anchor.cellRoleProfiles D c
  let Profile := {P : Lane_q_s08_anchor.KeyProfileDomain D c.1 → Fin (D.n + 1) //
    P ∈ profiles}
  have repExists (P : Profile) :
      ∃ a : EvenRole D.n, cellOf η₀ a.1 = c ∧
        Lane_q_s08_anchor.keyProfile D a.1 c.1 = P.1 := by
    rcases Finset.mem_image.mp P.2 with ⟨a, ha, hprofile⟩
    exact ⟨a, (Finset.mem_filter.mp ha).2, hprofile⟩
  let rep : Profile → EvenRole D.n := fun P => Classical.choose (repExists P)
  have repSpec (P : Profile) :
      cellOf η₀ (rep P).1 = c ∧
        Lane_q_s08_anchor.keyProfile D (rep P).1 c.1 = P.1 :=
    Classical.choose_spec (repExists P)
  let threshold : ℝ := Real.exp (-(2 / 100 : ℝ) * D.n)
  have hcover (z : Fin D.N) :
      (if D.Alarm q (Function.update W c z) c then (1 : ℝ) else 0) ≤
        ∑ P : Profile,
          (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0) := by
    by_cases hbad : D.Alarm q (Function.update W c z) c
    · rcases hbad with ⟨a, hac, hrate⟩
      have hbad' : D.Alarm q (Function.update W c z) c := ⟨a, hac, hrate⟩
      have hprofileMem : Lane_q_s08_anchor.keyProfile D a.1 c.1 ∈ profiles := by
        apply Finset.mem_image.mpr
        refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac⟩, rfl⟩
      let P : Profile := ⟨Lane_q_s08_anchor.keyProfile D a.1 c.1, hprofileMem⟩
      have hprofile : Lane_q_s08_anchor.keyProfile D a.1 c.1 =
          Lane_q_s08_anchor.keyProfile D (rep P).1 c.1 := by
        calc
          Lane_q_s08_anchor.keyProfile D a.1 c.1 = P.1 := rfl
          _ = Lane_q_s08_anchor.keyProfile D (rep P).1 c.1 := (repSpec P).2.symm
      have hrateEq := Lane_q_s08_anchor.alarmRate_eq_of_same_keyProfile
        D hG q (Function.update W c z) a (rep P) c hac (repSpec P).1 hprofile
      have hthreshold : threshold < D.alarmRate q (Function.update W c z) (rep P).1 := by
        simpa [threshold, hrateEq] using hrate
      have hsingle := Finset.univ.single_le_sum
        (f := fun P : Profile =>
          if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0)
        (fun P hP => by split_ifs <;> norm_num)
        (Finset.mem_univ P)
      have hsingle' : 1 ≤
          ∑ P : Profile,
            (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0) := by
        simpa [hthreshold] using hsingle
      have hleft :
          (if D.Alarm q (Function.update W c z) c then (1 : ℝ) else 0) = 1 := if_pos hbad'
      rw [hleft]
      exact hsingle'
    · simp only [hbad, ↓reduceIte]
      apply Finset.sum_nonneg
      intro P hP
      split_ifs <;> norm_num
  have hprofiles := Lane_q_s08_anchor.cellRoleProfiles_card_le D hG c
  have hprofileCard : Fintype.card Profile ≤ (D.n + 1) ^ (2 * sC η₀ D.n + 1) := by
    have hcard : Fintype.card Profile = profiles.card := by
      simp [Profile, profiles, Fintype.card_subtype]
    rw [hcard]
    exact hprofiles
  calc
    (∑ z, (D.Usel q c).w z *
          (if D.Alarm q (Function.update W c z) c then 1 else 0)) ≤
        ∑ z, (D.Usel q c).w z *
          ∑ P : Profile,
            (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_left (hcover z) ((D.Usel q c).nonneg z)
    _ = ∑ P : Profile, ∑ z, (D.Usel q c).w z *
          (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then 1 else 0) := by
          calc
            (∑ z, (D.Usel q c).w z *
                ∑ P : Profile,
                  (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0)) =
                ∑ z, ∑ P : Profile, (D.Usel q c).w z *
                  (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    rw [Finset.mul_sum]
            _ = ∑ P : Profile, ∑ z, (D.Usel q c).w z *
                  (if threshold < D.alarmRate q (Function.update W c z) (rep P).1 then (1 : ℝ) else 0) := by
                    rw [Finset.sum_comm]
    _ ≤ ∑ P : Profile, threshold := by
          apply Finset.sum_le_sum
          intro P hP
          simpa [threshold] using
            (Lane_q_s08_anchor.alarmRate_tail D hA q W (rep P) c (repSpec P).1)
    _ = (Fintype.card Profile : ℝ) * threshold := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) * threshold := by
          have hcard : (Fintype.card Profile : ℝ) ≤
              ((D.n + 1) ^ (2 * sC η₀ D.n + 1) : ℕ) := by exact_mod_cast hprofileCard
          have hcard' : (Fintype.card Profile : ℝ) ≤
              ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) := by
            norm_cast at hcard ⊢
          exact mul_le_mul_of_nonneg_right hcard' (Real.exp_pos _).le
    _ = ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
          Real.exp (-(2 / 100 : ℝ) * D.n) := by rfl

/-- L8.1j(vii) (08:387): the denominator and hit tests of `c` read anchors within cell distance one, an alarm at `c`
reads the rows of the neighbour cells of its vertices (cell distance one, by the edge cover), which read anchors
within distance one of those. -/
theorem cellBad_scope (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) : D.CellBadScope := by
  unfold Ctx.CellBadScope
  intro q c W W' hW
  exact D.cellBad_eq_of_ball2 hG q W W' c hW

set_option maxHeartbeats 1000000 in
/-- L8.1j(viii) (08:387–393): on a successful history the grouped cell events have raw probability at most
`q_A ≤ ε₀^{1/4} + 50(n+1)Δ/(1-Δ) + (n+1)^{2s+1}e^{-.02n} ≤ e^{-n^{c_A}}`, scopes the radius-two cell balls, and
dependency degree at most `(2s + (n-m) + 1)^4`; `x_A = 2q_A` meets the local-lemma condition. -/
theorem anchor_lll (hη₀ : 0 < η₀) (hp : 0 < p) (hh : 1 ≤ h) :
    ∃ cA > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.DenFailProb → D.HitFailProb → D.AlarmProb → D.CellBadScope →
      ∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA)) := by
  obtain ⟨cA, hcA, n₀, hAsymptotic⟩ :=
    Lane_q_s08_anchor.anchorLLL_asymptotic η₀ p h hη₀ hp hh
  refine ⟨cA, hcA, n₀, ?_⟩
  intro D hn hG hDen hHit hAlarm hScope q hGood
  let Delta : ℕ := (2 * sC η₀ D.n + dC η₀ D.n + 1) ^ 4
  let x : ℝ := 2 * Real.exp (-((D.n : ℝ) ^ cA))
  have hAsy := hAsymptotic D hn hG
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    nlinarith [hAsy.2.2]
  have hscope : ∀ c, FinProb.DependsOn (fun W : D.Anch => D.CellBad q W c) (cellBall c 2) :=
    hScope q
  have hdegree : ∀ c,
      (Finset.univ.filter fun e : D.CellT =>
        e ≠ c ∧ ¬ Disjoint (cellBall c 2) (cellBall e 2)).card ≤ Delta := by
    intro c
    let Dep := Finset.univ.filter fun e : D.CellT =>
      e ≠ c ∧ ¬ Disjoint (cellBall c 2) (cellBall e 2)
    have hsubset : Dep ⊆ cellBall c 4 := by
      intro e he
      rcases Finset.mem_filter.mp he with ⟨_, ⟨_, hdisj⟩⟩
      have hmeet : ∃ t, t ∈ cellBall c 2 ∧ t ∈ cellBall e 2 := by
        by_contra hnone
        apply hdisj
        apply Finset.disjoint_left.mpr
        intro t htc hte
        exact hnone ⟨t, htc, hte⟩
      rcases hmeet with ⟨t, htc, hte⟩
      have hct : cellDist c t ≤ 2 := (Finset.mem_filter.mp htc).2
      have het : cellDist e t ≤ 2 := (Finset.mem_filter.mp hte).2
      have hsym : cellDist t e = cellDist e t := by
        have hk : keyDist t.1 e.1 = keyDist e.1 t.1 := by
          unfold keyDist
          apply Finset.sum_congr rfl
          intro r hr
          exact Nat.dist_comm _ _
        unfold cellDist
        rw [hk, _root_.hammingDist_comm]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      calc
        cellDist c e ≤ cellDist c t + cellDist t e := D.cellDist_triangle c t e
        _ ≤ 2 + 2 := Nat.add_le_add hct (by rw [hsym]; exact het)
        _ = 4 := by norm_num
    have hcard : Dep.card ≤ (cellBall c 4).card := Finset.card_le_card hsubset
    have hball : (cellBall c 4).card ≤ Delta := by
      sorry
    exact hcard.trans hball
  have hprob : ∀ c, (FinProb.pi (fun c : D.CellT => D.Usel q c)).pr
      (fun W => D.CellBad q W c) ≤ x * (1 - x) ^ Delta := by
    intro c
    let P : FinProb D.Anch := FinProb.pi fun c : D.CellT => D.Usel q c
    have hDenRaw : P.pr (fun W => D.DenFail q W c) ≤ Real.sqrt (Real.sqrt D.eps0) := by
      simpa [P, Ctx.rawAnchors] using hDen q hGood c
    have hHitRaw : P.pr (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) ≤
        50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) := by
      simpa [P, Ctx.rawAnchors] using hHit q hGood c
    have hAlarmRaw : P.pr (fun W => D.Alarm q W c) ≤
        ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
          Real.exp (-(2 / 100 : ℝ) * D.n) := by
      apply Lane_q_s08_anchor.pi_pr_le_of_update_coordinate_bound
        (fun c : D.CellT => D.Usel q c) c (fun W => D.Alarm q W c)
      intro W
      exact hAlarm q W c
    have heq : (fun W => D.CellBad q W c) =
        (fun W => D.DenFail q W c ∨
          (¬ D.DenFail q W c ∧ D.HitFail q W c) ∨ D.Alarm q W c) := by
      funext W
      apply propext
      simp [Ctx.CellBad]
      tauto
    have hbad : P.pr (fun W => D.CellBad q W c) ≤
        Real.sqrt (Real.sqrt D.eps0) +
          50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) +
          ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
            Real.exp (-(2 / 100 : ℝ) * D.n) := by
      rw [heq]
      have hHitAlarm : P.pr
          (fun W => (¬ D.DenFail q W c ∧ D.HitFail q W c) ∨ D.Alarm q W c) ≤
            50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) +
              ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
                Real.exp (-(2 / 100 : ℝ) * D.n) := by
        calc
          P.pr (fun W => (¬ D.DenFail q W c ∧ D.HitFail q W c) ∨ D.Alarm q W c) ≤
              P.pr (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) +
                P.pr (fun W => D.Alarm q W c) := FinProb.pr_union P _ _
          _ ≤ _ := add_le_add hHitRaw hAlarmRaw
      calc
        P.pr (fun W => D.DenFail q W c ∨
            ((¬ D.DenFail q W c ∧ D.HitFail q W c) ∨ D.Alarm q W c)) ≤
            P.pr (fun W => D.DenFail q W c) +
              P.pr (fun W => (¬ D.DenFail q W c ∧ D.HitFail q W c) ∨ D.Alarm q W c) :=
                FinProb.pr_union P _ _
        _ ≤ Real.sqrt (Real.sqrt D.eps0) +
              (50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) +
                ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
                  Real.exp (-(2 / 100 : ℝ) * D.n)) := add_le_add hDenRaw hHitAlarm
        _ = Real.sqrt (Real.sqrt D.eps0) +
              50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) +
                ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) *
                  Real.exp (-(2 / 100 : ℝ) * D.n) := by ring
    have hprobSmall : P.pr (fun W => D.CellBad q W c) ≤ Real.exp (-((D.n : ℝ) ^ cA)) :=
      hbad.trans hAsy.1
    have hcharge : Real.exp (-((D.n : ℝ) ^ cA)) ≤ x * (1 - x) ^ Delta := by
      have hbern := one_add_mul_le_pow (a := -x) (by linarith [hx1]) Delta
      have hdx : (Delta : ℝ) * x ≤ 1 / 2 := by
        simpa [Delta, x, Nat.cast_pow, Nat.cast_add, Nat.cast_mul] using hAsy.2.1
      have hbern' : 1 - (Delta : ℝ) * x ≤ (1 - x) ^ Delta := by
        simpa [sub_eq_add_neg, mul_neg] using hbern
      have hpow : (1 : ℝ) / 2 ≤ (1 - x) ^ Delta := by
        nlinarith [hbern', hdx]
      dsimp [x]
      nlinarith [Real.exp_pos (-((D.n : ℝ) ^ cA)), hpow]
    exact hprobSmall.trans hcharge
  change LLLInput (fun c : D.CellT => D.Usel q c)
    (fun c W => D.CellBad q W c) (fun c => cellBall c 2) x Delta
  exact {
    x_nonneg := hx0
    x_lt_one := hx1
    scope := hscope
    degree := by simpa [Delta] using hdegree
    prob := hprob
  }

end Nodes

end HypercubeRamsey.S08
