import HypercubeRamsey.S08.L81.EvenNodes

/-!
# Lemma 8.1 assembled

Source: `sections/08-…tex`, lines 8–455.  The stage nodes give the tails of every failure; the averaging node
`realization_of` turns them into one realization with an injective odd assignment avoiding predictive failure and
even column sums at most one (08:454); its posterior even rows are Hall data (`hall_of_realization`, F-HallEmbed).
`l81_core` threads all nodes at the fixed tuple length `h = 10⁸` (`δh/4 > 2 · 25`, 08:206).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The fixed tuple length `h = 10⁸` (08:23, 206). -/
def hFix : ℕ := 10 ^ 8

/-- The final constant `C₀`: large enough for the odd column bound `10⁸ · 4(oddM K + 1)` and the even column bound
`16(loadC K + 1)`. -/
def C0 (K : ℝ) : ℝ := max (16 * (loadC K + 1)) ((10 : ℝ) ^ 8 * (4 * (oddM K + 1))) + 1

/-- The tails of the six failure events sum to less than one for large `n`. -/
theorem tails_small :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 3 * Real.exp (-(n : ℝ)) + 4 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1 := by
  sorry

section Nodes

variable (η₀ β p : ℝ) (h : ℕ)

/-- L8.1, averaging (08:366, 393, 422, 425, 454): the pre-anchor history is in the support of its law with
probability one (hidden events avoided, tags of positive centre probability); selection fails, or succeeds with a
load failure, with probability at most `a₁ + a₂ + a₃ + a₄`; on success the anchor law is supported on avoidance
(positive mass), and odd loads fail with probability at most `a₅`; at successful prehistories clock laws exist, and
at successful histories with the load bound any clock family has even loads above one with probability at most
`a₆`.  As the tails sum to less than one, some realization succeeds throughout. -/
theorem realization_of (D : Ctx η₀ β p h) (CL a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
    (hpos : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g))
    (h1 : D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) ≤ a₁)
    (h2 : D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ ¬ D.FewBad q.1.1 q.1.2 q.2.1.1) ≤ a₂)
    (h3 : D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧
      ¬ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2) ≤ a₃)
    (h4 : D.preLaw.pr (fun q => D.SelOK q ∧ ¬ D.LoadOK CL q) ≤ a₄)
    (h5 : D.stagedLaw.pr (fun z => D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y) ≤ a₅)
    (h6 : ∀ q : D.Pre, D.Good q → 0 < (D.rawAnchors q).pr (fun W => ∀ c, ¬ D.CellBad q W c))
    (h7 : ∀ (q : D.Pre) (W : D.Anch), D.Good q → D.GoodPre q W → ∃ J, D.ClockOK q W J)
    (h8 : ∀ q : D.Pre, D.Good q → D.LoadOK CL q →
      ∀ J : D.Anch → FinProb (OddRole D.n → Fin D.N), (∀ W, D.GoodPre q W → D.ClockOK q W (J W)) →
        ∑ W, (D.anchorLaw q).w W *
            (if D.GoodPre q W then (J W).pr (fun f => ∃ x, 1 < D.evenCol q W f x) else 0) ≤ a₆)
    (ha₆ : 0 ≤ a₆) (hsum : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ < 1) :
    ∃ (q : D.Pre) (W : D.Anch) (f : OddRole D.n → Fin D.N), D.Good q ∧ (∀ c, ¬ D.CellBad q W c) ∧
      Function.Injective f ∧ (∀ a : EvenRole D.n, ¬ D.PredFail q W a.1 (nbrLabels f a)) ∧
      ∀ x, D.evenCol q W f x ≤ 1 := by
  sorry

/-- F-HallEmbed input from a good realization (08:454): the posterior even rows are probability laws on the common
neighbourhoods of the injective odd labels, with column sums at most one. -/
theorem hall_of_realization (D : Ctx η₀ β p h) (hlaw : D.EvenRowLaw) (q : D.Pre) (W : D.Anch)
    (f : OddRole D.n → Fin D.N) (hinj : Function.Injective f)
    (hpf : ∀ a : EvenRole D.n, ¬ D.PredFail q W a.1 (nbrLabels f a))
    (hcol : ∀ x, D.evenCol q W f x ≤ 1) : CubeAt D.n D.N D.E :=
  cubeAt_of_rows D.E D.G f hinj (fun a x => D.evenRow q W f a x)
    (fun a x => (hlaw q W f a (hpf a)).1 x) (fun a => (hlaw q W f a (hpf a)).2.1)
    (fun a x hx => (hlaw q W f a (hpf a)).2.2 x hx) hcol

end Nodes

theorem C0_odd (K : ℝ) : (10 : ℝ) ^ 8 * (4 * (oddM K + 1)) ≤ C0 K := by
  unfold C0; linarith [le_max_right (16 * (loadC K + 1)) ((10 : ℝ) ^ 8 * (4 * (oddM K + 1)))]

theorem C0_even (K : ℝ) : 16 * (loadC K + 1) ≤ C0 K := by
  unfold C0; linarith [le_max_left (16 * (loadC K + 1)) ((10 : ℝ) ^ 8 * (4 * (oddM K + 1)))]

theorem C0_one (K : ℝ) (hK : 0 < K) : 1 ≤ C0 K := by
  have h0 : 0 ≤ 16 * (loadC K + 1) := by unfold loadC compC; positivity
  have := C0_even K
  unfold C0 at this ⊢; linarith [le_max_left (16 * (loadC K + 1)) ((10 : ℝ) ^ 8 * (4 * (oddM K + 1)))]

/-- Lemma 8.1 at one dimension (08:8–455), assembled from the nodes. -/
theorem l81_core (η₀ γ β p K : ℝ) (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ₀ : 0 < β)
    (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, ∀ E : Fin N → Fin N → Prop, ∀ X Y : Finset (Fin N), ∀ G : Colour,
      ∀ M : TagMix N, LargeAt n₀ C₀ n N → Input η₀ γ β p K n N E X Y G M → CubeAt n N E := by
  have hh1 : 1 ≤ hFix := by unfold hFix; norm_num
  have hh10 : 10 ≤ hFix := by unfold hFix; norm_num
  have hh8 : 10 ^ 8 ≤ hFix := le_refl _
  have hoddM : 0 ≤ oddM K := by unfold oddM; positivity
  have hloadC : 0 ≤ loadC K := by unfold loadC compC; positivity
  -- Step 1
  obtain ⟨nG, hgrid⟩ := grid_facts η₀ hη₀
  obtain ⟨nT, htrim⟩ := trim_std η₀ γ β p K hη₀ hγ₀ hγ₁ hβ₀ hβτ hp hK hFix
  obtain ⟨cR, hcR, nR, hres⟩ := res_near_small η₀ hη₀
  -- Steps 2 and 4
  obtain ⟨c', hc', nC, hgate⟩ := gate_tail η₀ γ β p K hFix hη₀ hβ₀ hβτ hp hK
  obtain ⟨nPC, hpostcap⟩ := post_cap η₀ γ β p K hFix hη₀ hβ₀ hβτ hh1
  -- Step 5
  obtain ⟨cH, hcH, nH, hlll⟩ := hidden_lll η₀ β p hFix c' hc' hη₀ hh1
  obtain ⟨nLC, hlist⟩ := list_count η₀ β p hFix hη₀
  obtain ⟨nLeg, hlegal⟩ := legal_of_counts η₀ β p hFix hη₀
  obtain ⟨nSC, hselc⟩ := sel_conseq η₀ β p hFix hη₀
  obtain ⟨nPos, hpost⟩ := pos_tail η₀ β p hFix hη₀
  obtain ⟨nFB, hfew⟩ := few_bad_tail η₀ β p hFix hη₀ hh8
  obtain ⟨nHT, hheight⟩ := height_tail η₀ β p hFix hη₀ (hd_admissible η₀ hη₀)
  -- Steps 6–8
  obtain ⟨nSP, hselpost⟩ := sel_post_cap η₀ β p hFix hh1
  obtain ⟨nPL, hp0law⟩ := p0_law η₀ β p hFix hh10
  obtain ⟨nRM, hrawmean⟩ := p0_raw_mean η₀ γ β p K hFix hη₀ hK hh8
  obtain ⟨nPR, hprow⟩ := prow_facts η₀ β p hFix
  -- Step 9
  obtain ⟨nSM, hselmean⟩ := select_mean η₀ β p hFix hη₀ hp (hd_admissible η₀ hη₀)
  obtain ⟨nBM, hbmean⟩ := bcomp_mean η₀ γ β p K hFix hη₀ hK
  obtain ⟨nCT, hcomp⟩ := comp_tail η₀ γ β p K hFix cH hcH hη₀ hβτ hK
  obtain ⟨nCe, hcenter⟩ := center_tail η₀ γ β p K hFix cR hcR hη₀ hγ₁ hK
  -- Step 10
  obtain ⟨nSL, hstarlik⟩ := starLik_bound η₀ β p hFix hη₀
  obtain ⟨cA, hcA, nA, hanchor⟩ := anchor_lll η₀ β p hFix hη₀ hp hh1
  -- Step 11
  obtain ⟨nOA, hoddA⟩ := odd_anchor_step η₀ β p hFix cA hcA hη₀
  obtain ⟨nOH, hoddH⟩ := odd_hidden_step η₀ β p K hFix cH hcH hη₀ hK
  obtain ⟨nOT, hoddT⟩ := odd_tail η₀ γ β p K hFix (oddM K) hoddM hη₀
  -- Step 12
  obtain ⟨nCR, hclock⟩ := clock_rows η₀ β p hFix hη₀
  obtain ⟨nEC, hecap⟩ := evenRow_cap η₀ γ β p K hFix hη₀ hγ₁ hp
  obtain ⟨nEA, heint⟩ := even_anchor_integral η₀ β p hFix cA hcA hη₀
  obtain ⟨nET, hetail⟩ := even_tail η₀ β p hFix (loadC K) hloadC hη₀
  obtain ⟨nTS, htails⟩ := tails_small
  refine ⟨nG + nT + nR + nC + nPC + nH + nLC + nLeg + nSC + nPos + nFB + nHT + nSP + nPL + nRM + nPR +
    nSM + nBM + nCT + nCe + nSL + nA + nOA + nOH + nOT + nCR + nEC + nEA + nET + nTS, C0 K, ?_⟩
  intro n N E X Y G M hL hI
  obtain ⟨hn₀, hC₀, hNle⟩ := hL
  let D : Ctx η₀ β p hFix := trimCtx η₀ β p hFix n N E G X M
  have hS : Std D γ K X Y (retained η₀ n E G X M) := htrim n (by omega) N E X Y G M hI
  have hGF : GridFacts η₀ D.n := hgrid n (by omega)
  have hn1 : 1 ≤ D.n := hGF.pos.1
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  have hNodd : (10 : ℝ) ^ 8 * (4 * (oddM K + 1)) * 2 ^ D.n ≤ D.N :=
    le_trans (mul_le_mul_of_nonneg_right (C0_odd K) h2pos.le) hC₀
  have hNeven : 16 * (loadC K + 1) * 2 ^ D.n ≤ D.N :=
    le_trans (mul_le_mul_of_nonneg_right (C0_even K) h2pos.le) hC₀
  have hNtwo : (2 : ℝ) ^ D.n ≤ D.N := by
    have := mul_le_mul_of_nonneg_right (C0_one K hK) h2pos.le
    rw [one_mul] at this
    exact le_trans this hC₀
  -- Steps 2 and 4
  have hDB : D.DensityBounds := density_bounds _ _ _ _ hp D hn1
  have hDT : D.DenTail := den_tail _ _ _ _ D hDB
  have hGT : D.GateTail c' := hgate D (by show nC ≤ n; omega) X Y _ hS hGF
  have hFS : D.FSupport := f_support _ _ _ _ D hn1
  have hPC : D.PostCap := hpostcap D (by show nPC ≤ n; omega) X Y _ hS hGF hDB
  -- Step 5
  have hHL : D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) := hlll D (by show nH ≤ n; omega) hGF hGT hDT
  have hposH : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g) := (cond_product_bound _ _ _ _ _ hHL).1
  have hLC : D.ListCount := hlist D (by show nLC ≤ n; omega) hGF
  have hLeg : D.LegalOfCounts := hlegal D (by show nLeg ≤ n; omega) hGF
  have hSC : D.SelConseq := hselc D (by show nSC ≤ n; omega) hGF hLeg
  have hSLoc : D.SelLocal := sel_local _ _ _ _ D
  -- Steps 6–8
  have hGLF : D.GselLeF := gsel_le_f _ _ _ _ D
  have hSPC : D.SelPostCap := hselpost D (by show nSP ≤ n; omega) hPC hGLF
  have hP0L : D.P0Law := hp0law D (by show nPL ≤ n; omega) hGF hSPC
  have hP0S : D.P0Support := p0_support _ _ _ _ D hFS hGLF
  have hP0M : D.P0RawMean K := hrawmean D (by show nRM ≤ n; omega) X Y _ hS hGF hDB hLC hP0L hGLF
  have hP0Loc : D.P0Local := p0_local _ _ _ _ D hSLoc
  have hHT : D.HitTail := hit_tail _ _ _ _ D hn1 hFS hGLF hP0L
  have hPR : D.PRowFacts := hprow D (by show nPR ≤ n; omega) hP0L hP0S
  -- Step 9
  have hSM : D.SelectMean := hselmean D (by show nSM ≤ n; omega) hGF
  have hBM : D.BcompMean K := hbmean D (by show nBM ≤ n; omega) X Y _ hS hGF
  have hCT := hcomp D (by show nCT ≤ n; omega) X Y _ hS hGF cond_product_bound hHL hBM
  have hCe := hcenter D (by show nCe ≤ n; omega) X Y _ hS hGF (hres n (by omega)) hSLoc hSM hSC
  have hLoad := load_tail _ _ _ _ D (compC K) (loadC K) _ _ (by positivity) hposH hCT hCe
  -- Step 10
  have hDF : D.DenFailProb := den_fail_prob _ _ _ _ D hSC
  have hHF : D.HitFailProb := hit_fail_prob _ _ _ _ D hSC hHT
  have hSLB : D.StarLikBound := hstarlik D (by show nSL ≤ n; omega) hGF hPR
  have hSRU : D.StarRefUpdate := starRef_update _ _ _ _ D
  have hAM : D.AlarmMean := alarm_mean _ _ _ _ D hSRU
  have hAP : D.AlarmProb := alarm_prob _ _ _ _ D hGF hAM
  have hCBS : D.CellBadScope := cellBad_scope _ _ _ _ D hGF
  have hALL := hanchor D (by show nA ≤ n; omega) hGF hDF hHF hAP hCBS
  -- Step 11
  have hOA : D.OddAnchorStep := hoddA D (by show nOA ≤ n; omega) hGF cond_product_bound hALL hP0Loc hPR
  have hOH : D.OddHiddenStep (33 * K + 1) :=
    hoddH D (by show nOH ≤ n; omega) hGF cond_product_bound hHL hP0Loc hP0M hP0L
  have hOM : D.OddMoment (oddM K) := odd_moment _ _ _ _ D (33 * K + 1) (by positivity) hOA hOH hPR
  have hOT := hoddT D (by show nOT ≤ n; omega) X Y _ hS hGF hNodd hPR hOM
  -- Step 12
  have hECap : D.EvenRowCap := hecap D (by show nEC ≤ n; omega) X Y _ hS hGF hSLB hSC
  have hSCan : D.StarCancel := star_cancel _ _ _ _ D hSRU hPR
  have hERL : D.EvenRowLaw := evenRow_law _ _ _ _ D hGF hPR
  -- Averaging and Hall
  have htl : 3 * Real.exp (-(D.n : ℝ)) + 4 * ((D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n) < 1 :=
    htails n (by omega)
  obtain ⟨q, W, f, _hq, _hW, hf, hpf, hcol⟩ := realization_of _ _ _ _ D (loadC K) _ _ _ _ _ _ hposH
    (hpost D (by show nPos ≤ n; omega) hGF)
    (hfew D (by show nFB ≤ n; omega) hGF hLC (bad_list_prob _ _ _ _ D) hposH)
    (hheight D (by show nHT ≤ n; omega) hGF hLeg)
    hLoad hOT
    (fun q hq => (cond_product_bound _ _ _ _ _ (hALL q hq)).1)
    (fun q W hq hW => hclock D (by show nCR ≤ n; omega) hGF hNtwo hNle hSC hPR q W hq hW)
    (fun q hq hLq J hJ => hetail D (by show nET ≤ n; omega) hGF hNle hNeven hECap hPR hSC q hq hLq J hJ
      (even_moment _ _ _ _ D q J hPR (clock_factor _ _ _ _ D q J hJ hPR)
        (heint D (by show nEA ≤ n; omega) hGF cond_product_bound hSCan hPR q hq (hALL q hq))))
    (by positivity) (by linarith)
  exact hall_of_realization _ _ _ _ D hERL q W f hf hpf hcol

end HypercubeRamsey.S08
