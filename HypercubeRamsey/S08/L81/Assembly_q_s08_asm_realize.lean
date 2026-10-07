import HypercubeRamsey.S08.L81.Assembly_q_s08_asm

namespace HypercubeRamsey.Lane_q_s08_asm

open Classical HypercubeRamsey.S08 OAI.HypercubeRamsey
open scoped BigOperators

theorem pre_support {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (hpos : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g))
    (q : D.Pre) (hq : D.preLaw.w q ≠ 0) : D.Supp q := by
  classical
  rcases q with ⟨⟨Θ, P⟩, ⟨⟨t, A⟩, T⟩⟩
  have hweight : (D.hiddenLaw.w Θ * D.posLaw.w P) * (D.rawTAT Θ).w ((t, A), T) ≠ 0 := by
    simpa [Ctx.preLaw, FinProb.bind] using hq
  have hhidden : D.hiddenLaw.w Θ ≠ 0 := by
    intro hz
    apply hweight
    simp [hz]
  have htat : (D.rawTAT Θ).w ((t, A), T) ≠ 0 := by
    intro hz
    apply hweight
    simp [hz]
  have havoid : ∀ g, ¬ D.HBad Θ g := by
    intro g hbad
    have hnot : ¬ (∀ g, ¬ D.HBad Θ g) := by
      intro hgood
      exact hgood g hbad
    have hz : D.hiddenLaw.w Θ = 0 := by
      simp [Ctx.hiddenLaw, condOr, hpos, FinProb.cond, hnot]
    exact hhidden hz
  have htag : (D.tagLawAll Θ).w t ≠ 0 := by
    intro hz
    apply htat
    simp [Ctx.rawTAT, FinProb.prod, hz]
  have htagProd : (∏ g : D.KeyT, ∏ ℓ : D.Loc, (D.tilt Θ g).w (t g ℓ)) ≠ 0 := by
    simpa [Ctx.tagLawAll, FinProb.pi] using htag
  have htags : ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ) := by
    intro g ℓ
    have hg : (∏ ℓ : D.Loc, (D.tilt Θ g).w (t g ℓ)) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp htagProd) g (Finset.mem_univ _)
    have hgl : (D.tilt Θ g).w (t g ℓ) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hg) ℓ (Finset.mem_univ _)
    exact lt_of_le_of_ne ((D.tilt Θ g).nonneg _) (Ne.symm hgl)
  change (∀ g, ¬ D.HBad Θ g) ∧ ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ)
  exact ⟨havoid, htags⟩

theorem staged_support {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (W : D.Anch) (hz : D.stagedLaw.w (q, W) ≠ 0) :
    D.preLaw.w q ≠ 0 ∧ (D.anchorLaw q).w W ≠ 0 := by
  have hprod : D.preLaw.w q * (D.anchorLaw q).w W ≠ 0 := by
    simpa [Ctx.stagedLaw, FinProb.bind] using hz
  constructor
  · intro hzero
    apply hprod
    simp [hzero]
  · intro hzero
    apply hprod
    simp [hzero]

theorem condOr_support {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (hmass : 0 < P.pr A) (ω : Ω) (hω : (condOr P A).w ω ≠ 0) : A ω := by
  by_contra hA
  apply hω
  simp [condOr, hmass, FinProb.cond, hA]

theorem anchor_avoids {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (hmass : 0 < (D.rawAnchors q).pr (fun W => ∀ c, ¬ D.CellBad q W c))
    (W : D.Anch) (hW : (D.anchorLaw q).w W ≠ 0) : ∀ c, ¬ D.CellBad q W c := by
  have havoid := condOr_support (D.rawAnchors q) (fun W => ∀ c, ¬ D.CellBad q W c) hmass W
  simpa [Ctx.anchorLaw] using havoid hW

theorem odd_bad_of_not_goodPre {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (W : D.Anch) (hcell : ∀ c, ¬ D.CellBad q W c)
    (hpre : ¬ D.GoodPre q W) : ∃ y, (1e-8 : ℝ) < D.oddCol q W y := by
  by_contra hnone
  have hcol : ∀ y, D.oddCol q W y ≤ (1e-8 : ℝ) := by
    intro y
    by_contra hy
    exact hnone ⟨y, lt_of_not_ge hy⟩
  exact hpre ⟨hcell, hcol⟩

theorem realization_of {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (CL a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
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
  classical
  let E1 : D.Pre × D.Anch → Prop := fun z => ¬ D.PosOK z.1.1.2
  let E2 : D.Pre × D.Anch → Prop := fun z =>
    D.PosOK z.1.1.2 ∧ ¬ D.FewBad z.1.1.1 z.1.1.2 z.1.2.1.1
  let E3 : D.Pre × D.Anch → Prop := fun z =>
    D.PosOK z.1.1.2 ∧ D.FewBad z.1.1.1 z.1.1.2 z.1.2.1.1 ∧
      ¬ D.GoodH z.1.1.1 z.1.1.2 z.1.2.1.1 z.1.2.1.2
  let E4 : D.Pre × D.Anch → Prop := fun z => D.SelOK z.1 ∧ ¬ D.LoadOK CL z.1
  let E5 : D.Pre × D.Anch → Prop := fun z =>
    D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y
  let U12 : D.Pre × D.Anch → Prop := fun z => E1 z ∨ E2 z
  let U123 : D.Pre × D.Anch → Prop := fun z => U12 z ∨ E3 z
  let U1235 : D.Pre × D.Anch → Prop := fun z => U123 z ∨ E5 z
  let U1234 : D.Pre × D.Anch → Prop := fun z => U123 z ∨ E4 z
  let U12345 : D.Pre × D.Anch → Prop := fun z => U1234 z ∨ E5 z
  let GoodStage : D.Pre × D.Anch → Prop := fun z => D.Good z.1 ∧ D.GoodPre z.1 z.2
  let FullStage : D.Pre × D.Anch → Prop := fun z =>
    D.Good z.1 ∧ D.LoadOK CL z.1 ∧ D.GoodPre z.1 z.2
  have hE1 : D.stagedLaw.pr E1 ≤ a₁ := by
    have heq := bind_pr_fst D.preLaw D.anchorLaw (fun q => ¬ D.PosOK q.1.2)
    simpa [Ctx.stagedLaw, E1] using heq ▸ h1
  have hE2 : D.stagedLaw.pr E2 ≤ a₂ := by
    have heq := bind_pr_fst D.preLaw D.anchorLaw
      (fun q => D.PosOK q.1.2 ∧ ¬ D.FewBad q.1.1 q.1.2 q.2.1.1)
    simpa [Ctx.stagedLaw, E2] using heq ▸ h2
  have hE3 : D.stagedLaw.pr E3 ≤ a₃ := by
    have heq := bind_pr_fst D.preLaw D.anchorLaw
      (fun q => D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧
        ¬ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2)
    simpa [Ctx.stagedLaw, E3] using heq ▸ h3
  have hE4 : D.stagedLaw.pr E4 ≤ a₄ := by
    have heq := bind_pr_fst D.preLaw D.anchorLaw (fun q => D.SelOK q ∧ ¬ D.LoadOK CL q)
    simpa [Ctx.stagedLaw, E4] using heq ▸ h4
  have hE5 : D.stagedLaw.pr E5 ≤ a₅ := by simpa [E5] using h5
  have hU12 : D.stagedLaw.pr U12 ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 := by
    simpa [U12] using FinProb.pr_union D.stagedLaw E1 E2
  have hU123 : D.stagedLaw.pr U123 ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 := by
    calc
      D.stagedLaw.pr U123 ≤ D.stagedLaw.pr U12 + D.stagedLaw.pr E3 := by
        simpa [U123] using FinProb.pr_union D.stagedLaw U12 E3
      _ ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 := by linarith [hU12]
  have hU1235 : D.stagedLaw.pr U1235 ≤
      D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 + D.stagedLaw.pr E5 := by
    calc
      D.stagedLaw.pr U1235 ≤ D.stagedLaw.pr U123 + D.stagedLaw.pr E5 := by
        simpa [U1235] using FinProb.pr_union D.stagedLaw U123 E5
      _ ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 + D.stagedLaw.pr E5 := by
        linarith [hU123]
  have hU12345 : D.stagedLaw.pr U12345 ≤
      D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 + D.stagedLaw.pr E4 +
        D.stagedLaw.pr E5 := by
    calc
      D.stagedLaw.pr U12345 ≤ D.stagedLaw.pr U1234 + D.stagedLaw.pr E5 := by
        simpa [U12345] using FinProb.pr_union D.stagedLaw U1234 E5
      _ ≤ D.stagedLaw.pr U123 + D.stagedLaw.pr E4 + D.stagedLaw.pr E5 := by
        have hu := FinProb.pr_union D.stagedLaw U123 E4
        simpa [U1234] using add_le_add_right hu (D.stagedLaw.pr E5)
      _ ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 +
          D.stagedLaw.pr E4 + D.stagedLaw.pr E5 := by linarith [hU123]
  have hcoverGood : ∀ z, D.stagedLaw.w z ≠ 0 → ¬ GoodStage z → U1235 z := by
    intro z hz hbad
    obtain ⟨hq, hW⟩ := staged_support D z.1 z.2 hz
    have hsupp := pre_support D hpos z.1 hq
    by_cases hp : D.PosOK z.1.1.2
    · by_cases hfew : D.FewBad z.1.1.1 z.1.1.2 z.1.2.1.1
      · by_cases hh : D.GoodH z.1.1.1 z.1.1.2 z.1.2.1.1 z.1.2.1.2
        · have hgood : D.Good z.1 := ⟨hsupp, ⟨hp, hfew, hh⟩⟩
          have hcell := anchor_avoids D z.1 (h6 z.1 hgood) z.2 hW
          by_cases hpre : D.GoodPre z.1 z.2
          · exact False.elim (hbad ⟨hgood, hpre⟩)
          · exact Or.inr ⟨hgood, odd_bad_of_not_goodPre D z.1 z.2 hcell hpre⟩
        · exact Or.inl (Or.inr ⟨hp, hfew, hh⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hp, hfew⟩))
    · exact Or.inl (Or.inl (Or.inl hp))
  have hcoverFull : ∀ z, D.stagedLaw.w z ≠ 0 → ¬ FullStage z → U12345 z := by
    intro z hz hbad
    obtain ⟨hq, hW⟩ := staged_support D z.1 z.2 hz
    have hsupp := pre_support D hpos z.1 hq
    by_cases hp : D.PosOK z.1.1.2
    · by_cases hfew : D.FewBad z.1.1.1 z.1.1.2 z.1.2.1.1
      · by_cases hh : D.GoodH z.1.1.1 z.1.1.2 z.1.2.1.1 z.1.2.1.2
        · have hsel : D.SelOK z.1 := ⟨hp, hfew, hh⟩
          have hgood : D.Good z.1 := ⟨hsupp, hsel⟩
          by_cases hload : D.LoadOK CL z.1
          · have hcell := anchor_avoids D z.1 (h6 z.1 hgood) z.2 hW
            by_cases hpre : D.GoodPre z.1 z.2
            · exact False.elim (hbad ⟨hgood, hload, hpre⟩)
            · exact Or.inr ⟨hgood, odd_bad_of_not_goodPre D z.1 z.2 hcell hpre⟩
          · exact Or.inl (Or.inr ⟨hsel, hload⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hp, hfew, hh⟩))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hp, hfew⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
  have hboundGood : D.stagedLaw.pr (fun z => ¬ GoodStage z) ≤ a₁ + a₂ + a₃ + a₅ := by
    calc
      D.stagedLaw.pr (fun z => ¬ GoodStage z) ≤ D.stagedLaw.pr U1235 :=
        pr_mono_support D.stagedLaw (fun z hz hbad => hcoverGood z hz hbad)
      _ ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 + D.stagedLaw.pr E5 := hU1235
      _ ≤ a₁ + a₂ + a₃ + a₅ := by linarith [hE1, hE2, hE3, hE5]
  have ha₄ : 0 ≤ a₄ := le_trans (pr_nonneg D.preLaw (fun q => D.SelOK q ∧ ¬ D.LoadOK CL q)) h4
  have hsumGood : a₁ + a₂ + a₃ + a₅ < 1 := by linarith [ha₄, ha₆, hsum]
  have hgoodPos : 0 < D.stagedLaw.pr GoodStage := by
    have hcomp := pr_compl D.stagedLaw GoodStage
    linarith [hboundGood]
  obtain ⟨z₀, hz₀, hgoodStage₀⟩ := exists_support_of_pos D.stagedLaw GoodStage hgoodPos
  have hgood₀ : D.Good z₀.1 := hgoodStage₀.1
  have hpre₀ : D.GoodPre z₀.1 z₀.2 := hgoodStage₀.2
  let J₀ : FinProb (OddRole D.n → Fin D.N) := Classical.choose (h7 z₀.1 z₀.2 hgood₀ hpre₀)
  have hJ₀ : D.ClockOK z₀.1 z₀.2 J₀ := Classical.choose_spec (h7 z₀.1 z₀.2 hgood₀ hpre₀)
  by_contra hNo
  have hgoodPreBound : ∀ q : D.Pre, D.Good q → D.LoadOK CL q →
      (D.anchorLaw q).pr (fun W => D.GoodPre q W) ≤ a₆ := by
    intro q hq hload
    let J : D.Anch → FinProb (OddRole D.n → Fin D.N) := fun W =>
      if hpre : D.GoodPre q W then Classical.choose (h7 q W hq hpre) else J₀
    have hJ : ∀ W, D.GoodPre q W → D.ClockOK q W (J W) := by
      intro W hpre
      simpa [J, hpre] using Classical.choose_spec (h7 q W hq hpre)
    have hbadSupport : ∀ W, D.GoodPre q W → ∀ f, (J W).w f ≠ 0 →
        ∃ x, 1 < D.evenCol q W f x := by
      intro W hpre f hf
      obtain ⟨hinj, hpf⟩ := (hJ W hpre).1 f hf
      have hnot : ¬ ∀ x, D.evenCol q W f x ≤ 1 := by
        intro hcol
        exact hNo ⟨q, W, f, hq, hpre.1, hinj, hpf, hcol⟩
      obtain ⟨x, hx⟩ := not_forall.mp hnot
      exact ⟨x, lt_of_not_ge hx⟩
    have hprobOne : ∀ W, D.GoodPre q W →
        (J W).pr (fun f => ∃ x, 1 < D.evenCol q W f x) = 1 := by
      intro W hpre
      exact pr_eq_one_of_support (J W) _ (hbadSupport W hpre)
    have hsumEven : ∑ W, (D.anchorLaw q).w W *
        (if D.GoodPre q W then 1 else 0) ≤ a₆ := by
      calc
        _ = ∑ W, (D.anchorLaw q).w W *
            (if D.GoodPre q W then
              (J W).pr (fun f => ∃ x, 1 < D.evenCol q W f x) else 0) := by
          apply Finset.sum_congr rfl
          intro W _
          by_cases hpre : D.GoodPre q W
          · simp [hpre, hprobOne W hpre]
          · simp [hpre]
        _ ≤ a₆ := h8 q hq hload J hJ
    have hprobEq : (D.anchorLaw q).pr (fun W => D.GoodPre q W) =
        ∑ W, (D.anchorLaw q).w W * (if D.GoodPre q W then 1 else 0) := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro W _
      by_cases hpre : D.GoodPre q W <;> simp [hpre]
    rw [hprobEq]
    exact hsumEven
  have hinner : ∀ q : D.Pre,
      (D.anchorLaw q).pr (fun W => FullStage (q, W)) ≤ a₆ := by
    intro q
    by_cases hq : D.Good q
    · by_cases hload : D.LoadOK CL q
      · simpa [FullStage, hq, hload] using hgoodPreBound q hq hload
      · have hz : (D.anchorLaw q).pr (fun W => FullStage (q, W)) = 0 := by
          unfold FinProb.pr
          apply Finset.sum_eq_zero
          intro W _
          simp [FullStage, hq, hload]
        rw [hz]
        exact ha₆
    · have hz : (D.anchorLaw q).pr (fun W => FullStage (q, W)) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro W _
        simp [FullStage, hq]
      rw [hz]
      exact ha₆
  have hFullFormula : D.stagedLaw.pr FullStage =
      ∑ q, D.preLaw.w q * (D.anchorLaw q).pr (fun W => FullStage (q, W)) := by
    simpa [Ctx.stagedLaw, FullStage] using
      (bind_pr D.preLaw D.anchorLaw (fun q W => D.Good q ∧ D.LoadOK CL q ∧ D.GoodPre q W))
  have hFullUpper : D.stagedLaw.pr FullStage ≤ a₆ := by
    rw [hFullFormula]
    calc
      (∑ q, D.preLaw.w q * (D.anchorLaw q).pr (fun W => FullStage (q, W))) ≤
          ∑ q, D.preLaw.w q * a₆ := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hinner q) (D.preLaw.nonneg q)
      _ = a₆ := by rw [← Finset.sum_mul, D.preLaw.sum_eq_one]; ring
  have hboundFull : D.stagedLaw.pr (fun z => ¬ FullStage z) ≤ a₁ + a₂ + a₃ + a₄ + a₅ := by
    calc
      D.stagedLaw.pr (fun z => ¬ FullStage z) ≤ D.stagedLaw.pr U12345 :=
        pr_mono_support D.stagedLaw (fun z hz hbad => hcoverFull z hz hbad)
      _ ≤ D.stagedLaw.pr E1 + D.stagedLaw.pr E2 + D.stagedLaw.pr E3 +
          D.stagedLaw.pr E4 + D.stagedLaw.pr E5 := hU12345
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := by linarith [hE1, hE2, hE3, hE4, hE5]
  have hcompFull := pr_compl D.stagedLaw FullStage
  have honele : 1 ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := by
    linarith [hcompFull, hboundFull, hFullUpper]
  linarith [hsum]

end HypercubeRamsey.Lane_q_s08_asm
