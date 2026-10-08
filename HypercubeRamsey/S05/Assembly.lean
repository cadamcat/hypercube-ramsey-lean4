import HypercubeRamsey.S05.Even
import HypercubeRamsey.Framework.FinProbLemmas

/-!
# L5.1 assembly and the Part B one-shot export

The constants are chosen in the order of D5.1 from the thresholds requested by the nodes.  At one dimension in
the large regime, L5.1a, L5.1b and L5.1e0 give the construction inputs; Steps 1–3 and the five conditioning
stages (with the history odd loads) give a successful key history; L5.1j and the row constructions give the
center layer and the odd rows; L5.1l(3) bounds the odd column sums; L5.1m gives the clock family; L5.1n and
L5.1o bound the even tests and the even loads.  With positive probability every requirement holds, which
yields an injective odd assignment and fractional even rows on common neighbourhoods; Hall's theorem gives the
cube.  None of the proofs below has a proof hole of its own.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey Filter

set_option synthInstance.maxSize 4096

/-- The injective labels of the odd roles. -/
structure OddAssignment5 {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) where
  label : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  injective : Function.Injective label

open Classical in
/-- Fractional placement rows for even roles on the common neighbourhoods of their odd neighbours' labels. -/
structure EvenPlacement5 {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (O : OddAssignment5 E G) where
  row : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  nonneg : ∀ a x, 0 ≤ row a x
  sum_one : ∀ a, ∑ x, row a x = 1
  common_neighborhood : ∀ a x, row a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (O.label b)
  column_load : ∀ x, ∑ a, row a x ≤ 1

/-- L5.1o: the odd assignment and even fractional rows assemble into a cube row certificate. -/
def L5_1o_rows {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (O : OddAssignment5 (n := n) (N := N) E G)
    (A : EvenPlacement5 (n := n) (N := N) O) :
    CubeRows5 (n := n) (N := N) E G := by
  exact {
    oddLabel := O.label
    odd_injective := O.injective
    evenRow := A.row
    row_nonneg := A.nonneg
    row_sum := A.sum_one
    row_supported := A.common_neighborhood
    column_load := A.column_load
  }

/-! ### Finite probability helpers -/

theorem FinProb.pr_mono5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

theorem FinProb.bind_pr_fst5 {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α)
    (K : α → FinProb β) (A : α → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1) = P.pr A := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hA : A a
  · simp only [hA, if_true]
    rw [← Finset.mul_sum, (K a).sum_eq_one, mul_one]
  · simp [hA]

theorem FinProb.bind_w_ne_zero5 {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α)
    (K : α → FinProb β) (ab : α × β) (h : (FinProb.bind P K).w ab ≠ 0) :
    P.w ab.1 ≠ 0 ∧ (K ab.1).w ab.2 ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem FinProb.pos_pr_true5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) : 0 < P.pr (fun _ => True) := by
  simp [FinProb.pr, P.sum_eq_one]

set_option maxHeartbeats 4000000 in
/-- L5.1, the construction (05:15–1282): for large `n` and `N ≥ C₀ 2^n` there are an injective odd assignment and
fractional even rows on its common `G`-neighbourhoods with column loads at most one. -/
theorem L5_1_rows : ∀ γ K' χ : ℝ, 0 < γ → γ < 1 → 0 < K' → 0 < χ →
    ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (ι : Type*) [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N),
      LargeAt n₀ C₀ n N → (∀ i, 0 ≤ Λ i) → ∑ i, Λ i = 1 →
      (∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K') →
      (∀ i, 0 < Λ i → χ * N ≤ ((Finset.univ.filter
        (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ)) →
      ∃ O : OddAssignment5 (n := n) (N := N) E G, Nonempty (EvenPlacement5 O) := by
  intro γ K' χ hγ hγ' hK hχ
  -- thresholds and constants requested by the nodes, in the order of D5.1
  obtain ⟨Rc, hc⟩ := Setup5.L5_1c (γ := γ) (K' := K') (χ := χ)
  obtain ⟨cL, cH, hcLH, Rf, hf⟩ := Setup5.L5_1f (γ := γ) (K' := K') (χ := χ)
  obtain ⟨Ccnt, _hCcnt, hcnt⟩ := Setup5.L5_1e_count (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R1, h1⟩ := Setup5.L5_1h1 (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R2, h2⟩ := Setup5.L5_1h2 (γ := γ) (K' := K') (χ := χ)
  obtain ⟨C₁, hC₁, Rl1, hl1⟩ := Setup5.L5_1l1 (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R3, h3⟩ := Setup5.L5_1h3 (γ := γ) (K' := K') (χ := χ) Ccnt cL cH hcLH
  obtain ⟨R4, h4⟩ := Setup5.L5_1h4 (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R5, h5⟩ := Setup5.L5_1h5 (γ := γ) (K' := K') (χ := χ) Ccnt cL cH hcLH
  obtain ⟨Ckey, Rj, hj⟩ := Setup5.L5_1j (γ := γ) (K' := K') (χ := χ) Ccnt cL cH hcLH
  obtain ⟨Cloc, Rk, hk⟩ := Setup5.L5_1k_rows (γ := γ) (K' := K') (χ := χ) cL cH hcLH Ckey
  obtain ⟨C₂, _hC₂, Rl2, hl2⟩ := Setup5.L5_1l2 (γ := γ) (K' := K') (χ := χ) Cloc C₁ hC₁
  obtain ⟨Rl3, hl3⟩ := Setup5.L5_1l3 (γ := γ) (K' := K') (χ := χ) (max C₁ C₂)
    (lt_of_lt_of_le hC₁ (le_max_left _ _))
  obtain ⟨A, P, nm, εc, hεc, hεc0, hm⟩ := L5_1m
  obtain ⟨Rmi, hmi⟩ := Setup5.L5_1m_inputs (γ := γ) (K' := K') (χ := χ) A P
  obtain ⟨Rs, hs⟩ := Setup5.L5_1n_setup (γ := γ) (K' := K') (χ := χ)
  obtain ⟨Rn, hn⟩ := Setup5.L5_1n (γ := γ) (K' := K') (χ := χ)
  obtain ⟨Rnr, hnr⟩ := Setup5.L5_1n_rows (γ := γ) (K' := K') (χ := χ)
  obtain ⟨Ro, ho⟩ := Setup5.L5_1o (γ := γ) (K' := K') (χ := χ)
  obtain ⟨p, -, hp⟩ := D5_1_params γ K' χ hγ hγ' hK hχ
    (Rc.join (Rf.join (R1.join (R2.join (Rl1.join (R3.join (R4.join (R5.join (Rl2.join (Rj.join
      (Rk.join (Rl3.join (Rmi.join (Rs.join (Rn.join (Rnr.join Ro))))))))))))))))
  obtain ⟨hpc, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpf, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hp1, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hp2, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpl1, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hp3, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hp4, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hp5, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpl2, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpj, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpk, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpl3, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpmi, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hps, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpn, hp⟩ := ParamReq5.holds_of_join hp
  obtain ⟨hpnr, hpo⟩ := ParamReq5.holds_of_join hp
  -- large-regime thresholds
  obtain ⟨nc, hc'⟩ := hc p hpc
  obtain ⟨nf, hf'⟩ := hf p hpf
  obtain ⟨ncnt, hcnt'⟩ := hcnt p
  obtain ⟨n1, h1'⟩ := h1 p hp1
  obtain ⟨n2, h2'⟩ := h2 p hp2
  obtain ⟨nl1, hl1'⟩ := hl1 p hpl1
  obtain ⟨n3, h3'⟩ := h3 p hp3
  obtain ⟨n4, h4'⟩ := h4 p hp4
  obtain ⟨n5, h5'⟩ := h5 p hp5
  obtain ⟨nl2, hl2'⟩ := hl2 p hpl2
  obtain ⟨nj, hj'⟩ := hj p hpj
  obtain ⟨nk, hk'⟩ := hk p hpk
  obtain ⟨C₀a, _hC₀a, nl3, hl3'⟩ := hl3 p hpl3
  obtain ⟨nmi, hmi'⟩ := hmi p hpmi
  obtain ⟨ns, hs'⟩ := hs p hps
  obtain ⟨nn, hn'⟩ := hn p hpn
  obtain ⟨nnr, hnr'⟩ := hnr p hpnr
  obtain ⟨C₀b, _hC₀b, no, ho'⟩ := ho p hpo
  obtain ⟨nb, hb⟩ := L5_1b p.alpha p.halpha.1 p.halpha.2
  obtain ⟨ne, he⟩ := L5_1e0 1 one_pos
  obtain ⟨nε, hnε⟩ : ∃ N₁ : ℕ, ∀ k ≥ N₁, εc k ≤ 1 := by
    have hev := hεc.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact Filter.eventually_atTop.mp hev
  refine ⟨nc + nf + ncnt + n1 + n2 + nl1 + n3 + n4 + n5 + nl2 + nj + nk + nl3 + nm + nmi + ns + nn +
    nnr + no + nb + ne + nε + 1, max (max C₀a C₀b) 1, ?_⟩
  intro n N E G ι _ Λ μ hLarge hΛ0 hΛ1 hwidth hbal hgood
  obtain ⟨hn₀, hN1, hN2⟩ := hLarge
  have hC₀a : C₀a * 2 ^ n ≤ (N : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)) hN1
  have hC₀b : C₀b * 2 ^ n ≤ (N : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)) hN1
  have h2N : 2 ^ n ≤ N := by
    have h1' : (1 : ℝ) * 2 ^ n ≤ (N : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hN1
    have h1'' : ((2 ^ n : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
    exact_mod_cast h1''
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos (by norm_num : 0 < 2) n) h2N
  -- L5.1a, L5.1b, L5.1e0: the construction inputs
  let Λf : FinProb ι := ⟨Λ, hΛ0, hΛ1⟩
  obtain ⟨P0, S0, hP1, hP2, hP3⟩ := L5_1a γ K' χ (n := n) (Bin := BinVector5 n) p E G Λf μ hNpos hwidth hbal
    (by intro i hi; convert hgood i hi; exact Iff.rfl)
  obtain ⟨g, hgE⟩ := hb n (by omega)
  obtain ⟨St, -⟩ := he n (by omega) ⌈(n : ℝ) ^ p.alpha⌉₊ (p.J n) g
  let X : Setup5 γ K' χ n N E G :=
    { p := p, P := P0, S := S0, g := g, St := St, y₀ := ⟨0, hNpos⟩
      partner_bin_free := hP3
      partner_related := fun v hv w a ha => (hP2 v a).2 (by
        rw [hP1 v hv w] at ha
        exact (Finset.mem_filter.mp ha).2) }
  -- Steps 1–3, record counts, coverage
  have hS1 : X.Step1Raw := hc' n (by omega) N E G X rfl
  have hS2 : X.Step2Raw := Setup5.L5_1d n N E G X
  have hS3 : X.Step3Raw (cL p.pre1) (cH p.pre1) := hf' n (by omega) N E G X rfl
  have hRC : X.RecordCount Ccnt := hcnt' n (by omega) N E G X rfl
  have hcov := L5_1e_cover X.g (X.p.J n)
  -- the five conditioning stages and the history odd loads
  obtain ⟨v, hvw, hv1⟩ := FinProb.exists_support_of_pos5 _ _
    (lt_of_lt_of_le (by norm_num) (h1' n (by omega) N E G X rfl hS1 hS2))
  have hvlab : v ∈ X.P.lab0 := by
    by_contra hv
    exact hvw (X.P.lab0_atom v hv)
  obtain ⟨ν₂, hν₂⟩ := h2' n (by omega) N E G X rfl v hv1
  obtain ⟨c, hcw, hcbad⟩ := FinProb.exists_support_of_pr_lt5 _ _
    (lt_of_le_of_lt (hl1' n (by omega) N E G X rfl hgE hN2 v ν₂ hν₂) (by norm_num))
  have hbase : X.baseLaw.w (v, c) ≠ 0 :=
    mul_ne_zero hvw (hν₂.2.2.2.2 c hcw)
  obtain ⟨ν₃, hν₃⟩ := h3' n (by omega) N E G X rfl hRC hS3 v c hbase (hν₂.1 c hcw) (hν₂.2.1 c hcw)
    (hν₂.2.2.1 c hcw)
  obtain ⟨hi, hiw, -⟩ := FinProb.exists_support_of_pos5 ν₃ (fun _ => True) (FinProb.pos_pr_true5 ν₃)
  obtain ⟨tr, htr⟩ := h4' n (by omega) N E G X rfl (v, c) hi (hν₃.2.2.1 hi hiw)
  obtain ⟨ν₅, hν₅⟩ := h5' n (by omega) N E G X rfl hRC hS3 (v, c) hi ν₃ hν₃ hiw tr htr
  -- the center layer and the rows (needed for the proxy means of the second history load)
  obtain ⟨L, hLlow, hLsucc⟩ := hj' n (by omega) N E G X rfl hRC
  obtain ⟨LR, hCloc⟩ := hk' n (by omega) N E G X rfl hcov.2 L hLlow
  let HC : X.HighChoice5 L.ht.hp.Loc :=
    { law := fun H r a hc hpf => Classical.choose
        ((L5_1g_common_high_law (X.highModel H r a hc hpf)).2 () trivial)
      cap := fun H r a hc hpf => (Classical.choose_spec
        ((L5_1g_common_high_law (X.highModel H r a hc hpf)).2 () trivial)).1
      support := fun H r a hc hpf => (Classical.choose_spec
        ((L5_1g_common_high_law (X.highModel H r a hc hpf)).2 () trivial)).2.1
      cost := fun H r a hc hpf c hcm => by
        have h := (Classical.choose_spec
          ((L5_1g_common_high_law (X.highModel H r a hc hpf)).2 () trivial)).2.2 ⟨c, hcm⟩
        simpa [Setup5.highModel, highDeletionCost5] using h }
  obtain ⟨HR⟩ := Setup5.L5_1g_rows n N E G X L hcov.2 HC
  have hZ : X.ProxyMeanData5 Cloc (v, c) hi (fun lo => LR.proxy ((v, c), X.joinHidden hi lo)) :=
    { nonneg := fun lo r y => LR.proxy_nonneg _ r y
      high_zero := fun lo r y hr => LR.proxy_high _ r y hr
      cap := fun lo r y => LR.proxy_cap _ r y
      locality := fun r lo lo' hagree => LR.proxy_local (v, c) hi r lo lo' (fun k hk =>
        hagree k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hk).2.trans (Nat.mul_le_mul_right _ hCloc)⟩))
      one_target := fun lo r y hr => by
        rw [LR.selExp_mean (v, c) hi r lo y hr]
        have hmean := L5_1k_mean_bound (LR.selExp (v, c) hi r lo)
          (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity r.1)))) (Real.exp_pos _)
          (Real.exp_le_one_iff.mpr (by
            have := X.p.hdelta.1
            have : (0 : ℝ) ≤ X.p.kPrime n (X.g.severity r.1) := Nat.cast_nonneg _
            nlinarith))
          (LR.selExp_records (v, c) hi r lo) y
        rw [LR.selExp_prior (v, c) hi r lo hr] at hmean
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        calc (N : ℝ) * _ ≤ (N : ℝ) * (2 * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y) :=
              mul_le_mul_of_nonneg_left hmean hN0
          _ = 2 * (N : ℝ) * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y := by ring }
  have hload1 : ∀ y, X.avgLowPrior (v, c) y ≤ C₁ := fun y => not_lt.mp fun h => hcbad ⟨y, h⟩
  obtain ⟨lo, hlow, hlobad⟩ := FinProb.exists_support_of_pr_lt5 _ _
    (lt_of_le_of_lt (hl2' n (by omega) N E G X rfl hgE hN2 (v, c) hi tr ν₅ _ _ hν₅ htr hload1 _ hZ)
      (by norm_num))
  -- the successful key history
  let H : X.KeyHist := ((v, c), X.joinHidden hi lo)
  have hgoodH : X.KeyGood5 H (cL p.pre1) (cH p.pre1) :=
    { parent_mem := hvlab
      step1 := hν₂.1 c hcw
      step2 := hν₅.1 lo hlow
      step3 := hν₅.2.1 lo hlow
      base_support := hbase
      key_support := by
        intro ℓ h
        cases ℓ with
        | inl k => exact hν₅.2.2.2 lo hlow k h
        | inr i => exact hν₃.2.2.2.2.2.2 hi hiw i h }
  have hsuccH : X.KeySuccess5 H (cL p.pre1) (cH p.pre1) (max C₁ C₂) LR.proxy :=
    ⟨hgoodH, fun y => (hload1 y).trans (le_max_left _ _),
      fun y => (not_lt.mp fun h => hlobad ⟨y, h⟩).trans (le_max_right _ _)⟩
  have hS2B : ∀ K, X.TypeOccurs K → X.Step2Bounds H K := fun K hK =>
    Setup5.L5_1d_bounds n N E G X hcov.2 H hgoodH.base_support hgoodH.step1 K hK (hgoodH.step2.1 K hK)
  -- the center stage at `H`
  have hPs := hLsucc H hgoodH
  have hPodd := hl3' n (by omega) N E G X rfl hgE hC₀a hN2 L _ _ LR HR H hsuccH
  obtain ⟨ES⟩ := hs' n (by omega) N E G X rfl L _ _ LR HR
  -- the clock family (L5.1m)
  have hclock : ∀ ω, L.success H ω → X.OddLoadsOK LR HR H ω →
      ∃ J : FinProb (OddRole5 n → X.OddOut),
        (∀ O, J.w O ≠ 0 → Function.Injective (fun b => (O b).2) ∧
          ∀ v, ∑ b, X.budgetCost HR H ω v b (O b) ≤ X.p.a 5 * (X.kStarLen : ℝ) * n) ∧
        (∀ (S : Finset (OddRole5 n)) (o : OddRole5 n → X.OddOut), S.card ≤ n ^ 2 →
          J.pr (fun O => ∀ b ∈ S, O b = o b) ≤ (1 + εc n) * ∏ b ∈ S, (X.oddRowFP LR HR H ω b).w (o b)) := by
    intro ω hsω hoddω
    obtain ⟨hatom, hcost, hoff, hmean, ht01, hhoeff⟩ :=
      hmi' n (by omega) N E G X rfl h2N hN2 hcov.1 L _ _ LR HR H ω hsω
    have hcol : ∀ x, ∑ b, labMarg (X.oddRowFP LR HR H ω b) Prod.snd x ≤ 1e-8 := by
      intro x
      have hx := hoddω x
      have heq : ∀ b, labMarg (X.oddRowFP LR HR H ω b) Prod.snd x =
          ∑ o : X.OddOut, (if o.2 = x then X.oddRow LR HR H ω b o else 0) := by
        intro b
        simp [labMarg, Setup5.oddRowFP, L.success_valid H ω hsω b]
      simpa [heq] using hx
    exact hm n (by omega) N h2N hN2 Prod.snd (X.oddRowFP LR HR H ω) (X.budgetCost HR H ω) _ _ _
      hcol hatom hcost hoff hmean ht01 hhoeff
  let J : X.CΩ L.ht → FinProb (OddRole5 n → X.OddOut) := fun ω =>
    if hω : L.success H ω ∧ X.OddLoadsOK LR HR H ω then Classical.choose (hclock ω hω.1 hω.2)
    else FinProb.dirac5 (fun _ => (0, X.y₀))
  have hJ : X.ClockFamily5 (LR := LR) (HR := HR) H J (εc n) :=
    { injective := fun ω hsω hoddω O hO => by
        have hdef : J ω = Classical.choose (hclock ω hsω hoddω) := dif_pos ⟨hsω, hoddω⟩
        rw [hdef] at hO
        exact ((Classical.choose_spec (hclock ω hsω hoddω)).1 O hO).1
      budgets := fun ω hsω hoddω O hO => by
        have hdef : J ω = Classical.choose (hclock ω hsω hoddω) := dif_pos ⟨hsω, hoddω⟩
        rw [hdef] at hO
        exact ((Classical.choose_spec (hclock ω hsω hoddω)).1 O hO).2
      joint := fun ω hsω hoddω S o hS => by
        have hdef : J ω = Classical.choose (hclock ω hsω hoddω) := dif_pos ⟨hsω, hoddω⟩
        rw [hdef]
        have h := (Classical.choose_spec (hclock ω hsω hoddω)).2 S o hS
        have hw : ∀ b, (X.oddRowFP LR HR H ω b).w (o b) = X.oddRow LR HR H ω b (o b) := by
          intro b
          simp [Setup5.oddRowFP, L.success_valid H ω hsω b]
        simpa [hw] using h }
  have hεn : εc n ≤ 1 := hnε n (by omega)
  -- the even tests and loads (L5.1n, L5.1o)
  have hPn := hn' n (by omega) N E G X rfl h2N hN2 L _ _ LR HR ES H hgoodH J (εc n) (hεc0 n) hεn hJ
  have hPo := ho' n (by omega) N E G X rfl hgE hC₀b hN2 L _ _ LR HR ES H hgoodH hS2B J (εc n)
    (hεc0 n) hεn hJ
  -- positivity of the joint success event
  have hcentre : (X.jointLaw H J).pr (fun ωO => ¬ (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1)) ≤
      2 / 100 := by
    rw [Setup5.jointLaw, FinProb.bind_pr_fst5 (X.centreLaw L.ht H) J
      (fun ω => ¬ (L.success H ω ∧ X.OddLoadsOK LR HR H ω))]
    have hm1 := FinProb.pr_mono5 (X.centreLaw L.ht H)
      (A := fun ω => ¬ (L.success H ω ∧ X.OddLoadsOK LR HR H ω))
      (B := fun ω => ¬ L.success H ω ∨ (L.success H ω ∧ ¬ X.OddLoadsOK LR HR H ω))
      (fun ω h => by
        by_cases hs : L.success H ω
        · exact Or.inr ⟨hs, fun ho => h ⟨hs, ho⟩⟩
        · exact Or.inl hs)
    have hu := FinProb.pr_union (X.centreLaw L.ht H) (fun ω => ¬ L.success H ω)
      (fun ω => L.success H ω ∧ ¬ X.OddLoadsOK LR HR H ω)
    beta_reduce at hm1 hu
    linarith
  have hbad : (X.jointLaw H J).pr (fun ωO => ¬ (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
      (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
      X.EvenLoadsOK ES H ωO.1 ωO.2)) < 1 := by
    have hm := FinProb.pr_mono5 (X.jointLaw H J)
      (A := fun ωO => ¬ (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
        (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
        X.EvenLoadsOK ES H ωO.1 ωO.2))
      (B := fun ωO => ¬ (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1) ∨
        ((L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          ∃ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c ∧ ¬ X.EvenTest ES H ωO.1 v c ωO.2) ∨
        (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
          ¬ X.EvenLoadsOK ES H ωO.1 ωO.2)))
      (fun ωO h => by
        by_cases h1 : L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1
        · refine Or.inr ?_
          by_cases h2 : ∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2
          · exact Or.inr ⟨h1.1, h1.2, h2, fun h3 => h ⟨h1.1, h1.2, h2, h3⟩⟩
          · refine Or.inl ⟨h1.1, h1.2, ?_⟩
            push_neg at h2
            exact h2
        · exact Or.inl h1)
    have hu1 := FinProb.pr_union (X.jointLaw H J)
      (fun ωO => ¬ (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1))
      (fun ωO => (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          ∃ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c ∧ ¬ X.EvenTest ES H ωO.1 v c ωO.2) ∨
        (L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
          ¬ X.EvenLoadsOK ES H ωO.1 ωO.2))
    have hu2 := FinProb.pr_union (X.jointLaw H J)
      (fun ωO => L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          ∃ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c ∧ ¬ X.EvenTest ES H ωO.1 v c ωO.2)
      (fun ωO => L.success H ωO.1 ∧ X.OddLoadsOK LR HR H ωO.1 ∧
          (∀ v c, X.evenRefOf (L.elig H) H ωO.1 v = some c → X.EvenTest ES H ωO.1 v c ωO.2) ∧
          ¬ X.EvenLoadsOK ES H ωO.1 ωO.2)
    beta_reduce at hm hu1 hu2
    linarith
  obtain ⟨⟨ω, O⟩, hw, hgoodEv⟩ := FinProb.exists_support_of_pr_lt5 _ _ hbad
  rw [not_not] at hgoodEv
  obtain ⟨hsω, hoddω, htestω, hloadω⟩ := hgoodEv
  have hJw : (J ω).w O ≠ 0 := (FinProb.bind_w_ne_zero5 _ _ (ω, O) hw).2
  have hbud : X.BudgetOK HR H ω O := hJ.budgets ω hsω hoddω O hJw
  -- each even role has its reference, gate and test, hence a valid even row
  have hrow : ∀ a : EvenRole5 n, ∃ cr, X.evenRefOf (L.elig H) H ω a = some cr ∧ ES.gate H a cr ω O ∧
      X.EvenTest ES H ω a cr O := by
    intro a
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (L.success_select H ω hsω a)
    have href : X.evenRefOf (L.elig H) H ω a = some (l, X.refSubset H ω a l) := by
      simp [Setup5.evenRefOf, hl]
    exact ⟨_, href, ES.gate_success H ω O hsω hbud a _ href, htestω a _ href⟩
  refine ⟨⟨fun b => (O b).2, hJ.injective ω hsω hoddω O hJw⟩, ⟨?_⟩⟩
  exact
    { row := fun a x => X.evenRow ES H ω O a x
      nonneg := fun a x => by
        obtain ⟨cr, hcr, hg, ht⟩ := hrow a
        exact (hnr' n (by omega) N E G X rfl L _ _ LR HR ES H hS2B ω O a cr hcr hg ht).1 x
      sum_one := fun a => by
        obtain ⟨cr, hcr, hg, ht⟩ := hrow a
        exact (hnr' n (by omega) N E G X rfl L _ _ LR HR ES H hS2B ω O a cr hcr hg ht).2.1
      common_neighborhood := fun a x hx b hab => by
        obtain ⟨cr, hcr, hg, ht⟩ := hrow a
        exact (hnr' n (by omega) N E G X rfl L _ _ LR HR ES H hS2B ω O a cr hcr hg ht).2.2.1 x hx b
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
      column_load := hloadω }

/-- L5.1, consumed one-shot form used by Part B. -/
theorem L5_1_consumed : ∀ γ K' χ : ℝ, 0 < γ → γ < 1 → 0 < K' → 0 < χ →
    ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (ι : Type*) [Fintype ι] (Λ : ι → ℝ) (μ : ι → Law N),
      LargeAt n₀ C₀ n N → (∀ i, 0 ≤ Λ i) → ∑ i, Λ i = 1 →
      (∀ i, 0 < Λ i → (μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ x, (N : ℝ) * ∑ i, Λ i * (μ i).w x ≤ K') →
      (∀ i, 0 < Λ i → χ * N ≤ ((Finset.univ.filter
        (fun y => (95 : ℝ) / 100 ≤ colDeg E G (μ i) y)).card : ℝ)) →
      CubeAt n N E := by
  intro γ K' χ hγ hγ' hK hχ
  obtain ⟨n₀, C₀, hRows⟩ := L5_1_rows γ K' χ hγ hγ' hK hχ
  refine ⟨n₀, C₀, ?_⟩
  intro n N E G ι inst Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  obtain ⟨O, ⟨A⟩⟩ := hRows n N E G ι Λ μ hLarge hΛ hΛsum hwidth hbalance hgood
  exact cube_of_rows5 (L5_1o_rows O A)

end HypercubeRamsey
