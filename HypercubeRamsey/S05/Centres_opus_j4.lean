import HypercubeRamsey.S05.Centres_q_s05_j34
import HypercubeRamsey.S03.Height.Selection

/-!
# J4 helpers: singleton losses (05:820–824, 835–838)

A prospective ID fails its singleton tests with probability `o(1)`: the prior-heavy fraction of its
reference tuple is controlled by the per-block tail (independent blocks, 05:787–800), and at a high
role with `j = J + 1` the optional column is hit by enough pool blocks (Step 2 optional mass test).
The failed prospective IDs in one site-level ball are then a sum of independent indicators of mean
`O(λ e^{-100})`, so an exponential-moment bound gives the `λ/12` threshold with probability
`1 - exp(-Ω(λ))`.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_j4

open Classical OAI.HypercubeRamsey
open scoped BigOperators
open Filter

noncomputable section

set_option maxHeartbeats 800000

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

/-- Exponential-moment upper tail for a count of independent events with total mean at most `μ`. -/
theorem count_tail_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (A : ∀ i, Ω i → Prop) (μ t : ℝ)
    (hμ : ∑ i, (P i).pr (A i) ≤ μ) :
    (FinProb.pi P).pr (fun ω => t ≤ ((Finset.univ.filter fun i => A i (ω i)).card : ℝ)) ≤
      Real.exp (2 * μ - t) := by
  classical
  let Y : ∀ i, Ω i → ℝ := fun i ω => if A i ω then 1 else 0
  have hY (i : ι) (ω : Ω i) : 0 ≤ Y i ω ∧ Y i ω ≤ 1 := by
    dsimp [Y]
    split_ifs <;> norm_num
  have hsum (ω : ∀ i, Ω i) : ∑ i, Y i (ω i) =
      ((Finset.univ.filter fun i => A i (ω i)).card : ℝ) := by
    have hcardNat : (Finset.univ.filter fun i => A i (ω i)).card =
        ∑ i, if A i (ω i) then (1 : ℕ) else 0 := by
      rw [Finset.card_filter]
    have hcardReal : (∑ i, if A i (ω i) then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun i => A i (ω i)).card : ℝ) := by
      exact_mod_cast hcardNat.symm
    simpa only [Y] using hcardReal
  have hmean : ∑ i, (P i).expect (Y i) = ∑ i, (P i).pr (A i) := by
    congr 1
    funext i
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : A i ω <;> simp [Y, h]
  have hnonneg : 0 ≤ ∑ i, (P i).pr (A i) :=
    Finset.sum_nonneg fun i _ => FinProb.pr_nonneg _ _
  have hmk := FinProb.pr_exp_markov (FinProb.pi P) (fun ω => ∑ i, Y i (ω i)) 1 t (by norm_num)
  have hmgf := FinProb.expect_exp_sum_le_of_mem_Icc P Y hY 1
  have he : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_d9
    linarith
  calc
    (FinProb.pi P).pr (fun ω => t ≤ ((Finset.univ.filter fun i => A i (ω i)).card : ℝ)) =
        (FinProb.pi P).pr (fun ω => t ≤ ∑ i, Y i (ω i)) := by
      congr 1
      funext ω
      rw [hsum ω]
    _ ≤ Real.exp (-1 * t) *
          (FinProb.pi P).expect (fun ω => Real.exp (1 * ∑ i, Y i (ω i))) := hmk
    _ ≤ Real.exp (-1 * t) * Real.exp ((Real.exp 1 - 1) * ∑ i, (P i).expect (Y i)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ ≤ Real.exp (2 * μ - t) := by
      rw [← Real.exp_add, hmean]
      apply Real.exp_le_exp.mpr
      have h1 : (Real.exp 1 - 1) * ∑ i, (P i).pr (A i) ≤ 2 * ∑ i, (P i).pr (A i) :=
        mul_le_mul_of_nonneg_right he hnonneg
      linarith

/-- Counting a filter on a product type by its first coordinate. -/
theorem card_filter_prod {α β : Type*} [Fintype α] [Fintype β] (Q : α → β → Prop) :
    (Finset.univ.filter fun e : α × β => Q e.1 e.2).card =
      ∑ a, (Finset.univ.filter fun b => Q a b).card := by
  classical
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- The per-location law of the center experiment: presence is independent of the arrays. -/
theorem cval_pr_le {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] (q b : ℝ) (hq : 0 ≤ q)
    (U : FinProb β₁) (Q : FinProb β₂) (Gv : β₂ → Prop) :
    ((FinProb.bernoulli q).prod ((FinProb.bernoulli b).prod (U.prod Q))).pr
        (fun c => c.1 = true ∧ Gv c.2.2.2) ≤ q * Q.pr Gv := by
  classical
  have hsplit := Lane_q_s05_j34.pr_prod_and (FinProb.bernoulli q)
    ((FinProb.bernoulli b).prod (U.prod Q)) (fun x => x = true) (fun r => Gv r.2.2)
  have hrest : ((FinProb.bernoulli b).prod (U.prod Q)).pr (fun r => Gv r.2.2) = Q.pr Gv :=
    (Lane_q_s05_j34.pr_prod_snd5 (FinProb.bernoulli b) (U.prod Q) (fun r => Gv r.2)).trans
      (Lane_q_s05_j34.pr_prod_snd5 U Q Gv)
  have hbern : (FinProb.bernoulli q).pr (fun x => x = true) ≤ q := by
    unfold FinProb.pr
    rw [Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false, add_zero]
    change max 0 (min q 1) ≤ q
    exact max_le hq (min_le_left _ _)
  calc
    _ = (FinProb.bernoulli q).pr (fun x => x = true) *
          ((FinProb.bernoulli b).prod (U.prod Q)).pr (fun r => Gv r.2.2) := hsplit
    _ ≤ q * Q.pr Gv := by
      rw [hrest]
      exact mul_le_mul_of_nonneg_right hbern (FinProb.pr_nonneg _ _)

variable (X : Setup5 γ K' χ n N E G)

/-- The singleton tests of one ID with arrays `A` for an even type `K` and optional key `o`
(the body of `singletonOK`, 05:820–824). -/
def singleCond {Id : Type} (H : X.KeyHist) (A : X.ArraysOn Id) (l : Id) (K : X.Ty)
    (o : Option X.Key) : Prop :=
  (((∑ i : Fin (X.p.typeBlocks n K),
      if ∃ j ∈ X.refSubsetOn H A (l, K) o, X.blockIdx K j = some i then
        (Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
          Lane_q_s05_j34.priorHeavy5 X H K (A (l, K) i e.1 e.2)).card
      else 0 : ℕ) : ℝ) ≤ X.p.nu0 * (X.refLen K (X.refSubsetOn H A (l, K) o) : ℝ)) ∧
    ∀ k, o = some (.inl k) →
      X.p.usedBlocks n ≤ (X.hitSet A (l, K) (X.lowCol H.2 k)).card

/-- Blocks per segment are positive for every type once `m > 1`. -/
theorem typeSegs_pos (hm : 1 < X.p.m n) (K : X.Ty) : 0 < X.p.q0 * X.p.typeSegs n K := by
  have hq0 := X.p.hq0.1
  have hlog : 0 < Real.log (X.p.m n : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hseg : 0 < X.p.typeSegs n K := by
    unfold Params5.typeSegs
    rcases K.2.2 with _ | j
    · exact Lane_sol_s05_h5l.uStarSeg_positive X.p n hm
    · unfold Params5.uSeg
      apply Nat.ceil_pos.mpr
      have hq : (0 : ℝ) < X.p.q0 := by exact_mod_cast hq0
      have hj : (0 : ℝ) < (j : ℝ) + 4 := by positivity
      exact div_pos (mul_pos (mul_pos X.p.hK1 hj) hlog) hq
  exact Nat.mul_pos hq0 hseg

/-- The prior-heavy part of the singleton test fails with probability at most `e^{-100}`. -/
theorem heavy_fail_le (H : X.KeyHist) {cL cH : ℝ} (hgood : X.KeyGood5 H cL cH)
    (K : X.Ty) (hType : X.TypeOccurs K) {Id : Type} (l : Id) (o : Option X.Key) (C : ℝ)
    (hC : 0 ≤ C)
    (hTail : (X.p.typeBlocks n K : ℝ) * Real.exp (-C * (X.p.typeSegs n K : ℝ)) ≤ Real.exp (-100))
    (hKB : (X.p.q0 + (Real.log 2 + X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| + C) / X.p.Kpp) /
      X.p.nu0 ≤ X.p.KB)
    (hm : 1 < X.p.m n) :
    (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
      (fun arrs : (∀ K : X.Ty, X.Array K) =>
        ¬ ((((∑ i : Fin (X.p.typeBlocks n K),
          if ∃ j ∈ X.refSubsetOn H (fun c : Id × X.Ty => arrs c.2) (l, K) o,
              X.blockIdx K j = some i then
            (Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
              Lane_q_s05_j34.priorHeavy5 X H K (arrs K i e.1 e.2)).card
          else 0 : ℕ) : ℝ) ≤ X.p.nu0 *
            (X.refLen K (X.refSubsetOn H (fun c : Id × X.Ty => arrs c.2) (l, K) o) : ℝ)))) ≤
      Real.exp (-100) := by
  classical
  have hcov := L5_1e_cover X.g (X.p.J n)
  have hBounds : X.Step2Bounds H K :=
    Setup5.L5_1d_bounds n N E G X hcov.2 H hgood.base_support hgood.step1 K hType
      (hgood.step2.1 K hType)
  have hDensity := hBounds.2.1
  have hLen := typeSegs_pos X hm K
  have hν : 0 < X.p.nu0 := X.p.hnu0
  have hKpp : 0 < X.p.Kpp := X.p.hKpp
  have hq0 : (0 : ℝ) < X.p.q0 := by exact_mod_cast X.p.hq0.1
  let A : ℝ := X.blockConst K
  let L : ℝ := X.p.Kpp * (1 + ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))
  have hApos : 0 < A := Real.exp_pos _
  have hlogA : Real.log A = L := Real.log_exp _
  have hLge : X.p.Kpp ≤ L := by
    have hs : 0 ≤ ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    dsimp [L]
    nlinarith
  have hLpos : 0 < L := lt_of_lt_of_le hKpp hLge
  let q : ℝ := ((X.p.q0 : ℝ) * K') / (A ^ X.p.KB)
  have hApow : 0 < A ^ X.p.KB := Real.rpow_pos_of_pos hApos _
  have hq0K : 0 < (X.p.q0 : ℝ) * K' := mul_pos hq0 X.p.hK
  have hqpos : 0 < q := div_pos hq0K hApow
  have hlogq : Real.log q = Real.log ((X.p.q0 : ℝ) * K') - X.p.KB * L := by
    dsimp [q]
    rw [Real.log_div hq0K.ne' hApow.ne', Real.log_rpow hApos, hlogA]
  -- the margin
  let B : ℝ := Real.log 2 + X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| + C
  have hB : 0 ≤ B := by
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have habs : 0 ≤ X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| :=
      mul_nonneg hν.le (abs_nonneg _)
    dsimp [B]
    linarith
  have hT : X.p.q0 + B / X.p.Kpp ≤ X.p.nu0 * X.p.KB := by
    have := (div_le_iff₀ hν).mp hKB
    linarith
  have hTL : (X.p.q0 + B / X.p.Kpp) * L ≤ X.p.nu0 * X.p.KB * L :=
    mul_le_mul_of_nonneg_right hT hLpos.le
  have hBL : B ≤ B / X.p.Kpp * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hKpp]
    exact mul_le_mul_of_nonneg_left hLge hB
  have hlogle : Real.log ((X.p.q0 : ℝ) * K') ≤ |Real.log ((X.p.q0 : ℝ) * K')| := le_abs_self _
  have hMargin : Real.log 2 + (X.p.q0 : ℝ) * Real.log A + X.p.nu0 * Real.log q ≤ -C := by
    rw [hlogq, hlogA]
    have hνlog : X.p.nu0 * Real.log ((X.p.q0 : ℝ) * K') ≤
        X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| := mul_le_mul_of_nonneg_left hlogle hν.le
    have hexp : X.p.nu0 * (Real.log ((X.p.q0 : ℝ) * K') - X.p.KB * L) =
        X.p.nu0 * Real.log ((X.p.q0 : ℝ) * K') - X.p.nu0 * X.p.KB * L := by ring
    rw [hexp]
    have hexp2 : (X.p.q0 + B / X.p.Kpp) * L = (X.p.q0 : ℝ) * L + B / X.p.Kpp * L := by ring
    dsimp [B] at hBL hexp2 hTL
    linarith
  have hq1 : q ≤ 1 := by
    have hlogA0 : 0 ≤ (X.p.q0 : ℝ) * Real.log A := by rw [hlogA]; positivity
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hνq : X.p.nu0 * Real.log q ≤ 0 := by linarith
    have hlq : Real.log q ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      have := mul_pos hν hpos
      linarith
    exact (Real.log_nonpos_iff hqpos.le).mp hlq
  have hWord := Lane_q_s05_j34.priorHeavy_reference_word_bound X H K hLen
  have hTail' := Lane_q_s05_j34.array_some_heavy_block_tail5 X H K hDensity hLen X.p.nu0 q C
    hν.le hν hqpos.le hqpos hq1 hWord hMargin
  have hcoord := Lane_q_s05_j34.pi_pr_coordinate_event
    (fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K) K
    (fun Ar : X.Array K => ∃ i, X.p.nu0 * (X.p.q0 * X.p.typeSegs n K : ℕ) <
      (Lane_q_s05_j34.priorHeavyBlockCount5 X H K (Ar i) : ℝ))
  refine le_trans (FinProb.pr_mono _ _ _ ?_) (le_trans hcoord.le (hTail'.trans hTail))
  intro arrs hfail
  apply Lane_q_s05_j34.heavy_ref_failure_imp_some_block5 X H K (arrs K)
    (X.refSubsetOn H (fun c : Id × X.Ty => arrs c.2) (l, K) o) X.p.nu0 hν.le
  have hsumEq : (∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ X.refSubsetOn H (fun c : Id × X.Ty => arrs c.2) (l, K) o,
            X.blockIdx K j = some i then
          (Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
            Lane_q_s05_j34.priorHeavy5 X H K (arrs K i e.1 e.2)).card
        else 0) =
      ∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ X.refSubsetOn H (fun c : Id × X.Ty => arrs c.2) (l, K) o,
            X.blockIdx K j = some i then
          Lane_q_s05_j34.priorHeavyBlockCount5 X H K (arrs K i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs
    · unfold Lane_q_s05_j34.priorHeavyBlockCount5
      exact card_filter_prod (fun s e => Lane_q_s05_j34.priorHeavy5 X H K (arrs K i s e))
    · rfl
  rw [← hsumEq]
  exact lt_of_not_ge hfail

/-- The optional-hit part of the singleton test fails with probability at most `e^{-100}`: at a high role
with `j = J + 1`, each pool block hits the optional column with probability at least
`e^{-(a₁+δ) q₀ u_*}`, and the pool has `e^{K_h q₀ u_*} k_*/u_*` independent blocks. -/
theorem opt_fail_le (H : X.KeyHist) {cL cH : ℝ} (hgood : X.KeyGood5 H cL cH)
    (x : CubeVertex n) (hx : IsEvenRole x) {Id : Type} (l : Id)
    (hKh : X.p.a 1 + X.p.delta + 1 ≤ X.p.Kh) (hm : 1 < X.p.m n)
    (hused : 400 ≤ X.p.usedBlocks n) :
    (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
      (fun arrs : (∀ K : X.Ty, X.Array K) =>
        ¬ ∀ k, X.g.optionalKey (X.p.J n) x = some (.inl k) →
          X.p.usedBlocks n ≤ (X.hitSet (fun c : Id × X.Ty => arrs c.2)
            (l, X.g.evenType (X.p.J n) x) (X.lowCol H.2 k)).card) ≤
      Real.exp (-100) := by
  classical
  by_cases hsev : X.g.severity x = X.p.J n + 1
  swap
  · have hnone : X.g.optionalKey (X.p.J n) x = none := by
      simp [ChunkGeometry5.optionalKey, hsev]
    calc
      _ ≤ (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) =>
            X.blockLaw H K).pr (fun _ => False) := by
        apply FinProb.pr_mono
        intro arrs hfail
        apply hfail
        intro k hk
        rw [hnone] at hk
        cases hk
      _ = 0 := by simp [FinProb.pr]
      _ ≤ Real.exp (-100) := (Real.exp_pos _).le
  let K : X.Ty := X.g.evenType (X.p.J n) x
  let t : CubeVertex (X.p.m n) := X.g.sign x
  have hhigh : K.2.2 = none := by
    have hnot : ¬ X.g.severity x ≤ X.p.J n := by omega
    simp [K, ChunkGeometry5.evenType, hnot]
  have hType : X.TypeOccurs K := ⟨x, hx, rfl⟩
  have hoptEq : X.g.optionalKey (X.p.J n) x = some (X.optKeyOf K t) := by
    simp [ChunkGeometry5.optionalKey, hsev, Setup5.optKeyOf, K, ChunkGeometry5.evenType, t]
  have hOpt : X.OptOccurs K t := ⟨x, hx, rfl, hoptEq⟩
  have hsegs : X.p.typeSegs n K = X.p.uStarSeg n := by
    simp [Params5.typeSegs, hhigh]
  have hblocks : X.p.typeBlocks n K = X.p.poolBlocks n := by
    simp [Params5.typeBlocks, hhigh]
  have hprefix : X.p.typeSegs n K ≤ X.p.uSeg n ((X.optKeyOf K t).level + 1) := by
    rw [hsegs]
    simpa [Setup5.optKeyOf, HiddenKey5.level] using
      Lane_q_s05_hist1b.uStarSeg_le_uSeg_high5 X.p n
  have hhit := Lane_q_s05_j34.optional_block_hit_lower5 X H K t hgood.base_support hgood.step1
    hgood.step2 hType hOpt hhigh hprefix
  let y : Fin N := H.2 (X.optKeyOf K t)
    (Fin.cast (by simp [Setup5.optKeyOf, colLen5]) (0 : Fin 1))
  have hincl : ∀ arrs : (∀ K : X.Ty, X.Array K),
      (¬ ∀ k, X.g.optionalKey (X.p.J n) x = some (.inl k) →
        X.p.usedBlocks n ≤ (X.hitSet (fun c : Id × X.Ty => arrs c.2)
          (l, X.g.evenType (X.p.J n) x) (X.lowCol H.2 k)).card) →
      (Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) =>
        X.BlockHits K (arrs K i) y).card < X.p.usedBlocks n := by
    intro arrs hfail
    push_neg at hfail
    obtain ⟨k, hk, hlt⟩ := hfail
    rw [hoptEq] at hk
    have hk' : X.optKeyOf K t = .inl k := Option.some.inj hk
    have hkEq : k = (K.1, t, ⟨X.p.J n, Nat.lt_succ_self _⟩) := by
      simp only [Setup5.optKeyOf, Sum.inl.injEq] at hk'
      exact hk'.symm
    subst hkEq
    have hle := Lane_q_s05_j34.high_hitset_card_lower5 X arrs K hhigh y
    exact lt_of_le_of_lt hle hlt
  have hsum : ∑ _i : Fin (X.p.typeBlocks n K), (X.blockLaw H K).pr (fun z => X.BlockHits K z y) =
      (X.p.poolBlocks n : ℝ) * (X.blockLaw H K).pr (fun z => X.BlockHits K z y) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hblocks]
  have hq0 : (1 : ℝ) ≤ X.p.q0 := by exact_mod_cast X.p.hq0.1
  have hu : (1 : ℝ) ≤ X.p.uStarSeg n := by
    exact_mod_cast Lane_sol_s05_h5l.uStarSeg_positive X.p n hm
  have hqu : (1 : ℝ) ≤ (X.p.q0 : ℝ) * X.p.uStarSeg n := by nlinarith
  have hpool : Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) * X.p.usedBlocks n ≤
      (X.p.poolBlocks n : ℝ) := Nat.le_ceil _
  have hhit' : Real.exp (-((X.p.a 1 + X.p.delta) * ((X.p.q0 : ℝ) * X.p.uStarSeg n))) ≤
      (X.blockLaw H K).pr (fun z => X.BlockHits K z y) := by
    have e : Real.exp (-((X.p.a 1 + X.p.delta) * ((X.p.q0 : ℝ) * X.p.uStarSeg n))) =
        Real.exp (-((X.p.a 1 + X.p.delta) * ((X.p.q0 : ℝ) * X.p.typeSegs n K))) := by
      rw [hsegs]
    rw [e]
    exact hhit
  have hmean : 2 * (X.p.usedBlocks n : ℝ) ≤
      ∑ _i : Fin (X.p.typeBlocks n K), (X.blockLaw H K).pr (fun z => X.BlockHits K z y) := by
    rw [hsum]
    set u : ℝ := (X.p.q0 : ℝ) * X.p.uStarSeg n with hu_def
    have hU : (0 : ℝ) ≤ X.p.usedBlocks n := Nat.cast_nonneg _
    have hexpgap : Real.exp 1 ≤ Real.exp (X.p.Kh * u) * Real.exp (-((X.p.a 1 + X.p.delta) * u)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc
      2 * (X.p.usedBlocks n : ℝ) ≤ Real.exp 1 * X.p.usedBlocks n :=
        mul_le_mul_of_nonneg_right he2 hU
      _ ≤ (Real.exp (X.p.Kh * u) * Real.exp (-((X.p.a 1 + X.p.delta) * u))) * X.p.usedBlocks n :=
        mul_le_mul_of_nonneg_right hexpgap hU
      _ = (Real.exp (X.p.Kh * u) * X.p.usedBlocks n) * Real.exp (-((X.p.a 1 + X.p.delta) * u)) := by
        ring
      _ ≤ (X.p.poolBlocks n : ℝ) * (X.blockLaw H K).pr (fun z => X.BlockHits K z y) :=
        mul_le_mul hpool hhit' (Real.exp_pos _).le (Nat.cast_nonneg _)
  have hcoord := Lane_q_s05_j34.pi_pr_coordinate_event
    (fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K) K
    (fun Ar : X.Array K => (Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) =>
      X.BlockHits K (Ar i) y).card < X.p.usedBlocks n)
  have hlower := Lane_q_s05_j34.pi_pr_lower_count_le_exp
    (fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K) (fun _ z => X.BlockHits K z y)
    (X.p.usedBlocks n) hmean
  have h400 : (400 : ℝ) ≤ X.p.usedBlocks n := by exact_mod_cast hused
  calc
    _ ≤ (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) =>
          X.blockLaw H K).pr (fun arrs => (Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) =>
            X.BlockHits K (arrs K i) y).card < X.p.usedBlocks n) :=
      FinProb.pr_mono _ _ _ hincl
    _ = _ := hcoord
    _ ≤ Real.exp (-(X.p.usedBlocks n : ℝ) / 4) := hlower
    _ ≤ Real.exp (-100) := Real.exp_le_exp.mpr (by linarith)

/-- A singleton test at an even role fails with probability at most `2 e^{-100}`. -/
theorem single_fail_le (H : X.KeyHist) {cL cH : ℝ} (hgood : X.KeyGood5 H cL cH)
    (x : CubeVertex n) (hx : IsEvenRole x) {Id : Type} (l : Id) (C : ℝ) (hC : 0 ≤ C)
    (hTail : (X.p.typeBlocks n (X.g.evenType (X.p.J n) x) : ℝ) *
      Real.exp (-C * (X.p.typeSegs n (X.g.evenType (X.p.J n) x) : ℝ)) ≤ Real.exp (-100))
    (hKB : (X.p.q0 + (Real.log 2 + X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| + C) / X.p.Kpp) /
      X.p.nu0 ≤ X.p.KB)
    (hKh : X.p.a 1 + X.p.delta + 1 ≤ X.p.Kh) (hm : 1 < X.p.m n)
    (hused : 400 ≤ X.p.usedBlocks n) :
    (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
      (fun arrs : (∀ K : X.Ty, X.Array K) =>
        ¬ singleCond X H (fun c : Id × X.Ty => arrs c.2) l (X.g.evenType (X.p.J n) x)
          (X.g.optionalKey (X.p.J n) x)) ≤ 2 * Real.exp (-100) := by
  classical
  have hType : X.TypeOccurs (X.g.evenType (X.p.J n) x) := ⟨x, hx, rfl⟩
  have hH := heavy_fail_le X H hgood (X.g.evenType (X.p.J n) x) hType l
    (X.g.optionalKey (X.p.J n) x) C hC hTail hKB hm
  have hO := opt_fail_le X H hgood x hx l hKh hm hused
  calc
    _ ≤ _ := FinProb.pr_mono _ _ (fun arrs => _ ∨ _) (fun arrs h => by
        unfold singleCond at h
        exact not_and_or.mp h)
    _ ≤ _ := FinProb.pr_union_le _ _ _
    _ ≤ Real.exp (-100) + Real.exp (-100) := add_le_add hH hO
    _ = 2 * Real.exp (-100) := by ring

/-- The final union-bound arithmetic: `e^{2n}` sites, `O(n)` levels, tail `e^{-n^{10}/24}`. -/
theorem final_tail_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ S Hc : ℝ, 0 ≤ S → S ≤ Real.exp (2 * (n : ℝ)) → 0 ≤ Hc →
      Hc ≤ 5 * (n : ℝ) → S * Hc * Real.exp (-(n : ℝ) ^ 10 / 24) ≤ Real.exp (-Real.sqrt n) / 3 := by
  have hdecayEv : ∀ᶠ n : ℕ in atTop,
      30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) ≤ 1 := by
    have htend : Tendsto (fun n : ℕ => 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))))
        atTop (nhds 0) := by
      simpa only [Real.rpow_one, mul_zero, Function.comp_apply] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2 : ℝ)
          (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop).const_mul 30
    have hsmall := htend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with n hn
    exact (show 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) < 1 from hn).le
  filter_upwards [hdecayEv, eventually_ge_atTop 2] with n hdecay hn2
  intro S Hc hS hSle hHc hHcle
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hpow9 : (96 : ℝ) ≤ (n : ℝ) ^ (9 : ℕ) := by
    have h : (2 : ℝ) ^ (9 : ℕ) ≤ (n : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hn2R 9
    norm_num at h ⊢
    linarith
  have hpow10 : 96 * (n : ℝ) ≤ (n : ℝ) ^ 10 := by
    have := mul_le_mul_of_nonneg_right hpow9 hn0
    calc 96 * (n : ℝ) ≤ (n : ℝ) ^ (9 : ℕ) * n := this
      _ = (n : ℝ) ^ 10 := by ring
  have hsqrt : Real.sqrt (n : ℝ) ≤ n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hn0
    · nlinarith
  have hexpo : 2 * (n : ℝ) + -(n : ℝ) ^ 10 / 24 ≤ -(n : ℝ) + -Real.sqrt n := by
    nlinarith
  have hfactor : 15 * ((n : ℝ) * Real.exp (-(n : ℝ))) ≤ 1 := by
    have hexp : Real.exp (-(n : ℝ)) ≤ Real.exp (-(1 / 2 : ℝ) * (n : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hm : (n : ℝ) * Real.exp (-(n : ℝ)) ≤ (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp hn0
    nlinarith [Real.exp_pos (-(1 / 2 : ℝ) * (n : ℝ)), Real.exp_pos (-(n : ℝ))]
  have hE : 0 ≤ Real.exp (-(n : ℝ) ^ 10 / 24) := (Real.exp_pos _).le
  calc
    S * Hc * Real.exp (-(n : ℝ) ^ 10 / 24) ≤
        Real.exp (2 * (n : ℝ)) * (5 * (n : ℝ)) * Real.exp (-(n : ℝ) ^ 10 / 24) := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact mul_le_mul hSle hHcle hHc (Real.exp_pos _).le
    _ = 5 * (n : ℝ) * Real.exp (2 * (n : ℝ) + -(n : ℝ) ^ 10 / 24) := by
      rw [Real.exp_add]
      ring
    _ ≤ 5 * (n : ℝ) * Real.exp (-(n : ℝ) + -Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) (by positivity)
    _ = (5 * ((n : ℝ) * Real.exp (-(n : ℝ)))) * Real.exp (-Real.sqrt n) := by
      rw [Real.exp_add]
      ring
    _ ≤ (1 / 3) * Real.exp (-Real.sqrt n) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith
    _ = Real.exp (-Real.sqrt n) / 3 := by ring

end

end HypercubeRamsey.Setup5.Lane_opus_s05_j4
