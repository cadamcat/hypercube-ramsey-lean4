import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.Framework.LawLemmas

namespace HypercubeRamsey.Lane_q_s04_valid

open Classical OAI.HypercubeRamsey
open HypercubeRamsey.S04
open scoped BigOperators

private theorem eventually_rpow_gt {a c : ℝ} (ha : 0 < a) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, c < (n : ℝ) ^ a := by
  have h := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (h.eventually (Filter.eventually_gt_atTop c))

private theorem mask_width {N : ℕ} {μ : Law N} (S : Mask μ) {t : ℝ}
    (hμ : μ.WidthLE t) : (maskLaw S).WidthLE (t + Real.log 2) := by
  have hm := mask_mass_pos S
  have hhalf : (1 / 2 : ℝ) ≤ ∑ x ∈ S.1, μ.w x := S.2.2
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog' : -Real.log 2 ≤ Real.log (∑ x ∈ S.1, μ.w x) := by
    rw [← hloghalf]
    exact hlog
  have hbound : t - Real.log (∑ x ∈ S.1, μ.w x) ≤ t + Real.log 2 := by linarith
  exact (Law.WidthLE.restrict hμ hm).mono hbound

private theorem mask_supported {N : ℕ} {μ : Law N} {S : Mask μ} {X : Finset (Fin N)}
    (hμ : μ.SupportedIn X) : (maskLaw S).SupportedIn X := by
  intro x hx
  by_cases hxS : x ∈ S.1
  · simp [maskLaw, Law.restrict, hxS, hμ x hx]
  · simp [maskLaw, Law.restrict, hxS]

private theorem restrict_supported {N : ℕ} {μ : Law N} {A X : Finset (Fin N)}
    (hm : 0 < ∑ x ∈ A, μ.w x) (hμ : μ.SupportedIn X) :
    (μ.restrict A hm).SupportedIn X := by
  intro x hx
  by_cases hxA : x ∈ A
  · simp [Law.restrict, hxA, hμ x hx]
  · simp [Law.restrict, hxA]

private theorem finProb_ext {Ω : Type*} [Fintype Ω] {P Q : FinProb Ω}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk w hw hs =>
    cases Q with
    | mk w' hw' hs' =>
      have hwEq : w = w' := funext h
      subst w'
      congr

private theorem law_cond_eq_restrict {N : ℕ} (P : Law N) (A : Fin N → Prop)
    (h : 0 < P.pr A) :
    P.cond A h = P.restrict (Finset.univ.filter A) (by
      simpa [FinProb.pr, Finset.sum_filter] using h) := by
  classical
  let S := Finset.univ.filter A
  have hmass : 0 < ∑ x ∈ S, P.w x := by
    simpa [S, FinProb.pr, Finset.sum_filter] using h
  have hpr : P.pr A = ∑ x ∈ S, P.w x := by
    simp [S, FinProb.pr, Finset.sum_filter]
  apply finProb_ext
  intro x
  by_cases hx : A x
  · simp [FinProb.cond, Law.restrict, S, hx, hpr]
  · simp [FinProb.cond, Law.restrict, S, hx]

private theorem cond_expect_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (h : 0 < P.pr A) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ x, A x → f x ≤ c) : (P.cond A h).expect f ≤ c := by
  unfold FinProb.expect
  calc
    (∑ x, (P.cond A h).w x * f x) ≤
        ∑ x, (P.cond A h).w x * c := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hA : A x
      · exact mul_le_mul_of_nonneg_left (hf x hA) ((P.cond A h).nonneg x)
      · have hzero : (P.cond A h).w x = 0 := by simp [FinProb.cond, hA]
        simp [hzero]
    _ = c := by
      rw [← Finset.sum_mul, (P.cond A h).sum_eq_one]
      ring

private theorem cond_expect_gt {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    (h : 0 < P.pr A) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ x, A x → c < f x) : c < (P.cond A h).expect f := by
  classical
  let R := P.cond A h
  have hsome : ∃ x, 0 < R.w x := by
    by_contra hnone
    have hzero : ∀ x, R.w x = 0 := by
      intro x
      have hx : ¬ 0 < R.w x := by
        intro hx
        exact hnone ⟨x, hx⟩
      exact le_antisymm (le_of_not_gt hx) (R.nonneg x)
    have hsum : (∑ x, R.w x) = 0 := Finset.sum_eq_zero (fun x hx => hzero x)
    rw [R.sum_eq_one] at hsum
    norm_num at hsum
  obtain ⟨x, hxpos⟩ := hsome
  have hxA : A x := by
    by_contra hnot
    have hz : R.w x = 0 := by simp [R, FinProb.cond, hnot]
    linarith
  have htermpos : 0 < R.w x * (f x - c) :=
    mul_pos hxpos (sub_pos.mpr (hf x hxA))
  have htermnon : ∀ y, 0 ≤ R.w y * (f y - c) := by
    intro y
    by_cases hy : A y
    · exact mul_nonneg (R.nonneg y) (sub_nonneg.mpr (le_of_lt (hf y hy)))
    · have hz : R.w y = 0 := by simp [R, FinProb.cond, hy]
      simp [hz]
  have hsumpos : 0 < ∑ y, R.w y * (f y - c) := by
    exact lt_of_lt_of_le htermpos
      (Finset.single_le_sum (fun y hy => htermnon y) (Finset.mem_univ x))
  have hdiff : R.expect f - c = ∑ y, R.w y * (f y - c) := by
    unfold FinProb.expect
    calc
      (∑ y, R.w y * f y) - c =
          (∑ y, R.w y * f y) - (∑ y, R.w y * c) := by
            rw [← Finset.sum_mul, R.sum_eq_one]
            ring
      _ = ∑ y, (R.w y * f y - R.w y * c) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ y, R.w y * (f y - c) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
  linarith

private theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

private theorem pr_exists_finset_le_sum {Ω α : Type*} [Fintype Ω] [Fintype α]
    [DecidableEq α] (P : FinProb Ω) (s : Finset α) (Q : α → Ω → Prop) :
    P.pr (fun ω => ∃ a ∈ s, Q a ω) ≤ ∑ a ∈ s, P.pr (Q a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold FinProb.pr
      simp
  | @insert a s ha ih =>
      have hEq : (fun ω => ∃ b ∈ insert a s, Q b ω) =
          (fun ω => Q a ω ∨ ∃ b ∈ s, Q b ω) := by
        funext ω
        simp [ha]
      calc
        P.pr (fun ω => ∃ b ∈ insert a s, Q b ω) =
            P.pr (fun ω => Q a ω ∨ ∃ b ∈ s, Q b ω) := by rw [hEq]
        _ ≤ P.pr (Q a) + P.pr (fun ω => ∃ b ∈ s, Q b ω) :=
          FinProb.pr_union P _ _
        _ ≤ P.pr (Q a) + ∑ b ∈ s, P.pr (Q b) := add_le_add (le_rfl) ih
        _ = ∑ b ∈ insert a s, P.pr (Q b) := by simp [ha, add_comm]

private def OwnRatioFailure {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n))
    (c : Loc β γ n) (W : Tuples β γ n N) : Prop :=
  key β γ n u.1 ∈ Zset β γ u ∧
    (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
      ratioThr β γ u (key β γ n u.1) *
        (maskLaw (ym u)).pr (HitsBut E G W D (Zset β γ u) c (key β γ n u.1))

private theorem valid_prob_bound_of_factor {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (hExposure : ExposureLow M tag) (hOwn : OwnRatio M tag)
    (hfactor : (1 + (setBd β γ n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) ≤
      Real.exp (-(n : ℝ) ^ (omega4 β γ / 5))) : ValidProb M tag := by
  classical
  intro xm ym u D hDpos hDcard
  let P := tupleLaw M tag xm
  let A : Tuples β γ n N → Prop := LowFail M tag ym u D
  let B : Tuples β γ n N → Prop := fun W =>
    ∃ c ∈ D, OwnRatioFailure M tag ym u D c W
  have hCover : ∀ W, ¬ Valid M tag u ((xm, ym), W) D → A W ∨ B W := by
    intro W hnotValid
    by_cases hlow : A W
    · exact Or.inl hlow
    · right
      by_contra hnone
      have hMass :
          Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) *
            ((Zset β γ u).card : ℝ))) ≤
            (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) := by
        by_contra hbad
        have hlt := lt_of_not_ge hbad
        exact hlow (Or.inl hlt)
      have hRatio : ∀ c ∈ D, ∀ κ ∈ Zset β γ u,
          ratioThr β γ u κ *
              (maskLaw (ym u)).pr (HitsBut E G W D (Zset β γ u) c κ) ≤
            (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) := by
        intro c hc κ hκ
        by_cases heq : κ = key β γ n u.1
        · subst κ
          by_contra hbad
          have hlt := lt_of_not_ge hbad
          exact hnone ⟨c, hc, hκ, hlt⟩
        · by_contra hbad
          have hlt := lt_of_not_ge hbad
          exact hlow (Or.inr ⟨c, hc, κ, hκ, heq, hlt⟩)
      exact hnotValid ⟨hDpos, hDcard, hMass, hRatio⟩
  have hBprob : P.pr B ≤ ∑ c ∈ D, P.pr (OwnRatioFailure M tag ym u D c) := by
    exact pr_exists_finset_le_sum P D (OwnRatioFailure M tag ym u D)
  have hsum :
      (∑ c ∈ D, P.pr (OwnRatioFailure M tag ym u D c)) ≤
        (D.card : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
    calc
      (∑ c ∈ D, P.pr (OwnRatioFailure M tag ym u D c)) ≤
          ∑ c ∈ D, Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
            apply Finset.sum_le_sum
            intro c hc
            by_cases hmem : key β γ n u.1 ∈ Zset β γ u
            · change P.pr (fun W => key β γ n u.1 ∈ Zset β γ u ∧
                  (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
                    ratioThr β γ u (key β γ n u.1) *
                      (maskLaw (ym u)).pr
                        (HitsBut E G W D (Zset β γ u) c (key β γ n u.1))) ≤ _
              simp only [hmem, true_and]
              simpa [P] using hOwn xm ym u D c hDpos hDcard hc hmem
            · have hzero : P.pr (OwnRatioFailure M tag ym u D c) = 0 := by
                unfold FinProb.pr
                apply Finset.sum_eq_zero
                intro W hW
                simp [OwnRatioFailure, hmem]
              rw [hzero]
              exact Real.exp_nonneg _
      _ = (D.card : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
            simp [mul_comm]
  have hDcardReal : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by exact_mod_cast hDcard
  have hsum' :
      (∑ c ∈ D, P.pr (OwnRatioFailure M tag ym u D c)) ≤
        (setBd β γ n : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) :=
    hsum.trans (mul_le_mul_of_nonneg_right hDcardReal (Real.exp_nonneg _))
  have hbad :
      P.pr (fun W => ¬ Valid M tag u ((xm, ym), W) D) ≤
        Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) +
          (setBd β γ n : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
    calc
      P.pr (fun W => ¬ Valid M tag u ((xm, ym), W) D) ≤ P.pr (fun W => A W ∨ B W) :=
        pr_mono P _ _ (fun W hbad => hCover W hbad)
      _ ≤ P.pr A + P.pr B := FinProb.pr_union P A B
      _ ≤ Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) +
            ∑ c ∈ D, P.pr (OwnRatioFailure M tag ym u D c) := by
          exact add_le_add (hExposure xm ym u D hDpos hDcard) hBprob
      _ ≤ _ := add_le_add (le_rfl) hsum'
  have hfactor' :
      Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) +
          (setBd β γ n : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) ≤
        Real.exp (-(n : ℝ) ^ (omega4 β γ / 5)) := by
    calc
      Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) +
          (setBd β γ n : ℝ) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) =
        (1 + (setBd β γ n : ℝ)) *
          Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by ring
      _ ≤ Real.exp (-(n : ℝ) ^ (omega4 β γ / 5)) := hfactor
  simpa [P, mul_comm, add_comm, add_left_comm, add_assoc] using hbad.trans hfactor'

private theorem valid_prob_factor_eventually (β γ : ℝ) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (1 + (setBd β γ n : ℝ)) * Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) ≤
        Real.exp (-(n : ℝ) ^ (omega4 β γ / 5)) := by
  let b := bH β γ
  let c := omega4 β γ / 5
  have hω : 0 < omega4 β γ := omega4_pos hβ hγ
  have hb : 0 < b := by dsimp [b, bH]; positivity
  have hcDiff : 0 < c - b := by
    dsimp [c, b, bH]
    nlinarith
  obtain ⟨n₀, hnPow⟩ := eventually_rpow_gt (c := 5) hcDiff
  refine ⟨n₀ + 1, ?_⟩
  intro n hn
  have hnBase : n₀ ≤ n := by omega
  have hnOne : 1 ≤ n := by omega
  have hnPos : 0 < n := by omega
  let x : ℝ := n
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hnPos
  have hxOne : 1 ≤ x := by dsimp [x]; exact_mod_cast hnOne
  have hPower : 5 < x ^ (c - b) := by simpa [x] using hnPow n hnBase
  have hbPower : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  have hbPowerOne : 1 ≤ x ^ b := Real.one_le_rpow hxOne hb.le
  have hsmall : 3 * x ^ b + 2 ≤ 5 * x ^ b := by nlinarith [hbPowerOne]
  have hlarge : 5 * x ^ b ≤ x ^ (c - b) * x ^ b :=
    mul_le_mul_of_nonneg_right hPower.le hbPower.le
  have hpowCmp : 3 * x ^ b + 2 ≤ x ^ c := by
    calc
      3 * x ^ b + 2 ≤ 5 * x ^ b := hsmall
      _ ≤ x ^ (c - b) * x ^ b := hlarge
      _ = x ^ ((c - b) + b) := (Real.rpow_add hx (c - b) b).symm
      _ = x ^ c := by congr 1 <;> ring
  have hceil : (setBd β γ n : ℝ) < 3 * x ^ b + 1 := by
    change (⌈3 * x ^ b⌉₊ : ℝ) < 3 * x ^ b + 1
    exact Nat.ceil_lt_add_one (by positivity)
  have hT : 1 + (setBd β γ n : ℝ) ≤ x ^ c := by
    have hT' : 1 + (setBd β γ n : ℝ) < 3 * x ^ b + 2 := by linarith
    exact hT'.le.trans hpowCmp
  have hExp : x ^ c ≤ Real.exp (x ^ c) := by
    have h := Real.add_one_le_exp (x ^ c)
    linarith
  have hFactorX :
      (1 + (setBd β γ n : ℝ)) * Real.exp (-2 * x ^ c) ≤ Real.exp (-x ^ c) := by
    calc
      (1 + (setBd β γ n : ℝ)) * Real.exp (-2 * x ^ c) ≤
          Real.exp (x ^ c) * Real.exp (-2 * x ^ c) :=
        mul_le_mul_of_nonneg_right (hT.trans hExp) (Real.exp_nonneg _)
      _ = Real.exp (-x ^ c) := by rw [← Real.exp_add]; congr 1 <;> ring
  simpa [x, c] using hFactorX

theorem valid_prob_core (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      ExposureLow M tag → OwnRatio M tag → ValidProb M tag := by
  obtain ⟨n₀, hfactor⟩ := valid_prob_factor_eventually β γ hβ hβγ hγ
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y M tag hExposure hOwn
  exact valid_prob_bound_of_factor M tag hExposure hOwn (hfactor n hn)

private theorem expect_ge_of_supported {N : ℕ} (P support : Law N) (f : Fin N → ℝ) (c : ℝ)
    (hsupp : ∀ x, support.w x = 0 → P.w x = 0)
    (hf : ∀ x, support.w x ≠ 0 → c ≤ f x) : c ≤ P.expect f := by
  unfold FinProb.expect
  have hterm : ∀ x, P.w x * c ≤ P.w x * f x := by
    intro x
    by_cases hs : support.w x = 0
    · simp [hsupp x hs]
    · exact mul_le_mul_of_nonneg_left (hf x hs) (P.nonneg x)
  calc
      c = (∑ x, P.w x) * c := by rw [P.sum_eq_one]; ring
    _ = ∑ x, P.w x * c := by rw [Finset.sum_mul]
    _ ≤ ∑ x, P.w x * f x := Finset.sum_le_sum fun x hx => hterm x

private theorem rowDeg_le_one {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x : Fin N) (ν : Law N) : rowDeg E G x ν ≤ 1 := by
  classical
  unfold rowDeg
  calc
    (∑ y, ν.w y * (if Hits E G x y then 1 else 0)) ≤ ∑ y, ν.w y := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hxy : Hits E G x y
      · simp [hxy]
      · simp [hxy]
        exact ν.nonneg y
    _ = 1 := ν.sum_eq_one

private theorem mask_zero_of_zero {N : ℕ} {μ : Law N} (S : Mask μ) (x : Fin N)
    (hμ : μ.w x = 0) : (maskLaw S).w x = 0 := by
  by_cases hx : x ∈ S.1
  · exact False.elim (S.2.1 x hx hμ)
  · simp [maskLaw, Law.restrict, hx]

private theorem mask_weight_le_two {N : ℕ} {μ : Law N} (S : Mask μ) (x : Fin N) :
    (maskLaw S).w x ≤ 2 * μ.w x := by
  by_cases hx : x ∈ S.1
  · have hm := mask_mass_pos S
    have hfac : 1 ≤ 2 * (∑ y ∈ S.1, μ.w y) := by linarith [S.2.2]
    have hmul : μ.w x ≤ 2 * (∑ y ∈ S.1, μ.w y) * μ.w x := by
      have h := mul_le_mul_of_nonneg_right hfac (μ.nonneg x)
      nlinarith [h]
    have hweight : (maskLaw S).w x = μ.w x / (∑ y ∈ S.1, μ.w y) := by
      simp [maskLaw, Law.restrict, hx]
    rw [hweight]
    apply (div_le_iff₀ hm).2
    nlinarith [hmul]
  · simp [maskLaw, Law.restrict, hx, μ.nonneg x]

private noncomputable def residualLaw {N : ℕ} (μ P : Law N)
    (hP : ∀ x, P.w x ≤ 2 * μ.w x) : Law N where
  w x := 2 * μ.w x - P.w x
  nonneg x := by linarith [hP x]
  sum_eq_one := by
    calc
      (∑ x, (2 * μ.w x - P.w x)) = (∑ x, 2 * μ.w x) - ∑ x, P.w x :=
        by rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ x, μ.w x) - ∑ x, P.w x := by rw [← Finset.mul_sum]
      _ = 1 := by rw [μ.sum_eq_one, P.sum_eq_one]; norm_num

private theorem residual_width {N : ℕ} {μ P : Law N} {s : ℝ}
    (hμ : μ.WidthLE s) (hP : ∀ x, P.w x ≤ 2 * μ.w x) :
    (residualLaw μ P hP).WidthLE (s + Real.log 2) := by
  intro x
  calc
    (residualLaw μ P hP).w x ≤ 2 * μ.w x := by
      dsimp [residualLaw]
      linarith [P.nonneg x]
    _ ≤ 2 * (Real.exp s / N) := mul_le_mul_of_nonneg_left (hμ x) (by norm_num)
    _ = Real.exp (s + Real.log 2) / N := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (2 : ℝ) > 0)]
      ring

private theorem residual_supported {N : ℕ} {μ P : Law N} {hP : ∀ x, P.w x ≤ 2 * μ.w x}
    (hzero : ∀ x, μ.w x = 0 → P.w x = 0) :
    ∀ x, μ.w x = 0 → (residualLaw μ P hP).w x = 0 := by
  intro x hx
  simp [residualLaw, hzero x hx, hx]

private theorem cond_width_of_event {N : ℕ} (P : Law N) (A : Fin N → Prop)
    {t q : ℝ} (h : 0 < P.pr A) (hwidth : P.WidthLE t)
    (hbudget : -Real.log (P.pr A) ≤ q) : Law.WidthLE (P.cond A h) (t + q) := by
  classical
  let S := Finset.univ.filter A
  have hmass : 0 < ∑ x ∈ S, P.w x := by
    simpa [S, FinProb.pr, Finset.sum_filter] using h
  have hpr : P.pr A = ∑ x ∈ S, P.w x := by
    simp [S, FinProb.pr, Finset.sum_filter]
  have heq : P.cond A h = P.restrict S hmass := by
    simpa [S] using law_cond_eq_restrict P A h
  have hw := Law.WidthLE.restrict hwidth hmass
  rw [heq]
  apply Law.WidthLE.mono hw
  rw [← hpr]
  linarith

private theorem expect_indicator {N : ℕ} (P : Law N) (A : Fin N → Prop) :
    P.expect (fun x => if A x then (1 : ℝ) else 0) = P.pr A := by
  classical
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> simp [hA]

private theorem dens_eq_expect_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) : dens E G μ ν = μ.expect (fun x => rowDeg E G x ν) := by
  classical
  unfold dens FinProb.expect rowDeg
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem dens_eq_expect_colDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) : dens E G μ ν = ν.expect (fun y => colDeg E G μ y) := by
  classical
  unfold dens FinProb.expect colDeg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem dens_dirac_eq_colDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : dens E G μ (Law.dirac y) = colDeg E G μ y := by
  rw [dens_eq_expect_colDeg]
  simp [FinProb.expect, Law.dirac]

private theorem dens_linear_first {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ P σ ν : Law N) (hweights : ∀ x, P.w x + σ.w x = 2 * μ.w x) :
    dens E G P ν + dens E G σ ν = 2 * dens E G μ ν := by
  rw [dens_eq_expect_rowDeg E G P ν, dens_eq_expect_rowDeg E G σ ν]
  unfold FinProb.expect
  calc
    (∑ x, P.w x * rowDeg E G x ν) + ∑ x, σ.w x * rowDeg E G x ν =
        ∑ x, (P.w x + σ.w x) * rowDeg E G x ν := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = 2 * ∑ x, μ.w x * rowDeg E G x ν := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [hweights x]
          ring
    _ = 2 * dens E G μ ν := by
      rw [dens_eq_expect_rowDeg]
      rfl

theorem entry_low_core (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y), NoPure β γ n N E G X Y → EntryLow M := by
  let ω := omega4 β γ
  have hω : 0 < ω := omega4_pos hβ hγ
  have hωβ : ω ≤ β / 1000 := by
    dsimp [ω, omega4]
    exact div_le_div_of_nonneg_right (min_le_left β (1 - γ)) (by norm_num)
  have hα : 0 < β - ω / 2 := by dsimp [ω]; nlinarith
  have hαβ : β - ω / 2 ≤ β := by nlinarith
  obtain ⟨nA, hnA⟩ := eventually_rpow_gt (a := β - ω / 2) (c := 4 * Real.log 2) hα
  obtain ⟨nB, hnB⟩ := eventually_rpow_gt (a := β) (c := 4 * Real.log 2) hβ
  refine ⟨max nA nB, ?_⟩
  intro n hn N E G X Y M hNoPure i S η hηsupp hηwidth
  have hnA' : 4 * Real.log 2 < (n : ℝ) ^ (β - ω / 2) := by
    simpa [ω] using hnA n (le_trans (le_max_left _ _) hn)
  have hnB' : 4 * Real.log 2 < (n : ℝ) ^ β := hnB n (le_trans (le_max_right _ _) hn)
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp [Real.zero_rpow (ne_of_gt hα)] at hnA'
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hpowle : (n : ℝ) ^ (β - ω / 2) ≤ (n : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hnR hαβ
  let P := maskLaw S
  let Bad : Fin N → Prop := fun x => rowDeg E G x η < Real.exp (-capL β γ n)
  by_contra hbound
  have hlarge : Real.exp (-((n : ℝ) ^ (β - ω / 2)) / 4) < P.pr Bad := lt_of_not_ge hbound
  have hmass : 0 < P.pr Bad := lt_trans (Real.exp_pos _) hlarge
  let A := Finset.univ.filter Bad
  have hmass' : 0 < ∑ x ∈ A, P.w x := by
    simpa [A, FinProb.pr, Finset.sum_filter] using hmass
  have hpr : P.pr Bad = ∑ x ∈ A, P.w x := by
    simp [A, FinProb.pr, Finset.sum_filter]
  have hcondEq : P.cond Bad hmass = P.restrict A hmass' := by
    simpa [A] using law_cond_eq_restrict P Bad hmass
  let μ' : Law N := P.cond Bad hmass
  have hlog : -Real.log (P.pr Bad) < (n : ℝ) ^ (β - ω / 2) / 4 := by
    have h := Real.log_lt_log (Real.exp_pos _) hlarge
    rw [Real.log_exp] at h
    linarith
  have hlogA : -Real.log (∑ x ∈ A, P.w x) < (n : ℝ) ^ (β - ω / 2) / 4 := by
    rw [← hpr]
    exact hlog
  have hmaskwidth : P.WidthLE (M.sX i + Real.log 2) := mask_width S (M.prep i).2.2.2.2.1
  have hwidthP4 : μ'.WidthLE (M.sX i + (n : ℝ) ^ (β - ω / 2) / 2) := by
    change Law.WidthLE (P.cond Bad hmass) _
    rw [hcondEq]
    have hw := Law.WidthLE.restrict hmaskwidth hmass'
    apply Law.WidthLE.mono hw
    have hlog2 : Real.log 2 ≤ (n : ℝ) ^ (β - ω / 2) / 4 := by nlinarith
    have hmassWidth : Real.log 2 - Real.log (∑ x ∈ A, P.w x) ≤
        (n : ℝ) ^ (β - ω / 2) / 2 := by linarith
    linarith
  have hwidthNoPure : μ'.WidthLE (2 * (n : ℝ) ^ β) := by
    change Law.WidthLE (P.cond Bad hmass) _
    rw [hcondEq]
    have hw := Law.WidthLE.restrict hmaskwidth hmass'
    apply Law.WidthLE.mono hw
    have hlog2 : Real.log 2 ≤ (n : ℝ) ^ β / 4 := by nlinarith
    calc
      M.sX i + Real.log 2 - Real.log (∑ x ∈ A, P.w x) ≤
          M.sX i + (n : ℝ) ^ β / 2 := by
            have hs : M.sX i + Real.log 2 - Real.log (∑ x ∈ A, P.w x) ≤
                M.sX i + Real.log 2 + (n : ℝ) ^ (β - ω / 2) / 4 := by linarith
            have hr : (n : ℝ) ^ (β - ω / 2) ≤ (n : ℝ) ^ β := hpowle
            linarith
      _ ≤ 3 / 2 * (n : ℝ) ^ β + (n : ℝ) ^ β / 2 := by
        exact add_le_add (M.prep i).2.1 le_rfl
      _ = 2 * (n : ℝ) ^ β := by ring
  have hsuppP : P.SupportedIn X := mask_supported (M.μ_supp i)
  have hsuppMu' : μ'.SupportedIn X := by
    change Law.SupportedIn (P.cond Bad hmass) X
    rw [hcondEq]
    exact restrict_supported hmass' hsuppP
  have hden : dens E G μ' η ≤ Real.exp (-capL β γ n) := by
    rw [dens_eq_expect_rowDeg]
    apply cond_expect_le P Bad hmass (fun x => rowDeg E G x η) (Real.exp (-capL β γ n))
    intro x hx
    exact le_of_lt hx
  have hNoPure' := hNoPure μ' η hwidthNoPure hηwidth hden
  exact hNoPure' ⟨hsuppMu', hηsupp⟩

set_option maxHeartbeats 1000000 in
theorem entry_own_core (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y), EntryOwn M := by
  let ω := omega4 β γ
  have hω : 0 < ω := omega4_pos hβ hγ
  have hωβ : ω ≤ β / 1000 := by
    dsimp [ω, omega4]
    exact div_le_div_of_nonneg_right (min_le_left β (1 - γ)) (by norm_num)
  have hα : 0 < β - ω / 2 := by dsimp [ω]; nlinarith
  have hτ : 0 < β - 7 * ω / 10 := by dsimp [ω]; nlinarith
  have hτ₂ : 0 < 2 * ω / 15 := by positivity
  obtain ⟨nA, hnA⟩ := eventually_rpow_gt (a := β - ω / 2) (c := 4 * Real.log 2) hα
  obtain ⟨nT, hnT⟩ := eventually_rpow_gt (a := β - 7 * ω / 10) (c := 8) hτ
  obtain ⟨nD, hnD⟩ := eventually_rpow_gt (a := 2 * ω / 15) (c := 2) hτ₂
  refine ⟨max nA (max nT nD), ?_⟩
  intro n hn N E G X Y M i S η hηsupp hηwidth
  have hr : 4 * Real.log 2 < (n : ℝ) ^ (β - ω / 2) := by
    simpa [ω] using hnA n (le_trans (le_max_left _ _) hn)
  have hτn : 8 < (n : ℝ) ^ (β - 7 * ω / 10) := by
    simpa [ω] using hnT n (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn))
  have hδpow : 2 < (n : ℝ) ^ (2 * ω / 15) := by
    apply hnD n
    exact le_trans (le_max_right nT nD)
      (le_trans (le_max_right nA (max nT nD)) hn)
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp [Real.zero_rpow (ne_of_gt hα)] at hr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnrpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hωposPow : 0 < (n : ℝ) ^ (ω / 5) := Real.rpow_pos_of_pos hnrpos _
  let r := (n : ℝ) ^ (β - ω / 2)
  let δ := (n : ℝ) ^ (-(ω / 5))
  let δ' := (n : ℝ) ^ (-(ω / 3))
  have hδTarget : δ = (n : ℝ) ^ (-ω / 5) := by
    dsimp [δ]
    congr 1
    ring
  have hδ'Target : δ' = (n : ℝ) ^ (-ω / 3) := by
    dsimp [δ']
    congr 1
    ring
  have hrpow : r = (n : ℝ) ^ (β - 7 * ω / 10) * (n : ℝ) ^ (ω / 5) := by
    dsimp [r]
    rw [show β - ω / 2 = (β - 7 * ω / 10) + ω / 5 by ring, Real.rpow_add hnrpos]
  have hratioPow : 2 * (n : ℝ) ^ (ω / 5) < r / 4 := by
    rw [hrpow]
    have hmul := mul_lt_mul_of_pos_right hτn hωposPow
    nlinarith
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hnrpos _
  have hδInv : (n : ℝ) ^ (-(ω / 5)) = ((n : ℝ) ^ (ω / 5))⁻¹ := by
    exact Real.rpow_neg hnrpos.le (ω / 5)
  have hExpLinear : 1 + r / 4 ≤ Real.exp (r / 4) := by
    have h := Real.add_one_le_exp (r / 4)
    nlinarith
  have htailHalf : Real.exp (-r / 4) ≤ δ / 2 := by
    have hden : 0 < 1 + r / 4 := by positivity
    have hpowden : 0 < (n : ℝ) ^ (ω / 5) := hωposPow
    have hInv₁ : 1 / Real.exp (r / 4) ≤ 1 / (1 + r / 4) :=
      one_div_le_one_div_of_le hden hExpLinear
    have hInv₂ : 1 / (1 + r / 4) ≤ 1 / (2 * (n : ℝ) ^ (ω / 5)) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) hpowden) (by linarith [hratioPow])
    dsimp [δ, r]
    rw [show -((n : ℝ) ^ (β - ω / 2)) / 4 = -(((n : ℝ) ^ (β - ω / 2)) / 4) by ring,
      Real.exp_neg, hδInv]
    calc
      (Real.exp ((n : ℝ) ^ (β - ω / 2) / 4))⁻¹ ≤
          (1 + (n : ℝ) ^ (β - ω / 2) / 4)⁻¹ := by simpa [one_div] using hInv₁
      _ ≤ (2 * (n : ℝ) ^ (ω / 5))⁻¹ := by simpa [one_div] using hInv₂
      _ = ((n : ℝ) ^ (ω / 5))⁻¹ / 2 := by field_simp [ne_of_gt hpowden]
  have htail : Real.exp (-r / 4) ≤ δ := by
    calc
      Real.exp (-r / 4) ≤ δ / 2 := htailHalf
      _ ≤ δ := by linarith [hδpos]
  have hlog2 : Real.log 2 ≤ r / 4 := by dsimp [r]; nlinarith
  have hlog2' : Real.log 2 ≤ (n : ℝ) ^ (β - ω / 2) / 4 := by
    simpa [r] using hlog2
  have hrβ : r ≤ (n : ℝ) ^ β := by
    dsimp [r]
    apply Real.rpow_le_rpow_of_exponent_le hnR
    nlinarith [hω]
  have hsmallPow : (n : ℝ) ^ (-(2 * ω / 15)) < 1 / 2 := by
    rw [Real.rpow_neg hnrpos.le]
    simpa [one_div] using (one_div_lt_one_div_of_lt (by norm_num) hδpow)
  have hδ'δ : δ' ≤ δ / 2 := by
    have heq : δ' = δ * (n : ℝ) ^ (-(2 * ω / 15)) := by
      dsimp [δ', δ]
      calc
        (n : ℝ) ^ (-(ω / 3)) =
            (n : ℝ) ^ ((-(ω / 5)) + (-(2 * ω / 15))) := by
              congr 1
              ring
        _ = (n : ℝ) ^ (-(ω / 5)) * (n : ℝ) ^ (-(2 * ω / 15)) :=
          Real.rpow_add hnrpos _ _
    rw [heq]
    calc
      δ * (n : ℝ) ^ (-(2 * ω / 15)) ≤ δ * (1 / 2) :=
        mul_le_mul_of_nonneg_left (le_of_lt hsmallPow) hδpos.le
      _ = δ / 2 := by ring
  rcases M.prep i with ⟨hsXlo, hsXhi, hsYlo, hsYhi, hμwidth, hνwidth,
    hpLower, hcolumn, hupper⟩
  let P := maskLaw S
  let q : Fin N → ℝ := fun x => rowDeg E G x η
  let a : ℝ := M.pd i - 1 / 2
  have ha : (n : ℝ) ^ (-h4 β γ) ≤ a := by
    dsimp [a]
    linarith [hpLower]
  have haPos : 0 < a := lt_of_lt_of_le (Real.rpow_pos_of_pos hnrpos _) ha
  have hmaskwidth : P.WidthLE (M.sX i + Real.log 2) := mask_width S hμwidth
  have hPbound : ∀ x, P.w x ≤ 2 * (M.μ i).w x := fun x => mask_weight_le_two S x
  let σ := residualLaw (M.μ i) P hPbound
  have hσwidth : σ.WidthLE (M.sX i + Real.log 2) := residual_width hμwidth hPbound
  have hmaskzero : ∀ x, (M.μ i).w x = 0 → P.w x = 0 := mask_zero_of_zero S
  have hσzero : ∀ x, (M.μ i).w x = 0 → σ.w x = 0 :=
    residual_supported hmaskzero
  have hσsupport : ∀ x, (M.μ i).w x = 0 → σ.w x = 0 := hσzero
  have hηwidthP4 : η.WidthLE (M.sY i + (n : ℝ) ^ (γ - ω / 2) / 2) := by
    apply Law.WidthLE.mono hηwidth
    have hpow : 0 ≤ (n : ℝ) ^ (γ - ω / 2) := (Real.rpow_pos_of_pos hnrpos _).le
    nlinarith
  have hσwidthP4 : σ.WidthLE (M.sX i + (n : ℝ) ^ (β - ω / 2) / 2) := by
    apply Law.WidthLE.mono hσwidth
    nlinarith [hlog2']
  have hPwidthP4 : P.WidthLE (M.sX i + (n : ℝ) ^ (β - ω / 2) / 2) := by
    apply Law.WidthLE.mono hmaskwidth
    nlinarith [hlog2']
  have hupperσ : dens E G σ η ≤ M.pd i + δ' := by
    have h := hupper σ η hσsupport hηsupp hσwidthP4 hηwidthP4
    rw [hδ'Target]
    exact h
  have hlowerμ : M.pd i - (n : ℝ) ^ (-ω / 5) ≤ dens E G (M.μ i) η := by
    have hcoldeg : ∀ y, (M.ν i).w y ≠ 0 →
        M.pd i - (n : ℝ) ^ (-ω / 5) ≤ colDeg E G (M.μ i) y := by
      intro y hy
      have hh := hcolumn y hy
      rw [dens_dirac_eq_colDeg] at hh
      exact hh
    calc
      M.pd i - (n : ℝ) ^ (-ω / 5) ≤
          η.expect (fun y => colDeg E G (M.μ i) y) :=
            expect_ge_of_supported η (M.ν i) (fun y => colDeg E G (M.μ i) y)
              (M.pd i - (n : ℝ) ^ (-ω / 5)) hηsupp hcoldeg
      _ = dens E G (M.μ i) η := (dens_eq_expect_colDeg E G (M.μ i) η).symm
  have hweights : ∀ x, P.w x + σ.w x = 2 * (M.μ i).w x := by
    intro x
    dsimp [σ, residualLaw]
    ring
  have hmeanIdentity : P.expect q + dens E G σ η = 2 * dens E G (M.μ i) η := by
    have h := dens_linear_first E G (M.μ i) P σ η hweights
    rw [dens_eq_expect_rowDeg E G P η] at h
    simpa [q] using h
  have hlowerμδ : M.pd i - δ ≤ dens E G (M.μ i) η := by
    rw [hδTarget]
    exact hlowerμ
  have hmean : M.pd i - 3 * δ ≤ P.expect q := by
    have hδ' : δ' ≤ δ := le_trans hδ'δ (by linarith [hδpos])
    have htwolower : 2 * (M.pd i - δ) ≤ 2 * dens E G (M.μ i) η :=
      mul_le_mul_of_nonneg_left hlowerμδ (by norm_num)
    linarith [hmeanIdentity, hupperσ, htwolower]
  let High : Fin N → Prop := fun x => M.pd i + δ' < q x
  have hhighProb : P.pr High ≤ Real.exp (-r / 4) := by
    by_contra hnot
    have hlarge : Real.exp (-r / 4) < P.pr High := lt_of_not_ge hnot
    have hhigh : 0 < P.pr High := lt_trans (Real.exp_pos _) hlarge
    have hlogHigh : -Real.log (P.pr High) < r / 4 := by
      have hlog := Real.log_lt_log (Real.exp_pos _) hlarge
      rw [Real.log_exp] at hlog
      linarith
    let μH : Law N := P.cond High hhigh
    have hμHwidth : μH.WidthLE (M.sX i + r / 2) := by
      have htmp := cond_width_of_event P High hhigh hmaskwidth (le_of_lt hlogHigh)
      apply Law.WidthLE.mono htmp
      linarith [hlog2']
    have hμHsupport : ∀ x, (M.μ i).w x = 0 → μH.w x = 0 := by
      intro x hx
      have hPx : P.w x = 0 := hmaskzero x hx
      simp [μH, FinProb.cond, hPx]
    have hμHwidthP4 : μH.WidthLE (M.sX i + (n : ℝ) ^ (β - ω / 2) / 2) := by
      simpa [r] using hμHwidth
    have hμHupper : dens E G μH η ≤ M.pd i + δ' := by
      have h := hupper μH η hμHsupport hηsupp hμHwidthP4 hηwidthP4
      rw [hδ'Target]
      exact h
    have hcondAvg : M.pd i + δ' < μH.expect q :=
      cond_expect_gt P High hhigh q (M.pd i + δ') (by intro x hx; exact hx)
    have hdenHigh : M.pd i + δ' < dens E G μH η := by
      rw [dens_eq_expect_rowDeg]
      simpa [q] using hcondAvg
    linarith
  have hhighProbSmall : P.pr High ≤ δ / 2 := hhighProb.trans htailHalf
  let Low : Fin N → Prop := fun x => q x < M.pd i - a / 4
  have hpoint : ∀ x, q x ≤ M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0) +
      (if High x then (1 : ℝ) else 0) := by
    intro x
    by_cases hlow : Low x
    · have hδnonneg : 0 ≤ δ' := (Real.rpow_pos_of_pos hnrpos _).le
      have hnotHigh : ¬ High x := by
        intro hh
        change M.pd i + δ' < q x at hh
        change q x < M.pd i - a / 4 at hlow
        nlinarith [haPos, hδnonneg]
      rw [if_pos hlow, if_neg hnotHigh]
      nlinarith [hlow, hδnonneg]
    · by_cases hhigh : High x
      · have hbase : 0 ≤ M.pd i + δ' := by
          have hpd : 1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ M.pd i := hpLower
          have hpowpos : 0 < (n : ℝ) ^ (-h4 β γ) := Real.rpow_pos_of_pos hnrpos _
          have hδnonneg : 0 ≤ δ' := (Real.rpow_pos_of_pos hnrpos _).le
          linarith
        have hqle := rowDeg_le_one E G x η
        rw [if_neg hlow, if_pos hhigh]
        linarith
      · have hqle : q x ≤ M.pd i + δ' := le_of_not_gt hhigh
        rw [if_neg hlow, if_neg hhigh]
        linarith
  have hEval : P.expect (fun x => M.pd i + δ' - a / 4 *
      (if Low x then (1 : ℝ) else 0) + (if High x then (1 : ℝ) else 0)) =
      M.pd i + δ' - a / 4 * P.pr Low + P.pr High := by
    have hfun₁ : (fun x => M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0) +
        (if High x then (1 : ℝ) else 0)) =
      (fun x => M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0)) +
        (fun x => if High x then (1 : ℝ) else 0) := by
      funext x
      rfl
    have hfun₂ : (fun x => M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0)) =
      (fun _ => M.pd i + δ') + (fun x => -(a / 4) * (if Low x then (1 : ℝ) else 0)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    calc
      P.expect (fun x => M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0) +
          (if High x then (1 : ℝ) else 0)) =
        P.expect (fun x => M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0)) +
          P.expect (fun x => if High x then (1 : ℝ) else 0) := by
            rw [hfun₁]
            change P.expect (fun x =>
              (M.pd i + δ' - a / 4 * (if Low x then (1 : ℝ) else 0)) +
                (if High x then (1 : ℝ) else 0)) = _
            exact FinProb.expect_add P _ _
      _ = (P.expect (fun _ => M.pd i + δ') +
          P.expect (fun x => -(a / 4) * (if Low x then (1 : ℝ) else 0))) +
          P.expect (fun x => if High x then (1 : ℝ) else 0) := by
            rw [hfun₂]
            change (P.expect (fun x => (M.pd i + δ') +
              (-(a / 4) * (if Low x then (1 : ℝ) else 0))) +
                P.expect (fun x => if High x then (1 : ℝ) else 0)) = _
            rw [FinProb.expect_add]
      _ = M.pd i + δ' - a / 4 * P.pr Low + P.pr High := by
            rw [FinProb.expect_const, FinProb.expect_smul, expect_indicator, expect_indicator]
            ring
  have hmeanUpper : P.expect q ≤ M.pd i + δ' - a / 4 * P.pr Low + P.pr High := by
    calc
      P.expect q ≤ P.expect (fun x => M.pd i + δ' - a / 4 *
          (if Low x then (1 : ℝ) else 0) + (if High x then (1 : ℝ) else 0)) :=
            FinProb.expect_mono P hpoint
      _ = M.pd i + δ' - a / 4 * P.pr Low + P.pr High := hEval
  have hLowBound : P.pr Low ≤ 20 * δ / a := by
    apply (le_div_iff₀ haPos).2
    have hsum := hmean.trans hmeanUpper
    have hbudget : δ' + P.pr High ≤ δ := by linarith [hδ'δ, hhighProbSmall]
    nlinarith [hbudget]
  simpa [P, Low, q, δ, δ', ω, a, hδTarget] using hLowBound

end HypercubeRamsey.Lane_q_s04_valid
