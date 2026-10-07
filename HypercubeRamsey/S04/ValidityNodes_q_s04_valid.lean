import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2

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

private theorem expect_indicator {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.expect (fun x => if A x then (1 : ℝ) else 0) = P.pr A := by
  classical
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x <;> simp [hA]

private theorem pr_const {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Prop) :
    P.pr (fun _ => A) = if A then (1 : ℝ) else 0 := by
  by_cases hA : A
  · simp [FinProb.pr, hA, P.sum_eq_one]
  · simp [FinProb.pr, hA]

private def prefixVals {α : Type*} {k : ℕ} (ω : Fin k → α) (i : Fin k) : Fin i.val → α :=
  fun j => ω ⟨j.val, lt_trans j.isLt i.isLt⟩

private theorem prefixVals_cons_succ {α : Type*} {k : ℕ} (a : α) (ω : Fin k → α)
    (i : Fin k) :
    prefixVals (Fin.cons a ω) i.succ = Fin.cons a (prefixVals ω i) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => rfl

private theorem expect_pi_cons {α : Type*} [Fintype α] {k : ℕ}
    (P : Fin (k + 1) → FinProb α) (f : (Fin (k + 1) → α) → ℝ) :
    (FinProb.pi P).expect f =
      (P 0).expect (fun a =>
        (FinProb.pi (fun i : Fin k => P i.succ)).expect (fun x => f (Fin.cons a x))) := by
  classical
  have hsumCons {m : ℕ} (g : (Fin (m + 1) → α) → ℝ) :
      (∑ x : Fin (m + 1) → α, g x) = ∑ a : α, ∑ y : Fin m → α, g (Fin.cons a y) := by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => α)) g]
    rw [Fintype.sum_prod_type]
    rfl
  unfold FinProb.expect
  rw [hsumCons]
  simp [FinProb.pi, Finset.mul_sum, Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm]

private theorem expect_if_eq {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (a₀ : α) (c : ℝ) :
    P.expect (fun a => if a = a₀ then c else 0) = P.w a₀ * c := by
  classical
  unfold FinProb.expect
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a ha hne
    simp [hne]
  · simp

private theorem expect_pi_prefix_fiber {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Q : Fin k → FinProb α) (i : Fin k) (p : Fin i.val → α) (f : α → ℝ) :
    (FinProb.pi Q).expect (fun x => if prefixVals x i = p then f (x i) else 0) =
      (∏ j : Fin i.val, (Q ⟨j.val, lt_trans j.isLt i.isLt⟩).w (p j)) * (Q i).expect f := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      cases i using Fin.cases with
      | zero =>
          have hpref (x : Fin (k + 1) → α) : prefixVals x 0 = p := by
            funext j
            exact Fin.elim0 j
          have hcons := expect_pi_cons Q
            (fun x => if prefixVals x 0 = p then f (x 0) else 0)
          have htail (a : α) :
              (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                  (fun x => if prefixVals (Fin.cons a x) 0 = p then f a else 0) = f a := by
            have hf : (fun x : Fin k → α =>
                if prefixVals (Fin.cons a x) 0 = p then f a else 0) = (fun _ => f a) := by
              funext x
              rw [if_pos (hpref (Fin.cons a x))]
            rw [hf, FinProb.expect_const]
          calc
            _ = (Q 0).expect (fun a =>
                  (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                    (fun x => if prefixVals (Fin.cons a x) 0 = p then f a else 0)) := hcons
            _ = (Q 0).expect f := by
                  congr 1
                  funext a
                  exact htail a
            _ = _ := by
              change (Q 0).expect f = 1 * (Q 0).expect f
              ring
      | succ i =>
          let p₀ := p ⟨0, Nat.zero_lt_succ _⟩
          let pt : Fin i.val → α := fun j => p j.succ
          have hp : p = (Fin.cons (α := fun _ : Fin i.val.succ => α) p₀ pt) := by
            funext j
            cases j using Fin.cases with
            | zero => simp [p₀]
            | succ j => rfl
          have hcons := expect_pi_cons Q
            (fun x => if prefixVals x i.succ = p then f (x i.succ) else 0)
          have hfun (a : α) (x : Fin k → α) :
              (if prefixVals (Fin.cons (α := fun _ : Fin (k + 1) => α) a x) i.succ = p then
                f ((Fin.cons (α := fun _ : Fin (k + 1) => α) a x) i.succ) else 0) =
              (if a = p₀ ∧ prefixVals x i = pt then f (x i) else 0) := by
            rw [prefixVals_cons_succ, hp]
            have hconsEq : (Fin.cons (α := fun _ : Fin i.val.succ => α) a (prefixVals x i)) =
                (Fin.cons (α := fun _ : Fin i.val.succ => α) p₀ pt) ↔
                a = p₀ ∧ prefixVals x i = pt := by
              constructor
              · intro h
                constructor
                · have h0 := congrFun h ⟨0, Nat.zero_lt_succ _⟩
                  simpa using h0
                · apply funext
                  intro j
                  have hj := congrFun h j.succ
                  simpa using hj
              · rintro ⟨ha, htail⟩
                subst a
                funext j
                cases j using Fin.cases with
                | zero => rfl
                | succ j => simp [htail]
            by_cases hc : a = p₀ ∧ prefixVals x i = pt
            · have hceq := hconsEq.mpr hc
              simp [hceq, hc]
            · have hne : Fin.cons (α := fun _ : Fin i.val.succ => α) a
                    (prefixVals x i) ≠ Fin.cons p₀ pt := by
                  intro h
                  exact hc (hconsEq.mp h)
              have hcur :
                  (Fin.cons (α := fun _ : Fin (k + 1) => α) a x) i.succ = x i := by simp
              simp [hc, hne, hcur]
          have hcons' : (FinProb.pi Q).expect
              (fun x => if prefixVals x i.succ = p then f (x i.succ) else 0) =
              (Q 0).expect (fun a => (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                (fun x => if a = p₀ ∧ prefixVals x i = pt then f (x i) else 0)) := by
            rw [hcons]
            congr 1
            funext a
            congr 1
            funext x
            exact hfun a x
          have htail := ih (fun j : Fin k => Q j.succ) i pt
          have hsplit : (Q 0).expect (fun a =>
              (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                (fun x => if a = p₀ ∧ prefixVals x i = pt then f (x i) else 0)) =
              (Q 0).w p₀ *
                (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                  (fun x => if prefixVals x i = pt then f (x i) else 0) := by
            have hinner (a : α) :
                (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                    (fun x => if a = p₀ ∧ prefixVals x i = pt then f (x i) else 0) =
                  if a = p₀ then
                    (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                      (fun x => if prefixVals x i = pt then f (x i) else 0) else 0 := by
              by_cases ha : a = p₀
              · subst a
                simp
              · have hz : (fun x : Fin k → α =>
                    if a = p₀ ∧ prefixVals x i = pt then f (x i) else 0) = fun _ => 0 := by
                  funext x
                  simp [ha]
                rw [hz, FinProb.expect_const]
                simp [ha]
            calc
              _ = (Q 0).expect (fun a => if a = p₀ then
                    (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                      (fun x => if prefixVals x i = pt then f (x i) else 0) else 0) := by
                    congr 1
                    funext a
                    exact hinner a
              _ = (Q 0).w p₀ *
                    (FinProb.pi (fun j : Fin k => Q j.succ)).expect
                      (fun x => if prefixVals x i = pt then f (x i) else 0) := by
                    exact expect_if_eq (Q 0) p₀ _
          have hprod :
              (∏ j : Fin i.val.succ,
                (Q ⟨j.val, lt_trans j.isLt i.succ.isLt⟩).w (p j)) =
              (Q 0).w p₀ * ∏ j : Fin i.val,
                (Q (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin k).succ).w (pt j) := by
            rw [Fin.prod_univ_succ]
            apply congrArg₂ (fun x y : ℝ => x * y)
            · simp [p₀]
            · apply Finset.prod_congr rfl
              intro j hj
              have hidx :
                  (⟨j.succ.val, lt_trans j.succ.isLt i.succ.isLt⟩ : Fin (k + 1)) =
                    (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin k).succ := by
                apply Fin.ext
                rfl
              rw [hidx]
          calc
            _ = ((Q 0).w p₀ *
                  (∏ j : Fin i.val, (Q (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin k).succ).w
                    (pt j))) * (Q i.succ).expect f := by
                  rw [hcons', hsplit, htail]
                  ring
            _ = (∏ j : Fin i.val.succ,
                  (Q ⟨j.val, lt_trans j.isLt i.succ.isLt⟩).w (p j)) *
                  (Q i.succ).expect f := by rw [← hprod]

private theorem expect_eq_on_support {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (f g : Ω → ℝ) (h : ∀ ω, P.w ω = 0 ∨ f ω = g ω) : P.expect f = P.expect g := by
  classical
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  rcases h ω with hz | hfg
  · simp [hz]
  · simp [hfg]

private theorem cond_true_eq_self {α : Type*} [Fintype α] [DecidableEq α] (P : FinProb α) :
    P.cond (fun _ => True) (by simp [FinProb.pr, P.sum_eq_one]) = P := by
  classical
  have hp : P.pr (fun _ => True) = 1 := by simp [FinProb.pr, P.sum_eq_one]
  apply finProb_ext
  intro a
  simp [FinProb.cond, hp]

private theorem pr_eq_weight_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) (a : α) : P.pr (fun x => x = a) = P.w a := by
  classical
  unfold FinProb.pr
  rw [Finset.sum_eq_single a]
  · simp
  · intro x hx hne
    simp [hne]
  · simp

private theorem pr_congr_local_early {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (h : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  simp [h ω]

private theorem pi_cond_prefix_expect_next {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (P : Fin k → FinProb α) (i : Fin k) (p : Fin i.val → α)
    (hpos : 0 < (FinProb.pi P).pr (fun x => prefixVals x i = p)) (f : α → ℝ) :
    ((FinProb.pi P).cond (fun x => prefixVals x i = p) hpos).expect (fun x => f (x i)) =
      (P i).expect f := by
  classical
  let C : Fin k → α → Prop := fun j a =>
    ∀ hj : j.val < i.val, a = p ⟨j.val, hj⟩
  have hEvent : (fun x : Fin k → α => prefixVals x i = p) =
      (fun x => ∀ j, C j (x j)) := by
    funext x
    apply propext
    constructor
    · intro hp j hj
      let q : Fin i.val := ⟨j.val, hj⟩
      have hindex : (⟨q.val, lt_trans q.isLt i.isLt⟩ : Fin k) = j := by
        apply Fin.ext
        rfl
      have h := congrFun hp q
      have hx : prefixVals x i q = x j := by
        change x (⟨q.val, lt_trans q.isLt i.isLt⟩ : Fin k) = x j
        rw [hindex]
      rw [hx] at h
      simpa [q] using h
    · intro hall
      funext q
      let j : Fin k := ⟨q.val, lt_trans q.isLt i.isLt⟩
      have hmem : j.val < i.val := by simpa [j] using q.isLt
      have hvalue : x j = p ⟨j.val, hmem⟩ := hall j hmem
      have hpeq : (⟨j.val, hmem⟩ : Fin i.val) = q := by
        apply Fin.ext
        rfl
      rw [hpeq] at hvalue
      have hindex : (⟨q.val, lt_trans q.isLt i.isLt⟩ : Fin k) = j := by
        apply Fin.ext
        rfl
      have hx : prefixVals x i q = x j := by
        change x (⟨q.val, lt_trans q.isLt i.isLt⟩ : Fin k) = x j
        rw [hindex]
      rw [hx]
      exact hvalue
  have hfactor : (FinProb.pi P).pr (fun x => prefixVals x i = p) =
      ∏ j, (P j).pr (C j) := by
    rw [hEvent]
    exact FinProb.pi_pr_forall P C
  have hfactorPos : 0 < ∏ j : Fin k, (P j).pr (C j) := by
    rw [← hfactor]
    exact hpos
  have hcoord (j : Fin k) : 0 < (P j).pr (C j) := by
    by_cases hj : j.val < i.val
    · by_contra hnot
      have hnon : 0 ≤ (P j).pr (C j) := FinProb.pr_nonneg (P j) (C j)
      have hzero : (P j).pr (C j) = 0 := le_antisymm (le_of_not_gt hnot) hnon
      have hprodZero : (∏ j' : Fin k, (P j').pr (C j')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hzero
      rw [hprodZero] at hfactorPos
      exact (lt_irrefl 0) hfactorPos
    · have hC : C j = (fun _ => True) := by
        funext a
        apply propext
        constructor
        · intro _
          trivial
        · intro _ hmem
          exact (hj hmem).elim
      rw [hC]
      simp [FinProb.pr, (P j).sum_eq_one]
  let Q : Fin k → FinProb α := fun j => (P j).cond (C j) (hcoord j)
  have hrectPos : 0 < (FinProb.pi P).pr (fun x => ∀ j, C j (x j)) := by
    simpa [hEvent] using hpos
  have hcond : (FinProb.pi P).cond (fun x => prefixVals x i = p) hpos = FinProb.pi Q := by
    simpa [hEvent] using FinProb.pi_cond_forall P C hcoord hrectPos
  have hsupport : ∀ x : Fin k → α,
      (FinProb.pi Q).w x = 0 ∨
        (if prefixVals x i = p then f (x i) else 0) = f (x i) := by
    intro x
    by_cases hp : prefixVals x i = p
    · exact Or.inr (by simp [hp])
    · left
      have hex : ∃ j : Fin k, ¬ C j (x j) := by
        have hnot : ¬ (∀ j, C j (x j)) := by
          intro hall
          exact hp ((Iff.of_eq (congrFun hEvent x)).2 hall)
        exact not_forall.mp hnot
      obtain ⟨j, hj⟩ := hex
      have hz : (Q j).w (x j) = 0 := by simp [Q, FinProb.cond, hj]
      unfold FinProb.pi
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
  have hweight (j : Fin i.val) :
      (Q ⟨j.val, lt_trans j.isLt i.isLt⟩).w (p j) = 1 := by
    let q : Fin k := ⟨j.val, lt_trans j.isLt i.isLt⟩
    have hmem : q.val < i.val := by exact j.isLt
    have hprob : (P q).pr (fun a => a = p j) = (P q).w (p j) :=
      pr_eq_weight_singleton (P q) (p j)
    have hCq : C q = (fun a => a = p j) := by
      funext a
      apply propext
      constructor
      · intro h
        exact h hmem
      · intro ha hq
        have heq : (⟨q.val, hq⟩ : Fin i.val) = j := by
          apply Fin.ext
          rfl
        simpa [heq] using ha
    have hpr : (P q).pr (C q) = (P q).w (p j) := by
      calc
        (P q).pr (C q) = (P q).pr (fun a => a = p j) := by
          apply pr_congr_local_early
          intro a
          exact Iff.of_eq (congrFun hCq a)
        _ = (P q).w (p j) := hprob
    have hposWeight : 0 < (P q).w (p j) := by
      rw [← hpr]
      exact hcoord q
    have hCpoint : C q (p j) := by
      intro hq
      have heq : (⟨q.val, hq⟩ : Fin i.val) = j := by
        apply Fin.ext
        rfl
      exact (congrArg p heq).symm
    have hQeq : Q ⟨j.val, lt_trans j.isLt i.isLt⟩ =
        (P q).cond (C q) (hcoord q) := by
      rfl
    rw [hQeq]
    simp only [FinProb.cond]
    rw [if_pos hCpoint, hpr]
    exact div_self (ne_of_gt hposWeight)
  have hprefixProd :
      (∏ j : Fin i.val, (Q ⟨j.val, lt_trans j.isLt i.isLt⟩).w (p j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact hweight j
  have hcurrent : Q i = P i := by
    apply finProb_ext
    intro a
    simp [Q, C, FinProb.cond, FinProb.pr, (P i).sum_eq_one]
  calc
    ((FinProb.pi P).cond (fun x => prefixVals x i = p) hpos).expect (fun x => f (x i)) =
        (FinProb.pi Q).expect (fun x => f (x i)) := by rw [hcond]
    _ = (FinProb.pi Q).expect (fun x => if prefixVals x i = p then f (x i) else 0) :=
      (expect_eq_on_support (FinProb.pi Q) _ _ hsupport).symm
    _ = (∏ j : Fin i.val, (Q ⟨j.val, lt_trans j.isLt i.isLt⟩).w (p j)) * (Q i).expect f :=
      expect_pi_prefix_fiber Q i p f
    _ = (P i).expect f := by rw [hprefixProd, hcurrent]; ring

private theorem pr_pi_cons {α : Type*} [Fintype α] {k : ℕ}
    (P : Fin (k + 1) → FinProb α) (A : (Fin (k + 1) → α) → Prop) :
    (FinProb.pi P).pr A =
      (P 0).expect (fun a =>
        (FinProb.pi (fun i : Fin k => P i.succ)).pr (fun x => A (Fin.cons a x))) := by
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).expect (fun ω => if A ω then 1 else 0) :=
      (expect_indicator _ _).symm
    _ = (P 0).expect (fun a =>
          (FinProb.pi (fun i : Fin k => P i.succ)).expect
            (fun x => if A (Fin.cons a x) then 1 else 0)) := expect_pi_cons P _
    _ = (P 0).expect (fun a =>
          (FinProb.pi (fun i : Fin k => P i.succ)).pr (fun x => A (Fin.cons a x))) := by
      congr 1
      funext a
      exact expect_indicator _ _

private theorem pi_pr_exists_bad_le {α : Type*} [Fintype α] :
    ∀ k (P : Fin k → FinProb α)
      (bad : ∀ i : Fin k, (Fin i.val → α) → α → Prop) (ε : ℝ),
      (∀ i p, (P i).pr (bad i p) ≤ ε) →
      (FinProb.pi P).pr (fun ω => ∃ i, bad i (prefixVals ω i) (ω i)) ≤ (k : ℝ) * ε := by
  intro k
  induction k with
  | zero =>
      intro P bad ε hbound
      unfold FinProb.pr
      simp
  | succ k ih =>
      intro P bad ε hbound
      let Head := P 0
      let Tail := FinProb.pi (fun i : Fin k => P i.succ)
      let A : α → Prop := fun a => bad 0 (fun j => Fin.elim0 j) a
      let B (a : α) (x : Fin k → α) : Prop :=
        ∃ i : Fin k, bad i.succ (Fin.cons a (prefixVals x i)) (x i)
      have hEvent (a : α) (x : Fin k → α) :
          (∃ i : Fin (k + 1),
            bad i (prefixVals (Fin.cons a x : Fin (k + 1) → α) i)
              ((Fin.cons a x : Fin (k + 1) → α) i)) =
            (A a ∨ B a x) := by
        apply propext
        constructor
        · rintro ⟨i, hi⟩
          cases i using Fin.cases with
          | zero =>
              have hpref : prefixVals (Fin.cons a x : Fin (k + 1) → α) 0 =
                  (fun j : Fin 0 => Fin.elim0 j) := by
                funext j
                exact Fin.elim0 j
              exact Or.inl (by simpa [A, hpref] using hi)
          | succ j =>
              exact Or.inr ⟨j, by simpa [B, prefixVals_cons_succ] using hi⟩
        · intro h
          rcases h with hA | ⟨i, hi⟩
          · have hpref : prefixVals (Fin.cons a x : Fin (k + 1) → α) 0 =
                (fun j : Fin 0 => Fin.elim0 j) := by
              funext j
              exact Fin.elim0 j
            exact ⟨0, by simpa [A, hpref] using hA⟩
          · exact ⟨i.succ, by simpa [B, prefixVals_cons_succ] using hi⟩
      have hTail : ∀ a, Tail.pr (B a) ≤ (k : ℝ) * ε := by
        intro a
        apply ih (fun i : Fin k => P i.succ)
          (fun i p x => bad i.succ (Fin.cons a p) x) ε
        intro i p
        exact hbound i.succ (Fin.cons a p)
      have hA : Head.pr A ≤ ε := hbound 0 (fun j => Fin.elim0 j)
      have hpoint : ∀ a, Tail.pr (fun x => A a ∨ B a x) ≤
          (if A a then (1 : ℝ) else 0) + (k : ℝ) * ε := by
        intro a
        have hconst : Tail.pr (fun _ => A a) = if A a then (1 : ℝ) else 0 :=
          pr_const Tail (A a)
        calc
          Tail.pr (fun x => A a ∨ B a x) ≤ Tail.pr (fun _ => A a) + Tail.pr (B a) :=
            FinProb.pr_union Tail _ _
          _ ≤ (if A a then (1 : ℝ) else 0) + (k : ℝ) * ε := by
            rw [hconst]
            exact add_le_add (le_rfl) (hTail a)
      calc
        (FinProb.pi P).pr (fun ω => ∃ i, bad i (prefixVals ω i) (ω i)) =
            Head.expect (fun a => Tail.pr (fun x => A a ∨ B a x)) := by
              simpa [Head, Tail, hEvent] using pr_pi_cons P
                (fun ω => ∃ i, bad i (prefixVals ω i) (ω i))
        _ ≤ Head.expect (fun a => (if A a then (1 : ℝ) else 0) + (k : ℝ) * ε) :=
          FinProb.expect_mono Head hpoint
        _ = Head.pr A + (k : ℝ) * ε := by
          rw [FinProb.expect_add, expect_indicator, FinProb.expect_const]
        _ ≤ ε + (k : ℝ) * ε := add_le_add hA (le_rfl)
        _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring

private theorem expect_pi_reindex {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (e : κ ≃ ι) (P : ι → FinProb α) (f : (ι → α) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun j => P (e j))).expect (fun x => f (fun i => x (e.symm i))) := by
  classical
  let E : (κ → α) ≃ (ι → α) := {
    toFun := fun x i => x (e.symm i)
    invFun := fun y j => y (e j)
    left_inv := by intro x; funext j; simp
    right_inv := by intro y; funext i; simp }
  have hE (x : κ → α) : E x = fun i => x (e.symm i) := rfl
  have hweight (x : κ → α) :
      (FinProb.pi (fun j => P (e j))).w x = (FinProb.pi P).w (E x) := by
    simp only [FinProb.pi]
    rw [hE]
    simpa using (Equiv.prod_comp e (fun i => (P i).w (x (e.symm i))))
  unfold FinProb.expect
  calc
    _ = ∑ x, (FinProb.pi P).w (E x) * f (E x) :=
      (Equiv.sum_comp E (fun y => (FinProb.pi P).w y * f y)).symm
    _ = ∑ x, (FinProb.pi (fun j => P (e j))).w x * f (E x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hweight]
    _ = _ := by simp [FinProb.expect, E]

private theorem pr_pi_reindex {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (e : κ ≃ ι) (P : ι → FinProb α) (A : (ι → α) → Prop) :
    (FinProb.pi P).pr A =
      (FinProb.pi (fun j => P (e j))).pr (fun x => A (fun i => x (e.symm i))) := by
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).expect (fun x => if A x then 1 else 0) :=
      (expect_indicator _ _).symm
    _ = (FinProb.pi (fun j => P (e j))).expect
          (fun x => if A (fun i => x (e.symm i)) then 1 else 0) :=
        expect_pi_reindex e P _
    _ = (FinProb.pi (fun j => P (e j))).pr
          (fun x => A (fun i => x (e.symm i))) := expect_indicator _ _

private theorem pi_cond_rect_last_expect {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (P : Fin m → FinProb α) (C : Fin m → α → Prop)
    (hcoord : ∀ j, 0 < (P j).pr (C j))
    (hpos : 0 < (FinProb.pi P).pr (fun x => ∀ j, C j (x j)))
    (last : Fin m) (f : α → ℝ) :
    ((FinProb.pi P).cond (fun x => ∀ j, C j (x j)) hpos).expect
        (fun x => f (x last)) = ((P last).cond (C last) (hcoord last)).expect f := by
  classical
  let Q : Fin m → FinProb α := fun j => (P j).cond (C j) (hcoord j)
  have hcond : (FinProb.pi P).cond (fun x => ∀ j, C j (x j)) hpos = FinProb.pi Q :=
    FinProb.pi_cond_forall P C hcoord hpos
  let first : Fin m := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) last.isLt⟩
  let e : Fin m ≃ Fin m := Equiv.swap first last
  have he : e first = last := by simp [e]
  have hswap : e.symm last = first := by
    rw [← he]
    exact e.symm_apply_apply first
  rw [hcond]
  calc
    (FinProb.pi Q).expect (fun x => f (x last)) =
        (FinProb.pi (fun j => Q (e j))).expect (fun x => f (x (e.symm last))) :=
          expect_pi_reindex e Q (fun x => f (x last))
    _ = (Q last).expect f := by
          have h := expect_pi_prefix_fiber (fun j => Q (e j)) first
            (fun j => Fin.elim0 j) f
          have htriv (x : Fin m → α) :
              prefixVals x first = (fun j : Fin 0 => Fin.elim0 j) := by
            funext j
            exact Fin.elim0 j
          have hfun : (fun x : Fin m → α =>
              if prefixVals x first = (fun j : Fin 0 => Fin.elim0 j) then f (x first) else 0) =
              (fun x => f (x first)) := by
            funext x
            rw [if_pos (htriv x)]
          rw [hfun] at h
          simpa [first, e, he, hswap] using h
    _ = ((P last).cond (C last) (hcoord last)).expect f := rfl

private theorem nonempty_finProb {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

private theorem pr_pi_depends_subset {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (P : ι → FinProb α) (s : Finset ι) (A : (ι → α) → Prop)
    (hA : ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → A ω = A ω') :
    (FinProb.pi P).pr A =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => α)).symm
          (a, fun i : {i // i ∉ s} =>
            (Classical.choice (nonempty_finProb (FinProb.pi P))) i.1))) := by
  classical
  let E := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ : ι => α)
  let ω₀ : ι → α := Classical.choice (nonempty_finProb (FinProb.pi P))
  let b₀ : ∀ i : {i // i ∉ s}, α := fun i => ω₀ i.1
  let f : (ι → α) → ℝ := fun ω => if A ω then 1 else 0
  have hf : FinProb.DependsOn f s := by
    intro ω ω' hagree
    change (if A ω then (1 : ℝ) else 0) = if A ω' then 1 else 0
    rw [hA ω ω' hagree]
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).expect f := (expect_indicator _ _).symm
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
          (fun a => f (E.symm (a, b₀))) := by
            exact FinProb.pi_expect_depends P s f ω₀ hf
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr
          (fun a => A (E.symm (a, b₀))) := expect_indicator _ _

private noncomputable def safeCond {N : ℕ} (P : Law N) (A : Fin N → Prop) : Law N :=
  if h : 0 < P.pr A then P.cond A h else P

private noncomputable def residualAfter {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs : List (Fin N)) : Law N :=
  xs.foldl (fun η x => safeCond η (fun y => Hits E G x y)) P

private noncomputable def GoodPath {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : ℝ) (P : Law N) : List (Fin N) → Prop
  | [] => True
  | x :: xs =>
      Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) ∧
        GoodPath E G L (safeCond P (fun y => Hits E G x y)) xs

private theorem residualAfter_append {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs ys : List (Fin N)) :
    residualAfter E G P (xs ++ ys) = residualAfter E G (residualAfter E G P xs) ys := by
  simp [residualAfter, List.foldl_append]

private theorem GoodPath_append {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : ℝ) (P : Law N) (xs ys : List (Fin N)) :
    GoodPath E G L P (xs ++ ys) ↔
      GoodPath E G L P xs ∧ GoodPath E G L (residualAfter E G P xs) ys := by
  induction xs generalizing P with
  | nil => simp [GoodPath, residualAfter]
  | cons x xs ih =>
      simp only [List.cons_append, GoodPath]
      rw [ih (P := safeCond P (fun y => Hits E G x y))]
      simp [residualAfter, and_assoc]

private noncomputable def FirstBad {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : ℝ) (P : Law N) : List (Fin N) → Prop
  | [] => False
  | x :: xs =>
      P.pr (fun y => Hits E G x y) < Real.exp (-L) ∨
        (Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) ∧
          FirstBad E G L (safeCond P (fun y => Hits E G x y)) xs)

private theorem not_GoodPath_iff_FirstBad {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : ℝ) (P : Law N) (xs : List (Fin N)) :
    ¬ GoodPath E G L P xs ↔ FirstBad E G L P xs := by
  induction xs generalizing P with
  | nil => simp [GoodPath, FirstBad]
  | cons x xs ih =>
      by_cases hq : Real.exp (-L) ≤ P.pr (fun y => Hits E G x y)
      · have htail := ih (P := safeCond P (fun y => Hits E G x y))
        simp [GoodPath, FirstBad, hq, htail]
      · have hbad : P.pr (fun y => Hits E G x y) < Real.exp (-L) := lt_of_not_ge hq
        simp [GoodPath, FirstBad, hq, hbad]

private theorem pr_Hit_eq_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (x : Fin N) :
    P.pr (fun y => Hits E G x y) = rowDeg E G x P := by
  classical
  simp [FinProb.pr, rowDeg, mul_comm]

private def finToList {α : Type*} {k : ℕ} (x : Fin k → α) : List α := List.ofFn x

private theorem finToList_cons {α : Type*} {k : ℕ} (a : α) (x : Fin k → α) :
    finToList (Fin.cons a x) = a :: finToList x := by
  simp [finToList]

private def tupleLabels {k N m : ℕ} (W : Fin m → Fin k → Fin N) : List (Fin N) :=
  (List.ofFn fun i : Fin m => finToList (W i)).flatten

private theorem tupleLabels_length {k N m : ℕ} (W : Fin m → Fin k → Fin N) :
    (tupleLabels W).length = m * k := by
  simp [tupleLabels, finToList, List.length_flatten, List.sum_ofFn]

private theorem tupleLabels_cons {k N m : ℕ} (a : Fin k → Fin N)
    (W : Fin m → Fin k → Fin N) :
    tupleLabels (Fin.cons a W) = finToList a ++ tupleLabels W := by
  simp [tupleLabels, finToList]

private theorem tupleLabels_snoc {k N m : ℕ} (W : Fin (m + 1) → Fin k → Fin N) :
    tupleLabels W = tupleLabels (Fin.init W) ++ finToList (W (Fin.last m)) := by
  rw [← Fin.snoc_init_self W]
  change (List.ofFn (fun i : Fin (m + 1) =>
      finToList (Fin.snoc (Fin.init W) (W (Fin.last m)) i))).flatten = _
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last, finToList, List.flatten, tupleLabels]

private theorem tupleLabels_split_last {k N m : ℕ} (W : Fin m → Fin k → Fin N)
    (last : Fin m) (hlast : last.val + 1 = m) :
    tupleLabels W = tupleLabels (prefixVals W last) ++ finToList (W last) := by
  let q := last.val
  let V : Fin (q + 1) → Fin k → Fin N := fun i => W (Fin.cast hlast i)
  have hOfFn : List.ofFn (fun i : Fin m => finToList (W i)) =
      List.ofFn (fun i : Fin (q + 1) => finToList (W (Fin.cast hlast i))) :=
    List.ofFn_congr hlast.symm _
  have hInit : Fin.init V = prefixVals W last := by
    funext j
    apply congrArg W
    apply Fin.ext
    rfl
  have hLast : V (Fin.last q) = W last := by
    apply congrArg W
    apply Fin.ext
    rfl
  calc
    tupleLabels W = tupleLabels V := by
      change (List.ofFn (fun i : Fin m => finToList (W i))).flatten = _
      simpa [tupleLabels, V] using congrArg List.flatten hOfFn
    _ = tupleLabels (Fin.init V) ++ finToList (V (Fin.last q)) := tupleLabels_snoc V
    _ = tupleLabels (prefixVals W last) ++ finToList (W last) := by rw [hInit, hLast]

private noncomputable def OuterFirstBad {N m k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (L : ℝ) (P : Law N) (W : Fin m → Fin k → Fin N) : Prop :=
  ∃ i : Fin m, GoodPath E G L P (tupleLabels (prefixVals W i)) ∧
    ∃ j : Fin k,
      GoodPath E G L P (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j)) ∧
        rowDeg E G (W i j)
          (residualAfter E G P
            (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j))) < Real.exp (-L)

private theorem FirstBad_finToList_iff {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (L : ℝ) (P : Law N) (x : Fin k → Fin N) :
    FirstBad E G L P (finToList x) ↔
      ∃ j : Fin k, GoodPath E G L P (finToList (prefixVals x j)) ∧
        rowDeg E G (x j) (residualAfter E G P (finToList (prefixVals x j))) <
          Real.exp (-L) := by
  induction k generalizing P with
  | zero =>
      simp [FirstBad, finToList]
  | succ k ih =>
      let a := x 0
      let tail : Fin k → Fin N := fun i => x i.succ
      have hx : x = Fin.cons a tail := by
        funext i
        cases i using Fin.cases <;> simp [a, tail]
      rw [hx]
      have hHead : FirstBad E G L P (finToList (Fin.cons a tail)) =
          (P.pr (fun y => Hits E G a y) < Real.exp (-L) ∨
            (Real.exp (-L) ≤ P.pr (fun y => Hits E G a y) ∧
              FirstBad E G L (safeCond P (fun y => Hits E G a y)) (finToList tail))) := by
        simp [FirstBad, finToList]
      let Q := safeCond P (fun y => Hits E G a y)
      have hIH := ih Q tail
      rw [hHead, hIH]
      have hzero : finToList (prefixVals (Fin.cons a tail) (0 : Fin (k + 1))) = [] := by
        have hfun : prefixVals (Fin.cons a tail) (0 : Fin (k + 1)) =
            (fun j : Fin 0 => Fin.elim0 j) := by
          funext j
          exact Fin.elim0 j
        simp [finToList, hfun]
      constructor
      · intro h
        rcases h with hbad | ⟨hq, ⟨j, hj⟩⟩
        · refine ⟨0, ?_⟩
          have hlow : rowDeg E G a P < Real.exp (-L) := by
            simpa [pr_Hit_eq_rowDeg] using hbad
          rw [hzero]
          simp [GoodPath, residualAfter, hlow]
        · refine ⟨j.succ, ?_⟩
          have hprefix :
              finToList (prefixVals (Fin.cons a tail) j.succ) =
                a :: finToList (prefixVals tail j) := by
            rw [prefixVals_cons_succ]
            simp [finToList]
          have hres : residualAfter E G P
              (a :: finToList (prefixVals tail j)) =
              residualAfter E G Q (finToList (prefixVals tail j)) := rfl
          rw [hprefix]
          change (Real.exp (-L) ≤ P.pr (fun y => Hits E G a y) ∧
              GoodPath E G L Q (finToList (prefixVals tail j))) ∧
            rowDeg E G (tail j)
              (residualAfter E G P (a :: finToList (prefixVals tail j))) < Real.exp (-L)
          rw [hres]
          exact ⟨⟨hq, hj.1⟩, hj.2⟩
      · rintro ⟨j, hj⟩
        cases j using Fin.cases with
        | zero =>
            rw [hzero] at hj
            simp [GoodPath, residualAfter] at hj
            have hlow : P.pr (fun y => Hits E G a y) < Real.exp (-L) := by
              simpa [pr_Hit_eq_rowDeg] using hj
            left
            exact hlow
        | succ j =>
            have hprefix :
                finToList (prefixVals (Fin.cons a tail) j.succ) =
                  a :: finToList (prefixVals tail j) := by
              rw [prefixVals_cons_succ]
              simp [finToList]
            have hres : residualAfter E G P
                (a :: finToList (prefixVals tail j)) =
                residualAfter E G Q (finToList (prefixVals tail j)) := rfl
            rw [hprefix, hres] at hj
            change (Real.exp (-L) ≤ P.pr (fun y => Hits E G a y) ∧
                GoodPath E G L Q (finToList (prefixVals tail j))) ∧
              rowDeg E G (tail j)
                (residualAfter E G Q (finToList (prefixVals tail j))) < Real.exp (-L) at hj
            rcases hj with ⟨⟨hq, hgoodTail⟩, hlow⟩
            right
            exact ⟨hq, ⟨j, ⟨hgoodTail, hlow⟩⟩⟩

private theorem OuterFirstBad_cons_iff {N k m : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (L : ℝ) (P : Law N) (a : Fin k → Fin N)
    (W : Fin m → Fin k → Fin N) :
    OuterFirstBad E G L P (Fin.cons a W) ↔
      FirstBad E G L P (finToList a) ∨
        (GoodPath E G L P (finToList a) ∧
          OuterFirstBad E G L (residualAfter E G P (finToList a)) W) := by
  constructor
  · rintro ⟨i, hprefix, j, hcombined, hlow⟩
    cases i using Fin.cases with
    | zero =>
        left
        have hPrefixZero : tupleLabels
            (prefixVals (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) 0) = [] := by
          simp [tupleLabels, prefixVals, finToList]
        have hCurrentZero : (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) 0 = a := by simp
        rw [hPrefixZero] at hcombined hlow
        simp only [List.nil_append] at hcombined hlow
        have hGood : GoodPath E G L P (finToList (prefixVals a j)) := by
          simpa [hCurrentZero] using hcombined
        have hLow : rowDeg E G (a j)
            (residualAfter E G P (finToList (prefixVals a j))) < Real.exp (-L) := by
          simpa [hCurrentZero] using hlow
        exact (FirstBad_finToList_iff E G L P a).2 ⟨j, hGood, hLow⟩
    | succ i =>
        right
        have hPrefixEq : tupleLabels
            (prefixVals (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) =
            finToList a ++ tupleLabels (prefixVals W i) := by
          rw [prefixVals_cons_succ, tupleLabels_cons]
        have hCurrent : (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ = W i := by simp
        have hCombinedEq :
            tupleLabels (prefixVals (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) ++
                finToList (prefixVals ((Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) j) =
              finToList a ++
                (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j)) := by
          rw [hPrefixEq, hCurrent]
          simp [List.append_assoc]
        rw [hPrefixEq] at hprefix
        have hPrefixParts := (GoodPath_append E G L P (finToList a)
          (tupleLabels (prefixVals W i))).1 hprefix
        rw [hCombinedEq] at hcombined
        have hCombinedParts := (GoodPath_append E G L P (finToList a)
          (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j))).1 hcombined
        have hLow' := hlow
        rw [hCombinedEq, residualAfter_append] at hLow'
        have hLow : rowDeg E G ((W i) j)
            (residualAfter E G (residualAfter E G P (finToList a))
              (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j))) <
              Real.exp (-L) := by simpa using hLow'
        exact ⟨hPrefixParts.1, ⟨i, hPrefixParts.2,
          ⟨j, hCombinedParts.2, hLow⟩⟩⟩
  · rintro (hfirst | ⟨hfirst, ⟨i, hprefix, ⟨j, hcombined, hlow⟩⟩⟩)
    · obtain ⟨j, hGood, hLow⟩ := (FirstBad_finToList_iff E G L P a).1 hfirst
      refine ⟨0, ?_, j, ?_, ?_⟩
      · simp [GoodPath, tupleLabels]
      · simpa [tupleLabels, prefixVals] using hGood
      · simpa [tupleLabels, prefixVals] using hLow
    · have hPrefixEq : tupleLabels
          (prefixVals (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) =
          finToList a ++ tupleLabels (prefixVals W i) := by
        rw [prefixVals_cons_succ, tupleLabels_cons]
      have hCurrent : (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ = W i := by simp
      have hCombinedEq :
          tupleLabels (prefixVals (Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) ++
              finToList (prefixVals ((Fin.cons a W : Fin (m + 1) → Fin k → Fin N) i.succ) j) =
            finToList a ++
              (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j)) := by
        rw [hPrefixEq, hCurrent]
        simp [List.append_assoc]
      refine ⟨i.succ, ?_, j, ?_, ?_⟩
      · rw [hPrefixEq]
        exact (GoodPath_append E G L P (finToList a) (tupleLabels (prefixVals W i))).2
          ⟨hfirst, hprefix⟩
      · rw [hCombinedEq]
        exact (GoodPath_append E G L P (finToList a)
          (tupleLabels (prefixVals W i) ++ finToList (prefixVals (W i) j))).2
          ⟨hfirst, hcombined⟩
      · rw [hCombinedEq, hCurrent, residualAfter_append]
        exact hlow

private theorem FirstBad_append {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : ℝ) (P : Law N) (xs ys : List (Fin N)) :
    FirstBad E G L P (xs ++ ys) ↔
      FirstBad E G L P xs ∨
        (GoodPath E G L P xs ∧ FirstBad E G L (residualAfter E G P xs) ys) := by
  calc
    FirstBad E G L P (xs ++ ys) ↔ ¬ GoodPath E G L P (xs ++ ys) :=
      (not_GoodPath_iff_FirstBad E G L P (xs ++ ys)).symm
    _ ↔ ¬ (GoodPath E G L P xs ∧
        GoodPath E G L (residualAfter E G P xs) ys) := by rw [GoodPath_append]
    _ ↔ FirstBad E G L P xs ∨
        (GoodPath E G L P xs ∧ FirstBad E G L (residualAfter E G P xs) ys) := by
      constructor
      · intro hnot
        by_cases hprev : GoodPath E G L P xs
        · right
          refine ⟨hprev, ?_⟩
          apply (not_GoodPath_iff_FirstBad E G L
            (residualAfter E G P xs) ys).mp
          intro htail
          exact hnot ⟨hprev, htail⟩
        · exact Or.inl ((not_GoodPath_iff_FirstBad E G L P xs).mp hprev)
      · intro h
        rcases h with hbad | ⟨hprev, hbad⟩
        · have hnot := (not_GoodPath_iff_FirstBad E G L P xs).mpr hbad
          exact fun hboth => hnot hboth.1
        · have hnot :=
            (not_GoodPath_iff_FirstBad E G L (residualAfter E G P xs) ys).mpr hbad
          exact fun hboth => hnot hboth.2

private theorem FirstBad_tupleLabels_iff {N k m : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (L : ℝ) (P : Law N) (W : Fin m → Fin k → Fin N) :
    FirstBad E G L P (tupleLabels W) ↔ OuterFirstBad E G L P W := by
  induction m generalizing P with
  | zero =>
      simp [tupleLabels, OuterFirstBad, FirstBad]
  | succ m ih =>
      let a := W 0
      let tail : Fin m → Fin k → Fin N := fun i => W i.succ
      have hW : W = Fin.cons a tail := by
        funext i
        cases i using Fin.cases <;> simp [a, tail]
      rw [hW, tupleLabels_cons, FirstBad_append]
      have hIH := ih (residualAfter E G P (finToList a)) tail
      rw [hIH]
      exact (OuterFirstBad_cons_iff E G L P a tail).symm

private theorem cond_supportedIn {N : ℕ} (P : Law N) (A : Fin N → Prop)
    (h : 0 < P.pr A) {Y : Finset (Fin N)}
    (hP : Law.SupportedIn P Y) : Law.SupportedIn (P.cond A h) Y := by
  intro y hy
  by_cases hAy : A y
  · simp [FinProb.cond, hP y hy, hAy]
  · simp [FinProb.cond, hAy]

private theorem safeCond_supportedIn {N : ℕ} (P : Law N) (A : Fin N → Prop)
    {Y : Finset (Fin N)} (hP : Law.SupportedIn P Y) :
    Law.SupportedIn (safeCond P A) Y := by
  unfold safeCond
  split
  · exact cond_supportedIn P A _ hP
  · exact hP

private theorem residualAfter_supportedIn {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs : List (Fin N)) {Y : Finset (Fin N)}
    (hP : Law.SupportedIn P Y) : Law.SupportedIn (residualAfter E G P xs) Y := by
  induction xs generalizing P with
  | nil => simpa [residualAfter] using hP
  | cons x xs ih =>
      change Law.SupportedIn (residualAfter E G
        (safeCond P (fun y => Hits E G x y)) xs) Y
      exact ih (P := safeCond P (fun y => Hits E G x y))
        (safeCond_supportedIn P _ hP)

private theorem residualAfter_width {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs : List (Fin N)) {t L : ℝ} (hP : P.WidthLE t)
    (hgood : GoodPath E G L P xs) :
    Law.WidthLE (residualAfter E G P xs) (t + (xs.length : ℝ) * L) := by
  induction xs generalizing P t with
  | nil => simpa [residualAfter] using hP
  | cons x xs ih =>
      change Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) ∧
        GoodPath E G L (safeCond P (fun y => Hits E G x y)) xs at hgood
      have hmass : 0 < P.pr (fun y => Hits E G x y) :=
        lt_of_lt_of_le (Real.exp_pos _) hgood.1
      have hbudget : -Real.log (P.pr (fun y => Hits E G x y)) ≤ L := by
        have hlog := Real.log_le_log (Real.exp_pos _) hgood.1
        rw [Real.log_exp] at hlog
        linarith
      have hcond : Law.WidthLE (P.cond (fun y => Hits E G x y) hmass) (t + L) :=
        cond_width_of_event P (fun y => Hits E G x y) hmass hP hbudget
      have hsafe : safeCond P (fun y => Hits E G x y) =
          P.cond (fun y => Hits E G x y) hmass := by
        simp [safeCond, hmass]
      have hstate : Law.WidthLE (safeCond P (fun y => Hits E G x y)) (t + L) := by
        rw [hsafe]
        exact hcond
      have htail := ih (P := safeCond P (fun y => Hits E G x y)) (t := t + L)
        hstate hgood.2
      change Law.WidthLE (residualAfter E G
        (safeCond P (fun y => Hits E G x y)) xs) _
      convert htail using 1 <;> simp [List.length_cons, Nat.cast_succ] <;> ring

private theorem pr_inter_eq_mul_cond {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hA : 0 < P.pr A) :
    P.pr (fun ω => A ω ∧ B ω) = P.pr A * (P.cond A hA).pr B := by
  classical
  unfold FinProb.pr at hA
  unfold FinProb.pr FinProb.cond
  rw [Finset.mul_sum]
  have hpr : P.pr A = ∑ z, if A z then P.w z else 0 := rfl
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hAw : A ω <;> by_cases hBw : B ω
  · simp only [hAw, hBw, ↓reduceIte]
    simp only [true_and, if_true]
    rw [hpr]
    field_simp [ne_of_gt hA]
  · simp [hAw, hBw]
  · simp [hAw, hBw]
  · simp [hAw, hBw]

private noncomputable def HitsList {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (xs : List (Fin N)) (y : Fin N) : Prop :=
  ∀ x ∈ xs, Hits E G x y

private theorem pr_HitsList_lower {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs : List (Fin N)) (L : ℝ) (hgood : GoodPath E G L P xs) :
    Real.exp (-(xs.length : ℝ) * L) ≤ P.pr (HitsList E G xs) := by
  induction xs generalizing P with
  | nil =>
      have htrue : P.pr (fun _ => True) = 1 := by simp [FinProb.pr, P.sum_eq_one]
      have hExp : Real.exp (-(([] : List (Fin N)).length : ℝ) * L) = 1 := by simp
      rw [hExp]
      have hHit : HitsList E G [] = (fun _ => True) := by
        funext y
        simp [HitsList]
      rw [hHit]
      exact htrue.ge
  | cons x xs ih =>
      change Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) ∧
        GoodPath E G L (safeCond P (fun y => Hits E G x y)) xs at hgood
      have hmass : 0 < P.pr (fun y => Hits E G x y) :=
        lt_of_lt_of_le (Real.exp_pos _) hgood.1
      have hsafe : safeCond P (fun y => Hits E G x y) =
          P.cond (fun y => Hits E G x y) hmass := by
        simp [safeCond, hmass]
      have htail := ih (safeCond P (fun y => Hits E G x y)) hgood.2
      rw [hsafe] at htail
      have hprob := pr_inter_eq_mul_cond P (fun y => Hits E G x y)
        (HitsList E G xs) hmass
      have hq : Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) := hgood.1
      have hprod : Real.exp (-L) * Real.exp (-(xs.length : ℝ) * L) ≤
          P.pr (fun y => Hits E G x y) * (P.cond (fun y => Hits E G x y) hmass).pr
            (HitsList E G xs) :=
        mul_le_mul hq htail (le_of_lt (Real.exp_pos _)) (by positivity)
      have hEq : Real.exp (-L) * Real.exp (-(xs.length : ℝ) * L) =
          Real.exp (-((xs.length : ℝ) + 1) * L) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      have hlist : (fun y => HitsList E G (x :: xs) y) =
          (fun y => Hits E G x y ∧ HitsList E G xs y) := by
        funext y
        simp [HitsList]
      calc
        Real.exp (-(↑(x :: xs).length) * L) =
            Real.exp (-L) * Real.exp (-(xs.length : ℝ) * L) := by
              rw [hEq]
              congr 1
              simp [Nat.cast_succ]
        _ ≤ P.pr (fun y => Hits E G x y) *
              (P.cond (fun y => Hits E G x y) hmass).pr (HitsList E G xs) := hprod
        _ = P.pr (fun y => Hits E G x y ∧ HitsList E G xs y) := hprob.symm
        _ = P.pr (HitsList E G (x :: xs)) := by rw [← hlist]

private theorem pr_HitsList_append {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (P : Law N) (xs ys : List (Fin N)) (L : ℝ)
    (hgood : GoodPath E G L P (xs ++ ys)) :
    P.pr (HitsList E G (xs ++ ys)) =
      P.pr (HitsList E G xs) * (residualAfter E G P xs).pr (HitsList E G ys) := by
  induction xs generalizing P with
  | nil => simp [HitsList, residualAfter, FinProb.pr, P.sum_eq_one]
  | cons x xs ih =>
      change Real.exp (-L) ≤ P.pr (fun y => Hits E G x y) ∧
        GoodPath E G L (safeCond P (fun y => Hits E G x y)) (xs ++ ys) at hgood
      have hmass : 0 < P.pr (fun y => Hits E G x y) :=
        lt_of_lt_of_le (Real.exp_pos _) hgood.1
      have hsafe : safeCond P (fun y => Hits E G x y) =
          P.cond (fun y => Hits E G x y) hmass := by simp [safeCond, hmass]
      have htail : GoodPath E G L (P.cond (fun y => Hits E G x y) hmass) (xs ++ ys) := by
        rw [← hsafe]
        exact hgood.2
      have hIH := ih (P.cond (fun y => Hits E G x y) hmass) htail
      have hres : residualAfter E G P (x :: xs) =
          residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs := by
        change residualAfter E G (safeCond P (fun y => Hits E G x y)) xs = _
        rw [hsafe]
      have hFullEvent : HitsList E G (x :: (xs ++ ys)) =
          (fun y => Hits E G x y ∧ HitsList E G (xs ++ ys) y) := by
        funext y
        simp [HitsList]
      have hBaseEvent : HitsList E G (x :: xs) =
          (fun y => Hits E G x y ∧ HitsList E G xs y) := by
        funext y
        simp [HitsList]
      have hFull := pr_inter_eq_mul_cond P (fun y => Hits E G x y)
        (HitsList E G (xs ++ ys)) hmass
      have hBase := pr_inter_eq_mul_cond P (fun y => Hits E G x y)
        (HitsList E G xs) hmass
      calc
        P.pr (HitsList E G (x :: xs ++ ys)) =
            P.pr (fun y => Hits E G x y ∧ HitsList E G (xs ++ ys) y) := by
              rw [List.cons_append, hFullEvent]
        _ = P.pr (fun y => Hits E G x y) *
              (P.cond (fun y => Hits E G x y) hmass).pr (HitsList E G (xs ++ ys)) := hFull
        _ = P.pr (fun y => Hits E G x y) *
              ((P.cond (fun y => Hits E G x y) hmass).pr (HitsList E G xs) *
                (residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs).pr
                  (HitsList E G ys)) := by rw [hIH]
        _ = P.pr (HitsList E G (x :: xs)) *
              (residualAfter E G P (x :: xs)).pr (HitsList E G ys) := by
              calc
                P.pr (fun y => Hits E G x y) *
                    ((P.cond (fun y => Hits E G x y) hmass).pr (HitsList E G xs) *
                      (residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs).pr
                        (HitsList E G ys)) =
                    (P.pr (fun y => Hits E G x y) *
                      (P.cond (fun y => Hits E G x y) hmass).pr (HitsList E G xs)) *
                      (residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs).pr
                        (HitsList E G ys) := by ring
                _ = P.pr (fun y => Hits E G x y ∧ HitsList E G xs y) *
                      (residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs).pr
                        (HitsList E G ys) := by rw [← hBase]
                _ = P.pr (HitsList E G (x :: xs)) *
                      (residualAfter E G (P.cond (fun y => Hits E G x y) hmass) xs).pr
                        (HitsList E G ys) := by rw [← hBaseEvent]
                _ = P.pr (HitsList E G (x :: xs)) *
                      (residualAfter E G P (x :: xs)).pr (HitsList E G ys) := by rw [← hres]

private theorem pr_HitsList_finToList_eq_prod {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (P : Law N) (x : Fin k → Fin N) (L : ℝ)
    (hgood : GoodPath E G L P (finToList x)) :
    P.pr (HitsList E G (finToList x)) =
      ∏ j : Fin k,
        (residualAfter E G P (finToList (prefixVals x j))).pr
          (fun y => Hits E G (x j) y) := by
  induction k generalizing P with
  | zero =>
      simp [finToList, HitsList, FinProb.pr, P.sum_eq_one]
  | succ k ih =>
      let a := x 0
      let tail : Fin k → Fin N := fun j => x j.succ
      have hx : x = Fin.cons a tail := by
        funext j
        cases j using Fin.cases <;> rfl
      have hlist : finToList x = a :: finToList tail := by
        rw [hx, finToList_cons]
      have hgood' : GoodPath E G L P ([a] ++ finToList tail) := by
        simpa [hlist] using hgood
      have hparts : Real.exp (-L) ≤ P.pr (fun y => Hits E G a y) ∧
          GoodPath E G L (safeCond P (fun y => Hits E G a y)) (finToList tail) := by
        simpa [GoodPath, hlist] using hgood
      have hprob := pr_HitsList_append E G P [a] (finToList tail) L hgood'
      have hone : HitsList E G [a] = (fun y => Hits E G a y) := by
        funext y
        simp [HitsList]
      have hprob' : P.pr (HitsList E G (finToList x)) =
          P.pr (fun y => Hits E G a y) *
            (safeCond P (fun y => Hits E G a y)).pr
              (HitsList E G (finToList tail)) := by
        calc
          P.pr (HitsList E G (finToList x)) =
              P.pr (HitsList E G (a :: finToList tail)) := by rw [hlist]
          _ = P.pr (HitsList E G ([a] ++ finToList tail)) := by rfl
          _ = P.pr (HitsList E G [a]) *
              (residualAfter E G P [a]).pr (HitsList E G (finToList tail)) := hprob
          _ = _ := by simp [hone, residualAfter, safeCond]
      have htail := ih (P := safeCond P (fun y => Hits E G a y)) tail hparts.2
      have hq0 :
          (residualAfter E G P (finToList (prefixVals x (0 : Fin (k + 1))))).pr
            (fun y => Hits E G (x 0) y) = P.pr (fun y => Hits E G a y) := by
        have hprefix : prefixVals x (0 : Fin (k + 1)) =
            (fun j : Fin 0 => Fin.elim0 j) := by
          funext j
          exact Fin.elim0 j
        have hnil : finToList (prefixVals x (0 : Fin (k + 1))) = [] := by
          rw [hprefix]
          simp [finToList]
        rw [hnil]
        simp only [residualAfter, List.foldl_nil]
        rw [hx]
        simp [a]
      have hqtail (j : Fin k) :
          (residualAfter E G P (finToList (prefixVals x j.succ))).pr
              (fun y => Hits E G (x j.succ) y) =
            (residualAfter E G (safeCond P (fun y => Hits E G a y))
              (finToList (prefixVals tail j))).pr (fun y => Hits E G (tail j) y) := by
        have hlistTail : finToList (prefixVals x j.succ) = a :: finToList (prefixVals tail j) := by
          rw [hx, prefixVals_cons_succ, finToList_cons]
        rw [hlistTail]
        have hres := residualAfter_append E G P [a] (finToList (prefixVals tail j))
        have hres' : residualAfter E G P (a :: finToList (prefixVals tail j)) =
            residualAfter E G (safeCond P (fun y => Hits E G a y))
              (finToList (prefixVals tail j)) := by
          simpa [residualAfter] using hres
        rw [hres']
      calc
        P.pr (HitsList E G (finToList x)) =
            P.pr (fun y => Hits E G a y) *
              (safeCond P (fun y => Hits E G a y)).pr
                (HitsList E G (finToList tail)) := hprob'
        _ = P.pr (fun y => Hits E G a y) *
              (∏ j : Fin k,
                (residualAfter E G P (finToList (prefixVals x j.succ))).pr
                  (fun y => Hits E G (x j.succ) y)) := by
              rw [htail]
              congr 1
              apply Finset.prod_congr rfl
              intro j hj
              exact (hqtail j).symm
        _ = ∏ j : Fin (k + 1),
              (residualAfter E G P (finToList (prefixVals x j))).pr
                (fun y => Hits E G (x j) y) := by
              rw [Fin.prod_univ_succ]
              rw [← hq0]

private noncomputable def seqFill {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (s : Finset ι) (e : Fin m ≃ {i // i ∈ s}) (ω₀ : ι → α)
    (V : Fin m → α) : ι → α := fun i =>
  if hi : i ∈ s then V (e.symm ⟨i, hi⟩) else ω₀ i

private theorem pr_congr_local {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (h : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  simp [h ω]

private theorem pi_pr_seqFill {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (P : ι → FinProb α) {m : ℕ} (s : Finset ι)
    (e : Fin m ≃ {i // i ∈ s}) (ω₀ : ι → α) (A : (ι → α) → Prop)
    (hA : ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → A ω = A ω') :
    (FinProb.pi P).pr A =
      (FinProb.pi (fun j : Fin m => P (e j).1)).pr (fun V => A (seqFill s e ω₀ V)) := by
  classical
  let Psub : {i // i ∈ s} → FinProb α := fun i => P i.1
  let E := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ => α)
  let b₀ : ∀ i : {j // j ∉ s}, α := fun i => ω₀ i.1
  let Asub : (∀ i : {j // j ∈ s}, α) → Prop := fun a => A (E.symm (a, b₀))
  letI : DecidablePred (fun i : ι => i ∈ s) := fun i => Finset.decidableMem i s
  let ωc : ι → α := Classical.choice (nonempty_finProb (FinProb.pi P))
  let bc : ∀ i : {j // j ∉ s}, α := fun i => ωc i.1
  have hMargChoice : (FinProb.pi P).pr A =
      (FinProb.pi Psub).pr (fun a => A (E.symm (a, bc))) := by
    change (FinProb.pi P).pr A =
      (FinProb.pi (fun i : {j // j ∈ s} => P i.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s)
          (fun _ => α)).symm
            (a, fun i : {j // j ∉ s} =>
              (Classical.choice (nonempty_finProb (FinProb.pi P))) i.1)))
    exact pr_pi_depends_subset P s A hA
  have hAgree (a : ∀ i : {j // j ∈ s}, α) :
      ∀ i ∈ s, E.symm (a, bc) i = E.symm (a, b₀) i := by
    intro i hi
    simp [E, hi]
  have hPred (a : ∀ i : {j // j ∈ s}, α) :
      A (E.symm (a, bc)) ↔ A (E.symm (a, b₀)) := by
    exact Iff.of_eq (hA _ _ (hAgree a))
  have hMarg : (FinProb.pi P).pr A =
      (FinProb.pi Psub).pr (fun a => A (E.symm (a, b₀))) := by
    calc
      (FinProb.pi P).pr A =
          (FinProb.pi Psub).pr (fun a => A (E.symm (a, bc))) := hMargChoice
      _ = (FinProb.pi Psub).pr (fun a => A (E.symm (a, b₀))) := by
          apply pr_congr_local
          intro a
          exact hPred a
  have hLift (V : Fin m → α) :
      E.symm ((fun i : {j // j ∈ s} => V (e.symm i)), b₀) = seqFill s e ω₀ V := by
    funext i
    by_cases hi : i ∈ s
    · simp [E, seqFill, b₀, hi]
    · simp [E, seqFill, b₀, hi]
  have hReindex := pr_pi_reindex e Psub Asub
  calc
    (FinProb.pi P).pr A = (FinProb.pi Psub).pr Asub := by simpa [Asub] using hMarg
    _ = (FinProb.pi (fun j : Fin m => P (e j).1)).pr
          (fun V => A (seqFill s e ω₀ V)) := by
        rw [hReindex]
        apply pr_congr_local
        intro V
        rw [← hLift V]

private theorem HitsList_tupleLabels_iff {N k m : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (W : Fin m → Fin k → Fin N) (y : Fin N) :
    HitsList E G (tupleLabels W) y ↔ ∀ i j, Hits E G (W i j) y := by
  simp [HitsList, tupleLabels, finToList, List.mem_flatten]
  constructor
  · intro h i j
    exact h (W i j) i j rfl
  · intro h x i j hEq
    subst x
    exact h i j

private abbrev RelevantTuple {β γ : ℝ} {n : ℕ} (u : OddRole n)
    (D : Finset (Loc β γ n)) :=
  {ck : Loc β γ n × Key β γ n // ck ∈ D ×ˢ Zset β γ u}

private theorem HitsList_tupleLaw_iff {β γ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (u : OddRole n) (D : Finset (Loc β γ n)) (m : ℕ)
    (e : Fin m ≃ RelevantTuple u D)
    (W : Tuples β γ n N) (y : Fin N) :
    HitsList E G (tupleLabels (fun i => W (e i).1)) y ↔
      HitsAll E G W D (Zset β γ u) y := by
  rw [HitsList_tupleLabels_iff]
  constructor
  · intro h c hc κ hκ j
    let p : RelevantTuple u D := ⟨(c, κ), Finset.mem_product.mpr ⟨hc, hκ⟩⟩
    simpa using h (e.symm p) j
  · intro h i j
    rcases Finset.mem_product.mp (e i).2 with ⟨hc, hκ⟩
    exact h (e i).1.1 hc (e i).1.2 hκ j

private theorem HitsBut_tuplePrefix_iff {β γ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (u : OddRole n) (D : Finset (Loc β γ n)) (m : ℕ)
    (e : Fin m ≃ RelevantTuple u D) (last : Fin m)
    (hlastVal : last.val + 1 = m) (target : RelevantTuple u D) (hlast : e last = target)
    (W : Tuples β γ n N) (y : Fin N) :
    HitsBut E G W D (Zset β γ u) target.1.1 target.1.2 y ↔
      HitsList E G (tupleLabels (prefixVals (fun i => W (e i).1) last)) y := by
  have hList := HitsList_tupleLabels_iff E G
    (prefixVals (fun i : Fin m => W (e i).1) last) y
  rw [hList]
  constructor
  · intro h i j
    let r : Fin m := ⟨i.val, Nat.lt_trans i.isLt last.isLt⟩
    have hrne : r ≠ last := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [r] at hval
      omega
    have hpairne : (e r).1 ≠ target.1 := by
      intro heq
      apply hrne
      apply e.injective
      exact Subtype.ext heq |>.trans hlast.symm
    rcases Finset.mem_product.mp (e r).2 with ⟨hc, hκ⟩
    have hhit := h (e r).1.1 hc (e r).1.2 hκ hpairne j
    simpa [r, prefixVals] using hhit
  · intro h c hc κ hκ hne j
    let q : RelevantTuple u D := ⟨(c, κ), Finset.mem_product.mpr ⟨hc, hκ⟩⟩
    let r : Fin m := e.symm q
    have hqne : q ≠ target := by
      intro hEq
      apply hne
      exact congrArg Subtype.val hEq
    have hrne : r ≠ last := by
      intro hr
      apply hqne
      calc
        q = e r := (Equiv.apply_symm_apply e q).symm
        _ = e last := congrArg e hr
        _ = target := hlast
    have hrlt : r.val < last.val := by
      have hrltm := r.isLt
      have hlastm : last.val < m := last.isLt
      omega
    let jp : Fin last.val := ⟨r.val, hrlt⟩
    have hprefix : prefixVals (fun i : Fin m => W (e i).1) last jp =
        (W (e r).1) := by
      simp [prefixVals, jp, r]
    have her : e r = q := Equiv.apply_symm_apply e q
    have hW : W (e r).1 = W (c, κ) := by
      have hval := congrArg Subtype.val her
      simpa [q] using congrArg W hval
    have hhit := h jp j
    rw [hprefix, hW] at hhit
    exact hhit

private theorem pr_congr {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (h : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  simp [h ω]

private theorem mass_fail_implies_outerFirstBad {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n)) (m : ℕ)
    (hcount : m = D.card * (Zset β γ u).card)
    (e : Fin m ≃ RelevantTuple u D)
    (W : Tuples β γ n N)
    (hMass : (maskLaw (ym u)).pr
        (HitsAll E G W D (Zset β γ u)) <
      Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) *
        ((Zset β γ u).card : ℝ)))) :
    OuterFirstBad E G (capL β γ n)
      (maskLaw (ym u))
      (fun i => W (e i).1) := by
  classical
  let P₀ := maskLaw (ym u)
  let V : Fin m → Fin (tupLen β γ n) → Fin N :=
    fun i => W (e i).1
  have hHits : P₀.pr (HitsAll E G W D (Zset β γ u)) =
      P₀.pr (HitsList E G (tupleLabels V)) := by
    apply pr_congr P₀
    intro y
    exact (HitsList_tupleLaw_iff u D m e W y).symm
  by_contra hnot
  have hGood : GoodPath E G (capL β γ n) P₀ (tupleLabels V) := by
    by_contra hbad
    have hfirst := (not_GoodPath_iff_FirstBad E G (capL β γ n) P₀
      (tupleLabels V)).mp hbad
    exact hnot ((FirstBad_tupleLabels_iff E G (capL β γ n) P₀ V).mp hfirst)
  have hLower := pr_HitsList_lower E G P₀ (tupleLabels V) (capL β γ n) hGood
  have hExp : Real.exp (-((tupleLabels V).length : ℝ) * capL β γ n) =
      Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) *
        ((Zset β γ u).card : ℝ))) := by
    congr 1
    rw [tupleLabels_length]
    rw [hcount]
    push_cast
    ring
  rw [hHits] at hMass
  rw [← hExp] at hMass
  exact (not_lt_of_ge hLower) hMass

private theorem cross_fail_implies_outerFirstBad {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n)) (m : ℕ)
    (e : Fin m ≃ RelevantTuple u D) (last : Fin m)
    (hlast : last.val + 1 = m) (target : RelevantTuple u D) (he : e last = target)
    (W : Tuples β γ n N) (hown : target.1.2 ≠ key β γ n u.1)
    (hCross : (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
      ratioThr β γ u target.1.2 *
        (maskLaw (ym u)).pr
          (HitsBut E G W D (Zset β γ u) target.1.1 target.1.2)) :
    OuterFirstBad E G (capL β γ n) (maskLaw (ym u)) (fun i => W (e i).1) := by
  classical
  let P₀ := maskLaw (ym u)
  let V : Fin m → Fin (tupLen β γ n) → Fin N := fun i => W (e i).1
  let base := tupleLabels (prefixVals V last)
  let targetLabels := finToList (V last)
  have hsplit : tupleLabels V = base ++ targetLabels :=
    tupleLabels_split_last V last hlast
  by_contra hnot
  have hGood : GoodPath E G (capL β γ n) P₀ (tupleLabels V) := by
    by_contra hbad
    have hfirst := (not_GoodPath_iff_FirstBad E G (capL β γ n) P₀ (tupleLabels V)).mp hbad
    exact hnot ((FirstBad_tupleLabels_iff E G (capL β γ n) P₀ V).mp hfirst)
  have hGood' : GoodPath E G (capL β γ n) P₀ (base ++ targetLabels) := by
    simpa [base, targetLabels, hsplit] using hGood
  have hParts := (GoodPath_append E G (capL β γ n) P₀ base targetLabels).1 hGood'
  have hAll : P₀.pr (HitsAll E G W D (Zset β γ u)) =
      P₀.pr (HitsList E G (tupleLabels V)) := by
    apply pr_congr P₀
    intro y
    exact (HitsList_tupleLaw_iff u D m e W y).symm
  have hBut :
      P₀.pr (HitsBut E G W D (Zset β γ u) target.1.1 target.1.2) =
        P₀.pr (HitsList E G base) := by
    apply pr_congr P₀
    intro y
    simpa [base, V] using (HitsBut_tuplePrefix_iff u D m e last hlast target he W y)
  have hTargetLower := pr_HitsList_lower E G
    (residualAfter E G P₀ base) targetLabels (capL β γ n) hParts.2
  have hbasePos : 0 < P₀.pr (HitsList E G base) := by
    exact lt_of_lt_of_le (Real.exp_pos _)
      (pr_HitsList_lower E G P₀ base (capL β γ n) hParts.1)
  have hbaseNonneg : 0 ≤ P₀.pr (HitsList E G base) := hbasePos.le
  have hmassAppend := pr_HitsList_append E G P₀ base targetLabels (capL β γ n) hGood'
  have hbound :
      Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) *
          P₀.pr (HitsList E G base) ≤ P₀.pr (HitsList E G (tupleLabels V)) := by
    have htailLen : (targetLabels.length : ℝ) = tupLen β γ n := by
      simp [targetLabels, finToList]
    have htailExp : Real.exp (-(targetLabels.length : ℝ) * capL β γ n) =
        Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) := by
      rw [htailLen]
      congr 1
      ring
    have htailLower :
        Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) ≤
          (residualAfter E G P₀ base).pr (HitsList E G targetLabels) := by
      simpa [htailLen] using hTargetLower
    calc
      Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) *
          P₀.pr (HitsList E G base) ≤
        P₀.pr (HitsList E G base) *
          (residualAfter E G P₀ base).pr (HitsList E G targetLabels) := by
            calc
              _ = P₀.pr (HitsList E G base) *
                  Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left htailLower hbaseNonneg
      _ = P₀.pr (HitsList E G (base ++ targetLabels)) := hmassAppend.symm
      _ = P₀.pr (HitsList E G (tupleLabels V)) := by rw [← hsplit]
  have hCross' :
      P₀.pr (HitsAll E G W D (Zset β γ u)) <
        Real.exp (-((tupLen β γ n : ℝ) * capL β γ n)) *
          P₀.pr (HitsList E G base) := by
    have hCross'' := hCross
    rw [hBut] at hCross''
    simpa [P₀, ratioThr, hown, mul_comm, mul_left_comm, mul_assoc] using hCross''
  rw [hAll] at hCross'
  exact (not_lt_of_ge hbound) hCross'

private theorem exists_fin_equiv_last {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∃ (e : Fin (Fintype.card α) ≃ α) (last : Fin (Fintype.card α)),
      last.val + 1 = Fintype.card α ∧ e last = a := by
  classical
  let m := Fintype.card α
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨a⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm.ne'
  let last : Fin m := ⟨m - 1, Nat.sub_lt hm (by decide)⟩
  let e0 : α ≃ Fin m := Fintype.equivFin α
  let e : Fin m ≃ α := (Equiv.swap (e0 a) last).trans e0.symm
  refine ⟨e, last, ?_, ?_⟩
  · dsimp [last]
    exact Nat.sub_add_cancel hm1
  · dsimp [e]
    calc
      e0.symm (Equiv.swap (e0 a) last last) = e0.symm (e0 a) := by simp
      _ = a := e0.symm_apply_apply a

private theorem tuple_entry_bad_prob {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (i : M.ι) (S : Mask (M.μ i)) (P₀ : Law N)
    (hEntry : EntryLow M) (hSupp : Law.SupportedIn P₀ Y) (base : List (Fin N))
    (gate : Prop)
    (hWidth : gate → ∀ xs, xs.length ≤ tupLen β γ n →
      GoodPath E G (capL β γ n) P₀ (base ++ xs) →
      Law.WidthLE (residualAfter E G P₀ (base ++ xs)) (2 * (n : ℝ) ^ γ)) :
    (FinProb.pi (fun _ : Fin (tupLen β γ n) => maskLaw S)).pr
      (fun x => ∃ j : Fin (tupLen β γ n),
        gate ∧ GoodPath E G (capL β γ n) P₀ (base ++ finToList (prefixVals x j)) ∧
          rowDeg E G (x j)
              (residualAfter E G P₀ (base ++ finToList (prefixVals x j))) <
            Real.exp (-capL β γ n)) ≤
      (tupLen β γ n : ℝ) *
        Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4)) := by
  classical
  let bad : ∀ j : Fin (tupLen β γ n), (Fin j.val → Fin N) → Fin N → Prop :=
    fun j p x =>
      gate ∧ GoodPath E G (capL β γ n) P₀ (base ++ finToList p) ∧
        rowDeg E G x (residualAfter E G P₀ (base ++ finToList p)) < Real.exp (-capL β γ n)
  have hbound : ∀ j p,
      (maskLaw S).pr (bad j p) ≤
        Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4)) := by
    intro j p
    by_cases hgate : gate
    · by_cases hgood : GoodPath E G (capL β γ n) P₀ (base ++ finToList p)
      · let η := residualAfter E G P₀ (base ++ finToList p)
        have hηsupp : Law.SupportedIn η Y := by
          exact residualAfter_supportedIn E G P₀ (base ++ finToList p) hSupp
        have hplen : (finToList p).length ≤ tupLen β γ n := by
          simpa [finToList] using j.isLt
        have hηwidth : Law.WidthLE η (2 * (n : ℝ) ^ γ) :=
          hWidth hgate (finToList p) hplen hgood
        have hEntry' := hEntry i S η hηsupp hηwidth
        have hExp : -((n : ℝ) ^ (β - omega4 β γ / 2)) / 4 =
            -((n : ℝ) ^ (β - omega4 β γ / 2) / 4) := by ring
        simpa [bad, η, hgate, hgood, hExp] using hEntry'
      · have hzero : (maskLaw S).pr (bad j p) = 0 := by
          unfold FinProb.pr
          apply Finset.sum_eq_zero
          intro x hx
          simp [bad, hgood, hgate]
        rw [hzero]
        exact Real.exp_nonneg _
    · have hzero : (maskLaw S).pr (bad j p) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro x hx
        simp [bad, hgate]
      rw [hzero]
      exact Real.exp_nonneg _
  simpa [bad, finToList] using
    (pi_pr_exists_bad_le (tupLen β γ n)
      (fun _ : Fin (tupLen β γ n) => maskLaw S) bad
      (Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4))) hbound)

private theorem tupleArray_firstBad_bound {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n)
    (m : ℕ) (s : Finset (Loc β γ n × Key β γ n))
    (e : Fin m ≃ {ck : Loc β γ n × Key β γ n // ck ∈ s})
    (hEntry : EntryLow M)
    (hWidth : ∀ (i : Fin m)
      (q : Fin i.val → Fin (tupLen β γ n) → Fin N) (xs : List (Fin N)),
      xs.length ≤ tupLen β γ n →
      GoodPath E G (capL β γ n)
        (maskLaw (ym u)) (tupleLabels q ++ xs) →
      Law.WidthLE (residualAfter E G (maskLaw (ym u)) (tupleLabels q ++ xs))
        (2 * (n : ℝ) ^ γ)) :
    (FinProb.pi (fun i : Fin m =>
      FinProb.pi (fun _ : Fin (tupLen β γ n) => maskLaw (xm (e i).1)))).pr
      (OuterFirstBad E G (capL β γ n) (maskLaw (ym u))) ≤
      (m : ℝ) * (tupLen β γ n : ℝ) *
        Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4)) := by
  classical
  let P : Fin m → FinProb (Fin (tupLen β γ n) → Fin N) :=
    fun i => FinProb.pi (fun _ : Fin (tupLen β γ n) => maskLaw (xm (e i).1))
  let bad : ∀ i : Fin m,
      (Fin i.val → (Fin (tupLen β γ n) → Fin N)) →
      (Fin (tupLen β γ n) → Fin N) → Prop :=
    fun i q W =>
      GoodPath E G (capL β γ n) (maskLaw (ym u)) (tupleLabels q) ∧
      ∃ j : Fin (tupLen β γ n),
        GoodPath E G (capL β γ n) (maskLaw (ym u))
          (tupleLabels q ++ finToList (prefixVals W j)) ∧
        rowDeg E G (W j) (residualAfter E G (maskLaw (ym u))
          (tupleLabels q ++ finToList (prefixVals W j))) < Real.exp (-capL β γ n)
  have hstep : ∀ i q,
      (P i).pr (bad i q) ≤
        (tupLen β γ n : ℝ) * Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4)) := by
    intro i q
    let p := e i
    let ck := p.1
    let base := tupleLabels q
    let gate := GoodPath E G (capL β γ n) (maskLaw (ym u)) base
    have hsupp : Law.SupportedIn (maskLaw (ym u)) Y :=
      mask_supported (M.ν_supp (tag (key β γ n u.1)))
    have hWidth' : gate → ∀ xs, xs.length ≤ tupLen β γ n →
        GoodPath E G (capL β γ n) (maskLaw (ym u)) (base ++ xs) →
        Law.WidthLE (residualAfter E G (maskLaw (ym u)) (base ++ xs))
          (2 * (n : ℝ) ^ γ) := by
      intro hgate xs hxs hgood
      exact hWidth i q xs hxs hgood
    have h := tuple_entry_bad_prob M (tag ck.2) (xm ck) (maskLaw (ym u))
      hEntry hsupp base gate hWidth'
    simpa [P, bad, p, ck, base, gate] using h
  have hEvent : (fun W => ∃ i, bad i (prefixVals W i) (W i)) =
      OuterFirstBad E G (capL β γ n) (maskLaw (ym u)) := by
    funext W
    simp [bad, OuterFirstBad]
  have hprob := pi_pr_exists_bad_le m P bad
    ((tupLen β γ n : ℝ) * Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4))) hstep
  calc
    (FinProb.pi P).pr (OuterFirstBad E G (capL β γ n) (maskLaw (ym u))) =
      (FinProb.pi P).pr (fun W => ∃ i, bad i (prefixVals W i) (W i)) := by
        rw [← hEvent]
    _ ≤ _ := by simpa [P, mul_assoc, mul_comm, mul_left_comm] using hprob

set_option maxHeartbeats 1000000 in
private theorem tupleLaw_firstBad_bound {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n)
    (m : ℕ) (s : Finset (Loc β γ n × Key β γ n))
    (e : Fin m ≃ {ck : Loc β γ n × Key β γ n // ck ∈ s})
    (hEntry : EntryLow M)
    (hWidth : ∀ (i : Fin m)
      (q : Fin i.val → Fin (tupLen β γ n) → Fin N) (xs : List (Fin N)),
      xs.length ≤ tupLen β γ n →
      GoodPath E G (capL β γ n) (maskLaw (ym u)) (tupleLabels q ++ xs) →
      Law.WidthLE (residualAfter E G (maskLaw (ym u)) (tupleLabels q ++ xs))
        (2 * (n : ℝ) ^ γ)) :
    (tupleLaw M tag xm).pr (fun W =>
      OuterFirstBad E G (capL β γ n) (maskLaw (ym u)) (fun i => W (e i).1)) ≤
      (m : ℝ) * (tupLen β γ n : ℝ) *
        Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2) / 4)) := by
  let Ppair : (Loc β γ n × Key β γ n) → FinProb (Fin (tupLen β γ n) → Fin N) :=
    fun ck => FinProb.pi (fun _ : Fin (tupLen β γ n) => maskLaw (xm ck))
  let SeqBad : (Fin m → Fin (tupLen β γ n) → Fin N) → Prop :=
    OuterFirstBad E G (capL β γ n) (maskLaw (ym u))
  let A : (Loc β γ n × Key β γ n → Fin (tupLen β γ n) → Fin N) → Prop :=
    fun W => SeqBad (fun i => W (e i).1)
  have hA : ∀ W W', (∀ ck ∈ s, W ck = W' ck) → A W = A W' := by
    intro W W' hagree
    have hseq : (fun i => W (e i).1) = (fun i => W' (e i).1) := by
      funext i
      exact hagree (e i).1 (e i).2
    simp [A, hseq]
  letI : DecidablePred (fun ck : Loc β γ n × Key β γ n => ck ∈ s) :=
    fun ck => Finset.decidableMem ck s
  letI : DecidableEq {ck : Loc β γ n × Key β γ n // ck ∈ s} := Subtype.instDecidableEq
  have hMarg : (FinProb.pi Ppair).pr A =
      (FinProb.pi (fun p : {ck : Loc β γ n × Key β γ n // ck ∈ s} => Ppair p.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun ck => ck ∈ s)
          (fun _ => Fin (tupLen β γ n) → Fin N)).symm
            (a, fun p => (Classical.choice (nonempty_finProb (FinProb.pi Ppair))) p.1))) := by
    change (FinProb.pi Ppair).pr A =
      (FinProb.pi (fun p : {ck : Loc β γ n × Key β γ n // ck ∈ s} => Ppair p.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun ck => ck ∈ s)
          (fun _ => Fin (tupLen β γ n) → Fin N)).symm
            (a, fun p => (Classical.choice (nonempty_finProb (FinProb.pi Ppair))) p.1)))
    exact pr_pi_depends_subset Ppair s A hA
  let Eprod := Equiv.piEquivPiSubtypeProd (fun ck : Loc β γ n × Key β γ n => ck ∈ s)
    (fun _ => Fin (tupLen β γ n) → Fin N)
  let ω₀ := Classical.choice (nonempty_finProb (FinProb.pi Ppair))
  let b₀ : ∀ p : {ck : Loc β γ n × Key β γ n // ck ∉ s},
      Fin (tupLen β γ n) → Fin N := fun p => ω₀ p.1
  let lift (a : {ck : Loc β γ n × Key β γ n // ck ∈ s} → Fin (tupLen β γ n) → Fin N) :=
    Eprod.symm (a, b₀)
  let Psub : {ck : Loc β γ n × Key β γ n // ck ∈ s} →
      FinProb (Fin (tupLen β γ n) → Fin N) :=
    fun p => Ppair p.1
  let Asub : (({ck : Loc β γ n × Key β γ n // ck ∈ s}) →
      Fin (tupLen β γ n) → Fin N) → Prop :=
    fun a => A (lift a)
  have hProj : ∀ a,
      (fun i => lift a (e i).1) = (fun i => a (e i)) := by
    intro a
    funext i
    simp [lift, Eprod, Equiv.piEquivPiSubtypeProd, (e i).2]
  have hSeq : (fun V => Asub (fun p => V (e.symm p))) = SeqBad := by
    funext V
    change SeqBad (fun i => lift (fun p => V (e.symm p)) (e i).1) = SeqBad V
    rw [hProj]
    congr 1
    funext i
    simp
  have hReindex := pr_pi_reindex e Psub Asub
  have hSeqBound := tupleArray_firstBad_bound M tag xm ym u m s e hEntry hWidth
  calc
    (tupleLaw M tag xm).pr (fun W => SeqBad (fun i => W (e i).1)) =
        (FinProb.pi Ppair).pr A := by
          rfl
    _ = (FinProb.pi Psub).pr Asub := by
          simpa [Psub, Asub, lift, Eprod, b₀, ω₀, Ppair] using hMarg
    _ = (FinProb.pi (fun i => Psub (e i))).pr SeqBad := by
          rw [hReindex]
          rw [hSeq]
    _ ≤ _ := by
          simpa [Psub, Ppair] using hSeqBound

private theorem eventual_width_budget_factors (β γ : ℝ) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (setBd β γ n : ℝ) ≤ 4 * (n : ℝ) ^ (omega4 β γ / 30) ∧
      (tupLen β γ n : ℝ) ≤ 2 * (n : ℝ) ^ (omega4 β γ / 3) ∧
      8 * (n : ℝ) ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) ≤ (n : ℝ) ^ γ / 4 ∧
      1 + Real.log 2 ≤ (n : ℝ) ^ γ / 4 := by
  let ω := omega4 β γ
  let b := ω / 30
  let a := ω / 3
  let d := ω / 2
  have hω : 0 < ω := omega4_pos hβ hγ
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hγpos : 0 < γ := lt_of_lt_of_le hβ hβγ
  obtain ⟨nB, hPowB⟩ := eventually_rpow_gt (c := 1) hb
  obtain ⟨nA, hPowA⟩ := eventually_rpow_gt (c := 1) ha
  obtain ⟨nD, hPowD⟩ := eventually_rpow_gt (c := 32) hd
  obtain ⟨nγ, hPowγ⟩ := eventually_rpow_gt (c := 4 * (1 + Real.log 2)) hγpos
  let n₀ := max 1 (max nB (max nA (max nD nγ)))
  refine ⟨n₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnB : nB ≤ n := by omega
  have hnA : nA ≤ n := by omega
  have hnD : nD ≤ n := by omega
  have hnγ : nγ ≤ n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnr1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hbOne : 1 ≤ (n : ℝ) ^ b := Real.one_le_rpow hnr1 hb.le
  have haOne : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hnr1 ha.le
  have hceilB : (setBd β γ n : ℝ) < 3 * (n : ℝ) ^ b + 1 := by
    change (⌈3 * (n : ℝ) ^ b⌉₊ : ℝ) < 3 * (n : ℝ) ^ b + 1
    exact Nat.ceil_lt_add_one (by positivity)
  have hceilA : (tupLen β γ n : ℝ) < (n : ℝ) ^ a + 1 := by
    change (⌈(n : ℝ) ^ a⌉₊ : ℝ) < (n : ℝ) ^ a + 1
    exact Nat.ceil_lt_add_one (by positivity)
  have hset : (setBd β γ n : ℝ) ≤ 4 * (n : ℝ) ^ b := by linarith
  have htuple : (tupLen β γ n : ℝ) ≤ 2 * (n : ℝ) ^ a := by linarith
  have hexp : γ - 8 / 15 * ω + h4 β γ ≤ γ - ω / 2 := by
    dsimp [ω, h4]
    nlinarith [hω]
  have hpowMono : (n : ℝ) ^ (γ - 8 / 15 * ω + h4 β γ) ≤
      (n : ℝ) ^ (γ - ω / 2) := Real.rpow_le_rpow_of_exponent_le hnr1 hexp
  have hfactor : 8 * (n : ℝ) ^ (γ - ω / 2) ≤ (n : ℝ) ^ γ / 4 := by
    have h32 : 32 ≤ (n : ℝ) ^ d := (hPowD n hnD).le
    have hnonneg : 0 ≤ (n : ℝ) ^ (γ - ω / 2) :=
      (Real.rpow_pos_of_pos hnr _).le
    have hmul := mul_le_mul_of_nonneg_right h32 hnonneg
    have heq : (n : ℝ) ^ d * (n : ℝ) ^ (γ - ω / 2) = (n : ℝ) ^ γ := by
      rw [← Real.rpow_add hnr d (γ - ω / 2)]
      congr 1
      dsimp [d, ω]
      ring
    rw [heq] at hmul
    nlinarith
  refine ⟨hset, htuple, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hpowMono (by norm_num)).trans hfactor
  · have h := hPowγ n hnγ
    linarith

private theorem residual_width_budget_of_length {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (u : OddRole n) (D : Finset (Loc β γ n))
    (S₀ : Mask (M.ν (tag (key β γ n u.1))))
    (hn : 1 ≤ n)
    (hD : D.card ≤ setBd β γ n) (hKey : KeyNbrCard β γ n)
    (hset : (setBd β γ n : ℝ) ≤ 4 * (n : ℝ) ^ (omega4 β γ / 30))
    (htuple : (tupLen β γ n : ℝ) ≤ 2 * (n : ℝ) ^ (omega4 β γ / 3))
    (hcost : 8 * (n : ℝ) ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) ≤ (n : ℝ) ^ γ / 4)
    (hlog : 1 + Real.log 2 ≤ (n : ℝ) ^ γ / 4)
    (xs : List (Fin N))
    (hxs : xs.length ≤ tupLen β γ n * D.card * (Zset β γ u).card)
    (hgood : GoodPath E G (capL β γ n) (maskLaw S₀) xs) :
    Law.WidthLE (residualAfter E G (maskLaw S₀) xs) (2 * (n : ℝ) ^ γ) := by
  let i := tag (key β γ n u.1)
  let r := (n : ℝ)
  let a := omega4 β γ / 3
  let b := omega4 β γ / 30
  let z := γ - 9 / 10 * omega4 β γ
  let h := h4 β γ
  have hnr : 0 < r := by
    dsimp [r]
    exact_mod_cast (show 0 < n by omega)
  have hnr1 : 1 ≤ r := by dsimp [r]; exact_mod_cast hn
  have hDreal : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by exact_mod_cast hD
  have hZreal : ((Zset β γ u).card : ℝ) ≤ r ^ z := hKey u
  have hD4 : (D.card : ℝ) ≤ 4 * r ^ b := hDreal.trans (by simpa [r, b] using hset)
  have hKD : (tupLen β γ n : ℝ) * (D.card : ℝ) ≤
      (2 * r ^ a) * (4 * r ^ b) := by
    exact mul_le_mul htuple hD4 (by positivity) (by positivity)
  have hKDZ : (tupLen β γ n : ℝ) * (D.card : ℝ) *
      ((Zset β γ u).card : ℝ) ≤ ((2 * r ^ a) * (4 * r ^ b)) * r ^ z :=
    mul_le_mul hKD hZreal (by positivity) (by positivity)
  have hpowProd : r ^ a * r ^ b * r ^ z * r ^ h =
      r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
    calc
      r ^ a * r ^ b * r ^ z * r ^ h = (r ^ a * r ^ b) * (r ^ z * r ^ h) := by ring
      _ = r ^ (a + b) * r ^ (z + h) := by
        rw [← Real.rpow_add hnr a b, ← Real.rpow_add hnr z h]
      _ = r ^ ((a + b) + (z + h)) := (Real.rpow_add hnr (a + b) (z + h)).symm
      _ = r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
        congr 1
        dsimp [a, b, z, h]
        ring
  have htotalCost :
      ((tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ)) *
          capL β γ n ≤ (n : ℝ) ^ γ / 4 := by
    calc
      ((tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ)) * capL β γ n ≤
      ((2 * r ^ a) * (4 * r ^ b) * r ^ z) * r ^ h := by
            exact mul_le_mul_of_nonneg_right hKDZ (Real.rpow_pos_of_pos hnr h).le
      _ = 8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
            calc
              ((2 * r ^ a) * (4 * r ^ b) * r ^ z) * r ^ h =
                  8 * (r ^ a * r ^ b * r ^ z * r ^ h) := by ring
              _ = 8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by rw [hpowProd]
      _ ≤ r ^ γ / 4 := by simpa [r] using hcost
  have hxsReal : (xs.length : ℝ) ≤
      (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ) := by
    exact_mod_cast hxs
  have hxsCost : (xs.length : ℝ) * capL β γ n ≤ (n : ℝ) ^ γ / 4 := by
    exact (mul_le_mul_of_nonneg_right hxsReal (Real.rpow_pos_of_pos hnr h).le).trans htotalCost
  have hνWidth : Law.WidthLE (M.ν i) (M.sY i + 1) := (M.prep i).2.2.2.2.2.1
  have hSY : M.sY i ≤ 3 / 2 * (n : ℝ) ^ γ := (M.prep i).2.2.2.1
  have hbase : Law.WidthLE (maskLaw S₀) (3 / 2 * (n : ℝ) ^ γ + 1 + Real.log 2) := by
    have hm := mask_width S₀ hνWidth
    exact hm.mono (by linarith)
  have htail := residualAfter_width E G (maskLaw S₀) xs hbase hgood
  apply Law.WidthLE.mono htail
  have hbaseBudget : 3 / 2 * (n : ℝ) ^ γ + 1 + Real.log 2 ≤
      7 / 4 * (n : ℝ) ^ γ := by linarith [hlog]
  linarith [hxsCost, hbaseBudget]

private theorem eventual_residual_width_budget (β γ : ℝ) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (u : OddRole n)
      (tag : Key β γ n → M.ι) (D : Finset (Loc β γ n))
      (S₀ : Mask (M.ν (tag (key β γ n u.1)))),
      D.card ≤ setBd β γ n → KeyNbrCard β γ n →
      ∀ xs, xs.length ≤ tupLen β γ n * D.card * (Zset β γ u).card →
      GoodPath E G (capL β γ n) (maskLaw S₀) xs →
      Law.WidthLE (residualAfter E G (maskLaw S₀) xs) (2 * (n : ℝ) ^ γ) := by
  obtain ⟨n₀, hFactors⟩ := eventual_width_budget_factors β γ hβ hβγ hγ
  refine ⟨max n₀ 1, ?_⟩
  intro n hn N E G X Y M u tag D S₀ hD hKey xs hxs hgood
  have hn1 : 1 ≤ n := by omega
  have hnFactors : n₀ ≤ n := by omega
  exact residual_width_budget_of_length M tag u D S₀ hn1 hD hKey
    (hFactors n hnFactors).1 (hFactors n hnFactors).2.1
    (hFactors n hnFactors).2.2.1 (hFactors n hnFactors).2.2.2
    xs hxs hgood

private theorem residual_own_width_budget_of_length {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (u : OddRole n) (S₀ : Mask (M.ν (tag (key β γ n u.1))))
    (xs : List (Fin N))
    (hcost : (xs.length : ℝ) * capL β γ n ≤ (n : ℝ) ^ (γ - omega4 β γ / 2) / 8)
    (hlog : 1 + Real.log 2 ≤ (n : ℝ) ^ (γ - omega4 β γ / 2) / 8)
    (hgood : GoodPath E G (capL β γ n) (maskLaw S₀) xs) :
    Law.WidthLE (residualAfter E G (maskLaw S₀) xs)
      (M.sY (tag (key β γ n u.1)) + (n : ℝ) ^ (γ - omega4 β γ / 2) / 4) := by
  let i := tag (key β γ n u.1)
  have hνWidth : Law.WidthLE (M.ν i) (M.sY i + 1) := (M.prep i).2.2.2.2.2.1
  have hbase : Law.WidthLE (maskLaw S₀) (M.sY i + 1 + Real.log 2) := by
    have hm := mask_width S₀ hνWidth
    exact hm.mono (by rfl)
  have htail := residualAfter_width E G (maskLaw S₀) xs hbase hgood
  apply Law.WidthLE.mono htail
  linarith [hcost, hlog]

private theorem eventual_own_residual_width_budget (β γ : ℝ) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (u : OddRole n)
      (tag : Key β γ n → M.ι) (D : Finset (Loc β γ n))
      (S₀ : Mask (M.ν (tag (key β γ n u.1)))) (xs : List (Fin N)),
      D.card ≤ setBd β γ n → KeyNbrCard β γ n →
      xs.length ≤ tupLen β γ n * D.card * (Zset β γ u).card →
      GoodPath E G (capL β γ n) (maskLaw S₀) xs →
      Law.WidthLE (residualAfter E G (maskLaw S₀) xs)
        (M.sY (tag (key β γ n u.1)) + (n : ℝ) ^ (γ - omega4 β γ / 2) / 4) := by
  let ω := omega4 β γ
  let gap := ω / 30 - h4 β γ
  let margin := γ - ω / 2
  have hω : 0 < ω := omega4_pos hβ hγ
  have hωβ : ω ≤ β / 1000 := by
    dsimp [ω, omega4]
    exact div_le_div_of_nonneg_right (min_le_left β (1 - γ)) (by norm_num)
  have hgap : 0 < gap := by dsimp [gap, h4]; nlinarith [hω]
  have hmargin : 0 < margin := by dsimp [margin]; nlinarith [hβγ, hωβ]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨nFactors, hFactors⟩ := eventual_width_budget_factors β γ hβ hβγ hγ
  obtain ⟨nGap, hGap⟩ := eventually_rpow_gt (a := gap) (c := 64) hgap
  obtain ⟨nMargin, hMargin⟩ := eventually_rpow_gt (a := margin)
    (c := 8 * (1 + Real.log 2)) hmargin
  refine ⟨max 1 (max nFactors (max nGap nMargin)), ?_⟩
  intro n hn N E G X Y M u tag D S₀ xs hD hKey hxs hgood
  have hnOne : 1 ≤ n := le_trans (Nat.le_max_left 1 _) hn
  have hnFactors : nFactors ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_left nFactors (max nGap nMargin))
      (Nat.le_max_right 1 (max nFactors (max nGap nMargin)))
  have hnGap : nGap ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_left nGap nMargin)
      (le_trans (Nat.le_max_right nFactors (max nGap nMargin))
        (Nat.le_max_right 1 (max nFactors (max nGap nMargin))))
  have hnMargin : nMargin ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_right nGap nMargin)
      (le_trans (Nat.le_max_right nFactors (max nGap nMargin))
        (Nat.le_max_right 1 (max nFactors (max nGap nMargin))))
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hnr : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  let r := (n : ℝ)
  let a := omega4 β γ / 3
  let b := omega4 β γ / 30
  let z := γ - 9 / 10 * omega4 β γ
  let h := h4 β γ
  have hset := (hFactors n hnFactors).1
  have htuple := (hFactors n hnFactors).2.1
  have hDreal : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by exact_mod_cast hD
  have hDbound : (D.card : ℝ) ≤ 4 * r ^ b := hDreal.trans (by simpa [r, b] using hset)
  have hZbound : ((Zset β γ u).card : ℝ) ≤ r ^ z := hKey u
  have hKD : (tupLen β γ n : ℝ) * (D.card : ℝ) ≤ (2 * r ^ a) * (4 * r ^ b) :=
    mul_le_mul htuple (by simpa [r, b] using hDbound) (by positivity) (by positivity)
  have hKDZ : (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ) ≤
      ((2 * r ^ a) * (4 * r ^ b)) * r ^ z :=
    mul_le_mul hKD hZbound (by positivity) (by positivity)
  have hpowProd : r ^ a * r ^ b * r ^ z * r ^ h =
      r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
    calc
      r ^ a * r ^ b * r ^ z * r ^ h = (r ^ a * r ^ b) * (r ^ z * r ^ h) := by ring
      _ = r ^ (a + b) * r ^ (z + h) := by
        rw [← Real.rpow_add hnr a b, ← Real.rpow_add hnr z h]
      _ = r ^ ((a + b) + (z + h)) := (Real.rpow_add hnr (a + b) (z + h)).symm
      _ = r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
        congr 1
        dsimp [a, b, z, h]
        ring
  have hcostRaw : (xs.length : ℝ) * capL β γ n ≤
      8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
    have hxsReal : (xs.length : ℝ) ≤
        (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ) := by
      exact_mod_cast hxs
    calc
      (xs.length : ℝ) * capL β γ n ≤
          ((tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ)) * r ^ h := by
            exact mul_le_mul_of_nonneg_right hxsReal (Real.rpow_pos_of_pos hnr h).le
      _ ≤ ((2 * r ^ a) * (4 * r ^ b) * r ^ z) * r ^ h := by
            exact mul_le_mul_of_nonneg_right hKDZ (Real.rpow_pos_of_pos hnr h).le
      _ = 8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by
            calc
              ((2 * r ^ a) * (4 * r ^ b) * r ^ z) * r ^ h =
                  8 * (r ^ a * r ^ b * r ^ z * r ^ h) := by ring
              _ = 8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := by rw [hpowProd]
  have hgapPow : 64 < r ^ gap := by simpa [r, gap] using hGap n hnGap
  have hmarginPow : 8 * (1 + Real.log 2) < r ^ margin := by
    simpa [r, margin] using hMargin n hnMargin
  have hsplit : r ^ margin =
      r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) * r ^ gap := by
    rw [← Real.rpow_add hnr (γ - 8 / 15 * omega4 β γ + h4 β γ) gap]
    congr 1
    dsimp [gap, margin, h4]
    ring
  have hcost : (xs.length : ℝ) * capL β γ n ≤ r ^ margin / 8 := by
    have hcoeff : 8 ≤ r ^ gap / 8 := by nlinarith [hgapPow]
    have hpos : 0 < r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) :=
      Real.rpow_pos_of_pos hnr _
    have hmul := mul_le_mul_of_nonneg_left hcoeff hpos.le
    calc
      (xs.length : ℝ) * capL β γ n ≤
          8 * r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) := hcostRaw
      _ ≤ r ^ (γ - 8 / 15 * omega4 β γ + h4 β γ) * r ^ gap / 8 := by
          nlinarith [hmul]
      _ = r ^ margin / 8 := by rw [← hsplit]
  have hlog : 1 + Real.log 2 ≤ r ^ margin / 8 := by nlinarith [hmarginPow]
  exact residual_own_width_budget_of_length M tag u S₀ xs (by simpa [r, margin] using hcost)
    (by simpa [r, margin] using hlog) hgood

private theorem own_product_bound_of_dips {k : ℕ} (a L : ℝ) (q : Fin k → ℝ)
    (dips : Finset (Fin k))
    (ha : 0 < a) (haHalf : a ≤ 1 / 2) (hL : 0 < L)
    (hgood : ∀ j ∉ dips, 1 / 2 + 3 / 4 * a ≤ q j)
    (hbad : ∀ j ∈ dips, Real.exp (-L) ≤ q j)
    (hcount : (dips.card : ℝ) ≤ a * (k : ℝ) / (20 * L)) :
    Real.exp ((k : ℝ) * (-Real.log 2 + c1 * a)) ≤ ∏ j : Fin k, q j := by
  classical
  have ha0 : 0 ≤ a := ha.le
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (inv_pos.mpr (by norm_num))
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hqpos : ∀ j, 0 < q j := by
    intro j
    by_cases hj : j ∈ dips
    · exact lt_of_lt_of_le (Real.exp_pos _) (hbad j hj)
    · exact lt_of_lt_of_le (by positivity) (hgood j hj)
  have htpos : 0 < 1 + 3 / 2 * a := by positivity
  have hlogFactor : 7 / 10 * a ≤ Real.log (1 + 3 / 2 * a) := by
    have hinvpos : 0 < (1 + 3 / 2 * a)⁻¹ := inv_pos.mpr htpos
    have hlog := Real.log_le_sub_one_of_pos hinvpos
    rw [Real.log_inv] at hlog
    have hratio : 1 - (1 + 3 / 2 * a)⁻¹ = (3 / 2 * a) / (1 + 3 / 2 * a) := by
      field_simp [ne_of_gt htpos]
      ring
    have hratioLog : (3 / 2 * a) / (1 + 3 / 2 * a) ≤ Real.log (1 + 3 / 2 * a) := by
      rw [← hratio]
      linarith
    have haSq : a * a ≤ a / 2 := by
      have h := mul_le_mul_of_nonneg_left haHalf ha0
      nlinarith
    have hfrac : 7 / 10 * a ≤ (3 / 2 * a) / (1 + 3 / 2 * a) := by
      rw [le_div_iff₀ htpos]
      nlinarith [haSq]
    exact hfrac.trans hratioLog
  have hg : -Real.log 2 + 7 / 10 * a ≤ 0 := by nlinarith [hlog2, haHalf]
  have hlogGood : ∀ j ∉ dips, -Real.log 2 + 7 / 10 * a ≤ Real.log (q j) := by
    intro j hj
    have hlow : 0 < 1 / 2 * (1 + 3 / 2 * a) := by positivity
    have hle : 1 / 2 * (1 + 3 / 2 * a) ≤ q j := by
      have := hgood j hj
      nlinarith
    have hlog := Real.log_le_log hlow hle
    have hlogMul : Real.log (1 / 2 * (1 + 3 / 2 * a)) =
        -Real.log 2 + Real.log (1 + 3 / 2 * a) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt htpos)]
      have hinv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [hinv, Real.log_inv]
    rw [hlogMul] at hlog
    linarith [hlogFactor]
  have hlogBad : ∀ j ∈ dips, -L ≤ Real.log (q j) := by
    intro j hj
    have hlog := Real.log_le_log (Real.exp_pos _) (hbad j hj)
    rw [Real.log_exp] at hlog
    exact hlog
  have hpoint : ∀ j : Fin k,
      -Real.log 2 + 7 / 10 * a - L * (if j ∈ dips then (1 : ℝ) else 0) ≤
        Real.log (q j) := by
    intro j
    by_cases hj : j ∈ dips
    · simp [hj]
      linarith [hlogBad j hj, hg]
    · simp [hj]
      linarith [hlogGood j hj]
  have hIndicator : ∑ j : Fin k, (if j ∈ dips then (1 : ℝ) else 0) = (dips.card : ℝ) := by
    have hNat := Finset.card_filter (fun j : Fin k => j ∈ dips) Finset.univ
    have hReal : ((Finset.univ.filter fun j : Fin k => j ∈ dips).card : ℝ) =
        ∑ j : Fin k, (if j ∈ dips then (1 : ℝ) else 0) := by
      exact_mod_cast hNat
    simpa using hReal.symm
  have hsum : (k : ℝ) * (-Real.log 2 + 7 / 10 * a) -
      (dips.card : ℝ) * L ≤ ∑ j : Fin k, Real.log (q j) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hpoint j)
    have hsumEq : ∑ j : Fin k,
        (-Real.log 2 + 7 / 10 * a - L * (if j ∈ dips then (1 : ℝ) else 0)) =
        (k : ℝ) * (-Real.log 2 + 7 / 10 * a) - (dips.card : ℝ) * L := by
      rw [Finset.sum_sub_distrib]
      have hconst : ∑ j : Fin k, (-Real.log 2 + 7 / 10 * a) =
          (k : ℝ) * (-Real.log 2 + 7 / 10 * a) := by
        simp [Finset.sum_const, nsmul_eq_mul] <;> ring
      rw [hconst, ← Finset.mul_sum, hIndicator]
      ring
    rw [hsumEq] at h
    exact h
  have hcountLoss : (dips.card : ℝ) * L ≤ a * (k : ℝ) / 20 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 20) hL)).mp hcount
    nlinarith
  have htarget : (k : ℝ) * (-Real.log 2 + c1 * a) ≤
      (k : ℝ) * (-Real.log 2 + 7 / 10 * a) - (dips.card : ℝ) * L := by
    dsimp [c1]
    have hk : 0 ≤ (k : ℝ) := by positivity
    nlinarith [mul_nonneg hk ha0]
  have hlogProd : Real.log (∏ j : Fin k, q j) = ∑ j : Fin k, Real.log (q j) := by
    rw [Real.log_prod]
    intro j hj
    exact (hqpos j).ne'
  have hprodPos : 0 < ∏ j : Fin k, q j := Finset.prod_pos fun j hj => hqpos j
  calc
    Real.exp ((k : ℝ) * (-Real.log 2 + c1 * a)) ≤
        Real.exp (Real.log (∏ j : Fin k, q j)) :=
      Real.exp_le_exp.mpr (by rw [hlogProd]; exact htarget.trans hsum)
    _ = ∏ j : Fin k, q j := Real.exp_log hprodPos

private theorem stopped_own_azuma_bound {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)]
    (P : FinProb Ω) (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ ω ω', history ⟨m, Nat.lt_succ_of_le hm⟩ ω = history ⟨m, Nat.lt_succ_of_le hm⟩ ω' →
        Δ i ω = Δ i ω')
    (θ t : ℝ)
    (hbound : ∀ i ω, 0 ≤ Δ i ω ∧ Δ i ω ≤ 1)
    (hmean : ∀ i (h : H i.castSucc),
      P.pr (fun ω => history i.castSucc ω = h) = 0 ∨
        (1 - θ) * P.pr (fun ω => history i.castSucc ω = h) ≤
          (∑ ω, if history i.castSucc ω = h then P.w ω * Δ i ω else 0))
    (hk : 0 < k) (ht : 0 < t) :
    P.pr (fun ω => ∑ i, Δ i ω < (k : ℝ) * (1 - θ) - t) ≤
      Real.exp (-2 * t ^ 2 / (k : ℝ)) := by
  have hwidth : 0 < ∑ i : Fin k, ((1 : ℝ) - 0) ^ 2 := by
    simp
    exact_mod_cast hk
  have h := xAzuma H P history project hfiltration Δ hadapted (fun _ => 1 - θ)
    (fun _ => 0) (fun _ => 1) hbound hmean hwidth t ht
  rw [show (k : ℝ) * (1 - θ) = (k : ℝ) - (k : ℝ) * θ by ring]
  simpa [Finset.sum_const, nsmul_eq_mul] using h

private theorem eventual_exposure_factor (β γ : ℝ) (hβ : 0 < β)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      40 * (n : ℝ) ^ 5 *
          Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2)) / 4) ≤
        Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
  let ω := omega4 β γ
  let α := β - ω / 2
  let c := ω / 5
  let δ := α / 2
  have hω : 0 < ω := omega4_pos hβ hγ
  have hωβ : ω ≤ β / 1000 := by
    dsimp [ω, omega4]
    exact div_le_div_of_nonneg_right (min_le_left β (1 - γ)) (by norm_num)
  have hα : 0 < α := by dsimp [α]; nlinarith
  have hgap : 0 < α - c := by dsimp [α, c]; nlinarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ + δ = α := by dsimp [δ]; ring
  have hfactorPow : 0 < δ := hδ
  have hcoeff : 0 < Real.log 40 + 5 / δ := by
    have hlog : 0 < Real.log 40 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨nLog, hnLog⟩ := eventually_rpow_gt (a := δ)
    (c := 8 * (Real.log 40 + 5 / δ)) hδ
  obtain ⟨nGap, hnGap⟩ := eventually_rpow_gt (a := α - c) (c := 16) hgap
  refine ⟨max nLog (max nGap 1), ?_⟩
  intro n hn
  have hnLog' : nLog ≤ n := le_trans (le_max_left _ _) hn
  have hnGap' : nGap ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_left nGap 1) (Nat.le_max_right nLog (max nGap 1))
  have hnOne : 1 ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_right nGap 1) (Nat.le_max_right nLog (max nGap 1))
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hnr : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hnδpos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hnr _
  have hnδone : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR hδ.le
  have hlogPow := Real.log_le_self hnδpos.le
  rw [Real.log_rpow hnr δ] at hlogPow
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [hlogPow]
  have hpowC : 8 * (Real.log 40 + 5 / δ) < (n : ℝ) ^ δ := hnLog n hnLog'
  have hlogFactor : Real.log (40 * (n : ℝ) ^ 5) ≤ (n : ℝ) ^ α / 8 := by
    have hlogN : Real.log (40 * (n : ℝ) ^ 5) = Real.log 40 + 5 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    have hlog5 : 5 * Real.log (n : ℝ) ≤ (5 / δ) * (n : ℝ) ^ δ := by
      have h := mul_le_mul_of_nonneg_left hlogPow (by positivity : 0 ≤ 5 / δ)
      have hleft : (5 / δ) * (δ * Real.log (n : ℝ)) = 5 * Real.log (n : ℝ) := by
        field_simp [ne_of_gt hδ]
      rw [hleft] at h
      exact h
    have hcoeffBound : Real.log 40 + 5 * Real.log (n : ℝ) ≤
        (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := by
      have hlog40 : 0 < Real.log 40 := Real.log_pos (by norm_num)
      calc
        Real.log 40 + 5 * Real.log (n : ℝ) ≤
            Real.log 40 + (5 / δ) * (n : ℝ) ^ δ := by linarith [hlog5]
        _ ≤ Real.log 40 * (n : ℝ) ^ δ + (5 / δ) * (n : ℝ) ^ δ := by
            have h := mul_le_mul_of_nonneg_left hnδone hlog40.le
            nlinarith
        _ = (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := by ring
    have hpowHalf : 8 * (Real.log 40 + 5 / δ) ≤ (n : ℝ) ^ δ := le_of_lt hpowC
    have hpowAlpha : (n : ℝ) ^ α = (n : ℝ) ^ δ * (n : ℝ) ^ δ := by
      rw [← Real.rpow_add hnr δ δ, hδeq]
    rw [hlogN, hpowAlpha]
    calc
      Real.log 40 + 5 * Real.log (n : ℝ) ≤
          (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := hcoeffBound
      _ ≤ ((n : ℝ) ^ δ * (n : ℝ) ^ δ) / 8 := by nlinarith [hnδpos]
      _ = _ := by ring
  have hFactorPos : 0 < 40 * (n : ℝ) ^ 5 := by positivity
  have hFactorExp : 40 * (n : ℝ) ^ 5 ≤ Real.exp ((n : ℝ) ^ α / 8) := by
    have h := Real.exp_le_exp.mpr hlogFactor
    rw [Real.exp_log hFactorPos] at h
    exact h
  have hGapPow : 16 < (n : ℝ) ^ (α - c) := hnGap n hnGap'
  have hnCpos : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnr _
  have hpowSplit : (n : ℝ) ^ α = (n : ℝ) ^ c * (n : ℝ) ^ (α - c) := by
    rw [← Real.rpow_add hnr c (α - c)]
    congr 1
    ring
  have hexpCompare : -((n : ℝ) ^ α) / 8 ≤ -2 * (n : ℝ) ^ c := by
    rw [hpowSplit]
    nlinarith [mul_lt_mul_of_pos_left hGapPow hnCpos]
  calc
    40 * (n : ℝ) ^ 5 * Real.exp (-((n : ℝ) ^ α) / 4) ≤
        Real.exp ((n : ℝ) ^ α / 8) * Real.exp (-((n : ℝ) ^ α) / 4) :=
      mul_le_mul_of_nonneg_right hFactorExp (Real.exp_nonneg _)
    _ = Real.exp (-((n : ℝ) ^ α) / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2 * (n : ℝ) ^ c) := Real.exp_le_exp.mpr hexpCompare

private theorem eventual_exposure_factor_four (β γ : ℝ) (hβ : 0 < β)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      40 * (n : ℝ) ^ 5 *
          Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2)) / 4) ≤
        Real.exp (-4 * (n : ℝ) ^ (omega4 β γ / 5)) := by
  let ω := omega4 β γ
  let α := β - ω / 2
  let c := ω / 5
  let δ := α / 2
  have hω : 0 < ω := omega4_pos hβ hγ
  have hωβ : ω ≤ β / 1000 := by
    dsimp [ω, omega4]
    exact div_le_div_of_nonneg_right (min_le_left β (1 - γ)) (by norm_num)
  have hα : 0 < α := by dsimp [α]; nlinarith
  have hgap : 0 < α - c := by dsimp [α, c]; nlinarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ + δ = α := by dsimp [δ]; ring
  obtain ⟨nLog, hnLog⟩ := eventually_rpow_gt (a := δ)
    (c := 8 * (Real.log 40 + 5 / δ)) hδ
  obtain ⟨nGap, hnGap⟩ := eventually_rpow_gt (a := α - c) (c := 32) hgap
  refine ⟨max nLog (max nGap 1), ?_⟩
  intro n hn
  have hnLog' : nLog ≤ n := le_trans (le_max_left _ _) hn
  have hnGap' : nGap ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_left nGap 1) (Nat.le_max_right nLog (max nGap 1))
  have hnOne : 1 ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_right nGap 1) (Nat.le_max_right nLog (max nGap 1))
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hnr : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hnδpos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hnr _
  have hnδone : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR hδ.le
  have hlogPow := Real.log_le_self hnδpos.le
  rw [Real.log_rpow hnr δ] at hlogPow
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith [hlogPow]
  have hpowC : 8 * (Real.log 40 + 5 / δ) < (n : ℝ) ^ δ := hnLog n hnLog'
  have hlogFactor : Real.log (40 * (n : ℝ) ^ 5) ≤ (n : ℝ) ^ α / 8 := by
    have hlogN : Real.log (40 * (n : ℝ) ^ 5) = Real.log 40 + 5 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    have hlog5 : 5 * Real.log (n : ℝ) ≤ (5 / δ) * (n : ℝ) ^ δ := by
      have h := mul_le_mul_of_nonneg_left hlogPow (by positivity : 0 ≤ 5 / δ)
      have hleft : (5 / δ) * (δ * Real.log (n : ℝ)) = 5 * Real.log (n : ℝ) := by
        field_simp [ne_of_gt hδ]
      rw [hleft] at h
      exact h
    have hcoeffBound : Real.log 40 + 5 * Real.log (n : ℝ) ≤
        (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := by
      have hlog40 : 0 < Real.log 40 := Real.log_pos (by norm_num)
      calc
        Real.log 40 + 5 * Real.log (n : ℝ) ≤
            Real.log 40 + (5 / δ) * (n : ℝ) ^ δ := by linarith [hlog5]
        _ ≤ Real.log 40 * (n : ℝ) ^ δ + (5 / δ) * (n : ℝ) ^ δ := by
            have h := mul_le_mul_of_nonneg_left hnδone hlog40.le
            nlinarith
        _ = (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := by ring
    have hpowHalf : 8 * (Real.log 40 + 5 / δ) ≤ (n : ℝ) ^ δ := le_of_lt hpowC
    have hpowAlpha : (n : ℝ) ^ α = (n : ℝ) ^ δ * (n : ℝ) ^ δ := by
      rw [← Real.rpow_add hnr δ δ, hδeq]
    rw [hlogN, hpowAlpha]
    calc
      Real.log 40 + 5 * Real.log (n : ℝ) ≤
          (Real.log 40 + 5 / δ) * (n : ℝ) ^ δ := hcoeffBound
      _ ≤ ((n : ℝ) ^ δ * (n : ℝ) ^ δ) / 8 := by nlinarith [hnδpos]
      _ = _ := by ring
  have hFactorPos : 0 < 40 * (n : ℝ) ^ 5 := by positivity
  have hFactorExp : 40 * (n : ℝ) ^ 5 ≤ Real.exp ((n : ℝ) ^ α / 8) := by
    have h := Real.exp_le_exp.mpr hlogFactor
    rw [Real.exp_log hFactorPos] at h
    exact h
  have hGapPow : 32 < (n : ℝ) ^ (α - c) := hnGap n hnGap'
  have hnCpos : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnr _
  have hpowSplit : (n : ℝ) ^ α = (n : ℝ) ^ c * (n : ℝ) ^ (α - c) := by
    rw [← Real.rpow_add hnr c (α - c)]
    congr 1
    ring
  have hexpCompare : -((n : ℝ) ^ α) / 8 ≤ -4 * (n : ℝ) ^ c := by
    rw [hpowSplit]
    nlinarith [mul_lt_mul_of_pos_left hGapPow hnCpos]
  calc
    40 * (n : ℝ) ^ 5 * Real.exp (-((n : ℝ) ^ α) / 4) ≤
        Real.exp ((n : ℝ) ^ α / 8) * Real.exp (-((n : ℝ) ^ α) / 4) :=
      mul_le_mul_of_nonneg_right hFactorExp (Real.exp_nonneg _)
    _ = Real.exp (-((n : ℝ) ^ α) / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-4 * (n : ℝ) ^ c) := Real.exp_le_exp.mpr hexpCompare

set_option maxHeartbeats 1000000 in
theorem exposure_low_core (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y)
      (tag : Key β γ n → M.ι),
      KeyNbrCard β γ n → EntryLow M → ExposureLow M tag := by
  obtain ⟨nWidth, hWidthAll⟩ :=
    eventual_residual_width_budget β γ hβ hβγ hγ
  obtain ⟨nFactors, hFactors⟩ :=
    eventual_width_budget_factors β γ hβ hβγ hγ
  obtain ⟨nAbsorb, hAbsorb⟩ := eventual_exposure_factor β γ hβ hγ
  refine ⟨max 1 (max nWidth (max nFactors nAbsorb)), ?_⟩
  intro n hn N E G X Y M tag hKey hEntry
  have hnWidth : nWidth ≤ n := by
    apply le_trans _ hn
    exact le_trans (Nat.le_max_left nWidth (max nFactors nAbsorb))
      (Nat.le_max_right 1 (max nWidth (max nFactors nAbsorb)))
  have hnFactors : nFactors ≤ n := by
    apply le_trans _ hn
    exact le_trans
      (le_trans (Nat.le_max_left nFactors nAbsorb)
        (Nat.le_max_right nWidth (max nFactors nAbsorb)))
      (Nat.le_max_right 1 (max nWidth (max nFactors nAbsorb)))
  have hnAbsorb : nAbsorb ≤ n := by
    apply le_trans _ hn
    exact le_trans
      (le_trans (Nat.le_max_right nFactors nAbsorb)
        (Nat.le_max_right nWidth (max nFactors nAbsorb)))
      (Nat.le_max_right 1 (max nWidth (max nFactors nAbsorb)))
  have hωpos : 0 < omega4 β γ := omega4_pos hβ hγ
  have hωlt : omega4 β γ < 1 := by
    dsimp [omega4]
    have hmin : min β (1 - γ) ≤ 1 - γ := min_le_right β (1 - γ)
    nlinarith
  have hnOne : 1 ≤ n := le_trans (Nat.le_max_left 1 _) hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hnWidth' : nWidth ≤ n := hnWidth
  have hnFactors' : nFactors ≤ n := hnFactors
  have hnAbsorb' : nAbsorb ≤ n := hnAbsorb
  intro xm ym u D hDpos hDcard
  classical
  let Z : Finset (Key β γ n) := Zset β γ u
  let s : Finset (Loc β γ n × Key β γ n) := D ×ˢ Z
  let A := {ck : Loc β γ n × Key β γ n // ck ∈ s}
  let m : ℕ := Fintype.card A
  let e : Fin m ≃ A := (Fintype.equivFin A).symm
  have hcount : m = D.card * Z.card := by
    dsimp [m, A, s]
    rw [Fintype.card_coe, Finset.card_product]
  have hcountReal : (m : ℝ) = (D.card : ℝ) * (Z.card : ℝ) := by exact_mod_cast hcount
  have hWidth : ∀ (i : Fin m)
      (q : Fin i.val → Fin (tupLen β γ n) → Fin N) (xs : List (Fin N)),
      xs.length ≤ tupLen β γ n →
      GoodPath E G (capL β γ n) (maskLaw (ym u)) (tupleLabels q ++ xs) →
      Law.WidthLE (residualAfter E G (maskLaw (ym u)) (tupleLabels q ++ xs))
        (2 * (n : ℝ) ^ γ) := by
    intro i q xs hxs hgood
    have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
    have hlen : (tupleLabels q ++ xs).length ≤ (tupLen β γ n) * m := by
      rw [List.length_append, tupleLabels_length]
      calc
        i.val * tupLen β γ n + xs.length ≤ i.val * tupLen β γ n + tupLen β γ n :=
          Nat.add_le_add_left hxs _
        _ = (i.val + 1) * tupLen β γ n := by rw [Nat.add_mul, one_mul]
        _ ≤ m * tupLen β γ n := Nat.mul_le_mul_right _ hi
        _ = tupLen β γ n * m := Nat.mul_comm _ _
    have hlen' : (tupleLabels q ++ xs).length ≤
        tupLen β γ n * D.card * Z.card := by
      simpa [hcount, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlen
    exact hWidthAll n hnWidth M u tag D (ym u) hDcard hKey
      (tupleLabels q ++ xs) hlen' hgood
  let P := tupleLaw M tag xm
  let ε : ℝ := Real.exp (-(((n : ℝ) ^ (β - omega4 β γ / 2)) / 4))
  let b : ℝ := (m : ℝ) * (tupLen β γ n : ℝ) * ε
  let mass : Tuples β γ n N → Prop := fun W =>
    (maskLaw (ym u)).pr (HitsAll E G W D Z) <
      Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) * (Z.card : ℝ)))
  let pairFail (c : Loc β γ n) (κ : Key β γ n) (W : Tuples β γ n N) : Prop :=
    (maskLaw (ym u)).pr (HitsAll E G W D Z) <
      ratioThr β γ u κ * (maskLaw (ym u)).pr (HitsBut E G W D Z c κ)
  let crossAny : Tuples β γ n N → Prop := fun W =>
    ∃ c ∈ D, ∃ κ ∈ Z, κ ≠ key β γ n u.1 ∧ pairFail c κ W
  have hbound (e' : Fin m ≃ A) :
      (P.pr (fun W => OuterFirstBad E G (capL β γ n) (maskLaw (ym u))
        (fun i => W (e' i).1))) ≤ b := by
    have h := tupleLaw_firstBad_bound M tag xm ym u m s e' hEntry hWidth
    simpa [P, b, ε] using h
  have hMassBound : P.pr mass ≤ b := by
    apply le_trans (pr_mono P mass
      (fun W => OuterFirstBad E G (capL β γ n) (maskLaw (ym u))
        (fun i => W (e i).1)) ?_)
    · exact hbound e
    · intro W hMass
      exact mass_fail_implies_outerFirstBad M tag ym u D m hcount e W hMass
  have hPairBound : ∀ c ∈ D, ∀ κ ∈ Z, κ ≠ key β γ n u.1 →
      P.pr (pairFail c κ) ≤ b := by
    intro c hc κ hκ hne
    let target : A := ⟨(c, κ), Finset.mem_product.mpr ⟨hc, hκ⟩⟩
    obtain ⟨e', last, hlast, he'⟩ := exists_fin_equiv_last target
    apply le_trans (pr_mono P (pairFail c κ)
      (fun W => OuterFirstBad E G (capL β γ n) (maskLaw (ym u))
        (fun i => W (e' i).1)) ?_)
    · exact hbound e'
    · intro W hFail
      exact cross_fail_implies_outerFirstBad M tag ym u D m e' last hlast
        target he' W hne hFail
  have hCrossBound : P.pr crossAny ≤ (m : ℝ) * b := by
    have houter := pr_exists_finset_le_sum P D
      (fun c W => ∃ κ ∈ Z, κ ≠ key β γ n u.1 ∧ pairFail c κ W)
    calc
      P.pr crossAny ≤
          ∑ c ∈ D, P.pr (fun W => ∃ κ ∈ Z,
            κ ≠ key β γ n u.1 ∧ pairFail c κ W) := houter
      _ ≤ ∑ c ∈ D, ∑ κ ∈ Z, b := by
        apply Finset.sum_le_sum
        intro c hc
        calc
          P.pr (fun W => ∃ κ ∈ Z, κ ≠ key β γ n u.1 ∧ pairFail c κ W) ≤
              ∑ κ ∈ Z, P.pr (fun W => κ ≠ key β γ n u.1 ∧ pairFail c κ W) :=
            pr_exists_finset_le_sum P Z (fun κ W => κ ≠ key β γ n u.1 ∧ pairFail c κ W)
          _ ≤ ∑ κ ∈ Z, b := by
            apply Finset.sum_le_sum
            intro κ hκ
            by_cases hne : κ ≠ key β γ n u.1
            · simpa [hne] using hPairBound c hc κ hκ hne
            · have hzero : P.pr (fun W => κ ≠ key β γ n u.1 ∧ pairFail c κ W) = 0 := by
                have hpred : (fun W => κ ≠ key β γ n u.1 ∧ pairFail c κ W) =
                    (fun _ : Tuples β γ n N => False) := by
                  funext W
                  simp [hne]
                rw [hpred, pr_const]
                simp
              rw [hzero]
              positivity
      _ = (D.card : ℝ) * (Z.card : ℝ) * b := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = (m : ℝ) * b := by rw [← hcountReal]
  have hcover : ∀ W, LowFail M tag ym u D W → mass W ∨ crossAny W := by
    intro W h
    change mass W ∨ crossAny W at h
    exact h
  have hUnion : P.pr (LowFail M tag ym u D) ≤ P.pr mass + P.pr crossAny := by
    calc
      P.pr (LowFail M tag ym u D) ≤ P.pr (fun W => mass W ∨ crossAny W) :=
        pr_mono P _ _ hcover
      _ ≤ P.pr mass + P.pr crossAny := FinProb.pr_union P mass crossAny
  have hUnionBound : P.pr (LowFail M tag ym u D) ≤
      (1 + (m : ℝ)) * (m : ℝ) * (tupLen β γ n : ℝ) * ε := by
    calc
      P.pr (LowFail M tag ym u D) ≤ b + (m : ℝ) * b := le_trans hUnion
        (add_le_add hMassBound hCrossBound)
      _ = (1 + (m : ℝ)) * (m : ℝ) * (tupLen β γ n : ℝ) * ε := by
        simp [b]
        ring
  have hDreal : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by exact_mod_cast hDcard
  have hDlinear : (D.card : ℝ) ≤ 4 * (n : ℝ) := by
    have hDb := le_trans hDreal (hFactors n hnFactors).1
    have hpow : (n : ℝ) ^ (omega4 β γ / 30) ≤ (n : ℝ) := by
      have hpow' : (n : ℝ) ^ (omega4 β γ / 30) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hωlt])
      simpa using hpow'
    exact le_trans hDb (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hZlinear : (Z.card : ℝ) ≤ (n : ℝ) := by
    have hz := hKey u
    have hpow : (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ) ≤ (n : ℝ) := by
      have hpow' : (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hγ])
      simpa using hpow'
    exact le_trans hz hpow
  have hKlinear : (tupLen β γ n : ℝ) ≤ 2 * (n : ℝ) := by
    have hk := (hFactors n hnFactors).2.1
    have hpow : (n : ℝ) ^ (omega4 β γ / 3) ≤ (n : ℝ) := by
      have hpow' : (n : ℝ) ^ (omega4 β γ / 3) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hωlt])
      simpa using hpow'
    exact le_trans hk (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hmBound : (m : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    rw [hcountReal]
    calc
      (D.card : ℝ) * (Z.card : ℝ) ≤ (4 * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul hDlinear hZlinear (by positivity) (by positivity)
      _ = 4 * (n : ℝ) ^ 2 := by ring
  have honeM : 1 + (m : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by nlinarith [hmBound, hnR]
  have hfactorBound : (1 + (m : ℝ)) * (m : ℝ) * (tupLen β γ n : ℝ) ≤
      40 * (n : ℝ) ^ 5 := by
    have hmNonneg : 0 ≤ (m : ℝ) := by positivity
    have hprod := mul_le_mul honeM hmBound (by positivity) (by positivity)
    have hprod' := mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ (tupLen β γ n : ℝ))
    calc
      (1 + (m : ℝ)) * (m : ℝ) * (tupLen β γ n : ℝ) ≤
          (5 * (n : ℝ) ^ 2) * (4 * (n : ℝ) ^ 2) * (tupLen β γ n : ℝ) := hprod'
      _ ≤ (5 * (n : ℝ) ^ 2) * (4 * (n : ℝ) ^ 2) * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hKlinear (by positivity)
      _ = 40 * (n : ℝ) ^ 5 := by ring
  have hExpFactor := hAbsorb n hnAbsorb
  have hExpEq : Real.exp (-((n : ℝ) ^ (β - omega4 β γ / 2)) / 4) = ε := by
    unfold ε
    congr 1
    ring
  rw [hExpEq] at hExpFactor
  calc
    P.pr (LowFail M tag ym u D) ≤
        (1 + (m : ℝ)) * (m : ℝ) * (tupLen β γ n : ℝ) * ε := hUnionBound
    _ ≤ 40 * (n : ℝ) ^ 5 * ε :=
      mul_le_mul_of_nonneg_right hfactorBound (Real.exp_nonneg _)
    _ ≤ Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5)) := by
      exact hExpFactor

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
