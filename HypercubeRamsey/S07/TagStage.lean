import HypercubeRamsey.S07.Profiles
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S07.TagStage_q_s07_tag

/-!
# L7.1, Step 2: filter tails, tag avoidance and typical tags

Source: `sections/07-…tex`, lines 136–194.  `cond_product_bound` is the local-lemma tool used by all three
conditioning steps (tags here, anchors in Step 4, targets in Step 6).
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- Lemma 3.4 on a product law with free coordinates (TeX 03, Lemma 3.4 and the independent-variables paragraph
after it; `S03/ConditionalAvoidance.lean`): with events joined when their scopes meet, the avoidance event has
positive mass; removing the events whose scopes meet `U` costs `∏ (1 - x)^{-1}` (third assertion), and the
remaining events are independent of the coordinates in `U`. -/
theorem cond_product_bound : CondProductBound := by
  exact TagStageQ.cond_product_bound_impl

/-- L7.1d(i) (07:136–154): the raw mean cross-failure probability at a key is at most `4s²K n^{-D₀}`.  In a step
of a cross order the current filtered law `τ` has width `≤ n^{d/2} + 2cs log n < n^{1/4}`, and the next anchor
has raw marginal `α` with `N α ≤ K`, independent of the history; if `α(H_τ) ≥ K n^{-D₀}`,
`H_τ = {x : d_G(x, τ) < n^{-c}}`, the restriction of `α` to `H_τ` violates (7.1).  There are at most `(2s)²`
order–step pairs. -/
theorem cross_fail_mean (D₀ d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι) (K : ℝ),
      0 < N → GeomLocal Γ → (∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K) →
      Eq71At D₀ d n N E X Y →
      ∀ g, (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) ≤
        4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀) := by
  classical
  have hbudgetE := TagStageQ.eventually_cross_width_budget d hd hd'
  have hnlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hbudgetE.and hnlarge)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y p κ Γ M Q K hN hloc hmean hEq
  rcases hn₀ n hn with ⟨hbudget, hn2⟩
  intro g
  let P := FinProb.pi (TagStageQ.tagAnchorLaw Γ M Q)
  let I : Type := {h₀ : Γ.Key // h₀ ∈ Γ.keyNbrs g} × Fin (Γ.crossKeys g).length
  let Step : I → (Γ.Key → M.ι × Fin N) → Prop :=
    fun i z => TagStageQ.crossStepBad Γ M z g i.1.1 i.2.val
  let q : ℝ := K * (n : ℝ) ^ (-D₀)
  have hα : (Law.mix (Q g) M.μ).CapLE K := by
    intro x
    simpa [Law.mix] using hmean g x
  have hKone : 1 ≤ K := by
    have hsum : (N : ℝ) ≤ (N : ℝ) * K := by
      calc
        (N : ℝ) = ∑ x, (N : ℝ) * (Law.mix (Q g) M.μ).w x := by
          calc
            (N : ℝ) = (N : ℝ) * 1 := by ring
            _ = (N : ℝ) * ∑ x, (Law.mix (Q g) M.μ).w x := by
              rw [(Law.mix (Q g) M.μ).sum_eq_one]
            _ = ∑ x, (N : ℝ) * (Law.mix (Q g) M.μ).w x := by rw [Finset.mul_sum]
        _ ≤ ∑ x, K := Finset.sum_le_sum fun x hx => hα x
        _ = (N : ℝ) * K := by simp
    nlinarith [show 0 < (N : ℝ) by exact_mod_cast hN]
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hstep (i : I) : P.pr (Step i) ≤ q := by
    let h₀ : Γ.Key := i.1.1
    let k : Fin (Γ.crossKeys g).length := i.2
    have hh₀ : h₀ ∈ Γ.crossKeys g := by
      simpa [h₀, GridGeom.crossKeys] using i.1.2
    have hmain := TagStageQ.crossStepBad_pr_le Γ M Q D₀ K g h₀ hh₀ k hN hn2
      (le_of_lt hd) hloc hmean hEq hbudget
    simpa [P, Step, q, h₀, k] using hmain
  have hcrossSub : ∀ z : Γ.Key → M.ι × Fin N,
      (¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) →
        ∃ i ∈ (Finset.univ : Finset I), Step i z := by
    intro z hbad
    obtain ⟨h₀, hh₀, k, hk, hstep⟩ :=
      TagStageQ.crossFail_imp_exists_step Γ M z g hbad
    have hNbr : h₀ ∈ Γ.keyNbrs g := by simpa [GridGeom.crossKeys] using hh₀
    refine ⟨(⟨h₀, hNbr⟩, ⟨k, hk⟩), Finset.mem_univ _, ?_⟩
    exact hstep
  have hunion := TagStageQ.pr_exists_le_sum P Finset.univ Step
  have hbadMean :
      P.pr (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) ≤
        (Fintype.card I : ℝ) * q := by
    calc
      P.pr (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) ≤
          P.pr (fun z => ∃ i ∈ (Finset.univ : Finset I), Step i z) :=
        TagStageQ.pr_mono P (fun z hz => hcrossSub z hz)
      _ ≤ ∑ i ∈ (Finset.univ : Finset I), P.pr (Step i) := hunion
      _ ≤ ∑ i ∈ (Finset.univ : Finset I), q :=
        Finset.sum_le_sum fun i hi => hstep i
      _ = (Fintype.card I : ℝ) * q := by simp
  have hkeysBound : (Γ.crossKeys g).length ≤ 2 * gS d n := by
    have hlen : (Γ.crossKeys g).length = (Γ.keyNbrs g).card := by
      simp [GridGeom.crossKeys]
    rw [hlen]
    exact hloc.keyNbrs_card g
  have hcardI : Fintype.card I ≤ 4 * (gS d n) ^ 2 := by
    have hcard : Fintype.card I = (Γ.keyNbrs g).card * (Γ.crossKeys g).length := by
      simp [I]
    rw [hcard]
    calc
      (Γ.keyNbrs g).card * (Γ.crossKeys g).length ≤
          (2 * gS d n) * (2 * gS d n) := Nat.mul_le_mul (hloc.keyNbrs_card g) hkeysBound
      _ = 4 * (gS d n) ^ 2 := by ring
  have hcountReal : (Fintype.card I : ℝ) ≤ 4 * (gS d n : ℝ) ^ 2 := by
    exact_mod_cast hcardI
  calc
    (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) =
        P.pr (fun z => ¬ CrossValidRow Γ M (z g).1 (fun h => (z h).2) g) :=
      TagStageQ.tagAnchor_pi_crossFail Γ M Q g
    _ ≤ (Fintype.card I : ℝ) * q := hbadMean
    _ ≤ 4 * (gS d n : ℝ) ^ 2 * q :=
      mul_le_mul_of_nonneg_right hcountReal hqnonneg
    _ = 4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀) := by
      dsimp [q]
      ring

set_option maxHeartbeats 100000000
/-- L7.1e(i)–(ii) (07:163–175): the tag events satisfy the local-lemma input with charge `n^{-D₀/4}`: `B_g`
reads the tags on `{g} ∪ E(g)`, two events meet only within grid distance two, and Markov's inequality gives
`Pr(B_g) ≤ 4s²K n^{-D₀/2} ≤ n^{-D₀/4} (1 - n^{-D₀/4})^{(2s+1)²}` for large `n`. -/
theorem tag_lll (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      GeomLocal Γ → GeomBalls Γ →
      (∀ g, (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) ≤
        4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀)) →
      TagLLL Γ M Q D₀ := by
  classical
  have hgapProbExp : 2 * d - D₀ / 2 < -D₀ / 4 := by linarith
  have hgapDeltaExp : 2 * d - D₀ / 4 < 0 := by linarith
  have hgapProb := TagStageQ.eventually_power_gap (2 * d - D₀ / 2) (-D₀ / 4)
    (32 * (|K| + 1)) hgapProbExp (by positivity)
  have hgapDelta := TagStageQ.eventually_power_gap (2 * d - D₀ / 4) 0 50
    hgapDeltaExp (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hgapProb.and hgapDelta |>.and hlarge)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y p κ Γ M Q hloc hballs hmean
  rcases hn₀ n hn with ⟨⟨hgapP, hgapD⟩, hn2⟩
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnRgt : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  let g₀ : Γ.Key := (Γ.key (fun _ : Fin n => false)).1
  let i : M.ι := Classical.choice (TagStageQ.pi_nonempty (Q g₀))
  let y : Fin N := Classical.choice (TagStageQ.pi_nonempty (M.μ i))
  have hSlo : (n : ℝ) ^ d ≤ (gS d n : ℝ) := by
    dsimp [gS]
    exact Nat.le_ceil _
  have hpowge : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnRone (le_of_lt hd)
  have hSupper : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by
    dsimp [gS]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ d by positivity)
    linarith
  have hDistSymm (a b : Γ.Key) : Γ.keyDist a b = Γ.keyDist b a := by
    unfold GridGeom.keyDist
    apply Finset.sum_congr rfl
    intro r hr
    exact Nat.dist_comm _ _
  have hDistTriangle (a b c : Γ.Key) :
      Γ.keyDist a c ≤ Γ.keyDist a b + Γ.keyDist b c := by
    unfold GridGeom.keyDist
    calc
      (∑ r, Nat.dist (a r : ℕ) (c r : ℕ)) ≤
          ∑ r, (Nat.dist (a r : ℕ) (b r : ℕ) + Nat.dist (b r : ℕ) (c r : ℕ)) := by
        apply Finset.sum_le_sum
        intro r hr
        unfold Nat.dist
        omega
      _ = (∑ r, Nat.dist (a r : ℕ) (b r : ℕ)) +
            ∑ r, Nat.dist (b r : ℕ) (c r : ℕ) := by rw [Finset.sum_add_distrib]
  have hdegree (g : Γ.Key) :
      (Finset.univ.filter fun j => j ≠ g ∧
        ¬ Disjoint (Γ.keyBall g 1) (Γ.keyBall j 1)).card ≤ (2 * gS d n + 1) ^ 2 := by
    let A : Finset Γ.Key := Finset.univ.filter fun j =>
      j ≠ g ∧ ¬ Disjoint (Γ.keyBall g 1) (Γ.keyBall j 1)
    have hAsub : A ⊆ Γ.keyBall g 2 := by
      intro j hj
      have hmem := (Finset.mem_filter.mp hj).2
      obtain ⟨k, hkg, hkj⟩ := Finset.not_disjoint_iff.mp hmem.2
      have hkg' : Γ.keyDist g k ≤ 1 := by
        simpa [GridGeom.keyBall] using (Finset.mem_filter.mp hkg).2
      have hjk' : Γ.keyDist j k ≤ 1 := by
        simpa [GridGeom.keyBall] using (Finset.mem_filter.mp hkj).2
      have hkj' : Γ.keyDist k j ≤ 1 := by
        rw [hDistSymm]
        exact hjk'
      have hgj : Γ.keyDist g j ≤ 2 := by
        exact (hDistTriangle g k j).trans (by omega)
      simpa [GridGeom.keyBall] using hgj
    have hAcardReal : (A.card : ℝ) ≤ (2 * gS d n + 1 : ℝ) ^ 2 := by
      calc
        (A.card : ℝ) ≤ (Γ.keyBall g 2).card := by
          exact_mod_cast (Finset.card_le_card hAsub)
        _ ≤ (2 * (gS d n) + 1 : ℝ) ^ 2 := hballs.keyBall_card g 2
    have hAcard : A.card ≤ (2 * gS d n + 1) ^ 2 := by exact_mod_cast hAcardReal
    simpa [A] using hAcard
  have hmeanNonneg : 0 ≤ (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g₀) := by
    calc
      0 = (FinProb.pi Q).expect (fun _ => 0) := (FinProb.expect_const _ 0).symm
      _ ≤ (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g₀) :=
        FinProb.expect_mono _ (fun σ => TagStageQ.pr_nonneg _ _)
  have hgSlow : 1 ≤ (gS d n : ℝ) := hpowge.trans hSlo
  have hfactorPos : 0 < 4 * (gS d n : ℝ) ^ 2 * (n : ℝ) ^ (-D₀) := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hgSlow)))
      (Real.rpow_pos_of_pos hnRpos _)
  have hKnonneg : 0 ≤ K := by
    by_contra hK
    have hKneg : K < 0 := lt_of_not_ge hK
    have hright : 4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀) < 0 := by
      have hmul := mul_neg_of_pos_of_neg hfactorPos hKneg
      calc
        4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀) =
            (4 * (gS d n : ℝ) ^ 2 * (n : ℝ) ^ (-D₀)) * K := by ring
        _ < 0 := hmul
    linarith [hmean g₀]
  let t : ℝ := (n : ℝ) ^ (-D₀ / 2)
  let x : ℝ := (n : ℝ) ^ (-D₀ / 4)
  have htpos : 0 < t := by positivity
  have hxpos : 0 < x := by positivity
  have hxlt : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg hnRgt (by linarith)
  have hxnonneg : 0 ≤ x := hxpos.le
  have hpowQuot : (n : ℝ) ^ (-D₀) / t = (n : ℝ) ^ (-D₀ / 2) := by
    have h := Real.rpow_sub hnRpos (-D₀) (-D₀ / 2)
    have hexp : -D₀ - (-D₀ / 2) = -D₀ / 2 := by ring
    rw [hexp] at h
    exact h.symm
  have hsquare : (gS d n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (2 * d) := by
    have hsum : 0 ≤ 2 * (n : ℝ) ^ d + (gS d n : ℝ) := by positivity
    have hprod : 0 ≤ (2 * (n : ℝ) ^ d - (gS d n : ℝ)) *
        (2 * (n : ℝ) ^ d + (gS d n : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hSupper) hsum
    have hu2 : ((n : ℝ) ^ d) ^ 2 = (n : ℝ) ^ (2 * d) := by
      calc
        ((n : ℝ) ^ d) ^ 2 = (n : ℝ) ^ (d * 2) :=
          (Real.rpow_mul_natCast hnRpos.le d 2).symm
        _ = (n : ℝ) ^ (2 * d) := by congr 1 <;> ring
    nlinarith [hprod, hu2]
  have hmeanQuot :
      (4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀)) / t ≤
        16 * K * (n : ℝ) ^ (2 * d - D₀ / 2) := by
    have hfactor : 4 * (gS d n : ℝ) ^ 2 * K ≤
        16 * K * (n : ℝ) ^ (2 * d) := by
      calc
        4 * (gS d n : ℝ) ^ 2 * K =
            4 * ((gS d n : ℝ) ^ 2 * K) := by ring
        _ ≤ 4 * (4 * (n : ℝ) ^ (2 * d) * K) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsquare hKnonneg) (by norm_num)
        _ = 16 * K * (n : ℝ) ^ (2 * d) := by ring
    have hpowMul : (n : ℝ) ^ (2 * d) * (n : ℝ) ^ (-D₀ / 2) =
        (n : ℝ) ^ (2 * d - D₀ / 2) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> ring
    calc
      (4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀)) / t =
          (4 * (gS d n : ℝ) ^ 2 * K) * ((n : ℝ) ^ (-D₀) / t) := by ring
      _ = (4 * (gS d n : ℝ) ^ 2 * K) * (n : ℝ) ^ (-D₀ / 2) := by rw [hpowQuot]
      _ ≤ (16 * K * (n : ℝ) ^ (2 * d)) * (n : ℝ) ^ (-D₀ / 2) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnRpos.le _)
      _ = 16 * K * (n : ℝ) ^ (2 * d - D₀ / 2) := by
        calc
          _ = 16 * K * ((n : ℝ) ^ (2 * d) * (n : ℝ) ^ (-D₀ / 2)) := by ring
          _ = _ := by rw [hpowMul]
  have hmarkovBound (g : Γ.Key) :
      (FinProb.pi Q).pr (fun σ => TagBad Γ M D₀ σ g) ≤ x / 2 := by
    have hmarkov := FinProb.markov (FinProb.pi Q)
      (fun σ => crossFailKey Γ M σ g) t
      (fun σ => TagStageQ.pr_nonneg _ _) htpos
    have hbadle :
        (FinProb.pi Q).pr (fun σ => TagBad Γ M D₀ σ g) ≤
          (FinProb.pi Q).pr (fun σ => t ≤ crossFailKey Γ M σ g) := by
      apply TagStageQ.pr_mono
      intro σ hσ
      change (n : ℝ) ^ (-(D₀ / 2)) < crossFailKey Γ M σ g at hσ
      have hpow : (n : ℝ) ^ (-(D₀ / 2)) = (n : ℝ) ^ (-D₀ / 2) := by
        congr 1 <;> ring
      rw [hpow] at hσ
      exact le_of_lt hσ
    calc
      (FinProb.pi Q).pr (fun σ => TagBad Γ M D₀ σ g) ≤
          (FinProb.pi Q).expect (fun σ => crossFailKey Γ M σ g) / t :=
        hbadle.trans hmarkov
      _ ≤ (4 * (gS d n : ℝ) ^ 2 * K * (n : ℝ) ^ (-D₀)) / t :=
        div_le_div_of_nonneg_right (hmean g) htpos.le
      _ ≤ 16 * K * (n : ℝ) ^ (2 * d - D₀ / 2) := hmeanQuot
      _ ≤ x / 2 := by
        have hgap := hn₀ n hn
        rcases hgap with ⟨⟨hprobGap, hdeltaGap⟩, hnlarge⟩
        have hKabs : |K| = K := abs_of_nonneg hKnonneg
        have hhalf := mul_lt_mul_of_pos_left hprobGap (by norm_num : (0 : ℝ) < 1 / 2)
        dsimp [x]
        nlinarith [hhalf, Real.rpow_nonneg hnRpos.le (-D₀ / 4)]
  have hDeltaCast : (((2 * gS d n + 1) ^ 2 : ℕ) : ℝ) ≤
      25 * (n : ℝ) ^ (2 * d) := by
    have hbase : 2 * (gS d n : ℝ) + 1 ≤ 5 * (n : ℝ) ^ d := by
      nlinarith [hSupper, hpowge]
    have hbaseNonneg : 0 ≤ 2 * (gS d n : ℝ) + 1 := by positivity
    have hsum : 0 ≤ 5 * (n : ℝ) ^ d + (2 * (gS d n : ℝ) + 1) := by positivity
    have hprod : 0 ≤ (5 * (n : ℝ) ^ d - (2 * (gS d n : ℝ) + 1)) *
        (5 * (n : ℝ) ^ d + (2 * (gS d n : ℝ) + 1)) :=
      mul_nonneg (sub_nonneg.mpr hbase) hsum
    have hu2 : ((n : ℝ) ^ d) ^ 2 = (n : ℝ) ^ (2 * d) := by
      calc
        ((n : ℝ) ^ d) ^ 2 = (n : ℝ) ^ (d * 2) :=
          (Real.rpow_mul_natCast hnRpos.le d 2).symm
        _ = (n : ℝ) ^ (2 * d) := by congr 1 <;> ring
    push_cast
    nlinarith [hprod, hu2]
  have hDeltaX : (((2 * gS d n + 1) ^ 2 : ℕ) : ℝ) * x ≤ 1 / 2 := by
    have hpowMul : (n : ℝ) ^ (2 * d) * x = (n : ℝ) ^ (2 * d - D₀ / 4) := by
      dsimp [x]
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> ring
    calc
      (((2 * gS d n + 1) ^ 2 : ℕ) : ℝ) * x ≤
          25 * (n : ℝ) ^ (2 * d) * x :=
        mul_le_mul_of_nonneg_right hDeltaCast hxnonneg
      _ = 25 * (n : ℝ) ^ (2 * d - D₀ / 4) := by
        calc
          _ = 25 * ((n : ℝ) ^ (2 * d) * x) := by ring
          _ = _ := by rw [hpowMul]
      _ ≤ 1 / 2 := by
        have hgap := hn₀ n hn
        rcases hgap with ⟨⟨hprobGap, hdeltaGap⟩, hnlarge⟩
        have hdeltaGap' : 50 * (n : ℝ) ^ (2 * d - D₀ / 4) < 1 := by simpa using hdeltaGap
        have hhalfGap : 25 * (n : ℝ) ^ (2 * d - D₀ / 4) < 1 / 2 := by
          calc
            25 * (n : ℝ) ^ (2 * d - D₀ / 4) =
                (50 * (n : ℝ) ^ (2 * d - D₀ / 4)) / 2 := by ring
            _ < 1 / 2 := div_lt_div_of_pos_right hdeltaGap' (by norm_num)
        exact le_of_lt hhalfGap
  have hBern : 1 - (((2 * gS d n + 1) ^ 2 : ℕ) : ℝ) * x ≤
      (1 - x) ^ ((2 * gS d n + 1) ^ 2) := by
    have h := one_add_mul_le_pow (a := -x) (by linarith [hxlt])
      ((2 * gS d n + 1) ^ 2)
    convert h using 1 <;> ring
  have hpowerHalf : (1 / 2 : ℝ) ≤ (1 - x) ^ ((2 * gS d n + 1) ^ 2) := by
    linarith [hBern, hDeltaX]
  have hcharge : x / 2 ≤ x * (1 - x) ^ ((2 * gS d n + 1) ^ 2) := by
    calc
      x / 2 = x * (1 / 2) := by ring
      _ ≤ x * (1 - x) ^ ((2 * gS d n + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hpowerHalf hxnonneg
  have hxEq : x = xL D₀ n := by
    dsimp [x, xL]
    congr 1 <;> ring
  change LLLInput Q (fun g σ => TagBad Γ M D₀ σ g) (fun g => Γ.keyBall g 1)
    (xL D₀ n) ((2 * gS d n + 1) ^ 2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [xL]
    rw [show -(D₀ / 4) = -D₀ / 4 by ring]
    simpa [x] using hxnonneg
  · dsimp [xL]
    rw [show -(D₀ / 4) = -D₀ / 4 by ring]
    simpa [x] using hxlt
  · intro g
    exact TagStageQ.tagBad_depends D₀ Γ M g
  · intro g
    simpa using hdegree g
  · intro g
    calc
      (FinProb.pi Q).pr (fun σ => TagBad Γ M D₀ σ g) ≤ x / 2 := hmarkovBound g
      _ = xL D₀ n / 2 := by rw [hxEq]
      _ ≤ xL D₀ n * (1 - xL D₀ n) ^ ((2 * gS d n + 1) ^ 2) := by
        rw [← hxEq]
        exact hcharge

/-- L7.1e(iii) (07:177–194): under the tag law the tags are typical with constant `8(K+1)` except with probability
`n 2^n 4^{-n}`.  Moments: for even roles with distinct grid keys, removing the at most `2s+1` tag events touching
each key costs a factor `2` per role and leaves independent raw tags with means `≤ K` (profile (i)); then
Lemma 3.6 with near = same grid key (fraction `(2n^{-d/4})^s`, cap `e^{n^{d/2}}`) and a union over labels
(`scatteredMoments_union_labels`). -/
theorem typical_tags (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      0 < N → N ≤ n * 2 ^ n → CondProductBound → GeomFacts Γ →
      (∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K) → TagLLL Γ M Q D₀ →
      (tagLaw Γ M Q D₀).pr (fun σ => ¬ Typical Γ M (8 * (K + 1)) σ) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  classical
  have htouchExp : d - D₀ / 4 < 0 := by linarith
  have htouchGap := TagStageQ.eventually_power_gap (d - D₀ / 4) 0 10
    htouchExp (by norm_num)
  have hsmallEvent := TagStageQ.eventually_tag_moment_small D₀ d hD₀ hd hd'
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((htouchGap.and hsmallEvent).and hlarge)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y p κ Γ M Q hN hNle hCP hG hmean hT
  rcases hn₀ n hn with ⟨⟨htouchLarge, hsmallLarge⟩, hn2⟩
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let roleKey : EvenRole n → Γ.Key := fun a => (Γ.key a.1).1
  let load : EvenRole n → Fin N → (Γ.Key → M.ι) → ℝ :=
    fun a y σ => (N : ℝ) * (M.μ (σ (roleKey a))).w y
  let rawMean : EvenRole n → Fin N → ℝ := fun a y =>
    (Q (roleKey a)).expect (fun i => (N : ℝ) * (M.μ i).w y)
  let near : EvenRole n → Finset (EvenRole n) := fun a =>
    Finset.univ.filter fun a' => roleKey a' = roleKey a
  let fNear : ℝ := (2 * (n : ℝ) ^ (-d / 4)) ^ gS d n
  let cap : ℝ := Real.exp ((n : ℝ) ^ (d / 2))
  let charge : ℝ := xL D₀ n
  have hbaseCharge : charge * (2 * (gS d n : ℝ) + 1) ≤ 1 / 2 := by
    have hSbase : 2 * (gS d n : ℝ) + 1 ≤ 5 * (n : ℝ) ^ d := by
      have hSle : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by
        dsimp [gS]
        have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ d by positivity)
        have hpow : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnRone (by positivity)
        linarith
      have hpow : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnRone (by positivity)
      nlinarith [hSle]
    have hpowMul : (n : ℝ) ^ d * charge = (n : ℝ) ^ (d - D₀ / 4) := by
      dsimp [charge, xL]
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> ring
    have hgap : 10 * (n : ℝ) ^ (d - D₀ / 4) < 1 := by simpa using htouchLarge
    calc
      charge * (2 * (gS d n : ℝ) + 1) ≤ charge * (5 * (n : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hSbase (Real.rpow_nonneg hnRpos.le _)
      _ = 5 * (n : ℝ) ^ (d - D₀ / 4) := by
        calc
          charge * (5 * (n : ℝ) ^ d) = 5 * ((n : ℝ) ^ d * charge) := by ring
          _ = 5 * (n : ℝ) ^ (d - D₀ / 4) := by rw [hpowMul]
      _ ≤ 1 / 2 := by
        have hhalf : 5 * (n : ℝ) ^ (d - D₀ / 4) < 1 / 2 := by
          calc
            5 * (n : ℝ) ^ (d - D₀ / 4) =
                (1 / 2 : ℝ) * (10 * (n : ℝ) ^ (d - D₀ / 4)) := by ring
            _ < (1 / 2 : ℝ) * 1 := mul_lt_mul_of_pos_left hgap (by norm_num)
            _ = 1 / 2 := by ring
        exact le_of_lt hhalf
  have hchargeBaseBern :
      1 / 2 ≤ (1 - charge) ^ (2 * gS d n + 1) := by
    have hchargeLt : charge < 1 := by
      dsimp [charge, xL]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast (by omega : 1 < n)) (by linarith)
    have h := one_add_mul_le_pow (a := -charge) (by linarith [hchargeLt])
      (2 * gS d n + 1)
    have hBern : 1 - ((2 * gS d n + 1 : ℕ) : ℝ) * charge ≤
        (1 - charge) ^ (2 * gS d n + 1) := by
      convert h using 1 <;> ring
    have hcount : ((2 * gS d n + 1 : ℕ) : ℝ) * charge ≤ 1 / 2 := by
      simpa [mul_comm] using hbaseCharge
    linarith [hBern, hcount]
  have hLLL : LLLInput Q (fun g σ => TagBad Γ M D₀ σ g)
      (fun g => Γ.keyBall g 1) (xL D₀ n) ((2 * gS d n + 1) ^ 2) := by
    simpa [TagLLL] using hT
  have hCPtag := hCP Q (fun g σ => TagBad Γ M D₀ σ g)
    (fun g => Γ.keyBall g 1) (xL D₀ n) ((2 * gS d n + 1) ^ 2) hLLL
  have hnRgt : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hchargeLt : charge < 1 := by
    dsimp [charge, xL]
    exact Real.rpow_lt_one_of_one_lt_of_neg hnRgt (by linarith)
  have hroleCard : 0 < (Fintype.card (EvenRole n) : ℝ) := by
    have hcard : 0 < Fintype.card (EvenRole n) := by
      rw [hG.counts.even_card]
      positivity
    exact_mod_cast hcard
  have hroleNonempty : Nonempty (EvenRole n) := by
    apply Fintype.card_pos_iff.mp
    exact_mod_cast hroleCard
  letI : Nonempty (EvenRole n) := hroleNonempty
  have hmeanOne (a : EvenRole n) (y : Fin N) : rawMean a y ≤ K := by
    dsimp [rawMean]
    calc
      (Q (roleKey a)).expect (fun i => (N : ℝ) * (M.μ i).w y) =
          (N : ℝ) * ∑ i, (Q (roleKey a)).w i * (M.μ i).w y := by
        unfold FinProb.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ K := hmean (roleKey a) y
  have hmeanAverage (y : Fin N) :
      (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, rawMean a y ≤ K := by
    have hsum : ∑ a : EvenRole n, rawMean a y ≤
        (Fintype.card (EvenRole n) : ℝ) * K := by
      calc
        ∑ a : EvenRole n, rawMean a y ≤ ∑ a : EvenRole n, K :=
          Finset.sum_le_sum fun a ha => hmeanOne a y
        _ = (Fintype.card (EvenRole n) : ℝ) * K := by simp
    calc
      (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, rawMean a y ≤
          (Fintype.card (EvenRole n) : ℝ)⁻¹ *
            ((Fintype.card (EvenRole n) : ℝ) * K) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hroleCard.le)
      _ = K := by field_simp [ne_of_gt hroleCard]
  have hrawNonneg (a : EvenRole n) (y : Fin N) : 0 ≤ rawMean a y := by
    dsimp [rawMean]
    calc
      0 = (Q (roleKey a)).expect (fun _ => 0) := (FinProb.expect_const _ 0).symm
      _ ≤ (Q (roleKey a)).expect (fun i => (N : ℝ) * (M.μ i).w y) :=
        FinProb.expect_mono _ fun i => mul_nonneg (by positivity) ((M.μ i).nonneg y)
  have hNearSelf : ∀ a, a ∈ near a := by
    intro a
    simp [near]
  have hNearCard : ∀ a,
      ((near a).card : ℝ) ≤ fNear * Fintype.card (EvenRole n) := by
    intro a
    have hExpEq : -d / 4 = -(d / 4) := by ring
    simpa [near, fNear, hExpEq] using hG.near.even_sameKey a
  have hloadNonneg : ∀ a y σ, 0 ≤ load a y σ := by
    intro a y σ
    exact mul_nonneg (by positivity) ((M.μ (σ (roleKey a))).nonneg y)
  have hcap : ∀ a y σ, σ ∈ (Finset.univ : Finset (Γ.Key → M.ι)) → load a y σ ≤ cap := by
    intro a y σ hσ
    have hμ := (M.pure (σ (roleKey a))).1 y
    calc
      (N : ℝ) * (M.μ (σ (roleKey a))).w y ≤
          (N : ℝ) * (Real.exp ((n : ℝ) ^ (d / 2)) / N) :=
        mul_le_mul_of_nonneg_left hμ hNreal.le
      _ = cap := by
        dsimp [cap]
        field_simp [ne_of_gt hNreal]
  have hsmall : (n : ℝ) * fNear * cap ≤ 1 := by
    have hExpEq : -d / 4 = -(d / 4) := by ring
    simpa [fNear, cap, hExpEq] using hsmallLarge
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    calc
      (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
      _ ≤ (n : ℝ) * 2 ^ n := by exact_mod_cast hNle
  have hrawAverage (y : Fin N) :
      (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, rawMean a y ≤ K := hmeanAverage y
  have hkeySymm (g h : Γ.Key) : Γ.keyDist g h = Γ.keyDist h g := by
    unfold GridGeom.keyDist
    apply Finset.sum_congr rfl
    intro r hr
    exact Nat.dist_comm _ _
  have hjoint : ∀ (y : Fin N) (m : ℕ), m ≤ n → ∀ s : Fin m → EvenRole n,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        (∑ σ ∈ (Finset.univ : Finset (Γ.Key → M.ι)),
          (tagLaw Γ M Q D₀).w σ * ∏ i, load (s i) y σ) ≤
            (2 : ℝ) ^ m * ∏ i, rawMean (s i) y := by
    intro y m hm s hsep
    let keyOf : Fin m → Γ.Key := fun i => roleKey (s i)
    have hkeyInj : Function.Injective keyOf := by
      intro i j hEq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hbad := hsep j i hlt
        apply hbad
        simp [near, keyOf, hEq]
      · have hbad := hsep i j hgt
        apply hbad
        simp [near, keyOf, hEq]
    let Ukey : Finset Γ.Key := Finset.univ.image keyOf
    let coord : Fin m → Ukey := fun i =>
      ⟨keyOf i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    let Φ : (Γ.Key → M.ι) → ℝ := fun σ => ∏ i, load (s i) y σ
    let fCoord : Fin m → M.ι → ℝ := fun i z => (N : ℝ) * (M.μ z).w y
    have hcoord : ∀ i : Fin m, keyOf i ∈ Ukey := fun i =>
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hPhi : ∀ σ, 0 ≤ Φ σ := by
      intro σ
      dsimp [Φ]
      exact Finset.prod_nonneg fun i hi => hloadNonneg (s i) y σ
    have hPhiGlue (ω : Γ.Key → M.ι) (a : ∀ v : Ukey, M.ι) :
        Φ (glue Ukey ω a) = ∏ i, fCoord i (a (coord i)) := by
      dsimp [Φ, load, fCoord, keyOf, roleKey]
      apply Finset.prod_congr rfl
      intro i hi
      have hiU : keyOf i ∈ Ukey := hcoord i
      have hcoordEq : coord i = ⟨keyOf i, hiU⟩ := by
        apply Subtype.ext
        rfl
      have hread : (glue Ukey ω a) (keyOf i) = a ⟨keyOf i, hiU⟩ := by
        simp [glue, keyOf, roleKey, hiU]
      rw [hcoordEq]
      rw [hread]
    have hInnerEq (ω : Γ.Key → M.ι) :
        (∑ a : (∀ v : Ukey, M.ι),
          (FinProb.pi (fun v : Ukey => Q v.1)).w a * Φ (glue Ukey ω a)) =
            ∏ i, rawMean (s i) y := by
      calc
        (∑ a : (∀ v : Ukey, M.ι),
            (FinProb.pi (fun v : Ukey => Q v.1)).w a * Φ (glue Ukey ω a)) =
            (FinProb.pi (fun v : Ukey => Q v.1)).expect
              (fun a => ∏ i, fCoord i (a (coord i))) := by
          rw [FinProb.expect]
          apply Finset.sum_congr rfl
          intro a ha
          rw [hPhiGlue]
        _ = ∏ i, rawMean (s i) y := by
          simpa [rawMean, fCoord, keyOf, roleKey] using
            (TagStageQ.pi_expect_prod_restrict keyOf hkeyInj Q fCoord)
    have hBnonneg : 0 ≤ ∏ i, rawMean (s i) y :=
      Finset.prod_nonneg fun i hi => hrawNonneg (s i) y
    have hB : ∀ ω : Γ.Key → M.ι,
        (∑ a : (∀ v : Ukey, M.ι),
          (FinProb.pi (fun v : Ukey => Q v.1)).w a * Φ (glue Ukey ω a)) ≤
            ∏ i, rawMean (s i) y := by
      intro ω
      rw [hInnerEq]
    let Touch : Finset Γ.Key := Finset.univ.filter fun g =>
      ¬ Disjoint (Γ.keyBall g 1) Ukey
    have hTouchSub : Touch ⊆ Finset.univ.biUnion fun i : Fin m => Γ.keyBall (keyOf i) 1 := by
      intro g hg
      have hnot := (Finset.mem_filter.mp hg).2
      obtain ⟨k, hkg, hkU⟩ := Finset.not_disjoint_iff.mp hnot
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkU
      have hdist : Γ.keyDist g (keyOf i) ≤ 1 := by
        simpa [GridGeom.keyBall] using (Finset.mem_filter.mp hkg).2
      have hdist' : Γ.keyDist (keyOf i) g ≤ 1 := by
        rw [hkeySymm]
        exact hdist
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simpa [GridGeom.keyBall] using hdist'
    have hballCardNat (g : Γ.Key) : (Γ.keyBall g 1).card ≤ 2 * gS d n + 1 := by
      have hreal := hG.balls.keyBall_card g 1
      have hreal' : ((Γ.keyBall g 1).card : ℝ) ≤
          (((2 * gS d n + 1 : ℕ) : ℝ)) := by simpa using hreal
      exact_mod_cast hreal'
    have hTouchCard : Touch.card ≤ m * (2 * gS d n + 1) := by
      calc
        Touch.card ≤ (Finset.univ.biUnion fun i : Fin m => Γ.keyBall (keyOf i) 1).card :=
          Finset.card_le_card hTouchSub
        _ ≤ ∑ i : Fin m, (Γ.keyBall (keyOf i) 1).card := Finset.card_biUnion_le
        _ ≤ ∑ i : Fin m, (2 * gS d n + 1) :=
          Finset.sum_le_sum fun i hi => hballCardNat (keyOf i)
        _ = m * (2 * gS d n + 1) := by simp
    have hcostDen : (1 / 2 : ℝ) ^ m ≤ (1 - charge) ^ Touch.card := by
      have hpowCost : (1 / 2 : ℝ) ^ m ≤
          (1 - charge) ^ (m * (2 * gS d n + 1)) := by
        calc
          (1 / 2 : ℝ) ^ m ≤ ((1 - charge) ^ (2 * gS d n + 1)) ^ m :=
            pow_le_pow_left₀ (by norm_num) hchargeBaseBern m
          _ = (1 - charge) ^ ((2 * gS d n + 1) * m) := by rw [pow_mul]
          _ = (1 - charge) ^ (m * (2 * gS d n + 1)) := by
            exact congrArg (fun k : ℕ => (1 - charge) ^ k) (Nat.mul_comm _ _)
      have hbaseNonneg : 0 ≤ 1 - charge := sub_nonneg.mpr hchargeLt.le
      have hchargeNonneg : 0 ≤ charge := by
        dsimp [charge, xL]
        exact Real.rpow_nonneg hnRpos.le _
      have hbaseLeOne : 1 - charge ≤ 1 := sub_le_self 1 hchargeNonneg
      exact hpowCost.trans (pow_le_pow_of_le_one hbaseNonneg hbaseLeOne hTouchCard)
    have hcostInv : ((1 - charge) ^ Touch.card)⁻¹ ≤ (2 : ℝ) ^ m := by
      have h := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) hcostDen
      simpa [one_div] using h
    have hcondMoment := hCPtag.2 Ukey Φ hPhi (∏ i, rawMean (s i) y) hB
    have hcondBound : (tagLaw Γ M Q D₀).expect Φ ≤
        ((1 - charge) ^ Touch.card)⁻¹ * ∏ i, rawMean (s i) y := by
      simpa [tagLaw, Touch, charge, Finset.prod_const] using hcondMoment
    have hCondMoment : (tagLaw Γ M Q D₀).expect Φ ≤
        (2 : ℝ) ^ m * ∏ i, rawMean (s i) y := by
      calc
        (tagLaw Γ M Q D₀).expect Φ ≤
            ((1 - charge) ^ Touch.card)⁻¹ * ∏ i, rawMean (s i) y := hcondBound
        _ ≤ (2 : ℝ) ^ m * ∏ i, rawMean (s i) y :=
          mul_le_mul_of_nonneg_right hcostInv hBnonneg
    have hsumExpect :
        (∑ σ ∈ (Finset.univ : Finset (Γ.Key → M.ι)),
          (tagLaw Γ M Q D₀).w σ * Φ σ) = (tagLaw Γ M Q D₀).expect Φ := by
      simp [FinProb.expect]
    rw [hsumExpect]
    exact hCondMoment
  have hScattered := scatteredMoments_union_labels
    (tagLaw Γ M Q D₀) (Finset.univ : Finset (Γ.Key → M.ι)) load
    hloadNonneg (Real.exp ((n : ℝ) ^ (d / 2))) (by positivity)
    (by intro a y σ hσ; exact hcap a y σ hσ)
    near hNearSelf fNear (by positivity) hNearCard n (by omega)
    (2 : ℝ) K (by norm_num) hK rawMean hrawNonneg hrawAverage hjoint hsmall hlabels
  have hfailEvent : ∀ σ,
      ¬ Typical Γ M (8 * (K + 1)) σ ↔
        ∃ y, 8 * (K + 1) <
          (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a : EvenRole n, load a y σ := by
    intro σ
    simp [Typical, load, roleKey]
  have hthreshold : 4 * (2 : ℝ) * (K + 1) = 8 * (K + 1) := by ring
  simpa [FinProb.pr, Finset.mem_univ, hfailEvent, load, roleKey, hthreshold] using hScattered

/-- Step 2 assembled: the tag events satisfy the local-lemma input and the tag law gives typical tags. -/
theorem tag_stage (D₀ d K : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
      0 < N → N ≤ n * 2 ^ n → GeomFacts Γ → Eq71At D₀ d n N E X Y →
      TagLLL Γ M P.Q D₀ ∧
        (tagLaw Γ M P.Q D₀).pr (fun σ => ¬ Typical Γ M (8 * (K + 1)) σ) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hcross⟩ := cross_fail_mean D₀ d hd hd8
  obtain ⟨n₂, hlll⟩ := tag_lll D₀ d K hD₀ hd hd'
  obtain ⟨n₃, htyp⟩ := typical_tags D₀ d K hD₀ hd hd' hK
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  intro n hn N E G X Y p κ Γ M P hN hNle hG h71
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hT : TagLLL Γ M P.Q D₀ :=
    hlll n hn₂ Γ M P.Q hG.loc hG.balls (hcross n hn₁ Γ M P.Q K hN hG.loc P.mu_mean h71)
  exact ⟨hT, htyp n hn₃ Γ M P.Q hN hNle cond_product_bound hG P.mu_mean hT⟩

end HypercubeRamsey.S07
