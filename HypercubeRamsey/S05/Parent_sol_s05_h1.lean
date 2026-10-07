import HypercubeRamsey.S05.Bounds_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h1

open Classical Filter Real
open OAI.HypercubeRamsey
open scoped Topology BigOperators

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 400000

noncomputable section

theorem prob_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (F : Ω → Prop) : 0 ≤ P.pr F := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [P.nonneg ω]

theorem expect_div {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun ω => f ω / c) = P.expect f / c := by
  simp only [FinProb.expect, mul_div_assoc, Finset.sum_div]

theorem exp_half_square (a : ℝ) : exp (-a) = exp (-a / 2) ^ 2 := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

theorem family_bound {Ω I C : Type*} [Fintype Ω] [Fintype I] [Fintype C]
    (P : FinProb Ω) (code : I → C) (rate : I → Ω → ℝ) (threshold : I → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hnonneg : ∀ i ω, 0 ≤ rate i ω) (hpos : ∀ i, 0 < threshold i)
    (hraw : ∀ i, P.expect (rate i) ≤ threshold i ^ 2)
    (hsmall : ∀ i, threshold i ≤ ε)
    (hsame : ∀ i j, code i = code j → rate i = rate j ∧ threshold i = threshold j) :
    P.pr (fun ω => ∃ i, threshold i < rate i ω) ≤ (Fintype.card C : ℝ) * ε := by
  apply coded_markov P code rate threshold ε hε hnonneg hpos _ hsame
  intro i
  calc
    P.expect (rate i) ≤ threshold i ^ 2 := hraw i
    _ ≤ ε * threshold i := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hsmall i) (hpos i).le

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def RawStep1 : Prop :=
  (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
    X.baseLaw.pr (fun b => X.step1Fail b ℓ K.1.1 (X.p.typeSegs n K)) ≤
      exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)))) ∧
  ∀ ℓ, X.KeyOccurs ℓ → X.baseLaw.pr (fun b => X.capFail b ℓ) ≤
    exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))))

def RawStep2 : Prop :=
  (∀ K, X.TypeOccurs K → X.keyLaw.pr (fun H => X.step2Fail H K) ≤
    ((K.2.1.card : ℝ) + 1) * exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)))) ∧
  ∀ K t, X.OptOccurs K t → X.keyLaw.pr (fun H => X.optFail H K t) ≤
    exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)))

def ParentGood (v : Fin N) : Prop :=
  (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) ≤
      exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)) ∧
  (∀ ℓ, X.KeyOccurs ℓ → (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) ≤
      exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) / 2)) ∧
  (∀ K, X.TypeOccurs K → (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) ≤
      ((K.2.1.card : ℝ) + 1) * exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)) ∧
  ∀ K t, X.OptOccurs K t → (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) ≤
      exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)

theorem base_event_mean (F : X.Base → Prop) :
    X.baseLaw.pr F = X.P.prior.parent.expect (fun v => (X.coarseLaw v).pr (fun c => F (v, c))) :=
  bind_pr X.P.prior.parent X.coarseLaw F

theorem key_event_mean (F : X.KeyHist → Prop) :
    X.keyLaw.pr F = X.P.prior.parent.expect (fun v => (X.keyLawAt v).pr (fun cu => F ((v, cu.1), cu.2))) := by
  classical
  unfold Setup5.keyLaw
  rw [bind_pr]
  unfold Setup5.baseLaw
  simpa only [Setup5.keyLawAt, bind_pr, FinProb.expect] using
    FinProb.bind_expect X.P.prior.parent X.coarseLaw
      (fun v c => (X.hiddenLaw (v, c)).pr (fun U => F ((v, c), U)))

abbrev LowRole := {x : OAI.HypercubeRamsey.CubeVertex n // IsEvenRole x ∧ X.g.severity x ≤ X.p.J n}
abbrev HighRole := {x : OAI.HypercubeRamsey.CubeVertex n // IsEvenRole x ∧ ¬ X.g.severity x ≤ X.p.J n}
abbrev LowCompIdx := Σ x : LowRole X, {ℓ : X.Key // ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x.1)}
abbrev HighCompIdx := Σ x : HighRole X, {ℓ : X.Key // ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x.1)}
abbrev CapIdx := {ℓ : X.Key // X.KeyOccurs ℓ}
abbrev OptIdx := {q : HighRole X × OAI.HypercubeRamsey.CubeVertex (X.p.m n) //
  X.OptOccurs (X.g.evenType (X.p.J n) q.1.1) q.2}

def typeThreshold (x : OAI.HypercubeRamsey.CubeVertex n) : ℝ :=
  exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n (X.g.evenType (X.p.J n) x))) / 2)

def compRate (x : OAI.HypercubeRamsey.CubeVertex n) (ℓ : X.Key) (v : Fin N) : ℝ :=
  (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ (X.g.key x).1
    (X.p.typeSegs n (X.g.evenType (X.p.J n) x)))

def typeRate (x : OAI.HypercubeRamsey.CubeVertex n) (v : Fin N) : ℝ :=
  (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x)) /
    ((X.g.typeKeys (X.p.J n) x).card + 1 : ℝ)

theorem cap_alarm_bound (hr : RawStep1 X) (hm : 1 ≤ X.p.m n) :
    X.P.prior.parent.pr (fun v => ∃ ℓ : CapIdx X,
      exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.1.level + 1))) / 2) <
        (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ.1)) ≤
      (Fintype.card (LowShape (X.p.m n) (X.p.J n)) : ℝ) * regularEps X.p n := by
  classical
  apply family_bound X.P.prior.parent (fun ℓ : CapIdx X => capCode X ℓ.1)
    (fun ℓ v => (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ.1))
    (fun ℓ => exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.1.level + 1))) / 2))
    (regularEps X.p n) (exp_pos _).le
    (fun ℓ v => prob_nonneg _ _) (fun ℓ => exp_pos _) ?_ ?_ ?_
  · intro ℓ
    have h := hr.2 ℓ.1 ℓ.2
    rw [base_event_mean] at h
    simpa only [exp_half_square] using h
  · intro ℓ
    exact regular_threshold_le X.p n hm (ℓ.1.level + 1)
  · intro ℓ ℓ' hcode
    have hl : ℓ.1.level = ℓ'.1.level :=
      congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.1.val) hcode
    constructor
    · funext v
      exact (capCode_rate X v ℓ.1 ℓ'.1 hcode).symm
    · simp [hl]

theorem low_comp_alarm_bound (hr : RawStep1 X) (hm : 1 ≤ X.p.m n) :
    X.P.prior.parent.pr (fun v => ∃ q : LowCompIdx X,
      typeThreshold X q.1.1 < compRate X q.1.1 q.2.1 v) ≤
      (Fintype.card (LowShape (X.p.m n) (X.p.J n)) : ℝ) * (Fintype.card KeyCode : ℝ) *
        regularEps X.p n := by
  classical
  let code (q : LowCompIdx X) := lowComparisonCode X q.1.1 q.1.2.2 q.2.1 q.2.2
  have h := family_bound X.P.prior.parent code
    (fun q v => compRate X q.1.1 q.2.1 v) (fun q => typeThreshold X q.1.1)
    (regularEps X.p n) (exp_pos _).le
    (fun q v => prob_nonneg _ _) (fun q => exp_pos _) ?_ ?_ ?_
  · simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using h
  · intro q
    have hK : X.TypeOccurs (X.g.evenType (X.p.J n) q.1.1) := ⟨q.1.1, q.1.2.1, rfl⟩
    have hr := hr.1 _ hK q.2.1 q.2.2
    rw [base_event_mean] at hr
    simpa only [compRate, typeThreshold, exp_half_square, ChunkGeometry5.evenType, Prod.fst] using hr
  · intro q
    simpa [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType, q.1.2.2] using
      regular_threshold_le X.p n hm (X.g.severity q.1.1)
  · intro q q' hcode
    constructor
    · funext v
      exact (lowComparison_rate X v q.1.1 q'.1.1 q.1.2.2 q'.1.2.2 q.2.1 q'.2.1 q.2.2 q'.2.2 hcode).symm
    · have hs : X.g.severity q.1.1 = X.g.severity q'.1.1 :=
        congrArg (fun c : LowShape (X.p.m n) (X.p.J n) × KeyCode => c.1.1.val) hcode
      simp [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType, q.1.2.2, q'.1.2.2, hs]

theorem high_comp_alarm_bound (hr : RawStep1 X) :
    X.P.prior.parent.pr (fun v => ∃ q : HighCompIdx X,
      typeThreshold X q.1.1 < compRate X q.1.1 q.2.1 v) ≤
      (Fintype.card HighShape : ℝ) * (Fintype.card KeyCode : ℝ) * highEps X.p n := by
  classical
  let code (q : HighCompIdx X) := highComparisonCode X q.1.1 q.1.2.2 q.2.1 q.2.2
  have h := family_bound X.P.prior.parent code
    (fun q v => compRate X q.1.1 q.2.1 v) (fun q => typeThreshold X q.1.1)
    (highEps X.p n) (exp_pos _).le
    (fun q v => prob_nonneg _ _) (fun q => exp_pos _) ?_ ?_ ?_
  · simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using h
  · intro q
    have hK : X.TypeOccurs (X.g.evenType (X.p.J n) q.1.1) := ⟨q.1.1, q.1.2.1, rfl⟩
    have hr := hr.1 _ hK q.2.1 q.2.2
    rw [base_event_mean] at hr
    simpa only [compRate, typeThreshold, exp_half_square, ChunkGeometry5.evenType, Prod.fst] using hr
  · intro q
    simp [typeThreshold, highEps, Params5.typeSegs, ChunkGeometry5.evenType, q.1.2.2]
  · intro q q' hcode
    constructor
    · funext v
      exact (highComparison_rate X v q.1.1 q'.1.1 q.1.2.2 q'.1.2.2 q.2.1 q'.2.1 q.2.2 q'.2.2 hcode).symm
    · simp [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType, q.1.2.2, q'.1.2.2]



theorem type_event_bound (hr : RawStep2 X) (x : CubeVertex n) (hx : IsEvenRole x) :
    X.P.prior.parent.expect (typeRate X x) ≤ typeThreshold X x ^ 2 := by
  have hK : X.TypeOccurs (X.g.evenType (X.p.J n) x) := ⟨x, hx, rfl⟩
  have h := hr.1 _ hK
  rw [key_event_mean, exp_half_square] at h
  change X.P.prior.parent.expect (fun v => (X.keyLawAt v).pr
    (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x))) ≤
      ((X.g.typeKeys (X.p.J n) x).card + 1 : ℝ) * typeThreshold X x ^ 2 at h
  unfold typeRate
  rw [expect_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (X.g.typeKeys (X.p.J n) x).card + 1)).2
  exact h.trans_eq (mul_comm _ _)

theorem low_type_alarm_bound (hr : RawStep2 X) (hm : 1 ≤ X.p.m n) :
    X.P.prior.parent.pr (fun v => ∃ x : LowRole X,
      typeThreshold X x.1 < typeRate X x.1 v) ≤
      (Fintype.card (LowShape (X.p.m n) (X.p.J n)) : ℝ) * regularEps X.p n := by
  classical
  apply family_bound X.P.prior.parent (fun x : LowRole X => lowShape X x.1 x.2.2)
    (fun x => typeRate X x.1) (fun x => typeThreshold X x.1) (regularEps X.p n)
    (exp_pos _).le ?_ (fun x => exp_pos _) ?_ ?_ ?_
  · intro x v
    exact div_nonneg (prob_nonneg _ _) (by positivity)
  · intro x
    exact type_event_bound X hr x.1 x.2.1
  · intro x
    simpa only [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType,
      dif_pos x.2.2, Prod.snd] using regular_threshold_le X.p n hm (X.g.severity x.1)
  · intro x x' hcode
    constructor
    · funext v
      unfold typeRate
      rw [lowShape_step2Rate X v x.1 x'.1 x.2.2 x'.2.2 hcode,
        lowShape_keys_card X x.1 x'.1 x.2.2 x'.2.2 hcode]
    · have hs : X.g.severity x.1 = X.g.severity x'.1 :=
        congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.1.val) hcode
      simp only [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType,
        dif_pos x.2.2, dif_pos x'.2.2, Prod.snd, hs]

theorem high_type_alarm_bound (hr : RawStep2 X) :
    X.P.prior.parent.pr (fun v => ∃ x : HighRole X,
      typeThreshold X x.1 < typeRate X x.1 v) ≤
      (Fintype.card HighShape : ℝ) * highEps X.p n := by
  classical
  apply family_bound X.P.prior.parent (fun x : HighRole X => highShape X x.1 x.2.2)
    (fun x => typeRate X x.1) (fun x => typeThreshold X x.1) (highEps X.p n)
    (exp_pos _).le ?_ (fun x => exp_pos _) ?_ ?_ ?_
  · intro x v
    exact div_nonneg (prob_nonneg _ _) (by positivity)
  · intro x
    exact type_event_bound X hr x.1 x.2.1
  · intro x
    simp only [typeThreshold, highEps, Params5.typeSegs, ChunkGeometry5.evenType,
      dif_neg x.2.2, Prod.snd]
    exact le_rfl
  · intro x x' hcode
    constructor
    · funext v
      unfold typeRate
      rw [highShape_step2Rate X v x.1 x'.1 x.2.2 x'.2.2 hcode,
        highShape_keys_card X x.1 x'.1 x.2.2 x'.2.2 hcode]
    · simp only [typeThreshold, Params5.typeSegs, ChunkGeometry5.evenType,
        dif_neg x.2.2, dif_neg x'.2.2, Prod.snd]

theorem opt_alarm_bound (hr : RawStep2 X) :
    X.P.prior.parent.pr (fun v => ∃ q : OptIdx X,
      highEps X.p n < (X.keyLawAt v).pr
        (fun cu => X.optFail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) q.1.1.1) q.1.2)) ≤
      (Fintype.card HighShape : ℝ) * highEps X.p n := by
  classical
  apply family_bound X.P.prior.parent (fun q : OptIdx X => highShape X q.1.1.1 q.1.1.2.2)
    (fun q v => (X.keyLawAt v).pr
      (fun cu => X.optFail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) q.1.1.1) q.1.2))
    (fun _ => highEps X.p n) (highEps X.p n) (exp_pos _).le
    (fun q v => prob_nonneg _ _) (fun _ => exp_pos _) ?_ (fun _ => le_rfl) ?_
  · intro q
    have h := hr.2 _ _ q.2
    rw [key_event_mean] at h
    simpa only [highEps, exp_half_square] using h
  · intro q q' hcode
    refine ⟨?_, rfl⟩
    funext v
    exact (highShape_optRate X v q.1.1.1 q'.1.1.1 q.1.1.2.2 q'.1.1.2.2 hcode q.1.2 q'.1.2).symm

def lowCompAlarm (v : Fin N) : Prop :=
  ∃ q : LowCompIdx X, typeThreshold X q.1.1 < compRate X q.1.1 q.2.1 v

def highCompAlarm (v : Fin N) : Prop :=
  ∃ q : HighCompIdx X, typeThreshold X q.1.1 < compRate X q.1.1 q.2.1 v

def capAlarm (v : Fin N) : Prop :=
  ∃ ℓ : CapIdx X, exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.1.level + 1))) / 2) <
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ.1)

def lowTypeAlarm (v : Fin N) : Prop :=
  ∃ x : LowRole X, typeThreshold X x.1 < typeRate X x.1 v

def highTypeAlarm (v : Fin N) : Prop :=
  ∃ x : HighRole X, typeThreshold X x.1 < typeRate X x.1 v

def optAlarm (v : Fin N) : Prop :=
  ∃ q : OptIdx X, highEps X.p n < (X.keyLawAt v).pr
    (fun cu => X.optFail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) q.1.1.1) q.1.2)

theorem not_good_alarm (v : Fin N) (hbad : ¬ ParentGood X v) :
    lowCompAlarm X v ∨ highCompAlarm X v ∨ capAlarm X v ∨
      lowTypeAlarm X v ∨ highTypeAlarm X v ∨ optAlarm X v := by
  classical
  unfold ParentGood at hbad
  simp only [not_and_or] at hbad
  rcases hbad with hc | hcap | ht | ho
  · push_neg at hc
    obtain ⟨K, hK, ℓ, hℓ, hf⟩ := hc
    obtain ⟨x, hx, rfl⟩ := hK
    by_cases hj : X.g.severity x ≤ X.p.J n
    · exact Or.inl ⟨⟨⟨x, hx, hj⟩, ⟨ℓ, hℓ⟩⟩, hf⟩
    · exact Or.inr (Or.inl ⟨⟨⟨x, hx, hj⟩, ⟨ℓ, hℓ⟩⟩, hf⟩)
  · push_neg at hcap
    obtain ⟨ℓ, hℓ, hf⟩ := hcap
    exact Or.inr (Or.inr (Or.inl ⟨⟨ℓ, hℓ⟩, hf⟩))
  · push_neg at ht
    obtain ⟨K, hK, hf⟩ := ht
    obtain ⟨x, hx, rfl⟩ := hK
    have hnorm : typeThreshold X x < typeRate X x v := by
      change ((X.g.typeKeys (X.p.J n) x).card + 1 : ℝ) * typeThreshold X x <
        (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2)
          (X.g.evenType (X.p.J n) x)) at hf
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (X.g.typeKeys (X.p.J n) x).card + 1)).2
      exact (mul_comm _ _).trans_lt hf
    by_cases hj : X.g.severity x ≤ X.p.J n
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨x, hx, hj⟩, hnorm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨x, hx, hj⟩, hnorm⟩))))
  · push_neg at ho
    obtain ⟨K, t, hK, hf⟩ := ho
    obtain ⟨x, hx, rfl, hopt⟩ := hK
    have hj : ¬ X.g.severity x ≤ X.p.J n := by
      by_cases hs : X.g.severity x = X.p.J n + 1
      · omega
      · simp only [ChunkGeometry5.optionalKey, if_neg hs] at hopt
        cases hopt
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨(⟨x, hx, hj⟩, t), x, hx, rfl, hopt⟩, hf⟩))))

theorem prob_or_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (F G : Ω → Prop) :
    P.pr (fun ω => F ω ∨ G ω) ≤ P.pr F + P.pr G := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hF : F ω <;> by_cases hG : G ω <;>
    simp only [hF, hG, or_true, true_or, or_false, false_or, ite_true, ite_false, zero_add, add_zero]
  all_goals linarith [P.nonneg ω]

theorem parent_bad_bound (hr1 : RawStep1 X) (hr2 : RawStep2 X) (hm : 1 ≤ X.p.m n) :
    X.P.prior.parent.pr (fun v => ¬ ParentGood X v) ≤
      (Fintype.card (LowShape (X.p.m n) (X.p.J n)) : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) *
        regularEps X.p n +
      (Fintype.card HighShape : ℝ) * ((Fintype.card KeyCode : ℝ) + 2) * highEps X.p n := by
  let P := X.P.prior.parent
  have h1 := low_comp_alarm_bound X hr1 hm
  have h2 := high_comp_alarm_bound X hr1
  have h3 := cap_alarm_bound X hr1 hm
  have h4 := low_type_alarm_bound X hr2 hm
  have h5 := high_type_alarm_bound X hr2
  have h6 := opt_alarm_bound X hr2
  have hunion := prob_or_le P (lowCompAlarm X) (fun v => highCompAlarm X v ∨ capAlarm X v ∨
    lowTypeAlarm X v ∨ highTypeAlarm X v ∨ optAlarm X v)
  have hu2 := prob_or_le P (highCompAlarm X) (fun v => capAlarm X v ∨
    lowTypeAlarm X v ∨ highTypeAlarm X v ∨ optAlarm X v)
  have hu3 := prob_or_le P (capAlarm X) (fun v => lowTypeAlarm X v ∨ highTypeAlarm X v ∨ optAlarm X v)
  have hu4 := prob_or_le P (lowTypeAlarm X) (fun v => highTypeAlarm X v ∨ optAlarm X v)
  have hu5 := prob_or_le P (highTypeAlarm X) (optAlarm X)
  have hmono := pr_mono P (not_good_alarm X)
  change P.pr (lowCompAlarm X) ≤ _ at h1
  change P.pr (highCompAlarm X) ≤ _ at h2
  change P.pr (capAlarm X) ≤ _ at h3
  change P.pr (lowTypeAlarm X) ≤ _ at h4
  change P.pr (highTypeAlarm X) ≤ _ at h5
  change P.pr (optAlarm X) ≤ _ at h6
  nlinarith only [h1, h2, h3, h4, h5, h6, hunion, hu2, hu3, hu4, hu5, hmono]

theorem parent_good_mass (p : Params5 γ K' χ) (hp : stage1Request.Holds p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → RawStep1 X → RawStep2 X →
        99 / 100 ≤ X.P.prior.parent.pr (ParentGood X) := by
  obtain ⟨n₀, hsmall⟩ := eventually_alarm_small p (request_budget p hp)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp hr1 hr2
  obtain ⟨hm, hlow, hhigh⟩ := hsmall n hn
  have hm1 : 1 ≤ X.p.m n := by rw [hXp]; omega
  have hbad := parent_bad_bound X hr1 hr2 hm1
  rw [hXp] at hbad
  have hcompl := FinProb.pr_compl5 X.P.prior.parent (ParentGood X)
  linarith

end
end HypercubeRamsey.Lane_sol_s05_h1
