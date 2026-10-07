import HypercubeRamsey.S05.History_q_s05_hist2

namespace HypercubeRamsey.Lane_q_s05_hist1b

open Classical OAI.HypercubeRamsey

theorem ratio5_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ ratio5 a b := by
  unfold ratio5
  split_ifs <;> positivity

theorem ratio5_le_of_mul_le {a b M : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : 0 ≤ M) (h : a ≤ M * b) : ratio5 a b ≤ M := by
  unfold ratio5
  split_ifs with hb0
  · exact hM
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    exact (div_le_iff₀ hbpos).2 (by simpa [mul_comm] using h)

theorem blockWeight_nonneg {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (keys : Finset X.Key) (z : X.Block K) :
    0 ≤ X.blockWeight H K keys z := by
  have hbase : 0 ≤ X.blockBase H.1 K z := by
    unfold Setup5.blockBase
    exact Finset.prod_nonneg fun s _ => (X.segLaw H.1.1 (H.1.2.1 K.1.1)).nonneg (z s)
  have hlik (ℓ : X.Key) : 0 ≤ X.colLik H.1 K ℓ z (H.2 ℓ) := by
    unfold Setup5.colLik
    apply Finset.prod_nonneg
    intro h _
    exact ratio5_nonneg
      ((X.priorRep H.1 ℓ K.1.1 z).nonneg (H.2 ℓ h))
      ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).nonneg (H.2 ℓ h))
  have hgate : 0 ≤ (if X.blockGate H.1 K z then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  unfold Setup5.blockWeight
  exact mul_nonneg (mul_nonneg hbase hgate) (Finset.prod_nonneg fun ℓ _ => hlik ℓ)

theorem typeSegs_le_streamSegs {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (K : X.Ty) :
    X.p.typeSegs n K ≤ X.p.streamSegs n := by
  classical
  cases htype : K.2.2 with
  | none =>
    rw [show X.p.typeSegs n K = X.p.uStarSeg n by
      simp [Params5.typeSegs, htype]]
    simpa [Params5.streamSegs] using
      (Nat.le_max_right (X.p.uSeg n (X.p.J n + 1)) (X.p.uStarSeg n))
  | some j =>
    have hjJ : j.val ≤ X.p.J n := Nat.le_of_lt_succ j.isLt
    have hlog : 0 ≤ Real.log (X.p.m n : ℝ) := by
      by_cases hm : X.p.m n = 0
      · simp [hm]
      · apply Real.log_nonneg
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hcoef : 0 ≤ X.p.K1 * Real.log (X.p.m n : ℝ) / (X.p.q0 : ℝ) :=
      div_nonneg (mul_nonneg X.p.hK1.le hlog) (by exact_mod_cast X.p.hq0.1.le)
    have hjcast : (j.val : ℝ) ≤ ((X.p.J n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show j.val ≤ X.p.J n + 1 by omega)
    have hraw : X.p.K1 * ((j.val : ℝ) + 4) * Real.log (X.p.m n : ℝ) /
          (X.p.q0 : ℝ) ≤
        X.p.K1 * (((X.p.J n + 1 : ℕ) : ℝ) + 4) * Real.log (X.p.m n : ℝ) /
          (X.p.q0 : ℝ) := by
      calc
        _ = ((j.val : ℝ) + 4) *
            (X.p.K1 * Real.log (X.p.m n : ℝ) / (X.p.q0 : ℝ)) := by ring
        _ ≤ (((X.p.J n + 1 : ℕ) : ℝ) + 4) *
            (X.p.K1 * Real.log (X.p.m n : ℝ) / (X.p.q0 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith) hcoef
        _ = _ := by ring
    have hceil := Nat.ceil_mono hraw
    have hu : X.p.uSeg n j.val ≤ X.p.uSeg n (X.p.J n + 1) := by
      simpa [Params5.uSeg] using hceil
    have hmax : X.p.uSeg n (X.p.J n + 1) ≤ X.p.streamSegs n := by
      simpa [Params5.streamSegs] using
        (Nat.le_max_left (X.p.uSeg n (X.p.J n + 1)) (X.p.uStarSeg n))
    rw [show X.p.typeSegs n K = X.p.uSeg n j.val by simp [Params5.typeSegs, htype]]
    exact hu.trans hmax

theorem priorRep_trueBlock_eq_prior {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (hk : X.p.typeSegs n K ≤ X.p.streamSegs n) :
    X.priorRep H.1 ℓ K.1.1 (X.trueBlock H.1 K) = X.prior H.1 ℓ := by
  classical
  have hreplace : X.replaceStream H.1.2.2 K.1.1 (X.trueBlock H.1 K) = H.1.2.2 := by
    funext w s
    by_cases hw : w = K.1.1
    · subst w
      by_cases hs : (s : ℕ) < X.p.typeSegs n K
      · have hs' : (s : ℕ) < X.p.streamSegs n := lt_of_lt_of_le hs hk
        simp [Setup5.replaceStream, hs, Setup5.trueBlock, hs']
      · simp [Setup5.replaceStream, hs]
    · simp [Setup5.replaceStream, hw]
  simp [Setup5.priorRep, Setup5.prior, hreplace]

theorem blockGate_trueBlock_of_step1Pass {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (hType : X.TypeOccurs K) (hPass : X.Step1Pass H.1) :
    X.blockGate H.1 K (X.trueBlock H.1 K) := by
  classical
  intro ℓ hℓ y
  have hrep := priorRep_trueBlock_eq_prior X H K ℓ (typeSegs_le_streamSegs X K)
  have hstep : ¬ ∃ y, Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n K)) *
        (X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w y < (X.prior H.1 ℓ).w y := by
    simpa [Setup5.step1Fail] using hPass.1 K hType ℓ hℓ
  apply le_of_not_gt
  intro hlt
  apply hstep
  refine ⟨y, ?_⟩
  rw [← hrep]
  exact hlt

theorem blockBase_le_exp_refBlock {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (z : X.Block K) :
    X.blockBase H.1 K z ≤
      Real.exp (X.p.a 0 * ((X.p.q0 : ℝ) * X.p.typeSegs n K)) *
        (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
  classical
  have hq : 0 < (X.p.q0 : ℝ) := by exact_mod_cast X.p.hq0.1
  have ha : 0 < X.p.a 0 := by rw [X.p.ha0]; norm_num
  have hexp : 1 ≤ Real.exp (X.p.a 0 * (X.p.q0 : ℝ)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hseg (s : Fin (X.p.typeSegs n K)) :
      (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z s) ≤
        Real.exp (X.p.a 0 * (X.p.q0 : ℝ)) * X.S.reference.w (z s) := by
    by_cases hp : X.S.paired H.1.1 (H.1.2.1 K.1.1)
    · simpa [Setup5.segLaw, hp] using
        X.S.segment_density H.1.1 (H.1.2.1 K.1.1) (z s) hp
    · simp [Setup5.segLaw, hp]
      calc
        X.S.reference.w (z s) = 1 * X.S.reference.w (z s) := by ring
        _ ≤ Real.exp (X.p.a 0 * (X.p.q0 : ℝ)) * X.S.reference.w (z s) :=
          mul_le_mul_of_nonneg_right hexp (X.S.reference.nonneg (z s))
  have hprod :
      (∏ s : Fin (X.p.typeSegs n K), (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z s)) ≤
        ∏ s : Fin (X.p.typeSegs n K),
          (Real.exp (X.p.a 0 * (X.p.q0 : ℝ)) * X.S.reference.w (z s)) := by
    apply Finset.prod_le_prod₀
    · intro s hs
      exact (X.segLaw H.1.1 (H.1.2.1 K.1.1)).nonneg (z s)
    · intro s hs
      exact hseg s
  unfold Setup5.blockBase at *
  calc
    (∏ s : Fin (X.p.typeSegs n K), (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z s)) ≤
        ∏ s : Fin (X.p.typeSegs n K),
          (Real.exp (X.p.a 0 * (X.p.q0 : ℝ)) * X.S.reference.w (z s)) := hprod
    _ = (Real.exp (X.p.a 0 * (X.p.q0 : ℝ))) ^ X.p.typeSegs n K *
          ∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = Real.exp (X.p.a 0 * ((X.p.q0 : ℝ) * X.p.typeSegs n K)) *
          ∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s) := by
      congr 1
      calc
        (Real.exp (X.p.a 0 * (X.p.q0 : ℝ))) ^ X.p.typeSegs n K =
            Real.exp ((X.p.typeSegs n K : ℝ) * (X.p.a 0 * (X.p.q0 : ℝ))) := by
              rw [← Real.exp_nat_mul]
        _ = Real.exp (X.p.a 0 * ((X.p.q0 : ℝ) * X.p.typeSegs n K)) := by
              congr 1 <;> push_cast <;> ring

theorem normalize5_weight_eq_div_of_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (ω₀ : Ω) (ω : Ω) (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < ∑ x, f x) :
    (normalize5 f ω₀).w ω = f ω / (∑ x, f x) := by
  classical
  have hsum : (∑ x, max 0 (f x)) = ∑ x, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact max_eq_right (hf x)
  simp [normalize5, hsum, hmass, hf ω]

theorem colLik_le_exp_of_blockGate {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (ℓ : X.Key) (z : X.Block K) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N)
    (hℓ : ℓ ∈ K.2.1) (hgate : X.blockGate H.1 K z) :
    X.colLik H.1 K ℓ z θ ≤
      Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ) := by
  classical
  let B := Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K))
  have hB : 0 ≤ B := Real.exp_nonneg _
  have hratio (h : Fin (colLen5 (X.p.s n) ℓ)) :
      ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (θ h))
          ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (θ h)) ≤ B := by
    apply ratio5_le_of_mul_le
    · exact (X.priorRep H.1 ℓ K.1.1 z).nonneg (θ h)
    · exact (X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).nonneg (θ h)
    · exact hB
    · exact hgate ℓ (Finset.mem_union_left _ hℓ) (θ h)
  unfold Setup5.colLik
  calc
    (∏ h : Fin (colLen5 (X.p.s n) ℓ),
        ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (θ h))
          ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (θ h))) ≤
      ∏ h : Fin (colLen5 (X.p.s n) ℓ), B := by
        apply Finset.prod_le_prod₀
        · intro h hh
          exact ratio5_nonneg
            ((X.priorRep H.1 ℓ K.1.1 z).nonneg (θ h))
            ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).nonneg (θ h))
        · intro h hh
          exact hratio h
    _ = B ^ colLen5 (X.p.s n) ℓ := by simp
    _ = Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          colLen5 (X.p.s n) ℓ) := by
        dsimp [B]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem blockWeight_le_exp_refBlock_of_blockGate {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (z : X.Block K)
    (hgate : X.blockGate H.1 K z) :
    X.blockWeight H K K.2.1 z ≤
      Real.exp (X.p.a 0 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) +
        X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          (∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))) *
        (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
  classical
  let qu : ℝ := (X.p.q0 : ℝ) * X.p.typeSegs n K
  let sev : ℝ := ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ)
  have hlik (ℓ : X.Key) (hℓ : ℓ ∈ K.2.1) :
      0 ≤ X.colLik H.1 K ℓ z (H.2 ℓ) := by
    unfold Setup5.colLik
    apply Finset.prod_nonneg
    intro h hh
    exact ratio5_nonneg
      ((X.priorRep H.1 ℓ K.1.1 z).nonneg (H.2 ℓ h))
      ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).nonneg (H.2 ℓ h))
  have hlikBound (ℓ : X.Key) (hℓ : ℓ ∈ K.2.1) :
      X.colLik H.1 K ℓ z (H.2 ℓ) ≤
        Real.exp (X.p.a 1 * qu * (colLen5 (X.p.s n) ℓ : ℝ)) := by
    simpa [qu] using colLik_le_exp_of_blockGate X H K ℓ z (H.2 ℓ) hℓ hgate
  have hprod :
      (∏ ℓ ∈ K.2.1, X.colLik H.1 K ℓ z (H.2 ℓ)) ≤ Real.exp (X.p.a 1 * qu * sev) := by
    calc
      (∏ ℓ ∈ K.2.1, X.colLik H.1 K ℓ z (H.2 ℓ)) ≤
          ∏ ℓ ∈ K.2.1, Real.exp (X.p.a 1 * qu * (colLen5 (X.p.s n) ℓ : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro ℓ hℓ
          exact hlik ℓ hℓ
        · intro ℓ hℓ
          exact hlikBound ℓ hℓ
      _ = Real.exp (∑ ℓ ∈ K.2.1,
            X.p.a 1 * qu * (colLen5 (X.p.s n) ℓ : ℝ)) := by
        rw [← Real.exp_sum]
      _ = Real.exp (X.p.a 1 * qu * sev) := by
        congr 1
        simp [sev, Finset.mul_sum]
  have hbase := blockBase_le_exp_refBlock X H K z
  have hprodNonneg : 0 ≤ ∏ ℓ ∈ K.2.1, X.colLik H.1 K ℓ z (H.2 ℓ) :=
    Finset.prod_nonneg fun ℓ hℓ => hlik ℓ hℓ
  have hrefNonneg : 0 ≤ ∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s) :=
    Finset.prod_nonneg fun s hs => X.S.reference.nonneg (z s)
  unfold Setup5.blockWeight
  by_cases hgate' : X.blockGate H.1 K z
  · simp only [if_pos hgate']
    calc
      X.blockBase H.1 K z * 1 *
          ∏ ℓ ∈ K.2.1, X.colLik H.1 K ℓ z (H.2 ℓ) ≤
        (Real.exp (X.p.a 0 * qu) *
          (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s))) *
          ∏ ℓ ∈ K.2.1, X.colLik H.1 K ℓ z (H.2 ℓ) := by
            exact mul_le_mul_of_nonneg_right (by simpa [qu] using hbase) hprodNonneg
      _ ≤ (Real.exp (X.p.a 0 * qu) *
          (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s))) *
            Real.exp (X.p.a 1 * qu * sev) :=
              mul_le_mul_of_nonneg_left hprod (mul_nonneg (Real.exp_nonneg _) hrefNonneg)
      _ = Real.exp (X.p.a 0 * qu + X.p.a 1 * qu * sev) *
          (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
            calc
              _ = Real.exp (X.p.a 0 * qu) * Real.exp (X.p.a 1 * qu * sev) *
                  (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by ring
              _ = _ := by rw [← Real.exp_add]
  · simp only [if_neg hgate', mul_zero, zero_mul]
    exact mul_nonneg (Real.exp_nonneg _) hrefNonneg

theorem blockWeight_le_exp_refBlock {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (z : X.Block K) :
    X.blockWeight H K K.2.1 z ≤
      Real.exp (X.p.a 0 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) +
        X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          (∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))) *
        (∏ s : Fin (X.p.typeSegs n K), X.S.reference.w (z s)) := by
  classical
  by_cases hgate : X.blockGate H.1 K z
  · exact blockWeight_le_exp_refBlock_of_blockGate X H K z hgate
  · unfold Setup5.blockWeight
    simp only [if_neg hgate, mul_zero, zero_mul]
    exact mul_nonneg (Real.exp_nonneg _)
      (Finset.prod_nonneg fun s hs => X.S.reference.nonneg (z s))

theorem blockWeight_withCol_le_of_blockGate {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N)
    (hℓ : ℓ ∈ K.2.1) (hgate : X.blockGate H.1 K z) :
    X.blockWeight (X.withCol H ℓ θ) K K.2.1 z ≤
      Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
        (colLen5 (X.p.s n) ℓ : ℝ)) *
        X.blockWeight H K (K.2.1.erase ℓ) z := by
  classical
  have hlikNonneg (k : X.Key) :
      0 ≤ X.colLik H.1 K k z (H.2 k) := by
    unfold Setup5.colLik
    apply Finset.prod_nonneg
    intro h hh
    exact ratio5_nonneg
      ((X.priorRep H.1 k K.1.1 z).nonneg (H.2 k h))
      ((X.priorDel H.1 k K.1.1 (X.p.typeSegs n K)).nonneg (H.2 k h))
  have hlik (k : X.Key) (hk : k ∈ K.2.1.erase ℓ) :
      X.colLik H.1 K k z (Function.update H.2 ℓ θ k) = X.colLik H.1 K k z (H.2 k) := by
    have hne : k ≠ ℓ := Finset.ne_of_mem_erase hk
    simp [Function.update_of_ne hne]
  have hlikAt : X.colLik H.1 K ℓ z (Function.update H.2 ℓ θ ℓ) =
      X.colLik H.1 K ℓ z θ := by
    simp [Function.update_self]
  have hprod :
      (∏ k ∈ K.2.1, X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) ≤
        Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          (colLen5 (X.p.s n) ℓ : ℝ)) *
          (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k)) := by
    calc
      (∏ k ∈ K.2.1, X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) =
          X.colLik H.1 K ℓ z (Function.update H.2 ℓ θ ℓ) *
            (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) := by
              rw [← Finset.mul_prod_erase K.2.1
                (fun k => X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) hℓ]
      _ = X.colLik H.1 K ℓ z θ *
            (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k)) := by
              rw [hlikAt]
              congr 1
              apply Finset.prod_congr rfl
              intro k hk
              exact hlik k hk
      _ ≤ Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
            (colLen5 (X.p.s n) ℓ : ℝ)) *
            (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k)) := by
              apply mul_le_mul_of_nonneg_right
              · exact colLik_le_exp_of_blockGate X H K ℓ z θ hℓ hgate
              · exact Finset.prod_nonneg fun k hk => hlikNonneg k
  have hbase : 0 ≤ X.blockBase H.1 K z := by
    unfold Setup5.blockBase
    exact Finset.prod_nonneg fun s hs =>
      (X.segLaw H.1.1 (H.1.2.1 K.1.1)).nonneg (z s)
  change
    (X.blockBase H.1 K z * (if X.blockGate H.1 K z then 1 else 0) *
      (∏ k ∈ K.2.1, X.colLik H.1 K k z (Function.update H.2 ℓ θ k))) ≤
    Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
      (colLen5 (X.p.s n) ℓ : ℝ)) *
      (X.blockBase H.1 K z * (if X.blockGate H.1 K z then 1 else 0) *
        (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k)))
  by_cases hg : X.blockGate H.1 K z
  · simp only [if_pos hg]
    calc
      X.blockBase H.1 K z * 1 *
          (∏ k ∈ K.2.1, X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) =
        X.blockBase H.1 K z *
          (∏ k ∈ K.2.1, X.colLik H.1 K k z (Function.update H.2 ℓ θ k)) := by ring
      _ ≤
        X.blockBase H.1 K z *
          (Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
            (colLen5 (X.p.s n) ℓ : ℝ)) *
            (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k))) := by
              exact mul_le_mul_of_nonneg_left hprod hbase
      _ = Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
            (colLen5 (X.p.s n) ℓ : ℝ)) *
          (X.blockBase H.1 K z * 1 *
            (∏ k ∈ K.2.1.erase ℓ, X.colLik H.1 K k z (H.2 k))) := by ring
  · simp [hg]

theorem blockWeight_withCol_le {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N)
    (hℓ : ℓ ∈ K.2.1) :
    X.blockWeight (X.withCol H ℓ θ) K K.2.1 z ≤
      Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
        (colLen5 (X.p.s n) ℓ : ℝ)) *
        X.blockWeight H K (K.2.1.erase ℓ) z := by
  classical
  by_cases hgate : X.blockGate H.1 K z
  · exact blockWeight_withCol_le_of_blockGate X H K ℓ z θ hℓ hgate
  · simp [Setup5.blockWeight, Setup5.withCol, hgate]

theorem blockMass_withCol_le {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1) :
    X.blockMass (X.withCol H ℓ θ) K K.2.1 ≤
      Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
        (colLen5 (X.p.s n) ℓ : ℝ)) *
        X.blockMass H K (K.2.1.erase ℓ) := by
  classical
  unfold Setup5.blockMass
  calc
    (∑ z, X.blockWeight (X.withCol H ℓ θ) K K.2.1 z) ≤
        ∑ z, Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          (colLen5 (X.p.s n) ℓ : ℝ)) * X.blockWeight H K (K.2.1.erase ℓ) z :=
      Finset.sum_le_sum fun z hz => blockWeight_withCol_le X H K ℓ z θ hℓ
    _ = Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
        (colLen5 (X.p.s n) ℓ : ℝ)) *
        (∑ z, X.blockWeight H K (K.2.1.erase ℓ) z) := by
          rw [← Finset.mul_sum]

end HypercubeRamsey.Lane_q_s05_hist1b
