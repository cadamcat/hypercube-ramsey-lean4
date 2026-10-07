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

theorem base_segment_supported {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hb : X.baseLaw.w b ≠ 0) (w : BinVector5 n) (s : Fin (X.p.streamSegs n)) :
    (X.segLaw b.1 (b.2.1 w)).w (b.2.2 w s) ≠ 0 := by
  classical
  have hc : (X.coarseLaw b.1).w b.2 ≠ 0 := by
    have hprod : X.P.prior.parent.w b.1 * (X.coarseLaw b.1).w b.2 ≠ 0 := by
      simpa [Setup5.baseLaw, FinProb.bind] using hb
    exact (mul_ne_zero_iff.mp hprod).2
  have hprod :
      (∏ w' : BinVector5 n, (X.P.prior.partner b.1 w').w (b.2.1 w')) *
        (∏ w' : BinVector5 n, ∏ s' : Fin (X.p.streamSegs n),
          (X.segLaw b.1 (b.2.1 w')).w (b.2.2 w' s')) ≠ 0 := by
    simpa [Setup5.coarseLaw, FinProb.bind, FinProb.pi] using hc
  have hstream :
      ∏ w' : BinVector5 n, ∏ s' : Fin (X.p.streamSegs n),
        (X.segLaw b.1 (b.2.1 w')).w (b.2.2 w' s') ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).2
  have hw := (Finset.prod_ne_zero_iff.mp hstream) w (Finset.mem_univ _)
  exact (Finset.prod_ne_zero_iff.mp hw) s (Finset.mem_univ _)

theorem blockBase_segment_supported {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (z : X.Block K) (h : X.blockBase H.1 K z ≠ 0) (s : Fin (X.p.typeSegs n K)) :
    (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z s) ≠ 0 := by
  classical
  have hp : ∏ s' : Fin (X.p.typeSegs n K),
      (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z s') ≠ 0 := by
    simpa [Setup5.blockBase] using h
  exact (Finset.prod_ne_zero_iff.mp hp) s (Finset.mem_univ _)

theorem replaced_stream_segment_supported {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (z : X.Block K)
    (hb : X.baseLaw.w H.1 ≠ 0) (hblock : X.blockBase H.1 K z ≠ 0)
    (w : BinVector5 n) (s : Fin (X.p.streamSegs n)) :
    (X.segLaw H.1.1 (H.1.2.1 w)).w
      ((X.replaceStream H.1.2.2 K.1.1 z) w s) ≠ 0 := by
  classical
  by_cases hw : w = K.1.1
  · subst w
    by_cases hs : (s : ℕ) < X.p.typeSegs n K
    · have hk := typeSegs_le_streamSegs X K
      have hs' : (s : ℕ) < X.p.streamSegs n := hs.trans_le hk
      have hz : (X.segLaw H.1.1 (H.1.2.1 K.1.1)).w (z ⟨s, hs⟩) ≠ 0 :=
        blockBase_segment_supported X H K z hblock ⟨s, hs⟩
      simpa [Setup5.replaceStream, Function.update_self, hs, hs'] using hz
    · simpa [Setup5.replaceStream, Function.update_self, hs] using
        base_segment_supported X H.1 hb K.1.1 s
  · simpa [Setup5.replaceStream, Function.update_of_ne hw] using
      base_segment_supported X H.1 hb w s

theorem base_parent_supported {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hb : X.baseLaw.w b ≠ 0) : X.P.prior.parent.w b.1 ≠ 0 := by
  have hprod : X.P.prior.parent.w b.1 * (X.coarseLaw b.1).w b.2 ≠ 0 := by
    simpa [Setup5.baseLaw, FinProb.bind] using hb
  exact (mul_ne_zero_iff.mp hprod).1

theorem base_partner_supported {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (hb : X.baseLaw.w b ≠ 0) (w : BinVector5 n) :
    (X.P.prior.partner b.1 w).w (b.2.1 w) ≠ 0 := by
  classical
  have hc : (X.coarseLaw b.1).w b.2 ≠ 0 := by
    have hprod : X.P.prior.parent.w b.1 * (X.coarseLaw b.1).w b.2 ≠ 0 := by
      simpa [Setup5.baseLaw, FinProb.bind] using hb
    exact (mul_ne_zero_iff.mp hprod).2
  have hprod :
      (∏ w' : BinVector5 n, (X.P.prior.partner b.1 w').w (b.2.1 w')) *
        (∏ w' : BinVector5 n, ∏ s' : Fin (X.p.streamSegs n),
          (X.segLaw b.1 (b.2.1 w')).w (b.2.2 w' s')) ≠ 0 := by
    simpa [Setup5.coarseLaw, FinProb.bind, FinProb.pi] using hc
  have hpartners :
      ∏ w' : BinVector5 n, (X.P.prior.partner b.1 w').w (b.2.1 w') ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).1
  exact (Finset.prod_ne_zero_iff.mp hpartners) w (Finset.mem_univ _)

theorem colWeight_replaced_candidate_pos5 {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (hbase : X.baseLaw.w H.1 ≠ 0)
    (hblock : X.blockBase H.1 K z ≠ 0)
    (hcover : K.1.1 ∈ binList5 ℓ.coarse) :
    0 < X.colWeight H.1 ℓ (X.replaceStream H.1.2.2 K.1.1 z)
      (fun _ _ => True) (if ℓ.coarse.2 then H.1.1 else H.1.2.1 ℓ.coarse.1) := by
  classical
  let k := X.p.uSeg n (ℓ.level + 1)
  by_cases hbnd : ℓ.coarse.2
  · have hparentNe := base_parent_supported X H.1 hbase
    have hparentPos : 0 < X.P.prior.parent.w H.1.1 :=
      lt_of_le_of_ne (X.P.prior.parent.nonneg _) (Ne.symm hparentNe)
    have hpartnerPos (w : BinVector5 n) :
        0 < (X.P.prior.partner H.1.1 w).w (H.1.2.1 w) :=
      lt_of_le_of_ne ((X.P.prior.partner H.1.1 w).nonneg _) (Ne.symm (base_partner_supported X H.1 hbase w))
    have hlikPos (w : BinVector5 n) :
        0 < ∏ s : Fin (X.p.streamSegs n),
          if (s : ℕ) < k then
            (X.segLaw H.1.1 (H.1.2.1 w)).w
              ((X.replaceStream H.1.2.2 K.1.1 z) w s)
          else 1 := by
      apply Finset.prod_pos
      intro s hs
      by_cases hs' : (s : ℕ) < k
      · simp [hs']
        have hne := replaced_stream_segment_supported X H K z hbase hblock w s
        have hnonneg := (X.segLaw H.1.1 (H.1.2.1 w)).nonneg
          ((X.replaceStream H.1.2.2 K.1.1 z) w s)
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      · simp [hs']
    have houter : 0 < ∏ w' ∈ binList5 ℓ.coarse,
        (X.P.prior.partner H.1.1 w').w (H.1.2.1 w') *
          (∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < k then
            (X.segLaw H.1.1 (H.1.2.1 w')).w
              ((X.replaceStream H.1.2.2 K.1.1 z) w' s) else 1) := by
      apply Finset.prod_pos
      intro w' hw'
      exact mul_pos (hpartnerPos w') (hlikPos w')
    have hweight : 0 < X.P.prior.parent.w H.1.1 *
        ∏ w' ∈ binList5 ℓ.coarse,
          (X.P.prior.partner H.1.1 w').w (H.1.2.1 w') *
            (∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < k then
              (X.segLaw H.1.1 (H.1.2.1 w')).w
                ((X.replaceStream H.1.2.2 K.1.1 z) w' s) else 1) :=
      mul_pos hparentPos houter
    simpa [Setup5.colWeight, hbnd, k] using hweight
  · have hfalse : ℓ.coarse.2 = false := by
      cases h : ℓ.coarse.2 <;> simp_all
    have hbin : K.1.1 = ℓ.coarse.1 := by
      simpa [binList5, hfalse] using hcover
    have hpartnerNe := base_partner_supported X H.1 hbase ℓ.coarse.1
    have hpartnerPos : 0 <
        (X.P.prior.partner H.1.1 ℓ.coarse.1).w (H.1.2.1 ℓ.coarse.1) :=
      lt_of_le_of_ne ((X.P.prior.partner H.1.1 ℓ.coarse.1).nonneg _) (Ne.symm hpartnerNe)
    have hlikPos :
        0 < ∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < k then
          (X.segLaw H.1.1 (H.1.2.1 ℓ.coarse.1)).w
            ((X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 s)
        else 1 := by
      apply Finset.prod_pos
      intro s hs
      by_cases hs' : (s : ℕ) < k
      · simp [hs']
        have hne := replaced_stream_segment_supported X H K z hbase hblock ℓ.coarse.1 s
        have hnonneg := (X.segLaw H.1.1 (H.1.2.1 ℓ.coarse.1)).nonneg
          ((X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 s)
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      · simp [hs']
    have hweight : 0 < (X.P.prior.partner H.1.1 ℓ.coarse.1).w
        (H.1.2.1 ℓ.coarse.1) *
        ∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < k then
          (X.segLaw H.1.1 (H.1.2.1 ℓ.coarse.1)).w
            ((X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 s)
        else 1 := mul_pos hpartnerPos hlikPos
    simpa [Setup5.colWeight, hfalse, k] using hweight

theorem priorRep_raw_nonzero5 {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (hbase : X.baseLaw.w H.1 ≠ 0) (hblock : X.blockBase H.1 K z ≠ 0)
    (hcover : K.1.1 ∈ binList5 ℓ.coarse) (y : Fin N)
    (hrep : (X.priorRep H.1 ℓ K.1.1 z).w y ≠ 0) :
    X.colWeight H.1 ℓ (X.replaceStream H.1.2.2 K.1.1 z)
      (fun _ _ => True) y ≠ 0 := by
  classical
  let f : Fin N → ℝ := fun y =>
    X.colWeight H.1 ℓ (X.replaceStream H.1.2.2 K.1.1 z) (fun _ _ => True) y
  let y' : Fin N := if ℓ.coarse.2 then H.1.1 else H.1.2.1 ℓ.coarse.1
  have hfpos : 0 < f y' := by
    simpa [f, y'] using
      colWeight_replaced_candidate_pos5 X H K ℓ z hbase hblock hcover
  have hterm : 0 < max 0 (f y') := lt_of_lt_of_le hfpos (le_max_right _ _)
  have hsumge : max 0 (f y') ≤ ∑ y, max 0 (f y) :=
    Finset.single_le_sum (fun y _ => le_max_left _ _) (Finset.mem_univ y')
  have hsum : 0 < ∑ y, max 0 (f y) := lt_of_lt_of_le hterm hsumge
  have hnorm : (X.priorRep H.1 ℓ K.1.1 z).w y =
      max 0 (f y) / (∑ y', max 0 (f y')) := by
    simp [Setup5.priorRep, normalize5, f, hsum]
  have hdiv : max 0 (f y) / (∑ y', max 0 (f y')) ≠ 0 := by
    rw [← hnorm]
    exact hrep
  intro hzero
  have hzero' : f y = 0 := by simpa [f] using hzero
  apply hdiv
  simp [hzero']

theorem posterior_boundary_segment_nonzero5 {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (y : Fin N)
    (hprefix : X.p.typeSegs n K ≤ X.p.uSeg n (ℓ.level + 1))
    (hcover : K.1.1 ∈ binList5 ℓ.coarse) (hbnd : ℓ.coarse.2 = true)
    (hraw : X.colWeight H.1 ℓ (X.replaceStream H.1.2.2 K.1.1 z)
      (fun _ _ => True) y ≠ 0) (s : Fin (X.p.typeSegs n K)) :
    (X.segLaw y (H.1.2.1 K.1.1)).w (z s) ≠ 0 := by
  classical
  have hkey : (s : ℕ) < X.p.uSeg n (ℓ.level + 1) := lt_of_lt_of_le s.isLt hprefix
  have hstream : (s : ℕ) < X.p.streamSegs n :=
    lt_of_lt_of_le s.isLt (typeSegs_le_streamSegs X K)
  have hraw' := hraw
  simp [Setup5.colWeight, hbnd] at hraw'
  have houter : ∏ w' ∈ binList5 ℓ.coarse,
      (X.P.prior.partner y w').w (H.1.2.1 w') *
        (∏ s' : Fin (X.p.streamSegs n), if (s' : ℕ) < X.p.uSeg n (ℓ.level + 1) then
          (X.segLaw y (H.1.2.1 w')).w
            ((X.replaceStream H.1.2.2 K.1.1 z) w' s') else 1) ≠ 0 :=
    hraw'.2
  have hterm := (Finset.prod_ne_zero_iff.mp houter) K.1.1 hcover
  have hlik : (∏ s' : Fin (X.p.streamSegs n), if (s' : ℕ) < X.p.uSeg n (ℓ.level + 1) then
      (X.segLaw y (H.1.2.1 K.1.1)).w
        ((X.replaceStream H.1.2.2 K.1.1 z) K.1.1 s') else 1) ≠ 0 :=
    (mul_ne_zero_iff.mp hterm).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hlik) ⟨s, hstream⟩ (Finset.mem_univ _)
  have hfactor' : (X.segLaw y (H.1.2.1 K.1.1)).w
      ((X.replaceStream H.1.2.2 K.1.1 z) K.1.1 ⟨s, hstream⟩) ≠ 0 := by
    simpa [hkey] using hfactor
  have hword : (X.replaceStream H.1.2.2 K.1.1 z) K.1.1 ⟨s, hstream⟩ = z s := by
    simp [Setup5.replaceStream, Function.update_self, hstream, s.isLt]
  simpa [hword] using hfactor'

theorem posterior_interior_segment_nonzero5 {γ K' χ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (z : X.Block K) (y : Fin N)
    (hprefix : X.p.typeSegs n K ≤ X.p.uSeg n (ℓ.level + 1))
    (hcover : K.1.1 ∈ binList5 ℓ.coarse) (hbnd : ℓ.coarse.2 = false)
    (hraw : X.colWeight H.1 ℓ (X.replaceStream H.1.2.2 K.1.1 z)
      (fun _ _ => True) y ≠ 0) (s : Fin (X.p.typeSegs n K)) :
    (X.segLaw H.1.1 y).w (z s) ≠ 0 := by
  classical
  have hbin : K.1.1 = ℓ.coarse.1 := by
    simpa [binList5, hbnd] using hcover
  have hkey : (s : ℕ) < X.p.uSeg n (ℓ.level + 1) := lt_of_lt_of_le s.isLt hprefix
  have hstream : (s : ℕ) < X.p.streamSegs n :=
    lt_of_lt_of_le s.isLt (typeSegs_le_streamSegs X K)
  have hraw' := hraw
  simp [Setup5.colWeight, hbnd] at hraw'
  have hlik : (∏ s' : Fin (X.p.streamSegs n), if (s' : ℕ) < X.p.uSeg n (ℓ.level + 1) then
      (X.segLaw H.1.1 y).w
        ((X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 s') else 1) ≠ 0 :=
    hraw'.2
  have hfactor := (Finset.prod_ne_zero_iff.mp hlik) ⟨s, hstream⟩ (Finset.mem_univ _)
  have hfactor' : (X.segLaw H.1.1 y).w
      ((X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 ⟨s, hstream⟩) ≠ 0 := by
    simpa [hkey] using hfactor
  have hword : (X.replaceStream H.1.2.2 K.1.1 z) ℓ.coarse.1 ⟨s, hstream⟩ = z s := by
    rw [← hbin]
    simp [Setup5.replaceStream, Function.update_self, hstream, s.isLt]
  simpa [hword] using hfactor'

theorem uSeg_mono5 {γ K' χ : ℝ} (p : Params5 γ K' χ) (n a b : ℕ) (hab : a ≤ b) :
    p.uSeg n a ≤ p.uSeg n b := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := by
    by_cases hm : p.m n = 0
    · simp [hm]
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hcoef : 0 ≤ p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ) :=
    div_nonneg (mul_nonneg p.hK1.le hlog) (by exact_mod_cast p.hq0.1.le)
  have hlinear : (a : ℝ) + 4 ≤ (b : ℝ) + 4 := by
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hraw : p.K1 * ((a : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
      p.K1 * ((b : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ) := by
    calc
      _ = ((a : ℝ) + 4) * (p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by ring
      _ ≤ ((b : ℝ) + 4) * (p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) :=
        mul_le_mul_of_nonneg_right hlinear hcoef
      _ = _ := by ring
  simpa [Params5.uSeg] using Nat.ceil_mono hraw

theorem uStarSeg_le_uSeg_high5 {γ K' χ : ℝ} (p : Params5 γ K' χ) (n : ℕ) :
    p.uStarSeg n ≤ p.uSeg n (p.J n + 1) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := by
    by_cases hm : p.m n = 0
    · simp [hm]
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  have hcoef : 0 ≤ p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ) :=
    div_nonneg (mul_nonneg p.hK1.le hlog) hq.le
  have hlogdiv : 0 ≤ Real.log (p.m n : ℝ) / (p.q0 : ℝ) := div_nonneg hlog hq.le
  have hlinear : 1 ≤ ((p.J n + 1 : ℕ) : ℝ) + 4 := by
    have hJ : 0 ≤ ((p.J n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hraw : p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
      p.K1 * (((p.J n + 1 : ℕ) : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ) := by
    calc
      _ = p.eta * (Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by ring
      _ ≤ p.K1 * (Real.log (p.m n : ℝ) / (p.q0 : ℝ)) :=
        mul_le_mul_of_nonneg_right p.hK1_eta hlogdiv
      _ = 1 * (p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by ring
      _ ≤ (((p.J n + 1 : ℕ) : ℝ) + 4) *
          (p.K1 * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) :=
        mul_le_mul_of_nonneg_right hlinear hcoef
      _ = _ := by ring
  simpa [Params5.uStarSeg, Params5.uSeg] using Nat.ceil_mono hraw

theorem typeSegs_le_keyPrefix5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (K : X.Ty)
    (hType : X.TypeOccurs K) (ℓ : X.Key) (hℓ : ℓ ∈ K.2.1) :
    X.p.typeSegs n K ≤ X.p.uSeg n (ℓ.level + 1) := by
  classical
  rcases hType with ⟨x, hx, hK⟩
  subst K
  let j := X.g.severity x
  have hkeys : ℓ ∈ X.g.typeKeys (X.p.J n) x := by
    simpa [ChunkGeometry5.evenType] using hℓ
  by_cases hlow : X.g.severity x ≤ X.p.J n
  · have htypeSeg : X.p.typeSegs n (X.g.evenType (X.p.J n) x) = X.p.uSeg n j := by
      simp [Params5.typeSegs, ChunkGeometry5.evenType, j, hlow]
    have hmem := hkeys
    simp only [ChunkGeometry5.typeKeys, if_pos hlow, Finset.mem_union,
      Finset.mem_image] at hmem
    have hlevel : j ≤ ℓ.level + 1 := by
      rcases hmem with (hfirst | hsecond) | hthird
      · rcases hfirst with ⟨i, hi, heq⟩
        have hlev := congrArg HiddenKey5.level heq
        have hlev' : j = ℓ.level := by
          simpa [keyAt5, HiddenKey5.level, j, hlow] using hlev
        omega
      · rcases hsecond with ⟨i, hi, heq⟩
        have hlev := congrArg HiddenKey5.level heq
        have hlev' : j = ℓ.level := by
          simpa [keyAt5, HiddenKey5.level, j, hlow] using hlev
        omega
      · rcases hthird with ⟨j', hj', heq⟩
        have hchoices : j' = j + 1 ∨ (0 < j ∧ j' = j - 1) := by
          simp only [Finset.mem_singleton] at hj'
          change (j' = j + 1) ∨ j' ∈
            (if 0 < j then ({j - 1} : Finset ℕ) else ∅) at hj'
          by_cases hj : 0 < j
          · simp only [if_pos hj, Finset.mem_singleton] at hj'
            rcases hj' with h | h
            · exact Or.inl h
            · exact Or.inr ⟨hj, h⟩
          · simp only [if_neg hj, Finset.notMem_empty, or_false] at hj'
            exact Or.inl hj'
        have hlev := congrArg HiddenKey5.level heq
        rcases hchoices with hj' | ⟨hjpos, hj'⟩
        · by_cases hjle : j' ≤ X.p.J n
          · have hlev'' : j' = ℓ.level := by
              simpa [keyAt5, HiddenKey5.level, hjle] using hlev
            omega
          · have hlev'' : X.p.J n = ℓ.level := by
              simpa [keyAt5, HiddenKey5.level, hjle] using hlev
            omega
        · have hjle : j' ≤ X.p.J n := by omega
          have hlev'' : j' = ℓ.level := by
            simpa [keyAt5, HiddenKey5.level, hjle] using hlev
          omega
    rw [htypeSeg]
    exact uSeg_mono5 X.p n j (ℓ.level + 1) hlevel
  · have htypeSeg : X.p.typeSegs n (X.g.evenType (X.p.J n) x) = X.p.uStarSeg n := by
      simp [Params5.typeSegs, ChunkGeometry5.evenType, hlow]
    have hmem : ℓ ∈ Finset.image (fun i : CoarseKey5 n => (.inr i : X.Key))
        (X.g.coarseRange x) := by
      simpa [ChunkGeometry5.typeKeys, hlow] using hkeys
    rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
    have hlev := congrArg HiddenKey5.level heq
    have hlevel : ℓ.level = X.p.J n := by
      simpa [HiddenKey5.level] using hlev.symm
    rw [htypeSeg]
    rw [hlevel]
    exact uStarSeg_le_uSeg_high5 X.p n

theorem finite_subdensity_lower_bad5 {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FinProb Ω) (Q : FinProb Ξ) (L : Ω → Ξ → ℝ) (gate : Ω → Prop)
    (m : Ξ → ℝ) (ε : ℝ)
    (hm : ∀ x, m x = ∑ ω, if gate ω then P.w ω * L ω x else 0)
    (hε : 0 ≤ ε) :
    ∑ ω, ∑ x, (if gate ω ∧ (m x < ε) then P.w ω * Q.w x * L ω x else 0) ≤ ε := by
  classical
  let bad : Ξ → ℝ := fun x => ∑ ω,
    (if gate ω ∧ (m x < ε) then P.w ω * L ω x else 0)
  have hbad (x : Ξ) : bad x ≤ ε := by
    by_cases hmx : m x < ε
    · have heq : bad x = m x := by
        calc
          bad x = ∑ ω, if gate ω then P.w ω * L ω x else 0 := by
            dsimp [bad]
            apply Finset.sum_congr rfl
            intro ω hω
            simp [hmx]
          _ = m x := (hm x).symm
      rw [heq]
      exact le_of_lt hmx
    · have hzero : bad x = 0 := by
        simp [bad, hmx]
      rw [hzero]
      exact hε
  have hinner (x : Ξ) :
      (∑ ω, if gate ω ∧ (m x < ε) then P.w ω * Q.w x * L ω x else 0) =
        Q.w x * bad x := by
    calc
      _ = ∑ ω, Q.w x * (if gate ω ∧ (m x < ε) then P.w ω * L ω x else 0) := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hcond : gate ω ∧ m x < ε <;> simp [hcond] <;> ring
      _ = Q.w x * bad x := by
        dsimp [bad]
        rw [← Finset.mul_sum]
  have hswap :
      (∑ ω, ∑ x, if gate ω ∧ (m x < ε) then P.w ω * Q.w x * L ω x else 0) =
        ∑ x, ∑ ω, if gate ω ∧ (m x < ε) then P.w ω * Q.w x * L ω x else 0 := by
    rw [Finset.sum_comm]
  calc
    _ = ∑ x, ∑ ω, if gate ω ∧ (m x < ε) then P.w ω * Q.w x * L ω x else 0 := hswap
    _ = ∑ x, Q.w x * bad x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hinner x
    _ ≤ ∑ x, Q.w x * ε := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hbad x) (Q.nonneg x)
    _ = ε := by
      rw [← Finset.sum_mul, Q.sum_eq_one]
      ring

theorem finite_subdensity_ratio_bad5 {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FinProb Ω) (Q : FinProb Ξ) (L : Ω → Ξ → ℝ) (gate : Ω → Prop)
    (m d : Ξ → ℝ) (ε : ℝ)
    (hm : ∀ x, m x = ∑ ω, if gate ω then P.w ω * L ω x else 0)
    (hd : ∀ x, 0 ≤ d x)
    (hDel : ∑ x, Q.w x * d x ≤ 1)
    (hε : 0 ≤ ε) :
    ∑ ω, ∑ x, (if gate ω ∧ (m x < ε * d x) then P.w ω * Q.w x * L ω x else 0) ≤ ε := by
  classical
  let bad : Ξ → ℝ := fun x => ∑ ω,
    (if gate ω ∧ (m x < ε * d x) then P.w ω * L ω x else 0)
  have hbad (x : Ξ) : bad x ≤ ε * d x := by
    by_cases hmx : m x < ε * d x
    · have heq : bad x = m x := by
        calc
          bad x = ∑ ω, if gate ω then P.w ω * L ω x else 0 := by
            dsimp [bad]
            apply Finset.sum_congr rfl
            intro ω hω
            simp [hmx]
          _ = m x := (hm x).symm
      rw [heq]
      exact le_of_lt hmx
    · have hzero : bad x = 0 := by
        simp [bad, hmx]
      rw [hzero]
      exact mul_nonneg hε (hd x)
  have hinner (x : Ξ) :
      (∑ ω, if gate ω ∧ (m x < ε * d x) then P.w ω * Q.w x * L ω x else 0) =
        Q.w x * bad x := by
    calc
      _ = ∑ ω, Q.w x * (if gate ω ∧ (m x < ε * d x) then P.w ω * L ω x else 0) := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hcond : gate ω ∧ m x < ε * d x <;> simp [hcond] <;> ring
      _ = Q.w x * bad x := by
        dsimp [bad]
        rw [← Finset.mul_sum]
  have hswap :
      (∑ ω, ∑ x, if gate ω ∧ (m x < ε * d x) then P.w ω * Q.w x * L ω x else 0) =
        ∑ x, ∑ ω, if gate ω ∧ (m x < ε * d x) then P.w ω * Q.w x * L ω x else 0 := by
    rw [Finset.sum_comm]
  calc
    _ = ∑ x, ∑ ω, if gate ω ∧ (m x < ε * d x) then P.w ω * Q.w x * L ω x else 0 := hswap
    _ = ∑ x, Q.w x * bad x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hinner x
    _ ≤ ε * ∑ x, Q.w x * d x := by
      calc
        _ ≤ ∑ x, Q.w x * (ε * d x) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hbad x) (Q.nonneg x)
        _ = ε * ∑ x, Q.w x * d x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hDel hε
    _ = ε := by ring

end HypercubeRamsey.Lane_q_s05_hist1b
