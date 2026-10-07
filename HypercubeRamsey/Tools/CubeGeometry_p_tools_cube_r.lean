import Mathlib
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey
namespace CubeGeometryPToolsCubeR

open Finset
open scoped BigOperators

def samples (d s : ℕ) : Finset (Finset (Fin d)) := Finset.univ.powersetCard s

lemma samples_card (d s : ℕ) : (samples d s).card = Nat.choose d s := by
  simp [samples]

lemma samples_nonempty {d s : ℕ} (hsd : s ≤ d) : (samples d s).Nonempty := by
  rw [samples, Finset.powersetCard_nonempty]
  simpa using hsd

noncomputable def sampleLaw (d s : ℕ) (hsd : s ≤ d) : FinProb (Finset (Fin d)) where
  w B := if B ∈ samples d s then (Nat.choose d s : ℝ)⁻¹ else 0
  nonneg B := by split_ifs <;> positivity
  sum_eq_one := by
    classical
    have hchoose : (Nat.choose d s : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hsd).ne'
    calc
      (∑ B, if B ∈ samples d s then (Nat.choose d s : ℝ)⁻¹ else 0) =
          ∑ B ∈ samples d s, (Nat.choose d s : ℝ)⁻¹ := by
        rw [← Finset.sum_filter]
        <;> simp
      _ = (samples d s).card * (Nat.choose d s : ℝ)⁻¹ := by simp
      _ = 1 := by rw [samples_card]; field_simp

def intersectionWeight {d : ℕ} (A : Finset (Fin d)) (B : Finset (Fin d)) : ℕ :=
  (A ∩ B).card

lemma choose_ratio_le_pow {K d j : ℕ} (hKd : K ≤ d) (hd : 0 < d) :
    (Nat.choose K j : ℝ) / Nat.choose d j ≤ ((K : ℝ) / d) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hjK : j + 1 ≤ K
      · have hj : j ≤ K := by omega
        have hjd : j ≤ d := hj.trans hKd
        have hKrecNat := Nat.choose_succ_right_eq K j
        have hdrecNat := Nat.choose_succ_right_eq d j
        have hKrec : (Nat.choose K (j + 1) : ℝ) * (j + 1) =
            (Nat.choose K j : ℝ) * (K - j) := by exact_mod_cast hKrecNat
        have hdrec : (Nat.choose d (j + 1) : ℝ) * (j + 1) =
            (Nat.choose d j : ℝ) * (d - j) := by exact_mod_cast hdrecNat
        have hj1 : (0 : ℝ) < j + 1 := by positivity
        have hjlt : j < d := lt_of_lt_of_le
          (lt_of_lt_of_le (Nat.lt_succ_self j) hjK) hKd
        have hdj : (0 : ℝ) < d - j := by exact_mod_cast (Nat.sub_pos_of_lt hjlt)
        have hDpos : (0 : ℝ) < (Nat.choose d (j + 1) : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega)
        have hDpos0 : (0 : ℝ) < (Nat.choose d j : ℝ) := by
          exact_mod_cast Nat.choose_pos hjd
        have hquot :
            (Nat.choose K (j + 1) : ℝ) / Nat.choose d (j + 1) =
              ((Nat.choose K j : ℝ) * (K - j)) /
                ((Nat.choose d j : ℝ) * (d - j)) := by
          apply (div_eq_div_iff hDpos.ne' (mul_ne_zero hDpos0.ne' hdj.ne')).2
          calc
            (Nat.choose K (j + 1) : ℝ) * ((Nat.choose d j : ℝ) * (d - j)) =
                (Nat.choose K (j + 1) : ℝ) * (Nat.choose d (j + 1) * (j + 1)) := by
                  rw [← hdrec]
            _ = ((Nat.choose K (j + 1) : ℝ) * (j + 1)) * Nat.choose d (j + 1) := by ring
            _ = (Nat.choose K j : ℝ) * (K - j) * Nat.choose d (j + 1) := by rw [hKrec]
        have hstep :
            (Nat.choose K (j + 1) : ℝ) / Nat.choose d (j + 1) =
              ((Nat.choose K j : ℝ) / Nat.choose d j) * ((K - j : ℕ) / (d - j : ℕ)) := by
          calc
            _ = ((Nat.choose K j : ℝ) * (K - j)) /
                ((Nat.choose d j : ℝ) * (d - j)) := hquot
            _ = _ := by
              rw [Nat.cast_sub hj, Nat.cast_sub hjd]
              rw [div_mul_div_comm]
        have hfactor : ((K - j : ℕ) : ℝ) / (d - j : ℕ) ≤ (K : ℝ) / d := by
          have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
          have hKsub : ((K - j : ℕ) : ℝ) = (K : ℝ) - (j : ℝ) := by
            exact Nat.cast_sub hj
          have hdsub : ((d - j : ℕ) : ℝ) = (d : ℝ) - (j : ℝ) := by
            exact Nat.cast_sub hjd
          rw [hKsub, hdsub]
          apply (div_le_div_iff₀ hdj hdReal).2
          have hjKcast : (j : ℝ) ≤ K := by exact_mod_cast hj
          have hKdcast : (K : ℝ) ≤ d := by exact_mod_cast hKd
          have hjdcast : (j : ℝ) ≤ d := by exact_mod_cast hjd
          have hprod : 0 ≤ ((d : ℝ) - K) * j :=
            mul_nonneg (sub_nonneg.mpr hKdcast) (by positivity)
          nlinarith [hprod]
        calc
          (Nat.choose K (j + 1) : ℝ) / Nat.choose d (j + 1) =
              ((Nat.choose K j : ℝ) / Nat.choose d j) * ((K - j : ℕ) / (d - j : ℕ)) := hstep
          _ ≤ ((K : ℝ) / d) ^ j * ((K : ℝ) / d) :=
            mul_le_mul ih hfactor (by positivity) (by positivity)
          _ = ((K : ℝ) / d) ^ (j + 1) := by rw [pow_succ]
      · have hzero : Nat.choose K (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
        have hp : (0 : ℝ) ≤ (K : ℝ) / d := div_nonneg (Nat.cast_nonneg K) hdReal.le
        simpa [hzero] using (pow_nonneg hp (j + 1))

lemma factorialMomentSum {d s j : ℕ} (A : Finset (Fin d))
    (hsd : s ≤ d) (hjs : j ≤ s) :
    (∑ B ∈ samples d s, Nat.choose (intersectionWeight A B) j) =
      Nat.choose A.card j * Nat.choose (d - j) (s - j) := by
  classical
  have hsubsets (B : Finset (Fin d)) :
      (A ∩ B).powersetCard j = (A.powersetCard j).filter (fun J => J ⊆ B) := by
    ext J
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_inter_iff]
    constructor
    · rintro ⟨⟨hJA,hJB⟩,hcard⟩
      exact ⟨⟨hJA,hcard⟩,hJB⟩
    · rintro ⟨⟨hJA,hcard⟩,hJB⟩
      exact ⟨⟨hJA,hJB⟩,hcard⟩
  calc
    _ = ∑ B ∈ samples d s, ((A ∩ B).powersetCard j).card := by
      apply Finset.sum_congr rfl
      intro B hB
      simp [intersectionWeight]
    _ = ∑ B ∈ samples d s, ∑ J ∈ A.powersetCard j, if J ⊆ B then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hsubsets B, Finset.card_filter]
    _ = ∑ J ∈ A.powersetCard j, ∑ B ∈ samples d s, if J ⊆ B then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ J ∈ A.powersetCard j,
          ((samples d s).filter fun B => J ⊆ B).card := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [Finset.card_filter]
    _ = Nat.choose A.card j * Nat.choose (d - j) (s - j) := by
      have hJcount : (A.powersetCard j).card = Nat.choose A.card j := by
        rw [Finset.card_powersetCard]
      have hfixed (J : Finset (Fin d)) (hJ : J ∈ A.powersetCard j) :
          ((samples d s).filter fun B => J ⊆ B).card = Nat.choose (d - j) (s - j) := by
        have hjcard : J.card = j := (Finset.mem_powersetCard.mp hJ).2
        rw [samples, Finset.card_filter_powersetCard_subset]
        · simp [Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp hJ).2]
        · exact (Finset.mem_powersetCard.mp hJ).1.trans (Finset.subset_univ A)
        · simpa [hjcard] using hjs
      calc
        _ = ∑ J ∈ A.powersetCard j, Nat.choose (d - j) (s - j) := by
          apply Finset.sum_congr rfl
          intro J hJ
          exact hfixed J hJ
        _ = _ := by simp [hJcount]

lemma sampleLaw_expect {d s : ℕ} (hsd : s ≤ d) (f : Finset (Fin d) → ℝ) :
    (sampleLaw d s hsd).expect f =
      (∑ B ∈ samples d s, f B) / (Nat.choose d s : ℝ) := by
  classical
  unfold FinProb.expect
  change (∑ B : Finset (Fin d),
      (if B ∈ samples d s then (Nat.choose d s : ℝ)⁻¹ else 0) * f B) = _
  calc
    _ = ∑ B ∈ samples d s, (Nat.choose d s : ℝ)⁻¹ * f B := by
      calc
        _ = ∑ B, if B ∈ samples d s then (Nat.choose d s : ℝ)⁻¹ * f B else 0 := by
          simp only [ite_mul, zero_mul]
        _ = _ := by
          rw [← Finset.sum_filter]
          <;> simp
    _ = (Nat.choose d s : ℝ)⁻¹ * ∑ B ∈ samples d s, f B := by
      rw [← Finset.mul_sum]
    _ = _ := by simp [div_eq_mul_inv, mul_comm]

open Classical in
lemma sampleLaw_pr {d s : ℕ} (hsd : s ≤ d) (E : Finset (Fin d) → Prop) :
    (sampleLaw d s hsd).pr E =
      ((samples d s).filter E).card / (Nat.choose d s : ℝ) := by
  classical
  unfold FinProb.pr
  simp only [sampleLaw]
  change (∑ B : Finset (Fin d), if E B then
      (if B ∈ samples d s then (Nat.choose d s : ℝ)⁻¹ else 0) else 0) = _
  calc
    _ = ∑ B, if B ∈ samples d s ∧ E B then (Nat.choose d s : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases he : E B <;> by_cases hs : B ∈ samples d s <;>
        simp [sampleLaw, he, hs]
    _ = ∑ B ∈ Finset.univ.filter (fun B => B ∈ samples d s ∧ E B),
          (Nat.choose d s : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
    _ = ∑ B ∈ (samples d s).filter E, (Nat.choose d s : ℝ)⁻¹ := by
      rw [show Finset.univ.filter (fun B : Finset (Fin d) => B ∈ samples d s ∧ E B) =
        (samples d s).filter E by ext B; simp [and_comm]]
    _ = _ := by simp [div_eq_mul_inv, mul_comm]

lemma sampleLaw_factorialMoment {d s j : ℕ} (A : Finset (Fin d))
    (hsd : s ≤ d) (hjs : j ≤ s) :
    (sampleLaw d s hsd).expect
        (fun B => (Nat.choose (intersectionWeight A B) j : ℝ)) =
      (Nat.choose s j : ℝ) *
        ((Nat.choose A.card j : ℝ) / (Nat.choose d j : ℝ)) := by
  classical
  have hsumNat := factorialMomentSum A hsd hjs
  have hsumReal :
      ∑ B ∈ samples d s, (Nat.choose (intersectionWeight A B) j : ℝ) =
        (Nat.choose A.card j : ℝ) * Nat.choose (d - j) (s - j) := by
    exact_mod_cast hsumNat
  have hchooseMulNat : Nat.choose d s * Nat.choose s j =
      Nat.choose d j * Nat.choose (d - j) (s - j) := Nat.choose_mul hjs
  have hchooseMul : (Nat.choose d s : ℝ) * Nat.choose s j =
      (Nat.choose d j : ℝ) * Nat.choose (d - j) (s - j) := by
    exact_mod_cast hchooseMulNat
  have hds : (Nat.choose d s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsd).ne'
  have hdj : (Nat.choose d j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hjs.trans hsd)).ne'
  have hfrac : (Nat.choose (d - j) (s - j) : ℝ) / Nat.choose d s =
      (Nat.choose s j : ℝ) / Nat.choose d j := by
    apply (div_eq_div_iff hds hdj).2
    calc
      (Nat.choose (d - j) (s - j) : ℝ) * Nat.choose d j =
          (Nat.choose d j : ℝ) * Nat.choose (d - j) (s - j) := by ring
      _ = (Nat.choose d s : ℝ) * Nat.choose s j := hchooseMul.symm
      _ = (Nat.choose s j : ℝ) * Nat.choose d s := by ring
  rw [sampleLaw_expect, hsumReal]
  calc
    (Nat.choose A.card j : ℝ) * Nat.choose (d - j) (s - j) /
        Nat.choose d s =
      (Nat.choose A.card j : ℝ) *
        ((Nat.choose (d - j) (s - j) : ℝ) / Nat.choose d s) := by ring
    _ = _ := by rw [hfrac]; ring

noncomputable def bernoulliLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FinProb Bool where
  w b := if b then p else 1 - p
  nonneg b := by
    cases b
    · simp [sub_nonneg.mpr hp1]
    · simpa using hp
  sum_eq_one := by simp

def boolValue (b : Bool) : ℝ := if b then 1 else 0

lemma bernoulli_mgf_bound {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - p + p * Real.exp t ≤ Real.exp (p * t + t ^ 2 / 8) := by
  let P := bernoulliLaw p hp hp1
  have hmean : P.expect boolValue = p := by
    simp [P, bernoulliLaw, FinProb.expect, boolValue]
  have hbound : ∀ b, (0 : ℝ) ≤ boolValue b ∧ boolValue b ≤ 1 := by
    intro b
    cases b <;> simp [boolValue]
  have hh := xHoeffdingLemma P boolValue 0 1 t (by norm_num) hbound
  have hcenter : P.expect (fun b => Real.exp (t * (boolValue b - P.expect boolValue))) ≤
      Real.exp (t ^ 2 / 8) := by simpa [hmean] using hh
  have hform : P.expect (fun b => Real.exp (t * (boolValue b - P.expect boolValue))) =
      Real.exp (-t * p) * (1 - p + p * Real.exp t) := by
    calc
      P.expect (fun b => Real.exp (t * (boolValue b - P.expect boolValue))) =
          (1 - p) * Real.exp (t * (0 - p)) + p * Real.exp (t * (1 - p)) := by
        simp [P, bernoulliLaw, FinProb.expect, boolValue, hmean]
        <;> ring_nf
        <;> ac_rfl
      _ = Real.exp (-t * p) * (1 - p + p * Real.exp t) := by
        have hzeroExp : Real.exp (t * (0 - p)) = Real.exp (-t * p) := by
          congr 1
          ring
        have honeExp : Real.exp (t * (1 - p)) = Real.exp t * Real.exp (-t * p) := by
          rw [show t * (1 - p) = t + (-t) * p by ring, Real.exp_add]
        rw [hzeroExp, honeExp]
        ring
  have hcancel : Real.exp (t * p) * Real.exp (-t * p) = 1 := by
    calc
      _ = Real.exp (t * p + (-t) * p) := by rw [← Real.exp_add]
      _ = 1 := by rw [show t * p + (-t) * p = 0 by ring, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_left hcenter (Real.exp_nonneg (t * p))
  calc
    1 - p + p * Real.exp t =
        Real.exp (t * p) * (Real.exp (-t * p) * (1 - p + p * Real.exp t)) := by
      calc
        _ = (Real.exp (t * p) * Real.exp (-t * p)) * (1 - p + p * Real.exp t) := by
          rw [hcancel]
          ring
        _ = _ := by ring
    _ = Real.exp (t * p) * P.expect
        (fun b => Real.exp (t * (boolValue b - P.expect boolValue))) := by
      rw [hform]
    _ ≤ Real.exp (t * p) * Real.exp (t ^ 2 / 8) := hmul
    _ = Real.exp (p * t + t ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma expect_finset_sum {Ω ι : Type*} [Fintype Ω]
    (P : FinProb Ω) (S : Finset ι) (f : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, P.expect (f i) := by
  classical
  unfold FinProb.expect
  calc
    _ = ∑ ω, ∑ i ∈ S, P.w ω * f i ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
    _ = ∑ i ∈ S, ∑ ω, P.w ω * f i ω := Finset.sum_comm
    _ = _ := rfl

lemma sampleLaw_mgf_le {d s : ℕ} (A : Finset (Fin d)) (hsd : s ≤ d) (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) :
    (sampleLaw d s hsd).expect (fun B => Real.exp (t * (intersectionWeight A B : ℝ))) ≤
      Real.exp ((s : ℝ) * ((A.card : ℝ) / d) * t + (s : ℝ) * t ^ 2 / 8) := by
  classical
  let P := sampleLaw d s hsd
  let X := intersectionWeight A
  let p : ℝ := (A.card : ℝ) / d
  let a : ℝ := Real.exp t - 1
  have hAcard : A.card ≤ d := by
    simpa [Fintype.card_fin] using Finset.card_le_univ A
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have hAc : (A.card : ℝ) ≤ d := by exact_mod_cast hAcard
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      (A.card : ℝ) / d ≤ (d : ℝ) / d := div_le_div_of_nonneg_right hAc hdR.le
      _ = 1 := by field_simp
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith [(Real.one_le_exp_iff.mpr ht)]
  have hchooseBound (B : Finset (Fin d)) (hB : B ∈ samples d s) : X B ≤ s := by
    have hBcard : B.card = s := by
      simpa [samples] using hB
    dsimp [X, intersectionWeight]
    exact (Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)).trans_eq hBcard
  have hbin (B : Finset (Fin d)) (hB : B ∈ samples d s) :
      Real.exp (t * (X B : ℝ)) =
        ∑ j ∈ Finset.range (s + 1), (Nat.choose (X B) j : ℝ) * a ^ j := by
    have hexp : Real.exp (t * (X B : ℝ)) = (Real.exp t) ^ (X B) := by
      calc
        Real.exp (t * (X B : ℝ)) = Real.exp ((X B : ℝ) * t) := by congr 1 <;> ring
        _ = _ := by rw [Real.exp_nat_mul]
    have hbinom : (1 + a) ^ (X B) =
        ∑ j ∈ Finset.range (X B + 1), (Nat.choose (X B) j : ℝ) * a ^ j := by
      calc
        (1 + a) ^ (X B) = (a + 1) ^ (X B) := by congr 1 <;> ring
        _ = ∑ j ∈ Finset.range (X B + 1), a ^ j * 1 ^ (X B - j) * Nat.choose (X B) j :=
          add_pow a 1 (X B)
        _ = _ := by simp [mul_comm]
    have hwide : (1 + a) ^ (X B) =
        ∑ j ∈ Finset.range (s + 1), (Nat.choose (X B) j : ℝ) * a ^ j := by
      calc
        _ = ∑ j ∈ Finset.range (X B + 1), (Nat.choose (X B) j : ℝ) * a ^ j := hbinom
        _ = _ := by
          apply Finset.sum_subset
          · intro j hj
            exact Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hj)
                (Nat.add_le_add_right (hchooseBound B hB) 1))
          · intro j hj hjnot
            have hXlt : X B < j := by
              have hj' := Finset.mem_range.mp hj
              have hnot : ¬ j < X B + 1 := by
                intro hlt
                exact hjnot (Finset.mem_range.mpr hlt)
              omega
            simp [Nat.choose_eq_zero_of_lt hXlt]
    rw [hexp]
    rw [show Real.exp t = 1 + a by dsimp [a]; ring]
    exact hwide
  have hchange : P.expect (fun B => Real.exp (t * (X B : ℝ))) =
      P.expect (fun B => ∑ j ∈ Finset.range (s + 1),
        (Nat.choose (X B) j : ℝ) * a ^ j) := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hBs : B ∈ samples d s
    · simp [P, sampleLaw, hBs, hbin B hBs]
    · simp [P, sampleLaw, hBs]
  have hterm (j : ℕ) :
      P.expect (fun B => (Nat.choose (X B) j : ℝ) * a ^ j) =
        a ^ j * P.expect (fun B => (Nat.choose (X B) j : ℝ)) := by
    unfold FinProb.expect
    calc
      _ = ∑ B, a ^ j * (P.w B * (Nat.choose (X B) j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro B hB
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hmomentBound (j : ℕ) (hjs : j ≤ s) :
      P.expect (fun B => (Nat.choose (X B) j : ℝ)) ≤
        (Nat.choose s j : ℝ) * p ^ j := by
    rw [sampleLaw_factorialMoment A hsd hjs]
    apply mul_le_mul_of_nonneg_left
      (choose_ratio_le_pow (K := A.card) (d := d) (j := j) hAcard hd)
      (by positivity)
  have hsumBound :
      P.expect (fun B => Real.exp (t * (X B : ℝ))) ≤
        ∑ j ∈ Finset.range (s + 1), (Nat.choose s j : ℝ) * (p * a) ^ j := by
    rw [hchange, expect_finset_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j < s + 1 := Finset.mem_range.mp hj
    have hjs : j ≤ s := by omega
    calc
      P.expect (fun B => (Nat.choose (X B) j : ℝ) * a ^ j) =
          a ^ j * P.expect (fun B => (Nat.choose (X B) j : ℝ)) := hterm j
      _ ≤ a ^ j * ((Nat.choose s j : ℝ) * p ^ j) :=
        mul_le_mul_of_nonneg_left (hmomentBound j hjs) (pow_nonneg ha _)
      _ = (Nat.choose s j : ℝ) * (p * a) ^ j := by rw [mul_pow]; ring
  have hbinFinal :
      ∑ j ∈ Finset.range (s + 1), (Nat.choose s j : ℝ) * (p * a) ^ j = (1 + p * a) ^ s := by
    calc
      _ = ∑ j ∈ Finset.range (s + 1), (p * a) ^ j * Nat.choose s j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (p * a + 1) ^ s := by
        symm
        simpa [mul_comm] using (add_pow (p * a) (1 : ℝ) s)
      _ = _ := by congr 1 <;> ring
  have hbern := bernoulli_mgf_bound (p := p) (t := t) hp0 hp1
  have hbern' : 1 + p * a ≤ Real.exp (p * t + t ^ 2 / 8) := by
    calc
      1 + p * a = 1 - p + p * Real.exp t := by dsimp [a]; ring
      _ ≤ Real.exp (p * t + t ^ 2 / 8) := hbern
  calc
    P.expect (fun B => Real.exp (t * (X B : ℝ))) ≤
        ∑ j ∈ Finset.range (s + 1), (Nat.choose s j : ℝ) * (p * a) ^ j := hsumBound
    _ = (1 + p * a) ^ s := hbinFinal
    _ ≤ (Real.exp (p * t + t ^ 2 / 8)) ^ s := by gcongr
    _ = Real.exp ((s : ℝ) * (p * t + t ^ 2 / 8)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp ((s : ℝ) * p * t + (s : ℝ) * t ^ 2 / 8) := by congr 1 <;> ring

theorem hypergeometricIntersectionTailAux (d s : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hsd : s ≤ d) (A : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun B : Finset (Fin d) => B.card = s ∧
      ((B ∩ A).card : ℝ) ≥ (s : ℝ) * A.card / d + t)).card : ℝ) / Nat.choose d s ≤
        Real.exp (-2 * t ^ 2 / s) := by
  classical
  let P := sampleLaw d s hsd
  let X : Finset (Fin d) → ℝ := fun B => (intersectionWeight A B : ℝ)
  let μ : ℝ := (s : ℝ) * A.card / d
  let E : Finset (Fin d) → Prop := fun B => μ + t ≤ X B
  have hnum : (samples d s).filter E =
      Finset.univ.filter (fun B : Finset (Fin d) => B.card = s ∧
        ((B ∩ A).card : ℝ) ≥ (s : ℝ) * A.card / d + t) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hB, hE⟩
      have hcard : B.card = s := by simpa [samples] using hB
      refine ⟨hcard, ?_⟩
      simpa [E, μ, X, intersectionWeight, Finset.inter_comm, ge_iff_le] using hE
    · rintro ⟨hcard, hE⟩
      refine ⟨?_, ?_⟩
      · simpa [samples] using hcard
      · simpa [E, μ, X, intersectionWeight, Finset.inter_comm, ge_iff_le] using hE
  have hprob : P.pr E =
      ((Finset.univ.filter (fun B : Finset (Fin d) => B.card = s ∧
        ((B ∩ A).card : ℝ) ≥ (s : ℝ) * A.card / d + t)).card : ℝ) / Nat.choose d s := by
    rw [sampleLaw_pr hsd E, hnum]
  by_cases ht0 : t = 0
  · have hle : P.pr E ≤ 1 := by
      unfold FinProb.pr
      calc
        _ ≤ ∑ B, P.w B := by
          apply Finset.sum_le_sum
          intro B hB
          by_cases hE : E B <;> simp [hE, P.nonneg B]
        _ = 1 := P.sum_eq_one
    rw [← hprob, ht0]
    simpa using hle
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let rate : ℝ := 4 * t / s
    have hrate : 0 < rate := by dsimp [rate]; positivity
    have hmgf := sampleLaw_mgf_le A hsd hd rate hrate.le
    rw [← hprob]
    calc
      P.pr E ≤ Real.exp (-rate * (μ + t)) * P.expect (fun B => Real.exp (rate * X B)) :=
        FinProb.pr_exp_markov P X rate (μ + t) hrate.le
      _ ≤ Real.exp (-rate * (μ + t)) *
          Real.exp ((s : ℝ) * ((A.card : ℝ) / d) * rate + (s : ℝ) * rate ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (-2 * t ^ 2 / s) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [rate, μ]
        field_simp [ne_of_gt (show (0 : ℝ) < s by exact_mod_cast hs),
          ne_of_gt (show (0 : ℝ) < (d : ℝ) by exact_mod_cast hd)]
        ring

end CubeGeometryPToolsCubeR
end HypercubeRamsey
