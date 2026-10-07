import HypercubeRamsey.S06.Params
import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.S03.Height.Scale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HypercubeRamsey.S06.Lane_q_s06_ev_a

open Classical
open Filter
open scoped BigOperators

private theorem prod_drop_update {α Ω : Type*} [DecidableEq α] [Fintype α]
    (D : Finset α) (o : α → Ω) (c : α) (z : Ω) (f : α → Ω → ℝ) :
    (∏ e ∈ D, if c = e then 1 else f e (Function.update o c z e)) =
      ∏ e ∈ D, if c = e then 1 else f e (o e) := by
  apply Finset.prod_congr rfl
  intro e he
  by_cases hec : e = c
  · subst e
    simp
  · have hu : Function.update o c z e = o e :=
      Function.update_of_ne (f := o) (a := e) (a' := c) hec z
    simp [hec, hu]

theorem s3Del_update_irrelevant {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    {Id : Type} [Fintype Id] [DecidableEq Id]
    (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (b : X.State)
    (D : Finset (Id × X.Ty)) (o : X.Data Id) (c : Id × X.Ty) (z : X.Tuple) :
    X.s3Del H b D (Function.update o c z) c = X.s3Del H b D o c := by
  have hweight : ∀ ξ,
      X.s3Weight H b D (Function.update o c z) (some c) ξ =
        X.s3Weight H b D o (some c) ξ := by
    intro ξ
    cases hmode : X.stMode b <;>
      simp [Ctx6.s3Weight, hmode, Ctx6.lowWeight, Ctx6.highWeight, prod_drop_update]
  unfold Ctx6.s3Del
  exact congrArg (fun f : Fin N → ℝ => normalize6 f X.y₀) (funext hweight)

abbrev CentreRest6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (e : X.Loc × X.Ty) :=
  (((X.Loc → Bool) × (({q : X.Loc × X.Ty // q ≠ e}) → X.Tuple)) ×
      (X.Loc → Bool)) × X.hp.Ties

noncomputable def dataFromParts6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (e : X.Loc × X.Ty) (z : X.Tuple)
    (r : {q : X.Loc × X.Ty // q ≠ e} → X.Tuple) : X.Data X.Loc :=
  fun q => if h : q = e then z else r ⟨q, h⟩

noncomputable def centreFromParts6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (e : X.Loc × X.Ty) (z : X.Tuple) (r : CentreRest6 X e) : X.Centre :=
  (((r.1.1.1, dataFromParts6 X e z r.1.1.2), r.1.2), r.2)

noncomputable instance centreRestIndex6Fintype {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (e : X.Loc × X.Ty) :
    Fintype {q : X.Loc × X.Ty // q ≠ e} := by
  classical
  infer_instance

noncomputable def centreRestLaw6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (e : X.Loc × X.Ty) : FinProb (CentreRest6 X e) :=
  FinProb.prod (FinProb.prod (FinProb.prod X.hp.posLaw
    (FinProb.pi fun q : {q : X.Loc × X.Ty // q ≠ e} => X.tupleLaw H q.1.2))
    X.hp.actLaw) X.hp.tieLaw

theorem centre_weight_split6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (e : X.Loc × X.Ty) (z : X.Tuple) (r : CentreRest6 X e) :
    (X.centreLaw H).w (centreFromParts6 X e z r) =
      (X.tupleLaw H e.2).w z * (centreRestLaw6 X H e).w r := by
  classical
  have hdata := Lane_q_s06_even.pi_weight_split_coord_even
    (fun q : X.Loc × X.Ty => X.tupleLaw H q.2) e
      (dataFromParts6 X e z r.1.1.2)
  have hdata' :
      (∏ q, (X.tupleLaw H q.2).w (dataFromParts6 X e z r.1.1.2 q)) =
        (X.tupleLaw H e.2).w z *
          (∏ q : {q : X.Loc × X.Ty // q ≠ e},
            (X.tupleLaw H q.1.2).w (r.1.1.2 q)) := by
    calc
      _ = (X.tupleLaw H e.2).w (dataFromParts6 X e z r.1.1.2 e) *
          (∏ q : {q : X.Loc × X.Ty // q ≠ e},
            (X.tupleLaw H q.1.2).w (dataFromParts6 X e z r.1.1.2 q.1)) := hdata
      _ = _ := by
        have he : dataFromParts6 X e z r.1.1.2 e = z := by
          simp [dataFromParts6]
        have hrest :
            (∏ q : {q : X.Loc × X.Ty // q ≠ e},
              (X.tupleLaw H q.1.2).w (dataFromParts6 X e z r.1.1.2 q.1)) =
            (∏ q : {q : X.Loc × X.Ty // q ≠ e},
              (X.tupleLaw H q.1.2).w (r.1.1.2 q)) := by
          apply Finset.prod_congr rfl
          intro q hq
          simp [dataFromParts6, q.2]
        rw [he, hrest]
  change (((X.hp.posLaw.prod (X.dataLaw X.Loc H)).prod X.hp.actLaw).prod X.hp.tieLaw).w
      (centreFromParts6 X e z r) = _
  simp only [Ctx6.centreLaw, Ctx6.dataLaw, FinProb.prod, FinProb.pi,
    centreFromParts6, centreRestLaw6]
  rw [hdata']
  ring

noncomputable def centreSplitEquiv6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (e : X.Loc × X.Ty) : X.Centre ≃ X.Tuple × CentreRest6 X e where
  toFun C := (X.tup C e, (((X.pos C, fun q => X.tup C q.1), X.act C), X.ties C))
  invFun p := centreFromParts6 X e p.1 p.2
  left_inv := by
    rintro ⟨⟨⟨P, D⟩, A⟩, T⟩
    have hdata : dataFromParts6 X e (D e) (fun q => D q.1) = D := by
      funext q
      by_cases hq : q = e
      · subst q
        simp [dataFromParts6]
      · simp [dataFromParts6, hq]
    exact congrArg (fun d => (((P, d), A), T)) hdata
  right_inv := by
    rintro ⟨z, ⟨⟨P, r⟩, A⟩, T⟩
    apply Prod.ext
    · change (dataFromParts6 X e z r) e = z
      simp [dataFromParts6]
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · funext q
            change dataFromParts6 X e z r q.1 = r q
            simp [dataFromParts6, q.2]
        · rfl
      · rfl

theorem centreLaw_expect_split6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (e : X.Loc × X.Ty) (f : X.Centre → ℝ) :
    (X.centreLaw H).expect f =
      ∑ r : CentreRest6 X e, (centreRestLaw6 X H e).w r *
        ∑ z : X.Tuple, (X.tupleLaw H e.2).w z * f (centreFromParts6 X e z r) := by
  classical
  let Eeq := centreSplitEquiv6 X e
  unfold FinProb.expect
  rw [← Equiv.sum_comp Eeq.symm (fun C => (X.centreLaw H).w C * f C)]
  rw [Fintype.sum_prod_type]
  calc
    (∑ z : X.Tuple, ∑ r : CentreRest6 X e,
        (X.centreLaw H).w (Eeq.symm (z, r)) * f (Eeq.symm (z, r))) =
      ∑ z : X.Tuple, ∑ r : CentreRest6 X e,
        ((X.tupleLaw H e.2).w z * (centreRestLaw6 X H e).w r) *
          f (centreFromParts6 X e z r) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro r hr
        have heq : Eeq.symm (z, r) = centreFromParts6 X e z r := by rfl
        rw [heq, centre_weight_split6]
    _ = ∑ r : CentreRest6 X e, (centreRestLaw6 X H e).w r *
          ∑ z : X.Tuple, (X.tupleLaw H e.2).w z * f (centreFromParts6 X e z r) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring

private theorem nat_twopow40_bound (m : ℕ) (hm : 9 ≤ m) : 40 * (m + 1) ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm' : 9 ≤ m
      · calc
          40 * (m + 1 + 1) ≤ 2 * (40 * (m + 1)) := by nlinarith
          _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 (ih hm')
          _ = 2 ^ (m + 1) := by rw [pow_succ]; omega
      · have hmEq : m = 8 := by omega
        subst m
        norm_num

private theorem nat_twopow25_bound (m : ℕ) (hm : 9 ≤ m) : 50 * (m + 1) ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm' : 9 ≤ m
      · calc
          50 * (m + 1 + 1) ≤ 2 * (50 * (m + 1)) := by nlinarith
          _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 (ih hm')
          _ = 2 ^ (m + 1) := by rw [pow_succ]; omega
      · have hmEq : m = 8 := by omega
        subst m
        norm_num

/-- For the dimensions used in Section 6, the host-size exponent dwarfs both `n` and `2n`. -/
theorem large_power_bounds6 {n : ℕ} (hn : 10 ^ 10 ≤ n) :
    (n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 40) ∧
      2 * (n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 25) := by
  have h40div : 9 ≤ n / 40 := by omega
  have h25div : 9 ≤ n / 25 := by omega
  have h40rem := Nat.mod_lt n (by norm_num : 0 < 40)
  have h25rem := Nat.mod_lt n (by norm_num : 0 < 25)
  have h40eq : n = (n / 40) * 40 + n % 40 := by omega
  have h25eq : n = (n / 25) * 25 + n % 25 := by omega
  have h40nat : n ≤ 2 ^ (n / 40) := by
    have h := nat_twopow40_bound (n / 40) h40div
    omega
  have h25nat : 2 * n ≤ 2 ^ (n / 25) := by
    have h := nat_twopow25_bound (n / 25) h25div
    omega
  have h40cast : ((2 ^ (n / 40) : ℕ) : ℝ) =
      (2 : ℝ) ^ ((n / 40 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  have h25cast : ((2 ^ (n / 25 : ℕ) : ℕ) : ℝ) =
      (2 : ℝ) ^ ((n / 25 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  have h40le : ((n / 40 : ℕ) : ℝ) ≤ (n : ℝ) / 40 := by
    have heq : (n : ℝ) = ((n / 40 : ℕ) : ℝ) * 40 + ((n % 40 : ℕ) : ℝ) := by
      exact_mod_cast h40eq
    have hr : 0 ≤ ((n % 40 : ℕ) : ℝ) := by positivity
    nlinarith
  have h25le : ((n / 25 : ℕ) : ℝ) ≤ (n : ℝ) / 25 := by
    have heq : (n : ℝ) = ((n / 25 : ℕ) : ℝ) * 25 + ((n % 25 : ℕ) : ℝ) := by
      exact_mod_cast h25eq
    have hr : 0 ≤ ((n % 25 : ℕ) : ℝ) := by positivity
    nlinarith
  constructor
  · calc
      (n : ℝ) ≤ ((2 ^ (n / 40) : ℕ) : ℝ) := by exact_mod_cast h40nat
      _ = (2 : ℝ) ^ ((n / 40 : ℕ) : ℝ) := h40cast
      _ ≤ (2 : ℝ) ^ ((n : ℝ) / 40) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h40le
  · calc
      2 * (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ (n / 25) : ℕ) : ℝ) := by exact_mod_cast h25nat
      _ = (2 : ℝ) ^ ((n / 25 : ℕ) : ℝ) := h25cast
      _ ≤ (2 : ℝ) ^ ((n : ℝ) / 25) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h25le

theorem log_two_lower6 : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := 1) (by norm_num)
  norm_num at h
  simpa using h

theorem family_rate_of_growth {n m J T H k : ℕ} {α : ℝ}
    (hn : 2 ≤ n) (hJ : 2000000 ≤ J)
    (hT : (T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * J)
    (hlogT : Real.log (T + 2) ≤ 2 * α * Real.log n)
    (hH : H ≤ n ^ 4)
    (hk : κ₆ * (J : ℝ) * Real.log n ≤ k)
    (hα0 : 0 ≤ α)
    (hα : α ≤ 1 / 10 ^ 12) :
    (H : ℝ) * Real.exp (10 ^ 4 *
      (T * Real.log (3 * n * (4 * n ^ 10) + 2) +
        (J + 1) * Real.log (T + 2))) ≤ Real.exp ((5 / 100 : ℝ) * k) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have harg : (3 : ℝ) * n * (4 * (n : ℝ) ^ 10) + 2 ≤ 14 * (n : ℝ) ^ 11 := by
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 11 := by
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    nlinarith
  have hlogArg : Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤ 15 * Real.log n := by
    have hmon := Real.log_le_log (by positivity) harg
    have h14 : Real.log (14 : ℝ) ≤ 4 * Real.log 2 := by
      have h := Real.log_le_log (by norm_num) (by norm_num : (14 : ℝ) ≤ 2 ^ 4)
      rw [Real.log_pow] at h
      norm_num at h ⊢
      nlinarith
    have h2n : Real.log (2 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hmon
    have h14n : Real.log (14 : ℝ) ≤ 4 * Real.log n := by nlinarith [h14, h2n]
    have hsum : Real.log (14 : ℝ) + 11 * Real.log n ≤ 15 * Real.log n := by
      nlinarith [h14n]
    exact hmon.trans hsum
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJplus : (J : ℝ) + 1 ≤ 2 * J := by nlinarith
  have hTarg : (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
      (15 / 10 ^ 11 : ℝ) * J * Real.log n := by
    calc
      (T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) ≤
          (T : ℝ) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_left hlogArg (by exact_mod_cast (Nat.zero_le T))
      _ ≤ ((1 / 10 ^ 11 : ℝ) * J) * (15 * Real.log n) :=
            mul_le_mul_of_nonneg_right hT (mul_nonneg (by norm_num) hlogn)
      _ = (15 / 10 ^ 11 : ℝ) * J * Real.log n := by ring
  have hTtail : ((J : ℝ) + 1) * Real.log (T + 2) ≤
      4 * α * J * Real.log n := by
    calc
      ((J : ℝ) + 1) * Real.log (T + 2) ≤ ((J : ℝ) + 1) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
      _ ≤ (2 * J) * (2 * α * Real.log n) :=
        mul_le_mul_of_nonneg_right hJplus
          (mul_nonneg (mul_nonneg (by norm_num) hα0) hlogn)
      _ = 4 * α * J * Real.log n := by ring
  have hS : 10 ^ 4 *
      ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
        ((J : ℝ) + 1) * Real.log (T + 2)) ≤ (2 / 100 : ℝ) * k := by
    have hα' : 0 ≤ α := hα0
    have hJreal : (2000000 : ℝ) ≤ J := by exact_mod_cast hJ
    have hJlog : (2000000 : ℝ) * Real.log n ≤ J * Real.log n :=
      mul_le_mul_of_nonneg_right hJreal hlogn
    have hcoeff : 10 ^ 4 * (15 / 10 ^ 11 + 4 * α) ≤
        (2 / 100 : ℝ) * κ₆ := by
      norm_num [κ₆] at hα ⊢
      nlinarith [hα]
    have hsumRate := add_le_add hTarg hTtail
    calc
      10 ^ 4 *
          ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
            ((J : ℝ) + 1) * Real.log (T + 2)) ≤
          10 ^ 4 * (15 / 10 ^ 11 * J * Real.log n + 4 * α * J * Real.log n) :=
            mul_le_mul_of_nonneg_left hsumRate (by norm_num)
      _ = 10 ^ 4 * ((15 / 10 ^ 11 + 4 * α) * J * Real.log n) := by ring
      _ = (10 ^ 4 * (15 / 10 ^ 11 + 4 * α)) * (J * Real.log n) := by ring
      _ ≤ ((2 / 100 : ℝ) * κ₆) * (J * Real.log n) :=
            mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (by positivity) hlogn)
      _ ≤ (2 / 100 : ℝ) * k := by
            have hk' := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2 / 100)
            nlinarith [hk']
  have hHexp : (H : ℝ) ≤ Real.exp ((3 / 100 : ℝ) * k) := by
    have hHreal : (H : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hH
    have hexp : (n : ℝ) ^ 4 = Real.exp (4 * Real.log n) := by
      calc
        (n : ℝ) ^ 4 = (Real.exp (Real.log n)) ^ 4 := by rw [Real.exp_log hnpos]
        _ = Real.exp (4 * Real.log n) := by
          rw [← Real.exp_nat_mul (Real.log n) 4]
          norm_num
    have hlarge : 4 * Real.log n ≤ (3 / 100 : ℝ) * k := by
      have hJreal : (2000000 : ℝ) ≤ J := by exact_mod_cast hJ
      have hJlog : (2000000 : ℝ) * Real.log n ≤ J * Real.log n :=
        mul_le_mul_of_nonneg_right hJreal hlogn
      have hk' := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 3 / 100)
      calc
        4 * Real.log n ≤ 6 * Real.log n := by nlinarith [hlogn]
        _ = ((3 / 100 : ℝ) * κ₆) * ((2000000 : ℝ) * Real.log n) := by
          norm_num [κ₆]
          ring
        _ ≤ ((3 / 100 : ℝ) * κ₆) * ((J : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_left hJlog (by norm_num [κ₆])
        _ = (3 / 100 : ℝ) * (κ₆ * (J : ℝ) * Real.log n) := by ring
        _ ≤ (3 / 100 : ℝ) * k := by nlinarith [hk']
    calc
      (H : ℝ) ≤ (n : ℝ) ^ 4 := hHreal
      _ = Real.exp (4 * Real.log n) := hexp
      _ ≤ Real.exp ((3 / 100 : ℝ) * k) := Real.exp_le_exp.mpr hlarge
  calc
    (H : ℝ) * Real.exp (10 ^ 4 *
        ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
          ((J : ℝ) + 1) * Real.log (T + 2))) ≤
        Real.exp ((3 / 100 : ℝ) * k) * Real.exp ((2 / 100 : ℝ) * k) := by
      calc
        (H : ℝ) * Real.exp (10 ^ 4 *
            ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
              ((J : ℝ) + 1) * Real.log (T + 2))) ≤
            Real.exp ((3 / 100 : ℝ) * k) *
              Real.exp (10 ^ 4 *
                ((T : ℝ) * Real.log (3 * n * (4 * (n : ℝ) ^ 10) + 2) +
                  ((J : ℝ) + 1) * Real.log (T + 2))) :=
          mul_le_mul_of_nonneg_right hHexp (Real.exp_nonneg _)
        _ ≤ Real.exp ((3 / 100 : ℝ) * k) * Real.exp ((2 / 100 : ℝ) * k) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS) (Real.exp_nonneg _)
    _ = Real.exp ((5 / 100 : ℝ) * k) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem topScale_fourth_eventually (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ n₀, ∀ n ≥ n₀,
      topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ n ^ 4 := by
  let α := α₆ p₀
  let σ := σ₆ α
  let ζ := ζ₆ α
  let q : ℕ := ⌈(1 - ζ) / σ⌉₊
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  have hαle : α ≤ 1 / 10 ^ 12 := min_le_left _ _
  have hσ : 0 < σ := by dsimp [σ, σ₆]; positivity
  have hζeq : ζ = 2 * σ := by simp [σ, ζ, σ₆, ζ₆]; ring
  have hσsmall : σ < 1 / 4 := by
    rw [show σ = α / (10 ^ 6 : ℝ) by rfl, div_lt_iff₀ (by norm_num)]
    nlinarith [hαle]
  have hratioPos : 0 ≤ (1 - ζ) / σ := by
    apply div_nonneg
    · rw [hζeq]
      linarith
    · exact le_of_lt hσ
  have hqLower : (1 - ζ) / σ ≤ (q : ℝ) := Nat.le_ceil _
  have hqUpper : (q : ℝ) < (1 - ζ) / σ + 1 := Nat.ceil_lt_add_one hratioPos
  have hσqLower : 1 - ζ ≤ σ * q := by
    simpa [mul_comm] using (div_le_iff₀ hσ).mp hqLower
  have hσqUpper : σ * q ≤ 1 := by
    have hmul : (q : ℝ) * σ < 1 - ζ + σ := by
      calc
        (q : ℝ) * σ < ((1 - ζ) / σ + 1) * σ := mul_lt_mul_of_pos_right hqUpper hσ
        _ = 1 - ζ + σ := by field_simp [ne_of_gt hσ]
    rw [hζeq] at hmul
    nlinarith
  have hnTrend : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpowTrend : Tendsto (fun n : ℕ => (n : ℝ) ^ σ) atTop atTop :=
    (tendsto_rpow_atTop hσ).comp hnTrend
  have hpowEvent := hpowTrend.eventually_ge_atTop (2 : ℝ)
  have hNEvent := eventually_ge_atTop (2 ^ (q + 1) : ℕ)
  have hAll : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ σ ≥ 2 ∧ 2 ^ (q + 1) ≤ n := by
    filter_upwards [hpowEvent, hNEvent] with n hpow hn
    exact ⟨hpow, hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hpowN, hNq⟩ := hn₀ n hn
  have hpowone : 1 ≤ 2 ^ (q + 1) := one_le_pow₀ (by norm_num)
  have hn1 : 1 ≤ n := le_trans hpowone hNq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by positivity
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hceilM : 2 ≤ ⌈(n : ℝ) ^ σ⌉₊ := by
    have hcast : (2 : ℝ) ≤ ⌈(n : ℝ) ^ σ⌉₊ :=
      le_trans hpowN (Nat.le_ceil _)
    exact_mod_cast hcast
  have hMdef : M = ⌈(n : ℝ) ^ σ⌉₊ := by
    dsimp [M]
    exact max_eq_right hceilM
  have hMlow : (n : ℝ) ^ σ ≤ (M : ℝ) := by
    rw [hMdef]
    exact Nat.le_ceil _
  have hceilMupper : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ (n : ℝ) ^ σ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hMupper : (M : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    rw [hMdef]
    linarith [hceilMupper]
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlognupper : Real.log n ≤ n := by
    exact (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  have hlogsq : (Real.log n) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hlognupper)
      (add_nonneg (by positivity) hlogn)
    nlinarith [hprod]
  have hceilRupper : (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) ≤ (Real.log n) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hRupper : (R₀ : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    dsimp [R₀]
    rw [Nat.cast_max]
    apply max_le_iff.mpr
    constructor
    · have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          1 = (1 : ℝ) ^ 2 := by norm_num
          _ ≤ (n : ℝ) ^ 2 := by gcongr
      have htwo : (2 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
        calc
          2 = 2 * (1 : ℝ) := by ring
          _ ≤ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hnSq (by norm_num)
      simpa using (by norm_num : (1 : ℝ) ≤ 2).trans htwo
    · exact le_trans hceilRupper (by nlinarith [hlogsq, hnR])
  have hRlower : 1 ≤ R₀ := by dsimp [R₀]; omega
  have htargetReal : (n : ℝ) ^ (1 - ζ) ≤ (M : ℝ) ^ q := by
    calc
      (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ (σ * q) :=
        Real.rpow_le_rpow_of_exponent_le hnR hσqLower
      _ ≤ (M : ℝ) ^ q := by
        have hpow := Real.rpow_le_rpow (by positivity) hMlow (by positivity : 0 ≤ (q : ℝ))
        calc
          (n : ℝ) ^ (σ * (q : ℝ)) = ((n : ℝ) ^ σ) ^ (q : ℝ) :=
            Real.rpow_mul (x := (n : ℝ)) (by positivity) σ (q : ℝ)
          _ ≤ (M : ℝ) ^ (q : ℝ) := hpow
          _ = (M : ℝ) ^ q := by rw [Real.rpow_natCast]
  have htargetNat : target ≤ M ^ q * R₀ := by
    change ⌈(n : ℝ) ^ (1 - ζ)⌉₊ ≤ M ^ q * R₀
    rw [Nat.ceil_le]
    have hRnat : 1 ≤ R₀ := hRlower
    have hpowNat : (M : ℝ) ^ q ≤ (M ^ q * R₀ : ℕ) := by
      exact_mod_cast (Nat.le_mul_of_pos_right (M ^ q) (Nat.pos_of_ne_zero (by omega : R₀ ≠ 0)))
    exact htargetReal.trans hpowNat
  have hscaleExists : ∃ i, target ≤ M ^ i * R₀ := ⟨q, htargetNat⟩
  have hfind : Nat.find hscaleExists ≤ q := Nat.find_min' hscaleExists htargetNat
  have htop : topScale n σ ζ ≤ M ^ q * R₀ := by
    unfold topScale
    dsimp [M, R₀, target]
    have hbase : 1 ≤ M := by omega
    exact Nat.mul_le_mul_right R₀ (pow_le_pow_right' hbase hfind)
  have hMpow : (M : ℝ) ^ q ≤ (2 : ℝ) ^ q * n := by
    have hEqpow : ((n : ℝ) ^ σ) ^ q = (n : ℝ) ^ (σ * (q : ℝ)) := by
      calc
        ((n : ℝ) ^ σ) ^ q = ((n : ℝ) ^ σ) ^ (q : ℝ) := by rw [Real.rpow_natCast]
        _ = (n : ℝ) ^ (σ * (q : ℝ)) :=
          (Real.rpow_mul (x := (n : ℝ)) (by positivity) σ (q : ℝ)).symm
    calc
      (M : ℝ) ^ q ≤ (2 * (n : ℝ) ^ σ) ^ q := by gcongr
      _ = (2 : ℝ) ^ q * ((n : ℝ) ^ σ) ^ q := by rw [mul_pow]
      _ = (2 : ℝ) ^ q * (n : ℝ) ^ (σ * (q : ℝ)) := by
        rw [hEqpow]
      _ ≤ (2 : ℝ) ^ q * (n : ℝ) := by
        have hnexp : (n : ℝ) ^ (σ * (q : ℝ)) ≤ n := by
          calc
            (n : ℝ) ^ (σ * (q : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnR hσqUpper
            _ = n := by rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hnexp (by positivity)
  have hcoeff : 2 * (2 : ℝ) ^ q ≤ n := by
    have hNqReal : (2 : ℝ) ^ (q + 1) ≤ n := by exact_mod_cast hNq
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hNqReal
  have htopReal : (topScale n σ ζ : ℝ) ≤ (n : ℝ) ^ 4 := by
    have htopCast : (topScale n σ ζ : ℝ) ≤ (M ^ q * R₀ : ℕ) := by exact_mod_cast htop
    calc
      (topScale n σ ζ : ℝ) ≤ (M ^ q * R₀ : ℕ) := htopCast
      _ = (M : ℝ) ^ q * R₀ := by simp [Nat.cast_mul, Nat.cast_pow]
      _ ≤ ((2 : ℝ) ^ q * n) * (2 * (n : ℝ) ^ 2) :=
        mul_le_mul hMpow hRupper (by positivity) (by positivity)
      _ = (2 * (2 : ℝ) ^ q) * (n : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) ^ 4 := by
        calc
          (2 * (2 : ℝ) ^ q) * (n : ℝ) ^ 3 ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right hcoeff (by positivity)
          _ = (n : ℝ) ^ 4 := by ring
  exact_mod_cast htopReal

theorem parameter_growth (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ n₀, ∀ n ≥ n₀,
      let m := m₆ p₀ n
      let J := J₆ m
      let T := T₆ m
      let k := k₆ n m
      J ≥ 2000000 ∧ (T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * J ∧
        Real.log (T + 2) ≤ 2 * α₆ p₀ * Real.log n ∧ m ≤ n ∧ 12 ≤ k ∧ 10 ^ 10 ≤ n := by
  let α := α₆ p₀
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  have hαle : α ≤ 1 / 10 ^ 12 := min_le_left _ _
  have hnTrend : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmTrend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ ((tendsto_rpow_atTop hα).comp hnTrend)
    filter_upwards [] with n
    exact_mod_cast Nat.le_ceil ((n : ℝ) ^ α)
  have hpow04Trend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ) ^ (1 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 25 : ℝ))).comp hmTrend
  have hpow039Trend : Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ) ^ (39 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (39 / 1000 : ℝ))).comp hmTrend
  have hlogTrend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnTrend
  have hαlogTrend : Tendsto (fun n : ℕ => α * Real.log (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hα hlogTrend
  have hlogOne := hlogTrend.eventually_ge_atTop (1 : ℝ)
  have hαlogTwo := hαlogTrend.eventually_ge_atTop (Real.log 2)
  have hpow04 := hpow04Trend.eventually_ge_atTop (4000000 : ℝ)
  have hpow039 := hpow039Trend.eventually_ge_atTop (4 * 10 ^ 11 : ℝ)
  have hmLarge := hmTrend.eventually_ge_atTop (16 : ℝ)
  have hnLarge := (eventually_ge_atTop (10 ^ 10 : ℕ))
  have hAll : ∀ᶠ n : ℕ in atTop,
      let m := m₆ p₀ n
      let J := J₆ m
      let T := T₆ m
      let k := k₆ n m
      J ≥ 2000000 ∧ (T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * J ∧
        Real.log (T + 2) ≤ 2 * α * Real.log n ∧ m ≤ n ∧ 12 ≤ k ∧ 10 ^ 10 ≤ n := by
    filter_upwards [hlogOne, hαlogTwo, hpow04, hpow039, hmLarge, hnLarge]
      with n hlogn hαlogn h04 h039 hm16 hn10
    dsimp
    let m := m₆ p₀ n
    let J := J₆ m
    let T := T₆ m
    let k := k₆ n m
    have hn1 : 1 ≤ n := by omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : 0 < (n : ℝ) := by positivity
    have hmreal : (16 : ℝ) ≤ (m : ℝ) := hm16
    have hmpos : 0 < (m : ℝ) := by linarith
    have hJfloor : (m : ℝ) ^ (1 / 25 : ℝ) < (J : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hJlarge : 2000000 ≤ J := by
      have h04' : (4000000 : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := h04
      have : (2000000 : ℝ) < J := by nlinarith [hJfloor, h04']
      exact_mod_cast this.le
    have hJlower : (m : ℝ) ^ (1 / 25 : ℝ) / 2 ≤ J := by
      have h04' : (2 : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := by linarith [h04]
      nlinarith [hJfloor, h04']
    have hTceil : (T : ℝ) < (m : ℝ) ^ (1 / 1000 : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    have hmPowOne : 1 ≤ (m : ℝ) ^ (1 / 1000 : ℝ) := by
      rw [← Real.rpow_zero (m : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hmreal]) (by norm_num)
    have hTupper : (T : ℝ) ≤ 2 * (m : ℝ) ^ (1 / 1000 : ℝ) := by linarith [hTceil, hmPowOne]
    have h039 : (4 * 10 ^ 11 : ℝ) ≤ (m : ℝ) ^ (39 / 1000 : ℝ) := h039
    have hpowRel : (m : ℝ) ^ (1 / 25 : ℝ) =
        (m : ℝ) ^ (1 / 1000 : ℝ) * (m : ℝ) ^ (39 / 1000 : ℝ) := by
      rw [← Real.rpow_add hmpos]
      norm_num
    have hTsmall : (T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * J := by
      have h039mul := mul_le_mul_of_nonneg_right h039
        (by positivity : 0 ≤ (m : ℝ) ^ (1 / 1000 : ℝ))
      calc
        (T : ℝ) ≤ 2 * (m : ℝ) ^ (1 / 1000 : ℝ) := hTupper
        _ ≤ (1 / 10 ^ 11 : ℝ) * ((m : ℝ) ^ (1 / 25 : ℝ) / 2) := by
          rw [hpowRel]
          nlinarith [h039mul]
        _ ≤ (1 / 10 ^ 11 : ℝ) * J := by
          exact mul_le_mul_of_nonneg_left hJlower (by positivity)
    have hmUpper : (m : ℝ) ≤ 2 * (n : ℝ) ^ α := by
      have hceil : (m : ℝ) < (n : ℝ) ^ α + 1 := Nat.ceil_lt_add_one (by positivity)
      have hnPowOne : 1 ≤ (n : ℝ) ^ α := by
        rw [← Real.rpow_zero (n : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hnR (le_of_lt hα)
      linarith [hceil, hnPowOne]
    have hmle : m ≤ n := by
      change ⌈(n : ℝ) ^ α⌉₊ ≤ n
      rw [Nat.ceil_le]
      have hαle1 : α ≤ 1 := le_trans hαle (by norm_num)
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR hαle1
    have hTplus : (T : ℝ) + 2 ≤ m := by
      have hsqrt : (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) / 4 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
        nlinarith [hmreal]
      have hlowpow : (m : ℝ) ^ (1 / 1000 : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hmreal]) (by norm_num)
      nlinarith [hTceil, hsqrt, hlowpow, hmreal]
    have hlogM : Real.log (m : ℝ) ≤ Real.log 2 + α * Real.log n := by
      calc
        Real.log (m : ℝ) ≤ Real.log (2 * (n : ℝ) ^ α) :=
          Real.log_le_log hmpos hmUpper
        _ = Real.log 2 + α * Real.log n := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hnpos]
    have hlogT' : Real.log (T + 2) ≤ 2 * α * Real.log n := by
      calc
        Real.log (T + 2) ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by positivity) hTplus
        _ ≤ Real.log 2 + α * Real.log n := hlogM
        _ ≤ 2 * α * Real.log n := by nlinarith [hαlogn]
    have hkceil : κ₆ * (J : ℝ) * Real.log n ≤ (k : ℝ) := by
      dsimp [k, k₆]
      exact Nat.le_ceil _
    have hklarge : 12 ≤ k := by
      have hJreal : (2000000 : ℝ) ≤ J := by exact_mod_cast hJlarge
      have hJlog : (2000000 : ℝ) ≤ (J : ℝ) * Real.log n := by
        calc
          2000000 = 2000000 * 1 := by ring
          _ ≤ (J : ℝ) * Real.log n :=
            mul_le_mul hJreal hlogn (by norm_num) (by exact_mod_cast (Nat.zero_le J))
      have hklower : (200 : ℝ) ≤ (k : ℝ) := by
        have hk' := hkceil
        have hκ : κ₆ * 2000000 = 200 := by norm_num [κ₆]
        nlinarith [hk', hJlog, hκ]
      exact_mod_cast (show (12 : ℝ) ≤ (k : ℝ) by linarith)
    exact ⟨hJlarge, hTsmall, hlogT', hmle, hklarge, hn10⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hAll
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

end HypercubeRamsey.S06.Lane_q_s06_ev_a
