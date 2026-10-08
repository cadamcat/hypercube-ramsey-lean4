import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.Tools.HeavyTrunc

/-!
# q-s10-d7 finite posterior utilities

The even-row proof uses the generic heavy-coordinate truncation estimate for the
posterior law on candidate tuples.
-/

namespace HypercubeRamsey.Lane_q_s10_d7

open Classical
open Filter
open Topology
open scoped BigOperators

private theorem eventually_power_gap {a b c : ℝ} (hab : a < b) (_hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hnlarge, htend.eventually_gt_atTop c] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring

theorem evenRow_scales_eventually (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    ∀ᶠ n : ℕ in atTop,
      1000000000000000 ≤ n ∧
      200 * (n : ℝ) ^ δ < (n : ℝ) ^ (-δ) * n ∧
      200 * Real.log 2 < (n : ℝ) ^ (-δ) * n ∧
      200 < (n : ℝ) ^ (-δ) * (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) ∧
      10000 < (n : ℝ) ^ (-δ) * (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
  have hδhalf : δ < (1 : ℝ) / 2 := by linarith
  have hδgap : δ < 1 - δ := by linarith
  have hgap1 := eventually_power_gap hδgap (by norm_num : (0 : ℝ) < 200)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap2 := eventually_power_gap (by linarith : (0 : ℝ) < 1 - δ)
    (mul_pos (by norm_num : (0 : ℝ) < 200) hlog2)
  have hgap3 := eventually_power_gap (by positivity : (0 : ℝ) < 299 * δ)
    (by norm_num : (0 : ℝ) < 10000)
  have hlarge : ∀ᶠ n : ℕ in atTop, 1000000000000000 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1000000000000000,
      fun _ hn => hn⟩
  filter_upwards [hlarge, hgap1, hgap2, hgap3] with n hlarge hgap1 hgap2 hgap3
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have haId : (n : ℝ) ^ (-δ) * (n : ℝ) = (n : ℝ) ^ (1 - δ) := by
    calc
      (n : ℝ) ^ (-δ) * (n : ℝ) = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-δ + 1) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (1 - δ) := by congr 1 <;> ring
  have hkLower : (n : ℝ) ^ (300 * δ) ≤
      (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
    dsimp [HypercubeRamsey.S10.p10_1kTupleListLength]
    exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ (300 * δ)))
  have hakLower : (n : ℝ) ^ (299 * δ) ≤
      (n : ℝ) ^ (-δ) *
        (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
    have hpow : (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) =
        (n : ℝ) ^ (299 * δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    calc
      (n : ℝ) ^ (299 * δ) =
          (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) := hpow.symm
      _ ≤ (n : ℝ) ^ (-δ) *
          (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) :=
        mul_le_mul_of_nonneg_left hkLower (Real.rpow_nonneg hnpos.le _)
  refine ⟨hlarge, ?_, ?_, ?_⟩
  · rw [haId]
    exact hgap1
  · rw [haId]
    simpa [Real.rpow_zero] using hgap2
  · exact ⟨lt_trans (by norm_num : (200 : ℝ) < 10000)
        (lt_of_lt_of_le (by simpa [Real.rpow_zero] using hgap3) hakLower),
      lt_of_lt_of_le (by simpa [Real.rpow_zero] using hgap3) hakLower⟩

theorem exp_quartic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 / 256 ≤ Real.exp x := by
  have hlin : 1 + x / 4 ≤ Real.exp (x / 4) := by
    have := Real.add_one_le_exp (x / 4)
    linarith
  have hpow₁ : (1 + x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) hlin 4
  have hpow₂ : (x / 4) ^ 4 ≤ (1 + x / 4) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hexp : (Real.exp (x / 4)) ^ 4 = Real.exp x := by
    calc
      (Real.exp (x / 4)) ^ 4 = Real.exp (4 * (x / 4)) := by
        rw [← Real.exp_nat_mul]
        congr 1
      _ = Real.exp x := by congr 1 <;> ring
  calc
    x ^ 4 / 256 = (x / 4) ^ 4 := by ring
    _ ≤ (1 + x / 4) ^ 4 := hpow₂
    _ ≤ (Real.exp (x / 4)) ^ 4 := hpow₁
    _ = Real.exp x := hexp

theorem averageCoordinateMarginal_sum_one {N k : ℕ}
    (P : HypercubeRamsey.FinProb (Fin k → Fin N)) (hk : 0 < k) :
    ∑ x : Fin N, HypercubeRamsey.averageCoordinateMarginal P x = 1 := by
  classical
  have hcoord (i : Fin k) :
      ∑ x : Fin N, P.pr (fun ω => ω i = x) = 1 := by
    unfold HypercubeRamsey.FinProb.pr
    rw [Finset.sum_comm]
    have hrow (ω : Fin k → Fin N) :
        ∑ x : Fin N, @ite ℝ (ω i = x) (Classical.propDecidable _) (P.w ω) 0 = P.w ω := by
      rw [Finset.sum_eq_single (ω i)]
      · simp
      · intro x hx hne
        have hneq : ¬ ω i = x := fun he => hne he.symm
        simp [hneq]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    calc
      ∑ ω : (Fin k → Fin N), ∑ x : Fin N,
          @ite ℝ (ω i = x) (Classical.propDecidable _) (P.w ω) 0 = ∑ ω, P.w ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact hrow ω
      _ = 1 := P.sum_eq_one
  unfold HypercubeRamsey.averageCoordinateMarginal
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    (k : ℝ)⁻¹ * ∑ i : Fin k, ∑ x : Fin N, P.pr (fun ω => ω i = x) =
        (k : ℝ)⁻¹ * ∑ i : Fin k, 1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hcoord i
    _ = 1 := by simp [Nat.cast_ne_zero.mpr hk.ne']

theorem averageCoordinateMarginal_nonneg {N k : ℕ}
    (P : HypercubeRamsey.FinProb (Fin k → Fin N)) (x : Fin N) :
    0 ≤ HypercubeRamsey.averageCoordinateMarginal P x := by
  classical
  unfold HypercubeRamsey.averageCoordinateMarginal
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
  apply Finset.sum_nonneg
  intro i hi
  unfold HypercubeRamsey.FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

theorem finprob_expect_nonneg {α : Type*} [Fintype α]
    (P : HypercubeRamsey.FinProb α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
  unfold HypercubeRamsey.FinProb.expect
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (P.nonneg x) (hf x)

def completeSubprob {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x ≤ 1) :
    HypercubeRamsey.FinProb (Option α) where
  w x := match x with
    | none => 1 - ∑ y, w y
    | some y => w y
  nonneg x := by
    cases x with
    | none => exact sub_nonneg.mpr hsum
    | some y => exact hw y
  sum_eq_one := by
    rw [Fintype.sum_option]
    simp

theorem pi_weight_split_q_s10_d7 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, HypercubeRamsey.FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
        ∏ i : {i // i ∉ s}, (P i.1).w (ω i.1) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 := by
        exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

theorem pi_expect_split_q_s10_d7 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, HypercubeRamsey.FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (HypercubeRamsey.FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (HypercubeRamsey.FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (HypercubeRamsey.FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_q_s10_d7 P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

theorem finprob_prod_expect_q_s10_d7 {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinProb α) (Q : HypercubeRamsey.FinProb β) (f : α → β → ℝ) :
    (HypercubeRamsey.FinProb.prod P Q).expect (fun ab => f ab.1 ab.2) =
      P.expect (fun a => Q.expect (f a)) := by
  classical
  simp only [HypercubeRamsey.FinProb.expect, HypercubeRamsey.FinProb.prod,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem map_weight_ge_image_q_s10_d7 {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : HypercubeRamsey.FinProb α) (f : α → β) (a : α) :
    P.w a ≤ (HypercubeRamsey.FinProb.map P f).w (f a) := by
  classical
  unfold HypercubeRamsey.FinProb.map
  change P.w a ≤ ∑ x ∈ Finset.univ, if f x = f a then P.w x else 0
  simpa using (Finset.single_le_sum
    (f := fun x => if f x = f a then P.w x else 0)
    (s := Finset.univ)
    (by
      intro x hx
      split_ifs
      · exact P.nonneg x
      · exact le_rfl)
    (Finset.mem_univ a))

theorem bind_map_snd_weight_q_s10_d7 {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinProb α) (K : α → HypercubeRamsey.FinProb β) (b : β) :
    (HypercubeRamsey.FinProb.map (HypercubeRamsey.FinProb.bind P K) Prod.snd).w b =
      ∑ a, P.w a * (K a).w b := by
  classical
  change (∑ x : α × β,
      if x.2 = b then P.w x.1 * (K x.1).w x.2 else 0) = _
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', eq_comm]

theorem uniform_expect_q_s10_d7 {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    (HypercubeRamsey.FinProb.uniform s hs).expect f =
      (∑ x ∈ s, f x) / s.card := by
  classical
  simp only [HypercubeRamsey.FinProb.expect, HypercubeRamsey.FinProb.uniform,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

theorem finprob_expect_swap_q_s10_d7 {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinProb α) (Q : HypercubeRamsey.FinProb β)
    (f : α → β → ℝ) :
    P.expect (fun a => Q.expect (fun b => f a b)) =
      Q.expect (fun b => P.expect (fun a => f a b)) := by
  classical
  simp only [HypercubeRamsey.FinProb.expect]
  calc
    (∑ a, P.w a * ∑ b, Q.w b * f a b) =
        ∑ a, ∑ b, P.w a * Q.w b * f a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ b, ∑ a, P.w a * Q.w b * f a b := by rw [Finset.sum_comm]
    _ = ∑ b, Q.w b * ∑ a, P.w a * f a b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

theorem finprob_expect_congr_q_s10_d7 {α : Type*} [Fintype α]
    (P : HypercubeRamsey.FinProb α) (f g : α → ℝ) (h : ∀ x, f x = g x) :
    P.expect f = P.expect g := by
  classical
  unfold HypercubeRamsey.FinProb.expect
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x]

theorem pi_expect_prod_q_s10_d7 {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, HypercubeRamsey.FinProb (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (HypercubeRamsey.FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  unfold HypercubeRamsey.FinProb.expect HypercubeRamsey.FinProb.pi
  change (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) *
      ∏ i, f i (ω i)) = ∏ i, ∑ x : Ω i, (P i).w x * f i x
  calc
    (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) =
        ∑ ω : (∀ i, Ω i), ∏ i, (P i).w (ω i) * f i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ x : Ω i, (P i).w x * f i x :=
      (Fintype.prod_sum (fun i x => (P i).w x * f i x)).symm

theorem pi_expect_split_at_q_s10_d7 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω] (P : ι → HypercubeRamsey.FinProb Ω) (c : ι)
    (f : (ι → Ω) → ℝ) :
    (HypercubeRamsey.FinProb.pi P).expect f =
      ∑ r : ({i : ι // i ≠ c} → Ω),
        (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w r *
          ∑ x : Ω, (P c).w x *
            f (fun i => if hi : i = c then x else r ⟨i, hi⟩) := by
  classical
  let S : Finset ι := {c}
  let AType := ∀ i : {i : ι // i ∈ S}, Ω
  let RType := ∀ i : {i : ι // i ∉ S}, Ω
  let eA : AType ≃ Ω := {
    toFun := fun a => a ⟨c, by simp [S]⟩
    invFun := fun x => fun _ => x
    left_inv := by
      intro a
      funext i
      have hi : i.1 = c := Finset.mem_singleton.mp (by simpa [S] using i.2)
      change a ⟨c, Finset.mem_singleton_self c⟩ = a i
      exact congrArg a (Subtype.ext hi.symm)
    right_inv := by intro x; rfl
  }
  let eR : RType ≃ ({i : ι // i ≠ c} → Ω) := {
    toFun := fun r i => r ⟨i.1, by simpa [S] using i.2⟩
    invFun := fun r i => r ⟨i.1, by simpa [S] using i.2⟩
    left_inv := by intro r; funext i; rfl
    right_inv := by intro r; funext i; rfl
  }
  let E := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Ω)
  have hE (x : Ω) (r : {i : ι // i ≠ c} → Ω) :
      E.symm (eA.symm x, eR.symm r) =
        (fun i => if hi : i = c then x else r ⟨i, hi⟩) := by
    funext i
    by_cases hi : i = c
    · subst i
      simp [E, eA, eR, S]
    · simp [E, eA, eR, S, hi]
  have hE' (x : Ω) (r : RType) :
      E.symm (eA.symm x, r) = fun i => if hi : i = c then x else (eR r) ⟨i, hi⟩ := by
    rw [← eR.left_inv r]
    exact hE x (eR r)
  have hsplit := pi_expect_split_q_s10_d7 P S f
  rw [Finset.sum_comm] at hsplit
  have hAweight (x : Ω) :
      (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∈ S} => P i.1)).w
          (eA.symm x) = (P c).w x := by
    simp [AType, eA, S, HypercubeRamsey.FinProb.pi]
  let eIndex : {i : ι // i ∉ S} ≃ {i : ι // i ≠ c} := {
    toFun := fun i => ⟨i.1, by simpa [S] using i.2⟩
    invFun := fun i => ⟨i.1, by simpa [S] using i.2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hRweight' (r : RType) :
      (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∉ S} => P i.1)).w r =
        (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w (eR r) := by
    unfold HypercubeRamsey.FinProb.pi
    calc
      ∏ i : {i : ι // i ∉ S}, (P i.1).w (r i) =
          ∏ i : {i : ι // i ∉ S}, (P i.1).w ((eR r) (eIndex i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [eIndex, eR]
      _ = ∏ i : {i : ι // i ≠ c}, (P i.1).w ((eR r) i) :=
        Fintype.prod_equiv eIndex _ _ (by intro i; rfl)
  calc
    (HypercubeRamsey.FinProb.pi P).expect f =
        ∑ r : RType, ∑ a : AType,
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∈ S} => P i.1)).w a *
            (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∉ S} => P i.1)).w r *
              f (E.symm (a, r)) := hsplit
    _ = ∑ r : RType, ∑ x : Ω,
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∈ S} => P i.1)).w (eA.symm x) *
            (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∉ S} => P i.1)).w r *
              f (E.symm (eA.symm x, r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        symm
        exact Equiv.sum_comp eA.symm (fun a =>
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∈ S} => P i.1)).w a *
            (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ∉ S} => P i.1)).w r *
              f (E.symm (a, r)))
    _ = ∑ r : RType, ∑ x : Ω,
          (P c).w x *
            (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w (eR r) *
              f (fun i => if hi : i = c then x else (eR r) ⟨i, hi⟩) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro x hx
        rw [hAweight x, hRweight' r, hE' x r]
    _ = ∑ r : RType,
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w (eR r) *
            ∑ x : Ω, (P c).w x * f (fun i => if hi : i = c then x else (eR r) ⟨i, hi⟩) := by
        apply Finset.sum_congr rfl
        intro r hr
        calc
          (∑ x : Ω, (P c).w x *
              (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w (eR r) *
                f (fun i => if hi : i = c then x else (eR r) ⟨i, hi⟩)) =
            ∑ x : Ω,
              (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w (eR r) *
                ((P c).w x * f (fun i => if hi : i = c then x else (eR r) ⟨i, hi⟩)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
          _ = _ := by rw [Finset.mul_sum]
    _ = ∑ r : ({i : ι // i ≠ c} → Ω),
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w r *
            ∑ x : Ω, (P c).w x * f (fun i => if hi : i = c then x else r ⟨i, hi⟩) := by
        exact Equiv.sum_comp eR (fun r =>
          (HypercubeRamsey.FinProb.pi (fun i : {i : ι // i ≠ c} => P i.1)).w r *
            ∑ x : Ω, (P c).w x * f (fun i => if hi : i = c then x else r ⟨i, hi⟩))

theorem heightLevels_le_cube (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) {n : ℕ} (hn : 3 ≤ n) :
    (HypercubeRamsey.S10.p10_1kHeightParams n n δ).H + 1 ≤ n ^ 3 := by
  classical
  let R : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ δ⌉₊
  let T : ℕ := ⌈(n : ℝ) ^ (1 - 8 * δ)⌉₊
  let P : ℕ := ⌈(1 / δ)⌉₊
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hδle : δ ≤ 1 := by linarith
  have hpowδlow : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR hδ.le
  have hδP : 1 ≤ δ * (P : ℝ) := by
    have hceil := Nat.le_ceil (1 / δ)
    have hmul := mul_le_mul_of_nonneg_left (show (1 / δ : ℝ) ≤ (P : ℝ) from hceil) hδ.le
    have hcancel : δ * (1 / δ) = 1 := by field_simp [ne_of_gt hδ]
    nlinarith
  have hpowP : (n : ℝ) ≤ (n : ℝ) ^ (δ * (P : ℝ)) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (δ * (P : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hnR hδP
  have hMpow : (n : ℝ) ^ (δ * (P : ℝ)) ≤ (M : ℝ) ^ P := by
    have hMbase : (n : ℝ) ^ δ ≤ (M : ℝ) := by
      have hceil := Nat.le_ceil ((n : ℝ) ^ δ)
      dsimp [M]
      exact le_trans hceil (Nat.cast_le.mpr (le_max_right 2 ⌈(n : ℝ) ^ δ⌉₊))
    calc
      (n : ℝ) ^ (δ * (P : ℝ)) = ((n : ℝ) ^ δ) ^ P := by
        rw [Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)), Real.rpow_natCast]
      _ ≤ (M : ℝ) ^ P := by
        exact pow_le_pow_left₀ (by positivity) hMbase P
  have hTargetPow : (n : ℝ) ^ (1 - 8 * δ) ≤ (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - 8 * δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
      _ = (n : ℝ) := Real.rpow_one _
  have hTle : T ≤ M ^ P := by
    dsimp [T]
    rw [Nat.ceil_le]
    exact le_trans hTargetPow (le_trans hpowP (by exact_mod_cast hMpow))
  have hM : 2 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hR : 1 ≤ R := by dsimp [R]; exact le_max_left _ _
  have hScaleExists : ∃ i : ℕ, T ≤ M ^ i * R := ⟨P, by
    exact le_trans hTle (Nat.le_mul_of_pos_right _ (by omega : 0 < R))⟩
  let i : ℕ := Nat.find hScaleExists
  have hi : i ≤ P := Nat.find_min' hScaleExists (by
    exact le_trans hTle (Nat.le_mul_of_pos_right _ (by omega : 0 < R)))
  have hspec : T ≤ M ^ i * R := Nat.find_spec hScaleExists
  have htop : (HypercubeRamsey.S10.p10_1kHeightParams n n δ).H = M ^ i * R := by
    change HypercubeRamsey.topScale n δ (8 * δ) = M ^ i * R
    dsimp [HypercubeRamsey.topScale, M, R, T, i]
  have htopBound : (M ^ i * R : ℕ) ≤ R + M * T := by
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hprev : ¬ T ≤ M ^ (i - 1) * R := by
        intro hh
        have := Nat.find_min' hScaleExists hh
        omega
      have hprevlt : M ^ (i - 1) * R < T := Nat.lt_of_not_ge hprev
      have hpow : M ^ i * R = M * (M ^ (i - 1) * R) := by
        calc
          M ^ i * R = M ^ (i - 1 + 1) * R := by rw [Nat.sub_add_cancel hi1]
          _ = M ^ (i - 1) * M * R := by rw [pow_succ]
          _ = M * (M ^ (i - 1) * R) := by ac_rfl
      rw [hpow]
      have hlt : M * (M ^ (i - 1) * R) < M * T :=
        Nat.mul_lt_mul_of_pos_left hprevlt (by omega)
      omega
  have hlog : 0 ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ (n : ℝ) := by
    refine ⟨Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)), ?_⟩
    exact Real.log_le_self (le_trans (by norm_num) hnR)
  have hRreal : (R : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
    dsimp [R]
    rw [Nat.cast_max]
    apply max_le
    · norm_num
    · have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (n : ℝ)))
      have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
        nlinarith [hlog.1, hlog.2]
      nlinarith [hceil.le, hsq]
  have hMreal : (M : ℝ) ≤ 2 * (n : ℝ) ^ δ := by
    dsimp [M]
    rw [Nat.cast_max]
    apply max_le
    · calc
        (2 : ℝ) = 2 * 1 := by ring
        _ ≤ 2 * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_left hpowδlow (by norm_num)
    · have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le δ)
      exact le_trans hceil.le (by nlinarith [hpowδlow])
  have hTreal : (T : ℝ) ≤ 2 * (n : ℝ) ^ (1 - 8 * δ) := by
    dsimp [T]
    have hpowlow : 1 ≤ (n : ℝ) ^ (1 - 8 * δ) :=
      Real.one_le_rpow hnR (by linarith [hδsmall])
    have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le (1 - 8 * δ))
    exact le_trans hceil.le (by nlinarith [hpowlow])
  have hprodReal : (M : ℝ) * T ≤ 4 * (n : ℝ) := by
    have hmul := mul_le_mul hMreal hTreal (by positivity) (by positivity)
    have hpowMul : (n : ℝ) ^ δ * (n : ℝ) ^ (1 - 8 * δ) =
        (n : ℝ) ^ (1 - 7 * δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    calc
      (M : ℝ) * T ≤ 4 * ((n : ℝ) ^ δ * (n : ℝ) ^ (1 - 8 * δ)) := by nlinarith
      _ = 4 * (n : ℝ) ^ (1 - 7 * δ) := by rw [hpowMul]
      _ ≤ 4 * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          (n : ℝ) ^ (1 - 7 * δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hδ])
          _ = (n : ℝ) := Real.rpow_one _
  have hsumReal : (R : ℝ) + (M : ℝ) * T + 1 ≤ (n : ℝ) ^ 3 := by
    have hR' : (R : ℝ) ≤ (n : ℝ) ^ 2 + 1 := hRreal
    have hM' : (M : ℝ) * T ≤ 4 * (n : ℝ) := hprodReal
    nlinarith [show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
  have hnat : R + M * T + 1 ≤ n ^ 3 := by exact_mod_cast hsumReal
  rw [htop]
  exact le_trans (Nat.add_le_add_right htopBound 1) hnat

theorem natCube_le_twoPow_eventually :
    ∀ᶠ n : ℕ in atTop, n ^ 3 ≤ 2 ^ n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 3 / (2 : ℝ) ^ n < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hev] with n h
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  exact_mod_cast (le_of_lt ((div_lt_one hden).mp h))

end HypercubeRamsey.Lane_q_s10_d7
