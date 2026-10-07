import HypercubeRamsey.PartC.SliceSolver
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s14_lik

open scoped BigOperators

/-- The squared tilt pays for two label densities; remaining labels use
    the tested deletion ratio. -/
theorem deletion_density_le (α β m n A B Z : ℝ) (j : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hm : 0 < m) (hn : 0 < n)
    (hB : 0 < B) (hZ : 0 < Z) (hA : α * B ≤ A)
    (hret : A / 2 ≤ Z) (hr : β * n ≤ m) (hj : 2 ≤ j) :
    m ^ 2 / Z / m ^ j ≤
      (2 / α) * (1 / β) ^ (j - 2) * (n ^ 2 / B / n ^ j) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hnormal : 1 / Z ≤ (2 / α) * (1 / B) := by
    have hAZ : α * B ≤ 2 * Z := by linarith
    have h : (1 : ℝ) / Z ≤ 2 / (α * B) :=
      (div_le_div_iff₀ hZ (mul_pos hα hB)).2 (by nlinarith only [hAZ])
    convert h using 1 <;> field_simp [hα.ne', hB.ne'] <;> ring
  have hinv : 1 / m ≤ (1 / β) * (1 / n) := by
    have h := one_div_le_one_div_of_le (mul_pos hβ hn) hr
    simpa [one_div_mul_one_div, mul_comm] using h
  have hp : (1 / m) ^ t ≤ ((1 / β) * (1 / n)) ^ t :=
    pow_le_pow_left₀ (by positivity) hinv t
  have hleft : m ^ 2 / Z / m ^ (2 + t) = (1 / Z) * (1 / m) ^ t := by
    rw [pow_add]
    simp only [div_pow, one_pow]
    field_simp [hm.ne', hZ.ne'] <;> ring
  have hright : (2 / α) * (1 / β) ^ (2 + t - 2) *
      (n ^ 2 / B / n ^ (2 + t)) =
      ((2 / α) * (1 / B)) * (((1 / β) * (1 / n)) ^ t) := by
    simp only [Nat.add_sub_cancel_left, pow_add, mul_pow, div_pow, one_pow]
    field_simp [hn.ne', hB.ne', hα.ne', hβ.ne'] <;> ring
  rw [hleft, hright]
  exact mul_le_mul hnormal hp (by positivity) (by positivity)


/-- TeX 14:115–121, retaining the `.24 a k` slack for the mixture cost. -/
theorem deletion_label_product_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p m n A B Z a K : ℝ) (f : ι → ℝ)
    (hp : 0 ≤ p) (hf : ∀ l ∈ s, 0 ≤ f l)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B) (hZ : 0 < Z)
    (hA : Real.exp ((-Real.log 4 + 0.4 * a) * K) * B ≤ A)
    (hret : A / 2 ≤ Z)
    (hr : Real.exp ((-Real.log 2 + 0.08 * a) * K) * n ≤ m)
    (hj : 2 ≤ s.card) :
    (p * m ^ 2 / Z) * (∏ l ∈ s, f l / m) ≤
      (2 * Real.exp (((Real.log 2 - 0.08 * a) * s.card - 0.24 * a) * K)) *
        ((p * n ^ 2 / B) * ∏ l ∈ s, f l / n) := by
  have hd := deletion_density_le
    (Real.exp ((-Real.log 4 + 0.4 * a) * K))
    (Real.exp ((-Real.log 2 + 0.08 * a) * K))
    m n A B Z s.card (Real.exp_pos _) (Real.exp_pos _)
    hm hn hB hZ hA hret hr hj
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hcoeff : (2 / Real.exp ((-Real.log 4 + 0.4 * a) * K)) *
      (1 / Real.exp ((-Real.log 2 + 0.08 * a) * K)) ^ (s.card - 2) =
      2 * Real.exp (((Real.log 2 - 0.08 * a) * s.card - 0.24 * a) * K) := by
    simp only [div_eq_mul_inv, one_mul, ← Real.exp_neg, ← Real.exp_nat_mul]
    rw [mul_assoc, ← Real.exp_add, hlog]
    congr 2
    rw [Nat.cast_sub hj]
    push_cast
    ring
  rw [hcoeff] at hd
  have hprod : 0 ≤ p * ∏ l ∈ s, f l :=
    mul_nonneg hp (Finset.prod_nonneg hf)
  have h := mul_le_mul_of_nonneg_right hd hprod
  simp only [Finset.prod_div_distrib, Finset.prod_const] at ⊢
  convert h using 1 <;> ring


/-- Reading distinct coordinates of a product law gives their product marginal. -/
theorem pi_query_probability {ι Ω α : Type*} [Fintype ι] [Fintype Ω]
    [Fintype α] [DecidableEq Ω] (P : Ω → FinLaw α)
    (q : ι → Ω) (hq : Function.Injective q) (a : ι → α) :
    (FinLaw.pi P).pr (fun x => (fun l => x (q l)) = a) =
      ∏ l, (P (q l)).w (a l) := by
  classical
  let C := fun z y => ∀ l, q l = z → y = a l
  let F := fun z y => if C z y then (P z).w y else 0
  have hterm (x : Ω → α) :
      (if (fun l => x (q l)) = a then ∏ z, (P z).w (x z) else 0) =
      ∏ z, F z (x z) := by
    by_cases hx : (fun l => x (q l)) = a
    · rw [if_pos hx]
      apply Finset.prod_congr rfl
      intro z _
      have hc : C z (x z) := by
        intro l hl
        rw [← hl]
        exact congrFun hx l
      simp [F, hc]
    · rw [if_neg hx]
      have hn : ∃ l, x (q l) ≠ a l := by
        by_contra hn
        apply hx
        funext l
        exact not_not.mp (not_exists.mp hn l)
      obtain ⟨l, hl⟩ := hn
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (q l))
      have hc : ¬ C (q l) (x (q l)) := fun h => hl (h l rfl)
      simp [F, hc]
  have hqueried (l : ι) : (∑ y, F (q l) y) = (P (q l)).w (a l) := by
    have hc (y : α) : C (q l) y ↔ y = a l := by
      constructor
      · intro h
        exact h l rfl
      · intro hy l' hl'
        rw [hq hl']
        exact hy
    simp [F, hc]
  have hunused (z : Ω) (hz : z ∉ Finset.univ.image q) : ∑ y, F z y = 1 := by
    have hc (y : α) : C z y := by
      intro l hl
      exact False.elim (hz (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩))
    simp only [F, if_pos (hc _)]
    exact (P z).sum_one
  unfold FinLaw.pr
  simp only [FinLaw.pi]
  simp_rw [hterm]
  rw [← Fintype.prod_sum]
  calc
    _ = ∏ z ∈ Finset.univ.image q, ∑ y, F z y := by
      symm
      exact Finset.prod_subset (Finset.subset_univ _)
        (fun z _ hz => hunused z hz)
    _ = ∏ l, ∑ y, F (q l) y := by
      rw [Finset.prod_image]
      exact fun l _ l' _ h => hq h
    _ = _ := by simp_rw [hqueried]


/-- The failed-list numerical estimate already pays the reference mixture. -/
theorem mixture_cost_le (B a K c5 c : ℝ) (h t : ℕ)
    (hh : 2 ≤ h) (ha : 0 ≤ a) (hasmall : a ≤ 1 / 10)
    (hK : 0 ≤ K) (hc5 : c5 ≤ 1 / 1000) (hB : 0 ≤ B)
    (hbudget : (2 : ℝ) ^ h *
      (B * (2 * (t + 1) * Real.exp (-c5 * a ^ 2 * K))) ^ h ≤
      Real.exp (-Real.rpow (h : ℝ) (1 + c))) :
    2 * B ≤ Real.exp (0.04 * a * K) := by
  let z := 2 * (B * (2 * (t + 1) * Real.exp (-c5 * a ^ 2 * K)))
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hpow : z ^ h ≤ 1 := by
    have he : Real.exp (-Real.rpow (h : ℝ) (1 + c)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (Real.rpow_nonneg (by positivity) _)
    simpa only [z, mul_pow] using hbudget.trans he
  have hz : z ≤ 1 := by
    have hn : h ≠ 0 := by omega
    exact (pow_le_one_iff_of_nonneg hz0 hn).mp hpow
  have hfactor : 2 * B * Real.exp (-c5 * a ^ 2 * K) ≤ 1 := by
    have ht : (1 : ℝ) ≤ 2 * (t + 1) := by
      have ht0 : (0 : ℝ) ≤ t := by positivity
      linarith
    have hb := mul_le_mul_of_nonneg_left ht
      (show 0 ≤ 2 * B * Real.exp (-c5 * a ^ 2 * K) by positivity)
    dsimp [z] at hz
    nlinarith only [hb, hz]
  have hbound : 2 * B ≤ Real.exp (c5 * a ^ 2 * K) := by
    have h := mul_le_mul_of_nonneg_right hfactor (Real.exp_pos (c5 * a ^ 2 * K)).le
    have he : Real.exp (-c5 * a ^ 2 * K) * Real.exp (c5 * a ^ 2 * K) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    calc
      2 * B = (2 * B * Real.exp (-c5 * a ^ 2 * K)) *
          Real.exp (c5 * a ^ 2 * K) := by
        rw [mul_assoc, he, mul_one]
      _ ≤ Real.exp (c5 * a ^ 2 * K) := by simpa only [one_mul] using h
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hcoef : c5 * a ^ 2 ≤ 0.04 * a := by
    have h := mul_le_mul_of_nonneg_right hc5 (sq_nonneg a)
    nlinarith only [h, ha, hasmall, mul_nonneg ha (sub_nonneg.mpr hasmall)]
  exact mul_le_mul_of_nonneg_right hcoef hK


/-- Coordinatewise cube translation. -/
def shift {d : ℕ} (s z : CubePos d) : CubePos d := fun l => Bool.xor (s l) (z l)

@[simp] theorem shift_shift {d : ℕ} (s z : CubePos d) : shift s (shift s z) = z := by
  funext l
  cases hs : s l <;> cases hz : z l <;> simp [shift, hs, hz]

def shiftEquiv {d : ℕ} (s : CubePos d) : CubePos d ≃ CubePos d where
  toFun := shift s
  invFun := shift s
  left_inv := shift_shift s
  right_inv := shift_shift s

@[simp] theorem shift_flip {d : ℕ} (s z : CubePos d) (j : Fin d) :
    shift s (flipPos z j) = flipPos (shift s z) j := by
  funext l
  by_cases hl : l = j
  · subst l
    cases hs : s j <;> cases hz : z j <;> simp [shift, flipPos, hs, hz]
  · simp [shift, flipPos, hl]

@[simp] theorem shift_distance {d : ℕ} (s u v : CubePos d) :
    hammingDist (shift s u) (shift s v) = hammingDist u v := by
  unfold hammingDist
  congr 1
  ext l
  cases hs : s l <;> cases hu : u l <;> cases hv : v l <;> simp [shift, hs, hu, hv]

private def paritySum {d : ℕ} (z : CubePos d) : ZMod 2 :=
  ∑ l, if z l = true then 1 else 0

private theorem even_iff_paritySum {d : ℕ} (z : CubePos d) :
    IsEvenRole z ↔ paritySum z = 0 := by
  unfold IsEvenRole
  rw [← ZMod.natCast_eq_zero_iff_even]
  have h : paritySum z = ((Finset.univ.filter fun l => z l = true).card : ZMod 2) := by
    simp [paritySum]
  rw [h]

theorem shift_even {d : ℕ} (s z : CubePos d) (hs : IsEvenRole s) :
    IsEvenRole (shift s z) ↔ IsEvenRole z := by
  have hsum : paritySum (shift s z) = paritySum s + paritySum z := by
    unfold paritySum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    cases hs : s l <;> cases hz : z l <;> norm_num [shift, hs, hz] <;> decide
  rw [even_iff_paritySum, hsum, (even_iff_paritySum s).mp hs, zero_add]
  exact (even_iff_paritySum z).symm

theorem shift_syndrome {d : ℕ} (s z : CubePos d) :
    wordSyndrome (shift s z) = wordSyndrome s + wordSyndrome z := by
  funext j
  change (∑ l, if shift s z l = true ∧ l.val.testBit j = true then (1 : ZMod 2) else 0) =
    (∑ l, if s l = true ∧ l.val.testBit j = true then (1 : ZMod 2) else 0) +
      ∑ l, if z l = true ∧ l.val.testBit j = true then (1 : ZMod 2) else 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  cases hs : s l <;> cases hz : z l <;> cases hb : l.val.testBit j <;>
    norm_num [shift, hs, hz, hb] <;> decide

/-- Compose a uniformly sampled permutation with a fixed permutation. -/
def postcompose {α : Type*} (e : α ≃ α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.trans e
  invFun σ := σ.trans e.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

def precompose {α : Type*} (e : α ≃ α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := e.trans σ
  invFun σ := e.symm.trans σ
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

end HypercubeRamsey.Lane_sol_s14_lik




