import HypercubeRamsey.PartC.SliceSolver
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Height.Device
import HypercubeRamsey.S14.Construction_q_s14_post

namespace HypercubeRamsey.Lane_sol_s14_lik

open scoped BigOperators
open Classical

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

/-- A greedy disjoint-family scan commutes with renaming its ground set. -/
theorem greedy_scan_map {C : Type*} [Fintype C] [DecidableEq C] (e : C ≃ C)
    (items : List (Finset C)) (bad bad' : Finset C → Prop)
    (hbad : ∀ S, bad' (S.map e.toEmbedding) ↔ bad S) :
    (items.map (fun S => S.map e.toEmbedding)).foldl
      (fun A S => if bad' S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) (∅ : Finset (Finset C)) =
    (items.foldl
      (fun A S => if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A) (∅ : Finset (Finset C))).map
        (Equiv.finsetCongr e).toEmbedding := by
  classical
  let m := (Equiv.finsetCongr e).toEmbedding
  let f := fun (A : Finset (Finset C)) S =>
    if bad S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A
  let f' := fun (A : Finset (Finset C)) S =>
    if bad' S ∧ ∀ S' ∈ A, Disjoint S S' then insert S A else A
  have hcond (A : Finset (Finset C)) (S : Finset C) :
      (bad' (S.map e.toEmbedding) ∧
        ∀ S' ∈ A.map m, Disjoint (S.map e.toEmbedding) S') ↔
      (bad S ∧ ∀ S' ∈ A, Disjoint S S') := by
    rw [hbad]
    constructor
    · rintro ⟨hb, hd⟩
      refine ⟨hb, ?_⟩
      intro S' hS'
      exact (Finset.disjoint_map e.toEmbedding).mp
        (hd _ (Finset.mem_map.mpr ⟨S', hS', rfl⟩))
    · rintro ⟨hb, hd⟩
      refine ⟨hb, ?_⟩
      intro S' hS'
      obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_map.mp hS'
      exact (Finset.disjoint_map e.toEmbedding).mpr (hd S₀ hS₀)
  have hstep (A : Finset (Finset C)) (S : Finset C) :
      f' (A.map m) (S.map e.toEmbedding) = (f A S).map m := by
    dsimp [f, f']
    simp only [hcond A S]
    split_ifs <;> simp [m, Equiv.finsetCongr]
  have hscan (A : Finset (Finset C)) :
      (items.map (fun S => S.map e.toEmbedding)).foldl f' (A.map m) =
        (items.foldl f A).map m := by
    induction items generalizing A with
    | nil => rfl
    | cons S items ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [hstep]
      exact ih _
  simpa only [Finset.map_empty] using hscan ∅

/-- Rename a height-device experiment by a cube isometry. -/
theorem bad_transport (p : HDParams) (e : CubePos p.d ≃ CubePos p.d)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (hd : ∀ x y, hammingDist (e x) (e y) = hammingDist x y)
    (hp : ∀ c, P' (e c.1, c.2) = P c)
    (ha : ∀ c, A' (e c.1, c.2) = A c)
    (he : ∀ v j, E' (e v) j = (E v j).map (Equiv.prodCongr e (Equiv.refl _)).toEmbedding)
    (v : CubePos p.d) (j : Fin (p.H + 1)) :
    p.Bad P' A' E' (e v) j ↔ p.Bad P A E v j := by
  classical
  have hnone : (∀ c ∈ E' (e v) j, A' c = false) ↔ (∀ c ∈ E v j, A c = false) := by
    rw [he]
    constructor
    · intro hn c hc
      have h := hn _ (Finset.mem_map.mpr ⟨c, hc, rfl⟩)
      change A' (e c.1, c.2) = false at h
      rwa [ha] at h
    · intro hn c hc
      obtain ⟨c0, hc0, heq⟩ := Finset.mem_map.mp hc
      rw [← heq]
      change A' (e c0.1, c0.2) = false
      rw [ha]
      exact hn c0 hc0
  have hcrowd : (Finset.univ.filter fun u : CubePos p.d =>
      P' (u, j) = true ∧ A' (u, j) = true ∧ hammingDist u (e v) ≤ p.r + p.D) =
      (Finset.univ.filter fun u : CubePos p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ hammingDist u v ≤ p.r + p.D).map e.toEmbedding := by
    ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv, Equiv.symm_apply_apply, hd]
    rw [hp (u, j), ha (u, j)]
  unfold HDParams.Bad
  rw [hnone, hcrowd, Finset.card_map]

theorem reach_transport (p : HDParams) (e : CubePos p.d ≃ CubePos p.d)
    (Sites Sites' : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (hd : ∀ x y, hammingDist (e x) (e y) = hammingDist x y)
    (hs : ∀ v, e v ∈ Sites' ↔ v ∈ Sites)
    (hb : ∀ v j, p.BadN P' A' E' (e v) j ↔ p.BadN P A E v j)
    (q u : CubePos p.d) (R j : ℕ) :
    p.Reach Sites' P' A' E' (e q) R (e u) j ↔ p.Reach Sites P A E q R u j := by
  constructor
  · intro h
    have aux : ∀ u' j, p.Reach Sites' P' A' E' (e q) R u' j →
        p.Reach Sites P A E q R (e.symm u') j := by
      intro u' j h
      induction h with
      | start v hv hr =>
        apply HDParams.Reach.start
        · exact (hs _).mp (by simpa using hv)
        · simpa only [← hd (e.symm v) q, Equiv.apply_symm_apply] using hr
      | up v j hj hr hb' ih =>
        exact HDParams.Reach.up _ _ hj ih ((hb (e.symm v) j).mp (by simpa using hb'))
      | down v v' j hr hv' hd' hn ih =>
        apply HDParams.Reach.down _ _ _ ih
        · exact (hs _).mp (by simpa using hv')
        · simpa only [← hd (e.symm v') q, Equiv.apply_symm_apply] using hd'
        · simpa only [← hd (e.symm v) (e.symm v'), Equiv.apply_symm_apply] using hn
    simpa only [Equiv.symm_apply_apply] using aux _ _ h
  · intro h
    induction h with
    | start u hu hr => exact HDParams.Reach.start _ ((hs u).mpr hu) (by simpa [hd] using hr)
    | up u j hj hr hb' ih => exact HDParams.Reach.up _ _ hj ih ((hb u j).mpr hb')
    | down u u' j hr hu' hd' hn ih =>
      exact HDParams.Reach.down _ _ _ ih ((hs u').mpr hu') (by simpa [hd] using hd')
        (by simpa [hd] using hn)

theorem height_transport (p : HDParams) (e : CubePos p.d ≃ CubePos p.d)
    (Sites Sites' : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (hd : ∀ x y, hammingDist (e x) (e y) = hammingDist x y)
    (hs : ∀ v, e v ∈ Sites' ↔ v ∈ Sites)
    (hb : ∀ v j, p.BadN P' A' E' (e v) j ↔ p.BadN P A E v j)
    (q : CubePos p.d) (R : ℕ) :
    p.height Sites' P' A' E' R (e q) = p.height Sites P A E R q := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => reach_transport p e Sites Sites' P A P' A' E E' hd hs hb q q R j

/-- Distinct priorities remove the choice of a witness from selection. -/
theorem selection_transport (p : HDParams) (e : CubePos p.d ≃ CubePos p.d)
    (Sites Sites' : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (τ τ' : p.Ties) (R : ℕ)
    (hh : ∀ v, p.height Sites' P' A' E' R (e v) = p.height Sites P A E R v)
    (hb : ∀ v j, p.Bad P' A' E' (e v) j ↔ p.Bad P A E v j)
    (ha : ∀ c, A' (e c.1, c.2) = A c)
    (he : ∀ v j, E' (e v) j = (E v j).map (Equiv.prodCongr e (Equiv.refl _)).toEmbedding)
    (ht : ∀ v j c, p.priority τ' (e v, j) (e c.1, c.2) = p.priority τ (v, j) c)
    (v : CubePos p.d) :
    p.selectionAt Sites' P' A' E' τ' R (e v) =
      (p.selectionAt Sites P A E τ R v).map (Equiv.prodCongr e (Equiv.refl _)) := by
  classical
  let ec := Equiv.prodCongr e (Equiv.refl (Fin (p.H + 1)))
  have hactive (j : Fin (p.H + 1)) :
      (E' (e v) j).filter (fun c => A' c = true) =
      ((E v j).filter fun c => A c = true).map ec.toEmbedding := by
    rw [he]
    change ((E v j).map ec.toEmbedding).filter (fun c => A' c = true) = _
    ext c
    obtain ⟨c, rfl⟩ := ec.surjective c
    simp only [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    change (c ∈ E v j ∧ A' (e c.1, c.2) = true) ↔ (c ∈ E v j ∧ A c = true)
    rw [ha]
  have hprior (j : Fin (p.H + 1)) :
      ((E' (e v) j).filter fun c => A' c = true).image (p.priority τ' (e v, j)) =
      ((E v j).filter fun c => A c = true).image (p.priority τ (v, j)) := by
    rw [hactive]
    rw [Finset.map_eq_image, Finset.image_image]
    simp only [Function.comp_def]
    congr 1
    funext c
    exact ht v j c
  unfold HDParams.selectionAt
  simp only [hh, hb, hprior]
  split_ifs with hj hbad hne <;> simp only [Option.map_none, Option.map_some]
  all_goals try rfl
  apply congrArg some
  apply ((τ' (e v, ⟨p.height Sites P A E R v, by omega⟩)).injective.comp
    (Fintype.equivFin p.Loc).injective)
  change p.priority τ' (e v, ⟨p.height Sites P A E R v, by omega⟩) _ =
    p.priority τ' (e v, ⟨p.height Sites P A E R v, by omega⟩) _
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [ht]
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E R v, by omega⟩
  let active := (E v j).filter fun c => A c = true
  let active' := (E' (e v) j).filter fun c => A' c = true
  let priorities := active.image (p.priority τ (v, j))
  have hne' : priorities.Nonempty := hne
  let q0 := priorities.min' hne'
  have hm₁ : ∃ c, c ∈ active' ∧ p.priority τ' (e v, j) c = q0 := by
    apply Finset.mem_image.mp
    rw [show active'.image (p.priority τ' (e v, j)) = priorities from hprior j]
    exact Finset.min'_mem priorities hne'
  have hm₂ : ∃ c, c ∈ active ∧ p.priority τ (v, j) c = q0 :=
    Finset.mem_image.mp (Finset.min'_mem priorities hne')
  change p.priority τ' (e v, j) (Classical.choose hm₁) =
    p.priority τ (v, j) (Classical.choose hm₂)
  exact (Classical.choose_spec hm₁).2.trans (Classical.choose_spec hm₂).2.symm

theorem pr_fibers {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (P : FinLaw Ω) (f : Ω → Y) (A : Y → Prop) :
    P.pr (fun ω => A (f ω)) = ∑ y, if A y then P.pr (fun ω => f ω = y) else 0 := by
  classical
  have h := Lane_q_s14_post.expect_comp_eq_sum_pr P f (fun y => if A y then 1 else 0)
  simpa only [FinLaw.E, FinLaw.pr, mul_ite, mul_one, mul_zero] using h

theorem pr_bind {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (P : FinLaw Ω) (Q : Ω → FinLaw Y) (A : Ω × Y → Prop) :
    (FinLaw.bind P Q).pr A = ∑ ω, P.w ω * (Q ω).pr (fun y => A (ω, y)) := by
  classical
  unfold FinLaw.pr
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [FinLaw.bind]
  split_ifs <;> simp

/-- The experiment's unused label coordinates disappear from every star event. -/
theorem internal_query_pr {G B Z J : Type*} [Fintype G] [DecidableEq G]
    [Fintype B] [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J] {N : ℕ}
    (q : G → B → ℝ) (hq0 : ∀ g b, 0 ≤ q g b) (hq1 : ∀ g, ∑ b, q g b = 1)
    (U : G → B → Fin N → ℝ) (hU0 : ∀ g b y, 0 ≤ U g b y)
    (hU1 : ∀ g b, ∑ y, U g b y = 1) (grp : Z → G)
    (query : J → Z) (hinj : Function.Injective query)
    (A : (G → B) → (J → Fin N) → Prop) :
    (internalRefLaw q hq0 hq1 U hU0 hU1 grp).pr
      (fun ω => A ω.1 (fun j => ω.2 (query j))) =
      ∑ bins : G → B, (∏ g, q g (bins g)) *
        ∑ ys : J → Fin N, if A bins ys then
          ∏ j, U (grp (query j)) (bins (grp (query j))) (ys j) else 0 := by
  classical
  rw [internalRefLaw, pr_bind]
  apply Finset.sum_congr rfl
  intro bins _
  congr 1
  simp only [Prod.fst, Prod.snd]
  rw [pr_fibers (Y := J → Fin N) _ (fun labels : Z → Fin N => fun j => labels (query j)) (A bins)]
  apply Finset.sum_congr rfl
  intro ys _
  split_ifs
  · have hp := pi_query_probability (fun z =>
        (⟨U (grp z) (bins (grp z)), hU0 _ _, hU1 _ _⟩ : FinLaw (Fin N))) query hinj ys
    exact hp
  · rfl

/-- Badness only reads eligibility and center bits in the crowd ball. -/
theorem bad_congr_at (p : HDParams) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (v : CubePos p.d) (j : Fin (p.H + 1)) (he : E v j = E' v j)
    (ha : ∀ c ∈ E v j, A c = A' c)
    (hc : ∀ z, hammingDist z v ≤ p.r + p.D →
      P (z, j) = P' (z, j) ∧ A (z, j) = A' (z, j)) :
    p.Bad P A E v j ↔ p.Bad P' A' E' v j := by
  classical
  have hnone : (∀ c ∈ E v j, A c = false) ↔ (∀ c ∈ E' v j, A' c = false) := by
    rw [← he]
    constructor <;> intro h c hc'
    · rw [← ha c hc']
      exact h c hc'
    · rw [ha c hc']
      exact h c hc'
  have hcrowd : (Finset.univ.filter fun z : CubePos p.d =>
      P (z, j) = true ∧ A (z, j) = true ∧ hammingDist z v ≤ p.r + p.D) =
      (Finset.univ.filter fun z : CubePos p.d =>
        P' (z, j) = true ∧ A' (z, j) = true ∧ hammingDist z v ≤ p.r + p.D) := by
    apply Finset.filter_congr
    intro z _
    by_cases hz : hammingDist z v ≤ p.r + p.D
    · rw [(hc z hz).1, (hc z hz).2]
    · simp only [hz, and_false]
  unfold HDParams.Bad
  rw [hnone, hcrowd]

/-- A union indexed by every site commutes with independent renamings. -/
theorem biUnion_transport {A C : Type*} [Fintype A] [DecidableEq C]
    (ea : A ≃ A) (ec : C ≃ C) (S S' : A → Finset C)
    (hS : ∀ a, S' (ea a) = (S a).map ec.toEmbedding) :
    (Finset.univ.biUnion S') = (Finset.univ.biUnion S).map ec.toEmbedding := by
  classical
  ext c
  obtain ⟨c, rfl⟩ := ec.surjective c
  conv_lhs => simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  conv_rhs => simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, hc⟩
    obtain ⟨a, rfl⟩ := ea.surjective a
    refine ⟨a, ?_⟩
    rw [hS] at hc
    simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hc
  · rintro ⟨a, hc⟩
    refine ⟨ea a, ?_⟩
    rw [hS]
    exact Finset.mem_map.mpr ⟨c, hc, rfl⟩

end HypercubeRamsey.Lane_sol_s14_lik




