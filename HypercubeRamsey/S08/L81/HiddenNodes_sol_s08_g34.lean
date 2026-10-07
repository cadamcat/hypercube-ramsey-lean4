import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.FinProbLemmas

noncomputable section
namespace HypercubeRamsey.Lane_sol_s08_g34
open Classical
open scoped BigOperators

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (h : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x
  · simp [ha, h x ha]
  · simp only [if_neg ha]
    split_ifs <;> simp [P.nonneg]

theorem pr_le_one {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : P.pr A ≤ 1 := by
  calc
    _ ≤ ∑ x, P.w x := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> simp [P.nonneg]
    _ = 1 := P.sum_eq_one

private def consEquiv (Ω : Type*) (m : ℕ) :
    (Ω × (Fin m → Ω)) ≃ (Fin (m + 1) → Ω) where
  toFun p := Fin.cons (α := fun _ => Ω) p.1 p.2
  invFun f := (f 0, fun j => f j.succ)
  left_inv := by rintro ⟨x, f⟩; simp
  right_inv f := by funext j; exact Fin.cases (by simp) (fun i => by simp) j

theorem pi_pr_cons {Ω : Type*} [Fintype Ω] (m : ℕ)
    (P : Fin (m + 1) → FinProb Ω) (B : (Fin (m + 1) → Ω) → Prop) :
    (FinProb.pi P).pr B = ∑ y, (P 0).w y *
      (FinProb.pi (fun j : Fin m => P j.succ)).pr (fun f => B (Fin.cons (α := fun _ => Ω) y f)) := by
  unfold FinProb.pr
  rw [← (consEquiv Ω m).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  change (if B (Fin.cons (α := fun _ => Ω) y f) then ∏ j, (P j).w ((Fin.cons (α := fun _ => Ω) y f) j) else 0) = _
  rw [Fin.prod_univ_succ]
  by_cases hb : B (Fin.cons (α := fun _ => Ω) y f) <;> simp [hb, FinProb.pi]

def mass {N : ℕ} {Ω : Type*} {m : ℕ} (μ : Law N)
    (hit : Fin N → Ω → Prop) (f : Fin m → Ω) : ℝ := μ.pr (fun x => ∀ j, hit x (f j))

theorem mass_zero {N : ℕ} {Ω : Type*} (μ : Law N)
    (hit : Fin N → Ω → Prop) (f : Fin 0 → Ω) : mass μ hit f = 1 := by
  simp [mass, FinProb.pr, μ.sum_eq_one]

theorem mass_cons {N : ℕ} {Ω : Type*} {m : ℕ} (μ : Law N)
    (hit : Fin N → Ω → Prop) (y : Ω) (f : Fin m → Ω)
    (hm : 0 < μ.pr (fun x => hit x y)) :
    mass μ hit (Fin.cons (α := fun _ => Ω) y f) =
      μ.pr (fun x => hit x y) * mass (μ.cond (fun x => hit x y) hm) hit f := by
  unfold mass FinProb.pr FinProb.cond
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hall : (∀ j : Fin (m+1), hit x (Fin.cons (α := fun _ => Ω) y f j)) ↔
      hit x y ∧ ∀ j : Fin m, hit x (f j) := by simp [Fin.forall_fin_succ]
  dsimp only
  simp only [hall]
  have hm' : (∑ z, if hit z y then μ.w z else 0) ≠ 0 := ne_of_gt hm
  by_cases hy : hit x y <;> by_cases hf : ∀ j, hit x (f j) <;>
    simp [FinProb.pr, hy, hf, hm', mul_div_cancel₀, mul_comm]

theorem cond_support {N : ℕ} (μ : Law N) (X : Finset (Fin N))
    (A : Fin N → Prop) (hm : 0 < μ.pr A) (hμ : μ.SupportedIn X) :
    Law.SupportedIn (μ.cond A hm) X := by
  intro x hx
  simp [FinProb.cond, hμ x hx]

theorem cond_width {N : ℕ} (μ : Law N) (A : Fin N → Prop)
    (hm : 0 < μ.pr A) (t c a : ℝ) (hμ : μ.WidthLE t)
    (ha : a ≤ μ.pr A) (hc : 1 ≤ a * Real.exp c) :
    Law.WidthLE (μ.cond A hm) (t+c) := by
  intro x
  change (if A x then μ.w x else 0) / μ.pr A ≤ Real.exp (t+c) / N
  by_cases hx : A x
  · rw [if_pos hx]
    apply (div_le_iff₀ hm).2
    have he : 0 ≤ Real.exp t / (N : ℝ) := by positivity
    calc
      μ.w x ≤ Real.exp t / N := hμ x
      _ ≤ (Real.exp t / N) * (a * Real.exp c) := by nlinarith
      _ ≤ (Real.exp t / N) * (μ.pr A * Real.exp c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha (Real.exp_nonneg _)) he
      _ = (Real.exp (t+c) / N) * μ.pr A := by rw [Real.exp_add]; ring
  · simp [hx]; positivity

theorem mass_nonneg {N : ℕ} {Ω : Type*} {m : ℕ} (μ : Law N)
    (hit : Fin N → Ω → Prop) (f : Fin m → Ω) : 0 ≤ mass μ hit f := by
  unfold mass FinProb.pr
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [μ.nonneg]

/-- Independent blocks, with a uniform exceptional probability for every law of admissible width. -/
theorem sequential {N : ℕ} {Ω : Type*} [Fintype Ω]
    (hit : Fin N → Ω → Prop) (X : Finset (Fin N))
    (W a b c ε : ℝ) (ha : 0 < a) (hab : a ≤ b) (hc : 1 ≤ a * Real.exp c)
    (hε : 0 ≤ ε) (hc0 : 0 ≤ c) :
    ∀ m (P : Fin m → FinProb Ω),
      (∀ j (μ : Law N), μ.SupportedIn X → μ.WidthLE W →
        (P j).pr (fun y => ¬ (a ≤ μ.pr (fun x => hit x y) ∧ μ.pr (fun x => hit x y) ≤ b)) ≤ ε) →
      ∀ μ t, μ.SupportedIn X → μ.WidthLE t → t + (m : ℝ)*c ≤ W →
      (FinProb.pi P).pr (fun f => ¬ (a^m ≤ mass μ hit f ∧ mass μ hit f ≤ b^m)) ≤ (m : ℝ)*ε := by
  intro m
  induction m with
  | zero =>
    intro P hP μ t hμS hμW ht
    simp [mass_zero, FinProb.pr]
  | succ m ih =>
    intro P hP μ t hμS hμW ht
    have htW : t ≤ W := by
      have : 0 ≤ ((m+1 : ℕ) : ℝ)*c := mul_nonneg (Nat.cast_nonneg _) hc0
      linarith
    have hhead := hP 0 μ hμS (Law.WidthLE.mono hμW htW)
    rw [pi_pr_cons]
    have hb0 : 0 ≤ b := ha.le.trans hab
    have hmε : 0 ≤ (m : ℝ)*ε := mul_nonneg (Nat.cast_nonneg _) hε
    calc
      _ ≤ ∑ y, (P 0).w y *
          ((if ¬ (a ≤ μ.pr (fun x => hit x y) ∧ μ.pr (fun x => hit x y) ≤ b) then 1 else 0) +
            (m : ℝ)*ε) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ ((P 0).nonneg y)
        by_cases hy : a ≤ μ.pr (fun x => hit x y) ∧ μ.pr (fun x => hit x y) ≤ b
        · simp only [hy.1, hy.2, and_self, not_true_eq_false, ite_false, zero_add]
          let μ' : Law N := μ.cond (fun x => hit x y) (ha.trans_le hy.1)
          have hμ'W : μ'.WidthLE (t+c) := cond_width μ _ _ t c a hμW hy.1 hc
          have hμ'S : μ'.SupportedIn X := cond_support μ X _ _ hμS
          have hbudget : (t+c) + (m : ℝ)*c ≤ W := by push_cast at ht; linarith
          have htail := ih (fun j => P j.succ) (fun j => hP j.succ) μ' (t+c) hμ'S hμ'W hbudget
          apply le_trans (pr_mono _ _ _ _) htail
          intro f hf hgood
          apply hf
          rw [mass_cons μ hit y f (ha.trans_le hy.1)]
          constructor
          · rw [pow_succ, mul_comm (a^m)]
            exact mul_le_mul hy.1 hgood.1 (pow_nonneg ha.le _) (le_trans ha.le hy.1)
          · rw [pow_succ, mul_comm (b^m)]
            exact mul_le_mul hy.2 hgood.2 (mass_nonneg μ' hit f) hb0
        · simp only [hy, not_false_eq_true, if_true]
          exact le_trans (pr_le_one _ _) (by linarith)
      _ = (P 0).pr (fun y => ¬ (a ≤ μ.pr (fun x => hit x y) ∧ μ.pr (fun x => hit x y) ≤ b)) +
          (m : ℝ)*ε := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, (P 0).sum_eq_one, one_mul]
        congr 1
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro y _
        dsimp only
        split_ifs <;> ring
      _ ≤ ε + (m : ℝ)*ε := by linarith [hhead]
      _ = ((m+1 : ℕ) : ℝ)*ε := by push_cast; ring

theorem pi_pr_reindex {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (P : I → FinProb Ω) (B : (I → Ω) → Prop) :
    (FinProb.pi P).pr B =
      (FinProb.pi (fun j => P (e.symm j))).pr (fun f => B (fun i => f (e i))) := by
  let ef : (J → Ω) ≃ (I → Ω) := Equiv.arrowCongr e.symm (Equiv.refl Ω)
  unfold FinProb.pr
  rw [← ef.sum_comp]
  apply Finset.sum_congr rfl
  intro f _
  change (if B (fun i => f (e i)) then ∏ i, (P i).w (f (e i)) else 0) = _
  have hprod : (∏ i, (P i).w (f (e i))) = ∏ j, (P (e.symm j)).w (f j) := by
    exact Fintype.prod_equiv e _ _ (by intro i; simp)
  rw [hprod]
  rfl

theorem sequential_fintype {N : ℕ} {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (hit : Fin N → Ω → Prop) (X : Finset (Fin N))
    (W a b c ε : ℝ) (ha : 0 < a) (hab : a ≤ b) (hc : 1 ≤ a * Real.exp c)
    (hε : 0 ≤ ε) (hc0 : 0 ≤ c) (P : I → FinProb Ω)
    (hP : ∀ j (μ : Law N), μ.SupportedIn X → μ.WidthLE W →
      (P j).pr (fun y => ¬ (a ≤ μ.pr (fun x => hit x y) ∧ μ.pr (fun x => hit x y) ≤ b)) ≤ ε)
    (μ : Law N) (t : ℝ) (hμS : μ.SupportedIn X) (hμW : μ.WidthLE t)
    (ht : t + (Fintype.card I : ℝ)*c ≤ W) :
    (FinProb.pi P).pr (fun f => ¬ (a^(Fintype.card I) ≤ μ.pr (fun x => ∀ j, hit x (f j)) ∧
      μ.pr (fun x => ∀ j, hit x (f j)) ≤ b^(Fintype.card I))) ≤ (Fintype.card I : ℝ)*ε := by
  let e := Fintype.equivFin I
  rw [pi_pr_reindex e]
  have hm (f : Fin (Fintype.card I) → Ω) :
      μ.pr (fun x => ∀ j, hit x (f (e j))) = mass μ hit f := by
    unfold mass
    congr 1
    funext x
    apply propext
    constructor
    · intro hh j
      simpa using hh (e.symm j)
    · intro hh j
      exact hh (e j)
  simp_rw [hm]
  simpa only [FinProb.pi] using sequential hit X W a b c ε ha hab hc hε hc0 _ _
    (fun j => hP (e.symm j)) μ t hμS hμW ht

theorem pi_pr_slice_bound {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (P : I → FinProb Ω) (s : Finset I) (B : (I → Ω) → Prop) (L : ℝ)
    (hB : ∀ b : {i // i ∉ s} → Ω,
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).pr
        (fun a => B ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => Ω)).symm (a,b))) ≤ L) :
    (FinProb.pi P).pr B ≤ L := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => Ω)
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  have hsplit : (FinProb.pi P).pr B = ∑ b, Pc.w b * Ps.pr (fun a => B (e.symm (a,b))) := by
    unfold FinProb.pr
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hw : (FinProb.pi P).w (e.symm (a,b)) = Ps.w a * Pc.w b := by
      change (∏ i, (P i).w (e.symm (a,b) i)) = _
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ s)]
      have hl (i : {i // i ∈ s}) : e.symm (a,b) i.1 = a i := by
        simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
      have hr (i : {i // i ∉ s}) : e.symm (a,b) i.1 = b i := by
        simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
      simp_rw [hl, hr]
      dsimp only [Ps, Pc, FinProb.pi]
      congr 1
      · apply Finset.prod_congr
        · ext i; simp
        · intro i _; rfl
    dsimp only
    rw [hw]
    split_ifs <;> ring
  rw [hsplit]
  calc
    _ ≤ ∑ b, Pc.w b * L := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hB b) (Pc.nonneg b)
    _ = L := by rw [← Finset.sum_mul, Pc.sum_eq_one, one_mul]

theorem close_powers (u : ℝ) (hu : 0 ≤ u) (m : ℕ) (hm : (m : ℝ)*u ≤ 1/40) :
    (10/11 : ℝ) ≤ (1-u)^m ∧ (1+u)^m ≤ (11/10 : ℝ) := by
  have hlo : 1 - (m : ℝ)*u ≤ (1-u)^m := by
    by_cases hum : u ≤ 1
    · have hh := one_add_mul_le_pow (show (-2 : ℝ) ≤ -u by linarith) m
      convert hh using 1 <;> ring
    · have hm0 : m = 0 := by
        by_contra hmn
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmn
        nlinarith
      subst m
      simp
  have hhi : ∀ k ≤ m, (1+u)^k ≤ 1+2*(k : ℝ)*u := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ m := by omega
      have ih' := ih hk'
      have hku : (k : ℝ)*u ≤ 1/40 := by
        calc
          _ ≤ (m : ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hu
          _ ≤ _ := hm
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_right ih' (show 0 ≤ 1+u by linarith)
      push_cast
      nlinarith
  constructor
  · linarith
  · have hh := hhi m le_rfl
    linarith
end HypercubeRamsey.Lane_sol_s08_g34
