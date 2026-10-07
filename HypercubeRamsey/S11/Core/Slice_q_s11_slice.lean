import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S03.GatedPosterior

namespace HypercubeRamsey.Lane_q_s11_slice

open HypercubeRamsey
open HypercubeRamsey.S11.Core
open Filter
open scoped BigOperators

noncomputable section

variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype Ω]

/-- The marginal of an iid finite product law on any injective list of coordinates. -/
theorem pi_expect_injective_projection (P : FinProb Ω) (f : α → ι)
    (hf : Function.Injective f) (ω₀ : Ω) (g : (α → Ω) → ℝ) :
    (FinProb.pi (fun _ : ι => P)).expect (fun w => g (fun a => w (f a))) =
      (FinProb.pi (fun _ : α => P)).expect g := by
  classical
  let s : Finset ι := Finset.univ.image f
  let e : α ≃ {i // i ∈ s} := {
    toFun := fun a => ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
    invFun := fun i => Classical.choose (Finset.mem_image.mp i.2)
    left_inv := by
      intro a
      apply hf
      have := Classical.choose_spec (Finset.mem_image.mp (show f a ∈ s from
        Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
      exact this.2
    right_inv := by
      intro i
      apply Subtype.ext
      exact (Classical.choose_spec (Finset.mem_image.mp i.2)).2
  }
  let split := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ : ι => Ω)
  let b₀ : ∀ i : {i // i ∉ s}, Ω := fun _ => ω₀
  have hdep : FinProb.DependsOn (fun w : ι → Ω => g (fun a : α => w (f a))) s := by
    intro w w' hw
    apply congrArg g
    funext a
    exact hw (f a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  rw [FinProb.pi_expect_depends (fun _ : ι => P) s
    (fun w : ι → Ω => g (fun a : α => w (f a))) (fun _ => ω₀) hdep]
  change (∑ aS : ({i // i ∈ s} → Ω),
      (∏ i, P.w (aS i)) *
        g (fun a => split.symm (aS, b₀) (f a))) = _
  let eFun : (α → Ω) ≃ ({i // i ∈ s} → Ω) := {
    toFun := fun x i => x (e.symm i)
    invFun := fun aS a => aS (e a)
    left_inv := by intro x; funext a; simp
    right_inv := by intro aS; funext i; simp
  }
  have hproj (aS : {i // i ∈ s} → Ω) (a : α) :
      split.symm (aS, b₀) (f a) = aS (e a) := by
    have hfa : f a ∈ s := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp [split, Equiv.piEquivPiSubtypeProd, hfa, e]
  simp_rw [hproj]
  have hprod (x : α → Ω) :
      (∏ i : {i // i ∈ s}, P.w (x (e.symm i))) = ∏ a : α, P.w (x a) := by
    symm
    exact Fintype.prod_equiv e (fun a => P.w (x a))
      (fun i => P.w (x (e.symm i))) (by intro a; simp)
  have hprodAttach (x : α → Ω) :
      (∏ i ∈ s.attach, P.w (x (e.symm i))) = ∏ a : α, P.w (x a) := by
    simpa only [← Finset.univ_eq_attach] using hprod x
  symm
  apply Fintype.sum_equiv eFun
  intro x
  dsimp [eFun]
  rw [hprodAttach]
  change (∏ a : α, P.w (x a)) * g x =
    (∏ a : α, P.w (x a)) * g (fun a => x (e.symm (e a)))
  apply congrArg (fun r : ℝ => (∏ a : α, P.w (x a)) * r)
  apply congrArg g
  funext a
  simp

/-- Split a function on `Option α` into its value at `none` and its `some` values. -/
def optionFunEquiv (α Ω : Type*) : (Option α → Ω) ≃ (Ω × (α → Ω)) where
  toFun w := (w none, fun a => w (some a))
  invFun p := fun o => o.elim p.1 p.2
  left_inv := by intro w; funext o; cases o <;> rfl
  right_inv := by intro p; cases p; rfl

theorem pi_expect_option_split {α Ω : Type*} [Fintype α] [DecidableEq α] [Fintype Ω]
    (P : FinProb Ω) (f : (Option α → Ω) → ℝ) :
    (FinProb.pi (fun _ : Option α => P)).expect f =
      (FinProb.bind P (fun _ => FinProb.pi (fun _ : α => P))).expect
        (fun p => f ((optionFunEquiv α Ω).symm p)) := by
  classical
  let e := optionFunEquiv α Ω
  change (∑ W : Option α → Ω, (∏ o, P.w (W o)) * f W) =
    ∑ p : Ω × (α → Ω), P.w p.1 * (∏ a, P.w (p.2 a)) * f (e.symm p)
  apply Fintype.sum_equiv e
  intro W
  change (∏ o, P.w (W o)) * f W =
    (P.w (W none) * ∏ a, P.w (W (some a))) *
      f (fun o => o.elim (W none) (fun a => W (some a)))
  rw [Fintype.prod_option]
  have hfun : (fun o : Option α => o.elim (W none) (fun a => W (some a))) = W := by
    funext o
    cases o <;> rfl
  rw [hfun]

theorem oddRowW_nonneg_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (g : ℝ) (μ ν : Law N) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (ws : I → Fin k → Fin N) (y : Fin N) :
    0 ≤ oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν ws y := by
  classical
  have hdeg (y : Fin N) : 0 ≤ colDeg E G μ y := by
    unfold colDeg
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg (μ.nonneg x)
    split_ifs <;> norm_num
  have hlik : 0 ≤ lik (E := E) (G := G) (I := I) (k := k) μ ws y := by
    unfold lik
    apply Finset.prod_nonneg
    intro a ha
    apply Finset.prod_nonneg
    intro j hj
    exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (hdeg y)
  unfold oddRowW
  split_ifs with hp
  · exact div_nonneg (mul_nonneg (ν.nonneg y) hlik) hp.1.le
  · exact ν.nonneg y

theorem oddRowW_sum_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (g : ℝ) (μ ν : Law N) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (ws : I → Fin k → Fin N) :
    ∑ y, oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν ws y = 1 := by
  classical
  by_cases hp : Passes (E := E) (G := G) (I := I) (k := k) g μ ν ws
  · simp only [oddRowW, if_pos hp]
    rw [← Finset.sum_div]
    change normZ E G μ ν ws / normZ E G μ ν ws = 1
    exact div_self hp.1.ne'
  · simp [oddRowW, hp, ν.sum_eq_one]

noncomputable def normalizeWeight_q_s11_slice {α : Type*} [Fintype α]
    (ν : FinProb α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : FinProb α := by
  classical
  let d : ℝ := ∑ x, ν.w x * f x
  by_cases hd : 0 < d
  · exact {
      w := fun x => ν.w x * f x / d
      nonneg := fun x => div_nonneg (mul_nonneg (ν.nonneg x) (hf x)) hd.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        change d / d = 1
        exact div_self hd.ne' }
  · exact ν

def joinRadiusTwo_q_s11_slice {I T : Type} [Fintype I] [DecidableEq I]
    (t : T) (u : Pair I → T) : Option (Pair I) → T := fun o => o.elim t u

def centerLik_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (t : Fin k → Fin N) (y : Fin N) : ℝ :=
  ∏ j, hit E G (t j) y / colDeg E G μ y

theorem likDel_independent_center_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (μ : Law N)
    (t t' : Fin k → Fin N) (u : Pair I → Fin k → Fin N) (a : I) (y : Fin N) :
    likDel E G μ (ballStar (joinRadiusTwo_q_s11_slice t u) a) a y =
      likDel E G μ (ballStar (joinRadiusTwo_q_s11_slice t' u) a) a y := by
  classical
  unfold likDel
  apply Finset.prod_congr rfl
  intro b hb
  apply Finset.prod_congr rfl
  intro j hj
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  simp [ballStar, joinRadiusTwo_q_s11_slice, hba]

theorem lik_split_center_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (μ : Law N)
    (t : Fin k → Fin N) (u : Pair I → Fin k → Fin N) (a : I) (y : Fin N) :
    lik E G μ (ballStar (joinRadiusTwo_q_s11_slice t u) a) y =
      centerLik_q_s11_slice E G μ t y *
        likDel E G μ (ballStar (joinRadiusTwo_q_s11_slice t u) a) a y := by
  classical
  let f : I → ℝ := fun b =>
    ∏ j, hit E G ((ballStar (joinRadiusTwo_q_s11_slice t u) a) b j) y /
      colDeg E G μ y
  have hsplit := (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)).symm
  unfold lik
  change (∏ b, f b) = _
  rw [hsplit]
  have ha : f a = centerLik_q_s11_slice E G μ t y := by
    simp [f, centerLik_q_s11_slice, ballStar, joinRadiusTwo_q_s11_slice]
  rw [ha]
  rfl

theorem hit_center_of_lik_ne_zero_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (μ : Law N)
    (t : Fin k → Fin N) (u : Pair I → Fin k → Fin N) (a : I) (y : Fin N)
    (hlik : lik E G μ (ballStar (joinRadiusTwo_q_s11_slice t u) a) y ≠ 0)
    (j : Fin k) : Hits E G (t j) y := by
  classical
  have hprod :
      (∏ b : I, ∏ q : Fin k,
        hit E G ((ballStar (joinRadiusTwo_q_s11_slice t u) a) b q) y /
          colDeg E G μ y) ≠ 0 := by
    simpa [lik] using hlik
  have houter := (Finset.prod_ne_zero_iff.mp hprod)
  have hinner := houter a (Finset.mem_univ a)
  have hfactor := (Finset.prod_ne_zero_iff.mp hinner) j (Finset.mem_univ j)
  have hhit : hit E G (t j) y ≠ 0 := by
    have hEq : (ballStar (joinRadiusTwo_q_s11_slice t u) a) a j = t j := by
      simp [ballStar, joinRadiusTwo_q_s11_slice]
    rw [hEq] at hfactor
    intro hzero
    rw [hzero] at hfactor
    simp at hfactor
  unfold hit at hhit
  split_ifs at hhit with h
  · exact h
  · simp at hhit

theorem centerCoeff_bound_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (g : ℝ) (μ ν : Law N)
    (hgn : 0 < g) (hgs : g ≤ 1 / 4)
    (hhigh : ∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * g ≤ colDeg E G μ y)
    (t : Fin k → Fin N) (y : Fin N) (hy : ν.w y ≠ 0) :
    Real.exp ((1 / 5 : ℝ) * g * k) * centerLik_q_s11_slice E G μ t y ≤
      Real.exp ((Real.log 2 - 2 * g) * k) := by
  classical
  have htpos : 0 < (1 / 2 : ℝ) + 2 * g := by positivity
  have hlogFrac : (11 / 5 : ℝ) * g ≤ Real.log (1 + 4 * g) := by
    have hlog := Real.le_log_one_add_of_nonneg (x := 4 * g) (by positivity)
    have hden : 0 < 4 * g + 2 := by positivity
    have hfrac : (11 / 5 : ℝ) * g ≤ 8 * g / (4 * g + 2) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hgn.le, hgs]
    exact hfrac.trans (by convert hlog using 1 <;> ring)
  have hlogDen : -Real.log 2 + (11 / 5 : ℝ) * g ≤
      Real.log ((1 / 2 : ℝ) + 2 * g) := by
    have heq : (1 / 2 : ℝ) + 2 * g = (1 / 2 : ℝ) * (1 + 4 * g) := by ring
    rw [heq, Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (by positivity : (1 + 4 * g) ≠ 0)]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hratioPos : 0 < Real.exp ((1 / 5 : ℝ) * g) / ((1 / 2 : ℝ) + 2 * g) := by
    positivity
  have hlogRatio : Real.log
      (Real.exp ((1 / 5 : ℝ) * g) / ((1 / 2 : ℝ) + 2 * g)) =
        (1 / 5 : ℝ) * g - Real.log ((1 / 2 : ℝ) + 2 * g) := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt htpos), Real.log_exp]
  have hratioBound :
      Real.exp ((1 / 5 : ℝ) * g) / ((1 / 2 : ℝ) + 2 * g) ≤
        Real.exp (Real.log 2 - 2 * g) := by
    rw [← Real.exp_log hratioPos, hlogRatio]
    exact Real.exp_le_exp.mpr (by nlinarith [hlogDen])
  have hcoord (j : Fin k) :
      Real.exp ((1 / 5 : ℝ) * g) *
        (hit E G (t j) y / colDeg E G μ y) ≤ Real.exp (Real.log 2 - 2 * g) := by
    have hdeg := hhigh y hy
    have hdegpos : 0 < colDeg E G μ y := by nlinarith [hgn, hdeg]
    have hhit : hit E G (t j) y ≤ 1 := by
      unfold hit
      split_ifs <;> norm_num
    have hdiv : hit E G (t j) y / colDeg E G μ y ≤
        1 / ((1 / 2 : ℝ) + 2 * g) := by
      calc
        hit E G (t j) y / colDeg E G μ y ≤ 1 / colDeg E G μ y :=
          div_le_div_of_nonneg_right hhit hdegpos.le
        _ ≤ 1 / ((1 / 2 : ℝ) + 2 * g) :=
          one_div_le_one_div_of_le htpos hdeg
    calc
      Real.exp ((1 / 5 : ℝ) * g) *
          (hit E G (t j) y / colDeg E G μ y) ≤
        Real.exp ((1 / 5 : ℝ) * g) *
          (1 / ((1 / 2 : ℝ) + 2 * g)) :=
            mul_le_mul_of_nonneg_left hdiv (Real.exp_nonneg _)
      _ = Real.exp ((1 / 5 : ℝ) * g) / ((1 / 2 : ℝ) + 2 * g) := by ring
      _ ≤ Real.exp (Real.log 2 - 2 * g) := hratioBound
  have hdegpos0 : 0 < colDeg E G μ y := by
    have h := hhigh y hy
    nlinarith [hgn]
  have hprod :
      (∏ j : Fin k, Real.exp ((1 / 5 : ℝ) * g) *
        (hit E G (t j) y / colDeg E G μ y)) ≤
        ∏ j : Fin k, Real.exp (Real.log 2 - 2 * g) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      exact mul_nonneg (Real.exp_nonneg _)
        (div_nonneg (by unfold hit; split_ifs <;> norm_num)
          hdegpos0.le)
    · intro j hj
      exact hcoord j
  have hExpProd : ∏ j : Fin k, Real.exp ((1 / 5 : ℝ) * g) =
      Real.exp ((1 / 5 : ℝ) * g * k) := by
    calc
      (∏ j : Fin k, Real.exp ((1 / 5 : ℝ) * g)) =
          Real.exp ((1 / 5 : ℝ) * g) ^ k := by simp
      _ = Real.exp ((k : ℝ) * ((1 / 5 : ℝ) * g)) :=
        (Real.exp_nat_mul ((1 / 5 : ℝ) * g) k).symm
      _ = Real.exp ((1 / 5 : ℝ) * g * k) := by congr 1 <;> ring
  have hRhsProd : ∏ j : Fin k, Real.exp (Real.log 2 - 2 * g) =
      Real.exp ((Real.log 2 - 2 * g) * k) := by
    calc
      (∏ j : Fin k, Real.exp (Real.log 2 - 2 * g)) =
          Real.exp (Real.log 2 - 2 * g) ^ k := by simp
      _ = Real.exp ((k : ℝ) * (Real.log 2 - 2 * g)) :=
        (Real.exp_nat_mul (Real.log 2 - 2 * g) k).symm
      _ = Real.exp ((Real.log 2 - 2 * g) * k) := by congr 1 <;> ring
  calc
    Real.exp ((1 / 5 : ℝ) * g * k) * centerLik_q_s11_slice E G μ t y =
        ∏ j : Fin k, Real.exp ((1 / 5 : ℝ) * g) *
          (hit E G (t j) y / colDeg E G μ y) := by
      rw [← hExpProd, centerLik_q_s11_slice, ← Finset.prod_mul_distrib]
    _ ≤ ∏ j : Fin k, Real.exp (Real.log 2 - 2 * g) := hprod
    _ = Real.exp ((Real.log 2 - 2 * g) * k) := hRhsProd

def lawAsFinProb_q_s11_slice {N : ℕ} (ν : Law N) : FinProb (Fin N) where
  w := ν.w
  nonneg := ν.nonneg
  sum_eq_one := ν.sum_eq_one

theorem colDeg_nonneg_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ : Law N) (y : Fin N) : 0 ≤ colDeg E G μ y := by
  classical
  unfold colDeg
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg (μ.nonneg x)
  split_ifs <;> norm_num

theorem likDel_nonneg_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (μ : Law N) (ws : I → Fin k → Fin N) (a : I) (y : Fin N) :
    0 ≤ likDel E G μ ws a y := by
  classical
  unfold likDel
  apply Finset.prod_nonneg
  intro b hb
  apply Finset.prod_nonneg
  intro j hj
  exact div_nonneg (by unfold hit; split_ifs <;> norm_num)
    (colDeg_nonneg_q_s11_slice E G μ y)

def deletionLik_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    {I : Type} [Fintype I] [DecidableEq I] (μ : Law N) (y₀ : Fin N)
    (u : Pair I → Fin k → Fin N) (a : I) (y : Fin N) : ℝ :=
  likDel E G μ (ballStar (joinRadiusTwo_q_s11_slice (fun _ : Fin k => y₀) u) a) a y

def deletionMass_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    {I : Type} [Fintype I] [DecidableEq I] (μ ν : Law N) (y₀ : Fin N)
    (u : Pair I → Fin k → Fin N) (a : I) : ℝ :=
  ∑ y, ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y

noncomputable def deletionLaw_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] (μ ν : Law N)
    (y₀ : Fin N) (u : Pair I → Fin k → Fin N) (a : I) : FinProb (Fin N) :=
  normalizeWeight_q_s11_slice (lawAsFinProb_q_s11_slice ν)
    (deletionLik_q_s11_slice E G μ y₀ u a)
    (likDel_nonneg_q_s11_slice E G μ
      (ballStar (joinRadiusTwo_q_s11_slice (fun _ : Fin k => y₀) u) a) a)

theorem oddRow_le_deletion_q_s11_slice {N k : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] (g : ℝ)
    (μ ν : Law N) (y₀ : Fin N) (hg : 0 < g) (hgs : g ≤ 1 / 4)
    (hhigh : ∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * g ≤ colDeg E G μ y)
    (t : Fin k → Fin N) (u : Pair I → Fin k → Fin N) (a : I)
    (hp : Passes E G g μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a))
    (y : Fin N) :
    oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
        (ballStar (joinRadiusTwo_q_s11_slice t u) a) y ≤
      Real.exp ((Real.log 2 - 2 * g) * k) *
        (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y := by
  classical
  let t₀ : Fin k → Fin N := fun _ => y₀
  let d : ℝ := deletionMass_q_s11_slice E G μ ν y₀ u a
  have hdel (z : Fin N) :
      likDel E G μ (ballStar (joinRadiusTwo_q_s11_slice t u) a) a z =
        deletionLik_q_s11_slice E G μ y₀ u a z := by
    exact likDel_independent_center_q_s11_slice E G μ t t₀ u a z
  have hden : normZDel E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) a = d := by
    unfold normZDel d deletionMass_q_s11_slice
    apply Finset.sum_congr rfl
    intro z hz
    rw [hdel z]
  have hdnonneg : 0 ≤ d := by
    dsimp [d, deletionMass_q_s11_slice]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (ν.nonneg z)
      (likDel_nonneg_q_s11_slice E G μ
        (ballStar (joinRadiusTwo_q_s11_slice t₀ u) a) a z)
  have hdelNonneg (z : Fin N) :
      0 ≤ deletionLik_q_s11_slice E G μ y₀ u a z := by
    exact likDel_nonneg_q_s11_slice E G μ
      (ballStar (joinRadiusTwo_q_s11_slice t₀ u) a) a z
  have hcenterNonneg (z : Fin N) (hz : ν.w z ≠ 0) :
      0 ≤ centerLik_q_s11_slice E G μ t z := by
    unfold centerLik_q_s11_slice
    apply Finset.prod_nonneg
    intro j hj
    have hdeg := hhigh z hz
    have hdegpos : 0 < colDeg E G μ z := by nlinarith [hg]
    exact div_nonneg (by unfold hit; split_ifs <;> norm_num) hdegpos.le
  by_cases hy : ν.w y = 0
  · have hrow : oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
        (ballStar (joinRadiusTwo_q_s11_slice t u) a) y = 0 := by
      simp [oddRowW, hp, hy]
    rw [hrow]
    exact mul_nonneg (Real.exp_nonneg _) ((deletionLaw_q_s11_slice E G μ ν y₀ u a).nonneg y)
  · have hdeg := hhigh y hy
    have hdegpos : 0 < colDeg E G μ y := by nlinarith [hg]
    have hcoef := centerCoeff_bound_q_s11_slice E G g μ ν hg hgs hhigh t y hy
    have hlikSplit := lik_split_center_q_s11_slice E G μ t u a y
    by_cases hd : 0 < d
    · have hd' : 0 < ∑ z, ν.w z * deletionLik_q_s11_slice E G μ y₀ u a z := by
        simpa [d, deletionMass_q_s11_slice] using hd
      have hq : (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y =
          ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y / d := by
        simp [deletionLaw_q_s11_slice, normalizeWeight_q_s11_slice,
          lawAsFinProb_q_s11_slice, deletionMass_q_s11_slice, d, hd']
      let x : ℝ := (1 / 5 : ℝ) * g * k
      have hpass : Real.exp (-x) * d ≤
          normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) := by
        have hh := hp.2.2 a
        rw [hden] at hh
        convert hh using 1 <;> simp [x] <;> ring
      have hexpCancel : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add]
        simp
      have hdnorm : d ≤ Real.exp x *
          normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) := by
        calc
          d = Real.exp x * (Real.exp (-x) * d) := by rw [← mul_assoc, hexpCancel]; ring
          _ ≤ Real.exp x * normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) :=
            mul_le_mul_of_nonneg_left hpass (Real.exp_nonneg _)
      have hratio : d / normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) ≤
          Real.exp x := by
        apply (div_le_iff₀ hp.1).2
        nlinarith [hdnorm]
      have hrowEq :
          oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t u) a) y =
            centerLik_q_s11_slice E G μ t y *
              (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y *
                (d / normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a)) := by
        rw [oddRowW, if_pos hp, hlikSplit, hdel y, hq]
        field_simp [hd.ne', hp.1.ne']
        <;> ring
      have hqnonneg := (deletionLaw_q_s11_slice E G μ ν y₀ u a).nonneg y
      calc
        oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t u) a) y =
            centerLik_q_s11_slice E G μ t y *
              (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y *
                (d / normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a)) := hrowEq
        _ ≤ centerLik_q_s11_slice E G μ t y *
              (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y * Real.exp x := by
            have hmul := mul_le_mul_of_nonneg_left hratio
              (mul_nonneg (hcenterNonneg y hy) hqnonneg)
            nlinarith [hmul]
        _ = (Real.exp x * centerLik_q_s11_slice E G μ t y) *
              (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y := by ring
        _ ≤ Real.exp ((Real.log 2 - 2 * g) * k) *
              (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y :=
            mul_le_mul_of_nonneg_right hcoef hqnonneg
    · have htermnonneg : 0 ≤ ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y :=
        mul_nonneg (ν.nonneg y) (hdelNonneg y)
      have htermle : ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y ≤ d := by
        have hs := Finset.single_le_sum
          (s := Finset.univ)
          (f := fun z => ν.w z * deletionLik_q_s11_slice E G μ y₀ u a z)
          (fun z hz => mul_nonneg (ν.nonneg z) (hdelNonneg z))
          (Finset.mem_univ y)
        simpa [d, deletionMass_q_s11_slice] using hs
      have htermzero : ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y = 0 := by
        have hd0 : d = 0 := le_antisymm (le_of_not_gt hd) hdnonneg
        have hle0 : ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y ≤ 0 := by
          simpa [hd0] using htermle
        exact le_antisymm hle0 htermnonneg
      have hrowzero :
          oddRowW (E := E) (G := G) (I := I) (k := k) g μ ν
            (ballStar (joinRadiusTwo_q_s11_slice t u) a) y = 0 := by
        rw [oddRowW, if_pos hp, hlikSplit, hdel y]
        calc
          ν.w y * (centerLik_q_s11_slice E G μ t y *
              deletionLik_q_s11_slice E G μ y₀ u a y) /
              normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) =
              centerLik_q_s11_slice E G μ t y *
                (ν.w y * deletionLik_q_s11_slice E G μ y₀ u a y) /
                  normZ E G μ ν (ballStar (joinRadiusTwo_q_s11_slice t u) a) := by ring
          _ = 0 := by rw [htermzero]; simp
      have hd' : ¬ 0 < ∑ z, ν.w z * deletionLik_q_s11_slice E G μ y₀ u a z := by
        simpa [d, deletionMass_q_s11_slice] using hd
      have hq : (deletionLaw_q_s11_slice E G μ ν y₀ u a).w y = ν.w y := by
        simp [deletionLaw_q_s11_slice, normalizeWeight_q_s11_slice,
          lawAsFinProb_q_s11_slice, deletionMass_q_s11_slice, d, hd']
      rw [hrowzero, hq]
      exact mul_nonneg (Real.exp_nonneg _) (ν.nonneg y)

theorem sigmaW_sum_eq_one_of_cutoff_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] (g : ℝ) (μ : Law N)
    (z : I → Fin N) (hN : 0 < (N : ℝ))
    (hcut : (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) ≤
      ((commonSet E G μ z).card : ℝ)) :
    ∑ x, sigmaW E G g μ z x = 1 := by
  classical
  let C := commonSet E G μ z
  have hcardpos : 0 < (C.card : ℝ) := by
    have hpos : 0 < (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) :=
      mul_pos hN (Real.exp_pos _)
    exact lt_of_lt_of_le hpos (by simpa [C] using hcut)
  have hcardne : (C.card : ℝ) ≠ 0 := ne_of_gt hcardpos
  calc
    (∑ x, sigmaW E G g μ z x) = (C.card : ℝ) * (C.card : ℝ)⁻¹ := by
      simp [sigmaW, C, hcut, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    _ = 1 := mul_inv_cancel₀ hcardne

theorem supported_function_mass_card_bound_q_s11_slice {N k : ℕ}
    (C : Finset (Fin N)) (p : (Fin k → Fin N) → ℝ) (M : ℝ)
    (hsum : ∑ t, p t = 1)
    (hzero : ∀ t, (¬ ∀ j, t j ∈ C) → p t = 0)
    (hbound : ∀ t, p t ≤ M) (hM : 0 ≤ M) :
    1 ≤ (C.card : ℝ) ^ k * M := by
  classical
  let S : Finset (Fin k → Fin N) := Finset.univ.filter fun t => ∀ j, t j ∈ C
  have hcardNat : S.card ≤ C.card ^ k := by
    let Ccoord := {x : Fin N // x ∈ C}
    let f : {t // t ∈ S} → (Fin k → Ccoord) := fun t j =>
      ⟨t.1 j, (Finset.mem_filter.mp t.2).2 j⟩
    have hf : Function.Injective f := by
      intro t t' h
      apply Subtype.ext
      funext j
      exact congrArg (fun x : Ccoord => x.1) (congrFun h j)
    have hc := Fintype.card_le_of_injective f hf
    have hc' : Fintype.card {t // t ∈ S} ≤ Fintype.card (Fin k → Ccoord) := by
      simpa [S] using hc
    calc
      S.card = Fintype.card {t // t ∈ S} := (Fintype.card_coe S).symm
      _ ≤ Fintype.card (Fin k → Ccoord) := hc'
      _ = C.card ^ k := by simp [Ccoord, Fintype.card_fun]
  have hsumUpper : 1 ≤ (S.card : ℝ) * M := by
    calc
      1 = ∑ t, p t := hsum.symm
      _ ≤ ∑ t, if t ∈ S then M else 0 := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases hmem : t ∈ S
        · simp [hmem]
          exact hbound t
        · have hnot : ¬ ∀ j, t j ∈ C := by
            intro hcoords
            exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcoords⟩)
          simp [hmem, hzero t hnot]
      _ = (S.card : ℝ) * M := by
        simp [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  have hcardCast : (S.card : ℝ) ≤ (C.card : ℝ) ^ k := by
    exact_mod_cast hcardNat
  exact hsumUpper.trans (mul_le_mul_of_nonneg_right hcardCast hM)

theorem sigma_parameters_q_s11_slice :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      1 ≤ n ∧ gS n ≤ 1 / 4 ∧
      8 ≤ (n : ℝ) ^ ((2 : ℝ) / 25) ∧
      2 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 10) ≤ Fintype.card (InnerCoord n) ∧
      Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100) ≤
        (1 / 2 : ℝ) * gS n * Fintype.card (InnerCoord n) := by
  have hGlim : Tendsto (fun n : ℕ => gS n) atTop (nhds 0) := by
    unfold gS
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_div] using h
  have hGsmall : ∀ᶠ n : ℕ in atTop, gS n < 1 / 4 :=
    hGlim.eventually (Iio_mem_nhds (by norm_num))
  have hpow08 : ∀ᶠ n : ℕ in atTop,
      8 ≤ (n : ℝ) ^ ((2 : ℝ) / 25) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (2 : ℝ) / 25)).comp
      tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop 8
  have hpow01 : ∀ᶠ n : ℕ in atTop,
      2 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop 2
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)
  obtain ⟨nG, hnG⟩ := Filter.eventually_atTop.1 hGsmall
  obtain ⟨n08, hn08⟩ := Filter.eventually_atTop.1 hpow08
  obtain ⟨n01, hn01⟩ := Filter.eventually_atTop.1 hpow01
  refine ⟨max n₀ (max nG (max n08 n01)), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := hn₀ n (le_trans (le_max_left n₀ _) hn)
  have houter : max nG (max n08 n01) ≤ n :=
    le_trans (le_max_right n₀ _) hn
  have hnG' : gS n < 1 / 4 :=
    hnG n (le_trans (le_max_left nG _) houter)
  have hn08' : 8 ≤ (n : ℝ) ^ ((2 : ℝ) / 25) := by
    apply hn08
    exact le_trans (le_max_left n08 n01) (le_trans (le_max_right nG _) houter)
  have hn01' : 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    apply hn01
    exact le_trans (le_max_right n08 n01) (le_trans (le_max_right nG _) houter)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnreal
  have hargLeN : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num : (1 : ℝ) / 10 ≤ 1))
  have hfloorLe : (hIn n : ℝ) ≤ (n : ℝ) := by
    unfold hIn
    exact (Nat.floor_le (by positivity)).trans hargLeN
  have hInLeN : hIn n ≤ n := by exact_mod_cast hfloorLe
  have hcardLowerNat : hIn n ≤ Fintype.card (InnerCoord n) := by
    let f : Fin (hIn n) → InnerCoord n := fun j =>
      ⟨⟨j.val, lt_of_lt_of_le j.isLt hInLeN⟩, j.isLt⟩
    have hf : Function.Injective f := by
      intro j j' h
      apply Fin.ext
      exact congrArg (fun x : InnerCoord n => x.val.val) h
    simpa [InnerCoord] using Fintype.card_le_of_injective f hf
  have hcardCast : (hIn n : ℝ) ≤ (Fintype.card (InnerCoord n) : ℝ) := by
    exact_mod_cast hcardLowerNat
  have hfloorLt : (n : ℝ) ^ ((1 : ℝ) / 10) < (hIn n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((n : ℝ) ^ ((1 : ℝ) / 10))
  have hfloorLower : (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (hIn n : ℝ) := by
    nlinarith [hn01', hfloorLt]
  have hcardMain : (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 10) ≤
      (Fintype.card (InnerCoord n) : ℝ) := hfloorLower.trans hcardCast
  have hn01pow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hnreal (by norm_num)
  have hpowMul : (n : ℝ) ^ ((1 : ℝ) / 100) * (n : ℝ) ^ ((2 : ℝ) / 25) =
      (n : ℝ) ^ ((9 : ℝ) / 100) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  have hgmul : gS n * (n : ℝ) ^ ((1 : ℝ) / 10) =
      (n : ℝ) ^ ((9 : ℝ) / 100) := by
    unfold gS
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  have hgeom : (1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 100) ≤
      (1 / 2 : ℝ) * gS n * (Fintype.card (InnerCoord n) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hcardMain
      (show 0 ≤ gS n by unfold gS; positivity)
    nlinarith [hmul, hgmul]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsmall : Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100) ≤
      (1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 100) := by
    rw [← hpowMul]
    nlinarith [hn01pow, hn08']
  have hmargin := hsmall.trans hgeom
  exact ⟨hn1, le_of_lt hnG', hn08', hn01', hcardMain, hmargin⟩

end

end HypercubeRamsey.Lane_q_s11_slice
