import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S15.Needs
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S15.DirectNodes_q_s15_direct

namespace HypercubeRamsey.Lane_sol_s15_cross

open HypercubeRamsey Filter
open scoped BigOperators

set_option maxHeartbeats 600000

/-- The numerical step in the crossing exposure: a balanced hit mass divided
by denominators in the cleaned window stays between two exponential gates. -/
theorem ratio_window {b t d : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1 / 100)
    (ht : |t - 1 / 2| ≤ b) (hd : |d - 1 / 2| ≤ 3 * b) :
    Real.exp (-10 * b) ≤ t / d ∧ t / d ≤ Real.exp (10 * b) := by
  have ht' := abs_le.mp ht
  have hd' := abs_le.mp hd
  have hdpos : 0 < d := by linarith
  have hsq : b * b ≤ (1 / 100 : ℝ) * b := mul_le_mul_of_nonneg_right hsmall hb
  have hden : 0 < 1 + 10 * b := by linarith
  have hlo : 1 / (1 + 10 * b) ≤ t / d := by
    apply (div_le_div_iff₀ hden hdpos).2
    have hmul := mul_le_mul_of_nonneg_right ht'.1 hden.le
    nlinarith
  have hhi : t / d ≤ 1 + 10 * b := by
    apply (div_le_iff₀ hdpos).2
    have hmul := mul_le_mul_of_nonneg_left hd'.1 hden.le
    nlinarith
  constructor
  · have he : 1 + 10 * b ≤ Real.exp (10 * b) := by simpa [add_comm] using Real.add_one_le_exp (10 * b)
    calc
      Real.exp (-10 * b) = 1 / Real.exp (10 * b) := by rw [show -10 * b = -(10 * b) by ring, Real.exp_neg, one_div]
      _ ≤ 1 / (1 + 10 * b) := one_div_le_one_div_of_le hden he
      _ ≤ t / d := hlo
  · exact hhi.trans (by simpa [add_comm] using Real.add_one_le_exp (10 * b))

/-- Integrating ratios with varying denominators in a cleaned window gives
the same gates as the single-denominator calculation. -/
theorem ratio_filter_window {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) {b : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1 / 100)
    (hdeg : ∀ x, μ.w x ≠ 0 → |deg E c ν.w x - 1 / 2| ≤ 3 * b)
    (y : Fin N) (hy : |colDeg E c μ y - 1 / 2| ≤ b) :
    Real.exp (-10 * b) ≤ ∑ x, μ.w x * S15.normalizedHit E c ν x y ∧
      (∑ x, μ.w x * S15.normalizedHit E c ν x y) ≤ Real.exp (10 * b) := by
  classical
  let dl := 1 / 2 - 3 * b
  let du := 1 / 2 + 3 * b
  have hdl : 0 < dl := by dsimp [dl]; linarith
  have hdu : 0 < du := by dsimp [du]; linarith
  have hit_nonneg (x : Fin N) : 0 ≤ hit E c x y := by unfold hit; split_ifs <;> norm_num
  have hlow : colDeg E c μ y / du ≤ ∑ x, μ.w x * S15.normalizedHit E c ν x y := by
    unfold colDeg
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hzero : μ.w x = 0
    · simp [hzero]
    · have hd := abs_le.mp (hdeg x hzero)
      have hdpos : 0 < deg E c ν.w x := by dsimp [dl] at hdl; linarith
      simp only [S15.normalizedHit, if_pos hdpos]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
      apply div_le_div_of_nonneg_left (hit_nonneg x) hdpos
      dsimp [du]
      linarith
  have hhigh : (∑ x, μ.w x * S15.normalizedHit E c ν x y) ≤ colDeg E c μ y / dl := by
    unfold colDeg
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hzero : μ.w x = 0
    · simp [hzero]
    · have hd := abs_le.mp (hdeg x hzero)
      have hdpos : 0 < deg E c ν.w x := by dsimp [dl] at hdl; linarith
      simp only [S15.normalizedHit, if_pos hdpos]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
      apply div_le_div_of_nonneg_left (hit_nonneg x) hdl
      dsimp [dl]
      linarith
  exact ⟨(ratio_window hb hsmall hy (by dsimp [du]; rw [show 1 / 2 + 3 * b - 1 / 2 = 3 * b by ring, abs_of_nonneg (by positivity : 0 ≤ 3 * b)])).1.trans hlow,
    hhigh.trans (ratio_window hb hsmall hy (by dsimp [dl]; rw [show 1 / 2 - 3 * b - 1 / 2 = -(3 * b) by ring, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 3 * b)])).2⟩

/-- One ratio filter has an exponentially small exceptional set whenever
the entering first law and the new second law fit the discrepancy budgets. -/
theorem ratio_filter_tail {T : Stage} {k : ℕ} {wS wL w : ℝ}
    (hD : TwoBudgetDisc T k wS wL (bstar T k)) (c : Colour)
    (μ ν : Law (T.S.N k)) (hμ : μ.SupportedIn (T.X k)) (hwμ : μ.WidthLE wS)
    (hν : ν.SupportedIn (T.Y k)) (hwν : ν.WidthLE w)
    (hb : 0 ≤ bstar T k) (hsmall : bstar T k ≤ 1 / 100)
    (hdeg : ∀ x, μ.w x ≠ 0 → |deg (T.S.E k) c ν.w x - 1 / 2| ≤ 3 * bstar T k) :
    ν.pr (fun y => ¬ (Real.exp (-10 * bstar T k) ≤
      (∑ x, μ.w x * S15.normalizedHit (T.S.E k) c ν x y) ∧
      (∑ x, μ.w x * S15.normalizedHit (T.S.E k) c ν x y) ≤
        Real.exp (10 * bstar T k))) ≤ 2 * Real.exp (w - wL) := by
  classical
  have htail := S15.Needs.exceptional_second hD c (Or.inl ⟨le_rfl, le_rfl⟩)
    μ ν hμ hwμ hν hwν
  have hmono : ν.pr (fun y => ¬ (Real.exp (-10 * bstar T k) ≤
      (∑ x, μ.w x * S15.normalizedHit (T.S.E k) c ν x y) ∧
      (∑ x, μ.w x * S15.normalizedHit (T.S.E k) c ν x y) ≤ Real.exp (10 * bstar T k))) ≤
    ν.pr (fun y => bstar T k < |colDeg (T.S.E k) c μ y - 1 / 2|) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro y hmem
    by_cases hbad : bstar T k < |colDeg (T.S.E k) c μ y - 1 / 2|
    · simp only [if_pos hbad]
      split_ifs <;> simp [ν.nonneg y]
    · have hgood := ratio_filter_window (T.S.E k) c μ ν hb hsmall hdeg y (le_of_not_gt hbad)
      rw [if_neg (not_not.mpr hgood), if_neg hbad]
  exact hmono.trans (by simpa [FinProb.pr, ← Finset.sum_filter] using htail)

open HypercubeRamsey
open scoped BigOperators

set_option maxHeartbeats 400000

theorem pi_weight_resample {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (b : ι) (ω : ∀ i, Ω i) (y : Ω b) :
    (FinProb.pi P).w (Function.update ω b y) * (P b).w (ω b) =
      (FinProb.pi P).w ω * (P b).w y := by
  classical
  have hrest : (∏ i ∈ Finset.univ.erase b, (P i).w (Function.update ω b y i)) =
      ∏ i ∈ Finset.univ.erase b, (P i).w (ω i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  change (∏ i, (P i).w (Function.update ω b y i)) * (P b).w (ω b) =
    (∏ i, (P i).w (ω i)) * (P b).w y
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ b), hrest]
  simp
  ring

theorem pi_expect_resample {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (b : ι) (F : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect (fun ω => (P b).expect (fun y => F (Function.update ω b y))) =
      (FinProb.pi P).expect F := by
  classical
  let swap : ((∀ i, Ω i) × Ω b) → ((∀ i, Ω i) × Ω b) :=
    fun p => (Function.update p.1 b p.2, p.1 b)
  have hinvol : Function.Involutive swap := by
    intro p
    rcases p with ⟨ω, y⟩
    simp [swap]
  let e : ((∀ i, Ω i) × Ω b) ≃ ((∀ i, Ω i) × Ω b) :=
    { toFun := swap, invFun := swap, left_inv := hinvol, right_inv := hinvol }
  have hswap := Equiv.sum_comp e (fun p : ((∀ i, Ω i) × Ω b) =>
    (FinProb.pi P).w p.1 * (P b).w p.2 * F (Function.update p.1 b p.2))
  have hpoint (p : ((∀ i, Ω i) × Ω b)) :
      (FinProb.pi P).w (e p).1 * (P b).w (e p).2 * F (Function.update (e p).1 b (e p).2) =
        (FinProb.pi P).w p.1 * (P b).w p.2 * F p.1 := by
    change (FinProb.pi P).w (Function.update p.1 b p.2) * (P b).w (p.1 b) *
      F (Function.update (Function.update p.1 b p.2) b (p.1 b)) = _
    rw [pi_weight_resample]
    simp
  simp_rw [hpoint] at hswap
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hswap
  have hleft : (∑ ω, ∑ y, (FinProb.pi P).w ω * (P b).w y * F ω) =
      (FinProb.pi P).expect F := by
    simp_rw [mul_assoc, mul_comm ((P b).w _) (F _), ← mul_assoc, ← Finset.mul_sum]
    simp [FinProb.expect, (P b).sum_eq_one]
  rw [hleft] at hswap
  rw [hswap]
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro y hy
  ring


open HypercubeRamsey Filter
open scoped BigOperators
set_option maxHeartbeats 600000

structure CrossingExperiment (T : Stage) (k : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type*) [∀ i, Fintype (Ω i)] where
  P : ∀ i, FinProb (Ω i)
  label : ∀ i, Ω i → Fin (T.S.N k)
  ν : ι → Law (T.S.N k)
  marginal : ∀ i, ν i = FinProb.map (P i) (label i)
  c : Colour
  C : Finset ι
  μ : (∀ i, Ω i) → Law (T.S.N k)
  A : (∀ i, Ω i) → Prop
  μ_update : ∀ b ∈ C, ∀ ω y, μ (Function.update ω b y) = μ ω
  A_update : ∀ b ∈ C, ∀ ω y, A (Function.update ω b y) ↔ A ω

private theorem law_ext {N : ℕ} (P Q : Law N) (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

namespace CrossingExperiment
open Classical
variable {T : Stage} {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

noncomputable def weight (Q : CrossingExperiment T k ι Ω) (S : Finset ι)
    (ω : ∀ i, Ω i) (x : Fin (T.S.N k)) : ℝ :=
  (Q.μ ω).w x * ∏ i ∈ S, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))

noncomputable def mass (Q : CrossingExperiment T k ι Ω) (S : Finset ι)
    (ω : ∀ i, Ω i) : ℝ := ∑ x, Q.weight S ω x

def Good (Q : CrossingExperiment T k ι Ω) (S : Finset ι) (ω : ∀ i, Ω i) : Prop :=
  Real.exp (-10 * S.card * bstar T k) ≤ Q.mass S ω ∧
    Q.mass S ω ≤ Real.exp (10 * S.card * bstar T k)

theorem normalizedHit_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (ν : Law N) (x y : Fin N) : 0 ≤ S15.normalizedHit E c ν x y := by
  classical
  unfold S15.normalizedHit
  dsimp only
  split_ifs with h
  · apply div_nonneg _ h.le
    unfold hit
    split_ifs <;> norm_num
  · exact le_rfl

theorem weight_nonneg (Q : CrossingExperiment T k ι Ω) (S : Finset ι)
    (ω : ∀ i, Ω i) (x : Fin (T.S.N k)) : 0 ≤ Q.weight S ω x := by
  exact mul_nonneg ((Q.μ ω).nonneg x)
    (Finset.prod_nonneg fun i _ => normalizedHit_nonneg _ _ _ _ _)

noncomputable def entering (Q : CrossingExperiment T k ι Ω) (S : Finset ι)
    (ω : ∀ i, Ω i) : Law (T.S.N k) :=
  if h : 0 < Q.mass S ω then
    { w := fun x => Q.weight S ω x / Q.mass S ω
      nonneg := fun x => div_nonneg (Q.weight_nonneg S ω x) h.le
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self h.ne' }
  else Q.μ ω

theorem weight_update (Q : CrossingExperiment T k ι Ω) {S : Finset ι}
    {b : ι} (hb : b ∈ Q.C) (hnot : b ∉ S) (ω : ∀ i, Ω i) (y : Ω b)
    (x : Fin (T.S.N k)) : Q.weight S (Function.update ω b y) x = Q.weight S ω x := by
  unfold weight
  rw [Q.μ_update b hb ω y]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i ≠ b := by intro he; subst i; exact hnot hi
  rw [Function.update_of_ne hne]

theorem mass_update (Q : CrossingExperiment T k ι Ω) {S : Finset ι}
    {b : ι} (hb : b ∈ Q.C) (hnot : b ∉ S) (ω : ∀ i, Ω i) (y : Ω b) :
    Q.mass S (Function.update ω b y) = Q.mass S ω := by
  unfold mass
  exact Finset.sum_congr rfl (fun x _ => Q.weight_update hb hnot ω y x)

theorem entering_update (Q : CrossingExperiment T k ι Ω) {S : Finset ι}
    {b : ι} (hb : b ∈ Q.C) (hnot : b ∉ S) (ω : ∀ i, Ω i) (y : Ω b) :
    Q.entering S (Function.update ω b y) = Q.entering S ω := by
  apply law_ext
  funext x
  simp only [entering, Q.mass_update hb hnot ω y]
  split_ifs with h
  · exact congrArg (fun z => z / Q.mass S ω) (Q.weight_update hb hnot ω y x)
  · exact congrArg (fun μ => μ.w x) (Q.μ_update b hb ω y)

theorem mass_insert (Q : CrossingExperiment T k ι Ω) {S : Finset ι} {b : ι}
    (hnot : b ∉ S) (ω : ∀ i, Ω i) (hpos : 0 < Q.mass S ω) :
    Q.mass (insert b S) ω = Q.mass S ω *
      ∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b (ω b)) := by
  classical
  unfold mass weight
  simp only [Finset.prod_insert hnot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [entering, dif_pos hpos]
  change _ = _ * ((Q.weight S ω x / Q.mass S ω) * _)
  unfold weight
  field_simp [hpos.ne']
  rfl

noncomputable def Step (Q : CrossingExperiment T k ι Ω) (S : Finset ι)
    (b : ι) (ω : ∀ i, Ω i) : Prop :=
  Real.exp (-10 * bstar T k) ≤
    (∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b (ω b))) ∧
    (∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b (ω b))) ≤
      Real.exp (10 * bstar T k)

theorem good_insert (Q : CrossingExperiment T k ι Ω) {S : Finset ι} {b : ι}
    (hnot : b ∉ S) (ω : ∀ i, Ω i) (hgood : Q.Good S ω) (hstep : Q.Step S b ω) :
    Q.Good (insert b S) ω := by
  have hpos : 0 < Q.mass S ω := (Real.exp_pos _).trans_le hgood.1
  have hmul := Q.mass_insert hnot ω hpos
  constructor
  · rw [hmul, Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    calc
      Real.exp (-10 * ((S.card : ℝ) + 1) * bstar T k) =
          Real.exp (-10 * S.card * bstar T k) * Real.exp (-10 * bstar T k) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Q.mass S ω * _ := mul_le_mul hgood.1 hstep.1 (Real.exp_pos _).le hpos.le
  · rw [hmul, Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    calc
      Q.mass S ω * _ ≤ Real.exp (10 * S.card * bstar T k) * Real.exp (10 * bstar T k) :=
        mul_le_mul hgood.2 hstep.2 (le_trans (Real.exp_pos _).le hstep.1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedHit_le_four {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (ν : Law N) {b : ℝ} (hb : b ≤ 1 / 100) (x y : Fin N)
    (hdeg : |deg E c ν.w x - 1 / 2| ≤ 3 * b) :
    S15.normalizedHit E c ν x y ≤ 4 := by
  classical
  have hd := abs_le.mp hdeg
  have hpos : 0 < deg E c ν.w x := by linarith
  have hhit : hit E c x y ≤ 1 := by unfold hit; split_ifs <;> norm_num
  simp only [S15.normalizedHit, if_pos hpos]
  apply (div_le_iff₀ hpos).2
  linarith

theorem entering_properties (Q : CrossingExperiment T k ι Ω) {w0 wS : ℝ}
    (hN : 0 < T.S.N k) (hsmall : bstar T k ≤ 1 / 100)
    (hbudget : w0 + (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ wS)
    (hb : 0 ≤ bstar T k) (ω : ∀ i, Ω i)
    (hsupp : (Q.μ ω).SupportedIn (T.X k)) (hw : (Q.μ ω).WidthLE w0)
    (hdeg : ∀ i ∈ Q.C, ∀ x, (Q.μ ω).w x ≠ 0 →
      |deg (T.S.E k) Q.c (Q.ν i).w x - 1 / 2| ≤ 3 * bstar T k)
    {S : Finset ι} (hS : S ⊆ Q.C) (hgood : Q.Good S ω) :
    (Q.entering S ω).SupportedIn (T.X k) ∧ (Q.entering S ω).WidthLE wS ∧
      (∀ i ∈ Q.C, ∀ x, (Q.entering S ω).w x ≠ 0 →
        |deg (T.S.E k) Q.c (Q.ν i).w x - 1 / 2| ≤ 3 * bstar T k) := by
  classical
  have hpos : 0 < Q.mass S ω := (Real.exp_pos _).trans_le hgood.1
  have heq (x) : (Q.entering S ω).w x = Q.weight S ω x / Q.mass S ω := by
    simp [entering, hpos]
  have hbase (x) (hx : (Q.entering S ω).w x ≠ 0) : (Q.μ ω).w x ≠ 0 := by
    intro hzero
    apply hx
    simp [heq, weight, hzero]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [heq]
    simp [weight, hsupp x hx]
  · intro x
    have hprod : Q.weight S ω x ≤ (Q.μ ω).w x * (4 : ℝ) ^ S.card := by
      by_cases hzero : (Q.μ ω).w x = 0
      · simp [weight, hzero]
      · unfold weight
        apply mul_le_mul_of_nonneg_left _ ((Q.μ ω).nonneg x)
        calc
          (∏ i ∈ S, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))) ≤
              ∏ i ∈ S, (4 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact normalizedHit_nonneg _ _ _ _ _
            · intro i hi
              exact normalizedHit_le_four _ _ _ hsmall _ _ (hdeg i (hS hi) x hzero)
          _ = _ := by simp
    have harg : w0 + (S.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ wS := by
      have hcards : (S.card : ℝ) ≤ Q.C.card := by exact_mod_cast Finset.card_le_card hS
      have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hcards (by positivity : 0 ≤ Real.log 4 + 10 * bstar T k)
      linarith
    rw [heq]
    calc
      Q.weight S ω x / Q.mass S ω ≤ ((Q.μ ω).w x * (4 : ℝ) ^ S.card) /
          Real.exp (-10 * S.card * bstar T k) :=
        div_le_div₀ (mul_nonneg ((Q.μ ω).nonneg x) (by positivity)) hprod
          (Real.exp_pos _) hgood.1
      _ ≤ ((Real.exp w0 / T.S.N k) * (4 : ℝ) ^ S.card) /
          Real.exp (-10 * S.card * bstar T k) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hw x) (by positivity)) (Real.exp_pos _).le
      _ = Real.exp (w0 + (S.card : ℝ) * (Real.log 4 + 10 * bstar T k)) / T.S.N k := by
        rw [show (4 : ℝ) ^ S.card = Real.exp ((S.card : ℝ) * Real.log 4) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]]
        have he : Real.exp w0 * Real.exp ((S.card : ℝ) * Real.log 4) /
            Real.exp (-10 * S.card * bstar T k) =
              Real.exp (w0 + (S.card : ℝ) * (Real.log 4 + 10 * bstar T k)) := by
          rw [← Real.exp_add, ← Real.exp_sub]
          congr 1
          ring
        calc
          _ = (Real.exp w0 * Real.exp ((S.card : ℝ) * Real.log 4) /
              Real.exp (-10 * S.card * bstar T k)) / T.S.N k := by ring
          _ = _ := by rw [he]
      _ ≤ Real.exp wS / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg) (by positivity)
  · intro i hi x hx
    exact hdeg i hi x (hbase x hx)

theorem pr_eq_indicator {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A = P.expect (fun x => if A x then 1 else 0) := by
  classical
  simp [FinProb.pr, FinProb.expect, mul_ite]

theorem pr_mono {α : Type*} [Fintype α] (P : FinProb α) {A B : α → Prop}
    (h : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases hA : A x
  · simp [hA, h x hA]
  · simp only [if_neg hA]
    split_ifs <;> simp [P.nonneg x]

theorem map_pr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (f : α → β) (A : β → Prop) :
    (FinProb.map P f).pr A = P.pr (fun x => A (f x)) := by
  classical
  unfold FinProb.pr FinProb.map
  calc
    (∑ b, if A b then (∑ a, if f a = b then P.w a else 0) else 0) =
        ∑ b, ∑ a, if f a = b ∧ A b then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hA : A b <;> simp [hA]
    _ = ∑ a, ∑ b, if f a = b ∧ A b then P.w a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro b hb hne
        simp [Ne.symm hne]
      · simp

theorem resample_pr_bound (P : ∀ i, FinProb (Ω i)) (b : ι)
    (A : (∀ i, Ω i) → Prop) {δ : ℝ}
    (h : ∀ ω, (P b).pr (fun y => A (Function.update ω b y)) ≤ δ) :
    (FinProb.pi P).pr A ≤ δ := by
  classical
  rw [pr_eq_indicator, ← pi_expect_resample P b]
  calc
    (FinProb.pi P).expect (fun ω => (P b).expect
        (fun y => if A (Function.update ω b y) then 1 else 0)) ≤
      (FinProb.pi P).expect (fun _ => δ) := by
        apply FinProb.expect_mono
        intro ω
        rw [← pr_eq_indicator]
        exact h ω
    _ = δ := FinProb.expect_const _ _

theorem product_tail (Q : CrossingExperiment T k ι Ω) {w0 wS wL w : ℝ}
    (hD : TwoBudgetDisc T k wS wL (bstar T k))
    (hN : 0 < T.S.N k) (hb : 0 ≤ bstar T k) (hsmall : bstar T k ≤ 1 / 100)
    (hbudget : w0 + (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ wS)
    (hμ : ∀ ω, Q.A ω → (Q.μ ω).SupportedIn (T.X k))
    (hwμ : ∀ ω, Q.A ω → (Q.μ ω).WidthLE w0)
    (hν : ∀ i ∈ Q.C, (Q.ν i).SupportedIn (T.Y k))
    (hwν : ∀ i ∈ Q.C, (Q.ν i).WidthLE w)
    (hdeg : ∀ ω, Q.A ω → ∀ i ∈ Q.C, ∀ x, (Q.μ ω).w x ≠ 0 →
      |deg (T.S.E k) Q.c (Q.ν i).w x - 1 / 2| ≤ 3 * bstar T k) :
    (FinProb.pi Q.P).pr (fun ω => Q.A ω ∧ ¬ Q.Good Q.C ω) ≤
      Q.C.card * (2 * Real.exp (w - wL)) := by
  classical
  let δ := 2 * Real.exp (w - wL)
  have hδ : 0 ≤ δ := by positivity
  have hpartial : ∀ S : Finset ι, S ⊆ Q.C →
      (FinProb.pi Q.P).pr (fun ω => Q.A ω ∧ ¬ Q.Good S ω) ≤ (S.card : ℝ) * δ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro hS
      have hmass (ω) : Q.mass ∅ ω = 1 := by simp [mass, weight, (Q.μ ω).sum_eq_one]
      simp [FinProb.pr, Good, hmass]
    | @insert b S hnot ih =>
      intro hSC
      have hbC : b ∈ Q.C := hSC (Finset.mem_insert_self _ _)
      have hS : S ⊆ Q.C := fun i hi => hSC (Finset.mem_insert_of_mem hi)
      have hnext : (FinProb.pi Q.P).pr
          (fun ω => Q.A ω ∧ Q.Good S ω ∧ ¬ Q.Step S b ω) ≤ δ := by
        apply resample_pr_bound Q.P b
        intro ω
        have hA (y : Ω b) := Q.A_update b hbC ω y
        have hG (y : Ω b) : Q.Good S (Function.update ω b y) ↔ Q.Good S ω := by
          simp only [Good, Q.mass_update hbC hnot ω y]
        by_cases ha : Q.A ω
        · by_cases hg : Q.Good S ω
          · obtain ⟨hsupp, hwidth, hdegrees⟩ := Q.entering_properties hN hsmall hbudget hb ω
              (hμ ω ha) (hwμ ω ha) (hdeg ω ha) hS hg
            have htail := ratio_filter_tail hD Q.c (Q.entering S ω) (Q.ν b)
              hsupp hwidth (hν b hbC) (hwν b hbC) hb hsmall (hdegrees b hbC)
            have hmap : (Q.P b).pr (fun y => ¬ (
                Real.exp (-10 * bstar T k) ≤ (∑ x, (Q.entering S ω).w x *
                  S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y)) ∧
                (∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y)) ≤
                  Real.exp (10 * bstar T k))) ≤ δ := by
              rw [← map_pr (Q.P b) (Q.label b) (fun y =>
                ¬ (Real.exp (-10 * bstar T k) ≤
                    (∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x y) ∧
                    (∑ x, (Q.entering S ω).w x * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x y) ≤
                      Real.exp (10 * bstar T k)))]
              rw [← Q.marginal b]
              exact htail
            convert hmap using 1
            apply congrArg (Q.P b).pr
            funext y
            apply propext
            simp only [hA y, hG y, ha, hg, true_and, Step,
              Q.entering_update hbC hnot ω y, Function.update_self]
          · have he : (Q.P b).pr (fun y => Q.A (Function.update ω b y) ∧
                Q.Good S (Function.update ω b y) ∧ ¬ Q.Step S b (Function.update ω b y)) = 0 := by
              simp [FinProb.pr, hG, hg]
            rw [he]
            exact hδ
        · have he : (Q.P b).pr (fun y => Q.A (Function.update ω b y) ∧
              Q.Good S (Function.update ω b y) ∧ ¬ Q.Step S b (Function.update ω b y)) = 0 := by
            simp [FinProb.pr, hA, ha]
          rw [he]
          exact hδ
      have hsub : (FinProb.pi Q.P).pr (fun ω => Q.A ω ∧ ¬ Q.Good (insert b S) ω) ≤
          (FinProb.pi Q.P).pr (fun ω => (Q.A ω ∧ ¬ Q.Good S ω) ∨
            (Q.A ω ∧ Q.Good S ω ∧ ¬ Q.Step S b ω)) := by
        apply pr_mono
        rintro ω ⟨ha, hbad⟩
        by_cases hg : Q.Good S ω
        · exact Or.inr ⟨ha, hg, fun hs => hbad (Q.good_insert hnot ω hg hs)⟩
        · exact Or.inl ⟨ha, hg⟩
      have hu := FinProb.pr_union (FinProb.pi Q.P)
        (fun ω => Q.A ω ∧ ¬ Q.Good S ω) (fun ω => Q.A ω ∧ Q.Good S ω ∧ ¬ Q.Step S b ω)
      have hsum := hsub.trans (hu.trans (add_le_add (ih hS) hnext))
      simpa [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hsum
  exact hpartial Q.C (Finset.Subset.refl _)

end CrossingExperiment

end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey Filter
open scoped BigOperators
set_option maxHeartbeats 600000

variable {κ : CConsts} {T : Stage} {k : ℕ}

theorem highDirect_envelope_nonempty (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (i : Fin PT.tiling.m) : (PT.envelope i).Nonempty := by
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hsize := Lane_q_s15_direct.highDirect_envelope_card_lower PT hPT hm i
  apply Finset.card_pos.mp
  have hsizeR : ((PT.tiling.P i).M : ℝ) / 2 ≤ ((PT.envelope i).card : ℝ) := hsize
  exact_mod_cast (show (0 : ℝ) < (PT.envelope i).card by linarith)

noncomputable def directBaseLaw (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) : Law (T.S.N k) :=
  FinProb.uniform (PT.envelope (S15.patchAt PT hPT a.1))
    (highDirect_envelope_nonempty PT hPT hm _)

theorem directBaseLaw_w (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) (x : Fin (T.S.N k)) :
    (directBaseLaw PT hPT hm a).w x = S15.directBaseWeight PT hPT a x := rfl

theorem law_width_of_cap {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (P : Law N) {C v : ℝ} (hC : 0 < C)
    (hcap : ∀ x, (M : ℝ) * P.w x ≤ C)
    (hlog : Real.log ((N : ℝ) / M) ≤ v) : P.WidthLE (Real.log C + v) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  intro x
  calc
    P.w x ≤ C / M := (le_div_iff₀ hMR).2 (by simpa [mul_comm] using hcap x)
    _ = Real.exp (Real.log C + Real.log ((N : ℝ) / M)) / N := by
      rw [Real.exp_add, Real.exp_log hC, Real.exp_log (div_pos hNR hMR)]
      field_simp
    _ ≤ Real.exp (Real.log C + v) / N :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hNR.le

theorem direct_patch_log_width (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (hn : 1 ≤ (T.S.n k : ℝ)) (i : Fin PT.tiling.m) :
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ (T.S.n k : ℝ) ^ κ.ι := by
  have hu : (1 : ℝ) ≤ κ.u := by exact_mod_cast (show 1 ≤ κ.u by have := hκ.u_rng.2; omega)
  rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | ⟨_, hlog⟩
  · rw [hm] at hb; cases hb
  have hg := hPT.tiling_valid.direct_scale_bound (Or.inr hm) i
  have hpow := Real.rpow_le_rpow_of_exponent_le hn (show κ.ι / 2 ≤ κ.ι by linarith [hκ.ι_rng.1])
  have hgain : PT.tiling.gain i ≤ (T.S.n k : ℝ) ^ κ.ι := by
    simp only [Tiling.gain, hm]
    have hg0 : (0 : ℝ) ≤ (PT.tiling.P i).g := by positivity
    linarith
  have hgain0 : 0 ≤ PT.tiling.gain i := by simp [Tiling.gain, hm]; positivity
  have hdiv : PT.tiling.gain i / (1000 * (κ.u : ℝ)) ≤ PT.tiling.gain i := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (κ.u : ℝ))).2
    nlinarith
  exact hlog.trans (hdiv.trans hgain)

theorem exp_window_abs {r ℓ : ℕ} {b M : ℝ} (hb : 0 ≤ b) (hr : r ≤ ℓ)
    (hlo : Real.exp (-10 * r * b) ≤ M) (hhi : M ≤ Real.exp (10 * r * b)) :
    |M - 1| ≤ Real.exp (20 * ℓ * b) - 1 := by
  have harg : 10 * (r : ℝ) * b ≤ 20 * (ℓ : ℝ) * b := by
    have hc : (r : ℝ) ≤ ℓ := by exact_mod_cast hr
    have hm := mul_le_mul_of_nonneg_right hc hb
    nlinarith [show (0 : ℝ) ≤ ℓ by positivity]
  have he := Real.exp_le_exp.mpr harg
  have ha := Real.add_one_le_exp (10 * (r : ℝ) * b)
  have hb' := Real.add_one_le_exp (-10 * (r : ℝ) * b)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def directExperiment (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) :
    CrossingExperiment T k (S15.OddPosition T k) (fun _ => Fin (T.S.N k)) where
  P := S15.lawAtOdd PT hPT
  label := fun _ y => y
  ν := S15.lawAtOdd PT hPT
  marginal := by
    intro b
    apply FinProb.ext
    intro y
    simp [FinProb.map]
  c := PT.tiling.c
  C := S15.crossingNeighbours PT hPT a
  μ := fun _ => directBaseLaw PT hPT hm a
  A := fun _ => True
  μ_update := by intros; rfl
  A_update := by intros; rfl

 theorem crossing_parameters (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) ∧ bstar T k ≤ 1 / 100 ∧
      20 * (T.S.n k : ℝ) ^ κ.ι ≤ (T.S.n k : ℝ) ^ κ.xs ∧
      20 * (T.S.n k : ℝ) ^ κ.ι ≤ κ.α * T.S.n k / 2 ∧
      8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hιxs : κ.ι < κ.xs := by
    have hi := hκ.ι_rng.2
    have hm := min_le_left κ.xs (min κ.η0 (0.01 : ℝ))
    linarith [hκ.xs_rng.1]
  have hι1 : κ.ι < 1 := by linarith [hκ.xs_rng.2]
  have hs := hn.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι κ.xs 20 1 hιxs (by norm_num))
  have hl := hn.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι 1 20 (κ.α / 2) hι1 (by positivity [hκ.α_rng.1]))
  have hblim : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show (0 : ℝ) < 0.96 by norm_num)).comp hn using 1
    funext k
    norm_num [bstar]
  have hb := hblim.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  have htailim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((κ.R : ℝ) + 2)
    (κ.α / 2) (by positivity [hκ.α_rng.1])).const_mul 8).comp hn
  have ht := htailim.eventually (Iic_mem_nhds (show 8 * (0 : ℝ) < 1 by norm_num))
  filter_upwards [hn.eventually (eventually_ge_atTop 1), hs, hl, hb, ht] with k hk hs hl hb ht
  change 1 ≤ (T.S.n k : ℝ) at hk
  refine ⟨hk, hb, by simpa using hs, by simpa [Real.rpow_one, div_mul_eq_mul_div] using hl, ?_⟩
  have hpos : (0 : ℝ) < T.S.n k := by linarith
  have hmul := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hpos.le (-(κ.R : ℝ)))
  have he : (T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) =
      (T.S.n k : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hneg : -(κ.α / 2) * (T.S.n k : ℝ) = -κ.α * T.S.n k / 2 := by ring
  dsimp at hmul
  rw [hneg] at hmul
  calc
    8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) =
        (8 * ((T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * Real.exp (-κ.α * T.S.n k / 2))) *
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by rw [← he]; ring
    _ ≤ 1 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := hmul
    _ = _ := one_mul _

end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey Filter
open scoped BigOperators
open Classical
set_option maxHeartbeats 600000

theorem direct_crossing_exp_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highDirect, ∀ a : S15.EvenPosition T k,
        (S15.directRawLaw PT hPT).pr (fun ys =>
          |S15.directCrossingMass PT hPT ys a - 1| >
            Real.exp (20 * (PT.tiling.P (S15.patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
              2 * (T.S.n k : ℝ) * Real.exp (-κ.α * T.S.n k / 2) := by
  filter_upwards [hDeep, crossing_parameters κ hκ T] with k hD hp
  intro PT hPT hm a
  rcases hp with ⟨hn, hb, hs, hl, ht⟩
  let i := S15.patchAt PT hPT a.1
  let Q := directExperiment PT hPT hm a
  let n := (T.S.n k : ℝ)
  have hN := T.S.N_pos k
  have hpow : 1 ≤ n ^ κ.ι := Real.one_le_rpow hn hκ.ι_rng.1.le
  have hb0 : 0 ≤ bstar T k := by unfold bstar; positivity
  have hM (j : Fin PT.tiling.m) : 0 < (PT.tiling.P j).M := by
    rw [← (PT.tiling.P j).cardX]
    exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty j).1
  have hMR (j : Fin PT.tiling.m) : (0 : ℝ) < (PT.tiling.P j).M := by exact_mod_cast hM j
  have hμ : ∀ ys, Q.A ys → (Q.μ ys).SupportedIn (T.X k) := by
    intro ys hys x hx
    have hsub : PT.envelope i ⊆ T.X k :=
      (hPT.envelope_subset i).trans ((hPT.tiling_valid.patch_supports i).1.trans
        (fun z hz => (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1 hz)).1))
    have hx' : x ∉ PT.envelope i := fun he => hx (hsub he)
    change (directBaseLaw PT hPT hm a).w x = 0
    rw [directBaseLaw_w]
    simp [S15.directBaseWeight, i, hx']
  have hwμ : ∀ ys, Q.A ys → (Q.μ ys).WidthLE (2 * n ^ κ.ι) := by
    intro ys hys
    have hcap : ∀ x, ((PT.tiling.P i).M : ℝ) * (directBaseLaw PT hPT hm a).w x ≤ 2 := by
      intro x
      rw [directBaseLaw_w]
      exact Lane_q_s15_direct.highDirect_scaled_baseweight_le_two PT hPT hm i a rfl x
    have hw := law_width_of_cap hN (hM i) (directBaseLaw PT hPT hm a)
      (by norm_num : (0 : ℝ) < 2) hcap (direct_patch_log_width hκ PT hPT hm hn i)
    apply Law.WidthLE.mono hw
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog
    dsimp [n]
    linarith
  have hν : ∀ b ∈ Q.C, (Q.ν b).SupportedIn (T.Y k) := by
    intro b hb' y hy
    let j := S15.patchAt PT hPT b.1
    have hsub : (PT.tiling.P j).Y ⊆ T.Y k :=
      (hPT.tiling_valid.patch_supports j).2.2.1.trans
        (fun z hz => (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports j).2.2.2 hz)).1)
    exact hPT.law_supported j y (fun he => hy (hsub he))
  have hwν : ∀ b ∈ Q.C, (Q.ν b).WidthLE (11 * n ^ κ.ι) := by
    intro b hb'
    let j := S15.patchAt PT hPT b.1
    have hcap : ∀ y, ((PT.tiling.P j).M : ℝ) * (PT.π j).w y ≤ 11 := by
      intro y
      have hh := (le_div_iff₀ (hMR j)).mp (hPT.law_cap j y)
      simpa [mul_comm] using hh
    have hw := law_width_of_cap hN (hM j) (PT.π j)
      (by norm_num : (0 : ℝ) < 11) hcap (direct_patch_log_width hκ PT hPT hm hn j)
    apply Law.WidthLE.mono hw
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
    norm_num at hlog
    dsimp [n]
    linarith
  have hdeg : ∀ ys, Q.A ys → ∀ b ∈ Q.C, ∀ x, (Q.μ ys).w x ≠ 0 →
      |deg (T.S.E k) Q.c (Q.ν b).w x - 1 / 2| ≤ 3 * bstar T k := by
    intro ys hys b hb' x hxNe
    have hx : x ∈ PT.envelope i := by
      change (directBaseLaw PT hPT hm a).w x ≠ 0 at hxNe
      rw [directBaseLaw_w] at hxNe
      by_contra hx
      apply hxNe
      simp [S15.directBaseWeight, i, hx]
    have hj : S15.patchAt PT hPT b.1 ≠ i := (Finset.mem_filter.mp hb').2.2
    exact hPT.envelope_other_degree i (S15.patchAt PT hPT b.1) hj x hx
  have hcNat := Lane_q_s15_direct.highDirect_crossingNeighbours_card_le_prefix PT hPT a i rfl
  have hc : (Q.C.card : ℝ) ≤ n ^ κ.ι := by
    have hc' : (Q.C.card : ℝ) ≤ (PT.tiling.P i).ℓ := by exact_mod_cast hcNat
    have he : ((PT.tiling.P i).ℓ : ℝ) ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) := by
      exact_mod_cast (le_max_right (PT.tiling.P i).h (PT.tiling.P i).ℓ)
    exact hc'.trans (he.trans (hPT.tiling_valid.allocation_bounds i).1.le)
  have hbudget : 2 * n ^ κ.ι + (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ n ^ κ.xs := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hlog
    have hf : Real.log 4 + 10 * bstar T k ≤ 4 := by linarith
    have hm1 := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ Q.C.card by positivity)
    have hm2 := mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 4)
    dsimp [n] at *
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.ι]
  have hD' : TwoBudgetDisc T k (n ^ κ.xs) (κ.α * T.S.n k) (bstar T k) := by
    simpa [n, bstar] using hD
  have htail := Q.product_tail hD' hN hb0 hb hbudget hμ hwμ hν hwν hdeg
  have hcN : (Q.C.card : ℝ) ≤ n := by
    have hs : Q.C ⊆ Lane_q_s15_direct.star a := by
      intro b hb'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb').2.1⟩
    dsimp [n]
    exact_mod_cast (Finset.card_le_card hs).trans (Lane_q_s15_direct.star_card_le a)
  have he : Real.exp (11 * n ^ κ.ι - κ.α * T.S.n k) ≤ Real.exp (-κ.α * T.S.n k / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.ι]
  calc
    (S15.directRawLaw PT hPT).pr (fun ys => |S15.directCrossingMass PT hPT ys a - 1| >
        Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1) ≤
      (FinProb.pi Q.P).pr (fun ys => Q.A ys ∧ ¬ Q.Good Q.C ys) := by
        change (FinProb.pi Q.P).pr _ ≤ _
        apply CrossingExperiment.pr_mono
        intro ys hbad
        refine ⟨True.intro, ?_⟩
        intro hgood
        have hbound := exp_window_abs hb0 hcNat hgood.1 hgood.2
        exact not_lt_of_ge hbound hbad
    _ ≤ (Q.C.card : ℝ) * (2 * Real.exp (11 * n ^ κ.ι - κ.α * T.S.n k)) := htail
    _ ≤ n * (2 * Real.exp (-κ.α * T.S.n k / 2)) :=
      mul_le_mul hcN (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity) (by positivity)
    _ = 2 * (T.S.n k : ℝ) * Real.exp (-κ.α * T.S.n k / 2) := by dsimp [n]; ring

theorem direct_crossing_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highDirect, ∀ a : S15.EvenPosition T k,
        (S15.directRawLaw PT hPT).pr (fun ys =>
          |S15.directCrossingMass PT hPT ys a - 1| >
            Real.exp (20 * (PT.tiling.P (S15.patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
              (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by
  filter_upwards [direct_crossing_exp_bound κ hκ T hDeep, crossing_parameters κ hκ T] with k hk hp
  intro PT hPT hm a
  have hprob := hk PT hPT hm a
  rcases hp with ⟨hn, _, _, _, ht⟩
  have hn2 : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ (2 : ℕ) := by nlinarith
  apply hprob.trans
  calc
    2 * (T.S.n k : ℝ) * Real.exp (-κ.α * T.S.n k / 2) ≤
        8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) := by
      nlinarith [Real.exp_pos (-κ.α * T.S.n k / 2)]
    _ ≤ (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := ht

end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey OAI.HypercubeRamsey
open scoped BigOperators
open Classical
set_option maxHeartbeats 600000

variable {κ : CConsts} {T : Stage} {k : ℕ}

private theorem crossing_adj_flip {n : ℕ} {v w : CubeVertex n}
    (h : (cube n).Adj v w) : ∃ j : Fin n, w = cubeFlip v j := by
  classical
  change hammingDist v w = 1 at h
  unfold hammingDist at h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hjmem : j ∈ Finset.univ.filter (fun q : Fin n => v q ≠ w q) := by
    rw [hj]
    simp
  have hdiff : v j ≠ w j := (Finset.mem_filter.mp hjmem).2
  have hsame : ∀ q : Fin n, q ≠ j → v q = w q := by
    intro q hq
    by_contra hne
    have hqmem : q ∈ Finset.univ.filter (fun r : Fin n => v r ≠ w r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have hqEq : q = j := by
      rw [hj] at hqmem
      simpa using hqmem
    exact hq hqEq
  refine ⟨j, ?_⟩
  funext q
  by_cases hq : q = j
  · subst q
    have hcoord : cubeFlip v j j = !v j := by simp [cubeFlip, Function.update_self]
    rw [hcoord]
    cases hv : v j <;> cases hw : w j <;> simp_all
  · simp [cubeFlip, hq, hsame q hq]

theorem crossing_patch_injective (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) :
    Set.InjOn (fun b : S15.OddPosition T k => S15.patchAt PT hPT b.1)
      (S15.crossingNeighbours PT hPT a : Set (S15.OddPosition T k)) := by
  intro b hb c hc hbc
  obtain ⟨jb, hfb⟩ := crossing_adj_flip
    (show (cube (T.S.n k)).Adj a.1 b.1 from (Finset.mem_filter.mp hb).2.1)
  obtain ⟨jc, hfc⟩ := crossing_adj_flip
    (show (cube (T.S.n k)).Adj a.1 c.1 from (Finset.mem_filter.mp hc).2.1)
  let j := S15.patchAt PT hPT b.1
  have hbLeaf : b.1 ∈ PT.tiling.leaf j := (Classical.choose_spec (hPT.tiling_valid.prefix_complete b.1)).1
  have hcLeaf : c.1 ∈ PT.tiling.leaf j := by
    change c.1 ∈ PT.tiling.leaf (S15.patchAt PT hPT b.1)
    change S15.patchAt PT hPT b.1 = S15.patchAt PT hPT c.1 at hbc
    rw [hbc]
    exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete c.1)).1
  have hjb : jb.val < (PT.tiling.P j).ℓ := by
    by_contra hnot
    have haLeaf : a.1 ∈ PT.tiling.leaf j := by
      intro q hq
      have hne : q ≠ jb := by intro h; subst q; omega
      have hx := hbLeaf q hq
      rw [hfb] at hx
      simpa [cubeFlip, hne] using hx
    have hpa : S15.patchAt PT hPT a.1 = j :=
      ((Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).2 j haLeaf).symm
    exact (Finset.mem_filter.mp hb).2.2 hpa.symm
  have hcoord : jb = jc := by
    by_contra hne
    have he : b.1 jb = c.1 jb := (hbLeaf jb hjb).trans (hcLeaf jb hjb).symm
    rw [hfb, hfc] at he
    have hne' : jb ≠ jc := hne
    cases hv : a.1 jb <;> simp [cubeFlip, hne', hv] at he
  apply Subtype.ext
  rw [hfb, hfc, hcoord]

theorem crossing_slice_injective (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) :
    Set.InjOn (fun b : S15.OddPosition T k => S15.clusterSliceAt PT hPT b.1)
      (S15.clusterCrossingNeighbours PT hPT a : Set (S15.OddPosition T k)) := by
  intro b hb c hc he
  apply crossing_patch_injective PT hPT a hb hc
  exact congrArg Sigma.fst he

theorem crossing_slice_ne_own (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : S15.EvenPosition T k) (b : S15.OddPosition T k)
    (hb : b ∈ S15.clusterCrossingNeighbours PT hPT a) :
    S15.clusterSliceAt PT hPT b.1 ≠ S15.clusterSliceAt PT hPT a.1 := by
  intro he
  exact (Finset.mem_filter.mp hb).2.2 (congrArg Sigma.fst he)

theorem history_slice_positive (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm)
    (hW : 0 < (S15.clusterHistoryLaw PT hPT hm).w W) (s : S15.ClusterSlice PT) :
    0 < ((S15.clusterSolver PT hPT hm s.1).recLaw PT.parameter).w (S15.historyOnSlice W s) := by
  have hglobal : (∏ r : S15.ClusterRecordIndex PT hPT hm,
      (S15.clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2 (W r)) ≠ 0 := hW.ne'
  have hnonzero := Finset.prod_ne_zero_iff.mp hglobal
  change 0 < ∏ r, (S15.clusterSolver PT hPT hm s.1).lawRec PT.parameter r
    (S15.historyOnSlice W s r)
  apply Finset.prod_pos
  intro r hr
  have hn := hnonzero ⟨s, r⟩ (Finset.mem_univ _)
  exact lt_of_le_of_ne ((S15.clusterSolver PT hPT hm s.1).lawRec_nonneg PT.parameter r _)
    (Ne.symm hn)

noncomputable def sigmaLaw (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (I : S15.ClusterInternalData PT)
    (a : S15.EvenPosition T k) (hprob : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1) :
    Law (T.S.N k) where
  w := S15.clusterSigma PT hPT hm W I a
  nonneg := fun x => (S15.clusterSolver PT hPT hm (S15.patchAt PT hPT a.1)).σ_nonneg _ _ _ x
  sum_eq_one := hprob

theorem sigmaLaw_supported (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (hW : 0 < (S15.clusterHistoryLaw PT hPT hm).w W)
    (I : S15.ClusterInternalData PT) (a : S15.EvenPosition T k)
    (hprob : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1) :
    (sigmaLaw PT hPT hm W I a hprob).SupportedIn (T.X k) := by
  let s := S15.clusterSliceAt PT hPT a.1
  let S := S15.clusterSolver PT hPT hm s.1
  have hnonzero : S.σ (S15.clusterCenterRole PT hPT hm a) (S15.historyOnSlice W s)
      (nbrLabels (S15.clusterCenterRole PT hPT hm a).1 (I s).2) ≠ 0 := by
    intro hz
    have hfun : S15.clusterSigma PT hPT hm W I a = 0 := hz
    have hs : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 0 := by
      rw [hfun]
      simp
    linarith
  obtain ⟨v, hv, hsupp⟩ := S.σ_support _ _ _ hnonzero
  have hv' : v ∈ PT.activeVertices := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hv PT.parameter (history_slice_positive PT hPT hm W hW s)⟩
  intro x hx
  by_contra hn
  have hxc := (hsupp x hn).1
  have hxp := (hPT.corner_clean s.1 v hv').sub hxc
  have hxT := (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports s.1).2.1
    ((hPT.tiling_valid.patch_supports s.1).1 hxp))).1
  exact hx hxT

end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey
open Classical
open scoped BigOperators
set_option maxHeartbeats 600000

noncomputable def toProb {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : FinProb Ω :=
  ⟨P.w, P.nonneg, P.sum_one⟩

theorem pi_expect_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (b : ι) (f : Ω b → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω b)) = (P b).expect f := by
  rw [← pi_expect_resample P b]
  simp only [Function.update_self]
  exact FinProb.expect_const _ _

/-- A label of the two-stage reference experiment has the stated mixture marginal. -/
theorem refLaw_label_expect {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r)
    (z : IWord 𝒯 i) (f : Fin (T.S.N k) → ℝ) :
    (toProb (S.refLaw W)).expect (fun ω => f (ω.2 z)) =
      ∑ y, S.oddMarginal (S.groupOf z) W y * f y := by
  let Q : Group 𝒯 i → FinProb (Bin 𝒯 i) :=
    fun g => ⟨S.q g W, S.q_nonneg g W, S.q_sum g W⟩
  let U : (Group 𝒯 i → Bin 𝒯 i) → IWord 𝒯 i → Law (T.S.N k) :=
    fun D z => ⟨S.U (S.groupOf z) W (D (S.groupOf z)), S.U_nonneg _ W _, S.U_sum _ W _⟩
  change (FinProb.bind (FinProb.pi Q) (fun D => FinProb.pi (U D))).expect
    (fun ω => f (ω.2 z)) = _
  rw [FinProb.bind_expect (FinProb.pi Q) (fun D => FinProb.pi (U D)) (fun _ Y => f (Y z))]
  change (FinProb.pi Q).expect (fun D => (FinProb.pi (U D)).expect (fun Y => f (Y z))) = _
  simp_rw [pi_expect_one]
  change (FinProb.pi Q).expect (fun D =>
    ∑ y, S.U (S.groupOf z) W (D (S.groupOf z)) y * f y) = _
  rw [pi_expect_one Q (S.groupOf z) (fun D => ∑ y, S.U (S.groupOf z) W D y * f y)]
  unfold FinProb.expect SliceSolver.oddMarginal
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Every normalized hit has mean at most one, including zero-degree sites. -/
theorem normalizedHit_expect_le_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (ν : Law N) (x : Fin N) :
    ν.expect (fun y => S15.normalizedHit E c ν x y) ≤ 1 := by
  by_cases hd : 0 < deg E c ν.w x
  · rw [Lane_q_s15_direct.expect_normalizedHit_eq_one ν E c x hd]
  · simp [FinProb.expect, S15.normalizedHit, hd]

namespace CrossingExperiment
variable {T : Stage} {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- Removing a small entering submeasure costs at most its original mean mass.
No degree lower bound is needed on the removed sites. -/
theorem removed_expect_le (Q : CrossingExperiment T k ι Ω)
    (f : (∀ i, Ω i) → Fin (T.S.N k) → ℝ)
    (hf : ∀ ω x, 0 ≤ f ω x)
    (hupdate : ∀ b ∈ Q.C, ∀ ω y x, f (Function.update ω b y) x = f ω x)
    (S : Finset ι) (hS : S ⊆ Q.C) :
    (FinProb.pi Q.P).expect (fun ω => ∑ x, f ω x *
      ∏ i ∈ S, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))) ≤
        (FinProb.pi Q.P).expect (fun ω => ∑ x, f ω x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b S hb ih =>
    have hbC := hS (Finset.mem_insert_self b S)
    have hsub : S ⊆ Q.C := fun i hi => hS (Finset.mem_insert_of_mem hi)
    apply le_trans _ (ih hsub)
    rw [← pi_expect_resample Q.P b]
    apply FinProb.expect_mono
    intro ω
    have hpoint (y : Ω b) :
        (∑ x, f (Function.update ω b y) x * ∏ i ∈ insert b S,
          S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (Function.update ω b y i))) =
        ∑ x, (f ω x * ∏ i ∈ S,
          S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))) *
            S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hupdate b hbC ω y x, Finset.prod_insert hb, Function.update_self]
      have hp : (∏ i ∈ S, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x
          (Q.label i (Function.update ω b y i))) =
          ∏ i ∈ S, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Function.update_of_ne (show i ≠ b from fun h => hb (h ▸ hi))]
      rw [hp]
      ring
    simp_rw [hpoint]
    unfold FinProb.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x hx
    let a := f ω x * ∏ i ∈ S,
      S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))
    have hmean : (Q.P b).expect (fun y =>
        S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y)) ≤ 1 := by
      rw [← FinProb.map_expect, ← Q.marginal b]
      exact normalizedHit_expect_le_one _ _ _ _
    have ha : 0 ≤ a := mul_nonneg (hf ω x)
      (Finset.prod_nonneg fun i _ => normalizedHit_nonneg _ _ _ _ _)
    calc
      (∑ y, (Q.P b).w y * (a * S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y))) =
          a * (Q.P b).expect (fun y => S15.normalizedHit (T.S.E k) Q.c (Q.ν b) x (Q.label b y)) := by
        unfold FinProb.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hmean ha
      _ = a := mul_one _
end CrossingExperiment

/-- The union of crossing degree outliers has exponentially small mass under any narrow first law. -/
theorem crossing_gate_loss {T : Stage} {k : ℕ} {ι : Type*} [Fintype ι]
    (C : Finset ι) (c : Colour) (ν : ι → Law (T.S.N k)) (μ : Law (T.S.N k))
    {wS wL w : ℝ} (hD : TwoBudgetDisc T k wS wL (bstar T k))
    (hν : ∀ i ∈ C, (ν i).SupportedIn (T.Y k))
    (hwν : ∀ i ∈ C, (ν i).WidthLE wS)
    (hμ : μ.SupportedIn (T.X k)) (hwμ : μ.WidthLE w)
    (hb : 0 ≤ bstar T k) :
    μ.pr (fun x => ¬ ∀ i ∈ C, |deg (T.S.E k) c (ν i).w x - 1 / 2| ≤ 2 * bstar T k) ≤
      C.card * (2 * Real.exp (w - wL)) := by
  classical
  have hout (i : ι) (hi : i ∈ C) :
      μ.pr (fun x => 2 * bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|) ≤
        2 * Real.exp (w - wL) := by
    apply (CrossingExperiment.pr_mono μ (A := fun x => 2 * bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|)
      (B := fun x => bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|)
      (fun x hx => lt_of_le_of_lt (by linarith) hx)).trans
    simpa [FinProb.pr, ← Finset.sum_filter] using
      S15.Needs.exceptional_first hD c (Or.inl ⟨le_rfl, le_rfl⟩)
        (ν i) μ (hν i hi) (hwν i hi) hμ hwμ
  have hbound : ∀ S : Finset ι, S ⊆ C →
      μ.pr (fun x => ∃ i ∈ S, 2 * bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|) ≤
        S.card * (2 * Real.exp (w - wL)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [FinProb.pr]
    | @insert i S hi ih =>
      intro hs
      have hb := FinProb.pr_union μ
        (fun x => 2 * bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|)
        (fun x => ∃ j ∈ S, 2 * bstar T k < |deg (T.S.E k) c (ν j).w x - 1 / 2|)
      have he : μ.pr (fun x => ∃ j ∈ insert i S,
          2 * bstar T k < |deg (T.S.E k) c (ν j).w x - 1 / 2|) =
          μ.pr (fun x => (2 * bstar T k < |deg (T.S.E k) c (ν i).w x - 1 / 2|) ∨
            ∃ j ∈ S, 2 * bstar T k < |deg (T.S.E k) c (ν j).w x - 1 / 2|) := by
        congr 1
        funext x
        simp
      rw [he]
      have hh := hb.trans (add_le_add (hout i (hs (Finset.mem_insert_self _ _)))
        (ih (fun j hj => hs (Finset.mem_insert_of_mem hj))))
      simpa [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm] using hh
  convert hbound C (Finset.Subset.refl C) using 1
  congr 1
  funext x
  simp
end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey
open Classical
open scoped BigOperators
set_option maxHeartbeats 600000
variable {κ : CConsts} {T : Stage} {k : ℕ}

@[simp] theorem sliceAt_fst (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (v : S15.Position T k) : (S15.clusterSliceAt PT hPT v).1 = S15.patchAt PT hPT v := rfl

noncomputable def marginalLaw (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (b : S15.OddPosition T k) : Law (T.S.N k) :=
  FinProb.map (toProb ((S15.clusterSolver PT hPT hm (S15.patchAt PT hPT b.1)).refLaw
    (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1))))
      (fun ω => ω.2 (S15.solverWordAt PT hPT hm b.1))

theorem marginalLaw_w (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (b : S15.OddPosition T k) (y : Fin (T.S.N k)) :
    (marginalLaw PT hPT hm W b).w y = S15.clusterMarginal PT hPT hm W b y := by
  have hh := refLaw_label_expect
    (S15.clusterSolver PT hPT hm (S15.patchAt PT hPT b.1))
    (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1))
    (S15.solverWordAt PT hPT hm b.1) (fun z => if z = y then 1 else 0)
  simpa [FinProb.expect, S15.clusterMarginal, marginalLaw, FinProb.map, mul_ite, sliceAt_fst] using hh

theorem marginalLaw_supported (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (b : S15.OddPosition T k) :
    (marginalLaw PT hPT hm W b).SupportedIn (T.Y k) := by
  intro y hy
  rw [marginalLaw_w]
  let i := S15.patchAt PT hPT b.1
  let S := S15.clusterSolver PT hPT hm i
  let g := S.groupOf (S15.solverWordAt PT hPT hm b.1)
  change ∑ D : Bin PT.tiling i, S.q g (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1)) D *
    S.U g (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1)) D y = 0
  apply Finset.sum_eq_zero
  intro D hD
  have hnot : y ∉ D.1 := by
    intro hd
    have hpatch : y ∈ (PT.tiling.P i).Y :=
      (PT.tiling.P i).bins.le D.2 hd
    exact hy ((Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.2.2
        ((hPT.tiling_valid.patch_supports i).2.2.1 hpatch))).1)
  have hu : S.U g (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1)) D y = 0 := by
    by_contra hne
    exact hnot (S.U_support _ _ _ _ hne)
  rw [hu, mul_zero]

/-- The reference label cap has width bounded by a fixed multiple of the allocated height. -/
theorem sampler_scale_product (hκ : κ.Admissible) {h : ℕ} (hh : 0 < h) :
    (sliceK κ h : ℝ) * sliceT κ h ≤ 4 * h := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hcq : κ.cq < 1 := by
    have hm : (100 : ℝ) < κ.Mlo := by
      have hc := hκ.Cb_big
      have hd : 0 < 100 * κ.aC / κ.aB := by positivity [hκ.aC_rng.1, hκ.aB_rng.1]
      linarith [hκ.Mlo_big]
    have hq := hκ.cq_rng.2
    have he : 1 / (20 * (κ.Mlo : ℝ)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    exact hq.trans he
  have hMhi : (1 : ℝ) < κ.Mhi := by nlinarith [hκ.Mhi_big.2, hκ.cq_rng.1]
  have haC : κ.aC < 1 := by
    have hh := hκ.aC_rng.2
    have hl := min_le_right κ.η0 (1 : ℝ)
    linarith
  have hω : 4 * κ.ω ≤ 1 := by nlinarith [hκ.ω_rng.1, hκ.ω_rng.2]
  have hK : (sliceK κ h : ℝ) ≤ 2 * (h : ℝ) ^ (3 * κ.ω) := by
    exact Nat.ceil_le_two_mul ((show (2 : ℝ)⁻¹ ≤ 1 by norm_num).trans
      (Real.one_le_rpow h1 (by positivity [hκ.ω_rng.1])))
  have hT : (sliceT κ h : ℝ) ≤ 2 * (h : ℝ) ^ κ.ω := by
    exact Nat.ceil_le_two_mul ((show (2 : ℝ)⁻¹ ≤ 1 by norm_num).trans
      (Real.one_le_rpow h1 hκ.ω_rng.1.le))
  calc
    (sliceK κ h : ℝ) * sliceT κ h ≤
        (2 * (h : ℝ) ^ (3 * κ.ω)) * (2 * (h : ℝ) ^ κ.ω) :=
      mul_le_mul hK hT (by positivity) (by positivity)
    _ = 4 * (h : ℝ) ^ (4 * κ.ω) := by
      rw [show 4 * κ.ω = 3 * κ.ω + κ.ω by ring, Real.rpow_add h0]
      ring
    _ ≤ 4 * h := by
      have hp := Real.rpow_le_rpow_of_exponent_le h1 hω
      simpa using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 4)

end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey
open Classical
open scoped BigOperators
set_option maxHeartbeats 600000
namespace CrossingExperiment
variable {T : Stage} {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

noncomputable def gates (Q : CrossingExperiment T k ι Ω) : Finset (Fin (T.S.N k)) :=
  Finset.univ.filter fun x => ∀ i ∈ Q.C,
    |deg (T.S.E k) Q.c (Q.ν i).w x - 1 / 2| ≤ 2 * bstar T k

noncomputable def retained (Q : CrossingExperiment T k ι Ω) (ω : ∀ i, Ω i) : ℝ :=
  ∑ x ∈ Q.gates, (Q.μ ω).w x

noncomputable def trimmed (Q : CrossingExperiment T k ι Ω) :
    CrossingExperiment T k ι Ω where
  P := Q.P
  label := Q.label
  ν := Q.ν
  marginal := Q.marginal
  c := Q.c
  C := Q.C
  μ := fun ω => if h : 0 < Q.retained ω then Law.restrict (Q.μ ω) Q.gates h else Q.μ ω
  A := Q.A
  μ_update := by
    intro b hb ω y
    simp only [retained, Q.μ_update b hb ω y]
    rfl
  A_update := Q.A_update

noncomputable def removed (Q : CrossingExperiment T k ι Ω) (ω : ∀ i, Ω i) : ℝ :=
  ∑ x, (if Q.A ω ∧ x ∉ Q.gates then (Q.μ ω).w x else 0) *
    ∏ i ∈ Q.C, S15.normalizedHit (T.S.E k) Q.c (Q.ν i) x (Q.label i (ω i))

theorem retained_complement (Q : CrossingExperiment T k ι Ω) (ω : ∀ i, Ω i) :
    Q.retained ω + (Q.μ ω).pr (fun x => x ∉ Q.gates) = 1 := by
  have he : Q.retained ω + (Q.μ ω).pr (fun x => x ∉ Q.gates) = ∑ x, (Q.μ ω).w x := by
    unfold retained FinProb.pr
    have hs : (∑ x ∈ Q.gates, (Q.μ ω).w x) = ∑ x, if x ∈ Q.gates then (Q.μ ω).w x else 0 := by
      simp
    rw [hs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x ∈ Q.gates <;> simp [h]
  rw [he, (Q.μ ω).sum_eq_one]

theorem unfiltered_window {r ℓ : ℕ} {b q M V : ℝ}
    (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 100) (hℓ : 1 ≤ ℓ) (hr : r ≤ ℓ)
    (hqlo : 1 - b ≤ q) (hqhi : q ≤ 1)
    (hMlo : Real.exp (-10 * r * b) ≤ M) (hMhi : M ≤ Real.exp (10 * r * b))
    (hVlo : 0 ≤ V) (hVhi : V ≤ b) :
    |q * M + V - 1| ≤ Real.exp (20 * ℓ * b) - 1 := by
  have hq0 : 0 ≤ q := by linarith
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans hMlo
  have hrR : (r : ℝ) ≤ ℓ := by exact_mod_cast hr
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hE : 1 ≤ Real.exp (10 * (r : ℝ) * b) := Real.one_le_exp (by positivity)
  have hgap : Real.exp (10 * (r : ℝ) * b) + b ≤ Real.exp (20 * (ℓ : ℝ) * b) := by
    have h := Real.add_one_le_exp (10 * (ℓ : ℝ) * b)
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (10 * (ℓ : ℝ) * b)).le
    rw [← Real.exp_add] at hmul
    have he1 : Real.exp (10 * (r : ℝ) * b) ≤ Real.exp (10 * (ℓ : ℝ) * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he2 : 1 ≤ Real.exp (10 * (ℓ : ℝ) * b) := Real.one_le_exp (by positivity)
    have hsame : 10 * (ℓ : ℝ) * b + 10 * (ℓ : ℝ) * b = 20 * (ℓ : ℝ) * b := by ring
    rw [hsame] at hmul
    have hprod : b ≤ Real.exp (10 * (ℓ : ℝ) * b) * (10 * (ℓ : ℝ) * b) := by
      have hlb : b ≤ 10 * (ℓ : ℝ) * b := by nlinarith
      exact hlb.trans (le_mul_of_one_le_left (by positivity) he2)
    nlinarith
  have hlo : 1 - (10 * (r : ℝ) + 1) * b ≤ q * M + V := by
    have he := Real.add_one_le_exp (-10 * (r : ℝ) * b)
    have hm := mul_le_mul_of_nonneg_left hMlo hq0
    have hq := mul_le_mul_of_nonneg_right hqlo (Real.exp_pos (-10 * (r : ℝ) * b)).le
    have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 - b by linarith)
    nlinarith [show 0 ≤ (r : ℝ) * b ^ 2 by positivity]
  have hhi : q * M + V ≤ Real.exp (20 * (ℓ : ℝ) * b) := by
    have hh := mul_le_mul_of_nonneg_right hqhi hM0
    nlinarith
  have htarget := Real.add_one_le_exp (20 * (ℓ : ℝ) * b)
  exact abs_le.mpr ⟨by nlinarith, by linarith⟩

/-- Trimming degree outliers and restoring them by Markov proves the unfiltered tail. -/
theorem unfiltered_tail (Q : CrossingExperiment T k ι Ω) {w0 wS wL w : ℝ} {ℓ : ℕ}
    (hD : TwoBudgetDisc T k wS wL (bstar T k))
    (hN : 0 < T.S.N k) (hb : 0 < bstar T k) (hsmall : bstar T k ≤ 1 / 100)
    (hℓ : 1 ≤ ℓ) (hr : Q.C.card ≤ ℓ)
    (hbudget : w0 + Real.log 2 + (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ wS)
    (hμ : ∀ ω, Q.A ω → (Q.μ ω).SupportedIn (T.X k))
    (hwμ : ∀ ω, Q.A ω → (Q.μ ω).WidthLE w0)
    (hν : ∀ i ∈ Q.C, (Q.ν i).SupportedIn (T.Y k))
    (hwν : ∀ i ∈ Q.C, (Q.ν i).WidthLE w)
    (hνbudget : w ≤ wS)
    (hloss : (Q.C.card : ℝ) * (2 * Real.exp (w0 - wL)) ≤ bstar T k) :
    (FinProb.pi Q.P).pr (fun ω => Q.A ω ∧
      Real.exp (20 * ℓ * bstar T k) - 1 < |Q.mass Q.C ω - 1|) ≤
        Q.C.card * (2 * Real.exp (w - wL)) +
          (Q.C.card * (2 * Real.exp (w0 - wL))) / bstar T k := by
  let ε := (Q.C.card : ℝ) * (2 * Real.exp (w0 - wL))
  have hgate (ω) (ha : Q.A ω) : (Q.μ ω).pr (fun x => x ∉ Q.gates) ≤ ε := by
    simpa [gates, ε] using crossing_gate_loss Q.C Q.c Q.ν (Q.μ ω) hD hν
      (fun i hi => Law.WidthLE.mono (hwν i hi) hνbudget) (hμ ω ha) (hwμ ω ha) hb.le
  have hret (ω) (ha : Q.A ω) : 1 - bstar T k ≤ Q.retained ω ∧ Q.retained ω ≤ 1 := by
    have he := Q.retained_complement ω
    have hn : 0 ≤ (Q.μ ω).pr (fun x => x ∉ Q.gates) :=
      Finset.sum_nonneg fun x _ => by split_ifs <;> simp [FinProb.nonneg]
    have hh := (hgate ω ha).trans hloss
    constructor <;> linarith
  have hpos (ω) (ha : Q.A ω) : 0 < Q.retained ω := by
    have hh := (hret ω ha).1
    linarith
  have htw (ω) (ha : Q.A ω) : (Q.trimmed.μ ω).WidthLE (w0 + Real.log 2) := by
    intro x
    simp only [trimmed, dif_pos (hpos ω ha)]
    change (if x ∈ Q.gates then (Q.μ ω).w x / Q.retained ω else 0) ≤ _
    split_ifs with hx
    · have hN' : (0 : ℝ) < T.S.N k := by exact_mod_cast hN
      have hrhalf : 1 / 2 ≤ Q.retained ω := by have hh := (hret ω ha).1; linarith
      calc
        (Q.μ ω).w x / Q.retained ω ≤ (Real.exp w0 / T.S.N k) / (1 / 2) :=
          div_le_div₀ (by positivity) (hwμ ω ha x) (by norm_num) hrhalf
        _ = Real.exp (w0 + Real.log 2) / T.S.N k := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
    · positivity
  have hts (ω) (ha : Q.A ω) : (Q.trimmed.μ ω).SupportedIn (T.X k) := by
    intro x hx
    simp only [trimmed, dif_pos (hpos ω ha)]
    simp [Law.restrict, hμ ω ha x hx]
  have htd (ω) (ha : Q.A ω) (i : ι) (hi : i ∈ Q.C) (x : Fin (T.S.N k))
      (hx : (Q.trimmed.μ ω).w x ≠ 0) :
      |deg (T.S.E k) Q.c (Q.ν i).w x - 1 / 2| ≤ 3 * bstar T k := by
    have hxgate : x ∈ Q.gates := by
      by_contra hh
      apply hx
      simp [trimmed, dif_pos (hpos ω ha), Law.restrict, hh]
    have hg := (Finset.mem_filter.mp hxgate).2 i hi
    linarith
  have htail := Q.trimmed.product_tail hD hN hb.le hsmall hbudget hts htw hν hwν htd
  have hnon (ω) : 0 ≤ Q.removed ω := by
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · split_ifs <;> simp [FinProb.nonneg]
    · exact Finset.prod_nonneg fun i hi => normalizedHit_nonneg _ _ _ _ _
  have hexp : (FinProb.pi Q.P).expect Q.removed ≤ ε := by
    have hu : ∀ i ∈ Q.C, ∀ ω y x,
        (if Q.A (Function.update ω i y) ∧ x ∉ Q.gates then (Q.μ (Function.update ω i y)).w x else 0) =
        (if Q.A ω ∧ x ∉ Q.gates then (Q.μ ω).w x else 0) := by
      intro i hi ω y x
      simp [Q.A_update i hi ω y, Q.μ_update i hi ω y]
    apply (Q.removed_expect_le _ (by intros; split_ifs <;> simp [FinProb.nonneg])
      hu Q.C (Finset.Subset.refl _)).trans
    apply le_trans (FinProb.expect_mono _ ?_) (le_of_eq (FinProb.expect_const _ ε))
    intro ω
    by_cases ha : Q.A ω
    · have he : (∑ x, if Q.A ω ∧ x ∉ Q.gates then (Q.μ ω).w x else 0) =
          (Q.μ ω).pr (fun x => x ∉ Q.gates) := by
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hg : x ∈ Q.gates <;> simp [ha, hg]
      rw [he]
      exact hgate ω ha
    · simp [ha, ε]; positivity
  have hmark := (FinProb.markov (FinProb.pi Q.P) Q.removed (bstar T k) hnon hb).trans
    (div_le_div_of_nonneg_right hexp hb.le)
  have hmono : (FinProb.pi Q.P).pr (fun ω => Q.A ω ∧
      Real.exp (20 * ℓ * bstar T k) - 1 < |Q.mass Q.C ω - 1|) ≤
      (FinProb.pi Q.P).pr (fun ω => (Q.A ω ∧ ¬ Q.trimmed.Good Q.C ω) ∨
        bstar T k ≤ Q.removed ω) := by
    apply pr_mono
    rintro ω ⟨ha, hbad⟩
    by_cases hg : Q.trimmed.Good Q.C ω
    · right
      by_contra hv
      have hdecomp : Q.mass Q.C ω = Q.retained ω * Q.trimmed.mass Q.C ω + Q.removed ω := by
        unfold mass weight removed
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [trimmed, dif_pos (hpos ω ha)]
        by_cases hxg : x ∈ Q.gates
        · simp only [Law.restrict, hxg, if_pos, ha, true_and, not_true_eq_false,
            if_false, zero_mul, add_zero]
          change _ = Q.retained ω * ((Q.μ ω).w x / Q.retained ω * _)
          field_simp [(hpos ω ha).ne']
        · simp [Law.restrict, ha, hxg]
      have hh := unfiltered_window hb.le hsmall hℓ hr (hret ω ha).1 (hret ω ha).2
        hg.1 hg.2 (hnon ω) (le_of_lt (lt_of_not_ge hv))
      rw [← hdecomp] at hh
      exact not_lt_of_ge hh hbad
    · exact Or.inl ⟨ha, hg⟩
  exact hmono.trans ((FinProb.pr_union _ _ _).trans (add_le_add htail hmark))
end CrossingExperiment
end HypercubeRamsey.Lane_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey Filter
open Classical
open scoped BigOperators
set_option maxHeartbeats 600000
variable {κ : CConsts} {T : Stage} {k : ℕ}

theorem patch_eq_of_slice_eq (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (b : S15.OddPosition T k) (s : S15.ClusterSlice PT)
    (hs : S15.clusterSliceAt PT hPT b.1 = s) : S15.patchAt PT hPT b.1 = s.1 :=
  congrArg Sigma.fst hs

noncomputable def crossingWord (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : S15.EvenPosition T k) (s : S15.ClusterSlice PT) : IWord PT.tiling s.1 :=
  if h : ∃ b ∈ S15.clusterCrossingNeighbours PT hPT a, S15.clusterSliceAt PT hPT b.1 = s then
    cast (congrArg (IWord PT.tiling)
      (patch_eq_of_slice_eq PT hPT (Classical.choose h) s (Classical.choose_spec h).2))
      (S15.solverWordAt PT hPT hm (Classical.choose h).1)
  else fun _ => false

theorem crossingWord_at (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : S15.EvenPosition T k) (b : S15.OddPosition T k)
    (hb : b ∈ S15.clusterCrossingNeighbours PT hPT a) :
    crossingWord PT hPT hm a (S15.clusterSliceAt PT hPT b.1) = S15.solverWordAt PT hPT hm b.1 := by
  have hex : ∃ c ∈ S15.clusterCrossingNeighbours PT hPT a,
      S15.clusterSliceAt PT hPT c.1 = S15.clusterSliceAt PT hPT b.1 := ⟨b, hb, rfl⟩
  have hc : Classical.choose hex = b :=
    crossing_slice_injective PT hPT a (Classical.choose_spec hex).1 hb (Classical.choose_spec hex).2
  unfold crossingWord
  rw [dif_pos hex]
  have hw : HEq (S15.solverWordAt PT hPT hm (Classical.choose hex).1)
      (S15.solverWordAt PT hPT hm b.1) := by
    generalize Classical.choose hex = c at hc ⊢
    cases hc
    rfl
  exact eq_of_heq ((cast_heq _ _).trans hw)

noncomputable def clusterExperiment (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (a : S15.EvenPosition T k) :
    CrossingExperiment T k (S15.ClusterSlice PT) (fun s => S15.ClusterSliceOutcome PT s.1) where
  P := fun s => toProb ((S15.clusterSolver PT hPT hm s.1).refLaw (S15.historyOnSlice W s))
  label := fun s ω => ω.2 (crossingWord PT hPT hm a s)
  ν := fun s => FinProb.map
    (toProb ((S15.clusterSolver PT hPT hm s.1).refLaw (S15.historyOnSlice W s)))
      (fun ω => ω.2 (crossingWord PT hPT hm a s))
  marginal := fun _ => rfl
  c := PT.tiling.c
  C := (S15.clusterCrossingNeighbours PT hPT a).image (fun b => S15.clusterSliceAt PT hPT b.1)
  μ := fun I => if h : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 then
    sigmaLaw PT hPT hm W I a h else Law.dirac ⟨0, T.S.N_pos k⟩
  A := fun I => (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1
  μ_update := by
    intro s hs I y
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    have hne := crossing_slice_ne_own PT hPT a b hb
    have he : S15.clusterSigma PT hPT hm W (Function.update I (S15.clusterSliceAt PT hPT b.1) y) a =
        S15.clusterSigma PT hPT hm W I a := by
      funext x
      change (S15.clusterSolver PT hPT hm (S15.patchAt PT hPT a.1)).σ _ _
        (nbrLabels _ (Function.update I (S15.clusterSliceAt PT hPT b.1) y
          (S15.clusterSliceAt PT hPT a.1)).2) x = _
      rw [Function.update_of_ne (Ne.symm hne)]
      rfl
    simp only [he]
    split_ifs with hp
    · apply law_ext
      exact he
    · rfl
  A_update := by
    intro s hs I y
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    have hne := crossing_slice_ne_own PT hPT a b hb
    simp [S15.clusterSigma, Function.update_of_ne (Ne.symm hne)]

theorem clusterExperiment_nu (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (a : S15.EvenPosition T k) (b : S15.OddPosition T k)
    (hb : b ∈ S15.clusterCrossingNeighbours PT hPT a) :
    (clusterExperiment PT hPT hm W a).ν (S15.clusterSliceAt PT hPT b.1) =
      marginalLaw PT hPT hm W b := by
  simp only [clusterExperiment, marginalLaw, crossingWord_at PT hPT hm a b hb]
  rfl

theorem clusterExperiment_mass (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (a : S15.EvenPosition T k)
    (I : S15.ClusterInternalData PT) (ha : (clusterExperiment PT hPT hm W a).A I) :
    (clusterExperiment PT hPT hm W a).mass (clusterExperiment PT hPT hm W a).C I =
      S15.clusterCrossingMass PT hPT hm W I a := by
  let Q := clusterExperiment PT hPT hm W a
  change (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 at ha
  unfold CrossingExperiment.mass CrossingExperiment.weight S15.clusterCrossingMass
  apply Finset.sum_congr rfl
  intro x hx
  change (if h : (∑ y, S15.clusterSigma PT hPT hm W I a y) = 1 then
    sigmaLaw PT hPT hm W I a h else Law.dirac ⟨0, T.S.N_pos k⟩).w x * _ = _
  rw [dif_pos ha]
  change S15.clusterSigma PT hPT hm W I a x * _ = _
  congr 1
  change (∏ s ∈ (S15.clusterCrossingNeighbours PT hPT a).image
      (fun b => S15.clusterSliceAt PT hPT b.1),
    S15.normalizedHit (T.S.E k) Q.c (Q.ν s) x (Q.label s (I s))) = _
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro b hb
    rw [clusterExperiment_nu PT hPT hm W a b hb]
    simp only [Q, clusterExperiment, crossingWord_at PT hPT hm a b hb]
    have hweights : (marginalLaw PT hPT hm W b).w = S15.clusterMarginal PT hPT hm W b :=
      funext (marginalLaw_w PT hPT hm W b)
    simp only [S15.normalizedHit, S15.clusterFactor, S15.clusterDegree, hweights]
    rfl
  · exact crossing_slice_injective PT hPT a

/-- Allocations and solver caps give uniform marginal widths without conditioning on alarms. -/
theorem cluster_log_width (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hn : 1 ≤ (T.S.n k : ℝ)) (i : Fin PT.tiling.m) :
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ κ.a * (T.S.n k : ℝ) ^ κ.ι := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; positivity [hκ.θ_rng.1]
  have hu : (1 : ℝ) ≤ κ.u := by exact_mod_cast (show 1 ≤ κ.u by have := hκ.u_rng.2; omega)
  obtain hb | ⟨_, hlog⟩ := (hPT.tiling_valid.allocation_bounds i).2
  · rcases hm with hm | hm <;> rw [hm] at hb <;> cases hb
  have hh : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    apply le_trans _ (hPT.tiling_valid.allocation_bounds i).1.le
    exact_mod_cast le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ
  have hg : PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
    rcases hm with hm | hm <;> simp [Tiling.gain, hm]
  rw [hg] at hlog
  apply hlog.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (κ.u : ℝ))).2
  nlinarith [mul_le_mul_of_nonneg_left hh ha.le,
    show (0 : ℝ) ≤ κ.a * (T.S.n k : ℝ) ^ κ.ι by positivity]

theorem marginalLaw_width (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (b : S15.OddPosition T k)
    (hn : 1 ≤ (T.S.n k : ℝ)) :
    (marginalLaw PT hPT hm W b).WidthLE ((15 + κ.a) * (T.S.n k : ℝ) ^ κ.ι) := by
  let i := S15.patchAt PT hPT b.1
  let S := S15.clusterSolver PT hPT hm i
  let t := 2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i
  have hM : 0 < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hMR : (0 : ℝ) < (PT.tiling.P i).M := by exact_mod_cast hM
  have hcap (y) : ((PT.tiling.P i).M : ℝ) * (marginalLaw PT hPT hm W b).w y ≤ 8 * Real.exp t := by
    rw [marginalLaw_w]
    have hh := S.marginal_cap (S.groupOf (S15.solverWordAt PT hPT hm b.1))
      (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1)) y
    change ((PT.tiling.P i).M : ℝ) * S.oddMarginal
      (S.groupOf (S15.solverWordAt PT hPT hm b.1))
      (S15.historyOnSlice W (S15.clusterSliceAt PT hPT b.1)) y ≤ 8 * Real.exp t
    unfold SliceSolver.oddMarginal
    simpa only [mul_comm] using (le_div_iff₀ hMR).mp hh
  have hw := law_width_of_cap (T.S.N_pos k) hM (marginalLaw PT hPT hm W b)
    (by positivity : 0 < 8 * Real.exp t) hcap (cluster_log_width hκ PT hPT hm hn i)
  apply Law.WidthLE.mono hw
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (Real.exp_ne_zero t), Real.log_exp]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  norm_num at hlog
  have h1 := Real.one_le_rpow hn hκ.ι_rng.1.le
  have ht := sampler_scale_product hκ (S15.clusterHeight_pos PT hPT hm i)
  have hh : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    apply le_trans _ (hPT.tiling_valid.allocation_bounds i).1.le
    exact_mod_cast le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ
  change (sliceK κ (PT.tiling.P i).h : ℝ) * sliceT κ (PT.tiling.P i).h ≤ _ at ht
  dsimp [t, Tiling.kScale, Tiling.tScale]
  nlinarith

theorem sigmaLaw_width (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : S15.ClusterHistory PT hPT hm) (I : S15.ClusterInternalData PT)
    (a : S15.EvenPosition T k) (ha : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1) :
    (sigmaLaw PT hPT hm W I a ha).WidthLE ((T.S.n k : ℝ) ^ κ.ι) := by
  let i := S15.patchAt PT hPT a.1
  have hg0 : 0 ≤ PT.tiling.gain i := by
    have ha0 : 0 < κ.a := by rw [hκ.a_eq]; positivity [hκ.θ_rng.1]
    rcases hm with hm | hm <;> simp [Tiling.gain, hm] <;> positivity
  have hh : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    apply le_trans _ (hPT.tiling_valid.allocation_bounds i).1.le
    exact_mod_cast le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  intro x
  have hcap := (S15.clusterSolver PT hPT hm i).σ_cap (S15.clusterCenterRole PT hPT hm a)
    (S15.historyOnSlice W (S15.clusterSliceAt PT hPT a.1))
    (nbrLabels (S15.clusterCenterRole PT hPT hm a).1 (I (S15.clusterSliceAt PT hPT a.1)).2) x
  have hpow : (2 : ℝ) ^ (PT.tiling.P i).h ≤ Real.exp ((T.S.n k : ℝ) ^ κ.ι) := by
    calc
      (2 : ℝ) ^ (PT.tiling.P i).h = (Real.exp (Real.log 2)) ^ (PT.tiling.P i).h := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((PT.tiling.P i).h * Real.log 2) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ κ.ι) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have he : Real.exp (-500 * PT.tiling.gain i) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hNR : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  apply (le_div_iff₀ hNR).2
  change S15.clusterSigma PT hPT hm W I a x * (T.S.N k : ℝ) ≤ _
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 ^ (PT.tiling.P i).h)
  change (T.S.N k : ℝ) * S15.clusterSigma PT hPT hm W I a x ≤
    2 ^ (PT.tiling.P i).h * Real.exp (-500 * PT.tiling.gain i) at hcap
  nlinarith
end HypercubeRamsey.Lane_sol_s15_cross
namespace HypercubeRamsey.Lane_sol_s15_cross
open HypercubeRamsey Filter
open Classical
open scoped BigOperators
set_option maxHeartbeats 600000

theorem cluster_crossing_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) : S15.ClusterCrossingClaim κ T := by
  have hιxs : κ.ι < κ.xs := by
    linarith [hκ.ι_rng.2, min_le_left κ.xs (min κ.η0 (0.01 : ℝ)), hκ.xs_rng.1]
  have hι1 : κ.ι < 1 := by linarith [hκ.xs_rng.2]
  have ha : 0 < κ.a := by rw [hκ.a_eq]; positivity [hκ.θ_rng.1]
  have hnlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hs' := hnlim.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι κ.xs
    (30 + κ.a) 1 hιxs (by norm_num))
  have hl' := hnlim.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι 1
    (30 + κ.a) (κ.α / 2) hι1 (by positivity [hκ.α_rng.1]))
  filter_upwards [hDeep, crossing_parameters κ hκ T, hs', hl'] with k hD hp hs hl
  intro PT hPT hm W hW hAlarms a
  rcases hp with ⟨hn, hbsmall, _, _, htail⟩
  let n := (T.S.n k : ℝ)
  let Q := clusterExperiment PT hPT hm W a
  let i := S15.patchAt PT hPT a.1
  have hn1 : 1 ≤ n := hn
  have hn0 : 0 < n := by linarith
  have hp0 : 0 ≤ n ^ κ.ι := Real.rpow_nonneg hn0.le _
  have hpow : 1 ≤ n ^ κ.ι := Real.one_le_rpow hn hκ.ι_rng.1.le
  have hb : 0 < bstar T k := by unfold bstar; positivity
  have hcard : Q.C.card = (S15.clusterCrossingNeighbours PT hPT a).card :=
    Finset.card_image_of_injOn (crossing_slice_injective PT hPT a)
  have hr : Q.C.card ≤ (PT.tiling.P i).ℓ := by
    rw [hcard]
    exact Lane_q_s15_direct.highDirect_crossingNeighbours_card_le_prefix PT hPT a i rfl
  have hrN : (Q.C.card : ℝ) ≤ n := by
    rw [hcard]
    have hsub : S15.clusterCrossingNeighbours PT hPT a ⊆ Lane_q_s15_direct.star a := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
    dsimp [n]
    exact_mod_cast (Finset.card_le_card hsub).trans (Lane_q_s15_direct.star_card_le a)
  have hrcap : (Q.C.card : ℝ) ≤ n ^ κ.ι := by
    have hr' : (Q.C.card : ℝ) ≤ (PT.tiling.P i).ℓ := by exact_mod_cast hr
    have hh : ((PT.tiling.P i).ℓ : ℝ) ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) :=
      by exact_mod_cast le_max_right (PT.tiling.P i).h (PT.tiling.P i).ℓ
    exact hr'.trans (hh.trans (hPT.tiling_valid.allocation_bounds i).1.le)
  by_cases hi : (PT.tiling.P i).ℓ = 0
  · have hc0 : Q.C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hm0 (I) (hI : Q.A I) : S15.clusterCrossingMass PT hPT hm W I a = 1 := by
      rw [← clusterExperiment_mass PT hPT hm W a I hI]
      change Q.mass Q.C I = 1
      simp [hc0, CrossingExperiment.mass, CrossingExperiment.weight, (Q.μ I).sum_eq_one]
    have he : (S15.clusterInternalKernel PT hPT hm W).pr (fun I =>
        (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 ∧
          |S15.clusterCrossingMass PT hPT hm W I a - 1| >
            Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1) = 0 := by
      unfold FinLaw.pr
      apply Finset.sum_eq_zero
      intro I hI
      split_ifs with h
      · have he := hm0 I h.1
        have hf := h.2
        simp [he, hi] at hf
      · rfl
    rw [he]
    positivity
  have hℓ : 1 ≤ (PT.tiling.P i).ℓ := by omega
  have hμ (I) (hI : Q.A I) : (Q.μ I).SupportedIn (T.X k) := by
    change (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 at hI
    change (if h : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 then
      sigmaLaw PT hPT hm W I a h else Law.dirac ⟨0, T.S.N_pos k⟩).SupportedIn _
    rw [dif_pos hI]
    exact sigmaLaw_supported PT hPT hm W hW I a hI
  have hwμ (I) (hI : Q.A I) : (Q.μ I).WidthLE (n ^ κ.ι) := by
    change (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 at hI
    change (if h : (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 then
      sigmaLaw PT hPT hm W I a h else Law.dirac ⟨0, T.S.N_pos k⟩).WidthLE _
    rw [dif_pos hI]
    exact sigmaLaw_width hκ PT hPT hm W I a hI
  have hν (s) (hs : s ∈ Q.C) : (Q.ν s).SupportedIn (T.Y k) := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    rw [clusterExperiment_nu PT hPT hm W a b hb]
    exact marginalLaw_supported PT hPT hm W b
  have hwν (s) (hs : s ∈ Q.C) : (Q.ν s).WidthLE ((15 + κ.a) * n ^ κ.ι) := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    rw [clusterExperiment_nu PT hPT hm W a b hb]
    exact marginalLaw_width hκ PT hPT hm W b hn
  have hs' : (30 + κ.a) * n ^ κ.ι ≤ n ^ κ.xs := by simpa [n] using hs
  have hl' : (30 + κ.a) * n ^ κ.ι ≤ κ.α * n / 2 := by
    simpa [n, Real.rpow_one, div_mul_eq_mul_div] using hl
  have hbudget : n ^ κ.ι + Real.log 2 +
      (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ n ^ κ.xs := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have hf : Real.log 4 + 10 * bstar T k ≤ 4 := by norm_num at hlog4; linarith
    have hm := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ Q.C.card by positivity)
    nlinarith
  have hvbudget : (15 + κ.a) * n ^ κ.ι ≤ n ^ κ.xs := by nlinarith
  have he0 : Real.exp (n ^ κ.ι - κ.α * n) ≤ Real.exp (-κ.α * n / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have heν : Real.exp ((15 + κ.a) * n ^ κ.ι - κ.α * n) ≤ Real.exp (-κ.α * n / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinv : 1 / bstar T k ≤ n := by
    apply (div_le_iff₀ hb).2
    have hnb : n * bstar T k = n ^ (0.04 : ℝ) := by
      calc
        n * bstar T k = n ^ (1 : ℝ) * n ^ (-1 + 0.04 : ℝ) := by simp [bstar, n]
        _ = n ^ ((1 : ℝ) + (-1 + 0.04)) := (Real.rpow_add hn0 _ _).symm
        _ = _ := by norm_num
    rw [hnb]
    exact Real.one_le_rpow hn (by norm_num)
  have htailone : 8 * n ^ (2 : ℕ) * Real.exp (-κ.α * n / 2) ≤ 1 := by
    apply htail.trans
    exact Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr (Nat.cast_nonneg κ.R))
  have hloss : (Q.C.card : ℝ) * (2 * Real.exp (n ^ κ.ι - κ.α * n)) ≤ bstar T k := by
    have he := mul_le_mul hrN (mul_le_mul_of_nonneg_left he0 (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity) (by positivity)
    have hh : (Q.C.card : ℝ) * (2 * Real.exp (n ^ κ.ι - κ.α * n)) / bstar T k ≤ 1 := by
      calc
        _ = ((Q.C.card : ℝ) * (2 * Real.exp (n ^ κ.ι - κ.α * n))) * (1 / bstar T k) := by ring
        _ ≤ (n * (2 * Real.exp (-κ.α * n / 2))) * n :=
          mul_le_mul he hinv (by positivity) (by positivity)
        _ ≤ 8 * n ^ (2 : ℕ) * Real.exp (-κ.α * n / 2) := by nlinarith [Real.exp_pos (-κ.α * n / 2)]
        _ ≤ 1 := htailone
    exact (div_le_one hb).mp hh
  have hD' : TwoBudgetDisc T k (n ^ κ.xs) (κ.α * n) (bstar T k) := by
    simpa [n, bstar] using hD
  have hres := Q.unfiltered_tail hD' (T.S.N_pos k) hb hbsmall hℓ hr hbudget hμ hwμ
    hν hwν hvbudget hloss
  have hpr : (S15.clusterInternalKernel PT hPT hm W).pr (fun I =>
      (∑ x, S15.clusterSigma PT hPT hm W I a x) = 1 ∧
        |S15.clusterCrossingMass PT hPT hm W I a - 1| >
          Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1) ≤
      (FinProb.pi Q.P).pr (fun I => Q.A I ∧
        Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1 < |Q.mass Q.C I - 1|) := by
    change (FinProb.pi Q.P).pr _ ≤ _
    apply CrossingExperiment.pr_mono
    rintro I ⟨hI, hbad⟩
    exact ⟨hI, by rwa [clusterExperiment_mass PT hPT hm W a I hI]⟩
  apply hpr.trans (hres.trans _)
  have he1 := mul_le_mul hrN (mul_le_mul_of_nonneg_left heν (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity) (by positivity)
  have he2 := mul_le_mul hrN (mul_le_mul_of_nonneg_left he0 (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity) (by positivity)
  calc
    (Q.C.card : ℝ) * (2 * Real.exp ((15 + κ.a) * n ^ κ.ι - κ.α * n)) +
      ((Q.C.card : ℝ) * (2 * Real.exp (n ^ κ.ι - κ.α * n))) / bstar T k ≤
        n * (2 * Real.exp (-κ.α * n / 2)) + (n * (2 * Real.exp (-κ.α * n / 2))) * n := by
      rw [div_eq_mul_one_div]
      exact add_le_add he1 (mul_le_mul he2 hinv (by positivity) (by positivity))
    _ ≤ 8 * n ^ (2 : ℕ) * Real.exp (-κ.α * n / 2) := by
      have hpoly : 2 * n + 2 * n ^ (2 : ℕ) ≤ 8 * n ^ (2 : ℕ) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-κ.α * n / 2)).le
      nlinarith only [hmul]
    _ ≤ n ^ (-(κ.R : ℝ)) := htail
end HypercubeRamsey.Lane_sol_s15_cross
