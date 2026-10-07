import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S15.Needs
import HypercubeRamsey.Framework.FinProbLemmas

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
