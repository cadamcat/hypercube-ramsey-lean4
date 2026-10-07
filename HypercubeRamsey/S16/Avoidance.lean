import HypercubeRamsey.S16.Geometry
import HypercubeRamsey.S03.ConditionalAvoidance

/-! Primitive local-lemma certificates, before conditioning or calibration.
The certificates concern the input law and its supported singleton pins.
No certificate assumes existence of a feasible or calibrated output law. -/

namespace HypercubeRamsey.S16

open Classical
open scoped BigOperators

/-- Relative perturbations used by centered-price separation. -/
def RelativePerturbation {I O : Type*} [Fintype I] [Fintype O]
    (p q : I → FinLaw O) (ρ : ℝ) : Prop :=
  ∀ i o, (1 - ρ) / (1 + ρ) * (p i).w o ≤ (q i).w o ∧
    (q i).w o ≤ (1 + ρ) / (1 - ρ) * (p i).w o

noncomputable def centeredPrice {I O : Type*} [Fintype I] [Fintype O]
    (p : I → FinLaw O) (c : I × O → ℝ) (i : I) (o : O) : ℝ :=
  c (i, o) - ∑ y, c (i, y) * (p i).w y

/-- Price tilt of the original rows, including its gain and support control.
The constants are independent of the number of rows and of zero atoms. -/
theorem centered_price_perturbation {I O : Type*} [Fintype I] [Fintype O]
    (p : I → FinLaw O) (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1 / 3)
    (c : I × O → ℝ) :
    ∃ q : I → FinLaw O, RelativePerturbation p q ρ ∧
      (∀ i o, (q i).w o ≤ 2 * (p i).w o) ∧
      (∑ io : I × O, centeredPrice p c io.1 io.2 * (q io.1).w io.2) ≥
        ρ / 2 * ∑ io : I × O, |centeredPrice p c io.1 io.2| * (p io.1).w io.2 := by
  classical
  let s : I → O → ℝ := fun i o =>
    if 0 ≤ centeredPrice p c i o then 1 else -1
  let m : I → ℝ := fun i => ∑ o, s i o * (p i).w o
  let z : I → ℝ := fun i => 1 + ρ * m i
  have hsLow : ∀ i o, -1 ≤ s i o := by
    intro i o
    dsimp [s]
    split_ifs <;> norm_num
  have hsHigh : ∀ i o, s i o ≤ 1 := by
    intro i o
    dsimp [s]
    split_ifs <;> norm_num
  have hsPrice : ∀ i o,
      centeredPrice p c i o * s i o = |centeredPrice p c i o| := by
    intro i o
    by_cases h : 0 ≤ centeredPrice p c i o
    · simp [s, h, abs_of_nonneg h]
    · have hn : centeredPrice p c i o < 0 := lt_of_not_ge h
      simp [s, h, abs_of_neg hn]
  have hcenter : ∀ i,
      ∑ o, centeredPrice p c i o * (p i).w o = 0 := by
    intro i
    unfold centeredPrice
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [FinLaw.sum_one]
  have hmLow : ∀ i, -1 ≤ m i := by
    intro i
    dsimp [m]
    have hsum : ∑ o, (p i).w o = 1 := (p i).sum_one
    calc
      -1 = (-1) * ∑ o, (p i).w o := by rw [hsum]; ring
      _ = ∑ o, (-1) * (p i).w o := by rw [Finset.mul_sum]
      _ ≤ ∑ o, s i o * (p i).w o :=
        Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_right
          (hsLow i o) ((p i).nonneg o)
  have hmHigh : ∀ i, m i ≤ 1 := by
    intro i
    dsimp [m]
    have hsum : ∑ o, (p i).w o = 1 := (p i).sum_one
    calc
      ∑ o, s i o * (p i).w o ≤ ∑ o, 1 * (p i).w o :=
        Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_right
          (hsHigh i o) ((p i).nonneg o)
      _ = 1 := by simp [hsum]
  have hρlt : ρ < 1 := by linarith [hρ.2]
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ.1
  have h1m : 0 < 1 - ρ := by linarith
  have h1p : 0 < 1 + ρ := by linarith
  have hzLow : ∀ i, 1 - ρ ≤ z i := by
    intro i
    dsimp [z]
    nlinarith [mul_le_mul_of_nonneg_left (hmLow i) hρnonneg]
  have hzHigh : ∀ i, z i ≤ 1 + ρ := by
    intro i
    dsimp [z]
    nlinarith [mul_le_mul_of_nonneg_left (hmHigh i) hρnonneg]
  have hzPos : ∀ i, 0 < z i := by
    intro i
    have := hzLow i
    linarith
  have htiltLow : ∀ i o, 1 - ρ ≤ 1 + ρ * s i o := by
    intro i o
    nlinarith [mul_le_mul_of_nonneg_left (hsLow i o) hρnonneg]
  have htiltHigh : ∀ i o, 1 + ρ * s i o ≤ 1 + ρ := by
    intro i o
    nlinarith [mul_le_mul_of_nonneg_left (hsHigh i o) hρnonneg]
  have htiltNonneg : ∀ i o, 0 ≤ 1 + ρ * s i o := by
    intro i o
    have := htiltLow i o
    linarith
  have htiltSum : ∀ i, ∑ o, (1 + ρ * s i o) * (p i).w o = z i := by
    intro i
    dsimp [z, m]
    calc
      ∑ o, (1 + ρ * s i o) * (p i).w o =
          ∑ o, ((p i).w o + ρ * (s i o * (p i).w o)) := by
        apply Finset.sum_congr rfl
        intro o ho
        ring
      _ = (∑ o, (p i).w o) + ρ * ∑ o, s i o * (p i).w o := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 + ρ * ∑ o, s i o * (p i).w o := by rw [(p i).sum_one]
  let q : I → FinLaw O := fun i =>
    { w := fun o => ((1 + ρ * s i o) * (p i).w o) / z i
      nonneg := by
        intro o
        exact div_nonneg (mul_nonneg (htiltNonneg i o) ((p i).nonneg o))
          (le_of_lt (hzPos i))
      sum_one := by
        change ∑ o, ((1 + ρ * s i o) * (p i).w o) / z i = 1
        rw [← Finset.sum_div, htiltSum i]
        exact div_self (ne_of_gt (hzPos i)) }
  have hweight : ∀ i o,
      (q i).w o = ((1 + ρ * s i o) / z i) * (p i).w o := by
    intro i o
    simp [q]
    ring
  have hfactorLow : ∀ i o,
      (1 - ρ) / (1 + ρ) ≤ (1 + ρ * s i o) / z i := by
    intro i o
    apply (div_le_div_iff₀ h1p (hzPos i)).2
    have hleft := mul_le_mul_of_nonneg_left (hzHigh i) (by linarith : 0 ≤ 1 - ρ)
    have hright := mul_le_mul_of_nonneg_right (htiltLow i o) (le_of_lt h1p)
    nlinarith
  have hfactorHigh : ∀ i o,
      (1 + ρ * s i o) / z i ≤ (1 + ρ) / (1 - ρ) := by
    intro i o
    apply (div_le_div_iff₀ (hzPos i) h1m).2
    have hleft := mul_le_mul_of_nonneg_right (htiltHigh i o)
      (by linarith : 0 ≤ 1 - ρ)
    have hright := mul_le_mul_of_nonneg_left (hzLow i) (le_of_lt h1p)
    nlinarith
  have hfactorTwo : (1 + ρ) / (1 - ρ) ≤ 2 := by
    apply (div_le_iff₀ h1m).2
    nlinarith [hρ.2]
  have hperturb : RelativePerturbation p q ρ := by
    intro i o
    constructor
    · rw [hweight]
      exact mul_le_mul_of_nonneg_right (hfactorLow i o) ((p i).nonneg o)
    · rw [hweight]
      exact mul_le_mul_of_nonneg_right (hfactorHigh i o) ((p i).nonneg o)
  have hupper : ∀ i o, (q i).w o ≤ 2 * (p i).w o := by
    intro i o
    rw [hweight]
    exact (mul_le_mul_of_nonneg_right (hfactorHigh i o) ((p i).nonneg o)).trans
      (mul_le_mul_of_nonneg_right hfactorTwo ((p i).nonneg o))
  have habsNonneg : ∀ i, 0 ≤ ∑ o, |centeredPrice p c i o| * (p i).w o := by
    intro i
    exact Finset.sum_nonneg fun o _ => mul_nonneg (abs_nonneg _) ((p i).nonneg o)
  have hrow : ∀ i,
      (∑ o, centeredPrice p c i o * (q i).w o) =
        (ρ / z i) * (∑ o, |centeredPrice p c i o| * (p i).w o) := by
    intro i
    calc
      ∑ o, centeredPrice p c i o * (q i).w o =
          ∑ o, (centeredPrice p c i o * (1 + ρ * s i o) * (p i).w o) / z i := by
        apply Finset.sum_congr rfl
        intro o ho
        rw [hweight]
        ring
      _ = (∑ o, centeredPrice p c i o * (1 + ρ * s i o) * (p i).w o) / z i := by
        rw [← Finset.sum_div]
      _ = (∑ o, centeredPrice p c i o * (p i).w o +
          ρ * ∑ o, (centeredPrice p c i o * s i o) * (p i).w o) / z i := by
        congr 1
        calc
          (∑ o, centeredPrice p c i o * (1 + ρ * s i o) * (p i).w o) =
              ∑ o, (centeredPrice p c i o * (p i).w o +
                ρ * (centeredPrice p c i o * s i o * (p i).w o)) := by
            apply Finset.sum_congr rfl
            intro o ho
            ring
          _ = (∑ o, centeredPrice p c i o * (p i).w o) +
              ρ * ∑ o, (centeredPrice p c i o * s i o) * (p i).w o := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (ρ * ∑ o, |centeredPrice p c i o| * (p i).w o) / z i := by
        congr 1
        rw [hcenter i]
        have hsum :
            (∑ o, centeredPrice p c i o * s i o * (p i).w o) =
              ∑ o, |centeredPrice p c i o| * (p i).w o := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [hsPrice i o]
        rw [hsum]
        ring
      _ = (ρ / z i) * (∑ o, |centeredPrice p c i o| * (p i).w o) := by ring
  have hcoef : ∀ i, ρ / 2 ≤ ρ / z i := by
    intro i
    have hz2 : z i ≤ 2 := by
      calc z i ≤ 1 + ρ := hzHigh i
      _ ≤ 2 := by linarith [hρ.2]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (hzPos i)).2
    nlinarith [hρ.1]
  have hgainRow : ∀ i,
      (ρ / 2) * (∑ o, |centeredPrice p c i o| * (p i).w o) ≤
        ∑ o, centeredPrice p c i o * (q i).w o := by
    intro i
    rw [hrow i]
    exact mul_le_mul_of_nonneg_right (hcoef i) (habsNonneg i)
  refine ⟨q, hperturb, hupper, ?_⟩
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ o, centeredPrice p c i o * (q i).w o) ≥
        ∑ i, (ρ / 2) * ∑ o, |centeredPrice p c i o| * (p i).w o :=
      Finset.sum_le_sum fun i _ => hgainRow i
    _ = (ρ / 2) * ∑ i, ∑ o, |centeredPrice p c i o| * (p i).w o := by
      rw [Finset.mul_sum]

/-- An event family over a specified primitive finite experiment. `V` indexes
independent variables (groups, or whole within-bin assignments). `varOf`
identifies the variable containing each observed output coordinate. -/
structure AvoidanceData {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    (readout : Ω → I → O) (varOf : I → V)
    (safe : (I → O) → Prop) where
  base : FinLaw Ω
  Event : Type
  [eventFin : Fintype Event]
  [eventDec : DecidableEq Event]
  bad : Event → Finset Ω
  scope : Event → Finset V
  charge : Event → ℝ
  pinnedBound : Event → I → O → ℝ
  baseJointRate : ℝ
  touchRate : ℝ

instance {I O V Ω : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) : Fintype A.Event := A.eventFin

instance {I O V Ω : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) : DecidableEq A.Event := A.eventDec

namespace AvoidanceData

variable {I O V Ω : Type*} [Fintype I] [DecidableEq I] [Fintype O]
variable [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
variable {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}

noncomputable def avoid (A : AvoidanceData readout varOf safe) (S : Finset A.Event) :
    Finset Ω := Finset.univ.filter fun ω => ∀ e ∈ S, ω ∉ A.bad e

noncomputable def neighbors (A : AvoidanceData readout varOf safe) (e : A.Event) :
    Finset A.Event := Finset.univ.filter fun f => f ≠ e ∧ ¬ Disjoint (A.scope e) (A.scope f)

noncomputable def touching (A : AvoidanceData readout varOf safe) (S : Finset I) :
    Finset A.Event := Finset.univ.filter fun e => ∃ i ∈ S, varOf i ∈ A.scope e

noncomputable def avoidingLaw (A : AvoidanceData readout varOf safe)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) : FinLaw (I → O) :=
  FinLaw.map (FinLaw.cond A.base (A.avoid Finset.univ) hpos) readout

end AvoidanceData

/-- Primitive, robust certificates for the asymmetric local lemma. The
nonneighbor inequalities are multiplicative, so null pins are harmless.
The pin/outside identity is the product-variable independence needed for
T16:347–360; a rare-event bound alone cannot replace it. -/
structure AvoidanceHypotheses {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (original perturbed : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ) : Prop where
  rho_range : 0 < ρ ∧ ρ ≤ 1 / 3
  eta_range : 0 ≤ η ∧ η < 1
  perturbation : RelativePerturbation original perturbed ρ
  base_marginals : ∀ i o, A.base.pr (fun ω => readout ω i = o) = (perturbed i).w o
  safe_cover : ∀ ω, A.base.w ω ≠ 0 → (∀ e, ω ∉ A.bad e) → safe (readout ω)
  charge_range : ∀ e, 0 ≤ A.charge e ∧ A.charge e < 1
  nonneighbor : ∀ e (S : Finset A.Event), e ∉ S →
    (∀ f ∈ S, f ∉ A.neighbors e) →
    A.base.pr (fun ω => ω ∈ A.bad e ∧ ω ∈ A.avoid S) ≤
      A.base.pr (fun ω => ω ∈ A.bad e) * A.base.pr (fun ω => ω ∈ A.avoid S)
  charge_dominates : ∀ e,
    A.base.pr (fun ω => ω ∈ A.bad e) ≤
      A.charge e * ∏ f ∈ A.neighbors e, (1 - A.charge f)
  pinned_nonneighbor : ∀ e i o (S : Finset A.Event), e ∉ S →
    (∀ f ∈ S, f ∉ A.neighbors e) →
    A.base.pr (fun ω => readout ω i = o ∧ ω ∈ A.bad e ∧ ω ∈ A.avoid S) ≤
      A.pinnedBound e i o *
        A.base.pr (fun ω => readout ω i = o ∧ ω ∈ A.avoid S)
  /-- Product independence holds for every outside subfamily, including
  the subfamilies used in the pinned local-lemma induction (T16:350–360). -/
  pinned_outside : ∀ i o (R : Finset A.Event), Disjoint R (A.touching {i}) →
    A.base.pr (fun ω => readout ω i = o ∧ ω ∈ A.avoid R) =
      (perturbed i).w o * A.base.pr (fun ω => ω ∈ A.avoid R)
  pinned_bounds_nonneg : ∀ e i o, 0 ≤ A.pinnedBound e i o
  pinned_touch_budget : ∀ i o,
    (∑ e ∈ A.touching {i}, A.pinnedBound e i o *
      ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) ≤ η
  singleton_cost : ∀ i, (∏ e ∈ A.touching {i}, (1 - A.charge e)⁻¹) ≤ 1 + η
  base_joint : ∀ (S : Finset I) (o : I → O), allowed S →
    A.base.pr (fun ω => ∀ i ∈ S, readout ω i = o i) ≤
      Real.exp (A.baseJointRate * S.card) * ∏ i ∈ S, (perturbed i).w (o i)
  /-- The query event is independent of avoiding events outside its scope. -/
  query_outside : ∀ (S : Finset I) (o : I → O) (R : Finset A.Event),
    allowed S → Disjoint R (A.touching S) →
    A.base.pr (fun ω => (∀ i ∈ S, readout ω i = o i) ∧ ω ∈ A.avoid R) =
      A.base.pr (fun ω => ∀ i ∈ S, readout ω i = o i) *
        A.base.pr (fun ω => ω ∈ A.avoid R)
  joint_cost : ∀ S, allowed S →
    (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) ≤ Real.exp (A.touchRate * S.card)
  rate_budget : A.baseJointRate + Real.log ((1 + ρ) / (1 - ρ)) + A.touchRate ≤ rate

private theorem basePr_mem {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (s : Finset Ω) :
    P.pr (fun ω => ω ∈ s) = HypercubeRamsey.LocalLemma.mass P.w s := by
  classical
  unfold FinLaw.pr HypercubeRamsey.LocalLemma.mass
  calc
    (∑ ω, @ite ℝ ((fun x : Ω => x ∈ s) ω)
        (Classical.propDecidable _) (P.w ω) 0) =
        ∑ ω, @ite ℝ (ω ∈ s) (Finset.decidableMem ω s) (P.w ω) 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hs : ω ∈ s <;> simp [hs]
    _ = ∑ ω ∈ s, P.w ω := Finset.sum_ite_mem_eq s P.w

private theorem basePr_and_mem {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (s t : Finset Ω) :
    P.pr (fun ω => ω ∈ s ∧ ω ∈ t) =
      HypercubeRamsey.LocalLemma.mass P.w (s ∩ t) := by
  classical
  unfold FinLaw.pr HypercubeRamsey.LocalLemma.mass
  calc
    (∑ ω, @ite ℝ ((fun x : Ω => x ∈ s ∧ x ∈ t) ω)
        (Classical.propDecidable _) (P.w ω) 0) =
        ∑ ω, @ite ℝ (ω ∈ s ∩ t) (Finset.decidableMem ω (s ∩ t)) (P.w ω) 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;> simp [hs, ht]
    _ = ∑ ω ∈ s ∩ t, P.w ω := Finset.sum_ite_mem_eq (s ∩ t) P.w

private theorem avoidance_mass_eq {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (S : Finset A.Event) :
    HypercubeRamsey.LocalLemma.mass A.base.w
        (HypercubeRamsey.LocalLemma.avoid A.bad S) =
      ∑ ω ∈ A.avoid S, A.base.w ω := by
  rfl

private theorem avoidanceLocalLemma {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate) :
    (0 < HypercubeRamsey.LocalLemma.mass A.base.w
        (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ)) ∧
      (∀ e (S : Finset A.Event), e ∉ S →
        HypercubeRamsey.LocalLemma.mass A.base.w
            (A.bad e ∩ HypercubeRamsey.LocalLemma.avoid A.bad S) ≤
          A.charge e * HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad S)) ∧
      (∀ (S T : Finset A.Event), Disjoint S T → ∀ W : Ω → ℝ,
        (∀ ω, 0 ≤ W ω) →
        (∑ ω ∈ HypercubeRamsey.LocalLemma.avoid A.bad (S ∪ T),
            A.base.w ω * W ω) /
            HypercubeRamsey.LocalLemma.mass A.base.w
              (HypercubeRamsey.LocalLemma.avoid A.bad (S ∪ T)) ≤
          (∏ e ∈ T, (1 - A.charge e)⁻¹) *
            ((∑ ω ∈ HypercubeRamsey.LocalLemma.avoid A.bad S,
                A.base.w ω * W ω) /
              HypercubeRamsey.LocalLemma.mass A.base.w
                (HypercubeRamsey.LocalLemma.avoid A.bad S))) ∧
      (∀ (F : Finset Ω) (pF : ℝ) (adjF : A.Event → Prop) [DecidablePred adjF],
        (∀ S : Finset A.Event, (∀ e ∈ S, ¬ adjF e) →
          HypercubeRamsey.LocalLemma.mass A.base.w
              (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad S) ≤
            pF * HypercubeRamsey.LocalLemma.mass A.base.w
              (HypercubeRamsey.LocalLemma.avoid A.bad S)) →
        ∀ S : Finset A.Event,
          HypercubeRamsey.LocalLemma.mass A.base.w
              (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad S) /
              HypercubeRamsey.LocalLemma.mass A.base.w
                (HypercubeRamsey.LocalLemma.avoid A.bad S) ≤
            pF * ∏ e ∈ S.filter adjF, (1 - A.charge e)⁻¹) := by
  classical
  let adj : A.Event → A.Event → Prop := fun e f => f ∈ A.neighbors e
  have hadjDec : DecidableRel adj := Classical.decRel _
  letI : DecidableRel adj := hadjDec
  have hsymm : ∀ e f, adj e f → adj f e := by
    intro e f hef
    have hmem := Finset.mem_filter.mp hef
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨hmem.2.1.symm, ?_⟩
    intro hdis
    exact hmem.2.2 hdis.symm
  have hirr : ∀ e, ¬ adj e e := by
    intro e he
    have h := Finset.mem_filter.mp he
    exact h.2.1 rfl
  have hp : ∀ e (S : Finset A.Event), e ∉ S →
      (∀ f ∈ S, ¬ adj e f) →
      HypercubeRamsey.LocalLemma.mass A.base.w
          (A.bad e ∩ HypercubeRamsey.LocalLemma.avoid A.bad S) ≤
        (A.base.pr (fun ω => ω ∈ A.bad e)) *
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad S) := by
    intro e S heS hnon
    rw [← basePr_and_mem A.base (A.bad e)
        (HypercubeRamsey.LocalLemma.avoid A.bad S),
      ← basePr_mem A.base (HypercubeRamsey.LocalLemma.avoid A.bad S)]
    simpa [adj, AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid] using
      hA.nonneighbor e S heS hnon
  have hx0 : ∀ e, 0 ≤ A.charge e := fun e => (hA.charge_range e).1
  have hx1 : ∀ e, A.charge e < 1 := fun e => (hA.charge_range e).2
  have hpx : ∀ e, A.base.pr (fun ω => ω ∈ A.bad e) ≤
      A.charge e * ∏ f ∈ Finset.univ.filter (adj e), (1 - A.charge f) := by
    intro e
    simpa [adj] using hA.charge_dominates e
  have h := HypercubeRamsey.LocalLemma.conditional_avoidance
    A.base.w A.base.nonneg A.base.sum_one A.bad adj
    hsymm hirr
    (fun e => A.base.pr (fun ω => ω ∈ A.bad e)) A.charge hp hx0 hx1 hpx
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [HypercubeRamsey.LocalLemma.mass, HypercubeRamsey.LocalLemma.avoid,
      AvoidanceData.avoid] using h.1
  · intro e S heS
    have he := h.2.1 e S heS
    simpa [HypercubeRamsey.LocalLemma.avoid, AvoidanceData.avoid] using he
  · intro S T hST W hW
    have he := h.2.2.1 S T hST W hW
    simpa [HypercubeRamsey.LocalLemma.mass, HypercubeRamsey.LocalLemma.avoid,
      AvoidanceData.avoid] using he
  · intro F pF adjF inst hF S
    letI : DecidablePred adjF := inst
    have hF' : ∀ S : Finset A.Event, (∀ e ∈ S, ¬ adjF e) →
        HypercubeRamsey.LocalLemma.mass A.base.w
            (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad S) ≤
          pF * HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad S) := by
      intro S hS
      simpa [HypercubeRamsey.LocalLemma.mass, HypercubeRamsey.LocalLemma.avoid,
        AvoidanceData.avoid] using hF S hS
    have he := h.2.2.2 F pF adjF hF' S
    simpa [HypercubeRamsey.LocalLemma.mass, HypercubeRamsey.LocalLemma.avoid,
      AvoidanceData.avoid] using he

private theorem finLaw_map_pr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (B : β → Prop) :
    (FinLaw.map P f).pr B = P.pr (fun a => B (f a)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  calc
    (∑ b, if B b then ∑ a, if f a = b then P.w a else 0 else 0) =
        ∑ b, ∑ a, if B b ∧ f a = b then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hB : B b <;> simp [hB]
    _ = ∑ a, ∑ b, if B b ∧ f a = b then P.w a else 0 := Finset.sum_comm
    _ = ∑ a, if B (f a) then P.w a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hB : B (f a)
      · rw [Finset.sum_eq_single (f a)]
        · simp [hB]
        · intro b hb hne
          have hnot : ¬ (B b ∧ f a = b) := fun hh => hne hh.2.symm
          simp [hnot]
        · simp
      · rw [Finset.sum_eq_single (f a)]
        · simp [hB]
        · intro b hb hne
          have hnot : ¬ (B b ∧ f a = b) := fun hh => hne hh.2.symm
          simp [hnot]
        · simp

private theorem finLaw_cond_pr {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (s : Finset Ω) (hpos : 0 < ∑ ω ∈ s, P.w ω)
    (B : Ω → Prop) :
    (FinLaw.cond P s hpos).pr B =
      P.pr (fun ω => ω ∈ s ∧ B ω) / (∑ ω ∈ s, P.w ω) := by
  classical
  simp only [FinLaw.pr, FinLaw.cond]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hB : B ω <;> by_cases hs : ω ∈ s <;> simp [hB, hs]

private theorem finLaw_pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

private theorem finLaw_pr_union {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω <;> by_cases hB : B ω <;>
    simp [hA, hB, P.nonneg ω]

private theorem finLaw_pr_biUnion_le_sum {Ω κ : Type*} [Fintype Ω]
    [DecidableEq κ] (P : FinLaw Ω) (s : Finset κ) (E : κ → Ω → Prop) :
    P.pr (fun ω => ∃ k ∈ s, E k ω) ≤ ∑ k ∈ s, P.pr (E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinLaw.pr]
  | @insert k s hk ih =>
      have hEq : (fun ω => ∃ j ∈ insert k s, E j ω) =
          (fun ω => E k ω ∨ ∃ j ∈ s, E j ω) := by
        funext ω
        simp [hk]
      calc
        P.pr (fun ω => ∃ j ∈ insert k s, E j ω) =
            P.pr (fun ω => E k ω ∨ ∃ j ∈ s, E j ω) := by rw [hEq]
        _ ≤ P.pr (E k) + P.pr (fun ω => ∃ j ∈ s, E j ω) :=
          finLaw_pr_union P _ _
        _ ≤ P.pr (E k) + ∑ j ∈ s, P.pr (E j) := add_le_add le_rfl ih
        _ = ∑ j ∈ insert k s, P.pr (E j) := by simp [hk]

/-- Local lemma positivity, before an output law is defined. -/
theorem avoidance_positive {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate) :
    0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω := by
  have h := avoidanceLocalLemma A p q allowed ρ η rate hA
  simpa [avoidance_mass_eq] using h.1

/-- Support exclusion follows from the event cover and actual conditioning. -/
theorem avoidance_support {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) :
    ∀ x, (A.avoidingLaw hpos).w x ≠ 0 → safe x := by
  classical
  intro x hx
  have hnonneg := (A.avoidingLaw hpos).nonneg x
  have hxpos : 0 < (A.avoidingLaw hpos).w x := lt_of_le_of_ne hnonneg (Ne.symm hx)
  have hsum : 0 < ∑ ω, (if readout ω = x then
      (FinLaw.cond A.base (A.avoid Finset.univ) hpos).w ω else 0) := by
    simpa [AvoidanceData.avoidingLaw, FinLaw.map] using hxpos
  have hterm_nonneg : ∀ ω, 0 ≤ (if readout ω = x then
      (FinLaw.cond A.base (A.avoid Finset.univ) hpos).w ω else 0) := by
    intro ω
    split_ifs
    · exact (FinLaw.cond A.base (A.avoid Finset.univ) hpos).nonneg ω
    · exact le_rfl
  obtain ⟨ω, hωmem, hω⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun ω hω => hterm_nonneg ω)).mp hsum
  have heq : readout ω = x := by
    by_contra hne
    simp [hne] at hω
  have hcondpos : 0 < (FinLaw.cond A.base (A.avoid Finset.univ) hpos).w ω := by
    simpa [heq] using hω
  have hAvoid : ω ∈ A.avoid Finset.univ := by
    by_contra hnot
    have hzero : (FinLaw.cond A.base (A.avoid Finset.univ) hpos).w ω = 0 := by
      simp [FinLaw.cond, hnot]
    rw [hzero] at hcondpos
    exact (lt_irrefl 0 hcondpos)
  have hbase : A.base.w ω ≠ 0 := by
    intro hz
    have : A.base.w ω = 0 := hz
    simp [FinLaw.cond, hAvoid, this] at hcondpos
  have hAvoid' : ω ∈ Finset.univ.filter
      (fun ω => ∀ e ∈ Finset.univ, ω ∉ A.bad e) := by
    simpa [AvoidanceData.avoid] using hAvoid
  have hforall : ∀ e, ω ∉ A.bad e := by
    simpa using (Finset.mem_filter.mp hAvoid').2
  rw [← heq]
  exact hA.safe_cover ω hbase hforall

/-- Joint comparison: only charges touching the queried variables are paid. -/
theorem avoidance_joint {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) :
    ∀ (S : Finset I) (o : I → O), allowed S →
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) ≤
        Real.exp (rate * S.card) * ∏ i ∈ S, (p i).w (o i) := by
  classical
  intro S o hallowed
  let Q : Ω → Prop := fun ω => ∀ i ∈ S, readout ω i = o i
  let F : Finset Ω := Finset.univ.filter Q
  let adjF : A.Event → Prop := fun e => e ∈ A.touching S
  letI : DecidablePred adjF := Classical.decPred _
  let β : ℝ := (1 + ρ) / (1 - ρ)
  let pF : ℝ := A.base.pr Q
  have hF : ∀ R : Finset A.Event, (∀ e ∈ R, ¬ adjF e) →
      HypercubeRamsey.LocalLemma.mass A.base.w
          (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) ≤
        pF * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad R) := by
    intro R hR
    have hdis : Disjoint R (A.touching S) := by
      apply Finset.disjoint_left.mpr
      intro e heR heTouch
      exact hR e heR heTouch
    have hquery := hA.query_outside S o R hallowed hdis
    have hleft :
        A.base.pr (fun ω => (∀ i ∈ S, readout ω i = o i) ∧
          ω ∈ A.avoid R) =
          HypercubeRamsey.LocalLemma.mass A.base.w
            (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) := by
      calc
        A.base.pr (fun ω => (∀ i ∈ S, readout ω i = o i) ∧
            ω ∈ A.avoid R) =
            A.base.pr (fun ω => ω ∈ F ∧ ω ∈ A.avoid R) := by
          congr 1
          funext ω
          simp [F, Q]
        _ = HypercubeRamsey.LocalLemma.mass A.base.w
            (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) := by
          rw [basePr_and_mem A.base F (A.avoid R)]
          simp [AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid]
    have hq : A.base.pr (fun ω => ∀ i ∈ S, readout ω i = o i) = pF := by
      simp [pF, Q]
    have havoid : A.base.pr (fun ω => ω ∈ A.avoid R) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad R) := by
      simpa [AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid] using
        basePr_mem A.base (A.avoid R)
    have hm : HypercubeRamsey.LocalLemma.mass A.base.w
          (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) =
        pF * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad R) := by
      calc
        _ = A.base.pr (fun ω => (∀ i ∈ S, readout ω i = o i) ∧
              ω ∈ A.avoid R) := hleft.symm
        _ = A.base.pr (fun ω => ∀ i ∈ S, readout ω i = o i) *
              A.base.pr (fun ω => ω ∈ A.avoid R) := hquery
        _ = _ := by rw [← hq, ← havoid]
    exact hm.le
  have hmain := avoidanceLocalLemma A p q allowed ρ η rate hA
  have hlocal := hmain.2.2.2 F pF adjF hF Finset.univ
  have hmap :
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) =
        A.base.pr (fun ω => ω ∈ A.avoid Finset.univ ∧ Q ω) /
          (∑ ω ∈ A.avoid Finset.univ, A.base.w ω) := by
    unfold AvoidanceData.avoidingLaw
    rw [finLaw_map_pr, finLaw_cond_pr]
  have hmapMass :
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) =
        HypercubeRamsey.LocalLemma.mass A.base.w
            (F ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) /
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    rw [hmap]
    have hnumerator : A.base.pr
        (fun ω => ω ∈ A.avoid Finset.univ ∧ Q ω) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (A.avoid Finset.univ ∩ F) := by
      rw [← basePr_and_mem A.base (A.avoid Finset.univ) F]
      congr 1
      funext ω
      simp [F, Q]
    rw [hnumerator, ← avoidance_mass_eq A Finset.univ]
    simp [Finset.inter_comm, AvoidanceData.avoid,
      HypercubeRamsey.LocalLemma.avoid]
  have hlocal' :
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) ≤
        pF * ∏ e ∈ A.touching S, (1 - A.charge e)⁻¹ := by
    rw [hmapMass]
    simpa [adjF] using hlocal
  have hbase : pF ≤
      Real.exp (A.baseJointRate * S.card) *
        ∏ i ∈ S, (q i).w (o i) := by
    simpa [pF, Q] using hA.base_joint S o hallowed
  have hprod :
      (∏ i ∈ S, (q i).w (o i)) ≤
        β ^ S.card * ∏ i ∈ S, (p i).w (o i) := by
    calc
      (∏ i ∈ S, (q i).w (o i)) ≤
          ∏ i ∈ S, β * (p i).w (o i) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (q i).nonneg (o i)
        · intro i hi
          exact (hA.perturbation i (o i)).2
      _ = β ^ S.card * ∏ i ∈ S, (p i).w (o i) := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const]
  have hCost :
      (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) ≤
        Real.exp (A.touchRate * S.card) := hA.joint_cost S hallowed
  have hCostNonneg :
      0 ≤ ∏ e ∈ A.touching S, (1 - A.charge e)⁻¹ := by
    apply Finset.prod_nonneg
    intro e he
    exact inv_nonneg.mpr (le_of_lt (sub_pos.mpr (hA.charge_range e).2))
  have hρltOne : ρ < 1 := by nlinarith [hA.rho_range.1, hA.rho_range.2]
  have hβpos : 0 < β := by
    dsimp [β]
    exact div_pos (by linarith [hA.rho_range.1]) (by linarith [hρltOne])
  have hBaseNonneg :
      0 ≤ Real.exp (A.baseJointRate * S.card) *
        (β ^ S.card * ∏ i ∈ S, (p i).w (o i)) := by
    apply mul_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · apply mul_nonneg
      · exact pow_nonneg (le_of_lt hβpos) _
      · exact Finset.prod_nonneg fun i hi => (p i).nonneg (o i)
  have hβpow : β ^ S.card =
      Real.exp (Real.log β * (S.card : ℝ)) := by
    calc
      β ^ S.card = (Real.exp (Real.log β)) ^ S.card := by
        rw [Real.exp_log hβpos]
      _ = Real.exp ((S.card : ℝ) * Real.log β) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (Real.log β * (S.card : ℝ)) := by congr 1 <;> ring
  have hRate : A.baseJointRate + Real.log β + A.touchRate ≤ rate := by
    simpa [β] using hA.rate_budget
  have hExp :
      Real.exp (A.baseJointRate * S.card) * β ^ S.card *
          Real.exp (A.touchRate * S.card) ≤
        Real.exp (rate * S.card) := by
    rw [hβpow, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hrate := mul_le_mul_of_nonneg_right hRate hcard
    nlinarith [hrate]
  have hPnonneg : 0 ≤ ∏ i ∈ S, (p i).w (o i) :=
    Finset.prod_nonneg fun i hi => (p i).nonneg (o i)
  have houtput :
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) ≤
        Real.exp (A.baseJointRate * S.card) * β ^ S.card *
          Real.exp (A.touchRate * S.card) * ∏ i ∈ S, (p i).w (o i) := by
    calc
      (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) ≤
          pF * ∏ e ∈ A.touching S, (1 - A.charge e)⁻¹ := hlocal'
      _ ≤ (Real.exp (A.baseJointRate * S.card) * β ^ S.card *
            ∏ i ∈ S, (p i).w (o i)) *
            (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) := by
        have htouchNonneg : 0 ≤ ∏ e ∈ A.touching S, (1 - A.charge e)⁻¹ := hCostNonneg
        have hstep1 : pF *
            (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) ≤
            (Real.exp (A.baseJointRate * S.card) *
              (∏ i ∈ S, (q i).w (o i))) *
              (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) :=
          mul_le_mul_of_nonneg_right hbase htouchNonneg
        have hstep2 :
            (Real.exp (A.baseJointRate * S.card) *
              (∏ i ∈ S, (q i).w (o i))) *
              (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) ≤
            (Real.exp (A.baseJointRate * S.card) *
              (β ^ S.card * ∏ i ∈ S, (p i).w (o i))) *
              (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _)))
            htouchNonneg
        have hassoc :
            (Real.exp (A.baseJointRate * S.card) *
              (β ^ S.card * ∏ i ∈ S, (p i).w (o i))) *
              (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) =
            (Real.exp (A.baseJointRate * S.card) * β ^ S.card *
              ∏ i ∈ S, (p i).w (o i)) *
              (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹) := by
          exact congrArg (fun x : ℝ => x *
            (∏ e ∈ A.touching S, (1 - A.charge e)⁻¹))
            (mul_assoc (Real.exp (A.baseJointRate * S.card))
              (β ^ S.card) (∏ i ∈ S, (p i).w (o i))).symm
        exact hstep1.trans (hstep2.trans (le_of_eq hassoc))
      _ ≤ ((Real.exp (A.baseJointRate * S.card) * β ^ S.card) *
            ∏ i ∈ S, (p i).w (o i)) * Real.exp (A.touchRate * S.card) :=
        mul_le_mul_of_nonneg_left hCost (by
          simpa [mul_assoc] using hBaseNonneg)
      _ = Real.exp (A.baseJointRate * S.card) * β ^ S.card *
            Real.exp (A.touchRate * S.card) * ∏ i ∈ S, (p i).w (o i) := by ring
  calc
    (A.avoidingLaw hpos).pr (fun x => ∀ i ∈ S, x i = o i) ≤
        Real.exp (A.baseJointRate * S.card) * β ^ S.card *
          Real.exp (A.touchRate * S.card) * ∏ i ∈ S, (p i).w (o i) := houtput
    _ ≤ Real.exp (rate * S.card) * ∏ i ∈ S, (p i).w (o i) := by
      exact mul_le_mul_of_nonneg_right hExp hPnonneg

/-- Two-sided singleton control uses the pinned touching estimates. -/
theorem avoidance_relative_singletons {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) :
    ∀ i o, |(A.avoidingLaw hpos).pr (fun x => x i = o) - (q i).w o| ≤ η * (q i).w o := by
  classical
  intro i o
  let pin : Ω → Prop := fun ω => readout ω i = o
  let U : Finset A.Event := A.touching {i}
  let R : Finset A.Event := Finset.univ \ U
  let Fpin : Finset Ω := Finset.univ.filter pin
  let q0 : ℝ := (q i).w o
  have hRU : R ∪ U = Finset.univ := by
    ext e
    simp [R]
  have hdisRU : Disjoint R U := by
    apply Finset.disjoint_left.mpr
    intro e heR heU
    exact (Finset.mem_sdiff.mp heR).2 heU
  have hAvoidSplit : A.avoid Finset.univ = A.avoid R ∩ A.avoid U := by
    ext ω
    simp only [AvoidanceData.avoid, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · intro hall
      constructor <;> intro e he <;> exact hall e True.intro
    · rintro ⟨hR, hU⟩ e _
      have heRU : e ∈ R ∪ U := by rw [hRU]; exact Finset.mem_univ e
      rcases Finset.mem_union.mp heRU with h | h
      · exact hR e h
      · exact hU e h
  have hmain := avoidanceLocalLemma A p q allowed ρ η rate hA
  have hfullSubR :
      HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ ⊆
        HypercubeRamsey.LocalLemma.avoid A.bad R := by
    intro ω hω
    simp [HypercubeRamsey.LocalLemma.avoid] at hω ⊢
    intro e heR
    exact hω e
  have hmassMono :
      HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) ≤
        HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad R) :=
    Finset.sum_le_sum_of_subset_of_nonneg hfullSubR
      (fun ω _ _ => A.base.nonneg ω)
  have hRmassPos : 0 < HypercubeRamsey.LocalLemma.mass A.base.w
      (HypercubeRamsey.LocalLemma.avoid A.bad R) := lt_of_lt_of_le hmain.1 hmassMono
  have hRprobPos : 0 < A.base.pr (fun ω => ω ∈ A.avoid R) := by
    rw [basePr_mem]
    simpa [AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid] using hRmassPos
  have hq0 : A.base.pr pin = q0 := by
    simpa [pin, q0] using hA.base_marginals i o
  have hq0nonneg : 0 ≤ q0 := (q i).nonneg o
  have hAvoidProb : ∀ T : Finset A.Event,
      A.base.pr (fun ω => ω ∈ A.avoid T) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad T) := by
    intro T
    simpa [AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid] using
      basePr_mem A.base (A.avoid T)
  have hPinProb : ∀ T : Finset A.Event,
      A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid T) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) := by
    intro T
    rw [← basePr_and_mem A.base Fpin
      (HypercubeRamsey.LocalLemma.avoid A.bad T)]
    congr 1
    funext ω
    simp [Fpin, pin, AvoidanceData.avoid, HypercubeRamsey.LocalLemma.avoid]
  have hPinBadProb : ∀ e T,
      A.base.pr (fun ω => pin ω ∧ ω ∈ A.bad e ∧ ω ∈ A.avoid T) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          ((Fpin ∩ A.bad e) ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) := by
    intro e T
    rw [← basePr_and_mem A.base (Fpin ∩ A.bad e)
      (HypercubeRamsey.LocalLemma.avoid A.bad T)]
    congr 1
    funext ω
    simp [Fpin, pin, and_assoc, AvoidanceData.avoid,
      HypercubeRamsey.LocalLemma.avoid]
  have houtsideR : A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid R) =
      q0 * A.base.pr (fun ω => ω ∈ A.avoid R) := by
    simpa [pin, q0] using hA.pinned_outside i o R hdisRU
  have hstart : A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid R) =
      q0 * A.base.pr (fun ω => ω ∈ A.avoid R) := houtsideR
  let good : Ω → Prop := fun ω => pin ω ∧ ω ∈ A.avoid Finset.univ
  let loss : Ω → Prop := fun ω =>
    ∃ e ∈ U, pin ω ∧ ω ∈ A.avoid R ∧ ω ∈ A.bad e
  have hcover : ∀ ω, pin ω ∧ ω ∈ A.avoid R → good ω ∨ loss ω := by
    intro ω ⟨hpin, hR⟩
    by_cases hU : ω ∈ A.avoid U
    · left
      have hfull : ω ∈ A.avoid Finset.univ := by
        rw [hAvoidSplit]
        exact Finset.mem_inter.mpr ⟨hR, hU⟩
      exact ⟨hpin, hfull⟩
    · right
      have hbad : ∃ e ∈ U, ω ∈ A.bad e := by
        simpa [AvoidanceData.avoid] using hU
      rcases hbad with ⟨e, heU, heBad⟩
      exact ⟨e, heU, hpin, hR, heBad⟩
  have hcoverProb : A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid R) ≤
      A.base.pr (fun ω => good ω ∨ loss ω) :=
    finLaw_pr_mono A.base _ _ hcover
  have hunionProb : A.base.pr (fun ω => good ω ∨ loss ω) ≤
      A.base.pr good + A.base.pr loss := finLaw_pr_union A.base good loss
  let adjPin : A.Event → Prop := fun e => e ∈ U
  letI : DecidablePred adjPin := Classical.decPred _
  have hFpin : ∀ T : Finset A.Event, (∀ e ∈ T, ¬ adjPin e) →
      HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) ≤
        q0 * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad T) := by
    intro T hT
    have hdis : Disjoint T U := by
      apply Finset.disjoint_left.mpr
      intro e heT heU
      exact hT e heT heU
    have hout := hA.pinned_outside i o T hdis
    rw [← hPinProb T, ← hAvoidProb T]
    simpa [pin, q0] using hout.le
  have hlocalPin := hmain.2.2.2 Fpin q0 adjPin hFpin Finset.univ
  have hmapPin :
      (A.avoidingLaw hpos).pr (fun x => x i = o) =
        HypercubeRamsey.LocalLemma.mass A.base.w
            (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) /
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    unfold AvoidanceData.avoidingLaw
    rw [finLaw_map_pr, finLaw_cond_pr]
    have hnum : A.base.pr
        (fun ω => ω ∈ A.avoid Finset.univ ∧ pin ω) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
      have h := hPinProb Finset.univ
      rw [← h]
      congr 1
      funext ω
      simp [Fpin, pin, and_comm]
    rw [hnum, ← avoidance_mass_eq A Finset.univ]
  have hlocalPin' :
      (A.avoidingLaw hpos).pr (fun x => x i = o) ≤
        q0 * ∏ e ∈ U, (1 - A.charge e)⁻¹ := by
    rw [hmapPin]
    simpa [adjPin] using hlocalPin
  have hupper :
      (A.avoidingLaw hpos).pr (fun x => x i = o) ≤ q0 * (1 + η) := by
      calc
      (A.avoidingLaw hpos).pr (fun x => x i = o) ≤
          q0 * ∏ e ∈ U, (1 - A.charge e)⁻¹ := hlocalPin'
      _ ≤ q0 * (1 + η) :=
        mul_le_mul_of_nonneg_left (hA.singleton_cost i) hq0nonneg
  have hFE : ∀ (e : A.Event) (heU : e ∈ U),
      ∀ T : Finset A.Event,
        (∀ f ∈ T, ¬ (f ∈ A.neighbors e ∨ f ∈ U)) →
        HypercubeRamsey.LocalLemma.mass A.base.w
            ((Fpin ∩ A.bad e) ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) ≤
          (q0 * A.pinnedBound e i o) *
            HypercubeRamsey.LocalLemma.mass A.base.w
              (HypercubeRamsey.LocalLemma.avoid A.bad T) := by
    intro e heU T hT
    have heT : e ∉ T := by
      intro he
      exact hT e he (Or.inr heU)
    have hnon : ∀ f ∈ T, f ∉ A.neighbors e := by
      intro f hf hne
      exact hT f hf (Or.inl hne)
    have hdis : Disjoint T U := by
      apply Finset.disjoint_left.mpr
      intro f hf hfu
      exact hT f hf (Or.inr hfu)
    have hpinned := hA.pinned_nonneighbor e i o T heT hnon
    have houtside := hA.pinned_outside i o T hdis
    calc
      HypercubeRamsey.LocalLemma.mass A.base.w
          ((Fpin ∩ A.bad e) ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) =
          A.base.pr (fun ω => pin ω ∧ ω ∈ A.bad e ∧ ω ∈ A.avoid T) :=
        (hPinBadProb e T).symm
      _ ≤ A.pinnedBound e i o *
          A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid T) := hpinned
      _ = A.pinnedBound e i o *
          (q0 * A.base.pr (fun ω => ω ∈ A.avoid T)) := by rw [houtside]
      _ = (q0 * A.pinnedBound e i o) *
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad T) := by
        rw [hAvoidProb T]
        ring
  have hlossBound : A.base.pr loss ≤
      η * q0 * A.base.pr (fun ω => ω ∈ A.avoid R) := by
    calc
      A.base.pr loss ≤ ∑ e ∈ U,
          A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid R ∧ ω ∈ A.bad e) := by
        simpa [loss, and_assoc] using
          finLaw_pr_biUnion_le_sum A.base U
            (fun e ω => pin ω ∧ ω ∈ A.avoid R ∧ ω ∈ A.bad e)
      _ ≤ ∑ e ∈ U,
          q0 * (A.pinnedBound e i o *
            ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) *
            A.base.pr (fun ω => ω ∈ A.avoid R) := by
        apply Finset.sum_le_sum
        intro e heU
        let adjE : A.Event → Prop :=
          fun f => f ∈ A.neighbors e ∨ f ∈ U
        letI : DecidablePred adjE := Classical.decPred _
        have hFE' := hFE e heU
        have hFE'' : ∀ T : Finset A.Event, (∀ f ∈ T, ¬ adjE f) →
            HypercubeRamsey.LocalLemma.mass A.base.w
                ((Fpin ∩ A.bad e) ∩ HypercubeRamsey.LocalLemma.avoid A.bad T) ≤
              (q0 * A.pinnedBound e i o) *
                HypercubeRamsey.LocalLemma.mass A.base.w
                  (HypercubeRamsey.LocalLemma.avoid A.bad T) := by
          simpa [adjE, mul_assoc, mul_left_comm, mul_comm] using hFE'
        have hfilterSub : R.filter adjE ⊆ A.neighbors e := by
          intro f hf
          rcases Finset.mem_filter.mp hf with ⟨hfR, hAdj⟩
          rcases hAdj with hNeigh | hTouch
          · exact hNeigh
          · exact False.elim (Finset.disjoint_left.mp hdisRU hfR hTouch)
        have hprod :
            (∏ f ∈ R.filter adjE, (1 - A.charge f)⁻¹) ≤
              ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹ := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ hfilterSub
          · intro f hf
            exact inv_nonneg.mpr
              (le_of_lt (sub_pos.mpr (hA.charge_range f).2))
          · intro f hf _
            apply (one_le_inv₀ (sub_pos.mpr (hA.charge_range f).2)).2
            linarith [(hA.charge_range f).1]
        have hlocal := hmain.2.2.2 (Fpin ∩ A.bad e)
          (q0 * A.pinnedBound e i o) adjE hFE'' R
        have hprodBound := mul_le_mul_of_nonneg_left hprod
          (mul_nonneg hq0nonneg (hA.pinned_bounds_nonneg e i o))
        have hlocal'' :
            HypercubeRamsey.LocalLemma.mass A.base.w
                ((Fpin ∩ A.bad e) ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) /
              HypercubeRamsey.LocalLemma.mass A.base.w
                (HypercubeRamsey.LocalLemma.avoid A.bad R) ≤
              (q0 * A.pinnedBound e i o) *
                ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹ :=
          hlocal.trans hprodBound
        have hnum := (div_le_iff₀ hRmassPos).1 hlocal''
        have hprob := hPinBadProb e R
        calc
          A.base.pr (fun ω => pin ω ∧ ω ∈ A.avoid R ∧ ω ∈ A.bad e) ≤
              (q0 * A.pinnedBound e i o *
                ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) *
                HypercubeRamsey.LocalLemma.mass A.base.w
                  (HypercubeRamsey.LocalLemma.avoid A.bad R) := by
            have hprob' : A.base.pr
                (fun ω => pin ω ∧ ω ∈ A.avoid R ∧ ω ∈ A.bad e) =
                HypercubeRamsey.LocalLemma.mass A.base.w
                  (Fpin ∩ A.bad e ∩ HypercubeRamsey.LocalLemma.avoid A.bad R) := by
              simpa [and_assoc, and_left_comm, and_comm] using hprob
            rw [hprob']
            simpa [mul_assoc] using hnum
          _ = q0 * (A.pinnedBound e i o *
                ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) *
                A.base.pr (fun ω => ω ∈ A.avoid R) := by
            rw [← hAvoidProb R]
            ring
      _ = (q0 * A.base.pr (fun ω => ω ∈ A.avoid R)) *
          ∑ e ∈ U, A.pinnedBound e i o *
            ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹ := by
        calc
          (∑ e ∈ U, q0 *
              (A.pinnedBound e i o *
                ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) *
              A.base.pr (fun ω => ω ∈ A.avoid R)) =
              ∑ e ∈ U, (q0 * A.base.pr (fun ω => ω ∈ A.avoid R)) *
                (A.pinnedBound e i o *
                  ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹) := by
            apply Finset.sum_congr rfl
            intro e he
            ring
          _ = (q0 * A.base.pr (fun ω => ω ∈ A.avoid R)) *
              ∑ e ∈ U, A.pinnedBound e i o *
                ∏ f ∈ A.neighbors e, (1 - A.charge f)⁻¹ := by
            rw [Finset.mul_sum]
      _ ≤ (q0 * A.base.pr (fun ω => ω ∈ A.avoid R)) * η :=
        mul_le_mul_of_nonneg_left (hA.pinned_touch_budget i o)
          (mul_nonneg hq0nonneg (le_of_lt hRprobPos))
      _ = η * q0 * A.base.pr (fun ω => ω ∈ A.avoid R) := by ring
  have hgoodLower :
      (1 - η) * q0 * A.base.pr (fun ω => ω ∈ A.avoid R) ≤ A.base.pr good := by
    have hstartle := hcoverProb.trans hunionProb
    rw [hstart] at hstartle
    nlinarith [hlossBound]
  have hgoodProb : A.base.pr good =
      HypercubeRamsey.LocalLemma.mass A.base.w
        (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    rw [← basePr_and_mem A.base Fpin
      (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ)]
    congr 1
    funext ω
    simp [good, Fpin, pin, AvoidanceData.avoid,
      HypercubeRamsey.LocalLemma.avoid]
  have hgoodLowerMass :
      q0 * (1 - η) * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad R) ≤
        HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    rw [hgoodProb, hAvoidProb R] at hgoodLower
    nlinarith [hgoodLower]
  have hdenPos : 0 < HypercubeRamsey.LocalLemma.mass A.base.w
      (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    simpa [avoidance_mass_eq] using hpos
  have hdenLe : HypercubeRamsey.LocalLemma.mass A.base.w
      (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) ≤
      HypercubeRamsey.LocalLemma.mass A.base.w
        (HypercubeRamsey.LocalLemma.avoid A.bad R) := hmassMono
  have hcNonneg : 0 ≤ q0 * (1 - η) := by
    have hη : 0 ≤ 1 - η := by nlinarith [(hA.eta_range).2]
    exact mul_nonneg hq0nonneg hη
  have hnumLe :
      q0 * (1 - η) * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) ≤
        HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    calc
      q0 * (1 - η) * HypercubeRamsey.LocalLemma.mass A.base.w
          (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) ≤
          q0 * (1 - η) * HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad R) :=
        mul_le_mul_of_nonneg_left hdenLe hcNonneg
      _ ≤ HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := hgoodLowerMass
  have hlower : q0 * (1 - η) ≤
      HypercubeRamsey.LocalLemma.mass A.base.w
        (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) /
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) :=
    (le_div_iff₀ hdenPos).2 hnumLe
  have hmapPin :
      (A.avoidingLaw hpos).pr (fun x => x i = o) =
        HypercubeRamsey.LocalLemma.mass A.base.w
            (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) /
          HypercubeRamsey.LocalLemma.mass A.base.w
            (HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
    unfold AvoidanceData.avoidingLaw
    rw [finLaw_map_pr, finLaw_cond_pr]
    have hnum : A.base.pr
        (fun ω => ω ∈ A.avoid Finset.univ ∧ pin ω) =
        HypercubeRamsey.LocalLemma.mass A.base.w
          (Fpin ∩ HypercubeRamsey.LocalLemma.avoid A.bad Finset.univ) := by
      have h := hPinProb Finset.univ
      rw [← h]
      congr 1
      funext ω
      simp [Fpin, pin, and_comm]
    rw [hnum, ← avoidance_mass_eq A Finset.univ]
  have houtLower : q0 * (1 - η) ≤
      (A.avoidingLaw hpos).pr (fun x => x i = o) := by
    rw [hmapPin]
    exact hlower
  have habs :
      |(A.avoidingLaw hpos).pr (fun x => x i = o) - q0| ≤ η * q0 := by
    rw [abs_le]
    constructor
    · linarith [houtLower]
    · linarith [hupper]
  simpa [q0] using habs

end HypercubeRamsey.S16
