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
  sorry

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

/-- Local lemma positivity, before an output law is defined. -/
theorem avoidance_positive {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate) :
    0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω := by
  sorry

/-- Support exclusion follows from the event cover and actual conditioning. -/
theorem avoidance_support {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) :
    ∀ x, (A.avoidingLaw hpos).w x ≠ 0 → safe x := by
  sorry

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
  sorry

/-- Two-sided singleton control uses the pinned touching estimates. -/
theorem avoidance_relative_singletons {I O V Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V] [Fintype Ω]
    {readout : Ω → I → O} {varOf : I → V} {safe : (I → O) → Prop}
    (A : AvoidanceData readout varOf safe) (p q : I → FinLaw O)
    (allowed : Finset I → Prop) (ρ η rate : ℝ)
    (hA : AvoidanceHypotheses A p q allowed ρ η rate)
    (hpos : 0 < ∑ ω ∈ A.avoid Finset.univ, A.base.w ω) :
    ∀ i o, |(A.avoidingLaw hpos).pr (fun x => x i = o) - (q i).w o| ≤ η * (q i).w o := by
  sorry

end HypercubeRamsey.S16
