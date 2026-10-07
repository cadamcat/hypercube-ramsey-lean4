import HypercubeRamsey.S03.Clock.Exploration

/-!
# Product-rectangle exploration leaves

A leaf records, per row-label edge, either no inspection, a no-arrival condition through a horizon, or the
exact arrival tick and mark. Its event is therefore a product rectangle in the independent edge-clock data.
The active-endpoint fields encode the exploration dependency graph used for the lopsided coupling.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- One coordinate condition in an exploration leaf. -/
inductive EdgeConstraint (T : ℕ) (α : Type*) where
  | unrestricted : EdgeConstraint T α
  | absentBefore (horizon : Fin (T + 1)) : EdgeConstraint T α
  | exactArrival (tick : Fin T) (mark : α) : EdgeConstraint T α
  deriving DecidableEq

/-- Whether a clock value satisfies one coordinate condition. -/
def EdgeConstraint.Allows {T : ℕ} {α : Type*}
    (C : EdgeConstraint T α) (x : MeshClockValue T α) : Prop :=
  match C, x with
  | .unrestricted, _ => True
  | .absentBefore _, .noArrival => True
  | .absentBefore h, .tick t _ => h.val ≤ t.val
  | .exactArrival t a, x => x = .tick t a

/-- Whether this constraint records an inspection of the edge. -/
def EdgeConstraint.inspected {T : ℕ} {α : Type*} : EdgeConstraint T α → Prop
  | .unrestricted => False
  | .absentBefore _ => True
  | .exactArrival _ _ => True

/-- Whether this constraint records a hit. -/
def EdgeConstraint.isHit {T : ℕ} {α : Type*} : EdgeConstraint T α → Prop
  | .exactArrival _ _ => True
  | _ => False

/-- A rectangle leaf, together with its active endpoints. -/
structure ClockLeaf (T : ℕ) (R : Type*) (g : ℕ) (Ω : R → Type*) where
  constraint : ∀ e : RowLabel R g, EdgeConstraint T (Ω e.1)
  active : Finset (Endpoint R g)
  inspected_touches_active : ∀ e, (constraint e).inspected →
    Sum.inl e.1 ∈ active ∨ Sum.inr e.2 ∈ active
  hits_activate_both : ∀ e, (constraint e).isHit →
    Sum.inl e.1 ∈ active ∧ Sum.inr e.2 ∈ active

/-- The cylinder event specified by a leaf. -/
def ClockLeaf.Event {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L : ClockLeaf T R g Ω) (ξ : ClockField T R g Ω) : Prop :=
  ∀ e, (L.constraint e).Allows (ξ e)

/-- The leaf event is explicitly a product of one-edge coordinate conditions. -/
theorem clockLeaf_rect {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L : ClockLeaf T R g Ω) (ξ : ClockField T R g Ω) :
    L.Event ξ ↔ ∀ e, (L.constraint e).Allows (ξ e) := Iff.rfl

/-- Two leaves are nonneighbors when their active endpoint sets are disjoint. -/
def ClockLeaf.Nonneighbor {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (L L' : ClockLeaf T R g Ω) : Prop := Disjoint L.active L'.active

/-- Avoid every leaf in a finite family. -/
def avoidsLeaves {T : ℕ} {R : Type*} {g : ℕ} {Ω : R → Type*}
    (leaves : List (ClockLeaf T R g Ω)) (ξ : ClockField T R g Ω) : Prop :=
  ∀ L, L ∈ leaves → ¬ L.Event ξ

/-- For a finite product of mesh clocks, forcing a positive leaf cannot increase the probability of avoiding
any finite family of nonneighbor leaves. The coupling delays clocks on shared absence coordinates. -/
theorem leaf_forcing_coupling {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (edgeLaw : ∀ e : RowLabel R g, FinProb (MeshClockValue T (Ω e.1)))
    (L : ClockLeaf T R g Ω) (bad : List (ClockLeaf T R g Ω))
    (hpositive : 0 < (clockFieldLaw edgeLaw).pr L.Event)
    (hnonneighbor : ∀ L' ∈ bad, L.Nonneighbor L') :
    (clockFieldLaw edgeLaw).pr (fun ξ => L.Event ξ ∧ avoidsLeaves bad ξ) /
      (clockFieldLaw edgeLaw).pr L.Event ≤
        (clockFieldLaw edgeLaw).pr (avoidsLeaves bad) := by
  sorry

end HypercubeRamsey.Clock
