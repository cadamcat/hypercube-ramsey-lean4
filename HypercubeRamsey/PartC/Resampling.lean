import HypercubeRamsey.PartC.LowMode

/-!
# Section 17 restricted finite resampling (D17.R)

Each round tests the current configuration, then executes every true event
whose earlier true neighbours are absent. Selected scopes are disjoint by
the priority rule, so each touched cell advances exactly one tape entry.
-/

namespace HypercubeRamsey

open Classical

/-- Event `v` as a predicate of the cell configuration, with its cell scope. -/
structure ListEvent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) where
  S : Pos T k → Config F → Prop
  scope : Pos T k → Finset G.Cell
  scope_ok : ∀ v (c₁ c₂ : Config F),
    (∀ C ∈ scope v, c₁ C = c₂ C) → (S v c₁ ↔ S v c₂)

/-- Tape entry indexed by every possible pool for a cell. -/
abbrev TapeEntry {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (F : FreshCell G) (C : G.Cell) :=
  ∀ _P : F.Pool C, F.State C

namespace ListEvent

/-- Two distinct events are neighbours when their scopes share a cell. -/
def Adjacent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (v w : Pos T k) : Prop :=
  v ≠ w ∧ ¬ Disjoint (LE.scope v) (LE.scope w)

/-- A fixed deterministic rank used to break ties in a user-supplied order. -/
noncomputable def canonicalRank {T : Stage} {k : ℕ}
    (v : Pos T k) : ℕ := (Fintype.equivFin (Pos T k)) v

/-- The total priority induced by an order label and the canonical tie-break. -/
def before {T : Stage} {k : ℕ}
    (order : Pos T k → ℕ) (v w : Pos T k) : Prop :=
  order v < order w ∨ (order v = order w ∧ canonicalRank v < canonicalRank w)

/-- Events selected for execution in one round at configuration `s`. -/
noncomputable def active {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (s : Config F) : Finset (Pos T k) :=
  Finset.univ.filter fun v => v ∈ events ∧ LE.S v s ∧
    ∀ u, u ∈ events → before order u v → LE.Adjacent u v → ¬ LE.S u s

/-- One round of the restricted process, with per-cell tape counters. -/
noncomputable def round {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, F.Pool C) (tapes : ∀ C, ℕ → TapeEntry F C)
    (s : Config F) (count : G.Cell → ℕ) : Config F × (G.Cell → ℕ) := by
  classical
  let selected := LE.active order events s
  let touches : G.Cell → Prop := fun C => ∃ v ∈ selected, C ∈ LE.scope v
  exact (
    (fun C => if h : touches C then tapes C (count C + 1) (pools C) else s C),
    (fun C => if touches C then count C + 1 else count C))

/-- Run exactly `Ts` simultaneous-priority rounds from tape entry zero. -/
noncomputable def runRounds {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (Ts : ℕ) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry F C) : Config F × (G.Cell → ℕ) := by
  classical
  induction Ts with
  | zero =>
      exact ((fun C => tapes C 0 (pools C)), fun _ => 0)
  | succ n ih =>
      exact LE.round order events pools tapes ih.1 ih.2

/-- The final state of a deterministic restricted resampling simulation. -/
noncomputable def resample {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (Ts : ℕ) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry F C) : Config F :=
  (LE.runRounds Ts order events pools tapes).1

/-- The graph ball around a finite set of events in the scope-intersection graph. -/
noncomputable def graphBall {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (seed : Finset (Pos T k)) : ℕ → Finset (Pos T k)
  | 0 => seed
  | n + 1 =>
      let prev := LE.graphBall seed n
      prev ∪ (Finset.univ.filter fun w => ∃ v ∈ prev, LE.Adjacent w v)

/-- Events incident to a cell. -/
def incidentEvents {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (C : G.Cell) : Finset (Pos T k) :=
  Finset.univ.filter fun v => C ∈ LE.scope v

/-- D17.R-loc cell clause: any restricted run containing the full event ball
has the same final state on the central cell as the unrestricted run. -/
def CellLocalitySpec {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (Ts : ℕ) (order : Pos T k → ℕ)
    (pools : ∀ C, F.Pool C) (tapes : ∀ C, ℕ → TapeEntry F C) : Prop :=
  ∀ C events,
    LE.graphBall (LE.incidentEvents C) (2 * Ts + 3) ⊆ events →
      (LE.resample Ts order Finset.univ pools tapes) C =
        (LE.resample Ts order events pools tapes) C

/-- D17.R-loc event clause: the final truth of an event is determined by its
local event ball. -/
def EventTruthLocalitySpec {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} {F : FreshCell G}
    (LE : ListEvent F) (Ts : ℕ) (order : Pos T k → ℕ)
    (pools : ∀ C, F.Pool C) (tapes : ∀ C, ℕ → TapeEntry F C) : Prop :=
  ∀ v events,
    LE.graphBall {v} (2 * Ts + 3) ⊆ events →
      (LE.S v (LE.resample Ts order Finset.univ pools tapes) ↔
        LE.S v (LE.resample Ts order events pools tapes))

end ListEvent

end HypercubeRamsey
