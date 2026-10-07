import HypercubeRamsey.S18.Transfer

namespace HypercubeRamsey.S18
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

namespace LateData
variable (D : LateData hPT)
noncomputable def freshConfigLaw (pools : ∀ C, D.fresh.Pool C) : FinLaw (Config D.fresh) :=
  FinLaw.pi (fun C => D.fresh.fresh C (pools C))
noncomputable def poolListOK (pools : ∀ C, D.fresh.Pool C) (v : Pos T k) : Prop :=
  (D.freshConfigLaw pools).pr (D.encoding.events.S v) ≤ Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ))
noncomputable def poolGood (x : D.encoding.InitInput) : Prop :=
  (∀ C, D.fresh.typical C (x.1 C)) ∧ ∀ v, D.poolListOK x.1 v
noncomputable def expandCells (seed : Finset D.geom.Cell) : Finset D.geom.Cell :=
  seed ∪ ((D.encoding.events.graphBall
    (seed.biUnion (D.encoding.events.incidentEvents)) (2 * D.encoding.Ts + 3)).biUnion
      D.encoding.events.scope)
noncomputable def initialRegion (v : Pos T k) := D.expandCells (D.encoding.events.scope v)
noncomputable def lateRegion (f : LateEvent D) :=
  D.expandCells ((cubeBall f.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells)
noncomputable def poolGate (region : Finset D.geom.Cell) (x : D.encoding.InitInput) : Prop :=
  (∀ C ∈ region, D.fresh.typical C (x.1 C)) ∧
    ∀ v, D.encoding.events.scope v ⊆ region → D.poolListOK x.1 v
noncomputable def pLate (f : LateEvent D) (x : D.encoding.InitInput) : ℝ :=
  (D.encoding.kernels.refRun (D.encoding.initialState x)).pr (lateFailure D f)
end LateData

/-- All terminal failures: pool typicality, eq. (23), final S_v, late risk. -/
abbrev TerminalIndex (D : LateData hPT) := (D.geom.Cell ⊕ Pos T k) ⊕ (Pos T k ⊕ LateEvent D)
noncomputable def terminalFailure (D : LateData hPT) (δ : ℝ) (f : TerminalIndex D)
    (x : D.encoding.InitInput) : Prop :=
  match f with
  | .inl (.inl C) => ¬ D.fresh.typical C (x.1 C)
  | .inl (.inr v) => ¬ D.poolListOK x.1 v
  | .inr (.inl v) => D.poolGate (D.initialRegion v) x ∧ D.encoding.events.S v (D.encoding.initialState x)
  | .inr (.inr F) => D.poolGate (D.lateRegion F) x ∧
      Real.exp (-Real.rpow (T.S.n k : ℝ) δ) < D.pLate F x
noncomputable def terminalSet (D : LateData hPT) (δ : ℝ) : Finset D.encoding.InitInput :=
  Finset.univ.filter fun x => ∀ f, ¬ terminalFailure D δ f x
abbrev SlotPin (D : LateData hPT) :=
  Σ C : D.geom.Cell, Fin (D.geom.nslot C) × Bin PT.tiling (D.geom.cellPatch C)
noncomputable def pinEvent (D : LateData hPT) (pin : SlotPin D) (x : D.encoding.InitInput) : Prop :=
  x.1 pin.1 pin.2.1 = pin.2.2
noncomputable def initialProbability (D : LateData hPT) (pin : Option (SlotPin D))
    (event : D.encoding.InitInput → Prop) : ℝ :=
  match pin with
  | none => D.encoding.permLaw.pr event
  | some p => D.encoding.permLaw.pr (fun x => pinEvent D p x ∧ event x) /
      D.encoding.permLaw.pr (pinEvent D p)

def TerminalRiskBound (D : LateData hPT) (δ : ℝ) : Prop :=
  ∀ pin f, initialProbability D pin (terminalFailure D δ f) ≤
    Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))

/-- Canonical terminal avoidance, including actual local nonnegative-test
comparison. There is no separately selectable terminal or requirement table. -/
structure TerminalCertificate (D : LateData hPT) (δ ε : ℝ) where
  positive : 0 < ∑ x ∈ terminalSet D δ, D.encoding.permLaw.w x
  pools : ∀ x ∈ terminalSet D δ, D.poolGood x
  initial : ∀ x ∈ terminalSet D δ, ∀ v, ¬ D.encoding.events.S v (D.encoding.initialState x)
  late : ∀ x ∈ terminalSet D δ, ∀ f, D.pLate f x ≤ Real.exp (-Real.rpow (T.S.n k : ℝ) δ)
  comparison : ∀ seed : Finset D.geom.Cell,
    (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
    ∀ Ψ : D.encoding.InitInput → ℝ, (∀ x, 0 ≤ Ψ x) →
    (∀ x x', (∀ C ∈ D.expandCells seed, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) → Ψ x = Ψ x') →
    (D.encoding.terminalLaw (terminalSet D δ) positive).E Ψ ≤ (1 + ε) * D.encoding.permLaw.E Ψ

/-- A replay is defined on every input. Marked executions are forced; the
ordinary rule is used elsewhere. Each touched cell advances once per round. -/
noncomputable def replayRounds (D : LateData hPT) (marked : Finset (Pos T k))
    (pattern : ℕ → Finset (Pos T k)) (x : D.encoding.InitInput) :
    ℕ → Config D.fresh × (D.geom.Cell → ℕ)
  | 0 => ((fun C => x.2.extend C 0 (x.1 C)), fun _ => 0)
  | t + 1 =>
    let prev := replayRounds D marked pattern x t
    let selected := (pattern t ∩ marked) ∪
      (D.encoding.events.active D.encoding.order Finset.univ prev.1 \ marked)
    let touches := fun C => ∃ v ∈ selected, C ∈ D.encoding.events.scope v
    ((fun C => if touches C then x.2.extend C (prev.2 C + 1) (x.1 C) else prev.1 C),
     fun C => if touches C then prev.2 C + 1 else prev.2 C)
noncomputable def actualPattern (D : LateData hPT) (marked : Finset (Pos T k))
    (x : D.encoding.InitInput) (t : ℕ) :=
  D.encoding.events.active D.encoding.order Finset.univ
    (D.encoding.events.runRounds t D.encoding.order Finset.univ x.1 x.2.extend).1 ∩ marked

def ReplayAgreement (D : LateData hPT) : Prop :=
  ∀ marked x t, replayRounds D marked (actualPattern D marked x) x t =
    D.encoding.events.runRounds t D.encoding.order Finset.univ x.1 x.2.extend

/-- Full neighbor buffer around the events touching critical cells. -/
noncomputable def replayMarked (D : LateData hPT) (critical : Finset D.geom.Cell) : Finset (Pos T k) :=
  let touching := critical.biUnion D.encoding.events.incidentEvents
  touching ∪ (Finset.univ.filter fun v => ∃ u ∈ touching, D.encoding.events.Adjacent v u)

/-- G18: agreement, independence of noncritical outputs, and prescribed
critical tape indices, all for the total forced replay on every input. -/
def ReplayFacts (D : LateData hPT) : Prop :=
  ReplayAgreement D ∧
  (∀ (critical : Finset D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (x x' : D.encoding.InitInput) (t : ℕ),
    (∀ C, C ∉ critical → x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
    ∀ C, C ∉ critical →
      (replayRounds D (replayMarked D critical) pattern x t).1 C =
        (replayRounds D (replayMarked D critical) pattern x' t).1 C ∧
      (replayRounds D (replayMarked D critical) pattern x t).2 C =
        (replayRounds D (replayMarked D critical) pattern x' t).2 C) ∧
  (∀ (critical : Finset D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (x : D.encoding.InitInput) (t : ℕ), ∀ C ∈ critical,
      (replayRounds D (replayMarked D critical) pattern x t).2 C =
        ∑ j ∈ Finset.range t,
          if ∃ v ∈ pattern j ∩ replayMarked D critical, C ∈ D.encoding.events.scope v then 1 else 0)

/-- Leaf forcing acts on the actual permutation-pool/tape experiment. Exact
conditional pushforward and preservation replace the former free bad finset. -/
structure LeafCoupling (D : LateData hPT) (δ : ℝ) where
  Leaf : Type
  [leafFin : Fintype Leaf]
  leaf : Leaf → Finset D.encoding.InitInput
  requirement : Leaf → TerminalIndex D
  domains : Leaf → Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C))
  images : Leaf → Finset (Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i)
  tapes : Leaf → Finset D.geom.Cell
  covers : ∀ f x, terminalFailure D δ f x ↔ ∃ L, requirement L = f ∧ x ∈ leaf L
  adjacent : Leaf → Leaf → Prop
  adjacent_eq : ∀ L L', adjacent L L' ↔
    ¬ Disjoint (domains L) (domains L') ∨ ¬ Disjoint (images L) (images L') ∨ ¬ Disjoint (tapes L) (tapes L')
  depends_on : ∀ L x x',
    (∀ slot ∈ domains L, x.1 slot.1 slot.2 = x'.1 slot.1 slot.2) →
    (∀ C ∈ tapes L, x.2 C = x'.2 C) → (x ∈ leaf L ↔ x' ∈ leaf L)
  scope_bound : ∀ L, ((domains L).card + (images L).card + (tapes L).card : ℝ) ≤
    Real.rpow (T.S.n k : ℝ) (10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r))
  touching_charge : ∀ L,
    (∑ L' : Leaf, if adjacent L L' then 2 * D.encoding.permLaw.pr (fun x => x ∈ leaf L') else 0) ≤
      2 * Real.rpow (T.S.n k : ℝ) (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) - (κ.P : ℝ) * D.encoding.Ts / 3)
  force : ∀ L, 0 < ∑ x ∈ leaf L, D.encoding.permLaw.w x →
    D.encoding.InitInput → FinLaw D.encoding.InitInput
  conditional_pushforward : ∀ L hL,
    FinLaw.map (FinLaw.bind D.encoding.permLaw (force L hL)) Prod.snd =
      FinLaw.cond D.encoding.permLaw (leaf L) hL
  preserves : ∀ L hL x y, 0 < (force L hL x).w y → ∀ L',
    ¬ adjacent L L' → x ∈ leaf L' → y ∈ leaf L'
  /-- Lopsided consequence in the direction used by the local lemma. -/
  nonneighbor_bound : ∀ (L : Leaf) (avoided : Finset Leaf),
    (∀ L' ∈ avoided, ¬ adjacent L L') →
    D.encoding.permLaw.pr (fun x => x ∈ leaf L ∧ ∀ L' ∈ avoided, x ∉ leaf L') ≤
      D.encoding.permLaw.pr (fun x => x ∈ leaf L) *
        D.encoding.permLaw.pr (fun x => ∀ L' ∈ avoided, x ∉ leaf L')
attribute [instance] LeafCoupling.leafFin

end HypercubeRamsey.S18
