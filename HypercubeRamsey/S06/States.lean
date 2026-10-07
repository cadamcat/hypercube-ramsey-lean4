import HypercubeRamsey.S06.ChunkGeometry

/-!
# Section 6 states, their neighbourhoods, and the encoded cube

L6.1e (06:229–263).  A state retains the residual bits, the coarse bin vector and flag (not the exact coarse
counts), the fine counts with distances `5.5` and `6.5` merged on each side of mid-weight, and the severity
`j`.  It need not determine parity: even and odd states are kept apart by the roles they come from.  The odd
state `b` reads the whole actual-edge neighbourhood `N_q(b)`.

Repair note.  The frozen `StateEncoding6` only tied the state fields to one representative of each state, so
the frozen `L6_1e` was proved with a one-point state space.  The state map is now concrete, and the facts the
later steps use (determination of key/sign/flippable set/severity, `O(n)` neighbours, one state across a
low/high transition, one nonmatching-primary state, coverage of the target by every neighbouring type) are
stated about it; only the one-hot code is existential.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- A Section 6 state (06:231–237). -/
abbrev State6 (L : ChunkLayout6 n) :=
  ({a // a ∈ L.residual} → Bool) × BinVector6 n × KeyFlag6 × (Fin L.m → Fin (n + 1)) × Fin (L.m + 1)

namespace ChunkLayout6

variable (L : ChunkLayout6 n)

/-- The quotient map `q_st` (06:240). -/
def stateOf (x : CubeVertex n) : State6 L :=
  (fun a => x a.1, L.coarseBin x, (L.key x).2, fun i => ⟨min (L.mergedCount x i) n, by omega⟩,
    sevFin6 L.m (L.severity x))

def stKey (s : State6 L) : CoarseKey6 (BinVector6 n) := (s.2.1, s.2.2.1)

def stSign (s : State6 L) : CubeVertex L.m := fun i => decide (L.fineLength < 2 * (s.2.2.2.1 i).val)

def stFlippable (s : State6 L) : Finset (Fin L.m) :=
  Finset.univ.filter fun i => Nat.dist (2 * (s.2.2.2.1 i).val) L.fineLength = 1

def stSeverity (s : State6 L) : ℕ := s.2.2.2.2.val

/-- Even states `𝒮_A = q_st(A)` and odd states `𝒮_B = q_st(B)` (06:241). -/
def evenStates : Finset (State6 L) := (Finset.univ.filter fun x : CubeVertex n => IsEvenRole x).image L.stateOf

def oddStates : Finset (State6 L) :=
  (Finset.univ.filter fun x : CubeVertex n => ¬ IsEvenRole x).image L.stateOf

/-- The even neighbourhood `N_q(b)` of an odd state, defined by actual-edge existence (06:246–252). -/
def stNbr (b : State6 L) : Finset (State6 L) :=
  Finset.univ.filter fun a => ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
    L.stateOf u = b ∧ L.stateOf v = a ∧ (cube n).Adj u v

end ChunkLayout6

/-- The low/high mode of a severity (06:73). -/
def modeOf6 (J j : ℕ) : Mode6 := if j ≤ J then .low else .high

/-- Names of the variables a tuple may be required to hit: named parents and hidden scalars (06:126–131). -/
inductive VarName6 (W : Type*) (m : ℕ) where
  | par (p : ParentName6 W)
  | hid (ℓ : HiddenKey6 W m)
  deriving DecidableEq

/-- The required names of a type: `P_h` and `Z_S` at low; `P_h, P*_h` and `Z_S` at high (06:126–129). -/
def reqNames6 {W : Type*} {m : ℕ} (β : Type6 W m) : Finset (VarName6 W m) :=
  insert (.par (primaryName6 β.key)) (β.obs.image VarName6.hid) ∪
    (if β.mode = .high then {VarName6.par (otherPrimaryName6 β.key)} else ∅)

namespace ChunkLayout6

variable (L : ChunkLayout6 n)

/-- The type of an even state at cutoff `J` (06:118–123). -/
def stType (J : ℕ) (s : State6 L) : Type6 (BinVector6 n) L.m :=
  makeType6 binAdjacent6 (L.stKey s) (L.stSign s) (L.stFlippable s) (L.stSeverity s) J

/-- The low target key `ℓ_b = (h_b, t_b)` of an odd state (06:304). -/
def stTarget (s : State6 L) : HiddenKey6 (BinVector6 n) L.m := (L.stKey s, L.stSign s)

end ChunkLayout6

/-- L6.1e facts about the concrete state map at cutoff `J` (06:231–263, 06:118–131). -/
structure StateFacts6 (L : ChunkLayout6 n) (J : ℕ) : Prop where
  key_eq : ∀ x, L.stKey (L.stateOf x) = L.key x
  sign_eq : ∀ x, L.stSign (L.stateOf x) = L.sign x
  flippable_eq : ∀ x, L.stFlippable (L.stateOf x) = L.flippable x
  severity_eq : ∀ x, L.stSeverity (L.stateOf x) = L.severity x
  nbr_card : ∀ b, (L.stNbr b).card ≤ 3 * n
  nbr_nonempty : ∀ b ∈ L.oddStates, (L.stNbr b).Nonempty
  /-- An even state lies in the neighbourhoods of `O(n)` odd states (06:258). -/
  odd_nbr_card : ∀ a, (L.oddStates.filter fun b => a ∈ L.stNbr b).card ≤ 3 * n
  /-- All neighbours across a low/high transition form one state (06:261–262). -/
  low_high_one : ∀ b, ((L.stNbr b).filter fun a =>
    modeOf6 J (L.stSeverity a) ≠ modeOf6 J (L.stSeverity b)).card ≤ 1
  /-- All nonmatching-primary neighbours form one state (06:262–263). -/
  nonmatching_one : ∀ b, ((L.stNbr b).filter fun a =>
    primaryName6 (L.stKey a) ≠ primaryName6 (L.stKey b)).card ≤ 1
  /-- Every neighbouring type of a low odd state observes its target key (06:123). -/
  low_target_covered : ∀ b, ∀ a ∈ L.stNbr b, modeOf6 J (L.stSeverity b) = .low →
    L.stTarget b ∈ (L.stType J a).obs
  /-- Every neighbouring type of a high odd state requires its named primary (06:130, 06:402). -/
  high_target_required : ∀ b, ∀ a ∈ L.stNbr b, modeOf6 J (L.stSeverity b) = .high →
    VarName6.par (primaryName6 (L.stKey b)) ∈ reqNames6 (L.stType J a)

/-- The one-hot code of the states in an ambient cube of dimension `d = (1+o(1))n` (06:233–258). -/
structure StateCode6 (L : ChunkLayout6 n) where
  d : ℕ
  enc : State6 L → CubeVertex d
  enc_injective : ∀ x y, enc (L.stateOf x) = enc (L.stateOf y) → L.stateOf x = L.stateOf y
  nbr_dist : ∀ b, ∀ a ∈ L.stNbr b, ∀ a' ∈ L.stNbr b, hammingDist (enc a) (enc a') ≤ D₀₆
  residual_dist : ∀ x y, L.residualDist x y ≤ hammingDist (enc (L.stateOf x)) (enc (L.stateOf y))
  d_lower : cd₆ * n ≤ d
  d_upper : (d : ℝ) ≤ Cd₆ * n

/-- L6.1e (facts): the concrete state map determines key, sign, flippable set and severity; neighbourhoods have
`O(n)` states, one low/high-transition state and one nonmatching-primary state, and cover the target
(06:231–263; uses `ChunkFlips6`). -/
theorem L6_1e_facts (α : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (g : ChunkGeometry6 n α) (J : ℕ), StateFacts6 g.L J := by
  sorry

/-- L6.1e (code): one-hot fields give an injective code of role states in `Q_d`, `n/2 ≤ d ≤ 2n`, with even
neighbours of one odd state within distance `10` and residual distance preserved (06:233–258). -/
theorem L6_1e_code (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 100) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ g : ChunkGeometry6 n α, Nonempty (StateCode6 g.L) := by
  sorry

end

end S06
end HypercubeRamsey
