import HypercubeRamsey.S06.ChunkGeometry
import HypercubeRamsey.S05.Geometry
import HypercubeRamsey.Tools.CubeGeometry

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

set_option maxHeartbeats 1000000
/-- L6.1e (facts): the concrete state map determines key, sign, flippable set and severity; neighbourhoods have
`O(n)` states, one low/high-transition state and one nonmatching-primary state, and cover the target
(06:231–263; uses `ChunkFlips6`). -/
theorem L6_1e_facts (α : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (g : ChunkGeometry6 n α) (J : ℕ), StateFacts6 g.L J := by
  refine ⟨4, ?_⟩
  intro n hn g J
  have hnLarge : 4 ≤ n := by omega
  have hnR4 : 4 ≤ (n : ℝ) := by exact_mod_cast hnLarge
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let L := g.L
  have hfineBound (x : CubeVertex n) (i : Fin L.m) : L.fineCount x i ≤ L.fineLength := by
    calc
      L.fineCount x i ≤ (L.fineChunks i).card := Finset.card_filter_le _ _
      _ = L.fineLength := L.fine_chunk_length i
  have hlenBound : L.fineLength ≤ n := by
    have hpowcmp : (n : ℝ) ^ (3 / 10 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa [Real.sqrt_eq_rpow] using
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (3 / 10 : ℝ) ≤ 1 / 2)
    have hmul : 2 * Real.sqrt (n : ℝ) ≤ n := by
      nlinarith [hnR4, Real.sqrt_nonneg (n : ℝ),
        Real.sq_sqrt (show (0 : ℝ) ≤ n by exact_mod_cast (by omega : 0 ≤ n))]
    have hReal : (L.fineLength : ℝ) ≤ (n : ℝ) := by
      calc
        (L.fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ) := L.fine_length_upper
        _ ≤ 2 * Real.sqrt (n : ℝ) := by gcongr
        _ ≤ n := hmul
    exact_mod_cast hReal
  have hmergedBound (x : CubeVertex n) (i : Fin L.m) :
      L.mergedCount x i ≤ n := by
    have hc := hfineBound x i
    have hn := hlenBound
    dsimp [ChunkLayout6.mergedCount]
    split_ifs <;> omega
  have hseverityBound (x : CubeVertex n) : L.severity x ≤ L.m := by
    unfold ChunkLayout6.severity
    exact (Finset.card_filter_le _ _).trans (by simp)
  let g5 : ChunkGeometry5 n L.m := {
    fineLength := L.fineLength
    coarseChunks := L.coarseChunks
    fineChunks := L.fineChunks
    residual := L.residual
    chunks_disjoint := L.chunks_disjoint
    chunks_cover := L.chunks_cover
    occupied_sublinear := L.occupied_sublinear
    coarse_length := L.coarse_length
    bin := L.bin
    bin_monotone := L.bin_monotone
    bin_consecutive := L.bin_step
    bin_probability_bound := by
      intro i j
      simpa [show (1 / 25 : ℝ) = 4 / 100 by norm_num] using L.bin_probability i j
    fine_length_odd := L.fine_length_odd
    fine_length_lower := L.fine_length_lower
    fine_length_upper := L.fine_length_upper
    fine_chunk_length := L.fine_chunk_length
    residual_nonempty := L.residual_nonempty }
  let keyLift : CoarseKey5 n → CoarseKey6 (BinVector6 n) := fun k =>
    (k.1, if k.2 then KeyFlag6.boundary else KeyFlag6.interior)
  have coarseBin5Eq (x : CubeVertex n) : g5.coarseBin x = L.coarseBin x := by
    funext i
    rfl
  have boundary5Eq (x : CubeVertex n) : g5.boundary x ↔ L.boundary x := by
    unfold ChunkGeometry5.boundary ChunkLayout6.boundary
    constructor
    · rintro ⟨i, a, ha, hneq⟩
      have hneq' : L.coarseBin (flipVertex6 x a) ≠ L.coarseBin x := by
        intro heq
        apply hneq
        rw [coarseBin5Eq (flipVertex5 x a), coarseBin5Eq x]
        simpa [flipVertex5, flipVertex6, BinVector5, BinVector6,
          coarseChunkCount5, coarseChunkCount] using heq
      exact ⟨i, a, ha, hneq'⟩
    · rintro ⟨i, a, ha, hneq⟩
      have hneq' : g5.coarseBin (flipVertex5 x a) ≠ g5.coarseBin x := by
        intro heq
        apply hneq
        rw [coarseBin5Eq (flipVertex5 x a), coarseBin5Eq x] at heq
        simpa [flipVertex5, flipVertex6, BinVector5, BinVector6,
          coarseChunkCount5, coarseChunkCount] using heq
      exact ⟨i, a, ha, hneq'⟩
  have key5Eq (x : CubeVertex n) : keyLift (g5.key x) = L.key x := by
    simp [keyLift, ChunkGeometry5.key, ChunkLayout6.key, coarseBin5Eq, boundary5Eq]
  have sign5Eq (x : CubeVertex n) : g5.sign x = L.sign x := by
    funext i
    rfl
  have flippable5Eq (x : CubeVertex n) : g5.flippable x = L.flippable x := by
    rfl
  have severity5Eq (x : CubeVertex n) : g5.severity x = L.severity x := by
    rfl
  have coarseRangeObs (x : CubeVertex n) (k : CoarseKey5 n)
      (hk : k ∈ g5.coarseRange x) :
      keyLift k ∈ keyNeighborhood6 binAdjacent6 (L.key x) := by
    unfold ChunkGeometry5.coarseRange at hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      rw [key5Eq x]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
    · rcases Finset.mem_image.mp hk with ⟨a, ha, rfl⟩
      have hcoords : ∃ i, a ∈ g5.coarseChunks i := by
        simpa [ChunkGeometry5.coarseCoords] using ha
      obtain ⟨i, hi⟩ := hcoords
      have hadj : (cube n).Adj x (flipVertex5 x a) := by
        simpa [flipVertex5, cubeFlip] using cubeFlip_adj x a
      have hrel : keyAdjacent6 binAdjacent6 (L.key x)
          (keyLift (g5.key (flipVertex5 x a))) := by
        rw [key5Eq (flipVertex5 x a)]
        have hcoarse : a ∈ L.coarseChunks i := by simpa [g5] using hi
        have hdiff : x a ≠ flipVertex6 x a a := by simp [flipVertex6]
        have hrel' := g.flips.coarse_flip_key x (flipVertex6 x a)
          (by simpa [flipVertex5, flipVertex6] using hadj) ⟨i, a, hcoarse, hdiff⟩
        exact hrel'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩
  have hsignMerged (x : CubeVertex n) (i : Fin L.m) :
      (L.fineLength < 2 * L.mergedCount x i) ↔
        (L.fineLength < 2 * L.fineCount x i) := by
    have hc := hfineBound x i
    dsimp [ChunkLayout6.mergedCount]
    split_ifs <;> omega
  have hflipMerged (x : CubeVertex n) (i : Fin L.m) :
      Nat.dist (2 * L.mergedCount x i) L.fineLength = 1 ↔
        Nat.dist (2 * L.fineCount x i) L.fineLength = 1 := by
    have hc := hfineBound x i
    dsimp [ChunkLayout6.mergedCount]
    split_ifs <;> simp only [Nat.dist] <;> omega
  have adjData {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
      ∃ k, x k ≠ y k ∧ ∀ j, j ≠ k → x j = y j := by
    have hcard : (Finset.univ.filter (fun j : Fin n => x j ≠ y j)).card = 1 := hxy
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hmem : k ∈ Finset.univ.filter (fun j : Fin n => x j ≠ y j) := by
      rw [hk]
      simp
    refine ⟨k, (Finset.mem_filter.mp hmem).2, ?_⟩
    intro j hj
    by_contra hne
    have hjmem : j ∈ Finset.univ.filter (fun t : Fin n => x t ≠ y t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hk] at hjmem
    exact hj (Finset.mem_singleton.mp hjmem)
  have filterCardStep {x y : CubeVertex n} (S : Finset (Fin n)) (k : Fin n)
      (hk : k ∈ S) (hxy : x k ≠ y k) (hsame : ∀ a, a ≠ k → x a = y a) :
      ((S.filter (fun a => x a = true)).card + 1 =
          (S.filter (fun a => y a = true)).card) ∨
        ((S.filter (fun a => y a = true)).card + 1 =
          (S.filter (fun a => x a = true)).card) := by
    cases hx : x k <;> cases hy : y k
    · simp_all
    · left
      have hset : S.filter (fun a => y a = true) =
          insert k (S.filter (fun a => x a = true)) := by
        ext a
        by_cases hak : a = k
        · subst a
          simp [hk, hx, hy]
        · simp [hak, hsame a hak]
      have hnot : k ∉ S.filter (fun a => x a = true) := by simp [hk, hx]
      rw [hset, Finset.card_insert_of_notMem hnot]
    · right
      have hset : S.filter (fun a => x a = true) =
          insert k (S.filter (fun a => y a = true)) := by
        ext a
        by_cases hak : a = k
        · subst a
          simp [hk, hx, hy]
        · simp [hak, hsame a hak]
      have hnot : k ∉ S.filter (fun a => y a = true) := by simp [hk, hy]
      rw [hset, Finset.card_insert_of_notMem hnot]
    · simp_all
  have fineSignChangeFlippable {x y : CubeVertex n} (i : Fin L.m)
      (hstep : L.fineCount x i + 1 = L.fineCount y i ∨
        L.fineCount y i + 1 = L.fineCount x i)
      (hsign : L.sign x i ≠ L.sign y i) :
      Nat.dist (2 * L.fineCount y i) L.fineLength = 1 := by
    have hbool : decide (L.fineLength < 2 * L.fineCount x i) ≠
        decide (L.fineLength < 2 * L.fineCount y i) := by
      simpa [ChunkLayout6.sign] using hsign
    rcases L.fine_length_odd with ⟨q, hq⟩
    rcases hstep with hxy | hyx
    · have hmul : 2 * L.fineCount x i < 2 * (L.fineCount x i + 1) := by omega
      have hP : ¬ L.fineLength < 2 * L.fineCount x i := by
        intro hp
        have hQ : L.fineLength < 2 * L.fineCount y i := by
          rw [← hxy]
          exact lt_trans hp hmul
        exact hbool (by simp [hp, hQ])
      have hQ : L.fineLength < 2 * (L.fineCount x i + 1) := by
        by_contra hq'
        have hQ' : ¬ L.fineLength < 2 * L.fineCount y i := by
          rw [← hxy]
          exact hq'
        exact hbool (by simp [hP, hQ'])
      have hLower : 2 * L.fineCount x i ≤ L.fineLength := Nat.le_of_not_gt hP
      have hQy : L.fineLength < 2 * L.fineCount y i := by rw [← hxy]; exact hQ
      have hUpper : L.fineLength ≤ 2 * L.fineCount x i + 1 := by rw [← hxy] at hQy; omega
      have hEll : L.fineLength = 2 * L.fineCount x i + 1 := by omega
      have hle : L.fineLength ≤ 2 * L.fineCount y i := by rw [← hxy, hEll]; omega
      rw [Nat.dist_eq_sub_of_le_right hle, ← hxy, hEll]
      omega
    · have hmul : 2 * L.fineCount y i < 2 * (L.fineCount y i + 1) := by omega
      have hQ : ¬ L.fineLength < 2 * L.fineCount y i := by
        intro hq0
        have hP : L.fineLength < 2 * L.fineCount x i := by
          rw [← hyx]
          exact lt_trans hq0 hmul
        exact hbool (by simp [hP, hq0])
      have hP : L.fineLength < 2 * (L.fineCount y i + 1) := by
        by_contra hp
        have hp' : ¬ L.fineLength < 2 * L.fineCount x i := by
          rw [← hyx]
          exact hp
        exact hbool (by simp [hp', hQ])
      have hLower : 2 * L.fineCount y i ≤ L.fineLength := Nat.le_of_not_gt hQ
      have hPy : L.fineLength < 2 * L.fineCount x i := by rw [← hyx]; exact hP
      have hUpper : L.fineLength ≤ 2 * L.fineCount y i + 1 := by rw [← hyx] at hPy; omega
      have hEll : L.fineLength = 2 * L.fineCount y i + 1 := by omega
      rw [Nat.dist_eq_sub_of_le (by rw [hEll]; omega), hEll]
      omega
  have keyAdjSymm {w w' : BinVector6 n} :
      binAdjacent6 w w' → binAdjacent6 w' w := by
    rintro ⟨i, hsame, hdist⟩
    refine ⟨i, ?_, by simpa [Nat.dist_comm] using hdist⟩
    intro j hji
    exact (hsame j hji).symm
  have keyRelSymm {h k : CoarseKey6 (BinVector6 n)} :
      keyAdjacent6 binAdjacent6 h k → keyAdjacent6 binAdjacent6 k h := by
    intro hadj
    rcases hadj with heq | hbin | ⟨hboundary, kboundary, hbins⟩
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl hbin.symm)
    · exact Or.inr (Or.inr ⟨kboundary, hboundary, keyAdjSymm hbins⟩)
  have keyRelOfAdj {x y : CubeVertex n} (hxy : (cube n).Adj x y) :
      keyAdjacent6 binAdjacent6 (L.key x) (L.key y) := by
    by_cases hc : ∃ i a, a ∈ L.coarseChunks i ∧ x a ≠ y a
    · exact (g.flips.coarse_flip_key x y hxy hc)
    · have hnon : ∀ i a, a ∈ L.coarseChunks i → x a = y a := by
        intro i a ha
        by_contra hne
        exact hc ⟨i, a, ha, hne⟩
      have hkey := g.flips.noncoarse_flip_key x y hxy hnon
      exact Or.inl hkey
  have severityEqOfCoarseFlip {x y : CubeVertex n} (hxy : (cube n).Adj x y)
      (hc : ∃ i a, a ∈ L.coarseChunks i ∧ x a ≠ y a) :
      L.severity x = L.severity y := by
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    rcases hc with ⟨i, a, hcoarse, haxy⟩
    have hak : a = k := by
      by_contra hne
      exact haxy (hsame a hne)
    subst a
    have hFine : ∀ j b, b ∈ L.fineChunks j → x b = y b := by
      intro j b hb
      by_cases hbk : b = k
      · subst b
        have hdisj := L.chunks_disjoint.2.1 i j
        exact False.elim ((Finset.disjoint_left.mp hdisj) hcoarse hb)
      · exact hsame b hbk
    exact (g.flips.nonfine_flip_fine x y hxy hFine).2.2
  have coarseEdgeFields {x y : CubeVertex n} (hxy : (cube n).Adj x y)
      (hc : ∃ i a, a ∈ L.coarseChunks i ∧ x a ≠ y a) :
      (∀ a, a ∈ L.residual → x a = y a) ∧
        (∀ i, L.mergedCount x i = L.mergedCount y i) := by
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    rcases hc with ⟨i, a, hcoarse, haxy⟩
    have hak : a = k := by
      by_contra hne
      exact haxy (hsame a hne)
    subst a
    have hres : ∀ a, a ∈ L.residual → x a = y a := by
      intro a haR
      by_cases hak : a = k
      · subst a
        have hdisj := L.chunks_disjoint.2.2.2.1 i
        exact False.elim ((Finset.disjoint_left.mp hdisj) hcoarse haR)
      · exact hsame a hak
    have hcount (j : Fin L.m) : L.fineCount x j = L.fineCount y j := by
      unfold ChunkLayout6.fineCount
      apply congrArg Finset.card
      ext a
      by_cases haFine : a ∈ L.fineChunks j
      · by_cases hak : a = k
        · subst a
          have hdisj := L.chunks_disjoint.2.1 i j
          exact False.elim ((Finset.disjoint_left.mp hdisj.symm) haFine hcoarse)
        · simp [haFine, hsame a hak]
      · simp [haFine]
    refine ⟨hres, ?_⟩
    intro j
    simp [ChunkLayout6.mergedCount, hcount j]
  have keyDiffFacts {h k : CoarseKey6 (BinVector6 n)}
      (hadj : keyAdjacent6 binAdjacent6 h k)
      (hdiff : primaryName6 h ≠ primaryName6 k) : h.1 = k.1 ∧ h.2 ≠ k.2 := by
    rcases hadj with heq | hsame | ⟨hh, hk, _⟩
    · subst k
      exact (hdiff rfl).elim
    · refine ⟨hsame, ?_⟩
      intro hf
      apply hdiff
      exact congrArg primaryName6 (Prod.ext hsame hf)
    · rcases h with ⟨w, f⟩
      rcases k with ⟨w', f'⟩
      have hf : f = .boundary := hh
      have hf' : f' = .boundary := hk
      subst f
      subst f'
      exact (hdiff rfl).elim
  have otherFlagOfNe (f f' : KeyFlag6) (hne : f ≠ f') :
      f' = (if f = KeyFlag6.interior then KeyFlag6.boundary else KeyFlag6.interior) := by
    cases f <;> cases f' <;> simp_all
  have keyPrimary {h k : CoarseKey6 (BinVector6 n)}
      (hadj : keyAdjacent6 binAdjacent6 h k) :
      primaryName6 h = primaryName6 k ∨
        primaryName6 h = otherPrimaryName6 k := by
    rcases hadj with heq | hsame | ⟨hh, hk, _⟩
    · subst k
      exact Or.inl rfl
    · rcases h with ⟨w, f⟩
      rcases k with ⟨w', f'⟩
      have hw : w = w' := hsame
      subst w'
      cases f <;> cases f' <;> simp [primaryName6, otherPrimaryName6]
    · rcases h with ⟨w, f⟩
      rcases k with ⟨w', f'⟩
      have hf : f = .boundary := hh
      have hf' : f' = .boundary := hk
      subst f
      subst f'
      exact Or.inl rfl
  have reqPrimary {β : Type6 (BinVector6 n) L.m} :
      VarName6.par (primaryName6 β.key) ∈ reqNames6 β := by
    simp [reqNames6]
  have reqOther {β : Type6 (BinVector6 n) L.m} (hmode : β.mode = .high) :
      VarName6.par (otherPrimaryName6 β.key) ∈ reqNames6 β := by
    simp [reqNames6, hmode]
  have reqForName {β : Type6 (BinVector6 n) L.m} (name : ParentName6 (BinVector6 n))
      (hname : name = primaryName6 β.key ∨
        (β.mode = .high ∧ name = otherPrimaryName6 β.key)) :
      VarName6.par name ∈ reqNames6 β := by
    rcases hname with h | ⟨hm, h⟩
    · rw [h]
      exact reqPrimary
    · rw [h]
      exact reqOther hm
  have stateKeyEq (x : CubeVertex n) :
      L.stKey (L.stateOf x) = L.key x := by
    simp [ChunkLayout6.stKey, ChunkLayout6.stateOf, ChunkLayout6.key]
  have stateSeverityEq (x : CubeVertex n) :
      L.stSeverity (L.stateOf x) = L.severity x := by
    change min (L.severity x) L.m = L.severity x
    exact Nat.min_eq_left (hseverityBound x)
  have stTypeKey (x : CubeVertex n) :
      (L.stType J (L.stateOf x)).key = L.key x := by
    simp only [ChunkLayout6.stType, Type6.key, makeType6]
    split_ifs <;> exact stateKeyEq x
  have stTypeHigh (x : CubeVertex n)
      (hmode : modeOf6 J (L.severity x) = .high) :
      (L.stType J (L.stateOf x)).mode = .high := by
    have hsev := stateSeverityEq x
    have hnot : ¬ L.severity x ≤ J := by
      intro hle
      simp [modeOf6, hle] at hmode
    simp only [ChunkLayout6.stType, Type6.mode, makeType6]
    rw [hsev]
    simp [hnot]
  have stateSignEq (x : CubeVertex n) :
      L.stSign (L.stateOf x) = L.sign x := by
    funext i
    change decide (L.fineLength < 2 * min (L.mergedCount x i) n) =
      decide (L.fineLength < 2 * L.fineCount x i)
    rw [Nat.min_eq_left (hmergedBound x i)]
    by_cases hm : L.fineLength < 2 * L.mergedCount x i
    · have hc : L.fineLength < 2 * L.fineCount x i := (hsignMerged x i).mp hm
      simp [hm, hc]
    · have hc : ¬ L.fineLength < 2 * L.fineCount x i := by
        intro hc
        exact hm ((hsignMerged x i).mpr hc)
      simp [hm, hc]
  have stateFlippableEq (x : CubeVertex n) :
      L.stFlippable (L.stateOf x) = L.flippable x := by
    ext i
    unfold ChunkLayout6.stFlippable ChunkLayout6.stateOf ChunkLayout6.flippable
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.min_eq_left (hmergedBound x i)]
    exact hflipMerged x i
  have transitionData {x y : CubeVertex n} (hxy : (cube n).Adj x y)
      (hmode : modeOf6 J (L.severity x) ≠ modeOf6 J (L.severity y)) :
      L.key x = L.key y ∧
        (∀ a, a ∈ L.residual → x a = y a) ∧
        (∀ i, L.mergedCount x i = L.mergedCount y i) ∧
        ((L.severity x = J ∧ L.severity y = J + 1) ∨
          (L.severity x = J + 1 ∧ L.severity y = J)) := by
    have hnoCoarse : ¬ ∃ i a, a ∈ L.coarseChunks i ∧ x a ≠ y a := by
      intro hc
      have hsev := severityEqOfCoarseFlip hxy hc
      apply hmode
      simp [modeOf6, hsev]
    have hFine : ∃ i a, a ∈ L.fineChunks i ∧ x a ≠ y a := by
      by_contra hnone
      have hnon : ∀ i a, a ∈ L.fineChunks i → x a = y a := by
        intro i a ha
        by_contra hne
        exact hnone ⟨i, a, ha, hne⟩
      have hsev := (g.flips.nonfine_flip_fine x y hxy hnon).2.2
      apply hmode
      rw [hsev]
    obtain ⟨i, a, ha, haxy⟩ := hFine
    obtain ⟨k, hneq, hsame⟩ := adjData hxy
    have hak : a = k := by
      by_contra hne
      exact haxy (hsame a hne)
    subst a
    have hnoncoarse : ∀ j b, b ∈ L.coarseChunks j → x b = y b := by
      intro j b hb
      by_contra hne
      exact hnoCoarse ⟨j, b, hb, hne⟩
    have hkey : L.key x = L.key y := g.flips.noncoarse_flip_key x y hxy hnoncoarse
    have hres : ∀ b, b ∈ L.residual → x b = y b := by
      intro b hb
      by_cases hbk : b = k
      · subst b
        exact False.elim ((Finset.disjoint_left.mp (L.chunks_disjoint.2.2.2.2 i)) ha hb)
      · exact hsame b hbk
    have hcount (j : Fin L.m) (hji : j ≠ i) :
        L.fineCount x j = L.fineCount y j := by
      unfold ChunkLayout6.fineCount
      apply congrArg Finset.card
      ext b
      by_cases hb : b ∈ L.fineChunks j
      · by_cases hbk : b = k
        · subst b
          exact False.elim ((Finset.disjoint_left.mp
            (L.chunks_disjoint.2.2.1 i j (Ne.symm hji)) ha hb))
        · simp [hb, hsame b hbk]
      · simp [hb]
    have hstep : L.fineCount x i + 1 = L.fineCount y i ∨
        L.fineCount y i + 1 = L.fineCount x i := by
      simpa [ChunkLayout6.fineCount] using
        filterCardStep (L.fineChunks i) k ha hneq hsame
    have hcase : (L.severity x ≤ J ∧ J < L.severity y) ∨
        (L.severity y ≤ J ∧ J < L.severity x) := by
      by_cases hx : L.severity x ≤ J
      · by_cases hy : L.severity y ≤ J
        · exfalso
          apply hmode
          simp [modeOf6, hx, hy]
        · exact Or.inl ⟨hx, Nat.lt_of_not_ge hy⟩
      · by_cases hy : L.severity y ≤ J
        · exact Or.inr ⟨hy, Nat.lt_of_not_ge hx⟩
        · exfalso
          apply hmode
          simp [modeOf6, hx, hy]
    have hdist : Nat.dist (L.severity x) (L.severity y) ≤ 1 :=
      g.flips.fine_flip_severity x y hxy ⟨i, k, ha, hneq⟩
    have hsevCase : (L.severity x = J ∧ L.severity y = J + 1) ∨
        (L.severity x = J + 1 ∧ L.severity y = J) := by
      rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · have hlt : L.severity x < L.severity y := by omega
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hdist
        omega
      · have hlt : L.severity y < L.severity x := by omega
        rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hlt)] at hdist
        omega
    let A := Finset.univ.filter fun j : Fin L.m =>
      Nat.dist (2 * L.fineCount x j) L.fineLength ≤ 11
    let B := Finset.univ.filter fun j : Fin L.m =>
      Nat.dist (2 * L.fineCount y j) L.fineLength ≤ 11
    have hErase : A.erase i = B.erase i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B]
      · simp only [A, B, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rw [hcount j hji]
    have hcardErase (T : Finset (Fin L.m)) :
        T.card = (T.erase i).card + if i ∈ T then 1 else 0 := by
      by_cases hi : i ∈ T
      · rw [← Finset.insert_erase hi, Finset.card_insert_of_notMem (by simp)]
        simp [hi]
      · simp [hi]
    have hsevNe : L.severity x ≠ L.severity y := by
      rcases hsevCase with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    have hnear : (i ∈ A) ≠ (i ∈ B) := by
      intro hsameNear
      have hmem : i ∈ A ↔ i ∈ B := Iff.of_eq hsameNear
      have hcard : A.card = B.card := by
        rw [hcardErase A, hcardErase B, hErase]
        by_cases hiA : i ∈ A
        · have hiB : i ∈ B := hmem.mp hiA
          simp [hiA, hiB]
        · have hiB : i ∉ B := by
            intro h
            exact hiA (hmem.mpr h)
          simp [hiA, hiB]
      apply hsevNe
      simpa [A, B, ChunkLayout6.severity] using hcard
    rcases L.fine_length_odd with ⟨q, hq⟩
    have oddDistance (c : ℕ) : Odd (Nat.dist (2 * c) L.fineLength) := by
      rw [hq]
      by_cases h : 2 * c ≤ 2 * q + 1
      · have hz : 2 * c - (2 * q + 1) = 0 := Nat.sub_eq_zero_of_le h
        refine ⟨q - c, ?_⟩
        unfold Nat.dist
        rw [hz]
        omega
      · have hle : 2 * q + 1 ≤ 2 * c := by omega
        have hz : 2 * q + 1 - 2 * c = 0 := Nat.sub_eq_zero_of_le hle
        refine ⟨c - q - 1, ?_⟩
        unfold Nat.dist
        rw [hz]
        omega
    have distanceStepBound (c : ℕ) :
        Nat.dist (2 * c) L.fineLength ≤ Nat.dist (2 * (c + 1)) L.fineLength + 2 ∧
        Nat.dist (2 * (c + 1)) L.fineLength ≤ Nat.dist (2 * c) L.fineLength + 2 := by
      rw [hq]
      unfold Nat.dist
      omega
    have hmergedAt : L.mergedCount x i = L.mergedCount y i := by
      have hdistPair :
          (Nat.dist (2 * L.fineCount x i) L.fineLength = 11 ∧
            Nat.dist (2 * L.fineCount y i) L.fineLength = 13) ∨
          (Nat.dist (2 * L.fineCount x i) L.fineLength = 13 ∧
            Nat.dist (2 * L.fineCount y i) L.fineLength = 11) := by
        by_cases hx : i ∈ A
        · by_cases hy : i ∈ B
          · exact (hnear (propext ⟨fun _ => hy, fun _ => hx⟩)).elim
          · have hx' : Nat.dist (2 * L.fineCount x i) L.fineLength ≤ 11 :=
              (Finset.mem_filter.mp hx).2
            have hy' : 11 < Nat.dist (2 * L.fineCount y i) L.fineLength := by
              by_contra h
              exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
            have hdxOdd := oddDistance (L.fineCount x i)
            have hdyOdd := oddDistance (L.fineCount y i)
            rcases hdxOdd with ⟨cx, hcx⟩
            rcases hdyOdd with ⟨cy, hcy⟩
            rcases hstep with hxy | hyx
            · have hbound := distanceStepBound (L.fineCount x i)
              rw [hxy] at hbound
              rcases hbound with ⟨hbound₁, hbound₂⟩
              simp only [hcx, hcy] at hx' hy' hbound₁ hbound₂
              have heq : Nat.dist (2 * L.fineCount x i) L.fineLength = 11 := by omega
              have heq' : Nat.dist (2 * L.fineCount y i) L.fineLength = 13 := by omega
              exact Or.inl ⟨heq, heq'⟩
            · have hbound := distanceStepBound (L.fineCount y i)
              rw [hyx] at hbound
              rcases hbound with ⟨hbound₁, hbound₂⟩
              simp only [hcx, hcy] at hx' hy' hbound₁ hbound₂
              have heq : Nat.dist (2 * L.fineCount x i) L.fineLength = 11 := by omega
              have heq' : Nat.dist (2 * L.fineCount y i) L.fineLength = 13 := by omega
              exact Or.inl ⟨heq, heq'⟩
        · by_cases hy : i ∈ B
          · have hx' : 11 < Nat.dist (2 * L.fineCount x i) L.fineLength := by
              by_contra h
              exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
            have hy' : Nat.dist (2 * L.fineCount y i) L.fineLength ≤ 11 :=
              (Finset.mem_filter.mp hy).2
            have hdxOdd := oddDistance (L.fineCount x i)
            have hdyOdd := oddDistance (L.fineCount y i)
            rcases hdxOdd with ⟨cx, hcx⟩
            rcases hdyOdd with ⟨cy, hcy⟩
            rcases hstep with hxy | hyx
            · have hbound := distanceStepBound (L.fineCount x i)
              rw [hxy] at hbound
              rcases hbound with ⟨hbound₁, hbound₂⟩
              simp only [hcx, hcy] at hx' hy' hbound₁ hbound₂
              have heq : Nat.dist (2 * L.fineCount y i) L.fineLength = 11 := by omega
              have heq' : Nat.dist (2 * L.fineCount x i) L.fineLength = 13 := by omega
              exact Or.inr ⟨heq', heq⟩
            · have hbound := distanceStepBound (L.fineCount y i)
              rw [hyx] at hbound
              rcases hbound with ⟨hbound₁, hbound₂⟩
              simp only [hcx, hcy] at hx' hy' hbound₁ hbound₂
              have heq : Nat.dist (2 * L.fineCount y i) L.fineLength = 11 := by omega
              have heq' : Nat.dist (2 * L.fineCount x i) L.fineLength = 13 := by omega
              exact Or.inr ⟨heq', heq⟩
          · have hSame : (i ∈ A) = (i ∈ B) := by
              apply propext
              constructor
              · exact fun h => (hx h).elim
              · exact fun h => (hy h).elim
            exact (hnear hSame).elim
      rcases hdistPair with ⟨hx11, hy13⟩ | ⟨hx13, hy11⟩
      · have hx13' := hy13
        have hx11' := hx11
        unfold Nat.dist at hx13' hx11'
        dsimp [ChunkLayout6.mergedCount]
        split_ifs <;> omega
      · have hx13' := hx13
        have hy11' := hy11
        unfold Nat.dist at hx13' hy11'
        dsimp [ChunkLayout6.mergedCount]
        split_ifs <;> omega
    have hmerged : ∀ j, L.mergedCount x j = L.mergedCount y j := by
      intro j
      by_cases hji : j = i
      · subst j
        exact hmergedAt
      · have hc := hcount j hji
        simp [ChunkLayout6.mergedCount, hc]
    exact ⟨hkey, hres, hmerged, hsevCase⟩
  refine {
    key_eq := by
      intro x
      simp [ChunkLayout6.stKey, ChunkLayout6.stateOf, ChunkLayout6.key]
    sign_eq := stateSignEq
    flippable_eq := stateFlippableEq
    severity_eq := by
      intro x
      change min (L.severity x) L.m = L.severity x
      exact Nat.min_eq_left (hseverityBound x)
    nbr_card := by sorry
    nbr_nonempty := by
      intro b hb
      have hb' : ∃ x : CubeVertex n, ¬ IsEvenRole x ∧ L.stateOf x = b := by
        simpa [ChunkLayout6.oddStates] using hb
      rcases hb' with ⟨x, hx, rfl⟩
      have hn : 0 < n := by omega
      let i : Fin n := ⟨0, hn⟩
      let y := flipVertex6 x i
      have hy : IsEvenRole y := by
        change IsEvenRole (flipVertex6 x i)
        exact (cubeFlip_parity x i).mpr hx
      have hxy : (cube n).Adj x y := by
        change (cube n).Adj x (cubeFlip x i)
        simpa [y, flipVertex6, cubeFlip] using cubeFlip_adj x i
      refine ⟨L.stateOf y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨x, y, hx, hy, rfl, rfl, hxy⟩
    odd_nbr_card := by sorry
    low_high_one := by
      intro b
      let S := (L.stNbr b).filter fun a =>
        modeOf6 J (L.stSeverity a) ≠ modeOf6 J (L.stSeverity b)
      change S.card ≤ 1
      rw [Finset.card_le_one_iff]
      intro a a' ha ha'
      have hmemA : a ∈ L.stNbr b ∧
          modeOf6 J (L.stSeverity a) ≠ modeOf6 J (L.stSeverity b) := by
        simpa [S] using ha
      have hmemA' : a' ∈ L.stNbr b ∧
          modeOf6 J (L.stSeverity a') ≠ modeOf6 J (L.stSeverity b) := by
        simpa [S] using ha'
      rcases hmemA with ⟨haNbr, hmodeA⟩
      rcases hmemA' with ⟨haNbr', hmodeA'⟩
      rcases (Finset.mem_filter.mp haNbr).2 with ⟨u, v, hu, hv, hbu, hav, hxy⟩
      rcases (Finset.mem_filter.mp haNbr').2 with ⟨u', v', hu', hv', hbu', hav', hxy'⟩
      have hmodeUV : modeOf6 J (L.severity u) ≠ modeOf6 J (L.severity v) := by
        rw [← hav, ← hbu, stateSeverityEq v, stateSeverityEq u] at hmodeA
        exact Ne.symm hmodeA
      have hmodeU'V' : modeOf6 J (L.severity u') ≠ modeOf6 J (L.severity v') := by
        rw [← hav', ← hbu', stateSeverityEq v', stateSeverityEq u'] at hmodeA'
        exact Ne.symm hmodeA'
      have hdata := transitionData hxy hmodeUV
      have hdata' := transitionData hxy' hmodeU'V'
      have hstateUU' : L.stateOf u = L.stateOf u' := hbu.trans hbu'.symm
      have hkeyUU' : L.key u = L.key u' := by
        calc
          L.key u = L.stKey (L.stateOf u) := (stateKeyEq u).symm
          _ = L.stKey (L.stateOf u') := congrArg L.stKey hstateUU'
          _ = L.key u' := stateKeyEq u'
      have hkeyVV' : L.key v = L.key v' := by
        calc
          L.key v = L.key u := hdata.1.symm
          _ = L.key u' := hkeyUU'
          _ = L.key v' := hdata'.1
      have hresUU' : ∀ r, r ∈ L.residual → u r = u' r := by
        have hresState := congrArg Prod.fst hstateUU'
        intro r hr
        exact congrFun hresState ⟨r, hr⟩
      have hresVV' : ∀ r, r ∈ L.residual → v r = v' r := by
        intro r hr
        calc
          v r = u r := (hdata.2.1 r hr).symm
          _ = u' r := hresUU' r hr
          _ = v' r := hdata'.2.1 r hr
      have hmergedUU' : ∀ i, L.mergedCount u i = L.mergedCount u' i := by
        have hcode := congrArg (fun s : State6 L => s.2.2.2.1) hstateUU'
        intro i
        have hval := congrArg Fin.val (congrFun hcode i)
        simpa [ChunkLayout6.stateOf, Nat.min_eq_left (hmergedBound u i),
          Nat.min_eq_left (hmergedBound u' i)] using hval
      have hmergedVV' : ∀ i, L.mergedCount v i = L.mergedCount v' i := by
        intro i
        calc
          L.mergedCount v i = L.mergedCount u i := (hdata.2.2.1 i).symm
          _ = L.mergedCount u' i := hmergedUU' i
          _ = L.mergedCount v' i := hdata'.2.2.1 i
      have targetSeverity {x y : CubeVertex n}
          (hmode : modeOf6 J (L.severity x) ≠ modeOf6 J (L.severity y))
          (hcase : (L.severity x = J ∧ L.severity y = J + 1) ∨
            (L.severity x = J + 1 ∧ L.severity y = J)) :
          L.severity y = if L.severity x ≤ J then J + 1 else J := by
        by_cases hxLow : L.severity x ≤ J
        · have hyHigh : ¬ L.severity y ≤ J := by
            intro hyLow
            apply hmode
            simp [modeOf6, hxLow, hyLow]
          rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> simp [hxLow] <;> omega
        · have hyLow : L.severity y ≤ J := by
            by_contra hyHigh
            apply hmode
            simp [modeOf6, hxLow, hyHigh]
          rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> simp [hxLow] <;> omega
      have hsevV : L.severity v = if L.severity u ≤ J then J + 1 else J :=
        targetSeverity hmodeUV hdata.2.2.2
      have hsevV' : L.severity v' = if L.severity u' ≤ J then J + 1 else J :=
        targetSeverity hmodeU'V' hdata'.2.2.2
      have hsevUU' : L.severity u = L.severity u' := by
        calc
          L.severity u = L.stSeverity (L.stateOf u) := (stateSeverityEq u).symm
          _ = L.stSeverity (L.stateOf u') := congrArg L.stSeverity hstateUU'
          _ = L.severity u' := stateSeverityEq u'
      have hsevVV' : L.severity v = L.severity v' := by
        rw [hsevV, hsevV', hsevUU']
      have hfineFn :
          (fun i : Fin L.m => (⟨min (L.mergedCount v i) n, by omega⟩ : Fin (n + 1))) =
            (fun i : Fin L.m => (⟨min (L.mergedCount v' i) n, by omega⟩ : Fin (n + 1))) := by
        funext i
        apply Fin.ext
        simp only [Nat.min_eq_left (hmergedBound v i), Nat.min_eq_left (hmergedBound v' i)]
        exact hmergedVV' i
      have hseverityFin : sevFin6 L.m (L.severity v) = sevFin6 L.m (L.severity v') := by
        apply Fin.ext
        simp [sevFin6, Nat.min_eq_left (hseverityBound v), Nat.min_eq_left (hseverityBound v')]
        exact hsevVV'
      have hstateTail :
          (L.coarseBin v, (L.key v).2,
            (fun i : Fin L.m => (⟨min (L.mergedCount v i) n, by omega⟩ : Fin (n + 1))),
            sevFin6 L.m (L.severity v)) =
          (L.coarseBin v', (L.key v').2,
            (fun i : Fin L.m => (⟨min (L.mergedCount v' i) n, by omega⟩ : Fin (n + 1))),
            sevFin6 L.m (L.severity v')) := by
        refine Prod.ext ?_ ?_
        · change L.coarseBin v = L.coarseBin v'
          exact congrArg Prod.fst hkeyVV'
        · refine Prod.ext ?_ ?_
          · change (L.key v).2 = (L.key v').2
            exact congrArg Prod.snd hkeyVV'
          · exact Prod.ext hfineFn hseverityFin
      have hstateVV' : L.stateOf v = L.stateOf v' := by
        change (fun r : {r // r ∈ L.residual} => v r.1,
            (L.coarseBin v, (L.key v).2,
              (fun i : Fin L.m => (⟨min (L.mergedCount v i) n, by omega⟩ : Fin (n + 1))),
              sevFin6 L.m (L.severity v))) =
          (fun r : {r // r ∈ L.residual} => v' r.1,
            (L.coarseBin v', (L.key v').2,
              (fun i : Fin L.m => (⟨min (L.mergedCount v' i) n, by omega⟩ : Fin (n + 1))),
              sevFin6 L.m (L.severity v')))
        refine Prod.ext ?_ ?_
        · funext r
          exact hresVV' r.1 r.2
        · exact hstateTail
      calc
        a = L.stateOf v := hav.symm
        _ = L.stateOf v' := hstateVV'
        _ = a' := hav'
    nonmatching_one := by
      intro b
      let S := (L.stNbr b).filter fun a =>
        primaryName6 (L.stKey a) ≠ primaryName6 (L.stKey b)
      change S.card ≤ 1
      rw [Finset.card_le_one_iff]
      intro a a' ha ha'
      have hmemA : a ∈ L.stNbr b ∧
          primaryName6 (L.stKey a) ≠ primaryName6 (L.stKey b) := by simpa [S] using ha
      have hmemA' : a' ∈ L.stNbr b ∧
          primaryName6 (L.stKey a') ≠ primaryName6 (L.stKey b) := by simpa [S] using ha'
      rcases hmemA with ⟨haNbr, hdiffA⟩
      rcases hmemA' with ⟨haNbr', hdiffA'⟩
      rcases (Finset.mem_filter.mp haNbr).2 with ⟨u, v, hu, hv, hbu, hav, hxy⟩
      rcases (Finset.mem_filter.mp haNbr').2 with ⟨u', v', hu', hv', hbu', hav', hxy'⟩
      have hdiffVA := hdiffA
      rw [← hav, ← hbu, stateKeyEq v, stateKeyEq u] at hdiffVA
      have hdiffVU := Ne.symm hdiffVA
      have hkeyFacts := keyDiffFacts (keyRelOfAdj hxy) hdiffVU
      have hdiffV'A := hdiffA'
      rw [← hav', ← hbu', stateKeyEq v', stateKeyEq u'] at hdiffV'A
      have hdiffV'U := Ne.symm hdiffV'A
      have hkeyFacts' := keyDiffFacts (keyRelOfAdj hxy') hdiffV'U
      have hkeyUU' : L.key u = L.key u' := by
        calc
          L.key u = L.stKey (L.stateOf u) := (stateKeyEq u).symm
          _ = L.stKey b := by rw [hbu]
          _ = L.stKey (L.stateOf u') := by rw [← hbu']
          _ = L.key u' := stateKeyEq u'
      have hbinVV' : (L.key v).1 = (L.key v').1 := by
        calc
          (L.key v).1 = (L.key u).1 := hkeyFacts.1.symm
          _ = (L.key u').1 := congrArg Prod.fst hkeyUU'
          _ = (L.key v').1 := hkeyFacts'.1
      have hflagUU' : (L.key u).2 = (L.key u').2 := congrArg Prod.snd hkeyUU'
      have hflagVV' : (L.key v).2 = (L.key v').2 := by
        have hvFlag := otherFlagOfNe (L.key u).2 (L.key v).2 hkeyFacts.2
        have hv'Flag := otherFlagOfNe (L.key u').2 (L.key v').2 hkeyFacts'.2
        rw [← hflagUU'] at hv'Flag
        exact hvFlag.trans hv'Flag.symm
      have hkeyVV' : L.key v = L.key v' := Prod.ext hbinVV' hflagVV'
      have hc : ∃ i c, c ∈ L.coarseChunks i ∧ u c ≠ v c := by
        by_contra h
        have hnon : ∀ i c, c ∈ L.coarseChunks i → u c = v c := by
          intro i c hc'
          by_contra hne
          exact h ⟨i, c, hc', hne⟩
        have hkey := g.flips.noncoarse_flip_key u v hxy hnon
        exact hkeyFacts.2 (congrArg Prod.snd hkey)
      have hc' : ∃ i c, c ∈ L.coarseChunks i ∧ u' c ≠ v' c := by
        by_contra h
        have hnon : ∀ i c, c ∈ L.coarseChunks i → u' c = v' c := by
          intro i c hc0
          by_contra hne
          exact h ⟨i, c, hc0, hne⟩
        have hkey := g.flips.noncoarse_flip_key u' v' hxy' hnon
        exact hkeyFacts'.2 (congrArg Prod.snd hkey)
      have hcoarse := coarseEdgeFields hxy hc
      have hcoarse' := coarseEdgeFields hxy' hc'
      have hstateUU' : L.stateOf u = L.stateOf u' := hbu.trans hbu'.symm
      have hresUU' : ∀ r, r ∈ L.residual → u r = u' r := by
        have hres := congrArg Prod.fst hstateUU'
        intro r hr
        exact congrFun hres ⟨r, hr⟩
      have hresVV' : ∀ r, r ∈ L.residual → v r = v' r := by
        intro r hr
        calc
          v r = u r := (hcoarse.1 r hr).symm
          _ = u' r := hresUU' r hr
          _ = v' r := hcoarse'.1 r hr
      have hmergedUU' : ∀ i, L.mergedCount u i = L.mergedCount u' i := by
        have hcode := congrArg (fun s : State6 L => s.2.2.2.1) hstateUU'
        intro i
        have hval := congrArg Fin.val (congrFun hcode i)
        simpa [ChunkLayout6.stateOf, Nat.min_eq_left (hmergedBound u i),
          Nat.min_eq_left (hmergedBound u' i)] using hval
      have hmergedVV' : ∀ i, L.mergedCount v i = L.mergedCount v' i := by
        intro i
        calc
          L.mergedCount v i = L.mergedCount u i := (hcoarse.2 i).symm
          _ = L.mergedCount u' i := hmergedUU' i
          _ = L.mergedCount v' i := hcoarse'.2 i
      have hsevUU' : L.severity u = L.severity u' := by
        have hcode := congrArg (fun s : State6 L => s.2.2.2.2) hstateUU'
        have hval := congrArg Fin.val hcode
        simpa [ChunkLayout6.stateOf, sevFin6, Nat.min_eq_left (hseverityBound u),
          Nat.min_eq_left (hseverityBound u')] using hval
      have hsevVV' : L.severity v = L.severity v' := by
        calc
          L.severity v = L.severity u := (severityEqOfCoarseFlip hxy hc).symm
          _ = L.severity u' := hsevUU'
          _ = L.severity v' := severityEqOfCoarseFlip hxy' hc'
      have hfineFn :
          (fun i : Fin L.m => (⟨min (L.mergedCount v i) n, by omega⟩ : Fin (n + 1))) =
            (fun i : Fin L.m => (⟨min (L.mergedCount v' i) n, by omega⟩ : Fin (n + 1))) := by
        funext i
        apply Fin.ext
        simp only [Fin.val_mk, Nat.min_eq_left (hmergedBound v i),
          Nat.min_eq_left (hmergedBound v' i)]
        exact hmergedVV' i
      have hseverityFin : sevFin6 L.m (L.severity v) = sevFin6 L.m (L.severity v') := by
        apply Fin.ext
        simp [sevFin6, Nat.min_eq_left (hseverityBound v),
          Nat.min_eq_left (hseverityBound v')]
        exact hsevVV'
      have hstateVV' : L.stateOf v = L.stateOf v' := by
        change (fun r : {r // r ∈ L.residual} => v r.1, L.coarseBin v, (L.key v).2,
            (fun i : Fin L.m => (⟨min (L.mergedCount v i) n, by omega⟩ : Fin (n + 1))),
            sevFin6 L.m (L.severity v)) =
          (fun r : {r // r ∈ L.residual} => v' r.1, L.coarseBin v', (L.key v').2,
            (fun i : Fin L.m => (⟨min (L.mergedCount v' i) n, by omega⟩ : Fin (n + 1))),
            sevFin6 L.m (L.severity v'))
        refine Prod.ext ?_ ?_
        · funext r
          exact hresVV' r.1 r.2
        · refine Prod.ext ?_ ?_
          · exact hbinVV'
          · refine Prod.ext ?_ ?_
            · exact hflagVV'
            · exact Prod.ext hfineFn hseverityFin
      calc
        a = L.stateOf v := hav.symm
        _ = L.stateOf v' := hstateVV'
        _ = a' := hav'
    low_target_covered := by
      intro b a hab hmode
      rcases (Finset.mem_filter.mp hab).2 with ⟨u, v, hu, hv, hbu, hav, hxy⟩
      subst b
      subst a
      have hTarget : L.stTarget (L.stateOf u) = (L.key u, L.sign u) := by
        simp [ChunkLayout6.stTarget, stateKeyEq u, stateSignEq u]
      rw [hTarget]
      have hlowU : L.severity u ≤ J := by
        rw [stateSeverityEq u] at hmode
        simpa [modeOf6] using hmode
      by_cases hvLow : L.severity v ≤ J
      · letI : DecidableEq (BinVector6 n) := fun x y => Classical.propDecidable (x = y)
        have hkeyNbr : L.key u ∈ keyNeighborhood6 binAdjacent6 (L.key v) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, keyRelSymm (keyRelOfAdj hxy)⟩
        have hlowObs : (L.key u, L.sign u) ∈
            lowObservations6 binAdjacent6 (L.key v) (L.sign v) (L.flippable v) := by
          by_cases hsign : L.sign u = L.sign v
          · apply Finset.mem_union.mpr
            left
            exact Finset.mem_image.mpr ⟨L.key u, hkeyNbr, Prod.ext rfl hsign.symm⟩
          · have hFine : ∃ i k, k ∈ L.fineChunks i ∧ u k ≠ v k := by
              by_contra hnone
              have hnon : ∀ i k, k ∈ L.fineChunks i → u k = v k := by
                intro i k hk
                by_contra hne
                exact hnone ⟨i, k, hk, hne⟩
              exact hsign ((g.flips.nonfine_flip_fine u v hxy hnon).1)
            rcases hFine with ⟨i, k, hk, hneq⟩
            obtain ⟨k', hneq', hsame⟩ := adjData hxy
            have hkk' : k = k' := by
              by_contra hne
              exact hneq (hsame k hne)
            subst k
            have hnonCoarse : ∀ j c, c ∈ L.coarseChunks j → u c = v c := by
              intro j c hc
              by_cases hck : c = k'
              · subst c
                exact False.elim ((Finset.disjoint_left.mp (L.chunks_disjoint.2.1 j i)) hc hk)
              · exact hsame c hck
            have hkeyEq : L.key u = L.key v :=
              g.flips.noncoarse_flip_key u v hxy hnonCoarse
            have hstep : L.fineCount u i + 1 = L.fineCount v i ∨
                L.fineCount v i + 1 = L.fineCount u i := by
              simpa [ChunkLayout6.fineCount] using
                filterCardStep (L.fineChunks i) k' hk hneq' hsame
            have hsignAt : L.sign u i ≠ L.sign v i := by
              intro heq
              apply hsign
              funext j
              by_cases hji : j = i
              · subst j
                exact heq
              · exact g.flips.fine_flip_sign u v i hxy ⟨k', hk, hneq'⟩ j hji
            have hflippable : i ∈ L.flippable v := by
              unfold ChunkLayout6.flippable
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact fineSignChangeFlippable i hstep hsignAt
            have hflipAt : L.sign u i = !(L.sign v i) := by
              cases huSign : L.sign u i <;> cases hvSign : L.sign v i
              · exact False.elim (hsignAt (by rw [huSign, hvSign]))
              · rfl
              · rfl
              · exact False.elim (hsignAt (by rw [huSign, hvSign]))
            have hsignUpdate : Function.update (L.sign v) i (!(L.sign v i)) = L.sign u := by
              funext j
              by_cases hji : j = i
              · subst j
                simp [Function.update, hflipAt]
              · simp [Function.update, hji]
                exact (g.flips.fine_flip_sign u v i hxy ⟨k', hk, hneq'⟩ j hji).symm
            apply Finset.mem_union.mpr
            right
            exact Finset.mem_image.mpr ⟨i, hflippable, Prod.ext hkeyEq.symm hsignUpdate⟩
        change (L.key u, L.sign u) ∈ (L.stType J (L.stateOf v)).obs
        simp only [ChunkLayout6.stType, Type6.obs, makeType6]
        rw [stateKeyEq v, stateSignEq v, stateFlippableEq v, stateSeverityEq v]
        simpa [hvLow] using hlowObs
      · have hmodeUV : modeOf6 J (L.severity u) ≠ modeOf6 J (L.severity v) := by
          simp [modeOf6, hlowU, hvLow]
        have hdata := transitionData hxy hmodeUV
        have hsevV : L.severity v = J + 1 := by
          rcases hdata.2.2.2 with ⟨huJ, hvJ⟩ | ⟨hvJ, huJ⟩ <;> omega
        have hsignUV : L.sign u = L.sign v := by
          funext i
          change decide (L.fineLength < 2 * L.fineCount u i) =
            decide (L.fineLength < 2 * L.fineCount v i)
          by_cases huMajor : L.fineLength < 2 * L.fineCount u i
          · have huMerged : L.fineLength < 2 * L.mergedCount u i :=
              (hsignMerged u i).mpr huMajor
            have hvMerged : L.fineLength < 2 * L.mergedCount v i := by
              simpa [hdata.2.2.1 i] using huMerged
            have hvMajor : L.fineLength < 2 * L.fineCount v i :=
              (hsignMerged v i).mp hvMerged
            simp [huMajor, hvMajor]
          · have hvMajor : ¬ L.fineLength < 2 * L.fineCount v i := by
              intro hvMajor
              have hvMerged : L.fineLength < 2 * L.mergedCount v i :=
                (hsignMerged v i).mpr hvMajor
              have huMerged : L.fineLength < 2 * L.mergedCount u i := by
                simpa [hdata.2.2.1 i] using hvMerged
              exact huMajor ((hsignMerged u i).mp huMerged)
            simp [huMajor, hvMajor]
        have hhighObs : (L.key u, L.sign u) ∈
            highObservations6 (L.key v) (L.sign v) (L.severity v) J := by
          simp [highObservations6, hsevV, hdata.1, hsignUV]
        change (L.key u, L.sign u) ∈ (L.stType J (L.stateOf v)).obs
        simp only [ChunkLayout6.stType, Type6.obs, makeType6]
        rw [stateKeyEq v, stateSignEq v, stateFlippableEq v, stateSeverityEq v]
        simpa [hvLow] using hhighObs
    high_target_required := by
      intro b a hab hmode
      rcases (Finset.mem_filter.mp hab).2 with ⟨u, v, hu, hv, hbu, hav, hxy⟩
      subst b
      subst a
      rw [stateSeverityEq u] at hmode
      let β := L.stType J (L.stateOf v)
      have hKeyβ : β.key = L.key v := stTypeKey v
      by_cases hc : ∃ i c, c ∈ L.coarseChunks i ∧ u c ≠ v c
      · have hsev := severityEqOfCoarseFlip hxy hc
        have hmodeV : modeOf6 J (L.severity v) = .high := by
          rw [← hsev]
          exact hmode
        have hβMode : β.mode = .high := stTypeHigh v hmodeV
        have hprim := keyPrimary (keyRelOfAdj hxy)
        have hName : primaryName6 (L.key u) = primaryName6 β.key ∨
            (β.mode = .high ∧ primaryName6 (L.key u) = otherPrimaryName6 β.key) := by
          rcases hprim with hp | hp
          · exact Or.inl (by rw [hKeyβ]; exact hp)
          · exact Or.inr ⟨hβMode, by rw [hKeyβ]; exact hp⟩
        exact reqForName (β := β) (primaryName6 (L.key u)) hName
      · have hnon : ∀ i c, c ∈ L.coarseChunks i → u c = v c := by
          intro i c hc'
          by_contra hne
          exact hc ⟨i, c, hc', hne⟩
        have hkey := g.flips.noncoarse_flip_key u v hxy hnon
        have hName : primaryName6 (L.key u) = primaryName6 β.key ∨
            (β.mode = .high ∧ primaryName6 (L.key u) = otherPrimaryName6 β.key) := by
          exact Or.inl (by rw [hKeyβ, hkey])
        exact reqForName (β := β) (primaryName6 (L.key u)) hName }

/-- L6.1e (code): one-hot fields give an injective code of role states in `Q_d`, `n/2 ≤ d ≤ 2n`, with even
neighbours of one odd state within distance `10` and residual distance preserved (06:233–258). -/
theorem L6_1e_code (α : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 100) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ g : ChunkGeometry6 n α, Nonempty (StateCode6 g.L) := by
  sorry

end

end S06
end HypercubeRamsey
