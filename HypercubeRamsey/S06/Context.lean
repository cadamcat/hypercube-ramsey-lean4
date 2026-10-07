import HypercubeRamsey.S06.Reduction
import HypercubeRamsey.S06.States

/-!
# The fixed inputs of the Section 6 construction at one dimension

`Ctx6 γ p₀ K n N E G M` bundles the hypotheses of Lemma 6.1 at dimension `n`, the Case 2 parent record of
L6.1a, the chunk geometry of L6.1b, the state facts and code of L6.1e, and the fixed fallback label and tag
(06:145–147).  Every later node is a statement about an arbitrary context of large enough dimension; the
constants `n₀ C₀` come before `∀ n N` (`ForLarge6`, 06:24–26).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- The Section 6 context at one dimension. -/
structure Ctx6 (γ p₀ K : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N) where
  par : ParentCase6 n N E G M γ Dstar₆
  g : ChunkGeometry6 n (α₆ p₀)
  facts : StateFacts6 g.L (J₆ g.L.m)
  code : StateCode6 g.L
  y₀ : Fin N
  i₀ : M.ι
  hBal : M.Balanced K
  hWidth : ∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)
  hCap : ∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar₆)
  hDeg : ∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y → 1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y

/-- A claim about Section 6 contexts holds for all contexts of large dimension and host size: the constants
`n₀, C₀` are chosen before `n, N, E, G, M` (06:24–26). -/
def ForLarge6 (γ p₀ K : ℝ)
    (P : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N), Ctx6 γ p₀ K n N E G M → Prop) :
    Prop :=
  ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N)
    (X : Ctx6 γ p₀ K n N E G M), LargeAt n₀ C₀ n N → P n N E G M X

theorem LargeAt.mono_max {n₀ n₁ : ℕ} {C₀ C₁ : ℝ} {n N : ℕ} (h : LargeAt (max n₀ n₁) (max C₀ C₁) n N) :
    LargeAt n₀ C₀ n N ∧ LargeAt n₁ C₁ n N := by
  obtain ⟨hn, hC, hN⟩ := h
  have hpow : (0 : ℝ) ≤ 2 ^ n := by positivity
  refine ⟨⟨le_trans (le_max_left _ _) hn, ?_, hN⟩, ⟨le_trans (le_max_right _ _) hn, ?_, hN⟩⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow) hC
  · exact le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow) hC

/-- Two `ForLarge6` claims hold together (take the larger constants). -/
theorem ForLarge6.and {γ p₀ K : ℝ} {P Q : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
    Ctx6 γ p₀ K n N E G M → Prop} (hP : ForLarge6 γ p₀ K P) (hQ : ForLarge6 γ p₀ K Q) :
    ForLarge6 γ p₀ K (fun n N E G M X => P n N E G M X ∧ Q n N E G M X) := by
  obtain ⟨n₀, C₀, h₀⟩ := hP
  obtain ⟨n₁, C₁, h₁⟩ := hQ
  refine ⟨max n₀ n₁, max C₀ C₁, fun n N E G M X hL => ?_⟩
  obtain ⟨hL₀, hL₁⟩ := LargeAt.mono_max hL
  exact ⟨h₀ n N E G M X hL₀, h₁ n N E G M X hL₁⟩

/-- Weakening inside `ForLarge6`. -/
theorem ForLarge6.mono {γ p₀ K : ℝ} {P Q : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
    Ctx6 γ p₀ K n N E G M → Prop} (hP : ForLarge6 γ p₀ K P)
    (hPQ : ∀ n N E G M X, P n N E G M X → Q n N E G M X) : ForLarge6 γ p₀ K Q := by
  obtain ⟨n₀, C₀, h₀⟩ := hP
  exact ⟨n₀, C₀, fun n N E G M X hL => hPQ n N E G M X (h₀ n N E G M X hL)⟩

namespace Ctx6

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-! ### Sizes (06:70–73, 06:125, 06:163) -/

def L : ChunkLayout6 n := X.g.L
def m : ℕ := X.g.L.m
def J : ℕ := J₆ X.g.L.m
def T : ℕ := T₆ X.g.L.m
def k : ℕ := k₆ n X.g.L.m
def ε (_X : Ctx6 γ p₀ K n N E G M) : ℝ := ε₆ p₀ n

/-- The tag type. -/
abbrev ι (_X : Ctx6 γ p₀ K n N E G M) : Type := M.ι

/-! ### Keys and types -/

abbrev Bin (_X : Ctx6 γ p₀ K n N E G M) : Type := BinVector6 n
abbrev Key (_X : Ctx6 γ p₀ K n N E G M) : Type := CoarseKey6 (BinVector6 n)
abbrev HKey : Type := HiddenKey6 (BinVector6 n) X.g.L.m
abbrev Ty : Type := Type6 (BinVector6 n) X.g.L.m
abbrev Name : Type := VarName6 (BinVector6 n) X.g.L.m
abbrev State : Type := State6 X.g.L

/-! Fixed instances, so that every statement uses the same decidability and finiteness instances. -/
instance instDecEqBin : DecidableEq X.Bin := inferInstanceAs (DecidableEq (BinVector6 n))
instance instFintypeBin : Fintype X.Bin := inferInstanceAs (Fintype (BinVector6 n))
instance instDecEqKey : DecidableEq X.Key := inferInstanceAs (DecidableEq (CoarseKey6 (BinVector6 n)))
instance instFintypeKey : Fintype X.Key := inferInstanceAs (Fintype (CoarseKey6 (BinVector6 n)))
instance instDecEqHKey : DecidableEq X.HKey := inferInstanceAs (DecidableEq (HiddenKey6 (BinVector6 n) X.g.L.m))
instance instFintypeHKey : Fintype X.HKey := inferInstanceAs (Fintype (HiddenKey6 (BinVector6 n) X.g.L.m))
instance instDecEqTy : DecidableEq X.Ty := inferInstanceAs (DecidableEq (Type6 (BinVector6 n) X.g.L.m))
instance instFintypeTy : Fintype X.Ty := inferInstanceAs (Fintype (Type6 (BinVector6 n) X.g.L.m))
instance instDecEqName : DecidableEq X.Name := inferInstanceAs (DecidableEq (VarName6 (BinVector6 n) X.g.L.m))
instance instDecEqState : DecidableEq X.State := inferInstanceAs (DecidableEq (State6 X.g.L))
instance instFintypeState : Fintype X.State := inferInstanceAs (Fintype (State6 X.g.L))
instance instFintypeι : Fintype X.ι := M.fin
instance instDecEqι : DecidableEq X.ι := Classical.decEq _

/-- `C(h)` (06:88–89). -/
def C (_X : Ctx6 γ p₀ K n N E G M) (h : CoarseKey6 (BinVector6 n)) : Finset (CoarseKey6 (BinVector6 n)) :=
  keyNeighborhood6 binAdjacent6 h

/-- The bins of a key list. -/
def binsOf (_X : Ctx6 γ p₀ K n N E G M) (S : Finset (CoarseKey6 (BinVector6 n))) : Finset (BinVector6 n) :=
  S.image Prod.fst

/-- The type of an even role (06:118–123). -/
def evenType (x : CubeVertex n) : X.Ty :=
  makeType6 binAdjacent6 (X.g.L.key x) (X.g.L.sign x) (X.g.L.flippable x) (X.g.L.severity x) X.J

/-- The type of an even state. -/
def stType (s : X.State) : X.Ty := X.g.L.stType X.J s

/-- The mode of a state. -/
def stMode (s : X.State) : Mode6 := modeOf6 X.J (X.g.L.stSeverity s)

/-- Types occurring at even roles. -/
def occTypes : Finset X.Ty := (Finset.univ.filter fun x : CubeVertex n => IsEvenRole x).image X.evenType

/-- Keys occurring at roles, and the keys whose Step 1 tests are required: `C(h)` of occurring keys. -/
def occKeys : Finset X.Key := Finset.univ.image X.g.L.key
def step1Keys : Finset X.Key := X.occKeys.biUnion X.C

/-- A neighbouring tuple has the same mode and the same named primary as the odd state (06:300). -/
def Matching (b : X.State) (β : X.Ty) : Prop :=
  β.mode = X.stMode b ∧ primaryName6 β.key = primaryName6 (X.g.L.stKey b)

end Ctx6

end

end S06
end HypercubeRamsey
