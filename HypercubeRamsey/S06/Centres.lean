import HypercubeRamsey.S06.Stages
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S06.Prob

/-!
# Centres, marking, eligibility and the height choices

L6.1i (06:525–570).  Given an admitted history, the centre experiment draws prospective positions, the
independent tuple arrays (one tuple per (ID, type), also at absent IDs), activations and tie priorities.  At each
odd state and each pair of consecutive levels a maximal family of disjoint failed ID sets (Step 3 descriptors that
fail) is chosen by a fixed rule and marked forbidden at the adjacent even sites; eligibility is what remains of the
prospective centres.  The long (or short) height rule of Lemma 3.8 then chooses one ID per even state, shared by
its roles.  An odd state is valid when its neighbourhood has legitimate choices on two consecutive levels with at
most `T` IDs, the position counts are at most `2λ`, and its actual descriptor passes the true-target gate and the
Step 3 data tests (06:599–603).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- A maximal family of pairwise disjoint members of `F`. -/
def IsMaxDisjoint6 {α : Type*} (F 𝓜 : Finset (Finset α)) : Prop :=
  𝓜 ⊆ F ∧ (∀ A ∈ 𝓜, ∀ B ∈ 𝓜, A ≠ B → Disjoint A B) ∧ ∀ A ∈ F, (∀ B ∈ 𝓜, Disjoint A B) → A ∈ 𝓜

/-- The fixed rule choosing a maximal disjoint family (06:536–537); it reads only `F`. -/
def maxDisjoint6 {α : Type*} (F : Finset (Finset α)) : Finset (Finset α) :=
  if h : ∃ 𝓜, IsMaxDisjoint6 F 𝓜 then Classical.choose h else ∅

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-! ### The height device (06:531–534) -/

/-- The height-device parameters: encoded dimension `d`, `D₀ = 10`, `r = ⌊ρn⌋`, `λ = n^{10}`, exponents from `α`. -/
def hp : HDParams where
  n := n
  d := X.code.d
  D := D₀₆
  r := ⌊ρ₆ * n⌋₊
  H := topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀))
  lam := (n : ℝ) ^ J₀₆
  b₀ := b₀₆ (α₆ p₀)
  b := b₆ (α₆ p₀)

/-- Centre IDs: location–level pairs in the encoded cube. -/
abbrev Loc : Type := X.hp.Loc

/-- Centre randomness: positions, tuple arrays, activations, ties. -/
abbrev Centre : Type := (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) × X.hp.Ties

/-- The raw centre law at a history (06:535, 06:141–144). -/
def centreLaw (H : X.Hist) : FinProb X.Centre :=
  ((X.hp.posLaw.prod (X.dataLaw X.Loc H)).prod X.hp.actLaw).prod X.hp.tieLaw

def pos (C : X.Centre) : X.Loc → Bool := C.1.1.1
def tup (C : X.Centre) : X.Data X.Loc := C.1.1.2
def act (C : X.Centre) : X.Loc → Bool := C.1.2
def ties (C : X.Centre) : X.hp.Ties := C.2

/-- The site of an even state. -/
def site (a : X.State) : CubeVertex X.code.d := X.code.enc a

/-- Height sites: the encoded even states (06:242). -/
def sites : X.hp.Sites := X.g.L.evenStates.image X.site

/-- Prospective centres at a site-level: present IDs on that level in the radius-`r` ball. -/
def prosp (P : X.Loc → Bool) (v : CubeVertex X.code.d) (l : Fin (X.hp.H + 1)) : Finset X.Loc :=
  Finset.univ.filter fun ℓ => P ℓ = true ∧ ℓ.2 = l ∧ _root_.hammingDist ℓ.1 v ≤ X.hp.r

/-- A pair of consecutive levels. -/
def levelPair (j : Fin X.hp.H) : Finset (Fin (X.hp.H + 1)) := {j.castSucc, j.succ}

/-- Permitted IDs of a neighbouring even state at a level pair. -/
def permAt (P : X.Loc → Bool) (b : X.State) (j : Fin X.hp.H) : X.g.L.stNbr b → Finset X.Loc :=
  fun a => (X.levelPair j).biUnion (X.prosp P (X.site a.1))

/-! ### Marking and eligibility (06:535–551) -/

/-- The ID sets of the failing Step 3 descriptors at an odd state and level pair. -/
def failedSets (H : X.Hist) (C : X.Centre) (b : X.State) (j : Fin X.hp.H) : Finset (Finset X.Loc) :=
  ((X.descsIn b (X.permAt (X.pos C) b j)).filter fun D => X.S3Fail H b D (X.tup C)).image
    fun D => D.image Prod.fst

/-- Marked IDs at a site-level: the unions of the maximal disjoint families of the adjacent odd states. -/
def marked (H : X.Hist) (C : X.Centre) (v : CubeVertex X.code.d) (l : Fin (X.hp.H + 1)) : Finset X.Loc :=
  X.g.L.oddStates.biUnion fun b =>
    if v ∈ (X.g.L.stNbr b).image X.site then
      (Finset.univ.filter fun j : Fin X.hp.H => l ∈ X.levelPair j).biUnion fun j =>
        (maxDisjoint6 (X.failedSets H C b j)).biUnion id
    else ∅

/-- Eligibility: prospective centres minus marks (it reads no activation, alarm or selection adjustment). -/
def elig (H : X.Hist) (C : X.Centre) : X.hp.EligMap := fun v l => X.prosp (X.pos C) v l \ X.marked H C v l

/-! ### Height choices and actual descriptors (06:555–570) -/

/-- The long and short consultation radii (06:531, 06:640–643). -/
def Rlong : ℕ := X.hp.Rlong
def Rshort : ℕ := X.hp.Rshort X.m

/-- The ID chosen at an even state with consultation radius `R`. -/
def choice (H : X.Hist) (C : X.Centre) (R : ℕ) (a : X.State) : Option X.Loc :=
  X.hp.selectionAt X.sites (X.pos C) (X.act C) (X.elig H C) (X.ties C) R (X.site a)

def defaultLoc : X.Loc := (fun _ => false, 0)

/-- The actual descriptor of an odd state: the (ID, type) pairs chosen by its neighbouring even states. -/
def actDesc (H : X.Hist) (C : X.Centre) (R : ℕ) (b : X.State) : Finset (X.Loc × X.Ty) :=
  Finset.univ.image fun a : X.g.L.stNbr b => ((X.choice H C R a.1).getD X.defaultLoc, X.stType a.1)

/-- Validity of an odd state under the rule of radius `R` (06:599–603). -/
def OddValid (H : X.Hist) (C : X.Centre) (R : ℕ) (b : X.State) : Prop :=
  (∀ a ∈ X.g.L.stNbr b, (X.choice H C R a).isSome) ∧
    (∀ a ∈ X.g.L.stNbr b, ∀ l, ((X.prosp (X.pos C) (X.site a) l).card : ℝ) ≤ 2 * X.hp.lam) ∧
      (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr b, ∀ ℓ, X.choice H C R a = some ℓ → ℓ.2 ∈ X.levelPair j) ∧
        ((X.actDesc H C R b).image Prod.fst).card ≤ X.T ∧
          X.S3TrueGate H b (X.actDesc H C R b) ∧ X.S3Tests H b (X.actDesc H C R b) (X.tup C)

/-! ### Geometry success (06:540–559) -/

/-- Every site-level ball has between `λ/2` and `2λ` prospective centres. -/
def CountsOK (C : X.Centre) : Prop :=
  ∀ v ∈ X.sites, ∀ l, X.hp.lam / 2 ≤ ((X.prosp (X.pos C) v l).card : ℝ) ∧
    ((X.prosp (X.pos C) v l).card : ℝ) ≤ 2 * X.hp.lam

/-- Every maximal family has fewer than `n` members. -/
def MarksOK (H : X.Hist) (C : X.Centre) : Prop :=
  ∀ b ∈ X.g.L.oddStates, ∀ j, (maxDisjoint6 (X.failedSets H C b j)).card < n

/-- Legal eligibility (prospective, on level, in the ball, at least `λ/3`) at every site and level. -/
def EligOK (H : X.Hist) (C : X.Centre) : Prop := X.hp.Legal (X.pos C) (X.elig H C) X.sites

/-- The global height properties of Lemma 3.8 for the long rule. -/
def HeightsOK (H : X.Hist) (C : X.Centre) : Prop :=
  X.hp.GoodHeights X.sites (X.pos C) (X.act C) (X.elig H C)

def GeoGood (H : X.Hist) (C : X.Centre) : Prop :=
  X.CountsOK C ∧ X.MarksOK H C ∧ X.EligOK H C ∧ X.HeightsOK H C

/-- Every actual odd role's state is valid under the long rule. -/
def AllOddValid (H : X.Hist) (C : X.Centre) : Prop :=
  ∀ u : CubeVertex n, ¬ IsEvenRole u → X.OddValid H C X.Rlong (X.g.L.stateOf u)

/-- L6.1i predicates. -/
def CountsBound : Prop := ∀ H, (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) ≤ Real.exp (-(n : ℝ))

def MarksBound : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → (X.centreLaw H).pr (fun C => X.CountsOK C ∧ ¬ X.MarksOK H C) ≤ Real.exp (-(n : ℝ))

def EligDet : Prop := ∀ H C, X.CountsOK C → X.MarksOK H C → X.EligOK H C

def HeightsBound : Prop :=
  ∀ H, (X.centreLaw H).pr (fun C => X.EligOK H C ∧ ¬ X.HeightsOK H C) ≤ Real.exp (-(n : ℝ))

def ValidDet : Prop := ∀ H C, X.histLaw.w H ≠ 0 → X.GeoGood H C → X.AllOddValid H C

/-- The centre stage succeeds with probability `≥ 1 − 1/100` at every admitted history. -/
def CentreFacts : Prop :=
  X.CountsBound ∧ X.MarksBound ∧ X.EligDet ∧ X.HeightsBound ∧ X.ValidDet ∧
    ∀ H, X.histLaw.w H ≠ 0 → (X.centreLaw H).pr (fun C => ¬ (X.GeoGood H C ∧ X.AllOddValid H C)) ≤ 1 / 100

end Ctx6

/-- L6.1i (counts): position counts in `[λ/2, 2λ]` (L3.8j, `height_position_counts`). -/
theorem L6_1i_counts (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.CountsBound := by
  sorry

/-- L6.1i (marks, 06:540–551): `n` disjoint failed ID sets read independent arrays; `D_n^n e^{−c₂kn} ≤
e^{−c₂kn/2}` with `log D_n < c₂k/2`; union over states and level pairs `exp(O(n))`. -/
theorem L6_1i_marks (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.DescCount → X.MarksBound := by
  sorry

/-- L6.1i (eligibility, 06:553–555): fewer than `n` marked sets per star and level pair remove `O(n²T)` centres
from a site-level, leaving at least `λ/3`. -/
theorem L6_1i_elig (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EligDet := by
  sorry

/-- L6.1i (heights, 06:555–557): the global height bound of Lemma 3.8 (`height_selection_global`, auxiliary
randomness = the tuple arrays). -/
theorem L6_1i_heights (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HeightsBound := by
  sorry

/-- L6.1i (validity, 06:557–559): good heights give choices on two consecutive levels, the crowd bound gives at
most `2n^b ≤ T` IDs, and a failed actual descriptor would be disjoint from the marked union. -/
theorem L6_1i_valid (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.ValidDet := by
  sorry

/-- Union bound for the centre stage. -/
theorem centre_union6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (hn : 300 ≤ n) (hC : X.CountsBound) (hM : X.MarksBound) (hE : X.EligDet)
    (hH : X.HeightsBound) (hV : X.ValidDet) :
    ∀ H, X.histLaw.w H ≠ 0 →
      (X.centreLaw H).pr (fun C => ¬ (X.GeoGood H C ∧ X.AllOddValid H C)) ≤ 1 / 100 := by
  intro H hHist
  have hexp : Real.exp (-(n : ℝ)) ≤ 1 / 301 := by
    have h1 : (n : ℝ) + 1 ≤ Real.exp n := Real.add_one_le_exp _
    have h2 : (300 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : Real.exp (-(n : ℝ)) * Real.exp n = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
    nlinarith
  have hsub := pr_mono6 (X.centreLaw H) (A := fun C => ¬ (X.GeoGood H C ∧ X.AllOddValid H C))
    (B := fun C => ¬ X.CountsOK C ∨ ((X.CountsOK C ∧ ¬ X.MarksOK H C) ∨ (X.EligOK H C ∧ ¬ X.HeightsOK H C)))
    (by
      intro C hbad
      by_contra hcon
      push_neg at hcon
      obtain ⟨hc, hm, hh⟩ := hcon
      have hm' := hm hc
      have he := hE H C hc hm'
      have hgeo : X.GeoGood H C := ⟨hc, hm', he, hh he⟩
      exact hbad ⟨hgeo, hV H C hHist hgeo⟩)
  have h1 := pr_or_le6 (X.centreLaw H) (fun C => ¬ X.CountsOK C)
    (fun C => (X.CountsOK C ∧ ¬ X.MarksOK H C) ∨ (X.EligOK H C ∧ ¬ X.HeightsOK H C))
  have h2 := pr_or_le6 (X.centreLaw H) (fun C => X.CountsOK C ∧ ¬ X.MarksOK H C)
    (fun C => X.EligOK H C ∧ ¬ X.HeightsOK H C)
  have hc := hC H
  have hm := hM H hHist
  have hh := hH H
  linarith

/-- L6.1i assembled from its nodes. -/
theorem centreFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StepFacts → X.StageFacts → X.CentreFacts := by
  have h := (L6_1i_counts γ p₀ K hadm).and <| (L6_1i_marks γ p₀ K hadm).and <|
    (L6_1i_elig γ p₀ K hadm).and <| (L6_1i_heights γ p₀ K hadm).and (L6_1i_valid γ p₀ K hadm)
  obtain ⟨n₀, C₀, h₀⟩ := h
  refine ⟨max n₀ 300, C₀, fun n N E G M X hL hS hT => ?_⟩
  have hL' : LargeAt n₀ C₀ n N := ⟨le_trans (le_max_left _ _) hL.1, hL.2.1, hL.2.2⟩
  obtain ⟨hC, hM, hE, hH, hV⟩ := h₀ n N E G M X hL'
  have hsupp := hT.2.2.2
  have hcount : X.DescCount := hS.2.2.2.2.2.2.2.1
  exact ⟨hC, hM hsupp hcount, hE, hH, hV hsupp,
    centre_union6 X (le_trans (le_max_right _ _) hL.1) hC (hM hsupp hcount) hE hH (hV hsupp)⟩

end

end S06
end HypercubeRamsey
