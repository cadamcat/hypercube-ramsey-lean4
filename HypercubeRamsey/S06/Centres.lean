import HypercubeRamsey.S06.Stages
import HypercubeRamsey.S03.Height.Selection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

set_option maxHeartbeats 1000000

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
  have hExp := height_exponents6_admissible p₀ hadm.2.2.1
  refine ⟨10 ^ 13, 1, fun n N E G M X hL => ?_⟩
  have hn : 10 ^ 13 ≤ n := hL.1
  have hn300 : 300 ≤ n := by omega
  have hnreal : (10 ^ 13 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnlarge : (1200 : ℝ) ≤ n := by linarith
  have hα : 0 < α₆ p₀ := hExp.1
  have hαsmall : α₆ p₀ ≤ 1 / 10 ^ 12 := hExp.2.2.1
  have hσle : σ₆ (α₆ p₀) ≤ 1 := by
    dsimp [σ₆]
    nlinarith [hαsmall]
  have hζbounds : 0 < ζ₆ (α₆ p₀) ∧ ζ₆ (α₆ p₀) < 1 := by
    constructor <;> dsimp [ζ₆] <;> nlinarith [hα, hαsmall]
  have hpowσ : (n : ℝ) ^ σ₆ (α₆ p₀) ≤ n := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1 hσle
    simpa only [Real.rpow_one] using h
  have hpowζ : (n : ℝ) ^ (1 - ζ₆ (α₆ p₀)) ≤ n := by
    have hExpLE : 1 - ζ₆ (α₆ p₀) ≤ 1 := by linarith [hζbounds.1]
    have h := Real.rpow_le_rpow_of_exponent_le hn1 hExpLE
    simpa only [Real.rpow_one] using h
  have hR : X.hp.r = ⌊(1 / 100 : ℝ) * n⌋₊ := by rfl
  have hr11 : 11 ≤ X.hp.r := by
    rw [hR]
    have hfloor := Nat.lt_floor_add_one ((1 / 100 : ℝ) * n)
    have harg : (12 : ℝ) ≤ (1 / 100 : ℝ) * n := by nlinarith
    have hfloorR : (11 : ℝ) < (⌊(1 / 100 : ℝ) * n⌋₊ : ℝ) := by nlinarith
    exact_mod_cast hfloorR.le
  have hdNat : n ≤ 2 * X.hp.d := by
    have hd : (1 / 2 : ℝ) * n ≤ X.hp.d := by
      simpa [Ctx6.hp, cd₆] using X.code.d_lower
    exact_mod_cast (show (n : ℝ) ≤ 2 * (X.hp.d : ℝ) by nlinarith)
  have hfactorNat : n ≤ 3 * (X.hp.d + 1 - 11) := by omega
  have hfactorReal : (n : ℝ) / 3 ≤ ((X.hp.d + 1 - 11 : ℕ) : ℝ) := by
    have hcast : (n : ℝ) ≤ 3 * ((X.hp.d + 1 - 11 : ℕ) : ℝ) := by exact_mod_cast hfactorNat
    nlinarith
  have hlargePower : (n : ℝ) ^ 10 ≤ ((n : ℝ) / 3) ^ 11 / (Nat.factorial 11 : ℝ) := by
    have hden : ((3 : ℝ) ^ 11) * (Nat.factorial 11 : ℝ) ≤ 10 ^ 13 := by norm_num [Nat.factorial]
    have hmul := mul_le_mul_of_nonneg_right hden (pow_nonneg (show (0 : ℝ) ≤ n by positivity) 10)
    have hnMul := mul_le_mul_of_nonneg_right hnreal (pow_nonneg (show (0 : ℝ) ≤ n by positivity) 10)
    have hpowId : ((n : ℝ) / 3) ^ 11 = (n : ℝ) ^ 11 / (3 : ℝ) ^ 11 := by rw [div_pow]
    rw [hpowId]
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)]
    calc
      (n : ℝ) ^ 10 * (Nat.factorial 11 : ℝ) * (3 : ℝ) ^ 11 ≤
          (n : ℝ) ^ 10 * 10 ^ 13 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ ≤ (n : ℝ) ^ 10 * n := mul_le_mul_of_nonneg_left hnreal (by positivity)
      _ = (n : ℝ) ^ 11 := by ring
  have hpowChoose :
      (((X.hp.d + 1 - 11 : ℕ) : ℝ) ^ 11) / (Nat.factorial 11 : ℝ) ≤
        (Nat.choose X.hp.d 11 : ℝ) := Nat.pow_le_choose 11 X.hp.d
  have hchooseLower : (n : ℝ) ^ 10 ≤ (Nat.choose X.hp.d 11 : ℝ) := by
    calc
      (n : ℝ) ^ 10 ≤ ((n : ℝ) / 3) ^ 11 / (Nat.factorial 11 : ℝ) := hlargePower
      _ ≤ (((X.hp.d + 1 - 11 : ℕ) : ℝ) ^ 11) / (Nat.factorial 11 : ℝ) := by
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfactorReal 11) (by positivity)
      _ ≤ (Nat.choose X.hp.d 11 : ℝ) := hpowChoose
  have hChooseMem : 11 ∈ Finset.range (X.hp.r + 1) := by simp [Finset.mem_range, hr11]
  have hChooseVNat : Nat.choose X.hp.d 11 ≤ X.hp.V := by
    change Nat.choose X.hp.d 11 ≤ ∑ i ∈ Finset.range (X.hp.r + 1), Nat.choose X.hp.d i
    exact Finset.single_le_sum (fun i hi => Nat.zero_le _) hChooseMem
  have hVlower : (n : ℝ) ^ 10 ≤ (X.hp.V : ℝ) := by
    exact hchooseLower.trans (by exact_mod_cast hChooseVNat)
  have hVpos : 0 < (X.hp.V : ℝ) := by
    have hnPowPos : 0 < (n : ℝ) ^ 10 := by positivity
    linarith
  have hlamleV : X.hp.lam ≤ (X.hp.V : ℝ) := by
    change (n : ℝ) ^ J₀₆ ≤ (X.hp.V : ℝ)
    rw [show J₀₆ = ((10 : ℕ) : ℝ) by norm_num [J₀₆], Real.rpow_natCast]
    exact hVlower
  have hprob : X.hp.lam / (X.hp.V : ℝ) ≤ 1 := (div_le_one hVpos).2 hlamleV
  have hPrProdFst {A B : Type} [Fintype A] [Fintype B]
      (P : FinProb A) (Q : FinProb B) (ev : A → Prop) :
      (P.prod Q).pr (fun z => ev z.1) = P.pr ev := by
    unfold FinProb.pr FinProb.prod
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, if ev a then P.w a * Q.w b else 0) =
          ∑ a, if ev a then P.w a * ∑ b, Q.w b else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : ev a <;> simp [h, Finset.mul_sum]
      _ = ∑ a, if ev a then P.w a else 0 := by simp [Q.sum_eq_one]
  let badPosition : (X.Loc → Bool) → Prop := fun P =>
    ∃ v ∈ X.sites, ∃ j : Fin (X.hp.H + 1),
      let count := (Finset.univ.filter fun u : CubeVertex X.hp.d =>
        P (u, j) = true ∧ _root_.hammingDist u v ≤ X.hp.r).card
      ((count : ℝ) < X.hp.lam / 2 ∨ 2 * X.hp.lam < (count : ℝ))
  have hCountCard (P : X.Loc → Bool) (v : CubeVertex X.hp.d) (j : Fin (X.hp.H + 1)) :
      (X.prosp P v j).card =
        (Finset.univ.filter fun u : CubeVertex X.hp.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ X.hp.r).card := by
    let f := fun u : CubeVertex X.hp.d => (u, j)
    have hset : X.prosp P v j =
        (Finset.univ.filter fun u : CubeVertex X.hp.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ X.hp.r).image f := by
      ext x
      constructor
      · intro hx
        unfold Ctx6.prosp at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨hP, hj, hdist⟩
        apply Finset.mem_image.mpr
        have hu : x.1 ∈ Finset.univ.filter fun u : CubeVertex X.hp.d =>
            P (u, j) = true ∧ _root_.hammingDist u v ≤ X.hp.r := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hxEq : x = (x.1, j) := Prod.ext rfl hj
          rw [hxEq] at hP
          exact ⟨hP, hdist⟩
        exact ⟨x.1, hu, Prod.ext rfl hj.symm⟩
      · intro hx
        change x ∈ (Finset.univ.filter fun u : CubeVertex X.hp.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ X.hp.r).image f at hx
        rcases Finset.mem_image.mp hx with ⟨u, hu, heq⟩
        cases heq
        rcases Finset.mem_filter.mp hu with ⟨_, hP, hdist⟩
        unfold Ctx6.prosp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hP, rfl, hdist⟩
    rw [hset]
    exact Finset.card_image_of_injective _ (by
      intro u u' h
      exact congrArg Prod.fst h)
  have hCountsEvent (C : X.Centre) :
      (¬ X.CountsOK C) ↔ badPosition (X.pos C) := by
    classical
    constructor
    · intro hbad
      unfold Ctx6.CountsOK at hbad
      push_neg at hbad
      rcases hbad with ⟨v, hv, j, hbad⟩
      refine ⟨v, hv, j, ?_⟩
      dsimp [badPosition]
      have hbad' :
          ((X.prosp (X.pos C) v j).card : ℝ) < X.hp.lam / 2 ∨
            2 * X.hp.lam < ((X.prosp (X.pos C) v j).card : ℝ) := by
        by_cases hlow : ((X.prosp (X.pos C) v j).card : ℝ) < X.hp.lam / 2
        · exact Or.inl hlow
        · exact Or.inr (hbad (le_of_not_gt hlow))
      simpa [hCountCard] using hbad'
    · rintro ⟨v, hv, j, hbad⟩
      unfold Ctx6.CountsOK
      intro hgood
      have hpair := hgood v hv j
      dsimp [badPosition] at hbad
      rcases hbad with hlow | hhigh
      · have hlow' : ((X.prosp (X.pos C) v j).card : ℝ) < X.hp.lam / 2 := by
          simpa [hCountCard] using hlow
        linarith
      · have hhigh' : 2 * X.hp.lam < ((X.prosp (X.pos C) v j).card : ℝ) := by
          simpa [hCountCard] using hhigh
        linarith
  intro H
  let Pbase : FinProb (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) :=
    ((X.hp.posLaw.prod (X.dataLaw X.Loc H)).prod X.hp.actLaw)
  let badAux : (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) → Prop :=
    fun z => badPosition z.1.1
  have hEventFun :
      (fun C : X.Centre => ¬ X.CountsOK C) =
        (fun C => badAux ((X.pos C, X.tup C), X.act C)) := by
    funext C
    change (¬ X.CountsOK C) = badPosition (X.pos C)
    exact propext (hCountsEvent C)
  have hCentreProj :
      (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) = Pbase.pr badAux := by
    rw [hEventFun]
    simpa [Pbase, badAux, Ctx6.centreLaw, Ctx6.pos, Ctx6.tup, Ctx6.act] using
      (hPrProdFst Pbase X.hp.tieLaw badAux)
  have hBaseProj : Pbase.pr badAux = X.hp.posLaw.pr badPosition := by
    calc
      Pbase.pr badAux =
          (X.hp.posLaw.prod (X.dataLaw X.Loc H)).pr (fun z => badPosition z.1) := by
        simpa [Pbase, badAux] using
          (hPrProdFst (X.hp.posLaw.prod (X.dataLaw X.Loc H)) X.hp.actLaw
            (fun z => badPosition z.1))
      _ = X.hp.posLaw.pr badPosition :=
        hPrProdFst X.hp.posLaw (X.dataLaw X.Loc H) badPosition
  have hlamPos : 0 < X.hp.lam := by
    change 0 < (n : ℝ) ^ J₀₆
    exact Real.rpow_pos_of_pos hnpos _
  have hrReal : (X.hp.r : ℝ) ≤ X.hp.d := by
    rw [hR]
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ (1 / 100 : ℝ) * n by positivity)
    have hdReal : (1 / 2 : ℝ) * n ≤ X.hp.d := by
      simpa [Ctx6.hp, cd₆] using X.code.d_lower
    nlinarith
  have hrNat : X.hp.r ≤ X.hp.d := by exact_mod_cast hrReal
  have hVnat : 0 < X.hp.V := by exact_mod_cast hVpos
  have hPositionTail :
      X.hp.posLaw.pr badPosition ≤
        2 * (X.sites.card : ℝ) * ((X.hp.H + 1 : ℕ) : ℝ) * Real.exp (-X.hp.lam / 12) := by
    have h := height_position_counts X.hp X.sites hlamPos hVnat hrNat hprob
    simpa [badPosition] using h
  have hCountTail :
      (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) ≤
        2 * (X.sites.card : ℝ) * ((X.hp.H + 1 : ℕ) : ℝ) * Real.exp (-X.hp.lam / 12) := by
    rw [hCentreProj, hBaseProj]
    exact hPositionTail
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M₀ : ℕ := max 2 ⌈(n : ℝ) ^ σ₆ (α₆ p₀)⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ₆ (α₆ p₀))⌉₊
  have hLog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hLogLe : Real.log (n : ℝ) ≤ n := Real.log_le_self hnpos.le
  have hLogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hLogSqCast : (Real.log (n : ℝ)) ^ 2 ≤ ((n ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hLogSq
  have hR₀lower : 1 ≤ R₀ := by dsimp [R₀]; exact le_max_left _ _
  have hR₀upper : R₀ ≤ n ^ 2 := by
    dsimp [R₀]
    apply max_le
    · exact Nat.one_le_pow 2 n (by omega)
    · exact Nat.ceil_le.mpr hLogSqCast
  have hM₀lower : 2 ≤ M₀ := by dsimp [M₀]; exact le_max_left _ _
  have hM₀upper : M₀ ≤ n := by
    dsimp [M₀]
    apply max_le
    · omega
    · exact Nat.ceil_le.mpr hpowσ
  have hTargetUpper : target ≤ n := Nat.ceil_le.mpr hpowζ
  have hTargetPow : target ≤ 2 ^ target := by
    have h := Nat.choose_succ_le_two_pow target 1
    have h' : target + 1 ≤ 2 ^ target := by simpa using h
    omega
  have hTargetWitness : target ≤ M₀ ^ target * R₀ := by
    calc
      target ≤ 2 ^ target := hTargetPow
      _ ≤ M₀ ^ target := pow_le_pow_left' hM₀lower target
      _ ≤ M₀ ^ target * R₀ := by
        have h := Nat.mul_le_mul_left (M₀ ^ target) hR₀lower
        simpa using h
  have hScaleExists : ∃ i : ℕ, target ≤ M₀ ^ i * R₀ := ⟨target, hTargetWitness⟩
  have hFind : Nat.find hScaleExists ≤ target := Nat.find_min' hScaleExists hTargetWitness
  have hTopScale : topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ M₀ ^ target * R₀ := by
    unfold topScale
    change M₀ ^ Nat.find hScaleExists * R₀ ≤ M₀ ^ target * R₀
    exact Nat.mul_le_mul_right R₀ (pow_le_pow_right' (by omega : 1 ≤ M₀) hFind)
  have hMpowN : M₀ ^ target ≤ n ^ n := by
    calc
      M₀ ^ target ≤ n ^ target := pow_le_pow_left' hM₀upper target
      _ ≤ n ^ n := pow_le_pow_right' (by omega : 1 ≤ n) hTargetUpper
  have hnTwoPow : n ≤ 2 ^ n := by
    have h := Nat.choose_succ_le_two_pow n 1
    have h' : n + 1 ≤ 2 ^ n := by simpa using h
    omega
  have hnPowTwo : n ^ n ≤ 2 ^ (n * n) := by
    calc
      n ^ n ≤ (2 ^ n) ^ n := pow_le_pow_left' hnTwoPow n
      _ = 2 ^ (n * n) := (pow_mul 2 n n).symm
  have hnSqTwo : n ^ 2 ≤ 2 ^ (2 * n) := by
    calc
      n ^ 2 ≤ (2 ^ n) ^ 2 := pow_le_pow_left' hnTwoPow 2
      _ = 2 ^ (n * 2) := (pow_mul 2 n 2).symm
      _ = 2 ^ (2 * n) := by rw [Nat.mul_comm n 2]
  have hTopNat : topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ n ^ n * n ^ 2 := by
    calc
      topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ M₀ ^ target * R₀ := hTopScale
      _ ≤ n ^ n * n ^ 2 := Nat.mul_le_mul hMpowN hR₀upper
  have hTopPower : X.hp.H ≤ 2 ^ (n ^ 2 + 2 * n) := by
    have hTopEq : X.hp.H = topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) := by rfl
    rw [hTopEq]
    calc
      topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) ≤ n ^ n * n ^ 2 := hTopNat
      _ ≤ 2 ^ (n * n) * 2 ^ (2 * n) := Nat.mul_le_mul hnPowTwo hnSqTwo
      _ = 2 ^ (n ^ 2 + 2 * n) := by
        rw [← pow_add]
        congr 1
        simp [pow_two]
  have hHplus : X.hp.H + 1 ≤ 2 ^ (n ^ 2 + 2 * n + 1) := by
    have hPowOne : 1 ≤ 2 ^ (n ^ 2 + 2 * n) := Nat.one_le_pow (n ^ 2 + 2 * n) 2 (by norm_num)
    calc
      X.hp.H + 1 ≤ 2 ^ (n ^ 2 + 2 * n) + 1 := Nat.add_le_add_right hTopPower 1
      _ ≤ 2 ^ (n ^ 2 + 2 * n) + 2 ^ (n ^ 2 + 2 * n) := Nat.add_le_add_left hPowOne _
      _ = 2 ^ (n ^ 2 + 2 * n + 1) := by rw [pow_succ]; omega
  have hdNatUpper : X.code.d ≤ 2 * n := by
    have hdReal : (X.code.d : ℝ) ≤ 2 * n := by simpa [Cd₆] using X.code.d_upper
    exact_mod_cast hdReal
  have hSitesCard : X.sites.card ≤ 2 ^ (2 * n) := by
    calc
      X.sites.card ≤ Fintype.card (CubeVertex X.code.d) := Finset.card_le_univ _
      _ = 2 ^ X.code.d := by simp
      _ ≤ 2 ^ (2 * n) := pow_le_pow_right' (by norm_num : 1 ≤ 2) hdNatUpper
  have hPrefNat : 2 * X.sites.card * (X.hp.H + 1) ≤ 2 ^ (n ^ 2 + 4 * n + 2) := by
    have hSiteMul : 2 * X.sites.card ≤ 2 * 2 ^ (2 * n) := Nat.mul_le_mul_left 2 hSitesCard
    calc
      2 * X.sites.card * (X.hp.H + 1) ≤
          (2 * 2 ^ (2 * n)) * 2 ^ (n ^ 2 + 2 * n + 1) := Nat.mul_le_mul hSiteMul hHplus
      _ = 2 ^ (n ^ 2 + 4 * n + 2) := by
        rw [show 2 * 2 ^ (2 * n) = 2 ^ (2 * n + 1) by rw [pow_succ]; omega,
          ← pow_add]
        congr 1
        ring
  have hPrefReal :
      2 * (X.sites.card : ℝ) * ((X.hp.H + 1 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (n ^ 2 + 4 * n + 2) := by exact_mod_cast hPrefNat
  have hTwoPowExp (q : ℕ) : (2 : ℝ) ^ q ≤ Real.exp (q : ℝ) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := pow_le_pow_left₀ (by norm_num) h2e q
      _ = Real.exp (q : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
  have hPrefExp :
      2 * (X.sites.card : ℝ) * ((X.hp.H + 1 : ℕ) : ℝ) ≤
        Real.exp ((n : ℝ) ^ 2 + 4 * n + 2) := by
    have h := hPrefReal.trans (hTwoPowExp (n ^ 2 + 4 * n + 2))
    have hArg : ((n ^ 2 + 4 * n + 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 + 4 * n + 2 := by
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rw [← hArg]
    exact h
  have hlamEq : X.hp.lam = (n : ℝ) ^ 10 := by
    change (n : ℝ) ^ J₀₆ = (n : ℝ) ^ 10
    rw [show J₀₆ = ((10 : ℕ) : ℝ) by norm_num [J₀₆], Real.rpow_natCast]
  have hn2real : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hn8 : (256 : ℝ) ≤ (n : ℝ) ^ 8 := by
    calc
      256 = (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (n : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hn2real 8
  have hpow10 : 256 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 10 := by
    have hmul := mul_le_mul_of_nonneg_right hn8 (sq_nonneg (n : ℝ))
    calc
      256 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (n : ℝ) ^ 2 := hmul
      _ = (n : ℝ) ^ 10 := by ring
  have hnSq : n ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have honeSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hBigNum : 12 * ((n : ℝ) ^ 2 + 5 * n + 2) ≤ (n : ℝ) ^ 10 := by
    calc
      12 * ((n : ℝ) ^ 2 + 5 * n + 2) ≤ 256 * (n : ℝ) ^ 2 := by nlinarith
      _ ≤ (n : ℝ) ^ 10 := hpow10
  have hBigDiv : (n : ℝ) ^ 2 + 5 * n + 2 ≤ (n : ℝ) ^ 10 / 12 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hBigNum]
  calc
    (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) ≤
        2 * (X.sites.card : ℝ) * ((X.hp.H + 1 : ℕ) : ℝ) * Real.exp (-X.hp.lam / 12) := hCountTail
    _ ≤ Real.exp ((n : ℝ) ^ 2 + 4 * n + 2) * Real.exp (-X.hp.lam / 12) :=
      mul_le_mul_of_nonneg_right hPrefExp (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) ^ 2 + 4 * n + 2 - X.hp.lam / 12) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by rw [hlamEq]; linarith [hBigDiv])

/-- L6.1i (marks, 06:540–551): `n` disjoint failed ID sets read independent arrays; `D_n^n e^{−c₂kn} ≤
e^{−c₂kn/2}` with `log D_n < c₂k/2`; union over states and level pairs `exp(O(n))`. -/
theorem L6_1i_marks (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.DescCount → X.MarksBound := by
  sorry

/-- L6.1i (eligibility, 06:553–555): fewer than `n` marked sets per star and level pair remove `O(n²T)` centres
from a site-level, leaving at least `λ/3`. -/
theorem L6_1i_elig (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EligDet := by
  refine ⟨300, 1, fun n N E G M X hL => ?_⟩
  intro H C hCounts hMarks
  have hExp := height_exponents6_admissible p₀ hadm.2.2.1
  have hα0 : 0 < α₆ p₀ := hExp.1
  have hα1 : α₆ p₀ ≤ 1 := hExp.2.2.1.trans (by norm_num)
  have hn300 : 300 ≤ n := hL.1
  have hn1 : (1 : ℝ) ≤ n := by
    have hn1Nat : (1 : ℕ) ≤ n := by omega
    exact_mod_cast hn1Nat
  have hpowα : (n : ℝ) ^ α₆ p₀ ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hα1
  have hmle : X.m ≤ n := by
    change X.g.L.m ≤ n
    rw [X.g.m_eq]
    exact Nat.ceil_le.mpr hpowα
  have hmpos : 0 < X.m := by
    change 0 < X.g.L.m
    rw [X.g.m_eq]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have hmge : 1 ≤ X.m := Nat.succ_le_iff.mpr hmpos
  have hmgeR : (1 : ℝ) ≤ (X.m : ℝ) := by exact_mod_cast hmge
  have hTpowR : (X.m : ℝ) ^ (1 / 1000 : ℝ) ≤ (X.m : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmgeR (by norm_num)
  have hTpow : (X.m : ℝ) ^ (1 / 1000 : ℝ) ≤ X.m := by
    simpa only [Real.rpow_one] using hTpowR
  have hTle : X.T ≤ X.m := by
    change T₆ X.g.L.m ≤ X.g.L.m
    unfold T₆
    exact Nat.ceil_le.mpr hTpow
  have hTn : X.T ≤ n := le_trans hTle hmle
  have hn200 : 200 ≤ n := by omega
  have hn200r : (200 : ℝ) ≤ n := by exact_mod_cast hn200
  have hn7 : (36 : ℝ) ≤ (n : ℝ) ^ 7 := by
    have hbase : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hpow : (2 : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hbase 7
    exact le_trans (by norm_num) hpow
  have h36 : (36 : ℝ) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 10 := by
    have hmul := mul_le_mul_of_nonneg_right hn7
      (pow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity) 3)
    nlinarith [hmul]
  have hRemoval : 6 * (n : ℝ) ^ 2 * (X.T : ℝ) ≤ (n : ℝ) ^ 10 / 6 := by
    have hTcast : (X.T : ℝ) ≤ n := by exact_mod_cast hTn
    have hsmall : 6 * (n : ℝ) ^ 2 * (X.T : ℝ) ≤ 6 * (n : ℝ) ^ 3 := by
      calc
        6 * (n : ℝ) ^ 2 * (X.T : ℝ) ≤ 6 * (n : ℝ) ^ 2 * n :=
          mul_le_mul_of_nonneg_left hTcast (by positivity)
        _ = 6 * (n : ℝ) ^ 3 := by ring
    nlinarith [hsmall, h36]
  have hmax_subset (F : Finset (Finset X.Loc)) : maxDisjoint6 F ⊆ F := by
    classical
    unfold maxDisjoint6
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · simp
  have hfailed_card (b : X.State) (j : Fin X.hp.H) (A : Finset X.Loc)
      (hA : A ∈ X.failedSets H C b j) : A.card ≤ X.T := by
    classical
    simp only [Ctx6.failedSets, Finset.mem_image] at hA
    rcases hA with ⟨D, hD, hEq⟩
    have hD' := (Finset.mem_filter.mp hD).1
    simp only [Ctx6.descsIn, Finset.mem_image] at hD'
    rcases hD' with ⟨φ, hφ, hdesc⟩
    have hφcard : (Finset.univ.image φ).card ≤ X.T :=
      (Finset.mem_filter.mp hφ).2.2
    have hImg : (X.descOf b φ).image Prod.fst = Finset.univ.image φ := by
      ext x
      simp [Ctx6.descOf]
    calc
      A.card = (D.image Prod.fst).card := by rw [hEq]
      _ = ((X.descOf b φ).image Prod.fst).card := by rw [hdesc]
      _ = (Finset.univ.image φ).card := by rw [hImg]
      _ ≤ X.T := hφcard
  have hUnionFamily (F : Finset (Finset X.Loc)) (hcard : F.card < n)
      (hsize : ∀ A ∈ F, A.card ≤ X.T) : (F.biUnion id).card ≤ n * X.T := by
    calc
      (F.biUnion id).card ≤ ∑ A ∈ F, A.card := Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ F, X.T := Finset.sum_le_sum fun A hA => hsize A hA
      _ = F.card * X.T := by simp
      _ ≤ n * X.T := Nat.mul_le_mul_right X.T hcard.le
  have hsite_inj {a a' : X.State} (ha : a ∈ X.g.L.evenStates) (ha' : a' ∈ X.g.L.evenStates)
      (he : X.site a = X.site a') : a = a' := by
    classical
    unfold ChunkLayout6.evenStates at ha ha'
    simp only [Finset.mem_image] at ha ha'
    rcases ha with ⟨x, hx, rfl⟩
    rcases ha' with ⟨x', hx', rfl⟩
    exact X.code.enc_injective _ _ he
  have hstate_even {a b : X.State} (ha : a ∈ X.g.L.stNbr b) : a ∈ X.g.L.evenStates := by
    classical
    unfold ChunkLayout6.stNbr at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨u, v, _hu, hv, _hb, hst, _hadj⟩
    unfold ChunkLayout6.evenStates
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hst⟩
  intro v hv l
  have hdEq : X.hp.d = X.code.d := by rfl
  let vCode : CubeVertex X.code.d := hdEq ▸ v
  rw [Ctx6.sites] at hv
  obtain ⟨a₀, ha₀, hsite₀⟩ := Finset.mem_image.mp hv
  have hsite₀Code : X.site a₀ = vCode := by simpa [vCode, hdEq, Ctx6.hp] using hsite₀
  let B : Finset X.State := X.g.L.oddStates.filter fun b => a₀ ∈ X.g.L.stNbr b
  let Js : Finset (Fin X.hp.H) := Finset.univ.filter fun j => l ∈ X.levelPair j
  let inner (b : X.State) : Finset X.Loc :=
    Js.biUnion fun j => (maxDisjoint6 (X.failedSets H C b j)).biUnion id
  have hBcard : B.card ≤ 3 * n := by
    simpa [B] using X.facts.odd_nbr_card a₀
  have hJsCard : Js.card ≤ 2 := by
    let f : Fin X.hp.H → Fin 2 := fun j => if j.val = l.val then 0 else 1
    have hlevel (j : Fin X.hp.H) (hj : j ∈ Js) : j.val = l.val ∨ j.val + 1 = l.val := by
      have hmem := (Finset.mem_filter.mp hj).2
      have hpair : l = j.castSucc ∨ l = j.succ := by
        simpa [Ctx6.levelPair] using hmem
      rcases hpair with hpair | hpair
      · have hv := congrArg Fin.val hpair
        left
        simpa using hv.symm
      · have hv := congrArg Fin.val hpair
        right
        simpa using hv.symm
    have hinj : (Js : Set (Fin X.hp.H)).InjOn f := by
      intro j hj k hk hfk
      have hjp := hlevel j (by simpa using hj)
      have hkp := hlevel k (by simpa using hk)
      by_cases hjEq : j.val = l.val
      · have hkEq : k.val = l.val := by
          by_contra hkNe
          have hv := congrArg Fin.val hfk
          simp [f, hjEq, hkNe] at hv
        apply Fin.ext
        omega
      · have hjSucc := hjp.resolve_left hjEq
        have hkNe : k.val ≠ l.val := by
          by_contra hkEq
          have hv := congrArg Fin.val hfk
          simp [f, hjEq, hkEq] at hv
        have hkSucc := hkp.resolve_left hkNe
        apply Fin.ext
        omega
    have hcard := Finset.card_le_card_of_injOn f (s := Js) (t := Finset.univ)
      (by intro j hj; exact Finset.mem_univ _) hinj
    simpa using hcard
  have hInnerBound (b : X.State) (hb : b ∈ B) : (inner b).card ≤ 2 * (n * X.T) := by
    calc
      (inner b).card ≤ ∑ j ∈ Js, ((maxDisjoint6 (X.failedSets H C b j)).biUnion id).card := by
        simp only [inner]
        exact Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Js, n * X.T := by
        apply Finset.sum_le_sum
        intro j hj
        apply hUnionFamily
        · exact hMarks b (Finset.mem_filter.mp hb).1 j
        · intro A hA
          apply hfailed_card
          exact hmax_subset _ hA
      _ = Js.card * (n * X.T) := by simp
      _ ≤ 2 * (n * X.T) := Nat.mul_le_mul_right _ hJsCard
  have hmarkcard : (X.marked H C vCode l).card ≤ 6 * n ^ 2 * X.T := by
    have hsub : X.marked H C vCode l ⊆ B.biUnion inner := by
      intro x hx
      classical
      unfold Ctx6.marked at hx
      simp only [Finset.mem_biUnion] at hx
      rcases hx with ⟨b, hb, hx⟩
      by_cases hadj : vCode ∈ (X.g.L.stNbr b).image X.site
      · have hbB : b ∈ B := by
          apply Finset.mem_filter.mpr
          refine ⟨hb, ?_⟩
          obtain ⟨a, ha, hsite⟩ := Finset.mem_image.mp hadj
          have haEven := hstate_even ha
          have he : X.site a = X.site a₀ := hsite.trans hsite₀Code.symm
          have haEq := hsite_inj haEven ha₀ he
          simpa [haEq] using ha
        have hx' : x ∈ inner b := by
          change x ∈ if vCode ∈ (X.g.L.stNbr b).image X.site then
            Js.biUnion (fun j => (maxDisjoint6 (X.failedSets H C b j)).biUnion id) else ∅ at hx
          rw [if_pos hadj] at hx
          simpa [inner, Js] using hx
        exact Finset.mem_biUnion.mpr ⟨b, hbB, hx'⟩
      · change x ∈ if vCode ∈ (X.g.L.stNbr b).image X.site then
          Js.biUnion (fun j => (maxDisjoint6 (X.failedSets H C b j)).biUnion id) else ∅ at hx
        rw [if_neg hadj] at hx
        simp at hx
    calc
      (X.marked H C vCode l).card ≤ (B.biUnion inner).card := Finset.card_le_card hsub
      _ ≤ ∑ b ∈ B, (inner b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ B, 2 * (n * X.T) := Finset.sum_le_sum fun b hb => hInnerBound b hb
      _ = B.card * (2 * (n * X.T)) := by simp
      _ ≤ 3 * n * (2 * (n * X.T)) := Nat.mul_le_mul_right _ hBcard
      _ = 6 * n ^ 2 * X.T := by ring
  have hmarkedSmall : (X.marked H C vCode l).card ≤ (n : ℝ) ^ 10 / 6 := by
    have hcast : ((X.marked H C vCode l).card : ℝ) ≤ 6 * (n : ℝ) ^ 2 * (X.T : ℝ) := by exact_mod_cast hmarkcard
    have hrem : 6 * (n : ℝ) ^ 2 * (X.T : ℝ) ≤ (n : ℝ) ^ 10 / 6 := hRemoval
    exact hcast.trans hrem
  have hprosplow : (n : ℝ) ^ 10 / 2 ≤ (X.prosp (X.pos C) vCode l).card := by
    simpa [Ctx6.hp, J₀₆, vCode, hdEq] using (hCounts v hv l).1
  let s := X.prosp (X.pos C) vCode l
  let t := X.marked H C vCode l
  have hcardEq := Finset.card_sdiff_add_card_inter s t
  have hInter : (s ∩ t).card ≤ t.card := Finset.card_le_card Finset.inter_subset_right
  have hInterR : ((s ∩ t).card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast hInter
  have hcardDiff : (n : ℝ) ^ 10 / 3 ≤ (s \ t).card := by
    have hEqR : ((s \ t).card : ℝ) + ((s ∩ t).card : ℝ) = s.card := by exact_mod_cast hcardEq
    have hsR : (n : ℝ) ^ 10 / 2 ≤ s.card := by simpa [s] using hprosplow
    nlinarith [hEqR, hsR, hInterR, hmarkedSmall]
  have hLegal : X.hp.LegalAt (X.pos C) (X.elig H C) vCode l := by
    constructor
    · intro x hx
      have hx' : x ∈ X.prosp (X.pos C) vCode l \ X.marked H C vCode l := by
        simpa [Ctx6.elig] using hx
      have hxPro : x ∈ X.prosp (X.pos C) vCode l := (Finset.mem_sdiff.mp hx').1
      simpa [Ctx6.prosp] using hxPro
    · change (n : ℝ) ^ 10 / 3 ≤
        (X.prosp (X.pos C) vCode l \ X.marked H C vCode l).card
      simpa [Ctx6.elig, s, t, Ctx6.hp, J₀₆] using hcardDiff
  exact hLegal


/-- L6.1i (heights, 06:555–557): the global height bound of Lemma 3.8 (`height_selection_global`, auxiliary
randomness = the tuple arrays). -/
theorem L6_1i_heights (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HeightsBound := by
  rcases height_exponents6_admissible p₀ hadm.2.2.1 with
    ⟨_, _, _, _, _, ⟨hAdm⟩⟩
  let reg : HDRegime (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) D₀₆ :=
    .lin (1 / 400) ⟨by norm_num, by norm_num⟩
  obtain ⟨c, hc, n₀, hglobal⟩ :=
    height_selection_global J₀₆ (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) (σ₆ (α₆ p₀))
      (ζ₆ (α₆ p₀)) (θ₆ (α₆ p₀)) (a₆ (α₆ p₀)) cd₆ Cd₆ D₀₆ hAdm reg
  refine ⟨max n₀ 200, 1, fun n N E G M X hL => ?_⟩
  intro H
  have hn200 : 200 ≤ n := le_trans (le_max_right _ _) hL.1
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hL.1
  have hn200real : (200 : ℝ) ≤ n := by exact_mod_cast hn200
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
  have hrEq : X.hp.r = ⌊(1 / 100 : ℝ) * n⌋₊ := by rfl
  have hrLower : (n : ℝ) / 200 ≤ (X.hp.r : ℝ) := by
    rw [hrEq]
    have hfloor := Nat.lt_floor_add_one ((1 / 100 : ℝ) * n)
    nlinarith [hfloor, hn200real]
  have hrUpper : (X.hp.r : ℝ) ≤ (n : ℝ) / 100 := by
    rw [hrEq]
    calc
      (⌊(1 / 100 : ℝ) * n⌋₊ : ℝ) ≤ (1 / 100 : ℝ) * n :=
        Nat.floor_le (show (0 : ℝ) ≤ (1 / 100 : ℝ) * n by positivity)
      _ = (n : ℝ) / 100 := by ring
  have hdUpper : (X.hp.d : ℝ) ≤ 2 * n := X.code.d_upper
  have hdLower : (1 / 2 : ℝ) * n ≤ X.hp.d := X.code.d_lower
  have hreg : reg.ok n X.hp.d X.hp.r := by
    constructor
    · calc
        (1 / 400 : ℝ) * X.hp.d ≤ (1 / 400 : ℝ) * (2 * n) :=
          mul_le_mul_of_nonneg_left hdUpper (by norm_num)
        _ = (n : ℝ) / 200 := by ring
        _ ≤ (X.hp.r : ℝ) := hrLower
    · have hfour : (4 : ℝ) * (X.hp.r : ℝ) ≤ X.hp.d := by
        calc
          (4 : ℝ) * (X.hp.r : ℝ) ≤ 4 * ((n : ℝ) / 100) :=
            mul_le_mul_of_nonneg_left hrUpper (by norm_num)
          _ ≤ (1 / 2 : ℝ) * n := by nlinarith
          _ ≤ X.hp.d := hdLower
      exact_mod_cast hfour
  let Esel : (X.Loc → Bool) → X.Data X.Loc → X.hp.EligMap := fun P d =>
    X.elig H (((P, d), fun _ => false), fun _ => Equiv.refl _)
  let Pbase : FinProb (((X.hp.Loc → Bool) × X.Data X.Loc) × (X.hp.Loc → Bool)) :=
    (X.hp.posLaw.prod (X.dataLaw X.Loc H)).prod X.hp.actLaw
  let badAux : (((X.hp.Loc → Bool) × X.Data X.Loc) × (X.hp.Loc → Bool)) → Prop :=
    fun ω => X.hp.Legal ω.1.1 (Esel ω.1.1 ω.1.2) X.sites ∧
      ¬ X.hp.GoodHeights X.sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)
  have hElig (P : X.hp.Loc → Bool) (d : X.Data X.Loc) (A : X.hp.Loc → Bool) (τ : X.hp.Ties) :
      X.elig H (((P, d), A), τ) = Esel P d := by
    funext v l
    rfl
  have hEvent (P : X.hp.Loc → Bool) (d : X.Data X.Loc) (A : X.hp.Loc → Bool) (τ : X.hp.Ties) :
      (X.EligOK H (((P, d), A), τ) ∧ ¬ X.HeightsOK H (((P, d), A), τ)) =
        badAux ((P, d), A) := by
    simp only [Ctx6.EligOK, Ctx6.HeightsOK, Ctx6.pos, Ctx6.act, badAux, Esel]
    rw [hElig]
  have hprob : (X.centreLaw H).pr
      (fun C => X.EligOK H C ∧ ¬ X.HeightsOK H C) = Pbase.pr badAux := by
    classical
    unfold FinProb.pr Ctx6.centreLaw FinProb.prod
    unfold Pbase
    unfold FinProb.prod
    rw [Fintype.sum_prod_type]
    simp_rw [hEvent]
    change (∑ z, ∑ τ,
        (if badAux z then
          X.hp.posLaw.w z.1.1 * (X.dataLaw X.Loc H).w z.1.2 * X.hp.actLaw.w z.2 *
            X.hp.tieLaw.w τ else 0)) =
      ∑ z, if badAux z then
        X.hp.posLaw.w z.1.1 * (X.dataLaw X.Loc H).w z.1.2 * X.hp.actLaw.w z.2 else 0
    calc
      (∑ z, ∑ τ,
          (if badAux z then
            X.hp.posLaw.w z.1.1 * (X.dataLaw X.Loc H).w z.1.2 * X.hp.actLaw.w z.2 *
              X.hp.tieLaw.w τ else 0)) =
          ∑ z, (if badAux z then
            X.hp.posLaw.w z.1.1 * (X.dataLaw X.Loc H).w z.1.2 * X.hp.actLaw.w z.2 *
              ∑ τ, X.hp.tieLaw.w τ else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hz' : badAux z <;> simp [hz', Finset.mul_sum, mul_assoc]
      _ = ∑ z, if badAux z then
          X.hp.posLaw.w z.1.1 * (X.dataLaw X.Loc H).w z.1.2 * X.hp.actLaw.w z.2 else 0 := by
        simp [X.hp.tieLaw.sum_eq_one]
  have hbad := hglobal X.hp rfl rfl rfl rfl rfl hn0 X.code.d_lower X.code.d_upper hreg
    X.sites (X.dataLaw X.Loc H) Esel
  have hnPow' : (n : ℝ) ≤ (n : ℝ) ^ (1 + c) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 + c) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by linarith [hc])
  rw [hprob]
  have hbad' : Pbase.pr badAux ≤ Real.exp (-((n : ℝ) ^ (1 + c))) := by
    simpa [badAux, Esel, Pbase, Ctx6.hp] using hbad
  exact (hbad'.trans (Real.exp_le_exp.mpr (by linarith [hnPow'])))


/-- L6.1i (validity, 06:557–559): good heights give choices on two consecutive levels, the crowd bound gives at
most `2n^b ≤ T` IDs, and a failed actual descriptor would be disjoint from the marked union. -/
theorem L6_1i_valid (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.ValidDet := by
  have hExp := height_exponents6_admissible p₀ hadm.2.2.1
  have hα : 0 < α₆ p₀ := hExp.1
  let δ := (3 * α₆ p₀) / 4000
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have htend : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hδ).comp _root_.tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ k : ℕ in Filter.atTop, (2 : ℝ) ≤ (k : ℝ) ^ δ :=
    htend.eventually_ge_atTop 2
  obtain ⟨nT, hnT⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 300 nT, 1, fun n N E G M X hL hHist => ?_⟩
  have hnT' : nT ≤ n := le_trans (le_max_right _ _) hL.1
  have hn300 : 300 ≤ n := le_trans (le_max_left _ _) hL.1
  have hTbound : 2 * (n : ℝ) ^ b₆ (α₆ p₀) ≤ (X.T : ℝ) := by
    have hnδ := hnT n hnT'
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn300)
    have hsum : b₆ (α₆ p₀) + δ = α₆ p₀ / 1000 := by
      dsimp [b₆, δ]
      ring
    have hpow : 2 * (n : ℝ) ^ b₆ (α₆ p₀) ≤ (n : ℝ) ^ (α₆ p₀ / 1000) := by
      calc
        2 * (n : ℝ) ^ b₆ (α₆ p₀) =
            (n : ℝ) ^ b₆ (α₆ p₀) * 2 := by ring
        _ ≤ (n : ℝ) ^ b₆ (α₆ p₀) * (n : ℝ) ^ δ :=
          mul_le_mul_of_nonneg_left hnδ
            (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity) _)
        _ = (n : ℝ) ^ (b₆ (α₆ p₀) + δ) := (Real.rpow_add hnPos _ _).symm
        _ = (n : ℝ) ^ (α₆ p₀ / 1000) := by rw [hsum]
    have hmLower : (n : ℝ) ^ α₆ p₀ ≤ (X.m : ℝ) := by
      change (n : ℝ) ^ α₆ p₀ ≤ (X.g.L.m : ℝ)
      rw [X.g.m_eq]
      exact Nat.le_ceil _
    have hcomp : (n : ℝ) ^ (α₆ p₀ / 1000) =
        ((n : ℝ) ^ α₆ p₀) ^ (1 / 1000 : ℝ) := by
      rw [show α₆ p₀ / 1000 = α₆ p₀ * (1 / 1000 : ℝ) by ring,
        Real.rpow_mul (by positivity)]
    have hmPower : (n : ℝ) ^ (α₆ p₀ / 1000) ≤ (X.m : ℝ) ^ (1 / 1000 : ℝ) := by
      rw [hcomp]
      exact Real.rpow_le_rpow (by positivity) hmLower (by norm_num)
    have hTceil : (X.m : ℝ) ^ (1 / 1000 : ℝ) ≤ (X.T : ℝ) := by
      change (X.g.L.m : ℝ) ^ (1 / 1000 : ℝ) ≤ (T₆ X.g.L.m : ℝ)
      exact Nat.le_ceil _
    exact hpow.trans (hmPower.trans hTceil)
  intro H C hH hGeo
  rcases hHist H hH with ⟨hBase, hHid, _hV0, hStep1, hStep2, _hRates⟩
  have hstateEven {a b : X.State} (ha : a ∈ X.g.L.stNbr b) : a ∈ X.g.L.evenStates := by
    classical
    unfold ChunkLayout6.stNbr at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨u, v, _hu, hv, _hb, hst, _hadj⟩
    unfold ChunkLayout6.evenStates
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hst⟩
  have hsiteMem {a b : X.State} (ha : a ∈ X.g.L.stNbr b) : X.site a ∈ X.sites := by
    have haEven := hstateEven ha
    rw [Ctx6.sites]
    exact Finset.mem_image.mpr ⟨a, haEven, rfl⟩
  have hTypeAtState (w : CubeVertex n) :
      X.stType (X.g.L.stateOf w) = X.evenType w := by
    unfold Ctx6.stType Ctx6.evenType ChunkLayout6.stType
    simp [X.facts.key_eq w, X.facts.sign_eq w, X.facts.flippable_eq w, X.facts.severity_eq w]
  have hTypeOcc (b a : X.State) (ha : a ∈ X.g.L.stNbr b) : X.stType a ∈ X.occTypes := by
    have haEven := hstateEven ha
    unfold ChunkLayout6.evenStates at haEven
    simp only [Finset.mem_image] at haEven
    obtain ⟨w, hw, hstate⟩ := haEven
    have hwEven := (Finset.mem_filter.mp hw).2
    have htype : X.evenType w = X.stType a := by
      have h := hTypeAtState w
      rw [hstate] at h
      exact h.symm
    unfold Ctx6.occTypes
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwEven⟩, htype⟩
  have hchoiceData (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
      ∃ ℓ, X.choice H C X.Rlong a = some ℓ ∧
        ℓ ∈ X.elig H C (X.site a) ⟨X.hp.height X.sites (X.pos C) (X.act C)
          (X.elig H C) X.Rlong (X.site a), by
            have hh := (hGeo.2.2.2 (X.site a) (hsiteMem ha)).1
            exact Nat.lt_succ_of_lt (by simpa [Ctx6.Rlong] using hh)⟩ ∧ X.act C ℓ = true := by
    classical
    let P := X.pos C
    let A := X.act C
    let Esel := X.elig H C
    let v := X.site a
    let ht := X.hp.height X.sites P A Esel X.Rlong v
    have hsiteGood := hGeo.2.2.2 v (hsiteMem ha)
    have hlt : ht < X.hp.H := by
      simpa [ht, Ctx6.Rlong, P, A, Esel, v] using hsiteGood.1
    let j : Fin (X.hp.H + 1) := ⟨ht, by omega⟩
    have hheight0 : X.hp.height X.sites P A Esel X.hp.Rlong v < X.hp.H := by
      simpa [P, A, Esel, v] using hsiteGood.1
    have hnotBad : ¬ X.hp.Bad P A Esel v j := by
      intro hbad
      apply hsiteGood.2.1
      refine ⟨Nat.lt_succ_of_lt hheight0, ?_⟩
      simpa [Ctx6.Rlong, P, A, Esel, v, j, ht] using hbad
    let active : Finset X.Loc := (Esel v j).filter fun ℓ => A ℓ = true
    have hactive : active.Nonempty := by
      by_contra hne
      have hEmpty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      apply hnotBad
      left
      intro ℓ hℓ
      by_cases hact : A ℓ = true
      · have hmem : ℓ ∈ active := Finset.mem_filter.mpr ⟨hℓ, hact⟩
        rw [hEmpty] at hmem
        simp at hmem
      · cases hval : A ℓ <;> simp_all
    let priorities := active.image (fun ℓ => X.hp.priority (X.ties C) (v, j) ℓ)
    have hprio : priorities.Nonempty := by
      rcases hactive with ⟨ℓ, hℓ⟩
      exact ⟨X.hp.priority (X.ties C) (v, j) ℓ,
        Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩⟩
    let q := priorities.min' hprio
    have hq : q ∈ priorities := Finset.min'_mem priorities hprio
    have hmem : ∃ ℓ, ℓ ∈ active ∧ X.hp.priority (X.ties C) (v, j) ℓ = q :=
      Finset.mem_image.mp hq
    have hsel : X.hp.selectionAt X.sites P A Esel (X.ties C) X.Rlong v =
        some (Classical.choose hmem) := by
      simp [HDParams.selectionAt, Ctx6.Rlong, ht, j, hnotBad, active,
        priorities, q, hq, hmem]
      exact ⟨hlt, hnotBad, by
        simpa [active, j, Ctx6.Rlong, Ctx6.Loc, ht, P, A, Esel, v] using hactive⟩
    have hchoice : X.choice H C X.Rlong a = some (Classical.choose hmem) := by
      simpa [Ctx6.choice, P, A, Esel, v] using hsel
    obtain ⟨hactiveMem, hpriority⟩ := Classical.choose_spec hmem
    have hactiveMem' : Classical.choose hmem ∈ Esel v j ∧ A (Classical.choose hmem) = true := by
      simpa [active] using hactiveMem
    refine ⟨Classical.choose hmem, hchoice, ?_, hactiveMem'.2⟩
    exact hactiveMem'.1
  intro u hu
  let b := X.g.L.stateOf u
  have hbOdd : b ∈ X.g.L.oddStates := by
    unfold b ChunkLayout6.oddStates
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
  have hKeyOcc : X.g.L.key u ∈ X.occKeys := by
    unfold Ctx6.occKeys
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hKeyEq : X.g.L.stKey b = X.g.L.key u := by
    simpa [b] using X.facts.key_eq u
  have hKeySelf : X.g.L.key u ∈ X.C (X.g.L.key u) := by
    simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  have hStep1Key : X.g.L.key u ∈ X.step1Keys := by
    unfold Ctx6.step1Keys
    exact Finset.mem_biUnion.mpr ⟨X.g.L.key u, hKeyOcc, hKeySelf⟩
  have hTargetKey : (X.tgt b).1 ∈ X.step1Keys := by
    have hEq : (X.tgt b).1 = X.g.L.key u := by
      simpa [Ctx6.tgt, ChunkLayout6.stTarget] using hKeyEq
    rw [hEq]
    exact hStep1Key
  have hStep1Target := hStep1 (X.tgt b).1 hTargetKey
  change X.OddValid H C X.Rlong b
  have hoddNbr : (X.g.L.stNbr b).Nonempty := X.facts.nbr_nonempty b hbOdd
  have hsome : ∀ a ∈ X.g.L.stNbr b, (X.choice H C X.Rlong a).isSome := by
    intro a ha
    obtain ⟨ℓ, hℓ, _, _⟩ := hchoiceData b a ha
    simp [hℓ]
  have hcounts : ∀ a ∈ X.g.L.stNbr b, ∀ l,
      ((X.prosp (X.pos C) (X.site a) l).card : ℝ) ≤ 2 * X.hp.lam := by
    intro a ha l
    exact (hGeo.1 (X.site a) (hsiteMem ha) l).2
  let heightOf := fun a : X.State =>
    X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong (X.site a)
  have hOddNbr : (X.g.L.stNbr b).Nonempty := X.facts.nbr_nonempty b hbOdd
  let heights : Finset ℕ := (X.g.L.stNbr b).image heightOf
  have hHeights : heights.Nonempty := by
    rcases hOddNbr with ⟨a, ha⟩
    exact ⟨heightOf a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let hmin := heights.min' hHeights
  obtain ⟨aMin, haMin, hminEq⟩ := Finset.mem_image.mp (Finset.min'_mem heights hHeights)
  have hminLt : hmin < X.hp.H := by
    change heights.min' hHeights < X.hp.H
    rw [← hminEq]
    exact (hGeo.2.2.2 (X.site aMin) (hsiteMem haMin)).1
  let jFin : Fin X.hp.H := ⟨hmin, hminLt⟩
  have hminLe (a : X.State) (ha : a ∈ X.g.L.stNbr b) : hmin ≤ heightOf a :=
    Finset.min'_le heights (heightOf a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hlevelCases (a : X.State) (ha : a ∈ X.g.L.stNbr b) :
      heightOf a = hmin ∨ heightOf a = hmin + 1 := by
    have hclose := (hGeo.2.2.2 (X.site a) (hsiteMem ha)).2.2
      (X.site aMin) (hsiteMem haMin) (X.code.nbr_dist b a ha aMin haMin)
    have hupperInt : (heightOf a : ℤ) ≤ (hmin : ℤ) + 1 := by
      have hupper := (abs_le.mp hclose).2
      have hminInt : (heightOf aMin : ℤ) = (hmin : ℤ) := by exact_mod_cast hminEq
      rw [hminInt] at hupper
      linarith
    have hupperNat : heightOf a ≤ hmin + 1 := by exact_mod_cast hupperInt
    have hminLower : hmin ≤ heightOf a := hminLe a ha
    omega
  have hselectedLevel {a : X.State} (ha : a ∈ X.g.L.stNbr b) {ℓ : X.Loc}
      (hsel : X.choice H C X.Rlong a = some ℓ) : ℓ.2.val = heightOf a := by
    obtain ⟨ℓ₀, hchoice, hEligible, _hActive⟩ := hchoiceData b a ha
    have hSame : ℓ = ℓ₀ := Option.some.inj (hsel.symm.trans hchoice)
    cases hSame
    let ja : Fin (X.hp.H + 1) := ⟨heightOf a, by
      have hltA : heightOf a < X.hp.H := by
        simpa [heightOf, Ctx6.Rlong] using (hGeo.2.2.2 (X.site a) (hsiteMem ha)).1
      exact Nat.lt_succ_of_lt hltA⟩
    have hlegalAt := hGeo.2.2.1 (X.site a) (hsiteMem ha) ja
    have hlevelEq : ℓ.2 = ja := (hlegalAt.1 ℓ hEligible).2.1
    simpa [ja] using congrArg Fin.val hlevelEq
  have hselectedPair {a : X.State} (ha : a ∈ X.g.L.stNbr b) {ℓ : X.Loc}
      (hsel : X.choice H C X.Rlong a = some ℓ) : ℓ.2 ∈ X.levelPair jFin := by
    have hval := hselectedLevel ha hsel
    rcases hlevelCases a ha with hEq | hEq
    · have hv0 : ℓ.2.val = hmin := hval.trans hEq
      have hFin : ℓ.2 = jFin.castSucc := by
        apply Fin.ext
        simpa [jFin] using hv0
      simpa [Ctx6.levelPair, hFin]
    · have hv1 : ℓ.2.val = hmin + 1 := hval.trans hEq
      have hFin : ℓ.2 = jFin.succ := by
        apply Fin.ext
        simpa [jFin] using hv1
      simpa [Ctx6.levelPair, hFin]
  let Dids : Finset X.Loc := (X.actDesc H C X.Rlong b).image Prod.fst
  have hDidsMem {x : X.Loc} (hx : x ∈ Dids) :
      ∃ a ∈ X.g.L.stNbr b, (X.choice H C X.Rlong a).getD X.defaultLoc = x := by
    simpa [Dids, Ctx6.actDesc] using hx
  have hIdsAtLevel (q : Fin (X.hp.H + 1)) :
      ((Dids.filter fun x => x.2 = q).card : ℝ) ≤ (n : ℝ) ^ b₆ (α₆ p₀) := by
    let S : Finset X.Loc := Dids.filter fun x => x.2 = q
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      obtain ⟨a₀, ha₀, hget⟩ := hDidsMem (Finset.mem_filter.mp hx).1
      obtain ⟨ℓ₀, hchoice, hEligible, hActive⟩ := hchoiceData b a₀ ha₀
      have hEq0 : ℓ₀ = x := by simpa [hchoice] using hget
      have hlevelRep : heightOf a₀ = q.val := by
        have hselected := hselectedLevel ha₀ hchoice
        have hfirst : ℓ₀.2.val = x.2.val := congrArg (fun z : X.Loc => z.2.val) hEq0
        have hq : x.2 = q := (Finset.mem_filter.mp hx).2
        rw [hfirst, hq] at hselected
        exact hselected.symm
      have hrepGood := hGeo.2.2.2 (X.site a₀) (hsiteMem ha₀)
      have hrepHt : heightOf a₀ < X.hp.H := by
        simpa [heightOf, Ctx6.Rlong] using hrepGood.1
      have hqEq : q = ⟨heightOf a₀, Nat.lt_succ_of_lt hrepHt⟩ := Fin.ext hlevelRep.symm
      have hnotBad : ¬ X.hp.Bad (X.pos C) (X.act C) (X.elig H C) (X.site a₀) q := by
        intro hbad
        apply hrepGood.2.1
        refine ⟨Nat.lt_succ_of_lt (by simpa [heightOf, Ctx6.Rlong] using hrepGood.1), ?_⟩
        simpa [hqEq] using hbad
      let crowd : Finset (CubeVertex X.hp.d) := Finset.univ.filter fun y =>
        (X.pos C (y, q) = true ∧ X.act C (y, q) = true ∧
          _root_.hammingDist y (X.site a₀) ≤ X.hp.r + X.hp.D)
      have hCrowd : (crowd.card : ℝ) ≤ (n : ℝ) ^ b₆ (α₆ p₀) := by
        apply le_of_not_gt
        intro hlarge
        apply hnotBad
        right
        simpa [crowd, HDParams.Bad, Ctx6.hp] using hlarge
      have hMaps : Set.MapsTo (fun z : X.Loc => z.1) (S : Set X.Loc) (crowd : Set (CubeVertex X.hp.d)) := by
        intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyD, hyLevel⟩
        obtain ⟨a, ha, hgetA⟩ := hDidsMem hyD
        obtain ⟨ℓ, hchoiceA, hEligibleA, hActiveA⟩ := hchoiceData b a ha
        have hEqA : ℓ = y := by simpa [hchoiceA] using hgetA
        have hLevelA : ℓ.2 = q := by
          calc
            ℓ.2 = y.2 := congrArg (fun z : X.Loc => z.2) hEqA
            _ = q := hyLevel
        have hHeightA : heightOf a = q.val := by
          calc
            heightOf a = ℓ.2.val := (hselectedLevel ha hchoiceA).symm
            _ = q.val := congrArg Fin.val hLevelA
        let ja : Fin (X.hp.H + 1) := ⟨heightOf a, by
          have hltA : heightOf a < X.hp.H := by
            simpa [heightOf, Ctx6.Rlong] using (hGeo.2.2.2 (X.site a) (hsiteMem ha)).1
          exact Nat.lt_succ_of_lt hltA⟩
        have hlegalA := hGeo.2.2.1 (X.site a) (hsiteMem ha) ja
        have hlevelEqA : ℓ.2 = ja := (hlegalA.1 ℓ hEligibleA).2.1
        have hjaEq : ja = q := hlevelEqA.symm.trans hLevelA
        have hEligibleQ : y ∈ X.elig H C (X.site a) q := by
          have hℓQ : ℓ ∈ X.elig H C (X.site a) q := by
            rw [← hjaEq]
            exact hEligibleA
          exact hEqA ▸ hℓQ
        have hlegalAQ := hGeo.2.2.1 (X.site a) (hsiteMem ha) q
        obtain ⟨hpos, _hlev, hdist⟩ := hlegalAQ.1 y hEligibleQ
        have hActY : X.act C y = true := by simpa [hEqA] using hActiveA
        have hnear := X.code.nbr_dist b a ha a₀ ha₀
        have htri := _root_.hammingDist_triangle y.1 (X.site a) (X.site a₀)
        have hdistOut : _root_.hammingDist y.1 (X.site a₀) ≤ X.hp.r + X.hp.D :=
          le_trans htri (Nat.add_le_add hdist hnear)
        have hLocEq : y = (y.1, q) := by
          apply Prod.ext
          · rfl
          · exact hyLevel
        have hposPair : X.pos C (y.1, q) = true := by
          exact (congrArg (X.pos C) hLocEq).symm.trans hpos
        have hActPair : X.act C (y.1, q) = true := by
          exact (congrArg (X.act C) hLocEq).symm.trans hActY
        change y.1 ∈ crowd
        simp only [crowd, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hposPair, hActPair, hdistOut⟩
      have hInj : (S : Set X.Loc).InjOn (fun z : X.Loc => z.1) := by
        intro x hx y hy hxy
        apply Prod.ext hxy
        exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      have hCard : S.card ≤ crowd.card := Finset.card_le_card_of_injOn _ hMaps hInj
      exact (Nat.cast_le.mpr hCard).trans hCrowd
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simpa [S, hEmpty] using (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        (b₆ (α₆ p₀)))
  have hDidsCard : Dids.card ≤ X.T := by
    let L0 : Finset X.Loc := Dids.filter fun x => x.2 = jFin.castSucc
    let L1 : Finset X.Loc := Dids.filter fun x => x.2 = jFin.succ
    have hDsubset : Dids ⊆ L0 ∪ L1 := by
      intro x hx
      obtain ⟨a, ha, hget⟩ := hDidsMem hx
      obtain ⟨ℓ, hchoice, _, _⟩ := hchoiceData b a ha
      have hEq : ℓ = x := by simpa [hchoice] using hget
      have hPair : x.2 ∈ X.levelPair jFin := by
        simpa [hEq] using hselectedPair ha hchoice
      have hCases : x.2 = jFin.castSucc ∨ x.2 = jFin.succ := by
        simpa [Ctx6.levelPair] using hPair
      rcases hCases with h0 | h1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, h0⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, h1⟩))
    have hDcardNat : Dids.card ≤ L0.card + L1.card :=
      (Finset.card_le_card hDsubset).trans (Finset.card_union_le L0 L1)
    have hL0 : (L0.card : ℝ) ≤ (n : ℝ) ^ b₆ (α₆ p₀) := by
      simpa [L0] using hIdsAtLevel jFin.castSucc
    have hL1 : (L1.card : ℝ) ≤ (n : ℝ) ^ b₆ (α₆ p₀) := by
      simpa [L1] using hIdsAtLevel jFin.succ
    have hDcardR : (Dids.card : ℝ) ≤ 2 * (n : ℝ) ^ b₆ (α₆ p₀) := by
      have hsum : (Dids.card : ℝ) ≤ (L0.card : ℝ) + (L1.card : ℝ) := by
        exact_mod_cast hDcardNat
      linarith
    have hDcardR' : (Dids.card : ℝ) ≤ (X.T : ℝ) := hDcardR.trans hTbound
    exact_mod_cast hDcardR'
  let D0 : Finset (X.Loc × X.Ty) := X.actDesc H C X.Rlong b
  let φ : X.g.L.stNbr b → X.Loc := fun a => (X.choice H C X.Rlong a.1).getD X.defaultLoc
  have hDescEq : X.descOf b φ = D0 := by rfl
  have hPerm : ∀ a : X.g.L.stNbr b,
      φ a ∈ X.permAt (X.pos C) b jFin a := by
    intro a
    obtain ⟨ℓ, hChoice, hEligible, _hActive⟩ := hchoiceData b a.1 a.2
    have hPair := hselectedPair a.2 hChoice
    have hLevelVal := hselectedLevel a.2 hChoice
    have hLevelEq : (⟨heightOf a.1, by
        have hltA : heightOf a.1 < X.hp.H := by
          simpa [heightOf, Ctx6.Rlong] using (hGeo.2.2.2 (X.site a.1) (hsiteMem a.2)).1
        exact Nat.lt_succ_of_lt hltA⟩ : Fin (X.hp.H + 1)) = ℓ.2 :=
      Fin.ext hLevelVal.symm
    have hEligibleAtLevel : ℓ ∈ X.elig H C (X.site a.1) ℓ.2 := by
      rw [← hLevelEq]
      exact hEligible
    have hprosp : ℓ ∈ X.prosp (X.pos C) (X.site a.1) ℓ.2 := by
      have hmem : ℓ ∈ X.prosp (X.pos C) (X.site a.1) ℓ.2 \ X.marked H C (X.site a.1) ℓ.2 := by
        simpa [Ctx6.elig] using hEligibleAtLevel
      exact (Finset.mem_sdiff.mp hmem).1
    have hφ : φ a = ℓ := by simp [φ, hChoice]
    change φ a ∈ (X.levelPair jFin).biUnion (X.prosp (X.pos C) (X.site a.1))
    rw [hφ]
    exact Finset.mem_biUnion.mpr ⟨ℓ.2, hPair, hprosp⟩
  have hφImage : (Finset.univ.image φ).card = Dids.card := by
    have hImage : Finset.univ.image φ = Dids := by
      unfold Dids
      let pairFun := fun a : X.g.L.stNbr b => (φ a, X.stType a.1)
      have hDesc : X.actDesc H C X.Rlong b = Finset.univ.image pairFun := by rfl
      calc
        Finset.univ.image φ = Finset.univ.image (Prod.fst ∘ pairFun) := by
          rfl
        _ = (Finset.univ.image pairFun).image Prod.fst := Finset.image_image.symm
        _ = (X.actDesc H C X.Rlong b).image Prod.fst := by rw [hDesc]
    rw [hImage]
  have hφCard : (Finset.univ.image φ).card ≤ X.T := by rw [hφImage]; exact hDidsCard
  have hDDesc : D0 ∈ X.descsIn b (X.permAt (X.pos C) b jFin) := by
    unfold Ctx6.descsIn
    apply Finset.mem_image.mpr
    refine ⟨φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hPerm, hφCard⟩⟩, hDescEq⟩
  have hD0Mem (e : X.Loc × X.Ty) (he : e ∈ D0) :
      ∃ a : X.g.L.stNbr b, a.1 ∈ X.g.L.stNbr b ∧ e.2 = X.stType a.1 := by
    change e ∈ Finset.univ.image (fun a : X.g.L.stNbr b =>
      ((X.choice H C X.Rlong a.1).getD X.defaultLoc, X.stType a.1)) at he
    rcases Finset.mem_image.mp he with ⟨a, ha, heq⟩
    exact ⟨a, a.2, (congrArg Prod.snd heq).symm⟩
  have hDTypeOcc : ∀ e ∈ D0, e.2 ∈ X.occTypes := by
    intro e he
    obtain ⟨a, ha, htypeEq⟩ := hD0Mem e he
    have htype := hTypeOcc b a.1 a.2
    simpa [htypeEq] using htype
  have hObsKey (w : CubeVertex n) :
      ∀ ℓ, ℓ ∈ (X.evenType w).obs → ℓ.1 ∈ X.C (X.g.L.key w) := by
    have hSelf : X.g.L.key w ∈ X.C (X.g.L.key w) := by
      simp [Ctx6.C, keyNeighborhood6, keyAdjacent6, binAdjacent6]
    change ∀ ℓ, ℓ ∈ (makeType6 binAdjacent6 (X.g.L.key w) (X.g.L.sign w)
      (X.g.L.flippable w) (X.g.L.severity w) X.J).obs →
        ℓ.1 ∈ X.C (X.g.L.key w)
    unfold makeType6
    by_cases hlow : X.g.L.severity w ≤ X.J
    · rw [if_pos hlow]
      intro ℓ hlowObs
      change ℓ ∈ lowObservations6 binAdjacent6 (X.g.L.key w)
        (X.g.L.sign w) (X.g.L.flippable w) at hlowObs
      simp only [lowObservations6, Finset.mem_union, Finset.mem_image] at hlowObs
      rcases hlowObs with ⟨s, hs, hEq⟩ | ⟨i, hi, hEq⟩
      · have hkey : s = ℓ.1 := by simpa using congrArg Prod.fst hEq
        rw [← hkey]
        exact hs
      · have hkey : X.g.L.key w = ℓ.1 := by simpa using congrArg Prod.fst hEq
        rw [← hkey]
        exact hSelf
    · rw [if_neg hlow]
      intro ℓ hhighObs
      change ℓ ∈ highObservations6 (X.g.L.key w) (X.g.L.sign w)
        (X.g.L.severity w) X.J at hhighObs
      by_cases hsev : X.g.L.severity w = X.J + 1
      · rw [highObservations6, if_pos hsev] at hhighObs
        simp only [Finset.mem_singleton] at hhighObs
        have hkey : ℓ.1 = X.g.L.key w := congrArg Prod.fst hhighObs
        rw [hkey]
        exact hSelf
      · rw [highObservations6, if_neg hsev] at hhighObs
        simp at hhighObs
  have hstep1LocKey (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D0) : ℓ.1 ∈ X.step1Keys := by
    unfold Ctx6.locHid at hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hobs⟩
    obtain ⟨a, ha, htypeEq⟩ := hD0Mem e he
    have haEven := hstateEven ha
    unfold ChunkLayout6.evenStates at haEven
    simp only [Finset.mem_image] at haEven
    obtain ⟨w, hw, hstate⟩ := haEven
    have hwEven := (Finset.mem_filter.mp hw).2
    have htypeEqW : e.2 = X.evenType w := by
      calc
        e.2 = X.stType a := htypeEq
        _ = X.stType (X.g.L.stateOf w) := by rw [hstate]
        _ = X.evenType w := hTypeAtState w
    have hobsW : ℓ ∈ (X.evenType w).obs := by rw [← htypeEqW]; exact hobs
    have hCkey := hObsKey w ℓ hobsW
    have hKeyOcc : X.g.L.key w ∈ X.occKeys := by
      unfold Ctx6.occKeys
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    unfold Ctx6.step1Keys
    exact Finset.mem_biUnion.mpr ⟨X.g.L.key w, hKeyOcc, hCkey⟩
  have hTrueGate : X.S3TrueGate H b D0 := by
    cases hmode : X.stMode b
    · have hWithHid : X.withHid H (X.tgt b) (H.2 (X.tgt b)) = H := by
        simp [Ctx6.withHid]
      have hLowGate : X.LowGate H b D0 (X.trueTarget H b) := by
        unfold Ctx6.LowGate
        simp only [Ctx6.trueTarget, hmode]
        refine ⟨hHid (X.tgt b), ?_, ?_⟩
        · exact hStep1Target.1
        · intro e he
          exact (by simpa [hWithHid] using hStep2 e.2 (hDTypeOcc e he))
      simpa [Ctx6.S3TrueGate, hmode] using hLowGate
    · have htruePar : X.trueTarget H b = (X.parOf H.1).val (X.tgtName b) := by
        simp [Ctx6.trueTarget, hmode]
      have hUpdatePar : X.withParH H (X.tgtName b) (X.trueTarget H b) = H := by
        rw [htruePar]
        cases hnm : X.tgtName b <;>
          simp [Ctx6.withParH, Ctx6.withPar, Par6.set, Par6.val, Ctx6.parOf, hnm]
      have hPrior : 0 < (X.priorOf H (X.tgtName b)).w (X.trueTarget H b) := by
        rw [htruePar]
        cases hnm : X.tgtName b with
        | initial =>
            change 0 < X.initLaw.w H.1.1
            exact hBase.1
        | candidate w =>
            have hbin : w ∈ X.binsOf Finset.univ := by
              unfold Ctx6.binsOf
              exact Finset.mem_image.mpr ⟨(w, KeyFlag6.interior), Finset.mem_univ _, rfl⟩
            change 0 < (X.candLaw H.1.1).w (H.1.2.1 w)
            exact hBase.2.1 w hbin
      have hHighGate : X.HighGate H b D0 (X.trueTarget H b) := by
        unfold Ctx6.HighGate
        refine ⟨hPrior, ?_, ?_⟩
        · intro ℓ hℓ
          have hkey := hstep1LocKey ℓ hℓ
          simpa [hUpdatePar] using hStep1 ℓ.1 hkey
        · intro e he
          simpa [hUpdatePar] using hStep2 e.2 (hDTypeOcc e he)
      simpa [Ctx6.S3TrueGate, hmode] using hHighGate
  have hTests : X.S3Tests H b D0 (X.tup C) := by
    by_contra hTests
    let F := X.failedSets H C b jFin
    have hFailed : Dids ∈ F := by
      dsimp [F, Ctx6.failedSets]
      apply Finset.mem_image.mpr
      refine ⟨D0, Finset.mem_filter.mpr ⟨hDDesc, ⟨hTrueGate, hTests⟩⟩, ?_⟩
      rfl
    have hDidsNonempty : Dids.Nonempty := by
      rcases hoddNbr with ⟨a, ha⟩
      let a' : X.g.L.stNbr b := ⟨a, ha⟩
      let e : X.Loc × X.Ty :=
        ((X.choice H C X.Rlong a).getD X.defaultLoc, X.stType a)
      have he : e ∈ D0 := by
        change e ∈ Finset.univ.image (fun a : X.g.L.stNbr b =>
          ((X.choice H C X.Rlong a.1).getD X.defaultLoc, X.stType a.1))
        exact Finset.mem_image.mpr ⟨a', Finset.mem_univ _, rfl⟩
      refine ⟨e.1, ?_⟩
      change e.1 ∈ D0.image Prod.fst
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hExistsMax : ∃ 𝓜, IsMaxDisjoint6 F 𝓜 := by
      let goodFamilies : Finset (Finset (Finset X.Loc)) :=
        Finset.univ.filter fun 𝓜 =>
          𝓜 ⊆ F ∧ ∀ A ∈ 𝓜, ∀ B ∈ 𝓜, A ≠ B → Disjoint A B
      have hGood : goodFamilies.Nonempty := by
        refine ⟨∅, ?_⟩
        simp [goodFamilies]
      obtain ⟨𝓜, h𝓜mem, h𝓜max⟩ :=
        Finset.exists_max_image goodFamilies Finset.card hGood
      have h𝓜good := (Finset.mem_filter.mp h𝓜mem).2
      have hMaximal : IsMaxDisjoint6 F 𝓜 := by
        refine ⟨h𝓜good.1, h𝓜good.2, ?_⟩
        intro A hAF hDisj
        by_contra hAnot
        have hSub : insert A 𝓜 ⊆ F := by
          intro B hB
          rcases Finset.mem_insert.mp hB with hBA | hBM
          · simpa [hBA] using hAF
          · exact h𝓜good.1 hBM
        have hPair : ∀ B ∈ insert A 𝓜, ∀ C ∈ insert A 𝓜,
            B ≠ C → Disjoint B C := by
          intro B hB C hC hne
          rcases Finset.mem_insert.mp hB with hBA | hBM <;>
            rcases Finset.mem_insert.mp hC with hCA | hCM
          · subst B
            subst C
            exact (hne rfl).elim
          · subst B
            exact hDisj C hCM
          · subst C
            exact (hDisj B hBM).symm
          · exact h𝓜good.2 B hBM C hCM hne
        have hInsertGood : insert A 𝓜 ∈ goodFamilies := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, ⟨hSub, hPair⟩⟩
        have hCard : 𝓜.card < (insert A 𝓜).card := by simp [hAnot]
        have hMaxCard := h𝓜max (insert A 𝓜) hInsertGood
        omega
      exact ⟨𝓜, hMaximal⟩
    have hChosenMax : IsMaxDisjoint6 F (maxDisjoint6 F) := by
      unfold maxDisjoint6
      by_cases h : ∃ 𝓜, IsMaxDisjoint6 F 𝓜
      · rw [dif_pos h]
        exact Classical.choose_spec h
      · rw [dif_neg h]
        exact (h hExistsMax).elim
    have hIntersect : ∃ B ∈ maxDisjoint6 F, ∃ x ∈ Dids, x ∈ B := by
      by_cases hAin : Dids ∈ maxDisjoint6 F
      · rcases hDidsNonempty with ⟨x, hx⟩
        exact ⟨Dids, hAin, x, hx, hx⟩
      · have hnotAll : ¬ ∀ B ∈ maxDisjoint6 F, Disjoint Dids B := by
          intro hall
          exact hAin (hChosenMax.2.2 Dids hFailed hall)
        push_neg at hnotAll
        rcases hnotAll with ⟨B, hB, hnotDisj⟩
        have hcross : ∃ x ∈ Dids, x ∈ B := by
          rw [Finset.disjoint_left] at hnotDisj
          push_neg at hnotDisj
          exact hnotDisj
        exact ⟨B, hB, hcross⟩
    obtain ⟨B, hB, x, hx, hxB⟩ := hIntersect
    obtain ⟨a, ha, hget⟩ := hDidsMem hx
    obtain ⟨ℓ, hChoice, hEligible, _hActive⟩ := hchoiceData b a ha
    have hℓx : ℓ = x := by simpa [hChoice] using hget
    have hxLevel : x.2 ∈ X.levelPair jFin := by
      rw [← hℓx]
      exact hselectedPair ha hChoice
    let ja : Fin (X.hp.H + 1) := ⟨heightOf a, by
      have hltA : heightOf a < X.hp.H := by
        simpa [heightOf, Ctx6.Rlong] using (hGeo.2.2.2 (X.site a) (hsiteMem ha)).1
      exact Nat.lt_succ_of_lt hltA⟩
    have hja : ja = ℓ.2 := Fin.ext (hselectedLevel ha hChoice).symm
    have hEligibleAt : ℓ ∈ X.elig H C (X.site a) ℓ.2 := by
      rw [← hja]
      exact hEligible
    have hEligibleDiff :
        ℓ ∈ X.prosp (X.pos C) (X.site a) ℓ.2 \ X.marked H C (X.site a) ℓ.2 := by
      simpa [Ctx6.elig] using hEligibleAt
    have hNotMarked : x ∉ X.marked H C (X.site a) x.2 := by
      rw [← hℓx]
      exact (Finset.mem_sdiff.mp hEligibleDiff).2
    have hMarked : x ∈ X.marked H C (X.site a) x.2 := by
      unfold Ctx6.marked
      apply Finset.mem_biUnion.mpr
      refine ⟨b, hbOdd, ?_⟩
      have hSite : X.site a ∈ (X.g.L.stNbr b).image X.site :=
        Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rw [if_pos hSite]
      apply Finset.mem_biUnion.mpr
      refine ⟨jFin, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hxLevel
      · exact Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩
    exact hNotMarked hMarked
  refine ⟨hsome, hcounts, ?_, ?_, ?_, ?_⟩
  · refine ⟨jFin, ?_⟩
    intro a ha ℓ hsel
    exact hselectedPair ha hsel
  · exact hDidsCard
  · exact hTrueGate
  · exact hTests

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
