import HypercubeRamsey.Framework.OneShot

/-!
# Section 6 finite experiment and vocabulary

L6.1-Defs (06:78–157).  The raw experiment keeps variable names separate from
their realized labels.  In particular a primary is named by `ParentName6`,
and the fresh tag and all entries of a centre tuple form one observation.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open scoped BigOperators

noncomputable def c₀ : ℝ := 1 / 100
noncomputable def c₁ : ℝ := c₀ / 2
noncomputable def κ₆ : ℝ := 1 / 10000
def coarseChunkCount : ℕ := 300
noncomputable def fineMargin : ℝ := 5.5

inductive KeyFlag6 where
  | interior
  | boundary
  deriving DecidableEq

instance : Fintype KeyFlag6 := by
  refine ⟨{KeyFlag6.interior, KeyFlag6.boundary}, ?_⟩
  intro x
  cases x <;> simp

abbrev CoarseKey6 (W : Type*) := W × KeyFlag6

/-- The coarse relation includes each key, both flags at one bin, and adjacent boundary bins. -/
def keyAdjacent6 {W : Type*} (binAdjacent : W → W → Prop)
    (a b : CoarseKey6 W) : Prop :=
  a = b ∨ a.1 = b.1 ∨
    (a.2 = .boundary ∧ b.2 = .boundary ∧ binAdjacent a.1 b.1)

noncomputable def keyNeighborhood6 {W : Type*} [Fintype W] [DecidableEq W]
    (binAdjacent : W → W → Prop) [DecidableRel binAdjacent] (h : CoarseKey6 W) :
    Finset (CoarseKey6 W) :=
  by
    classical
    exact Finset.univ.filter (keyAdjacent6 binAdjacent h)

inductive ParentName6 (W : Type*) where
  | initial
  | candidate (w : W)
  deriving DecidableEq

/-- Primaries are named random variables; equality of their values does not merge their names. -/
def primaryName6 {W : Type*} (h : CoarseKey6 W) : ParentName6 W :=
  match h.2 with
  | .interior => .candidate h.1
  | .boundary => .initial

def otherPrimaryName6 {W : Type*} (h : CoarseKey6 W) : ParentName6 W :=
  match h.2 with
  | .interior => .initial
  | .boundary => .candidate h.1

structure Parents6 (W : Type*) (N : ℕ) where
  initial : Fin N
  candidate : W → Fin N

def Parents6.value {W : Type*} {N : ℕ} (p : Parents6 W N) : ParentName6 W → Fin N
  | .initial => p.initial
  | .candidate w => p.candidate w

def primary6 {W : Type*} {N : ℕ} (p : Parents6 W N) (h : CoarseKey6 W) : Fin N :=
  p.value (primaryName6 h)

def otherPrimary6 {W : Type*} {N : ℕ} (p : Parents6 W N) (h : CoarseKey6 W) : Fin N :=
  p.value (otherPrimaryName6 h)

abbrev HiddenKey6 (W : Type*) (m : ℕ) := CoarseKey6 W × CubeVertex m

inductive Mode6 where
  | low
  | high
  deriving DecidableEq

instance : Fintype Mode6 := by
  refine ⟨{Mode6.low, Mode6.high}, ?_⟩
  intro x
  cases x <;> simp

/-- The observation type of an even role; `observations` is its explicit padded hidden-key list. -/
structure Type6 (W : Type*) (m : ℕ) where
  key : CoarseKey6 W
  sign : CubeVertex m
  mode : Mode6
  severity : ℕ
  observations : Finset (HiddenKey6 W m)

def Type6.uBeta {W : Type*} {m : ℕ} (β : Type6 W m) : ℕ :=
  match β.mode with
  | .low => β.severity + 1
  | .high => 1

/-- A tuple is observed as a single fresh tag together with all of its entries. -/
abbrev TaggedTuple6 (ι : Type*) (k N : ℕ) := ι × (Fin k → Fin N)

structure Fallback6 (ι : Type*) (k N : ℕ) where
  tag : ι
  retained : Finset (Fin N)
  label : Fin N
  label_mem : label ∈ retained

def Fallback6.tuple {ι : Type*} {k N : ℕ} (f : Fallback6 ι k N) : TaggedTuple6 ι k N :=
  (f.tag, fun _ => f.label)

/-- Condition a finite law on a hit set; the fixed retained label is used off the support. -/
noncomputable def hitRestrictedLaw6 {N : ℕ} (μ : Law N) (hits : Finset (Fin N))
    (fallback : Fin N) : Law N := by
  classical
  let mass := ∑ x ∈ hits, μ.w x
  exact if h : 0 < mass then μ.restrict hits h else Law.dirac fallback

abbrev ParentHistory6 (W : Type*) (N : ℕ) := Fin N × (W → Fin N)
abbrev BaseHistory6 (W : Type*) (N : ℕ) (ι : Type*) :=
  ParentHistory6 W N × (CoarseKey6 W → ι)
abbrev HiddenHistory6 (W : Type*) (m N : ℕ) (ι : Type*) :=
  BaseHistory6 W N ι × (HiddenKey6 W m → Fin N)
abbrev RawSample6 (W : Type*) (m N k : ℕ) (ι Center Ty : Type*) :=
  HiddenHistory6 W m N ι × (Center × Ty → TaggedTuple6 ι k N)

/-- Finite kernels for the four successive stages of the raw experiment. -/
structure RawKernels6 (W : Type*) (m N k : ℕ) (ι Center Ty : Type*)
    [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]
    [Fintype Center] [DecidableEq Center] [Fintype Ty] [DecidableEq Ty] where
  initial : Law N
  candidate : Fin N → W → Law N
  baseTag : ParentHistory6 W N → CoarseKey6 W → FinProb ι
  hidden : BaseHistory6 W N ι → HiddenKey6 W m → Law N
  μ : ι → Law N
  tupleTag : HiddenHistory6 W m N ι → Center × Ty → FinProb ι
  tupleRequiredHits : HiddenHistory6 W m N ι → Center × Ty → ι → Finset (Fin N)
  fallback : Fallback6 ι k N

namespace RawKernels6

variable {W : Type*} {m N k : ℕ} {ι Center Ty : Type*}
  [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]
  [Fintype Center] [DecidableEq Center] [Fintype Ty] [DecidableEq Ty]

noncomputable def candidateProduct (K : RawKernels6 W m N k ι Center Ty) (v₀ : Fin N) :
    FinProb (W → Fin N) :=
  FinProb.pi (fun w => K.candidate v₀ w)

noncomputable def parents (K : RawKernels6 W m N k ι Center Ty) :
    FinProb (ParentHistory6 W N) :=
  FinProb.bind K.initial (fun v₀ => K.candidateProduct v₀)

noncomputable def baseTags (K : RawKernels6 W m N k ι Center Ty)
    (p : ParentHistory6 W N) : FinProb (CoarseKey6 W → ι) :=
  FinProb.pi (K.baseTag p)

noncomputable def base (K : RawKernels6 W m N k ι Center Ty) :
    FinProb (BaseHistory6 W N ι) :=
  FinProb.bind K.parents K.baseTags

noncomputable def hiddenScalars (K : RawKernels6 W m N k ι Center Ty)
    (b : BaseHistory6 W N ι) : FinProb (HiddenKey6 W m → Fin N) :=
  FinProb.pi (K.hidden b)

noncomputable def throughHidden (K : RawKernels6 W m N k ι Center Ty) :
    FinProb (HiddenHistory6 W m N ι) :=
  FinProb.bind K.base K.hiddenScalars

noncomputable def centreTuples (K : RawKernels6 W m N k ι Center Ty)
    (h : HiddenHistory6 W m N ι) : FinProb (Center × Ty → TaggedTuple6 ι k N) :=
  FinProb.pi (fun c => FinProb.bind (K.tupleTag h c) fun i =>
    FinProb.pi (fun _ : Fin k =>
      hitRestrictedLaw6 (K.μ i) (K.tupleRequiredHits h c i) K.fallback.label))

/-- The raw order is parents, independent base tags, independent hidden scalars, then tagged tuples. -/
noncomputable def raw (K : RawKernels6 W m N k ι Center Ty) :
    FinProb (RawSample6 W m N k ι Center Ty) :=
  FinProb.bind K.throughHidden K.centreTuples

end RawKernels6

/-! ### Mixture and posterior vocabulary -/

noncomputable def tagLaw6 {N : ℕ} (M : TagMix N) : FinProb M.ι where
  w := M.Λ
  nonneg := M.Λ_nonneg
  sum_eq_one := M.Λ_sum

noncomputable def secondMixture6 {N : ℕ} (M : TagMix N) : Law N :=
  Law.mix (tagLaw6 M) M.ν

noncomputable def tagPosterior6 {N : ℕ} (M : TagMix N) (y : Fin N) : FinProb M.ι := by
  classical
  by_cases hy : 0 < (secondMixture6 M).w y
  · refine ⟨fun i => M.Λ i * (M.ν i).w y / (secondMixture6 M).w y, ?_, ?_⟩
    · intro i
      exact div_nonneg (mul_nonneg (M.Λ_nonneg i) ((M.ν i).nonneg y))
        (le_of_lt hy)
    · have hsum : (∑ i, M.Λ i * (M.ν i).w y) = (secondMixture6 M).w y := by
        rfl
      calc
        ∑ i, M.Λ i * (M.ν i).w y / (secondMixture6 M).w y =
            (∑ i, M.Λ i * (M.ν i).w y) / (secondMixture6 M).w y := by
              rw [Finset.sum_div]
        _ = 1 := by rw [hsum]; exact div_self (ne_of_gt hy)
  · exact tagLaw6 M

noncomputable def broadLaw6 {N : ℕ} (M : TagMix N) (y : Fin N) : Law N :=
  Law.mix (tagPosterior6 M y) M.μ

def tagSupported6 {N : ℕ} (M : TagMix N) (i : M.ι) : Prop :=
  0 < M.Λ i

noncomputable def pointMass6 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) : FinProb Ω where
  w b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> positivity
  sum_eq_one := by simp

/-- Bayes tag posterior restricted to tags whose first law sees the opposite primary at density `c₁`.
If the restriction is undefined off the supported parent history, use the fixed, ID-independent fallback. -/
noncomputable def baseTagLaw6 {N : ℕ} (M : TagMix N) (E : Fin N → Fin N → Prop) (G : Colour)
    (parent opposite : Fin N) (fallback : M.ι) : FinProb M.ι := by
  classical
  let η := tagPosterior6 M parent
  let good : M.ι → Prop := fun i => c₁ ≤ colDeg E G (M.μ i) opposite
  exact if h : 0 < η.pr good then η.cond good h else pointMass6 fallback

/-- `Π'` conditioned on the relation-partner set, with a fixed fallback off the supported history. -/
noncomputable def partnerLaw6 {N : ℕ} (piPrime : Law N)
    (related : Fin N → Fin N → Prop) (y fallback : Fin N) : Law N := by
  classical
  let partners := Finset.univ.filter (related y)
  let mass := ∑ z ∈ partners, piPrime.w z
  exact if h : 0 < mass then piPrime.restrict partners h else Law.dirac fallback

/-- A zero-safe likelihood ratio; posterior ratios are only used on their reference support. -/
noncomputable def safeRatio6 (a b : ℝ) : ℝ := if b = 0 then 0 else a / b

/-- Step 2's tagged posterior integrand for a type and its complete observation list. -/
noncomputable def step2Weight6 {N : ℕ} {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]
    (T₀ : FinProb ι) (good : Finset ι) (S : Finset H) (z : H → Fin N)
    (withTag : ι → H → Law N) (withoutTag : H → Law N) (i : ι) : ℝ := by
  classical
  exact if i ∈ good then
    T₀.w i * ∏ ℓ ∈ S,
      safeRatio6 ((withTag i ℓ).w (z ℓ)) ((withoutTag ℓ).w (z ℓ))
    else 0

noncomputable def step2Mass6 {N : ℕ} {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]
    (T₀ : FinProb ι) (good : Finset ι) (S : Finset H) (z : H → Fin N)
    (withTag : ι → H → Law N) (withoutTag : H → Law N) : ℝ :=
  ∑ i, step2Weight6 T₀ good S z withTag withoutTag i

/-- The normalized Step 2 law `T_β`; the fallback applies only when the gated normalizer is zero. -/
noncomputable def step2TagLaw6 {N : ℕ} {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]
    (T₀ : FinProb ι) (good : Finset ι) (S : Finset H) (z : H → Fin N)
    (withTag : ι → H → Law N) (withoutTag : H → Law N) (fallback : ι) : FinProb ι := by
  classical
  let weight := step2Weight6 T₀ good S z withTag withoutTag
  let mass := ∑ i, weight i
  by_cases hm : 0 < mass
  · refine ⟨fun i => weight i / mass, ?_, ?_⟩
    · intro i
      have hweight : 0 ≤ weight i := by
        dsimp [weight, step2Weight6]
        split_ifs with hi
        · apply mul_nonneg (T₀.nonneg i)
          apply Finset.prod_nonneg
          intro ℓ hℓ
          dsimp [safeRatio6]
          split_ifs
          · positivity
          · exact div_nonneg ((withTag i ℓ).nonneg (z ℓ))
              ((withoutTag ℓ).nonneg (z ℓ))
        · exact le_rfl
      exact div_nonneg hweight hm.le
    · calc
        ∑ i, weight i / mass = (∑ i, weight i) / mass := by rw [Finset.sum_div]
        _ = 1 := by dsimp [mass]; exact div_self (ne_of_gt hm)
  · exact pointMass6 fallback

/-- Observation keys of a low role: its coarse neighborhood at the same sign, and the flippable fine signs. -/
noncomputable def lowObservations6 {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (binAdjacent : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m)
    (F : Finset (Fin m)) : Finset (HiddenKey6 W m) := by
  classical
  let sameSign := (keyNeighborhood6 binAdjacent h).product {t}
  let flipped := F.biUnion fun a => {(h, Function.update t a (!t a))}
  exact sameSign ∪ flipped

noncomputable def highObservations6 {W : Type*} {m : ℕ}
    (h : CoarseKey6 W) (t : CubeVertex m) (j J : ℕ) : Finset (HiddenKey6 W m) := by
  classical
  exact if j = J + 1 then {(h, t)} else ∅

/-- Full low/high type constructor used for even-role tuple sampling. -/
noncomputable def makeType6 {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (binAdjacent : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m)
    (F : Finset (Fin m)) (j J : ℕ) : Type6 W m :=
  if _hlow : j ≤ J then
    ⟨h, t, .low, j, lowObservations6 binAdjacent h t F⟩
  else
    ⟨h, t, .high, j, highObservations6 h t j J⟩

/-! ### L6.1-Defs: the named variables, posterior slots, and tuple observations -/

/-- Posterior slots used in the definition of a hidden scalar. -/
structure HiddenPosteriorSlots6 {W : Type*} {m N : ℕ} {ι : Type*}
    (base : BaseHistory6 W N ι) (ℓ : HiddenKey6 W m) where
  full : Law N
  withoutTag : CoarseKey6 W → Law N
  withReplacement : CoarseKey6 W → ι → Law N

/-- The full type data used by the Step 2 tag posterior. -/
structure TagPosteriorSlots6 {W : Type*} {m N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (base : BaseHistory6 W N ι) (β : Type6 W m) where
  goodTags : Finset ι
  fullMass : ℝ
  deletedMass : HiddenKey6 W m → ℝ
  posterior : FinProb ι
  deletedPosterior : HiddenKey6 W m → FinProb ι

noncomputable def step1GoodTags6 {N : ℕ} {ι H : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (d₁ : ℝ) (S : Finset H) (fullWithoutTag : H → Law N)
    (withReplacement : ι → H → Law N) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ ℓ ∈ S, ∀ x,
    (N : ℝ) * (withReplacement i ℓ).w x ≤ (n : ℝ) ^ d₁ ∧
      (withReplacement i ℓ).w x ≤ (n : ℝ) ^ d₁ * (fullWithoutTag ℓ).w x

/-- The realized hidden columns determine the named primary and its required hit list. -/
noncomputable def requiredHits6 {W : Type*} {m N : ℕ} {ι : Type*}
    (history : HiddenHistory6 W m N ι) (β : Type6 W m) : Finset (Fin N) := by
  classical
  let p : Parents6 W N := ⟨history.1.1.1, history.1.1.2⟩
  let primary : Finset (Fin N) := {primary6 p β.key}
  let hidden : Finset (Fin N) := β.observations.image history.2
  let second : Finset (Fin N) :=
    if β.mode = .high then {otherPrimary6 p β.key} else ∅
  exact primary ∪ hidden ∪ second

/--
L6.1-Defs.  The parent and tag kernels are fixed by Bayes restriction, the
hidden scalar is the named parent posterior, Step 2 is the normalized gated
likelihood product, and each tuple is a fresh tag followed by iid labels
conditioned to hit exactly its required named columns.  Undefined
conditionals use the fixed fallback tag/retained label, independent of ID
and sign; `raw` preserves the paper's four-stage order.
-/
structure Definitions6 (n : ℕ) (W : Type*) (m N k : ℕ) (M : TagMix N)
    (E : Fin N → Fin N → Prop) (G : Colour) (Center Ty : Type*)
    [Fintype W] [DecidableEq W] [DecidableEq M.ι] [Fintype Center] [DecidableEq Center]
    [Fintype Ty] [DecidableEq Ty] where
  kernels : RawKernels6 W m N k M.ι Center Ty
  π' : Law N
  parentRelation : Fin N → Fin N → Prop
  S₀ : Finset (Fin N)
  S₀_mass_pos : 0 < ∑ y ∈ S₀, π'.w y
  initial_exact : kernels.initial = π'.restrict S₀ S₀_mass_pos
  candidate_exact : ∀ v₀ w,
    kernels.candidate v₀ w = partnerLaw6 π' parentRelation v₀ kernels.fallback.label
  baseTag_exact : ∀ p h,
    kernels.baseTag p h = baseTagLaw6 M E G
      (Parents6.value ⟨p.1, p.2⟩ (primaryName6 h))
      (Parents6.value ⟨p.1, p.2⟩ (otherPrimaryName6 h)) kernels.fallback.tag
  d₁ : ℝ
  hiddenSlots : ∀ (b : BaseHistory6 W N M.ι) (ℓ : HiddenKey6 W m),
    HiddenPosteriorSlots6 b ℓ
  hidden_exact : ∀ b ℓ, kernels.hidden b ℓ = (hiddenSlots b ℓ).full
  step2Good : BaseHistory6 W N M.ι → Type6 W m → Finset M.ι
  step2Slots : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m),
    TagPosteriorSlots6 h.1 β
  step2_good_exact : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m),
    step2Good h.1 β = step1GoodTags6 n d₁ β.observations
    (fun ℓ => (hiddenSlots h.1 ℓ).withoutTag β.key)
    (fun i ℓ => (hiddenSlots h.1 ℓ).withReplacement β.key i)
  step2_full_mass_exact : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m),
    (step2Slots h β).fullMass = step2Mass6
      (kernels.baseTag h.1.1 β.key) (step2Good h.1 β) β.observations h.2
      (fun i ℓ => (hiddenSlots h.1 ℓ).withReplacement β.key i)
      (fun ℓ => (hiddenSlots h.1 ℓ).withoutTag β.key)
  step2_deleted_mass_exact : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m) ℓ,
    (step2Slots h β).deletedMass ℓ = step2Mass6
      (kernels.baseTag h.1.1 β.key) (step2Good h.1 β) (β.observations.erase ℓ) h.2
      (fun i ℓ' => (hiddenSlots h.1 ℓ').withReplacement β.key i)
      (fun ℓ' => (hiddenSlots h.1 ℓ').withoutTag β.key)
  step2_posterior_exact : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m),
    (step2Slots h β).posterior = step2TagLaw6
      (kernels.baseTag h.1.1 β.key) (step2Good h.1 β) β.observations h.2
      (fun i ℓ => (hiddenSlots h.1 ℓ).withReplacement β.key i)
      (fun ℓ => (hiddenSlots h.1 ℓ).withoutTag β.key) kernels.fallback.tag
  step2_deleted_posterior_exact : ∀ (h : HiddenHistory6 W m N M.ι) (β : Type6 W m) ℓ,
    (step2Slots h β).deletedPosterior ℓ = step2TagLaw6
      (kernels.baseTag h.1.1 β.key) (step2Good h.1 β) (β.observations.erase ℓ) h.2
      (fun i ℓ' => (hiddenSlots h.1 ℓ').withReplacement β.key i)
      (fun ℓ' => (hiddenSlots h.1 ℓ').withoutTag β.key) kernels.fallback.tag
  typeOf : Ty → Type6 W m
  tupleTag_exact : ∀ (h : HiddenHistory6 W m N M.ι) (c : Center × Ty),
    kernels.tupleTag h c = (step2Slots h (typeOf c.2)).posterior
  tupleRequiredHits_exact : ∀ (h : HiddenHistory6 W m N M.ι) (c : Center × Ty) i,
    kernels.tupleRequiredHits h c i = requiredHits6 h (typeOf c.2)

theorem fallback6_is_id_independent {ι Id : Type*} {k N : ℕ} (f : Fallback6 ι k N)
    (_c _c' : Id) : f.tuple = f.tuple := rfl

theorem fallback6_is_sign_independent {ι Sign : Type*} {k N : ℕ} (f : Fallback6 ι k N)
    (_t _t' : Sign) : f.tuple = f.tuple := rfl

end S06
end HypercubeRamsey
