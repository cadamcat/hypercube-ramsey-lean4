import HypercubeRamsey.S06.Steps
import HypercubeRamsey.S03.ConditionalAvoidance

/-!
# Conditioning stages: global parent, coarse base, hidden scalars

L6.1h (06:449–523).  Each stage restricts only its newly drawn variables at the fixed entering history
(06:452–455).  Alarm variables are raw conditional failure probabilities (06:456–460):

* stage 1 restricts `V₀` to values whose conditional Step 1/2/3 rates lose at most half their exponents;
* stage 2, at a retained `V₀`, conditions the product law of the bin variables on avoiding Step 1 failures and
  the alarms that the future Step 2 or Step 3 probability exceeds its next threshold (events grouped by bin);
* stage 3, at a retained base, conditions the product law of the hidden scalars on avoiding Step 2 failures and
  the alarm that the Step 3 probability over fresh tuples exceeds `e^{−c₂k}` (events grouped by bin and central
  sign, all severities in one group).

The stage laws are explicit restrictions of the raw laws.  The local-lemma certificates (`AvoidCert6`) are the
hypotheses of Lemma 3.4 (`LocalLemma.conditional_avoidance`) with explicit charges, so that later nodes can
remove the constraints touching a local set (06:517–519).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- The hypotheses of Lemma 3.4 for a weight function and an indexed family of bad events, with charges at most
`xmax` (06:493–494, 06:510–519). -/
structure AvoidCert6 {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    (w : Ω → ℝ) (E : I → Finset Ω) (xmax : ℝ) where
  adj : I → I → Prop
  adj_symm : ∀ i j, adj i j → adj j i
  adj_irrefl : ∀ i, ¬ adj i i
  x : I → ℝ
  x_nonneg : ∀ i, 0 ≤ x i
  x_le : ∀ i, x i ≤ xmax
  local_bound : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
    LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) ≤
      (x i * ∏ j ∈ Finset.univ.filter (adj i), (1 - x j)) * LocalLemma.mass w (LocalLemma.avoid E S)

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-! ### Alarm variables (06:456–468) -/

/-- Step 1 failure rate at key `h` given `V₀ = v`. -/
def rate1V0 (v : Fin N) (h : X.Key) : ℝ := (X.coarseLaw v).pr fun c => ¬ X.Step1OK (v, c) h

/-- Step 2 failure rate of type `β` given the base. -/
def rate2Base (b : X.Base) (β : X.Ty) : ℝ := (X.hidLaw b).pr fun Z => X.Step2Fail (b, Z) β

/-- Step 2 failure rate of type `β` given `V₀ = v`. -/
def rate2V0 (v : Fin N) (β : X.Ty) : ℝ := (X.coarseLaw v).expect fun c => X.rate2Base (v, c) β

/-- Step 3 failure probability over independent fresh tuples at an abstract descriptor, given the history. -/
def rate3 (H : X.Hist) (b : X.State) (D : Finset (Fin X.T × X.Ty)) : ℝ :=
  (X.dataLaw (Fin X.T) H).pr fun o => X.S3Fail H b D o

/-- The same, averaged over the raw hidden scalars at a base. -/
def rate3Base (b₀ : X.Base) (b : X.State) (D : Finset (Fin X.T × X.Ty)) : ℝ :=
  (X.hidLaw b₀).expect fun Z => X.rate3 (b₀, Z) b D

/-- The same, averaged over the raw bin variables at `V₀ = v`. -/
def rate3V0 (v : Fin N) (b : X.State) (D : Finset (Fin X.T × X.Ty)) : ℝ :=
  (X.coarseLaw v).expect fun c => X.rate3Base (v, c) b D

/-! ### Stage 1: the global parent (06:470–486) -/

/-- A retained `V₀`: every conditional raw failure probability loses at most half its exponent. -/
def V0Good (v : Fin N) : Prop :=
  (∀ h ∈ X.step1Keys, X.rate1V0 v h ≤ (n : ℝ) ^ (-(δ₁ / 4))) ∧
    (∀ β ∈ X.occTypes, X.rate2V0 v β ≤ (n : ℝ) ^ (-(δ₂ * β.u / 4))) ∧
      ∀ b ∈ X.g.L.oddStates, ∀ D ∈ X.absDescs b, X.rate3V0 v b D ≤ Real.exp (-(9 / 1000) * X.k)

/-- The stage 1 law: `Π'|_{S₀}` restricted to retained values. -/
def stage1Law : Law N := restrictOr6 X.initLaw X.V0Good X.y₀

/-! ### Stage 2: the coarse base (06:488–496) -/

/-- The bad event of bin `w` at stage 2: a Step 1 failure at a key whose relation is read at `w`, or an alarm
that a future Step 2 or Step 3 probability exceeds its next threshold. -/
def Bad2 (v : Fin N) (w : X.Bin) (c : X.Coarse) : Prop :=
  (∃ x : CubeVertex n, (X.g.L.key x).1 = w ∧ ∃ h ∈ X.C (X.g.L.key x), ¬ X.Step1OK (v, c) h) ∨
    (∃ x : CubeVertex n, IsEvenRole x ∧ (X.g.L.key x).1 = w ∧
      (n : ℝ) ^ (-(δ₂ * (X.evenType x).u / 8)) < X.rate2Base (v, c) (X.evenType x)) ∨
      ∃ b ∈ X.g.L.oddStates, (X.g.L.stKey b).1 = w ∧
        ∃ D ∈ X.absDescs b, Real.exp (-(9 / 2000) * X.k) < X.rate3Base (v, c) b D

def bad2Set (v : Fin N) (w : X.Bin) : Finset X.Coarse := Finset.univ.filter (X.Bad2 v w)

def fallbackCoarse : X.Coarse := (fun _ => X.y₀, fun _ => X.i₀)

/-- The stage 2 law: the raw bin variables conditioned on avoiding every stage 2 bad event. -/
def stage2Law (v : Fin N) : FinProb X.Coarse :=
  restrictOr6 (X.coarseLaw v) (fun c => ∀ w, ¬ X.Bad2 v w c) X.fallbackCoarse

/-! ### Stage 3: the hidden scalars (06:498–508) -/

/-- The bad event of the group (bin `w`, central sign `t`) at stage 3. -/
def Bad3 (b₀ : X.Base) (gr : X.Bin × CubeVertex X.m) (Z : X.Hid) : Prop :=
  (∃ x : CubeVertex n, IsEvenRole x ∧ (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.Step2Fail (b₀, Z) (X.evenType x)) ∨
    ∃ b ∈ X.g.L.oddStates, (X.g.L.stKey b).1 = gr.1 ∧ X.g.L.stSign b = gr.2 ∧
      ∃ D ∈ X.absDescs b, Real.exp (-c₂ * X.k) < X.rate3 (b₀, Z) b D

def bad3Set (b₀ : X.Base) (gr : X.Bin × CubeVertex X.m) : Finset X.Hid := Finset.univ.filter (X.Bad3 b₀ gr)

/-- The stage 3 law: the raw hidden scalars conditioned on avoiding every stage 3 bad event. -/
def stage3Law (b₀ : X.Base) : FinProb X.Hid :=
  restrictOr6 (X.hidLaw b₀) (fun Z => ∀ gr, ¬ X.Bad3 b₀ gr Z) (fun _ => X.y₀)

/-- The stagewise law of histories (06:452–455). -/
def histLaw : FinProb X.Hist := FinProb.bind (FinProb.bind X.stage1Law X.stage2Law) X.stage3Law

/-! ### The L6.1h predicates -/

/-- Step 1 and Step 2 rates depend on finitely many shapes: conditional on `V₀`, bins are iid and the hidden laws
do not read signs, so a rate depends only on the local grid shape around the key (up to isomorphism), the flag,
the mode, the severity and `|F|` (06:472–475; "Step 1 has only constantly many shapes"; Step 2 patterns
`m^{O(j+1)}` per severity, 06:294–295).  The pattern exponent `2u` is small against `δ₂u/4` because `α ≤ 10⁻¹²`. -/
def RateShapes12 : Prop :=
  ∃ (Sh : Type) (_ : Fintype Sh) (f₁ : X.Key → Sh) (f₂ : X.Ty → Sh),
    (∀ h h', f₁ h = f₁ h' → ∀ v, X.rate1V0 v h = X.rate1V0 v h') ∧
    (∀ β β', f₂ β = f₂ β' → β.u = β'.u ∧ ∀ v, X.rate2V0 v β = X.rate2V0 v β') ∧
    ((X.step1Keys.image f₁).card : ℝ) ≤ 10 ^ 200 ∧
    ∀ u : ℕ, (((X.occTypes.filter fun β => β.u = u).image f₂).card : ℝ) ≤ 10 ^ 210 * ((X.m : ℝ) + 1) ^ (2 * u)

/-- Step 3 rates at abstract descriptors depend on `exp(O(T log T + (J+1) log m))` shapes (IDs renamed into
`[T]`, central sign translated, fine data at the `O(J+1)` near-mid coordinates; 06:282–292, 06:479–481). -/
def RateShapes3 : Prop :=
  ∃ (Sh : Type) (_ : Fintype Sh) (f₃ : X.State → Finset (Fin X.T × X.Ty) → Sh),
    (∀ b D b' D', f₃ b D = f₃ b' D' → ∀ v, X.rate3V0 v b D = X.rate3V0 v b' D') ∧
    ((X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (f₃ b)).card : ℝ) ≤
      Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2)))

def RateShapes : Prop := X.RateShapes12 ∧ X.RateShapes3

/-- Stage 1 keeps at least half of the initial mass (06:475–486). -/
def V0Mass : Prop := (1 / 2 : ℝ) ≤ X.initLaw.pr X.V0Good

/-- At every retained `V₀` the stage 2 events satisfy Lemma 3.4 with charges `≤ n^{−δ₁/8} → 0` (bounded dependency,
grouped probabilities `O(n^{−δ₁/4})`, 06:488–496, 06:517–518); removing the boundedly many constraints touching a
fixed local set then costs `1 + o(1)`. -/
def CoarseCert : Prop :=
  ∀ v, X.V0Good v → Nonempty (AvoidCert6 (X.coarseLaw v).w (X.bad2Set v) ((n : ℝ) ^ (-(δ₁ / 8))))

/-- At every base in the support of stage 2 at a retained `V₀`, the stage 3 events satisfy Lemma 3.4 with charges
`≤ n^{−c₃/2}`, `c₃ = δ₂/64` (dependency `m^{O(1)}`, 06:498–516). -/
def HiddenCert : Prop :=
  ∀ v c, X.V0Good v → (X.stage2Law v).w c ≠ 0 →
    Nonempty (AvoidCert6 (X.hidLaw (v, c)).w (X.bad3Set (v, c)) ((n : ℝ) ^ (-(δ₂ / 128))))

/-- Every history in the support of the stagewise law passes all Step 1 and Step 2 tests, lies in the raw
support, and has Step 3 rate `≤ e^{−c₂k}` at every abstract descriptor (06:465–468). -/
def HistSupport : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 →
    X.BaseSupp H.1 ∧ (∀ ℓ, 0 < (X.hidPost H.1 ℓ.1).w (H.2 ℓ)) ∧ X.V0Good H.1.1 ∧
      (∀ h ∈ X.step1Keys, X.Step1OK H.1 h) ∧ (∀ β ∈ X.occTypes, X.Step2Tests H β) ∧
        ∀ b ∈ X.g.L.oddStates, ∀ D ∈ X.absDescs b, X.rate3 H b D ≤ Real.exp (-c₂ * X.k)

/-- All L6.1h predicates. -/
def StageFacts : Prop := X.V0Mass ∧ X.CoarseCert ∧ X.HiddenCert ∧ X.HistSupport

end Ctx6

/-- L6.1h (shapes, Steps 1–2, 06:472–475, 06:294–295): measure-preserving bin renamings (iid bins given `V₀`),
sign translations and fine-chunk permutations of the raw experiment. -/
theorem L6_1h_shapes12 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.RateShapes12 := by
  sorry

/-- L6.1h (shapes, Step 3, 06:282–292, 06:479–481): the same symmetries act on abstract descriptors; the count of
abstract descriptors per coarse shape and central sign. -/
theorem L6_1h_shapes3 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes3 := by
  sorry

/-- L6.1h (parent, 06:470–486): Markov on each shape and the unions over shapes; `E_v rate = raw rate`. -/
theorem L6_1h_parent (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.Step1CapBound → X.Step1DelBound → X.Step2Bound → X.Step3TestLow → X.Step3TestHigh → X.DescSize →
        X.RateShapes → X.V0Mass := by
  sorry

/-- L6.1h (coarse base, 06:488–496): grouped probabilities `o(1)` from stage 1 and Markov (conditional future
probabilities have the same sign symmetry given the base, so a bin's union runs over shapes), bounded dependency
degree. -/
theorem L6_1h_coarse (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes → X.CoarseCert := by
  sorry

/-- L6.1h (hidden scalars, 06:498–516): group probabilities `≤ n^{−c₃}` after the pattern unions, dependency
`m^C = n^{Cα + o(1)}`, `Cα < c₃/4`, charges `n^{−c₃/2}`. -/
theorem L6_1h_hidden (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes → X.HiddenCert := by
  sorry

/-- L6.1h (support, 06:465–468, 06:520–523): positivity of the avoidance masses (Lemma 3.4) makes the stage laws
genuine restrictions; the avoided events are exactly the failures; the Step 2 true gate is a Step 1 test. -/
theorem L6_1h_support (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.V0Mass → X.CoarseCert → X.HiddenCert → X.HistSupport := by
  sorry

/-- L6.1h assembled from its nodes and Steps 1–3. -/
theorem stageFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StepFacts → X.StageFacts := by
  have h := (L6_1h_shapes12 γ p₀ K hadm).and <| (L6_1h_shapes3 γ p₀ K hadm).and <| (L6_1h_parent γ p₀ K hadm).and <|
    (L6_1h_coarse γ p₀ K hadm).and <| (L6_1h_hidden γ p₀ K hadm).and (L6_1h_support γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hSh12, hSh3, hPa, hCo, hHi, hSu⟩ ⟨_hT, hC, hD, h2, _h2d, _h2s, hS, hN, h3l, h3h, _hbl, _hbh⟩
  have hshape : X.RateShapes := ⟨hSh12, hSh3 hN⟩
  have hmass := hPa hC hD h2 h3l h3h hS hshape
  have hco := hCo hN hshape
  have hhi := hHi hN hshape
  exact ⟨hmass, hco, hhi, hSu hmass hco hhi⟩

end

end S06
end HypercubeRamsey
