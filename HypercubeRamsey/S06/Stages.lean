import HypercubeRamsey.S06.Steps
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S06.Stages_q_s06_stages
import HypercubeRamsey.S06.Stages_sol_s06_shapes

open HypercubeRamsey.Lane_q_s06_stages

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
  have hmTail := m₆_nat_tendsto_atTop p₀ hadm.2.2.1
  obtain ⟨nM,hnM⟩ := Filter.eventually_atTop.1 (hmTail.eventually (Filter.eventually_ge_atTop 603))
  refine ⟨max 4 nM, 0, ?_⟩
  intro n N E G M X hLarge
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hm603 : 603 ≤ X.g.L.m := by
    rw [X.g.m_eq]
    exact hnM n (le_trans (le_max_right _ _) hLarge.1)
  let Sh : Type := (KeyFlag6 × Fin 603) ⊕ (Lane_sol_s06_shapes.Step2Shape X.g.L.m ⊕ X.Ty)
  letI : DecidableEq Sh := Classical.decEq _
  let f₁ : X.Key → Sh := fun h => Sum.inl (Lane_sol_s06_shapes.step1Shape X h)
  let f₂ : X.Ty → Sh := fun β => Sum.inr (Lane_sol_s06_shapes.taggedStep2Shape X β)
  refine ⟨Sh, inferInstance, f₁, f₂, ?_, ?_, ?_, ?_⟩
  · intro h h' heq v
    exact Lane_sol_s06_shapes.step1Rate_shape X h h' (Sum.inl.inj heq) v
  · intro β β' heq
    have hr := Lane_sol_s06_shapes.taggedStep2Shape_rates X hn4 β β' (Sum.inr.inj heq)
    exact ⟨hr.1,hr.2⟩
  · have hc : (X.step1Keys.image f₁).card =
        (X.step1Keys.image (Lane_sol_s06_shapes.step1Shape X)).card := by
      have h := Finset.card_image_of_injective
        (X.step1Keys.image (Lane_sol_s06_shapes.step1Shape X))
        (show Function.Injective (Sum.inl : (KeyFlag6 × Fin 603) → Sh) from fun _ _ h => Sum.inl.inj h)
      simpa only [Finset.image_image,Function.comp_def,f₁] using h
    rw [hc]
    exact Lane_sol_s06_shapes.step1Shape_card_bound X
  · intro u
    have hc : ((X.occTypes.filter fun β => β.u = u).image f₂).card ≤
        ((X.occTypes.filter fun β => β.u = u).image (Lane_sol_s06_shapes.taggedStep2Shape X)).card := by
      have h := Finset.card_image_le (s := (X.occTypes.filter fun β => β.u = u).image
        (Lane_sol_s06_shapes.taggedStep2Shape X)) (f := fun c => (Sum.inr c : Sh))
      simpa only [Finset.image_image,Function.comp_def,f₂] using h
    have hcR : (((X.occTypes.filter fun β => β.u = u).image f₂).card : ℝ) ≤
        (((X.occTypes.filter fun β => β.u = u).image (Lane_sol_s06_shapes.taggedStep2Shape X)).card : ℝ) := by
      exact_mod_cast hc
    exact hcR.trans (Lane_sol_s06_shapes.taggedStep2Shape_card_bound X hm603 u)

/-- L6.1h (shapes, Step 3, 06:282–292, 06:479–481): the same symmetries act on abstract descriptors; the count of
abstract descriptors per coarse shape and central sign. -/
theorem L6_1h_shapes3 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes3 := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hDesc
  let Sh : Type := (X.Key × Mode6 × CubeVertex X.m) × Finset (Fin X.T × X.Ty)
  let f₃ : X.State → Finset (Fin X.T × X.Ty) → Sh :=
    fun b D => (Lane_sol_s06_shapes.targetShape X b, D)
  refine ⟨Sh, inferInstance, f₃, ?_, ?_⟩
  · intro b D b' D' heq v
    have hb : Lane_sol_s06_shapes.targetShape X b = Lane_sol_s06_shapes.targetShape X b' :=
      congrArg Prod.fst heq
    have hD : D = D' := congrArg Prod.snd heq
    subst D'
    exact Lane_sol_s06_shapes.step3V0Rate_targetShape X b b' hb v D
  · sorry

set_option maxHeartbeats 10000000
/-- L6.1h (parent, 06:470–486): Markov on each shape and the unions over shapes; `E_v rate = raw rate`. -/
theorem L6_1h_parent (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.Step1CapBound → X.Step1DelBound → X.Step2Bound → X.Step3TestLow → X.Step3TestHigh → X.DescSize →
        X.RateShapes → X.V0Mass := by
  have hTail1 : ∀ᶠ n : ℕ in Filter.atTop,
      (10 ^ 200 : ℝ) * 603 * (n : ℝ) ^ (-(δ₁ / 4)) < 1 / 6 :=
    eventually_const_mul_nat_rpow_neg_lt
      (by norm_num [δ₁]) (by norm_num)
  obtain ⟨nTail1, hTail1⟩ := Filter.eventually_atTop.1 hTail1
  obtain ⟨_, _, hp₀, _⟩ := hadm
  have hαfacts := height_exponents6_admissible p₀ hp₀
  have hαpos : 0 < α₆ p₀ := hαfacts.1
  have hαupper : α₆ p₀ ≤ 1 / 10 ^ 12 := hαfacts.2.2.1
  have hMnat := m₆_nat_tendsto_atTop p₀ hp₀
  have hTJevent := hMnat.eventually eventually_T₆_le_J₆
  obtain ⟨nTJ, hTJevent⟩ := Filter.eventually_atTop.1 hTJevent
  have hMEventually := eventually_nat_ceil_rpow_add_two_le_double hαpos
  obtain ⟨nM, hMEventually⟩ := Filter.eventually_atTop.1 hMEventually
  have hexp2pos : 0 < δ₂ / 4 - 6 * α₆ p₀ := by
    norm_num [δ₂] at *
    nlinarith
  have hTail2 : ∀ᶠ n : ℕ in Filter.atTop,
      (10 ^ 210 : ℝ) * (n : ℝ) ^ (-(δ₂ / 4 - 6 * α₆ p₀)) < 1 / 6 :=
    eventually_const_mul_nat_rpow_neg_lt hexp2pos (by norm_num)
  obtain ⟨nTail2, hTail2⟩ := Filter.eventually_atTop.1 hTail2
  have hTail3 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(10 ^ 6 : ℝ)⁻¹) < 1 / 6 :=
    by
      simpa only [one_mul] using (eventually_const_mul_nat_rpow_neg_lt
        (a := (10 ^ 6 : ℝ)⁻¹) (c := 1) (b := 1 / 6) (by positivity) (by norm_num))
  obtain ⟨nTail3, hTail3⟩ := Filter.eventually_atTop.1 hTail3
  have hLogConst : ∀ᶠ n : ℕ in Filter.atTop, (40000 : ℝ) < (n : ℝ) ^ (1 / 10 ^ 8 : ℝ) := by
    have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 ^ 8 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10 ^ 8)).comp
        tendsto_natCast_atTop_atTop
    exact hpow.eventually_gt_atTop 40000
  obtain ⟨nLog, hLogConst⟩ := Filter.eventually_atTop.1 hLogConst
  let nBase := max 2 nM
  let nScale := max nTJ nBase
  let nLogMax := max nLog nScale
  let nTail3Max := max nTail3 nLogMax
  let nTail2Max := max nTail2 nTail3Max
  let n₀ := max nTail1 nTail2Max
  refine ⟨n₀, 0, ?_⟩
  intro n N E G M X hLarge hCap hDel hStep2 hLow hHigh hDesc hRate
  obtain ⟨hn, _, _⟩ := hLarge
  have hnTail1 : nTail1 ≤ n := le_trans (le_max_left nTail1 nTail2Max) hn
  have hnTail2 : nTail2 ≤ n :=
    le_trans (le_trans (le_max_left nTail2 nTail3Max) (le_max_right nTail1 nTail2Max)) hn
  have hnTail3 : nTail3 ≤ n :=
    le_trans (le_trans (le_trans (le_max_left nTail3 nLogMax)
      (le_max_right nTail2 nTail3Max)) (le_max_right nTail1 nTail2Max)) hn
  have hnLog : nLog ≤ n :=
    le_trans (le_trans (le_trans (le_max_left nLog nScale)
      (le_max_right nTail3 nLogMax))
      (le_max_right nTail2 nTail3Max))
      (le_trans (le_max_right nTail1 nTail2Max) hn)
  have hnTJ : nTJ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left nTJ nBase)
      (le_max_right nLog nScale)) (le_max_right nTail3 nLogMax))
      (le_trans (le_max_right nTail2 nTail3Max)
        (le_trans (le_max_right nTail1 nTail2Max) hn))
  have hnM : nM ≤ n :=
    le_trans (le_trans (le_trans (le_max_right 2 nM)
      (le_max_right nTJ nBase)) (le_max_right nLog nScale))
      (le_trans (le_max_right nTail3 nLogMax)
        (le_trans (le_max_right nTail2 nTail3Max)
          (le_trans (le_max_right nTail1 nTail2Max) hn)))
  have hStep1Raw : ∀ h, h ∈ X.step1Keys →
      X.baseLaw.pr (fun b => ¬ X.Step1OK b h) ≤ 603 * (n : ℝ) ^ (-(δ₁ / 2)) := by
    intro h hh
    have hsubset : ∀ b, (¬ X.Step1OK b h) →
        (¬ X.Step1Cap b h) ∨ ∃ s ∈ X.C h, ¬ X.Step1Del b h s := by
      intro b hb
      by_cases hcapb : X.Step1Cap b h
      · right
        by_contra hdel
        apply hb
        refine ⟨hcapb, ?_⟩
        intro s hs
        by_contra hfail
        exact hdel ⟨s, hs, hfail⟩
      · exact Or.inl hcapb
    have hfail := pr_mono X.baseLaw hsubset
    have hcap := hCap h hh
    have hdel : X.baseLaw.pr (fun b => ∃ s ∈ X.C h, ¬ X.Step1Del b h s) ≤
        (X.C h).card * ((n : ℝ) ^ (-(δ₁ / 2))) := by
      calc
        X.baseLaw.pr (fun b => ∃ s ∈ X.C h, ¬ X.Step1Del b h s) ≤
            ∑ s ∈ X.C h, X.baseLaw.pr (fun b => ¬ X.Step1Del b h s) :=
          pr_exists_finset_le X.baseLaw (X.C h) (fun s b => ¬ X.Step1Del b h s)
        _ ≤ ∑ s ∈ X.C h, (n : ℝ) ^ (-(δ₁ / 2)) := by
          apply Finset.sum_le_sum
          intro s hs
          exact hDel h hh s hs
        _ = (X.C h).card * ((n : ℝ) ^ (-(δ₁ / 2))) := by simp
    have hCcard : ((X.C h).card : ℝ) ≤ 602 := by
      have h := X.g.flips.key_neighborhood_card h
      exact_mod_cast h
    have hpow : 0 ≤ (n : ℝ) ^ (-(δ₁ / 2)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hdel' : X.baseLaw.pr (fun b => ∃ s ∈ X.C h, ¬ X.Step1Del b h s) ≤
        602 * ((n : ℝ) ^ (-(δ₁ / 2))) := by
      exact hdel.trans (mul_le_mul_of_nonneg_right hCcard hpow)
    have hu := FinProb.pr_union X.baseLaw (fun b => ¬ X.Step1Cap b h)
      (fun b => ∃ s ∈ X.C h, ¬ X.Step1Del b h s)
    calc
      X.baseLaw.pr (fun b => ¬ X.Step1OK b h) ≤
          X.baseLaw.pr (fun b => ¬ X.Step1Cap b h ∨ ∃ s ∈ X.C h, ¬ X.Step1Del b h s) := hfail
      _ ≤ X.baseLaw.pr (fun b => ¬ X.Step1Cap b h) +
            X.baseLaw.pr (fun b => ∃ s ∈ X.C h, ¬ X.Step1Del b h s) := hu
      _ ≤ (n : ℝ) ^ (-(δ₁ / 2)) + 602 * ((n : ℝ) ^ (-(δ₁ / 2))) := by linarith
      _ = 603 * ((n : ℝ) ^ (-(δ₁ / 2))) := by ring
  have hrate1Mean : ∀ h, X.initLaw.expect (fun v => X.rate1V0 v h) =
      X.baseLaw.pr (fun b => ¬ X.Step1OK b h) := by
    intro h
    simpa [Ctx6.baseLaw, Ctx6.rate1V0] using
      (bind_pr X.initLaw X.coarseLaw (fun v c => ¬ X.Step1OK (v, c) h)).symm
  have hrate2Mean : ∀ β, X.initLaw.expect (fun v => X.rate2V0 v β) =
      X.rawHist.pr (fun H => X.Step2Fail H β) := by
    intro β
    calc
      X.initLaw.expect (fun v => X.rate2V0 v β) =
          X.baseLaw.expect (fun b => X.rate2Base b β) := by
        change (∑ v, X.initLaw.w v * (X.coarseLaw v).expect (fun c => X.rate2Base (v, c) β)) =
          (FinProb.bind X.initLaw X.coarseLaw).expect (fun vc => X.rate2Base vc β)
        exact (FinProb.bind_expect X.initLaw X.coarseLaw
          (fun v c => X.rate2Base (v, c) β)).symm
      _ = X.rawHist.pr (fun H => X.Step2Fail H β) := by
        simpa [Ctx6.rawHist, Ctx6.rate2Base] using
          (bind_pr X.baseLaw X.hidLaw (fun b Z => X.Step2Fail (b, Z) β)).symm
  have hAbsTypes : ∀ b D, D ∈ X.absDescs b →
      ∀ e, e ∈ D → e.2 ∈ X.occTypes := by
    intro b D hD e he
    change D ∈ X.descsIn b (fun _ : X.g.L.stNbr b => Finset.univ) at hD
    rcases Finset.mem_image.mp hD with ⟨φ, hφ, hDdef⟩
    have he' : e ∈ X.descOf b φ := by simpa [hDdef] using he
    rcases Finset.mem_image.mp he' with ⟨a, ha, heq⟩
    have hNbr : ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
        X.g.L.stateOf u = b ∧ X.g.L.stateOf v = a.1 ∧ (cube n).Adj u v := by
      simpa [ChunkLayout6.stNbr] using a.2
    rcases hNbr with ⟨u, v, huOdd, hvEven, hstateU, hstateV, hAdj⟩
    have htype : X.stType a.1 = X.evenType v := by
      calc
        X.stType a.1 = X.stType (X.g.L.stateOf v) := by
          exact congrArg X.stType hstateV.symm
        _ = X.evenType v := by
          simp only [Ctx6.stType, ChunkLayout6.stType, Ctx6.evenType,
            X.facts.key_eq v, X.facts.sign_eq v, X.facts.flippable_eq v, X.facts.severity_eq v]
    have hvOcc : X.evenType v ∈ X.occTypes := by
      change X.evenType v ∈
        (Finset.univ.filter fun x : CubeVertex n => IsEvenRole x).image X.evenType
      exact Finset.mem_image.mpr ⟨v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvEven⟩, rfl⟩
    have htypePair : X.stType a.1 = e.2 := congrArg Prod.snd heq
    rw [← htypePair, htype]
    exact hvOcc
  have hraw3Mean : ∀ b D, X.initLaw.expect (fun v => X.rate3V0 v b D) =
      (X.rawHistData (Fin X.T)).pr (fun ω => X.S3Fail ω.1 b D ω.2) := by
    intro b D
    calc
      X.initLaw.expect (fun v => X.rate3V0 v b D) =
          X.baseLaw.expect (fun base => X.rate3Base base b D) := by
        change (∑ v, X.initLaw.w v * (X.coarseLaw v).expect (fun c => X.rate3Base (v, c) b D)) =
          (FinProb.bind X.initLaw X.coarseLaw).expect (fun base => X.rate3Base base b D)
        exact (FinProb.bind_expect X.initLaw X.coarseLaw
          (fun v c => X.rate3Base (v, c) b D)).symm
      _ = X.rawHist.expect (fun H => X.rate3 H b D) := by
        change (∑ base, X.baseLaw.w base * (X.hidLaw base).expect (fun Z => X.rate3 (base, Z) b D)) =
          (FinProb.bind X.baseLaw X.hidLaw).expect (fun H => X.rate3 H b D)
        exact (FinProb.bind_expect X.baseLaw X.hidLaw
          (fun base Z => X.rate3 (base, Z) b D)).symm
      _ = (X.rawHistData (Fin X.T)).pr (fun ω => X.S3Fail ω.1 b D ω.2) := by
        -- The final sampling stage is exactly the conditional data law.
        simpa [Ctx6.rawHistData, Ctx6.rate3] using
          (bind_pr X.rawHist (X.dataLaw (Fin X.T))
            (fun H o => X.S3Fail H b D o)).symm
  have hstep3Raw : ∀ b D, b ∈ X.g.L.oddStates → D ∈ X.absDescs b →
      X.initLaw.expect (fun v => X.rate3V0 v b D) ≤
        ((D.card : ℝ) + 1) * Real.exp (-(2 / 100) * X.k) := by
    intro b D hb hD
    have htypes := hAbsTypes b D hD
    have hfailBound :
        (X.rawHistData (Fin X.T)).pr (fun ω => X.S3Fail ω.1 b D ω.2) ≤
          ((D.card : ℝ) + 1) * X.s3Thr := by
      by_cases hmode : X.stMode b = .low
      · obtain ⟨hbase, hdel⟩ := hLow (Fin X.T) b hb hmode D htypes
        have hsplit : ∀ ω : X.Hist × X.Data (Fin X.T), X.S3Fail ω.1 b D ω.2 →
            (X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ∨
              ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
                X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) := by
          intro ω ⟨hgate, hnot⟩
          by_cases hpos : 0 < X.s3Mass ω.1 b D ω.2 none
          · by_cases hthreshold : X.s3Thr ≤ X.s3Mass ω.1 b D ω.2 none
            · have hbad : ¬ ∀ c ∈ D, X.Matching b c.2 →
                  X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) ≤ X.s3Mass ω.1 b D ω.2 none := by
                intro hall
                exact hnot ⟨hpos, hthreshold, hall⟩
              push Not at hbad
              rcases hbad with ⟨c, hc, hratio⟩
              have hratio' : X.Matching b c.2 ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) := by
                simpa only [not_imp] using hratio
              exact Or.inr ⟨c, hc, hgate, hratio'.2⟩
            · exact Or.inl ⟨hgate, lt_of_not_ge hthreshold⟩
          · have hmass : X.s3Mass ω.1 b D ω.2 none ≤ 0 := not_lt.mp hpos
            exact Or.inl ⟨hgate, lt_of_le_of_lt hmass (Real.exp_pos _)⟩
        have hbasePr : (X.rawHistData (Fin X.T)).pr
            (fun ω => X.S3TrueGate ω.1 b D ∧
              X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr := hbase
        have hdelPr : (X.rawHistData (Fin X.T)).pr
            (fun ω => ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
              X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤
                (D.card : ℝ) * X.s3Thr := by
          calc
            _ ≤ ∑ c ∈ D, (X.rawHistData (Fin X.T)).pr
                (fun ω => X.S3TrueGate ω.1 b D ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) :=
              pr_exists_finset_le (X.rawHistData (Fin X.T)) D (fun c ω =>
                X.S3TrueGate ω.1 b D ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c))
            _ ≤ ∑ c ∈ D, X.s3Thr := by
              apply Finset.sum_le_sum
              intro c hc
              exact hdel c hc
            _ = (D.card : ℝ) * X.s3Thr := by simp
        have hUnion := FinProb.pr_union (X.rawHistData (Fin X.T))
          (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr)
          (fun ω => ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
            X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c))
        calc
          (X.rawHistData (Fin X.T)).pr (fun ω => X.S3Fail ω.1 b D ω.2) ≤
              (X.rawHistData (Fin X.T)).pr
                (fun ω => (X.S3TrueGate ω.1 b D ∧
                    X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ∨
                  ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
                    X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) :=
            pr_mono _ hsplit
          _ ≤ X.s3Thr + (D.card : ℝ) * X.s3Thr := by linarith [hUnion, hbasePr, hdelPr]
          _ = ((D.card : ℝ) + 1) * X.s3Thr := by ring
      · have hmode' : X.stMode b = .high := by
          cases hm : X.stMode b <;> simp_all [Mode6]
        obtain ⟨hbase, hdel⟩ := hHigh (Fin X.T) b hb hmode' D htypes
        have hsplit : ∀ ω : X.Hist × X.Data (Fin X.T), X.S3Fail ω.1 b D ω.2 →
            (X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ∨
              ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
                X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) := by
          intro ω ⟨hgate, hnot⟩
          by_cases hpos : 0 < X.s3Mass ω.1 b D ω.2 none
          · by_cases hthreshold : X.s3Thr ≤ X.s3Mass ω.1 b D ω.2 none
            · have hbad : ¬ ∀ c ∈ D, X.Matching b c.2 →
                  X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) ≤ X.s3Mass ω.1 b D ω.2 none := by
                intro hall
                exact hnot ⟨hpos, hthreshold, hall⟩
              push Not at hbad
              rcases hbad with ⟨c, hc, hratio⟩
              have hratio' : X.Matching b c.2 ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c) := by
                simpa only [not_imp] using hratio
              exact Or.inr ⟨c, hc, hgate, hratio'.2⟩
            · exact Or.inl ⟨hgate, lt_of_not_ge hthreshold⟩
          · have hmass : X.s3Mass ω.1 b D ω.2 none ≤ 0 := not_lt.mp hpos
            exact Or.inl ⟨hgate, lt_of_le_of_lt hmass (Real.exp_pos _)⟩
        have hbasePr : (X.rawHistData (Fin X.T)).pr
            (fun ω => X.S3TrueGate ω.1 b D ∧
              X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr := hbase
        have hdelPr : (X.rawHistData (Fin X.T)).pr
            (fun ω => ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
              X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤
                (D.card : ℝ) * X.s3Thr := by
          calc
            _ ≤ ∑ c ∈ D, (X.rawHistData (Fin X.T)).pr
                (fun ω => X.S3TrueGate ω.1 b D ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) :=
              pr_exists_finset_le (X.rawHistData (Fin X.T)) D (fun c ω =>
                X.S3TrueGate ω.1 b D ∧
                  X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c))
            _ ≤ ∑ c ∈ D, X.s3Thr := by
              apply Finset.sum_le_sum
              intro c hc
              exact hdel c hc
            _ = (D.card : ℝ) * X.s3Thr := by simp
        have hUnion := FinProb.pr_union (X.rawHistData (Fin X.T))
          (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr)
          (fun ω => ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
            X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c))
        calc
          (X.rawHistData (Fin X.T)).pr (fun ω => X.S3Fail ω.1 b D ω.2) ≤
              (X.rawHistData (Fin X.T)).pr
                (fun ω => (X.S3TrueGate ω.1 b D ∧
                    X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ∨
                  ∃ c ∈ D, X.S3TrueGate ω.1 b D ∧
                    X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) :=
            pr_mono _ hsplit
          _ ≤ X.s3Thr + (D.card : ℝ) * X.s3Thr := by linarith [hUnion, hbasePr, hdelPr]
          _ = ((D.card : ℝ) + 1) * X.s3Thr := by ring
    rw [hraw3Mean b D]
    simpa [Ctx6.s3Thr] using hfailBound
  rcases hRate with ⟨hRate12, hRate3⟩
  rcases hRate12 with ⟨Sh12, _fSh12, f1, f2, hRate1Shape, hRate2Shape, hCount1, hCount2⟩
  let τ1 : ℝ := (n : ℝ) ^ (-(δ₁ / 4))
  let q1 : ℝ := (603 * (n : ℝ) ^ (-(δ₁ / 2))) / τ1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hMbound : (X.m : ℝ) + 2 ≤ (n : ℝ) ^ (2 * α₆ p₀) := by
    change (X.g.L.m : ℝ) + 2 ≤ (n : ℝ) ^ (2 * α₆ p₀)
    rw [X.g.m_eq]
    exact hMEventually n hnM
  have hTleJ : X.T ≤ X.J := by
    change T₆ X.g.L.m ≤ J₆ X.g.L.m
    rw [X.g.m_eq]
    exact hTJevent n hnTJ
  have hmOne : 1 ≤ X.m := by
    change 1 ≤ X.g.L.m
    rw [X.g.m_eq]
    exact (Nat.one_le_ceil_iff).2 (Real.rpow_pos_of_pos hnR _)
  have hJleM : X.J ≤ X.m := by
    change ⌊(X.g.L.m : ℝ) ^ (1 / 25 : ℝ)⌋₊ ≤ X.g.L.m
    have hmR : 1 ≤ (X.g.L.m : ℝ) := by exact_mod_cast hmOne
    have hpow : (X.g.L.m : ℝ) ^ (1 / 25 : ℝ) ≤ (X.g.L.m : ℝ) :=
      by
        have h := Real.rpow_le_rpow_of_exponent_le hmR (by norm_num : (1 / 25 : ℝ) ≤ 1)
        simpa only [Real.rpow_one] using h
    exact Nat.floor_le_of_le hpow
  have hTleM : X.T ≤ X.m := hTleJ.trans hJleM
  have hlogM : Real.log ((X.m : ℝ) + 2) ≤ 2 * α₆ p₀ * Real.log (n : ℝ) := by
    calc
      Real.log ((X.m : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ (2 * α₆ p₀)) :=
        Real.log_le_log (by positivity) hMbound
      _ = 2 * α₆ p₀ * Real.log (n : ℝ) := by rw [Real.log_rpow hnR]
  have hTplus : (X.T : ℝ) + 2 ≤ (X.m : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hTleM 2
  have hlogT : Real.log ((X.T : ℝ) + 2) ≤ 2 * α₆ p₀ * Real.log (n : ℝ) := by
    calc
      Real.log ((X.T : ℝ) + 2) ≤ Real.log ((X.m : ℝ) + 2) :=
        Real.log_le_log (by positivity) hTplus
      _ ≤ 2 * α₆ p₀ * Real.log (n : ℝ) := hlogM
  have hnRealOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogNNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnRealOne
  have hTlogNonneg : 0 ≤ Real.log ((X.T : ℝ) + 2) :=
    Real.log_nonneg (by have h : 0 ≤ (X.T : ℝ) := Nat.cast_nonneg _; linarith)
  have hMlogNonneg : 0 ≤ Real.log ((X.m : ℝ) + 2) :=
    Real.log_nonneg (by have h : 0 ≤ (X.m : ℝ) := Nat.cast_nonneg _; linarith)
  have hmPos : 0 < X.g.L.m :=
    lt_of_lt_of_le (by norm_num : 0 < 1) hmOne
  have hmRPos : 0 < (X.g.L.m : ℝ) := by exact_mod_cast hmPos
  have hTOne : 1 ≤ X.T := by
    change 1 ≤ T₆ X.g.L.m
    exact (Nat.one_le_ceil_iff).2 (Real.rpow_pos_of_pos hmRPos _)
  have hJOne : 1 ≤ X.J := le_trans hTOne hTleJ
  have hJplus : (X.J : ℝ) + 1 ≤ 2 * (X.J : ℝ) := by
    have hNat : X.J + 1 ≤ 2 * X.J := by omega
    exact_mod_cast hNat
  have hPfactor : (10 ^ 4 : ℝ) * ((X.T + X.J + 1 : ℕ) : ℝ) + 1 ≤
      40000 * (X.J : ℝ) := by
    have hNat : X.T + X.J + 1 ≤ 3 * X.J := by omega
    have hCast : ((X.T + X.J + 1 : ℕ) : ℝ) ≤ 3 * (X.J : ℝ) := by exact_mod_cast hNat
    have hJcast : (1 : ℝ) ≤ (X.J : ℝ) := by exact_mod_cast hJOne
    norm_num at *
    nlinarith
  have hPbound : (10 ^ 4 : ℝ) * ((X.T + X.J + 1 : ℕ) : ℝ) + 1 ≤
      40000 * (n : ℝ) ^ (2 * α₆ p₀) := by
    have hJm : (X.J : ℝ) ≤ (X.m : ℝ) := by exact_mod_cast hJleM
    have hJpow : (X.J : ℝ) ≤ (n : ℝ) ^ (2 * α₆ p₀) := by linarith [hMbound]
    calc
      _ ≤ 40000 * (X.J : ℝ) := hPfactor
      _ ≤ 40000 * (n : ℝ) ^ (2 * α₆ p₀) := by gcongr
  have hnPowNe : (n : ℝ) ^ (2 * α₆ p₀) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR (2 * α₆ p₀))
  have hlogP : Real.log ((10 ^ 4 : ℝ) * ((X.T + X.J + 1 : ℕ) : ℝ) + 1) ≤
      (1 / 10 ^ 8 + 2 * α₆ p₀) * Real.log (n : ℝ) := by
    calc
      Real.log ((10 ^ 4 : ℝ) * ((X.T + X.J + 1 : ℕ) : ℝ) + 1) ≤
          Real.log ((40000 : ℝ) * (n : ℝ) ^ (2 * α₆ p₀)) :=
      Real.log_le_log (by positivity) hPbound
      _ = Real.log 40000 + 2 * α₆ p₀ * Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num) hnPowNe, Real.log_rpow hnR]
      _ ≤ (1 / 10 ^ 8) * Real.log (n : ℝ) +
          2 * α₆ p₀ * Real.log (n : ℝ) := by
        have hlogConst : Real.log 40000 ≤ (1 / 10 ^ 8) * Real.log (n : ℝ) := by
          calc
            Real.log 40000 ≤ Real.log ((n : ℝ) ^ (1 / 10 ^ 8 : ℝ)) :=
              Real.log_le_log (by norm_num) (le_of_lt (hLogConst n hnLog))
            _ = (1 / 10 ^ 8) * Real.log (n : ℝ) := by rw [Real.log_rpow hnR]
        calc
          _ = 2 * α₆ p₀ * Real.log (n : ℝ) + Real.log 40000 := by ring
          _ ≤ 2 * α₆ p₀ * Real.log (n : ℝ) +
              (1 / 10 ^ 8) * Real.log (n : ℝ) :=
            add_le_add_right hlogConst (2 * α₆ p₀ * Real.log (n : ℝ))
          _ = (1 / 10 ^ 8) * Real.log (n : ℝ) +
              2 * α₆ p₀ * Real.log (n : ℝ) := by ring
      _ = (1 / 10 ^ 8 + 2 * α₆ p₀) * Real.log (n : ℝ) := by ring
  have hshapeBase :
      (X.T : ℝ) * Real.log ((X.T : ℝ) + 2) +
          ((X.J : ℝ) + 1) * Real.log ((X.m : ℝ) + 2) ≤
        6 * α₆ p₀ * (X.J : ℝ) * Real.log (n : ℝ) := by
    have hTleJReal : (X.T : ℝ) ≤ (X.J : ℝ) := by exact_mod_cast hTleJ
    have htermT : (X.T : ℝ) * Real.log ((X.T : ℝ) + 2) ≤
        (X.J : ℝ) * (2 * α₆ p₀ * Real.log (n : ℝ)) := by
      calc
        _ ≤ (X.J : ℝ) * Real.log ((X.T : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hTleJReal hTlogNonneg
        _ ≤ (X.J : ℝ) * (2 * α₆ p₀ * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogT (Nat.cast_nonneg _)
    have htermJ : ((X.J : ℝ) + 1) * Real.log ((X.m : ℝ) + 2) ≤
        (2 * (X.J : ℝ)) * (2 * α₆ p₀ * Real.log (n : ℝ)) := by
      calc
        _ ≤ (2 * (X.J : ℝ)) * Real.log ((X.m : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hJplus hMlogNonneg
        _ ≤ (2 * (X.J : ℝ)) * (2 * α₆ p₀ * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogM (by positivity)
    nlinarith [htermT, htermJ]
  have hshapeExp :
      10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2)) ≤
        60000 * α₆ p₀ * ((X.J : ℝ) * Real.log (n : ℝ)) := by
    have hshape := hshapeBase
    change 10 ^ 4 * ((X.T : ℝ) * Real.log ((X.T : ℝ) + 2) +
      ((X.J : ℝ) + 1) * Real.log ((X.m : ℝ) + 2)) ≤ _
    nlinarith [hshape]
  have hτ1 : 0 < τ1 := by dsimp [τ1]; exact Real.rpow_pos_of_pos hnR _
  have hq1 : 0 ≤ q1 := by dsimp [q1, τ1]; positivity
  have hq1Eq : q1 = 603 * (n : ℝ) ^ (-(δ₁ / 4)) := by
    dsimp [q1, τ1]
    calc
      603 * (n : ℝ) ^ (-(δ₁ / 2)) / (n : ℝ) ^ (-(δ₁ / 4)) =
          603 * ((n : ℝ) ^ (-(δ₁ / 2)) / (n : ℝ) ^ (-(δ₁ / 4))) := by ring
      _ = 603 * (n : ℝ) ^ (-(δ₁ / 2) - (-(δ₁ / 4))) := by
        rw [← Real.rpow_sub hnR]
      _ = 603 * (n : ℝ) ^ (-(δ₁ / 4)) := by
        rw [show -(δ₁ / 2) - (-(δ₁ / 4)) = -(δ₁ / 4) by ring]
  have hrate1Nonneg : ∀ h v, 0 ≤ X.rate1V0 v h := by
    intro h v
    dsimp [Ctx6.rate1V0, FinProb.pr]
    apply Finset.sum_nonneg
    intro c hc
    split_ifs
    · exact le_rfl
    · exact (X.coarseLaw v).nonneg c
  have hstep1AlarmEach : ∀ h, h ∈ X.step1Keys →
      X.initLaw.pr (fun v => τ1 ≤ X.rate1V0 v h) ≤ q1 := by
    intro h hh
    have hmark := FinProb.markov X.initLaw (fun v => X.rate1V0 v h)
      τ1 (fun v => hrate1Nonneg h v) hτ1
    calc
      X.initLaw.pr (fun v => τ1 ≤ X.rate1V0 v h) ≤
          X.initLaw.expect (fun v => X.rate1V0 v h) / τ1 := hmark
      _ ≤ (603 * (n : ℝ) ^ (-(δ₁ / 2))) / τ1 := by
        apply div_le_div_of_nonneg_right _ hτ1.le
        rw [hrate1Mean h]
        exact hStep1Raw h hh
      _ = q1 := rfl
  have hstep1Grouped :
      X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys,
        τ1 ≤ X.rate1V0 v h) ≤
        ∑ s ∈ X.step1Keys.image f1,
          X.initLaw.pr (fun v => τ1 ≤ X.rate1V0 v (chooseImageRep X.step1Keys f1 s)) := by
    exact pr_exists_shape_sum X.initLaw X.step1Keys f1
      (fun v h => X.rate1V0 v h) τ1
      (by
        intro h h' heq v
        exact hRate1Shape h h' heq v)
  have hstep1Grouped' :
      (∑ s ∈ X.step1Keys.image f1,
        X.initLaw.pr (fun v => τ1 ≤ X.rate1V0 v (chooseImageRep X.step1Keys f1 s))) ≤
        (10 ^ 200 : ℝ) * q1 := by
    calc
      _ ≤ ∑ s ∈ X.step1Keys.image f1,
          q1 := by
        apply Finset.sum_le_sum
        intro s hs
        exact hstep1AlarmEach _ (chooseImageRep_spec X.step1Keys f1 hs).1
      _ = (X.step1Keys.image f1).card * q1 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (10 ^ 200 : ℝ) * q1 := by
        apply mul_le_mul_of_nonneg_right _ hq1
        exact hCount1
  have hStep1Alarm : X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys,
      τ1 ≤ X.rate1V0 v h) ≤ (10 ^ 200 : ℝ) * q1 :=
    hstep1Grouped.trans hstep1Grouped'
  have hStep1Budget : (10 ^ 200 : ℝ) * q1 < 1 / 6 := by
    calc
      (10 ^ 200 : ℝ) * q1 = (10 ^ 200 : ℝ) * 603 * (n : ℝ) ^ (-(δ₁ / 4)) := by
        rw [hq1Eq]
        ring
      _ < 1 / 6 := hTail1 n hnTail1
  have hrate2BaseNonneg : ∀ base β, 0 ≤ X.rate2Base base β := by
    classical
    intro base β
    unfold Ctx6.rate2Base FinProb.pr
    apply Finset.sum_nonneg
    intro Z hZ
    by_cases hfail : X.Step2Fail (base, Z) β
    · simp [hfail, (X.hidLaw base).nonneg Z]
    · simp [hfail]
  have hrate2V0Nonneg : ∀ v β, 0 ≤ X.rate2V0 v β := by
    intro v β
    unfold Ctx6.rate2V0 FinProb.expect
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg ((X.coarseLaw v).nonneg c) (hrate2BaseNonneg (v, c) β)
  let τ₂ : ℕ → ℝ := fun u => (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 4))
  let q₂ : ℕ → ℝ := fun u => ((n : ℝ) ^ (-(δ₂ * (u : ℝ) / 2))) / τ₂ u
  have hstep2AlarmEach : ∀ u β, β ∈ X.occTypes → β.u = u →
      X.initLaw.pr (fun v => τ₂ u ≤ X.rate2V0 v β) ≤ q₂ u := by
    intro u β hβ hu
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have ht : 0 < τ₂ u := by dsimp [τ₂]; exact Real.rpow_pos_of_pos hnR _
    have hmark := FinProb.markov X.initLaw (fun v => X.rate2V0 v β) (τ₂ u)
      (fun v => hrate2V0Nonneg v β) ht
    have hraw : X.initLaw.expect (fun v => X.rate2V0 v β) ≤
        (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 2)) := by
      rw [hrate2Mean β, ← hu]
      exact hStep2 β hβ
    calc
      X.initLaw.pr (fun v => τ₂ u ≤ X.rate2V0 v β) ≤
          X.initLaw.expect (fun v => X.rate2V0 v β) / τ₂ u := hmark
      _ ≤ ((n : ℝ) ^ (-(δ₂ * (u : ℝ) / 2))) / τ₂ u :=
        div_le_div_of_nonneg_right hraw ht.le
      _ = q₂ u := rfl
  letI : Inhabited X.Ty := ⟨(default, Mode6.low, 0, ∅)⟩
  have hstep2GroupedU : ∀ u,
      X.initLaw.pr (fun v => ∃ β ∈ X.occTypes.filter (fun β => β.u = u),
        τ₂ u ≤ X.rate2V0 v β) ≤
        ∑ s ∈ (X.occTypes.filter (fun β => β.u = u)).image f2,
          X.initLaw.pr (fun v => τ₂ u ≤ X.rate2V0 v
            (chooseImageRep (X.occTypes.filter (fun β => β.u = u)) f2 s)) := by
    intro u
    exact pr_exists_shape_sum X.initLaw (X.occTypes.filter (fun β => β.u = u)) f2
      (fun v β => X.rate2V0 v β) (τ₂ u)
      (by
        intro β β' heq v
        exact (hRate2Shape β β' heq).2 v)
  have hstep2GroupedUB : ∀ u,
      X.initLaw.pr (fun v => ∃ β ∈ X.occTypes.filter (fun β => β.u = u),
        τ₂ u ≤ X.rate2V0 v β) ≤
        (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u) * q₂ u := by
    intro u
    have hqu : 0 ≤ q₂ u := by dsimp [q₂, τ₂]; positivity
    calc
      X.initLaw.pr (fun v => ∃ β ∈ X.occTypes.filter (fun β => β.u = u),
          τ₂ u ≤ X.rate2V0 v β) ≤
          ∑ s ∈ (X.occTypes.filter (fun β => β.u = u)).image f2,
            X.initLaw.pr (fun v => τ₂ u ≤ X.rate2V0 v
              (chooseImageRep (X.occTypes.filter (fun β => β.u = u)) f2 s)) := hstep2GroupedU u
      _ ≤ ∑ s ∈ (X.occTypes.filter (fun β => β.u = u)).image f2, q₂ u := by
        apply Finset.sum_le_sum
        intro s hs
        have hrep := chooseImageRep_spec (X.occTypes.filter (fun β => β.u = u)) f2 hs
        have hβ := Finset.mem_filter.mp hrep.1
        exact hstep2AlarmEach u (chooseImageRep (X.occTypes.filter (fun β => β.u = u)) f2 s)
          hβ.1 hβ.2
      _ = ((X.occTypes.filter (fun β => β.u = u)).image f2).card * q₂ u := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u) * q₂ u := by
        apply mul_le_mul_of_nonneg_right _ hqu
        exact hCount2 u
  have hstep2Alarm : X.initLaw.pr (fun v => ∃ β ∈ X.occTypes,
      τ₂ β.u ≤ X.rate2V0 v β) ≤
      ∑ u ∈ (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val),
        (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val := by
    have huBound : ∀ β, β ∈ X.occTypes → β.u ≤ X.m + 1 := by
      intro β hβ
      have hsev : β.sev < X.m + 1 := by
        dsimp [Type6.sev, Ctx6.m]
        exact β.2.2.1.isLt
      by_cases hm : β.mode = .low
      · have hu : β.u = β.sev + 1 := by simp [Type6.u, hm]
        rw [hu]
        exact Nat.succ_le_succ (Nat.le_of_lt_succ hsev)
      · have hh : β.mode = .high := by
          cases hmode : β.mode <;> simp_all [Mode6]
        have hu : β.u = 1 := by simp [Type6.u, hh]
        rw [hu]
        omega
    have hsub : ∀ v, (∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) →
        ∃ u : Fin (X.m + 2),
          u ∈ (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val) ∧
            ∃ β ∈ X.occTypes.filter (fun β => β.u = u.val),
              τ₂ u.val ≤ X.rate2V0 v β := by
      intro v hbad
      rcases hbad with ⟨β, hβ, hfail⟩
      have hbu := huBound β hβ
      have hbuPos : 0 < β.u := by
        cases hmode : β.mode <;> simp [Type6.u, hmode]
      let u : Fin (X.m + 2) := ⟨β.u, by omega⟩
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbuPos⟩, β, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hβ, rfl⟩
      · simpa using hfail
    calc
      X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) ≤
          X.initLaw.pr (fun v => ∃ u ∈ (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val),
            ∃ β ∈ X.occTypes.filter (fun β => β.u = u.val), τ₂ u.val ≤ X.rate2V0 v β) :=
        pr_mono X.initLaw hsub
      _ ≤ ∑ u ∈ (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val),
          X.initLaw.pr (fun v => ∃ β ∈ X.occTypes.filter (fun β => β.u = u.val),
            τ₂ u.val ≤ X.rate2V0 v β) := by
        simpa using pr_exists_finset_le X.initLaw
          (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val)
          (fun u v => ∃ β ∈ X.occTypes.filter (fun β => β.u = u.val),
            τ₂ u.val ≤ X.rate2V0 v β)
      _ ≤ ∑ u ∈ (Finset.univ.filter fun u : Fin (X.m + 2) => 0 < u.val),
          (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val := by
        apply Finset.sum_le_sum
        intro u hu
        exact hstep2GroupedUB u.val
  let U₂ : Finset (Fin (X.m + 2)) := Finset.univ.filter fun u => 0 < u.val
  have hstep2Alarm' : X.initLaw.pr (fun v => ∃ β ∈ X.occTypes,
      τ₂ β.u ≤ X.rate2V0 v β) ≤
      ∑ u ∈ U₂, (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val := by
    simpa [U₂] using hstep2Alarm
  have hq₂Exp : ∀ u, q₂ u = (n : ℝ) ^ (-(δ₂ / 4) * (u : ℝ)) := by
    intro u
    dsimp [q₂, τ₂]
    calc
      (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 2)) / (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 4)) =
          (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 2) - (-(δ₂ * (u : ℝ) / 4))) := by
            rw [← Real.rpow_sub hnR]
      _ = (n : ℝ) ^ (-(δ₂ / 4) * (u : ℝ)) := by
        rw [show -(δ₂ * (u : ℝ) / 2) - (-(δ₂ * (u : ℝ) / 4)) =
          -(δ₂ / 4) * (u : ℝ) by ring]
  let r₂ : ℝ := ((X.m : ℝ) + 1) ^ 2 * (n : ℝ) ^ (-(δ₂ / 4))
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hAlphaDecay : 4 * α₆ p₀ - δ₂ / 4 < 0 := by
    norm_num [δ₂] at *
    nlinarith
  have hr₂Nonneg : 0 ≤ r₂ := by dsimp [r₂]; positivity
  have hr₂Le : r₂ ≤ 1 := by
    have hmPlus1 : (X.m : ℝ) + 1 ≤ (n : ℝ) ^ (2 * α₆ p₀) := by linarith
    have hsquare : ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 = (n : ℝ) ^ (4 * α₆ p₀) := by
      calc
        ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 = ((n : ℝ) ^ (2 * α₆ p₀)) ^ (2 : ℝ) :=
          (Real.rpow_natCast ((n : ℝ) ^ (2 * α₆ p₀)) 2).symm
        _ = (n : ℝ) ^ ((2 * α₆ p₀) * 2) :=
          (Real.rpow_mul hnR.le (2 * α₆ p₀) (2 : ℝ)).symm
        _ = (n : ℝ) ^ (4 * α₆ p₀) := by
          rw [show (2 * α₆ p₀) * 2 = 4 * α₆ p₀ by ring]
    have hprod : ((X.m : ℝ) + 1) ^ 2 * (n : ℝ) ^ (-(δ₂ / 4)) ≤
        (n : ℝ) ^ (4 * α₆ p₀ - δ₂ / 4) := by
      calc
        ((X.m : ℝ) + 1) ^ 2 * (n : ℝ) ^ (-(δ₂ / 4)) ≤
            ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 * (n : ℝ) ^ (-(δ₂ / 4)) := by gcongr
        _ = (n : ℝ) ^ (4 * α₆ p₀) * (n : ℝ) ^ (-(δ₂ / 4)) := by rw [hsquare]
        _ = (n : ℝ) ^ (4 * α₆ p₀ - δ₂ / 4) := by
          rw [← Real.rpow_add hnR]
          rw [show 4 * α₆ p₀ + (-(δ₂ / 4)) = 4 * α₆ p₀ - δ₂ / 4 by ring]
    have hpow : (n : ℝ) ^ (4 * α₆ p₀ - δ₂ / 4) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hn1 hAlphaDecay
    dsimp [r₂]
    exact le_trans hprod hpow.le
  have hfactor₂ : ∀ (u : Fin (X.m + 2)),
      ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val = r₂ ^ u.val := by
    intro u
    have hmPow : ((X.m : ℝ) + 1) ^ (2 * u.val) = (((X.m : ℝ) + 1) ^ 2) ^ u.val :=
      pow_mul _ 2 u.val
    have hnPow : (n : ℝ) ^ (-(δ₂ / 4) * (u.val : ℝ)) =
        ((n : ℝ) ^ (-(δ₂ / 4))) ^ u.val := by
      calc
        (n : ℝ) ^ (-(δ₂ / 4) * (u.val : ℝ)) =
            ((n : ℝ) ^ (-(δ₂ / 4))) ^ (u.val : ℝ) :=
              Real.rpow_mul hnR.le (-(δ₂ / 4)) (u.val : ℝ)
        _ = ((n : ℝ) ^ (-(δ₂ / 4))) ^ u.val :=
          Real.rpow_natCast ((n : ℝ) ^ (-(δ₂ / 4))) u.val
    calc
      ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val =
          (((X.m : ℝ) + 1) ^ 2) ^ u.val * ((n : ℝ) ^ (-(δ₂ / 4))) ^ u.val := by
            rw [hq₂Exp, hmPow, hnPow]
      _ = r₂ ^ u.val := by rw [← mul_pow]
  have hGrouped2Total :
      (∑ u ∈ U₂, (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val) ≤
        ((X.m : ℝ) + 2) * ((10 ^ 210 : ℝ) * r₂) := by
    have hsum :
        (∑ u ∈ U₂, (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val) ≤
          ∑ u ∈ U₂, (10 ^ 210 : ℝ) * r₂ := by
      apply Finset.sum_le_sum
      intro u hu
      have huPos : 0 < u.val := by
        have hu' : u ∈ (Finset.univ.filter fun v : Fin (X.m + 2) => 0 < v.val) := by
          simpa [U₂] using hu
        exact (Finset.mem_filter.mp hu').2
      have huone : 1 ≤ u.val := by omega
      calc
        (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val =
            (10 ^ 210 : ℝ) * (((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val) := by ring
        _ = (10 ^ 210 : ℝ) * r₂ ^ u.val := by rw [hfactor₂ u]
        _ ≤ (10 ^ 210 : ℝ) * r₂ := mul_le_mul_of_nonneg_left
          (by
            simpa only [pow_one] using
              (pow_le_pow_of_le_one hr₂Nonneg hr₂Le huone)) (by positivity)
    have hUcard : U₂.card ≤ X.m + 2 := by
      calc
        U₂.card ≤ Fintype.card (Fin (X.m + 2)) := Finset.card_le_univ U₂
        _ = X.m + 2 := by simp
    calc
      _ ≤ ∑ u ∈ U₂, (10 ^ 210 : ℝ) * r₂ := hsum
      _ = (U₂.card : ℝ) * ((10 ^ 210 : ℝ) * r₂) := by simp
      _ ≤ ((X.m : ℝ) + 2) * ((10 ^ 210 : ℝ) * r₂) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hUcard
        · positivity
  have hStep2AlarmBound : X.initLaw.pr (fun v => ∃ β ∈ X.occTypes,
      τ₂ β.u ≤ X.rate2V0 v β) ≤
      (10 ^ 210 : ℝ) * ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 *
        (n : ℝ) ^ (-(δ₂ / 4)) := by
    calc
      _ ≤ ∑ u ∈ U₂, (10 ^ 210 : ℝ) * ((X.m : ℝ) + 1) ^ (2 * u.val) * q₂ u.val := hstep2Alarm'
      _ ≤ ((X.m : ℝ) + 2) * ((10 ^ 210 : ℝ) * r₂) := hGrouped2Total
      _ = (10 ^ 210 : ℝ) * ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 *
          (n : ℝ) ^ (-(δ₂ / 4)) := by dsimp [r₂]; ring
  have hpoly2 : ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 ≤
      (n : ℝ) ^ (6 * α₆ p₀) := by
    have hmPlus1 : (X.m : ℝ) + 1 ≤ (n : ℝ) ^ (2 * α₆ p₀) := by linarith
    have hsquare : ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 = (n : ℝ) ^ (4 * α₆ p₀) := by
      calc
        ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 = ((n : ℝ) ^ (2 * α₆ p₀)) ^ (2 : ℝ) :=
          (Real.rpow_natCast ((n : ℝ) ^ (2 * α₆ p₀)) 2).symm
        _ = (n : ℝ) ^ ((2 * α₆ p₀) * 2) :=
          (Real.rpow_mul hnR.le (2 * α₆ p₀) (2 : ℝ)).symm
        _ = (n : ℝ) ^ (4 * α₆ p₀) := by
          rw [show (2 * α₆ p₀) * 2 = 4 * α₆ p₀ by ring]
    have hprod : (n : ℝ) ^ (2 * α₆ p₀) * (n : ℝ) ^ (4 * α₆ p₀) =
        (n : ℝ) ^ (6 * α₆ p₀) := by
      rw [← Real.rpow_add hnR]
      rw [show 2 * α₆ p₀ + 4 * α₆ p₀ = 6 * α₆ p₀ by ring]
    have hsquareM : ((X.m : ℝ) + 1) ^ 2 ≤ ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hmPlus1
    calc
      ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 ≤
          (n : ℝ) ^ (2 * α₆ p₀) * ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 := by
        calc
          _ ≤ (n : ℝ) ^ (2 * α₆ p₀) * ((X.m : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hMbound (sq_nonneg _)
          _ ≤ (n : ℝ) ^ (2 * α₆ p₀) * ((n : ℝ) ^ (2 * α₆ p₀)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquareM (Real.rpow_nonneg hnR.le _)
      _ = (n : ℝ) ^ (6 * α₆ p₀) := by rw [hsquare, hprod]
  have hStep2Budget : X.initLaw.pr (fun v => ∃ β ∈ X.occTypes,
      τ₂ β.u ≤ X.rate2V0 v β) ≤ 1 / 6 := by
    calc
      _ ≤ (10 ^ 210 : ℝ) * ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 *
          (n : ℝ) ^ (-(δ₂ / 4)) := hStep2AlarmBound
      _ ≤ (10 ^ 210 : ℝ) * (n : ℝ) ^ (6 * α₆ p₀) *
          (n : ℝ) ^ (-(δ₂ / 4)) := by
        have hnegpow : 0 ≤ (n : ℝ) ^ (-(δ₂ / 4)) := Real.rpow_nonneg hnR.le _
        calc
          (10 ^ 210 : ℝ) * ((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2 *
              (n : ℝ) ^ (-(δ₂ / 4)) =
            ((10 ^ 210 : ℝ) * (((X.m : ℝ) + 2) * ((X.m : ℝ) + 1) ^ 2)) *
              (n : ℝ) ^ (-(δ₂ / 4)) := by ring
          _ ≤ ((10 ^ 210 : ℝ) * (n : ℝ) ^ (6 * α₆ p₀)) *
              (n : ℝ) ^ (-(δ₂ / 4)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpoly2 (by positivity)) hnegpow
      _ = (10 ^ 210 : ℝ) * (n : ℝ) ^ (-(δ₂ / 4 - 6 * α₆ p₀)) := by
        calc
          (10 ^ 210 : ℝ) * (n : ℝ) ^ (6 * α₆ p₀) * (n : ℝ) ^ (-(δ₂ / 4)) =
              (10 ^ 210 : ℝ) * ((n : ℝ) ^ (6 * α₆ p₀) * (n : ℝ) ^ (-(δ₂ / 4))) := by ring
          _ = (10 ^ 210 : ℝ) * (n : ℝ) ^ (6 * α₆ p₀ + (-(δ₂ / 4))) := by
            rw [← Real.rpow_add hnR]
          _ = (10 ^ 210 : ℝ) * (n : ℝ) ^ (-(δ₂ / 4 - 6 * α₆ p₀)) := by
            rw [show 6 * α₆ p₀ + (-(δ₂ / 4)) = -(δ₂ / 4 - 6 * α₆ p₀) by ring]
      _ ≤ 1 / 6 := (hTail2 n hnTail2).le
  rcases hRate3 with ⟨Sh3, _fSh3, f3, hRate3Shape, hCount3⟩
  letI : Inhabited X.State := ⟨(fun _ => false, (fun _ => 0), KeyFlag6.interior, (fun _ => 0), 0)⟩
  letI : Inhabited (X.State × Finset (Fin X.T × X.Ty)) := ⟨(default, ∅)⟩
  let S3 : Finset (X.State × Finset (Fin X.T × X.Ty)) :=
    Finset.univ.filter fun p => p.1 ∈ X.g.L.oddStates ∧ p.2 ∈ X.absDescs p.1
  let sh3 : X.State × Finset (Fin X.T × X.Ty) → Sh3 := fun p => f3 p.1 p.2
  let τ₃ : ℝ := Real.exp (-(9 / 1000 : ℝ) * X.k)
  let q₃ : ℝ :=
    (10 ^ 4 * (X.T + X.J + 1) + 1) * Real.exp (-(2 / 100 : ℝ) * X.k) / τ₃
  have hτ₃ : 0 < τ₃ := by dsimp [τ₃]; exact Real.exp_pos _
  have hq₃ : 0 ≤ q₃ := by dsimp [q₃, τ₃]; positivity
  have hrate3Nonneg : ∀ H b D, 0 ≤ X.rate3 H b D := by
    intro H b D
    classical
    unfold Ctx6.rate3 FinProb.pr
    apply Finset.sum_nonneg
    intro o ho
    by_cases hf : X.S3Fail H b D o
    · simp [hf, (X.dataLaw (Fin X.T) H).nonneg o]
    · simp [hf]
  have hrate3BaseNonneg : ∀ base b D, 0 ≤ X.rate3Base base b D := by
    intro base b D
    unfold Ctx6.rate3Base FinProb.expect
    apply Finset.sum_nonneg
    intro Z hZ
    exact mul_nonneg ((X.hidLaw base).nonneg Z) (hrate3Nonneg (base, Z) b D)
  have hrate3V0Nonneg : ∀ v b D, 0 ≤ X.rate3V0 v b D := by
    intro v b D
    unfold Ctx6.rate3V0 FinProb.expect
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg ((X.coarseLaw v).nonneg c) (hrate3BaseNonneg (v, c) b D)
  have hstep3AlarmEach : ∀ b D, b ∈ X.g.L.oddStates → D ∈ X.absDescs b →
      X.initLaw.pr (fun v => τ₃ ≤ X.rate3V0 v b D) ≤ q₃ := by
    intro b D hb hD
    have hsize : (D.card : ℝ) ≤ 10 ^ 4 * (X.T + X.J + 1) := by
      exact hDesc (Fin X.T) b (fun _ => Finset.univ) hb D (by simpa [Ctx6.absDescs] using hD)
    have hsize' : (D.card : ℝ) + 1 ≤ 10 ^ 4 * (X.T + X.J + 1) + 1 := by linarith
    have hraw := hstep3Raw b D hb hD
    have hmark := FinProb.markov X.initLaw (fun v => X.rate3V0 v b D) τ₃
      (fun v => hrate3V0Nonneg v b D) hτ₃
    calc
      X.initLaw.pr (fun v => τ₃ ≤ X.rate3V0 v b D) ≤
          X.initLaw.expect (fun v => X.rate3V0 v b D) / τ₃ := hmark
      _ ≤ (((D.card : ℝ) + 1) * Real.exp (-(2 / 100 : ℝ) * X.k)) / τ₃ :=
        div_le_div_of_nonneg_right hraw hτ₃.le
      _ ≤ q₃ := by
        apply div_le_div_of_nonneg_right ?_ hτ₃.le
        exact mul_le_mul_of_nonneg_right hsize' (Real.exp_nonneg _)
  have hS3ImageSubset : S3.image sh3 ⊆
      X.g.L.oddStates.biUnion (fun b => (X.absDescs b).image (f3 b)) := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨p, hp, hps⟩
    rcases (Finset.mem_filter.mp hp).2 with ⟨hb, hD⟩
    rw [← hps]
    exact Finset.mem_biUnion.mpr ⟨p.1, hb, Finset.mem_image.mpr ⟨p.2, hD, rfl⟩⟩
  have hS3Card : ((S3.image sh3).card : ℝ) ≤
      Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2))) := by
    have hcard : ((S3.image sh3).card : ℝ) ≤
        ((X.g.L.oddStates.biUnion (fun b => (X.absDescs b).image (f3 b))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hS3ImageSubset
    exact hcard.trans hCount3
  have hStep3ShapeEq : ∀ p p', sh3 p = sh3 p' → ∀ v,
      X.rate3V0 v p.1 p.2 = X.rate3V0 v p'.1 p'.2 := by
    intro p p' heq v
    exact hRate3Shape p.1 p.2 p'.1 p'.2 heq v
  have hStep3Grouped :
      X.initLaw.pr (fun v => ∃ p ∈ S3, τ₃ ≤ X.rate3V0 v p.1 p.2) ≤
        ∑ s ∈ S3.image sh3,
          X.initLaw.pr (fun v => τ₃ ≤ X.rate3V0 v
            (chooseImageRep S3 sh3 s).1 (chooseImageRep S3 sh3 s).2) := by
    exact pr_exists_shape_sum X.initLaw S3 sh3
      (fun v p => X.rate3V0 v p.1 p.2) τ₃ hStep3ShapeEq
  have hStep3Grouped' :
      (∑ s ∈ S3.image sh3,
        X.initLaw.pr (fun v => τ₃ ≤ X.rate3V0 v
          (chooseImageRep S3 sh3 s).1 (chooseImageRep S3 sh3 s).2)) ≤
        (S3.image sh3).card * q₃ := by
    calc
      _ ≤ ∑ s ∈ S3.image sh3, q₃ := by
        apply Finset.sum_le_sum
        intro s hs
        have hrep := chooseImageRep_spec S3 sh3 hs
        rcases (Finset.mem_filter.mp hrep.1).2 with ⟨hb, hD⟩
        exact hstep3AlarmEach _ _ hb hD
      _ = (S3.image sh3).card * q₃ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hStep3EventEq : ∀ v,
      (∃ p ∈ S3, τ₃ ≤ X.rate3V0 v p.1 p.2) ↔
        ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ ≤ X.rate3V0 v b D := by
    intro v
    constructor
    · rintro ⟨p, hp, hrate⟩
      rcases (Finset.mem_filter.mp hp).2 with ⟨hb, hD⟩
      exact ⟨p.1, hb, p.2, hD, hrate⟩
    · rintro ⟨b, hb, D, hD, hrate⟩
      exact ⟨(b, D), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hb, hD⟩⟩, hrate⟩
  have hStep3Alarm : X.initLaw.pr (fun v =>
      ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ ≤ X.rate3V0 v b D) ≤
        Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2))) * q₃ := by
    have hprobEq : X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates,
        ∃ D ∈ X.absDescs b, τ₃ ≤ X.rate3V0 v b D) =
        X.initLaw.pr (fun v => ∃ p ∈ S3, τ₃ ≤ X.rate3V0 v p.1 p.2) := by
      apply pr_congr
      intro v
      exact (hStep3EventEq v).symm
    calc
      _ = X.initLaw.pr (fun v => ∃ p ∈ S3, τ₃ ≤ X.rate3V0 v p.1 p.2) := hprobEq
      _ ≤ ∑ s ∈ S3.image sh3, X.initLaw.pr (fun v => τ₃ ≤ X.rate3V0 v
            (chooseImageRep S3 sh3 s).1 (chooseImageRep S3 sh3 s).2) := hStep3Grouped
      _ ≤ (S3.image sh3).card * q₃ := hStep3Grouped'
      _ ≤ Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) +
            (X.J + 1) * Real.log (X.m + 2))) * q₃ :=
        mul_le_mul_of_nonneg_right hS3Card hq₃
  let P₃ : ℝ := (10 ^ 4 : ℝ) * ((X.T + X.J + 1 : ℕ) : ℝ) + 1
  have hP₃pos : 0 < P₃ := by positivity
  have hlogP₃ : Real.log P₃ ≤ (1 / 10 ^ 8 + 2 * α₆ p₀) * Real.log (n : ℝ) := by
    simpa [P₃] using hlogP
  have hP₃cast : ((X.T + X.J + 1 : ℕ) : ℝ) =
      (X.T : ℝ) + (X.J : ℝ) + 1 := by norm_cast
  have hP₃eq : q₃ = P₃ * Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ)) := by
    dsimp [q₃, τ₃, P₃]
    rw [hP₃cast]
    calc
      ((10 ^ 4 : ℝ) * ((X.T : ℝ) + (X.J : ℝ) + 1) + 1) *
          Real.exp (-(2 / 100 : ℝ) * (X.k : ℝ)) /
            Real.exp (-(9 / 1000 : ℝ) * (X.k : ℝ)) =
          ((10 ^ 4 : ℝ) * ((X.T : ℝ) + (X.J : ℝ) + 1) + 1) *
            (Real.exp (-(2 / 100 : ℝ) * (X.k : ℝ)) /
              Real.exp (-(9 / 1000 : ℝ) * (X.k : ℝ))) := by ring
      _ = ((10 ^ 4 : ℝ) * ((X.T : ℝ) + (X.J : ℝ) + 1) + 1) *
            Real.exp (-(2 / 100 : ℝ) * (X.k : ℝ) -
              (-(9 / 1000 : ℝ) * (X.k : ℝ))) := by rw [← Real.exp_sub]
      _ = ((10 ^ 4 : ℝ) * ((X.T : ℝ) + (X.J : ℝ) + 1) + 1) *
            Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ)) := by
              rw [show -(2 / 100 : ℝ) * (X.k : ℝ) -
                (-(9 / 1000 : ℝ) * (X.k : ℝ)) =
                  -(11 / 1000 : ℝ) * (X.k : ℝ) by ring]
  have hJLogNonneg : 0 ≤ (X.J : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) hlogNNonneg
  have hlogP₃J : Real.log P₃ ≤
      (1 / 10 ^ 8 + 2 * α₆ p₀) * ((X.J : ℝ) * Real.log (n : ℝ)) := by
    have hlogNle : Real.log (n : ℝ) ≤ (X.J : ℝ) * Real.log (n : ℝ) := by
      calc
        Real.log (n : ℝ) = 1 * Real.log (n : ℝ) := by ring
        _ ≤ (X.J : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hJOne) hlogNNonneg
    calc
      Real.log P₃ ≤ (1 / 10 ^ 8 + 2 * α₆ p₀) * Real.log (n : ℝ) := hlogP₃
      _ ≤ (1 / 10 ^ 8 + 2 * α₆ p₀) * ((X.J : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogNle (by positivity)
  have hshapeLogP :
      10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2)) +
        Real.log P₃ ≤ (1 / 10 ^ 7) * ((X.J : ℝ) * Real.log (n : ℝ)) := by
    have hcoeff : 60000 * α₆ p₀ + (1 / 10 ^ 8 + 2 * α₆ p₀) ≤ 1 / 10 ^ 7 := by
      norm_num at *
      nlinarith
    calc
      _ ≤ 60000 * α₆ p₀ * ((X.J : ℝ) * Real.log (n : ℝ)) +
          (1 / 10 ^ 8 + 2 * α₆ p₀) * ((X.J : ℝ) * Real.log (n : ℝ)) :=
        add_le_add hshapeExp hlogP₃J
      _ = (60000 * α₆ p₀ + (1 / 10 ^ 8 + 2 * α₆ p₀)) *
          ((X.J : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ (1 / 10 ^ 7) * ((X.J : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff hJLogNonneg
  have hκJlog : κ₆ * ((X.J : ℝ) * Real.log (n : ℝ)) ≤ (X.k : ℝ) := by
    dsimp [Ctx6.k, Ctx6.J, k₆]
    calc
      κ₆ * ((J₆ X.g.L.m : ℝ) * Real.log (n : ℝ)) =
          κ₆ * (J₆ X.g.L.m : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (⌈κ₆ * (J₆ X.g.L.m : ℝ) * Real.log (n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hStep3Exp :
      10 ^ 4 * (X.T * Real.log (X.T + 2) + (X.J + 1) * Real.log (X.m + 2)) +
        Real.log P₃ - (11 / 1000 : ℝ) * (X.k : ℝ) ≤
      -(1 / 10 ^ 6 : ℝ) * ((X.J : ℝ) * Real.log (n : ℝ)) := by
    have hdecay : (1 / 10 ^ 7 : ℝ) - (11 / 1000 : ℝ) * κ₆ =
        -(1 / 10 ^ 6 : ℝ) := by norm_num [κ₆]
    have hneg : -(11 / 1000 : ℝ) * (X.k : ℝ) ≤
        -(11 / 1000 : ℝ) * (κ₆ * ((X.J : ℝ) * Real.log (n : ℝ))) := by
      exact mul_le_mul_of_nonpos_left hκJlog (by norm_num)
    calc
      _ ≤ (1 / 10 ^ 7 : ℝ) * ((X.J : ℝ) * Real.log (n : ℝ)) -
          (11 / 1000 : ℝ) * (X.k : ℝ) := by linarith [hshapeLogP]
      _ ≤ ((1 / 10 ^ 7 : ℝ) - (11 / 1000 : ℝ) * κ₆) *
          ((X.J : ℝ) * Real.log (n : ℝ)) := by nlinarith [hneg]
      _ = -(1 / 10 ^ 6 : ℝ) * ((X.J : ℝ) * Real.log (n : ℝ)) := by rw [hdecay]
  have hStep3Budget : X.initLaw.pr (fun v =>
      ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ ≤ X.rate3V0 v b D) ≤ 1 / 6 := by
    have hExpEq : Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) +
        (X.J + 1) * Real.log (X.m + 2))) * q₃ =
        Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) +
          (X.J + 1) * Real.log (X.m + 2)) + Real.log P₃ -
          (11 / 1000 : ℝ) * (X.k : ℝ)) := by
      let s : ℝ := 10 ^ 4 * (X.T * Real.log (X.T + 2) +
        (X.J + 1) * Real.log (X.m + 2))
      have hp : P₃ = Real.exp (Real.log P₃) := (Real.exp_log hP₃pos).symm
      calc
        Real.exp s * q₃ = Real.exp s * (P₃ * Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ))) := by
          rw [hP₃eq]
        _ = Real.exp s * (Real.exp (Real.log P₃) *
              Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ))) := by
                exact congrArg (fun z : ℝ => Real.exp s *
                  (z * Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ)))) hp
        _ = Real.exp (s + Real.log P₃ - (11 / 1000 : ℝ) * (X.k : ℝ)) := by
          calc
            _ = (Real.exp s * Real.exp (Real.log P₃)) *
                Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ)) := by ring
            _ = Real.exp (s + Real.log P₃) *
                Real.exp (-(11 / 1000 : ℝ) * (X.k : ℝ)) := by rw [← Real.exp_add]
            _ = Real.exp ((s + Real.log P₃) + (-(11 / 1000 : ℝ) * (X.k : ℝ))) := by
              rw [← Real.exp_add]
            _ = Real.exp (s + Real.log P₃ - (11 / 1000 : ℝ) * (X.k : ℝ)) := by
              congr 1 <;> ring
      all_goals rfl
    have hJlogLower : Real.log (n : ℝ) ≤ (X.J : ℝ) * Real.log (n : ℝ) := by
      calc
        Real.log (n : ℝ) = 1 * Real.log (n : ℝ) := by ring
        _ ≤ (X.J : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hJOne) hlogNNonneg
    calc
      _ ≤ Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) +
            (X.J + 1) * Real.log (X.m + 2))) * q₃ := hStep3Alarm
      _ = Real.exp (10 ^ 4 * (X.T * Real.log (X.T + 2) +
            (X.J + 1) * Real.log (X.m + 2)) + Real.log P₃ -
            (11 / 1000 : ℝ) * (X.k : ℝ)) := hExpEq
      _ ≤ Real.exp (-(1 / 10 ^ 6 : ℝ) * ((X.J : ℝ) * Real.log (n : ℝ))) :=
        Real.exp_le_exp.mpr hStep3Exp
      _ ≤ Real.exp (-(1 / 10 ^ 6 : ℝ) * Real.log (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hcoef : 0 ≤ (1 / 10 ^ 6 : ℝ) := by norm_num
        nlinarith [hJlogLower]
      _ = (n : ℝ) ^ (-(1 / 10 ^ 6 : ℝ)) := by
        rw [Real.rpow_def_of_pos hnR]
        congr 1 <;> ring
      _ ≤ 1 / 6 := by
        have h := (hTail3 n hnTail3).le
        simpa [one_div] using h
  have hnotV0Split : ∀ v, ¬ X.V0Good v →
      (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
        (∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
          ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D := by
    intro v hv
    by_cases h1 : ∀ h ∈ X.step1Keys, X.rate1V0 v h ≤ τ1
    · by_cases h2 : ∀ β ∈ X.occTypes, X.rate2V0 v β ≤ τ₂ β.u
      · by_cases h3 : ∀ b ∈ X.g.L.oddStates, ∀ D ∈ X.absDescs b,
            X.rate3V0 v b D ≤ τ₃
        · exact False.elim (hv ⟨h1, h2, h3⟩)
        · right
          right
          push Not at h3
          rcases h3 with ⟨b, hb, D, hD, hbad⟩
          exact ⟨b, hb, D, hD, hbad⟩
      · right
        left
        push Not at h2
        rcases h2 with ⟨β, hβ, hbad⟩
        exact ⟨β, hβ, hbad⟩
    · left
      push Not at h1
      rcases h1 with ⟨h, hh, hbad⟩
      exact ⟨h, hh, hbad⟩
  have hbadV0Pr : X.initLaw.pr (fun v => ¬ X.V0Good v) ≤
      X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 ≤ X.rate1V0 v h) +
        X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) +
          X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
            τ₃ ≤ X.rate3V0 v b D) := by
    have hmono := pr_mono X.initLaw hnotV0Split
    have hUnion12 := FinProb.pr_union X.initLaw
      (fun v => ∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h)
      (fun v => ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β)
    have hUnion123 := FinProb.pr_union X.initLaw
      (fun v => (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
        ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β)
      (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D)
    have hAssoc : X.initLaw.pr (fun v =>
        (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
          ((∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
            ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D)) =
        X.initLaw.pr (fun v =>
          ((∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
            ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
            ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D) := by
      apply pr_congr
      intro v
      exact or_assoc.symm
    have hA1 : X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ≤
        X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 ≤ X.rate1V0 v h) := by
      apply pr_mono
      intro v h
      rcases h with ⟨h, hh, hlt⟩
      exact ⟨h, hh, hlt.le⟩
    have hA2 : X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ≤
        X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) := by
      apply pr_mono
      intro v h
      rcases h with ⟨β, hβ, hlt⟩
      exact ⟨β, hβ, hlt.le⟩
    have hA3 : X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
        τ₃ < X.rate3V0 v b D) ≤
        X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
          τ₃ ≤ X.rate3V0 v b D) := by
      apply pr_mono
      intro v h
      rcases h with ⟨b, hb, D, hD, hlt⟩
      exact ⟨b, hb, D, hD, hlt.le⟩
    calc
      X.initLaw.pr (fun v => ¬ X.V0Good v) ≤
          X.initLaw.pr (fun v =>
            (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
              ((∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
                ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D)) := by
          simpa only [or_assoc] using hmono
      _ = X.initLaw.pr (fun v =>
            (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
              ((∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
                ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D)) := by
          rfl
      _ = X.initLaw.pr (fun v =>
            ((∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
              ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) ∨
              ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b, τ₃ < X.rate3V0 v b D) := hAssoc
      _ ≤ X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) +
            X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) +
              X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                τ₃ < X.rate3V0 v b D) := by
        calc
          _ ≤ X.initLaw.pr (fun v =>
                (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
                  ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) +
                X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                  τ₃ < X.rate3V0 v b D) := hUnion123
          _ = X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                τ₃ < X.rate3V0 v b D) +
              X.initLaw.pr (fun v =>
                (∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) ∨
                  ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) := by ring
          _ ≤ X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                τ₃ < X.rate3V0 v b D) +
              (X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) +
                X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β)) :=
            add_le_add_right hUnion12 _
          _ = X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 < X.rate1V0 v h) +
              X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u < X.rate2V0 v β) +
                X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                  τ₃ < X.rate3V0 v b D) := by ring
      _ ≤ X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 ≤ X.rate1V0 v h) +
            X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) +
              X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                τ₃ ≤ X.rate3V0 v b D) := by linarith
  have hStep1AlarmSmall : X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys,
      τ1 ≤ X.rate1V0 v h) < 1 / 6 := hStep1Alarm.trans_lt hStep1Budget
  have hbadSmall : X.initLaw.pr (fun v => ¬ X.V0Good v) < 1 / 2 := by
    calc
      X.initLaw.pr (fun v => ¬ X.V0Good v) ≤
          X.initLaw.pr (fun v => ∃ h ∈ X.step1Keys, τ1 ≤ X.rate1V0 v h) +
            X.initLaw.pr (fun v => ∃ β ∈ X.occTypes, τ₂ β.u ≤ X.rate2V0 v β) +
              X.initLaw.pr (fun v => ∃ b ∈ X.g.L.oddStates, ∃ D ∈ X.absDescs b,
                τ₃ ≤ X.rate3V0 v b D) := hbadV0Pr
      _ < 1 / 2 := by linarith [hStep1AlarmSmall, hStep2Budget, hStep3Budget]
  have hcomplement : X.initLaw.pr X.V0Good + X.initLaw.pr (fun v => ¬ X.V0Good v) = 1 := by
    classical
    let f : Fin N → ℝ := fun v => if X.V0Good v then X.initLaw.w v else 0
    let g : Fin N → ℝ := fun v => if ¬ X.V0Good v then X.initLaw.w v else 0
    have hGoodEq : X.initLaw.pr X.V0Good = ∑ v, f v := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hgood : X.V0Good v <;> simp [f, hgood]
    have hBadEq : X.initLaw.pr (fun v => ¬ X.V0Good v) = ∑ v, g v := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hgood : X.V0Good v <;> simp [g, hgood]
    calc
      X.initLaw.pr X.V0Good + X.initLaw.pr (fun v => ¬ X.V0Good v) =
          (∑ v, f v) + (∑ v, g v) := by rw [hGoodEq, hBadEq]
      _ = ∑ v, (f v + g v) := Finset.sum_add_distrib.symm
      _ = ∑ v, X.initLaw.w v := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hgood : X.V0Good v <;> simp [f, g, hgood]
      _ = 1 := X.initLaw.sum_eq_one
  have hgoodMass : (1 / 2 : ℝ) ≤ X.initLaw.pr X.V0Good := by
    linarith [hcomplement, hbadSmall]
  exact hgoodMass

set_option maxHeartbeats 200000

/-- L6.1h (coarse base, 06:488–496): grouped probabilities `o(1)` from stage 1 and Markov (conditional future
probabilities have the same sign symmetry given the base, so a bin's union runs over shapes), bounded dependency
degree. -/
theorem L6_1h_coarse (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes → X.CoarseCert := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hDesc hRate
  intro v hV0
  let charge : ℝ := (n : ℝ) ^ (-(δ₁ / 8))
  refine ⟨{
    adj := fun i j => i ≠ j
    adj_symm := by intro i j hij; exact Ne.symm hij
    adj_irrefl := by intro i hij; exact hij rfl
    x := fun _ => charge
    x_nonneg := by intro i; dsimp [charge]; positivity
    x_le := by intro i; rfl
    local_bound := by
      intro i S hiS hdisjoint
      sorry
  }⟩

/-- L6.1h (hidden scalars, 06:498–516): group probabilities `≤ n^{−c₃}` after the pattern unions, dependency
`m^C = n^{Cα + o(1)}`, `Cα < c₃/4`, charges `n^{−c₃/2}`. -/
theorem L6_1h_hidden (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount → X.RateShapes → X.HiddenCert := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hDesc hRate
  intro v c hV0 hSupport
  let charge : ℝ := (n : ℝ) ^ (-(δ₂ / 128))
  let scope : X.Bin × CubeVertex X.m → Finset X.HKey := bad3HiddenScope X
  let adj : X.Bin × CubeVertex X.m → X.Bin × CubeVertex X.m → Prop :=
    fun i j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)
  have hdep : ∀ gr, FinProb.DependsOn
      (fun Z : X.Hid => Z ∈ X.bad3Set (v, c) gr) (scope gr) := by
    intro gr Z Z' hZ
    apply propext
    have hbad : X.Bad3 (v, c) gr Z ↔ X.Bad3 (v, c) gr Z' := by
      unfold Ctx6.Bad3
      constructor
      · intro hbad
        rcases hbad with ⟨x, hxEven, hxBin, hxSign, hfail⟩ |
          ⟨b, hb, hbBin, hbSign, D, hD, hrate⟩
        · left
          refine ⟨x, hxEven, hxBin, hxSign, ?_⟩
          have hobs : ∀ ℓ ∈ (X.evenType x).obs, Z ℓ = Z' ℓ := by
            intro ℓ hℓ
            have hscope : ℓ ∈ scope gr := by
              change ℓ ∈ bad3HiddenScope X gr
              apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_univ _, Or.inl ⟨x, hxEven, hxBin, hxSign, hℓ⟩⟩
            exact hZ ℓ hscope
          exact (step2Fail_iff_of_agree X (v, c) (X.evenType x) Z Z' hobs).mp hfail
        · right
          refine ⟨b, hb, hbBin, hbSign, D, hD, ?_⟩
          have hscopeD : rate3HiddenScope X b D ⊆ scope gr := by
            intro ℓ hℓ
            change ℓ ∈ bad3HiddenScope X gr
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, Or.inr ⟨b, hb, hbBin, hbSign, D, hD, hℓ⟩⟩
          have hrateZ : ∀ ℓ ∈ rate3HiddenScope X b D, Z ℓ = Z' ℓ := by
            intro ℓ hℓ
            exact hZ ℓ (hscopeD hℓ)
          have hrateEq : X.rate3 ((v, c), Z) b D = X.rate3 ((v, c), Z') b D := by
            simpa [Ctx6.rate3] using
              s3FailPr_eq_of_agree X (v, c) b D Z Z' hrateZ
          simpa [hrateEq] using hrate
      · intro hbad
        rcases hbad with ⟨x, hxEven, hxBin, hxSign, hfail⟩ |
          ⟨b, hb, hbBin, hbSign, D, hD, hrate⟩
        · left
          refine ⟨x, hxEven, hxBin, hxSign, ?_⟩
          have hobs : ∀ ℓ ∈ (X.evenType x).obs, Z ℓ = Z' ℓ := by
            intro ℓ hℓ
            have hscope : ℓ ∈ scope gr := by
              change ℓ ∈ bad3HiddenScope X gr
              apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_univ _, Or.inl ⟨x, hxEven, hxBin, hxSign, hℓ⟩⟩
            exact hZ ℓ hscope
          exact (step2Fail_iff_of_agree X (v, c) (X.evenType x) Z Z' hobs).mpr hfail
        · right
          refine ⟨b, hb, hbBin, hbSign, D, hD, ?_⟩
          have hscopeD : rate3HiddenScope X b D ⊆ scope gr := by
            intro ℓ hℓ
            change ℓ ∈ bad3HiddenScope X gr
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, Or.inr ⟨b, hb, hbBin, hbSign, D, hD, hℓ⟩⟩
          have hrateZ : ∀ ℓ ∈ rate3HiddenScope X b D, Z ℓ = Z' ℓ := by
            intro ℓ hℓ
            exact hZ ℓ (hscopeD hℓ)
          have hrateEq : X.rate3 ((v, c), Z) b D = X.rate3 ((v, c), Z') b D := by
            simpa [Ctx6.rate3] using
              s3FailPr_eq_of_agree X (v, c) b D Z Z' hrateZ
          simpa [hrateEq] using hrate
    simpa [Ctx6.bad3Set] using hbad
  refine ⟨{
    adj := adj
    adj_symm := by
      intro i j hij
      exact ⟨Ne.symm hij.1, fun h => hij.2 (Disjoint.symm h)⟩
    adj_irrefl := by intro i hij; exact hij.1 rfl
    x := fun _ => charge
    x_nonneg := by intro i; dsimp [charge]; positivity
    x_le := by intro i; rfl
    local_bound := by
      intro i S hiS hdisjoint
      have hremote : ∀ j ∈ S, Disjoint (scope i) (scope j) := by
        intro j hj
        have hne : i ≠ j := by
          intro hij
          exact hiS (hij ▸ hj)
        by_contra hnot
        exact hdisjoint j hj ⟨hne, hnot⟩
      have hfactor : LocalLemma.mass (X.hidLaw (v, c)).w
          (X.bad3Set (v, c) i ∩ LocalLemma.avoid (X.bad3Set (v, c)) S) =
        (X.hidLaw (v, c)).pr (fun Z => Z ∈ X.bad3Set (v, c) i) *
          LocalLemma.mass (X.hidLaw (v, c)).w
            (LocalLemma.avoid (X.bad3Set (v, c)) S) := by
        simpa [Ctx6.hidLaw, scope] using
          pi_local_mass_factor (fun ℓ : X.HKey => X.hidPost (v, c) ℓ.1)
            (X.Bin × CubeVertex X.m) scope (X.bad3Set (v, c)) i S hdep hremote
      letI : DecidablePred (adj i) := fun j => Classical.propDecidable (adj i j)
      have hprob : (X.hidLaw (v, c)).pr (fun Z => Z ∈ X.bad3Set (v, c) i) ≤
          charge * ∏ j ∈ Finset.univ.filter (adj i), (1 - charge) := by
        sorry
      have hmassNonneg : 0 ≤ LocalLemma.mass (X.hidLaw (v, c)).w
          (LocalLemma.avoid (X.bad3Set (v, c)) S) := by
        rw [finprob_pr_finset_mass]
        exact pr_nonneg (X.hidLaw (v, c)) _
      rw [hfactor]
      exact mul_le_mul_of_nonneg_right hprob hmassNonneg
  }⟩

/-- L6.1h (support, 06:465–468, 06:520–523): positivity of the avoidance masses (Lemma 3.4) makes the stage laws
genuine restrictions; the avoided events are exactly the failures; the Step 2 true gate is a Step 1 test. -/
theorem L6_1h_support (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.V0Mass → X.CoarseCert → X.HiddenCert → X.HistSupport := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hV0Mass hCoarse hHidden
  obtain ⟨hn, _, _⟩ := hLarge
  have hn1 : 1 < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hpowCoarse : (n : ℝ) ^ (-(δ₁ / 8)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg hn1
    norm_num [δ₁]
  have hpowHidden : (n : ℝ) ^ (-(δ₂ / 128)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg hn1
    norm_num [δ₂]
  have hV0Pos : 0 < X.initLaw.pr X.V0Good := by
    have := hV0Mass
    dsimp [Ctx6.V0Mass] at this
    linarith
  have hCoarseAvoidPos : ∀ v, X.V0Good v →
      0 < LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) Finset.univ) := by
    intro v hv
    obtain ⟨cert⟩ := hCoarse v hv
    letI : DecidableRel cert.adj := Classical.decRel _
    have hx1 : ∀ i, cert.x i < 1 := fun i => (cert.x_le i).trans_lt hpowCoarse
    have hca := LocalLemma.conditional_avoidance
      (X.coarseLaw v).w (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one
      (X.bad2Set v) cert.adj cert.adj_symm cert.adj_irrefl
      (fun i => cert.x i * ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j)) cert.x
      (by
        intro i S hi hS
        exact cert.local_bound i S hi hS)
      cert.x_nonneg hx1
      (by intro i; rfl)
    exact hca.1
  have hHiddenAvoidPos : ∀ v c, X.V0Good v → (X.stage2Law v).w c ≠ 0 →
      0 < LocalLemma.mass (X.hidLaw (v, c)).w (LocalLemma.avoid (X.bad3Set (v, c)) Finset.univ) := by
    intro v c hv hc
    obtain ⟨cert⟩ := hHidden v c hv hc
    letI : DecidableRel cert.adj := Classical.decRel _
    have hx1 : ∀ i, cert.x i < 1 := fun i => (cert.x_le i).trans_lt hpowHidden
    have hca := LocalLemma.conditional_avoidance
      (X.hidLaw (v, c)).w (X.hidLaw (v, c)).nonneg (X.hidLaw (v, c)).sum_eq_one
      (X.bad3Set (v, c)) cert.adj cert.adj_symm cert.adj_irrefl
      (fun i => cert.x i * ∏ j ∈ Finset.univ.filter (cert.adj i), (1 - cert.x j)) cert.x
      (by
        intro i S hi hS
        exact cert.local_bound i S hi hS)
      cert.x_nonneg hx1
      (by intro i; rfl)
    exact hca.1
  intro H hH
  have hHistWeight :
      ((X.stage1Law.w H.1.1 * (X.stage2Law H.1.1).w H.1.2) * (X.stage3Law H.1).w H.2) ≠ 0 := by
    simpa [Ctx6.histLaw, FinProb.bind] using hH
  rcases mul_ne_zero_iff.mp hHistWeight with ⟨hStage12, hStage3⟩
  rcases mul_ne_zero_iff.mp hStage12 with ⟨hStage1, hStage2⟩
  have hStage1Spec : X.V0Good H.1.1 ∧ X.initLaw.w H.1.1 ≠ 0 := by
    apply restrictOr6_support_of_pos X.initLaw X.V0Good X.y₀ H.1.1 hV0Pos
    simpa [Ctx6.stage1Law] using hStage1
  have hStage2Pr : 0 < (X.coarseLaw H.1.1).pr (fun c => ∀ w, ¬ X.Bad2 H.1.1 w c) := by
    have hmass := hCoarseAvoidPos H.1.1 hStage1Spec.1
    have havoidPr : 0 < (X.coarseLaw H.1.1).pr
        (fun c => ∀ w ∈ (Finset.univ : Finset X.Bin), c ∉ X.bad2Set H.1.1 w) := by
      rw [← avoid_mass_eq_pr (X.coarseLaw H.1.1) (X.bad2Set H.1.1)]
      exact hmass
    have hprEq :
        (X.coarseLaw H.1.1).pr (fun c => ∀ w, ¬ X.Bad2 H.1.1 w c) =
          (X.coarseLaw H.1.1).pr
            (fun c => ∀ w ∈ (Finset.univ : Finset X.Bin), c ∉ X.bad2Set H.1.1 w) := by
      apply pr_congr
      intro c
      simp [Ctx6.bad2Set]
    rw [hprEq]
    exact havoidPr
  have hStage2Spec :
      (∀ w, ¬ X.Bad2 H.1.1 w H.1.2) ∧ (X.coarseLaw H.1.1).w H.1.2 ≠ 0 := by
    apply restrictOr6_support_of_pos (X.coarseLaw H.1.1)
      (fun c => ∀ w, ¬ X.Bad2 H.1.1 w c) X.fallbackCoarse H.1.2 hStage2Pr
    simpa [Ctx6.stage2Law] using hStage2
  have hStage3Pr : 0 < (X.hidLaw H.1).pr (fun Z => ∀ gr, ¬ X.Bad3 H.1 gr Z) := by
    have hmass := hHiddenAvoidPos H.1.1 H.1.2 hStage1Spec.1 hStage2
    have havoidPr : 0 < (X.hidLaw H.1).pr
        (fun Z => ∀ gr ∈ (Finset.univ : Finset (X.Bin × CubeVertex X.m)), Z ∉ X.bad3Set H.1 gr) := by
      rw [← avoid_mass_eq_pr (X.hidLaw H.1) (X.bad3Set H.1)]
      exact hmass
    have hprEq :
        (X.hidLaw H.1).pr (fun Z => ∀ gr, ¬ X.Bad3 H.1 gr Z) =
          (X.hidLaw H.1).pr
            (fun Z => ∀ gr ∈ (Finset.univ : Finset (X.Bin × CubeVertex X.m)), Z ∉ X.bad3Set H.1 gr) := by
      apply pr_congr
      intro Z
      simp [Ctx6.bad3Set]
    rw [hprEq]
    exact havoidPr
  have hStage3Spec :
      (∀ gr, ¬ X.Bad3 H.1 gr H.2) ∧ (X.hidLaw H.1).w H.2 ≠ 0 := by
    apply restrictOr6_support_of_pos (X.hidLaw H.1)
      (fun Z => ∀ gr, ¬ X.Bad3 H.1 gr Z) (fun _ => X.y₀) H.2 hStage3Pr
    simpa [Ctx6.stage3Law] using hStage3
  have hbaseLaw : (X.coarseLaw H.1.1).w H.1.2 ≠ 0 := hStage2Spec.2
  have hbaseFactors :
      (FinProb.pi (fun _ : X.Bin => X.candLaw H.1.1)).w H.1.2.1 ≠ 0 ∧
      (FinProb.pi (X.tagLawAt (H.1.1, H.1.2.1))).w H.1.2.2 ≠ 0 := by
    have hprod :
        (FinProb.pi (fun _ : X.Bin => X.candLaw H.1.1)).w H.1.2.1 *
          (FinProb.pi (X.tagLawAt (H.1.1, H.1.2.1))).w H.1.2.2 ≠ 0 := by
      simpa [Ctx6.coarseLaw, FinProb.bind] using hbaseLaw
    exact mul_ne_zero_iff.mp hprod
  have hcand : ∀ u, (X.candLaw H.1.1).w (H.1.2.1 u) ≠ 0 := by
    intro u
    exact pi_support_coordinate (fun _ : X.Bin => X.candLaw H.1.1) H.1.2.1 hbaseFactors.1 u
  have htag : ∀ s, (X.tagLawAt (H.1.1, H.1.2.1) s).w (H.1.2.2 s) ≠ 0 := by
    intro s
    exact pi_support_coordinate (X.tagLawAt (H.1.1, H.1.2.1)) H.1.2.2 hbaseFactors.2 s
  have hBaseSupp : X.BaseSupp H.1 := by
    change X.KeysSupp H.1 Finset.univ
    exact ⟨lt_of_le_of_ne (X.initLaw.nonneg H.1.1) (Ne.symm hStage1Spec.2),
      (fun u hu => lt_of_le_of_ne ((X.candLaw H.1.1).nonneg (H.1.2.1 u)) (Ne.symm (hcand u))),
      (fun s hs => lt_of_le_of_ne
        ((X.tagLawAt (H.1.1, H.1.2.1) s).nonneg (H.1.2.2 s)) (Ne.symm (htag s)))⟩
  have hStep1All : ∀ h, h ∈ X.step1Keys → X.Step1OK H.1 h := by
    intro h hh
    by_contra hfail
    have hmem : h ∈ (X.occKeys).biUnion X.C := by simpa [Ctx6.step1Keys] using hh
    obtain ⟨k, hkOcc, hkC⟩ := Finset.mem_biUnion.mp hmem
    obtain ⟨x, hxk⟩ := by simpa [Ctx6.occKeys] using hkOcc
    have hbad : X.Bad2 H.1.1 k.1 H.1.2 := by
      apply Or.inl
      refine ⟨x, congrArg Prod.fst hxk, h, ?_, hfail⟩
      simpa [hxk] using hkC
    exact hStage2Spec.1 k.1 hbad
  have hkeySymm : ∀ a b : X.Key,
      keyAdjacent6 binAdjacent6 a b → keyAdjacent6 binAdjacent6 b a := by
    intro a b hab
    rcases hab with heq | heq | ⟨hflag, hflag', hadj⟩
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq.symm)
    · rcases hadj with ⟨i, hrest, hdist⟩
      refine Or.inr (Or.inr ⟨hflag', hflag, ?_⟩)
      refine ⟨i, ?_, ?_⟩
      · intro j hji
        exact (hrest j hji).symm
      · simpa [Nat.dist_comm] using hdist
  have hselfC : ∀ h : X.Key, h ∈ X.C h := by
    intro h
    change h ∈ keyNeighborhood6 binAdjacent6 h
    simp [keyNeighborhood6, keyAdjacent6]
  have hObsKey : ∀ (x : CubeVertex n) (ell : X.HKey),
      ell ∈ (X.evenType x).obs → ell.1 ∈ X.C (X.g.L.key x) := by
    intro x ell hell
    unfold Ctx6.evenType at hell
    by_cases hj : X.g.L.severity x ≤ X.J
    · simp only [makeType6, if_pos hj, Type6.obs] at hell
      unfold lowObservations6 at hell
      have hell' :
          (∃ s ∈ keyNeighborhood6 binAdjacent6 (X.g.L.key x), (s, X.g.L.sign x) = ell) ∨
          (∃ a ∈ X.g.L.flippable x,
            (X.g.L.key x, Function.update (X.g.L.sign x) a (!X.g.L.sign x a)) = ell) := by
        simpa only [Finset.mem_def, Finset.union_val, Multiset.mem_union, Finset.image_val,
          Multiset.mem_dedup, Multiset.mem_map] using hell
      rcases hell' with hnear | hflip
      · rcases hnear with ⟨s, hs, heq⟩
        have hfst : s = ell.1 := by exact congrArg Prod.fst heq
        simpa [Ctx6.C, hfst] using hs
      · rcases hflip with ⟨a, ha, heq⟩
        have hfst : X.g.L.key x = ell.1 := by exact congrArg Prod.fst heq
        simpa [Ctx6.C, hfst] using hselfC (X.g.L.key x)
    · simp only [makeType6, if_neg hj, Type6.obs] at hell
      by_cases hsev : X.g.L.severity x = X.J + 1
      · have hell' : ell ∈ ({(X.g.L.key x, X.g.L.sign x)} : Finset X.HKey) := by
          rw [highObservations6, if_pos hsev] at hell
          exact hell
        have heq : ell = (X.g.L.key x, X.g.L.sign x) := Finset.mem_singleton.mp hell'
        have hfst : ell.1 = X.g.L.key x := by exact congrArg Prod.fst heq
        simpa [Ctx6.C, hfst] using hselfC (X.g.L.key x)
      · rw [highObservations6, if_neg hsev] at hell
        simp at hell
  have hStep2Tests : ∀ β, β ∈ X.occTypes → X.Step2Tests (H.1, H.2) β := by
    intro β hβ
    by_contra hnotTests
    change β ∈ (Finset.univ.filter fun x : CubeVertex n => IsEvenRole x).image X.evenType at hβ
    obtain ⟨x, hxrole, hxβ⟩ := Finset.mem_image.mp hβ
    have hxEven : IsEvenRole x := (Finset.mem_filter.mp hxrole).2
    have hxkey : X.g.L.key x = β.key := by
      have hkey : X.g.L.key x = (X.evenType x).key := by
        unfold Ctx6.evenType
        by_cases hh : X.g.L.severity x ≤ X.J <;> simp [makeType6, Type6.key, hh]
      exact hkey.trans (congrArg Type6.key hxβ)
    have hGate : X.tagGate H.1 β (H.1.2.2 β.key) := by
      intro ell hell y
      have hellKey : ell.1 ∈ X.C β.key := by
        rw [← hxkey]
        have hell' : ell ∈ (X.evenType x).obs := hxβ.symm ▸ hell
        exact hObsKey x ell hell'
      have hellInStep1 : ell.1 ∈ X.step1Keys := by
        change ell.1 ∈ X.occKeys.biUnion X.C
        apply Finset.mem_biUnion.mpr
        refine ⟨β.key, ?_, hellKey⟩
        change β.key ∈ Finset.univ.image X.g.L.key
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hxkey⟩
      have hrel : keyAdjacent6 binAdjacent6 β.key ell.1 := by
        have hmem : ell.1 ∈ Finset.univ.filter (keyAdjacent6 binAdjacent6 β.key) := by
          simpa [Ctx6.C, keyNeighborhood6] using hellKey
        exact (Finset.mem_filter.mp hmem).2
      have hbetaC : β.key ∈ X.C ell.1 := by
        change β.key ∈ keyNeighborhood6 binAdjacent6 ell.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeySymm β.key ell.1 hrel⟩
      have hdel := (hStep1All ell.1 hellInStep1).2 β.key hbetaC
      have hrep : X.hidPostRep H.1 ell.1 β.key (H.1.2.2 β.key) = X.hidPost H.1 ell.1 := by
        simp [Ctx6.hidPostRep, Ctx6.withTag]
      rw [hrep]
      exact hdel y
    have hfail : X.Step2Fail (H.1, H.2) β := ⟨hGate, hnotTests⟩
    have hfail' : X.Step2Fail (H.1, H.2) (X.evenType x) := hxβ.symm ▸ hfail
    have hbad : X.Bad3 H.1 ((X.g.L.key x).1, X.g.L.sign x) H.2 :=
      Or.inl ⟨x, hxEven, rfl, rfl, hfail'⟩
    exact hStage3Spec.1 _ hbad
  have hRate3 : ∀ b, b ∈ X.g.L.oddStates → ∀ D, D ∈ X.absDescs b →
      X.rate3 (H.1, H.2) b D ≤ Real.exp (-c₂ * X.k) := by
    intro b hb D hD
    by_contra hnot
    have hbad : X.Bad3 H.1 ((X.g.L.stKey b).1, X.g.L.stSign b) H.2 := by
      apply Or.inr
      refine ⟨b, hb, rfl, rfl, D, hD, ?_⟩
      exact lt_of_not_ge hnot
    exact hStage3Spec.1 _ hbad
  have hhidCoord : ∀ ell, (X.hidPost H.1 ell.1).w (H.2 ell) ≠ 0 := by
    intro ell
    exact pi_support_coordinate (fun ell : X.HKey => X.hidPost H.1 ell.1) H.2 hStage3Spec.2 ell
  exact ⟨hBaseSupp,
    (fun ell => lt_of_le_of_ne ((X.hidPost H.1 ell.1).nonneg (H.2 ell))
      (Ne.symm (hhidCoord ell))),
    hStage1Spec.1, hStep1All, hStep2Tests, hRate3⟩

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
