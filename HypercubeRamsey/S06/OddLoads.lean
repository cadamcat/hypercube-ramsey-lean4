import HypercubeRamsey.S06.OddRows

/-!
# Odd loads through the three histories, and the additional even history mean

L6.1k (06:659–704) and L6.1l (06:706–757).  Averages are over actual roles, with zero outside the indicated low or
high class.  Each average is controlled by Lemma 3.6 (`scattered_moments`) under one stage law, the next stage
starting from the good histories of the previous one:

* odd loads: the base average of `1_{low} N π_{ℓ(b)}(y)` (times its Step 1 indicator) under stage 2; the average of
  the long means under stage 3; the average of `N p_b(y)` under the raw centres;
* even mean: the average of the tag mixtures `N ∑_i T_{β(x)}(i) μ_i(a)` — first their conditional means `φ_x`
  under stage 2, then the mixtures themselves under stage 3.

The constants are explicit (they depend only on `K`); the host-size constant `C₀` of the export absorbs them.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- Load constants (06:677, 06:689, 06:698; 06:744, 06:755). -/
def Ckb (K : ℝ) : ℝ := 2 ^ 700 * (K + 1)
def Ckh (K : ℝ) : ℝ := 2 ^ 10 * (Ckb K + 1)
def Ckc (K : ℝ) : ℝ := 2 ^ 10 * (Ckh K + 1)
def Clb (K : ℝ) : ℝ := 2 ^ 700 * (K + 1) / c₁
def Clh (K : ℝ) : ℝ := 2 ^ 10 * (Clb K + 1)

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-! ### Averages over actual roles -/

def oddRoles (_X : Ctx6 γ p₀ K n N E G M) : Finset (CubeVertex n) :=
  Finset.univ.filter fun u => ¬ IsEvenRole u

def evenRoles (_X : Ctx6 γ p₀ K n N E G M) : Finset (CubeVertex n) :=
  Finset.univ.filter fun x => IsEvenRole x

/-- The base average of the low hidden priors, with the Step 1 indicator (06:664–667). -/
def baseAvg (b₀ : X.Base) (y : Fin N) : ℝ :=
  ((X.oddRoles.card : ℕ) : ℝ)⁻¹ * ∑ u ∈ X.oddRoles,
    if X.stMode (X.g.L.stateOf u) = .low ∧ X.Step1OK b₀ (X.tgt (X.g.L.stateOf u)).1 then
      (N : ℝ) * (X.hidPost b₀ (X.tgt (X.g.L.stateOf u)).1).w y
    else 0

/-- The long mean of a role at a history, averaged over raw centres (06:639–640). -/
def longMean (H : X.Hist) (u : CubeVertex n) (y : Fin N) : ℝ :=
  (X.centreLaw H).expect fun C => (N : ℝ) * X.oddRow H C u y

def longAvg (H : X.Hist) (y : Fin N) : ℝ :=
  ((X.oddRoles.card : ℕ) : ℝ)⁻¹ * ∑ u ∈ X.oddRoles, X.longMean H u y

/-- The proxy mean of a role at a history, averaged over raw centres (06:639–640). -/
def proxyMean (H : X.Hist) (u : CubeVertex n) (y : Fin N) : ℝ :=
  (X.centreLaw H).expect fun C => (N : ℝ) * X.proxyRow H C u y

/-- Odd roles whose signs are farther apart than twice the proxy locality `O(√m)` (06:641–643, 06:682–688). -/
def SignFar (u u' : CubeVertex n) : Prop :=
  100 * (Nat.sqrt X.m + 1) < _root_.hammingDist (X.g.L.sign u) (X.g.L.sign u')

/-- The normalized average odd load at a centre outcome (06:697–703). -/
def rowAvg (H : X.Hist) (C : X.Centre) (y : Fin N) : ℝ :=
  ((X.oddRoles.card : ℕ) : ℝ)⁻¹ * ∑ u ∈ X.oddRoles, (N : ℝ) * X.oddRow H C u y

/-- The tag mixture of an even role with its local-test indicator, `f_x(a)` (06:720–727). -/
def fEven (H : X.Hist) (x : CubeVertex n) (a : Fin N) : ℝ :=
  (if X.tagGate H.1 (X.evenType x) (H.1.2.2 (X.evenType x).key) ∧ X.Step2Tests H (X.evenType x) then 1 else 0) *
    ((N : ℝ) * ∑ i, (X.Tβ H (X.evenType x)).w i * (M.μ i).w a)

/-- `φ_x(a) = E_{Z,raw}[f_x | base]` (06:724). -/
def phiEven (b₀ : X.Base) (x : CubeVertex n) (a : Fin N) : ℝ :=
  (X.hidLaw b₀).expect fun Z => X.fEven (b₀, Z) x a

def phiAvg (b₀ : X.Base) (a : Fin N) : ℝ :=
  ((X.evenRoles.card : ℕ) : ℝ)⁻¹ * ∑ x ∈ X.evenRoles, X.phiEven b₀ x a

/-- The average tag mixture `avg_{x∈A} N ∑_i T_{β(x)}(i) μ_i(a)` (06:709–711). -/
def mixAvg (H : X.Hist) (a : Fin N) : ℝ :=
  ((X.evenRoles.card : ℕ) : ℝ)⁻¹ * ∑ x ∈ X.evenRoles,
    (N : ℝ) * ∑ i, (X.Tβ H (X.evenType x)).w i * (M.μ i).w a

/-! ### L6.1k and L6.1l predicates -/

/-- Odd loads, stage 2 (06:664–678). -/
def OddBaseLoad : Prop :=
  ∀ v, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).pr (fun c => ∃ y, Ckb K < X.baseAvg (v, c) y) ≤ 1 / 100

/-- Odd loads, stage 3 (06:680–691). -/
def OddHiddenLoad : Prop :=
  ∀ v c, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).w c ≠ 0 → (∀ y, X.baseAvg (v, c) y ≤ Ckb K) →
    (X.stage3Law (v, c)).pr (fun Z => ∃ y, Ckh K < X.longAvg ((v, c), Z) y) ≤ 1 / 100

/-- Joint comparison of the proxy means of separated low roles under stage 3 (06:683–689): removing the
hidden-stage constraints touching the targets costs a factor `2` each; the targets integrate under their raw
priors, and no other retained proxy mean reads them. -/
def OddHiddenJoint : Prop :=
  ∀ v c, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).w c ≠ 0 →
    ∀ (U : Finset (CubeVertex n)) (y : Fin N), U ⊆ X.oddRoles → (∀ u ∈ U, X.stMode (X.g.L.stateOf u) = .low) →
      U.card ≤ n → (∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → X.SignFar u u') →
        (X.stage3Law (v, c)).expect (fun Z => ∏ u ∈ U, X.proxyMean ((v, c), Z) u y) ≤
          2 ^ U.card * ∏ u ∈ U, (2 * (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y)

/-- Odd loads, raw centres (06:693–704). -/
def OddCentreLoad : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → (∀ y, X.longAvg H y ≤ Ckh K) →
    (X.centreLaw H).pr (fun C => X.AllOddValid H C ∧ ∃ y, Ckc K < X.rowAvg H C y) ≤ 1 / 100

/-- Even history mean, stage 2 (06:713–746). -/
def EvenBaseMean : Prop :=
  ∀ v, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).pr (fun c => ∃ a, Clb K < X.phiAvg (v, c) a) ≤ 1 / 100

/-- Even history mean, stage 3 (06:751–757). -/
def EvenHiddenMean : Prop :=
  ∀ v c, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).w c ≠ 0 → (∀ a, X.phiAvg (v, c) a ≤ Clb K) →
    (X.stage3Law (v, c)).pr (fun Z => ∃ a, Clh K < X.mixAvg ((v, c), Z) a) ≤ 1 / 100

def LoadFacts : Prop :=
  X.OddBaseLoad ∧ X.OddHiddenLoad ∧ X.OddCentreLoad ∧ X.EvenBaseMean ∧ X.EvenHiddenMean ∧ X.OddHiddenJoint

end Ctx6

/-- L6.1k (base, 06:664–678): cap `n^{d₁}`; boundary rows `n^{−.05+d₁}`; at interior keys the raw mean given `V₀`
is the candidate prior (`≤ 20Π ≤ 20K/N`); same-bin fraction `O((2n^{−.04})^{300})`; removing the coarse
constraints touching separated bins costs `O(1)^l` (Lemma 3.4); Lemma 3.6, Markov and the label union. -/
theorem L6_1k_base (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.CoarseCert → X.OddBaseLoad := by
  sorry

/-- L6.1k (hidden joint, 06:683–689): Lemma 3.4 removal of the stage 3 constraints touching separated targets
(charges `n^{−c₃/2}`, `m^{O(1)}` touching groups), then the proxy bound `2Nπ_{ℓ(b)}(y)` target by target. -/
theorem L6_1k_hjoint (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HiddenCert → X.HistSupport → X.ProxyMean → X.OddHiddenJoint := by
  sorry

/-- L6.1k (hidden, 06:680–691): sign neighbourhoods of radius `O(√m)` have fraction `2^{−m+o(m)}` (repeat cost
`n 2^{−m+o(m)} e^{m^{.15}}`); Lemma 3.6 with the joint comparison; the long/short comparison; high rows
`≤ n^{−.13J} n^{.05J}`. -/
theorem L6_1k_hidden (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.OddRowBounds → X.ProxyCap → X.LongShort → X.OddHiddenJoint → X.OddHiddenLoad := by
  sorry

/-- L6.1k (centres, 06:693–704): long computations at residual distance `> 2r + o(n)` use disjoint primitive
randomness; their means are the long means; caps handle close repeats. -/
theorem L6_1k_centres (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.OddRowBounds → X.OddCentreLoad := by
  sorry

/-- L6.1l (base, 06:713–749): rows outside interior `j = 0` are bounded deterministically (`T_β ≤ n^{d₂u}Λ`,
balance, rarity); at interior `j = 0` the cancellation `E_{I_h,Z_S}[f_x] ≤ N ∑_i T₀(i)μ_i(a)`, `T₀ ≤ O(η_{A_w})`,
`E_Π η = Λ`; scattered moments under stage 2. -/
theorem L6_1l_base (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step2Dom → X.CoarseCert → X.EvenBaseMean := by
  sorry

/-- L6.1l (hidden, 06:751–757): scattered moments of the `f_x` under stage 3; removing the constraints touching
separated key lists lets their means integrate to the `φ_x`; on admitted histories `f_x` is the tag mixture. -/
theorem L6_1l_hidden (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HiddenCert → X.Step2Dom → X.EvenHiddenMean := by
  sorry

/-- L6.1k and L6.1l assembled from their nodes. -/
theorem loadFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StepFacts → X.StageFacts → X.OddRowFacts → X.LoadFacts := by
  have h := (L6_1k_base γ p₀ K hadm).and <| (L6_1k_hjoint γ p₀ K hadm).and <| (L6_1k_hidden γ p₀ K hadm).and <|
    (L6_1k_centres γ p₀ K hadm).and <| (L6_1l_base γ p₀ K hadm).and (L6_1l_hidden γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hB, hJ, hH, hC, hEB, hEH⟩ hS hT hO
  obtain ⟨hTD, _hC1, _hD1, _h2, h2d, _h2s, _hS, _hN, _h3l, _h3h, _hbl, _hbh⟩ := hS
  obtain ⟨_hV, hCo, hHi, hSu⟩ := hT
  obtain ⟨_hTa, hRo, hPc, hPr, hLS⟩ := hO
  have hjoint := hJ hHi hSu hPr
  exact ⟨hB hCo, hH hSu hRo hPc hLS hjoint, hC hRo, hEB hTD h2d hCo, hEH hHi h2d, hjoint⟩

end

end S06
end HypercubeRamsey
