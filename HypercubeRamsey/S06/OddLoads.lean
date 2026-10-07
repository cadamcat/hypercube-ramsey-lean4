import HypercubeRamsey.S06.OddRows
import HypercubeRamsey.S06.OddLoads_q_s06_loads
import HypercubeRamsey.S06.OddLoads_sol_s06_loadA
import HypercubeRamsey.S06.OddLoads_sol_s06_loadD

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
open HypercubeRamsey.Lane_q_s06_loads
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
  have hStages : ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StageFacts :=
    ((stepFacts6 γ p₀ K hadm).and (stageFacts6 γ p₀ K hadm)).mono
      (fun _ _ _ _ _ _ h => h.2 h.1)
  obtain ⟨n₀, C₀, hStages⟩ := hStages
  refine ⟨n₀, C₀, ?_⟩
  intro n N E G M X hLarge hCoarse v hv hGood
  have hStage := hStages n N E G M X hLarge
  have hGoodMass : 0 < X.initLaw.pr X.V0Good :=
    lt_of_lt_of_le (by norm_num) hStage.1
  have hvRaw : X.initLaw.w v ≠ 0 :=
    (restrictOr6_supp hGoodMass hv).2
  have hS₀Mass : 0 < X.par.piPrime.pr (fun z => z ∈ X.par.S₀) := by
    linarith [X.par.S₀_mass]
  have hvS₀ : v ∈ X.par.S₀ :=
    (restrictOr6_supp hS₀Mass (by simpa [Ctx6.initLaw] using hvRaw)).1
  have hInteriorRaw (h : X.Key) (hh : h.2 = .interior) (y : Fin N) :
      (X.coarseLaw v).expect (fun c =>
        if X.Step1OK (v, c) h then (N : ℝ) * (X.hidPost (v, c) h).w y else 0) ≤ 20 * K :=
    Lane_sol_s06_loadA.interior_step1_mean_le X v h hh y hvS₀
  have hnPos : 0 < n := by
    by_contra hn
    have hnZero : n = 0 := by omega
    have hNZero : N ≤ 0 := by simpa [hnZero] using hLarge.2.2
    have hY := X.y₀.isLt
    omega
  have hBoundaryRaw (b : X.Base) (y : Fin N) :
      ((2 : ℝ) ^ n)⁻¹ * ∑ u : CubeVertex n,
        (if X.g.L.boundary u then Lane_sol_s06_loadA.baseLoadTerm X b u y else 0) ≤
          (n : ℝ) ^ (-(1 / 20 : ℝ) + d₁) :=
    Lane_sol_s06_loadA.boundary_baseLoadTerm_average_le X b y hnPos
  have hRawProduct (U : Finset (CubeVertex n))
      (hsep : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → X.g.L.coarseBin u ≠ X.g.L.coarseBin u') (y : Fin N) :
      (X.coarseLaw v).expect (fun c => ∏ u ∈ U,
        (if X.Step1OK (v, c) (X.g.L.coarseBin u, .interior) then
          (N : ℝ) * (X.hidPost (v, c) (X.g.L.coarseBin u, .interior)).w y else 0)) ≤
            (20 * K) ^ U.card :=
    Lane_sol_s06_loadA.interior_step1_product_raw_le X v hvS₀ U
      (fun u => (X.g.L.coarseBin u, .interior)) (fun _ => rfl) hsep y
  -- Remaining: coarse avoidance, near-bin moments, and the simultaneous label estimate.
  sorry

/-- L6.1k (hidden joint, 06:683–689): Lemma 3.4 removal of the stage 3 constraints touching separated targets
(charges `n^{−c₃/2}`, `m^{O(1)}` touching groups), then the proxy bound `2Nπ_{ℓ(b)}(y)` target by target. -/
theorem L6_1k_hjoint (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HiddenCert → X.HistSupport → X.ProxyMean → X.OddHiddenJoint := by
  classical
  rcases hadm with ⟨_hγ, _hγ1, hp₀, _hK⟩
  let α : ℝ := α₆ p₀
  have hα : 0 < α := (height_exponents6_admissible p₀ hp₀).1
  have hαsmall : α ≤ 1 / 10 ^ 12 := (height_exponents6_admissible p₀ hp₀).2.2.1
  obtain ⟨nCharge, hCharge⟩ :=
    _root_.Lane_q_s06_loads.bad3_touch_charge_small_eventually hα hαsmall
  refine ⟨max nCharge 2, 0, ?_⟩
  intro n N E G M X hLarge
  have hnCharge : nCharge ≤ n := le_trans (Nat.le_max_left _ _) hLarge.1
  have hnTwo : 2 ≤ n := le_trans (Nat.le_max_right _ _) hLarge.1
  have hTouchCharge := hCharge n hnCharge
  intro hHiddenCert hHistSupport hProxyMean
  intro v c hv1 hVgood hc U y hUSub hUlow hUcard hFar
  let b₀ : X.Base := (v, c)
  have hRawProxyMean (u : CubeVertex n) (hu : ¬ IsEvenRole u)
      (hLow : X.stMode (X.g.L.stateOf u) = .low) (hy : Fin N)
      (hBase : X.BaseSupp b₀) :
      (X.hidLaw b₀).expect (fun Z => X.proxyMean (b₀, Z) u hy) ≤
        2 * (N : ℝ) * (X.hidPost b₀ (X.tgt (X.g.L.stateOf u)).1).w hy := by
    let t : X.HKey := X.tgt (X.g.L.stateOf u)
    let S : Finset X.HKey := {t}
    let q : X.HKey → FinProb (Fin N) := fun ℓ => X.hidPost b₀ ℓ.1
    let e := Equiv.piEquivPiSubtypeProd (fun ℓ : X.HKey => ℓ ∈ S)
      (fun _ : X.HKey => Fin N)
    let f : X.Hid → ℝ := fun Z => X.proxyMean (b₀, Z) u hy
    change (FinProb.pi q).expect f ≤ _
    apply _root_.Lane_q_s06_loads.pi_expect_le_of_fiber_bound6 q S f
      (2 * (N : ℝ) * (X.hidPost b₀ t.1).w hy)
    intro b
    let Ps := FinProb.pi (fun ℓ : {ℓ // ℓ ∈ S} => q ℓ.1)
    let aξ : Fin N → (∀ ℓ : {ℓ // ℓ ∈ S}, Fin N) :=
      fun ξ => (_root_.Lane_q_s06_loads.singletonPiEquiv6 t).symm ξ
    let Z₀ : X.Hid := e.symm ((fun _ : {ℓ // ℓ ∈ S} => X.y₀), b)
    let H₀ : X.Hist := (b₀, Z₀)
    have hCoord (ξ : Fin N) : aξ ξ ⟨t, Finset.mem_singleton_self t⟩ = ξ := by
      change (_root_.Lane_q_s06_loads.singletonPiEquiv6 t)
        ((_root_.Lane_q_s06_loads.singletonPiEquiv6 t).symm ξ) = ξ
      exact (_root_.Lane_q_s06_loads.singletonPiEquiv6 t).apply_symm_apply ξ
    have hState (ξ : Fin N) : e.symm (aξ ξ, b) = (X.withHid H₀ t ξ).2 := by
      funext ℓ
      by_cases hℓ : ℓ = t
      · subst ℓ
        simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply]
        have ht : t ∈ S := by simp [S]
        rw [dif_pos ht]
        rw [hCoord ξ]
        simp [H₀, Z₀, Ctx6.withHid]
      · simp [e, aξ, Z₀, H₀, S, Ctx6.withHid, Equiv.piEquivPiSubtypeProd, hℓ]
    have hSum :
        (∑ a : ∀ ℓ : {ℓ // ℓ ∈ S}, Fin N,
          Ps.w a * f (e.symm (a, b))) =
          ∑ ξ, (X.hidPost b₀ t.1).w ξ * X.proxyMean (X.withHid H₀ t ξ) u hy := by
      calc
        _ = ∑ ξ, Ps.w (aξ ξ) * f (e.symm (aξ ξ, b)) := by
              rw [_root_.Lane_q_s06_loads.sum_singletonPi6 t
                (fun a => Ps.w a * f (e.symm (a, b)))]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro ξ hξ
              have hw := _root_.Lane_q_s06_loads.pi_singleton_weight6 q t (aξ ξ)
              rw [hw, hCoord ξ, hState ξ]
              rfl
    have hMeanEq (ξ : Fin N) :
        X.proxyMean (X.withHid H₀ t ξ) u hy =
          (N : ℝ) * (X.hp.posLaw).expect (fun P =>
            (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
              X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) := by
      unfold Ctx6.proxyMean
      rw [_root_.Lane_q_s06_loads.centreLaw_expect_as_position_and_proxy]
      calc
        _ = (X.hp.posLaw).expect (fun P => (N : ℝ) *
              (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
                X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) := by
                apply congrArg (fun g => (X.hp.posLaw).expect g)
                funext P
                exact FinProb.expect_smul _ _ _
        _ = _ := FinProb.expect_smul _ _ _
    have hInterchange :
        (∑ ξ, (X.hidPost b₀ t.1).w ξ * X.proxyMean (X.withHid H₀ t ξ) u hy) =
          (N : ℝ) * (X.hp.posLaw).expect (fun P => ∑ ξ,
            (X.hidPost b₀ t.1).w ξ *
              (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
                X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) := by
      let g : Fin N → (X.Loc → Bool) → ℝ := fun ξ P =>
        (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
          X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)
      simp_rw [hMeanEq]
      change (∑ ξ, (X.hidPost b₀ t.1).w ξ *
          ((N : ℝ) * (X.hp.posLaw).expect (g ξ))) =
        (N : ℝ) * (X.hp.posLaw).expect (fun P => ∑ ξ,
          (X.hidPost b₀ t.1).w ξ * g ξ P)
      have hterm (ξ : Fin N) :
          (X.hidPost b₀ t.1).w ξ * (X.hp.posLaw).expect (g ξ) =
            (X.hp.posLaw).expect (fun P => (X.hidPost b₀ t.1).w ξ * g ξ P) := by
        exact (FinProb.expect_smul _ _ _).symm
      have hSumExpect (s : Finset (Fin N)) :
          (∑ ξ ∈ s, (X.hp.posLaw).expect (fun P =>
            (X.hidPost b₀ t.1).w ξ * g ξ P)) =
          (X.hp.posLaw).expect (fun P => ∑ ξ ∈ s,
            (X.hidPost b₀ t.1).w ξ * g ξ P) := by
        classical
        induction s using Finset.induction_on with
        | empty => simp [HypercubeRamsey.FinProb.expect_const]
        | @insert ξ s hξ ih =>
            rw [Finset.sum_insert hξ]
            have hfun : (fun P => ∑ x ∈ insert ξ s,
                (X.hidPost b₀ t.1).w x * g x P) =
                (fun P => (X.hidPost b₀ t.1).w ξ * g ξ P +
                  ∑ x ∈ s, (X.hidPost b₀ t.1).w x * g x P) := by
              funext P
              rw [Finset.sum_insert hξ]
            rw [show (X.hp.posLaw).expect (fun P => ∑ x ∈ insert ξ s,
                (X.hidPost b₀ t.1).w x * g x P) =
                (X.hp.posLaw).expect (fun P =>
                  (X.hidPost b₀ t.1).w ξ * g ξ P +
                    ∑ x ∈ s, (X.hidPost b₀ t.1).w x * g x P) from congrArg _ hfun]
            rw [HypercubeRamsey.FinProb.expect_add, ih]
      calc
        _ = ∑ ξ, (N : ℝ) *
              ((X.hidPost b₀ t.1).w ξ * (X.hp.posLaw).expect (g ξ)) := by
                apply Finset.sum_congr rfl
                intro ξ hξ
                ring
        _ = (N : ℝ) * ∑ ξ,
              (X.hidPost b₀ t.1).w ξ * (X.hp.posLaw).expect (g ξ) := by
                rw [Finset.mul_sum]
        _ = (N : ℝ) * ∑ ξ,
              (X.hp.posLaw).expect (fun P => (X.hidPost b₀ t.1).w ξ * g ξ P) := by
                congr 1
                apply Finset.sum_congr rfl
                intro ξ hξ
                exact hterm ξ
        _ = (N : ℝ) * (X.hp.posLaw).expect (fun P => ∑ ξ,
              (X.hidPost b₀ t.1).w ξ * g ξ P) := by
                congr 1
                exact hSumExpect Finset.univ
    have hPoint (P : X.Loc → Bool) :
        (∑ ξ, (X.hidPost b₀ t.1).w ξ *
          (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
            X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) ≤
          2 * (X.hidPost b₀ t.1).w hy :=
      hProxyMean H₀ P u hBase hu hLow hy
    have hPosMean := FinProb.expect_mono X.hp.posLaw hPoint
    have hPosMean' :
        (X.hp.posLaw).expect (fun P => ∑ ξ,
          (X.hidPost b₀ t.1).w ξ *
            (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
              X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) ≤
          2 * (X.hidPost b₀ t.1).w hy := by
      calc
        _ ≤ (X.hp.posLaw).expect (fun _ => 2 * (X.hidPost b₀ t.1).w hy) := hPosMean
        _ = 2 * (X.hidPost b₀ t.1).w hy := FinProb.expect_const _ _
    calc
      (∑ a : ∀ ℓ : {ℓ // ℓ ∈ S}, Fin N,
          Ps.w a * f (e.symm (a, b))) =
          ∑ ξ, (X.hidPost b₀ t.1).w ξ * X.proxyMean (X.withHid H₀ t ξ) u hy := hSum
      _ = (N : ℝ) * (X.hp.posLaw).expect (fun P => ∑ ξ,
            (X.hidPost b₀ t.1).w ξ *
              (X.proxyLaw (X.withHid H₀ t ξ)).expect (fun ω =>
                X.proxyRow (X.withHid H₀ t ξ) (X.assemble P ω) u hy)) := hInterchange
      _ ≤ 2 * (N : ℝ) * (X.hidPost b₀ t.1).w hy := by
            exact (mul_le_mul_of_nonneg_left hPosMean' (by positivity)).trans_eq (by ring)
  have hStage3Support : ∃ z, (X.stage3Law b₀).w z ≠ 0 := by
    by_contra h
    have hz0 : ∀ z, (X.stage3Law b₀).w z = 0 := by
      intro z
      by_contra hne
      exact h ⟨z, hne⟩
    have hsum : ∑ z, (X.stage3Law b₀).w z = 0 := by simp [hz0]
    have hsumOne := (X.stage3Law b₀).sum_eq_one
    rw [hsum] at hsumOne
    norm_num at hsumOne
  obtain ⟨z₀, hz₀⟩ := hStage3Support
  have hHistWeight : X.histLaw.w (b₀, z₀) ≠ 0 := by
    change (X.stage1Law.w v * (X.stage2Law v).w c) * (X.stage3Law b₀).w z₀ ≠ 0
    exact mul_ne_zero (mul_ne_zero hv1 hc) hz₀
  obtain ⟨hBaseSupp, _, _, _, _, _⟩ := hHistSupport (b₀, z₀) hHistWeight
  have hMeanLocal :
      ∀ u : CubeVertex n, ∀ Z Z' : X.Hid,
        (∀ ℓ ∈ _root_.HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X u,
          Z ℓ = Z' ℓ) →
          X.proxyMean (b₀, Z) u y = X.proxyMean (b₀, Z') u y := by
    sorry
  let scope : CubeVertex n → Finset X.HKey :=
    _root_.HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6 X
  let f : CubeVertex n → X.Hid → ℝ := fun u Z => X.proxyMean (b₀, Z) u y
  have hf : ∀ u, FinProb.DependsOn (f u) (scope u) := by
    intro u Z Z' hZ
    exact hMeanLocal u Z Z' hZ
  have hdis : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → Disjoint (scope u) (scope u') := by
    intro u hu u' hu' hne
    apply _root_.HypercubeRamsey.Lane_q_s06_loads.proxyHidScope6_disjoint X u u'
    simpa [Ctx6.SignFar] using hFar u hu u' hu' hne
  let qH : X.HKey → FinProb (Fin N) := fun ℓ => X.hidPost b₀ ℓ.1
  have hFact := _root_.Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint
    qH U scope f hf hdis
  have hProxyNonneg (H : X.Hist) (u : CubeVertex n) : 0 ≤ X.proxyMean H u y := by
    unfold Ctx6.proxyMean FinProb.expect
    apply Finset.sum_nonneg
    intro C hC
    exact mul_nonneg ((X.centreLaw H).nonneg C)
      (mul_nonneg (by positivity)
        (_root_.HypercubeRamsey.Lane_q_s06_loads.Ctx6.proxyRow_nonneg X H C u y))
  have hRawNonneg (u : CubeVertex n) :
      0 ≤ (X.hidLaw b₀).expect (f u) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro Z hZ
    exact mul_nonneg ((X.hidLaw b₀).nonneg Z) (hProxyNonneg (b₀, Z) u)
  have hRawMean (u : CubeVertex n) (hu : u ∈ U) :
      (X.hidLaw b₀).expect (f u) ≤
        2 * (N : ℝ) * (X.hidPost b₀ (X.tgt (X.g.L.stateOf u)).1).w y := by
    apply hRawProxyMean u
    · have huOdd : ¬ IsEvenRole u := by
        simpa [Ctx6.oddRoles] using hUSub hu
      exact huOdd
    · exact hUlow u hu
    · exact hBaseSupp
  have hRawProduct :
      (X.hidLaw b₀).expect (fun Z => ∏ u ∈ U, f u Z) ≤
        ∏ u ∈ U, 2 * (N : ℝ) * (X.hidPost b₀ (X.tgt (X.g.L.stateOf u)).1).w y := by
    change (FinProb.pi qH).expect (fun Z => ∏ u ∈ U, f u Z) ≤ _
    rw [hFact]
    apply Finset.prod_le_prod₀
    · intro u hu
      exact hRawNonneg u
    · intro u hu
      exact hRawMean u hu
  let scopeUnion : Finset X.HKey :=
    _root_.Lane_q_s06_loads.proxyHidScopeUnion6 X U
  let W : X.Hid → ℝ := fun Z => ∏ u ∈ U, f u Z
  have hWLocal : ∀ Z Z', (∀ ℓ ∈ scopeUnion, Z ℓ = Z' ℓ) → W Z = W Z' := by
    intro Z Z' hZ
    apply Finset.prod_congr rfl
    intro u hu
    apply hMeanLocal u Z Z'
    intro ℓ hℓ
    exact hZ ℓ (Finset.mem_biUnion.mpr ⟨u, hu, hℓ⟩)
  have hW0 : ∀ Z, 0 ≤ W Z := by
    intro Z
    apply Finset.prod_nonneg
    intro u hu
    exact hProxyNonneg (b₀, Z) u
  obtain ⟨cert⟩ := hHiddenCert v c hVgood hc
  let xmax : ℝ := (n : ℝ) ^ (-(δ₂ / 128))
  let B : ℕ := 602 ^ 8 * (9 * (X.m + 1) ^ 8)
  have hBcast : (B : ℝ) =
      602 ^ 8 * (9 * (Nat.ceil ((n : ℝ) ^ α) + 1) ^ 8) := by
    dsimp [B, α]
    rw [Ctx6.m, X.g.m_eq]
    push_cast
    norm_num
  have hsmall : 2 * xmax * (B : ℝ) ≤ Real.log 2 := by
    dsimp [xmax]
    rw [hBcast]
    simpa [α] using hTouchCharge
  have hx0 : 0 ≤ xmax := by
    dsimp [xmax]
    positivity
  have hBposNat : 0 < B := by
    dsimp [B]
    positivity
  have hBge : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hBposNat)
  have hxhalf : xmax ≤ 1 / 2 := by
    have hxmono : 2 * xmax ≤ 2 * xmax * (B : ℝ) := by
      have hprod := mul_nonneg (by positivity : 0 ≤ 2 * xmax) (sub_nonneg.mpr hBge)
      nlinarith
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [hxmono, hsmall, hlog]
  have hxmax : xmax < 1 := by linarith [hxhalf]
  let T : Finset (X.Bin × CubeVertex X.m) :=
    _root_.Lane_q_s06_loads.bad3GroupsTouchProxyUnion6 X U
  let S : Finset (X.Bin × CubeVertex X.m) := Finset.univ \ T
  let bad : (X.Bin × CubeVertex X.m) → Finset X.Hid := X.bad3Set b₀
  let badScope : (X.Bin × CubeVertex X.m) → Finset X.HKey :=
    _root_.HypercubeRamsey.Lane_q_s06_loads.bad3HidScope6 X
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro gr hS hT
    exact (Finset.mem_sdiff.mp hS).2 hT
  have hUnionST : S ∪ T = Finset.univ := by
    ext gr
    simp [S]
  have hEventLocal : ∀ gr (Z Z' : X.Hid),
      (∀ ℓ ∈ badScope gr, Z ℓ = Z' ℓ) → (Z ∈ bad gr ↔ Z' ∈ bad gr) := by
    intro gr Z Z' hZ
    simpa [bad, Ctx6.bad3Set] using
      (_root_.Lane_q_s06_loads.bad3_congr_hidScope X b₀ gr Z Z' hZ)
  have hNotTouch (gr : X.Bin × CubeVertex X.m) (hgr : gr ∈ S) :
      Disjoint scopeUnion (badScope gr) := by
    have hnot : gr ∉ T := (Finset.mem_sdiff.mp hgr).2
    by_contra hdis
    apply hnot
    change gr ∈ Finset.univ.filter
      (fun gr => ¬ Disjoint scopeUnion (badScope gr))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdis⟩
  have hUnionCard : T.card ≤ U.card * B := by
    simpa [B] using
      (_root_.Lane_q_s06_loads.bad3GroupsTouchProxyUnion6_card_le X U)
  have hCharge :
      (∏ gr ∈ T, (1 - cert.x gr)⁻¹) ≤ (2 : ℝ) ^ U.card := by
    apply _root_.Lane_q_s06_loads.avoidance_charge_product_le_two_pow
      T cert.x xmax U.card B hx0 hxhalf
    · intro gr
      exact ⟨cert.x_nonneg gr, by simpa [xmax] using cert.x_le gr⟩
    · exact hUnionCard
    · exact hsmall
  have hJointGoal :
      (X.stage3Law b₀).expect (fun Z => ∏ u ∈ U, X.proxyMean (b₀, Z) u y) ≤
        2 ^ U.card * ∏ u ∈ U,
          (2 * (N : ℝ) * (X.hidPost b₀ (X.tgt (X.g.L.stateOf u)).1).w y) := by
    sorry
  exact hJointGoal

set_option maxHeartbeats 5000000
/-- L6.1k (hidden, 06:680–691): sign neighbourhoods of radius `O(√m)` have fraction `2^{−m+o(m)}` (repeat cost
`n 2^{−m+o(m)} e^{m^{.15}}`); Lemma 3.6 with the joint comparison; the long/short comparison; high rows
`≤ n^{−.13J} n^{.05J}`. -/
theorem L6_1k_hidden (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.OddRowBounds → X.ProxyCap → X.LongShort → X.OddHiddenJoint → X.OddHiddenLoad := by
  classical
  rcases hadm with ⟨hγ, hγ1, hp₀, hK⟩
  let α := α₆ p₀
  have hα : 0 < α := (height_exponents6_admissible p₀ hp₀).1
  obtain ⟨m₀, hmParam⟩ := sign_moment_parameters α hα
  have hpowT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ α) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hceilT : Filter.Tendsto (fun n : ℕ => (Nat.ceil ((n : ℝ) ^ α) : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop (Filter.Eventually.of_forall ?_) hpowT
    intro n
    exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ α))
  have heventM : ∀ᶠ n : ℕ in Filter.atTop,
      (m₀ : ℝ) ≤ (Nat.ceil ((n : ℝ) ^ α) : ℝ) :=
    hceilT.eventually (Filter.eventually_ge_atTop (m₀ : ℝ))
  have heventN : ∀ᶠ n : ℕ in Filter.atTop, 10 ≤ n :=
    Filter.eventually_ge_atTop 10
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (heventN.and heventM)
  refine ⟨n₀, 0, fun n N E G M X hL => ?_⟩
  intro hHistSupport hRowBounds hProxyCap hLongShort hHiddenJoint v c hv1 hVgood hc hbaseCap
  have hn10 : 10 ≤ n := (hn₀ n hL.1).1
  have hnpos : 0 < n := by omega
  have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hmCeil : m₀ ≤ Nat.ceil ((n : ℝ) ^ α) := by
    exact_mod_cast (hn₀ n hL.1).2
  have hm0 : m₀ ≤ X.m := by
    rw [Ctx6.m, X.g.m_eq]
    exact hmCeil
  have hnPow : (n : ℝ) ^ α ≤ (X.m : ℝ) := by
    rw [Ctx6.m, X.g.m_eq]
    exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ α))
  rcases hmParam n X.m hm0 hnPow with ⟨hRadius, hRadiusFrac, hJ20, hMomentSmall⟩
  have hMpos : 0 < X.m := by omega
  have hJ : 20 ≤ X.J := by
    change 20 ≤ Nat.floor ((X.m : ℝ) ^ (1 / 25 : ℝ))
    exact hJ20
  have hJle : X.J ≤ X.m := by
    change Nat.floor ((X.m : ℝ) ^ (1 / 25 : ℝ)) ≤ X.m
    have hMone : (1 : ℝ) ≤ (X.m : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt hMpos))
    have hmpow : (X.m : ℝ) ^ (1 / 25 : ℝ) ≤ (X.m : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hMone (by norm_num)
    have hmpow' : (X.m : ℝ) ^ (1 / 25 : ℝ) ≤ (X.m : ℝ) := by
      simpa [Real.rpow_one] using hmpow
    have hfloor := Nat.floor_mono hmpow'
    simpa using hfloor
  have hCkb0 : 0 ≤ Ckb K := by dsimp [Ckb]; positivity
  let P : FinProb X.Hid := X.stage3Law (v, c)
  let succ : Finset X.Hid := Finset.univ.filter fun z => P.w z ≠ 0
  let Low (u : CubeVertex n) : Prop :=
    ¬ IsEvenRole u ∧ X.stMode (X.g.L.stateOf u) = .low
  let Zfun : CubeVertex n → Fin N → X.Hid → ℝ := fun u y z =>
    if Low u then X.proxyMean ((v, c), z) u y else 0
  let dfun : CubeVertex n → Fin N → ℝ := fun u y =>
    if Low u then
      2 * (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y
    else 0
  let radius : ℕ := 100 * (Nat.sqrt X.m + 1)
  let near : CubeVertex n → Finset (CubeVertex n) := fun u =>
    Finset.univ.filter fun u' => _root_.hammingDist (X.g.L.sign u') (X.g.L.sign u) ≤ radius
  let ballFactor : ℝ :=
    2 * Real.exp (Real.binEntropy (1 / 4 : ℝ) * (X.m : ℝ)) / (2 : ℝ) ^ X.m
  have hRadius' : radius ≤ X.m / 2 := by simpa [radius, Ctx6.m] using hRadius
  have hRadiusFrac' :
      ((radius : ℕ) : ℝ) / (X.m : ℝ) ≤ 1 / 4 := by
    simpa [radius, Ctx6.m] using hRadiusFrac
  have hBallEntropy (t : CubeVertex X.m) :
      ((hammingBall t radius).card : ℝ) ≤
        Real.exp (Real.binEntropy (1 / 4 : ℝ) * (X.m : ℝ)) := by
    have hBall := hammingBall_volume_bound (n := X.m) (r := radius) (v := t)
      (by omega) hRadius'
    have hqmem : ((radius : ℕ) : ℝ) / (X.m : ℝ) ∈ Set.Icc 0 (2⁻¹ : ℝ) :=
      ⟨by positivity, by linarith [hRadiusFrac']⟩
    have hquarter : (1 / 4 : ℝ) ∈ Set.Icc 0 (2⁻¹ : ℝ) := by norm_num
    have hEntropy := Real.binEntropy_strictMonoOn.monotoneOn hqmem hquarter hRadiusFrac'
    calc
      _ ≤ Real.exp (Real.binEntropy (((radius : ℕ) : ℝ) / (X.m : ℝ)) * (X.m : ℝ)) := hBall
      _ ≤ Real.exp (Real.binEntropy (1 / 4 : ℝ) * (X.m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hEntropy (by positivity)
  have hSmall : (n : ℝ) * ballFactor * Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) ≤ 1 := by
    have h := hMomentSmall
    dsimp [ballFactor]
    nlinarith [h]
  have hLabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    have hNupper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hL.2.2
    simpa only [Fintype.card_fin] using hNupper
  have hRoleCard : X.oddRoles.card = 2 ^ (n - 1) := by
    have hpar := (parity_class_card hnpos).2
    have hOddEq : X.oddRoles = Finset.univ \ evenRoleSet n := by
      ext u
      simp [Ctx6.oddRoles, evenRoleSet]
    rw [hOddEq]
    exact hpar
  have hRolePos : 0 < X.oddRoles.card := by rw [hRoleCard]; positivity
  have hCubeCard : Fintype.card (CubeVertex n) = 2 ^ n := by simp
  have hPowNat : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by omega
  have hCubeCardR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hCubeCard
  have hRoleCardR : (X.oddRoles.card : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hRoleCard
  have hPowR : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hPowNat
  have hCkbCap : ∀ y, X.baseAvg (v, c) y ≤ Ckb K := hbaseCap
  have hStage3Supp : ∃ z, P.w z ≠ 0 := by
    by_contra h
    push_neg at h
    have hsum : (∑ z, P.w z) = 0 := Finset.sum_eq_zero fun z hz => h z
    rw [P.sum_eq_one] at hsum
    norm_num at hsum
  obtain ⟨z₀, hz₀⟩ := hStage3Supp
  have hInnerWeight : (FinProb.bind X.stage1Law X.stage2Law).w (v, c) ≠ 0 := by
    change X.stage1Law.w v * (X.stage2Law v).w c ≠ 0
    exact mul_ne_zero hv1 hc
  have hHistWeight (z : X.Hid) (hz : P.w z ≠ 0) :
      X.histLaw.w ((v, c), z) ≠ 0 := by
    change (FinProb.bind X.stage1Law X.stage2Law).w (v, c) * P.w z ≠ 0
    exact mul_ne_zero hInnerWeight hz
  obtain ⟨hBaseSupp, _, _, hStep1, _, _⟩ := hHistSupport ((v, c), z₀) (hHistWeight z₀ hz₀)
  have hSelfC (h : X.Key) : h ∈ X.C h := by
    unfold Ctx6.C
    simp [keyNeighborhood6, keyAdjacent6]
  have hKeyOcc (u : CubeVertex n) : X.g.L.key u ∈ X.occKeys := by
    unfold Ctx6.occKeys
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hStep1Key (u : CubeVertex n) : X.Step1OK (v, c) (X.g.L.key u) :=
    hStep1 (X.g.L.key u) (Finset.mem_biUnion.mpr
      ⟨X.g.L.key u, hKeyOcc u, hSelfC (X.g.L.key u)⟩)
  have hTgtKey (u : CubeVertex n) :
      (X.tgt (X.g.L.stateOf u)).1 = X.g.L.key u := by
    simpa [Ctx6.tgt, ChunkLayout6.stTarget] using X.facts.key_eq u
  have hStep1Target (u : CubeVertex n) :
      X.Step1OK (v, c) (X.tgt (X.g.L.stateOf u)).1 := by
    rw [hTgtKey]
    exact hStep1Key u
  have hRawSum (y : Fin N) :
      (∑ u, dfun u y) = 2 * (∑ u ∈ X.oddRoles,
        if X.stMode (X.g.L.stateOf u) = .low ∧ X.Step1OK (v, c) (X.tgt (X.g.L.stateOf u)).1 then
          (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y else 0) := by
    have hEvenZero (u : CubeVertex n) (hu : IsEvenRole u) : dfun u y = 0 := by
      simp [dfun, Low, hu]
    have hSplit : (∑ u : CubeVertex n, dfun u y) =
        (∑ u ∈ Finset.univ.filter IsEvenRole, dfun u y) +
          ∑ u ∈ Finset.univ.filter (fun u : CubeVertex n => ¬ IsEvenRole u), dfun u y := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := IsEvenRole)]
    have hOddTerms :
      (∑ u ∈ X.oddRoles, dfun u y) = 2 * (∑ u ∈ X.oddRoles,
          if X.stMode (X.g.L.stateOf u) = .low ∧ X.Step1OK (v, c) (X.tgt (X.g.L.stateOf u)).1 then
            (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hodd : ¬ IsEvenRole u := by simpa [Ctx6.oddRoles] using hu
      by_cases hl : X.stMode (X.g.L.stateOf u) = .low
      · simp [dfun, Low, hodd, hl, hStep1Target u]
        <;> ring
      · simp [dfun, Low, hodd, hl]
    rw [hSplit, Finset.sum_eq_zero (by intro u hu; exact hEvenZero u (Finset.mem_filter.mp hu).2)]
    simpa [Ctx6.oddRoles, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hOddTerms
  have hAvgBase (y : Fin N) :
      ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, dfun u y) = X.baseAvg (v, c) y := by
    have hCoef : ((Fintype.card (CubeVertex n) : ℝ)⁻¹) * 2 =
        ((X.oddRoles.card : ℕ) : ℝ)⁻¹ := by
      rw [hCubeCardR, hRoleCardR, hPowR]
      field_simp
    rw [hRawSum]
    calc
      _ = (((Fintype.card (CubeVertex n) : ℝ)⁻¹) * 2) *
          (∑ u ∈ X.oddRoles,
            if X.stMode (X.g.L.stateOf u) = .low ∧ X.Step1OK (v, c) (X.tgt (X.g.L.stateOf u)).1 then
              (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y else 0) := by ring
      _ = (X.oddRoles.card : ℝ)⁻¹ * _ := by rw [hCoef]
      _ = X.baseAvg (v, c) y := rfl
  have hMeanD (y : Fin N) :
      (Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, dfun u y ≤ Ckb K := by
    rw [hAvgBase]
    exact hCkbCap y
  have hD0 : 0 ≤ Ckb K := hCkb0
  have hProxyMean0 (H : X.Hist) (u : CubeVertex n) (y : Fin N) :
      0 ≤ X.proxyMean H u y := by
    unfold Ctx6.proxyMean FinProb.expect
    apply Finset.sum_nonneg
    intro C hC
    exact mul_nonneg ((X.centreLaw H).nonneg C)
      (mul_nonneg (by positivity)
        (HypercubeRamsey.Lane_q_s06_loads.Ctx6.proxyRow_nonneg X H C u y))
  have hZ0 : ∀ u y z, 0 ≤ Zfun u y z := by
    intro u y z
    by_cases hl : Low u
    · simpa [Zfun, hl] using hProxyMean0 ((v, c), z) u y
    · simp [Zfun, hl]
  have hDnonneg : ∀ u y, 0 ≤ dfun u y := by
    intro u y
    by_cases hl : Low u
    · simp only [dfun, if_pos hl]
      exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by positivity))
        ((X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).nonneg y)
    · simp [dfun, hl]
  have hLrow : ∀ u y z, z ∈ succ → Zfun u y z ≤ Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) := by
    intro u y z hz
    by_cases hl : Low u
    · have hzWeight : P.w z ≠ 0 := (Finset.mem_filter.mp hz).2
      have hhistWeight' := hHistWeight z hzWeight
      have hRowBound (C : X.Centre) :
          (N : ℝ) * X.proxyRow ((v, c), z) C u y ≤
            Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) := by
        by_cases hv : X.OddValid ((v, c), z) C X.Rshort (X.g.L.stateOf u)
        · have hcap := hProxyCap ((v, c), z) C u hhistWeight' hl.1 hv y
          have hcap' := hcap.2
          simp [hl.2] at hcap'
          simpa [Ctx6.proxyRow, Ctx6.oddRowAt, hv] using hcap'
        · have hzero : X.proxyRow ((v, c), z) C u y = 0 := by
            simp [Ctx6.proxyRow, Ctx6.oddRowAt, hv]
          rw [hzero]
          simpa using (Real.exp_nonneg ((X.m : ℝ) ^ (15 / 100 : ℝ)))
      have hmean := FinProb.expect_mono (X.centreLaw ((v, c), z)) hRowBound
      calc
        Zfun u y z = X.proxyMean ((v, c), z) u y := by simp [Zfun, hl]
        _ = (X.centreLaw ((v, c), z)).expect
            (fun C => (N : ℝ) * X.proxyRow ((v, c), z) C u y) := rfl
        _ ≤ (X.centreLaw ((v, c), z)).expect
            (fun _ => Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))) := hmean
        _ = Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) := FinProb.expect_const _ _
    · simpa [Zfun, hl] using (Real.exp_nonneg ((X.m : ℝ) ^ (15 / 100 : ℝ)))
  have hf : 0 ≤ ballFactor := by positivity
  have hpowPos : 0 < (2 : ℝ) ^ X.m := by positivity
  have hNear (u : CubeVertex n) :
      ((near u).card : ℝ) ≤ ballFactor * Fintype.card (CubeVertex n) := by
    have h := sign_near_card_le X.g (X.g.L.sign u) radius
    have hBallRatio :
        2 * (hammingBall (X.g.L.sign u) radius).card / (2 : ℝ) ^ X.m ≤ ballFactor := by
      dsimp [ballFactor]
      apply div_le_div_of_nonneg_right ?_ hpowPos.le
      exact mul_le_mul_of_nonneg_left (hBallEntropy (X.g.L.sign u)) (by norm_num)
    calc
      ((near u).card : ℝ) ≤ (2 * (hammingBall (X.g.L.sign u) radius).card / (2 : ℝ) ^ X.m) *
            (2 : ℝ) ^ n := h
      _ ≤ ballFactor * Fintype.card (CubeVertex n) := by
        have hCubeCardR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by exact_mod_cast hCubeCard
        rw [hCubeCardR]
        exact mul_le_mul_of_nonneg_right hBallRatio (by positivity)
  have hSelfNear : ∀ u, u ∈ near u := by
    intro u
    simp [near]
  have hSignFarSymm : ∀ u u', X.SignFar u u' → X.SignFar u' u := by
    intro u u' h
    unfold Ctx6.SignFar at *
    rw [hammingDist_comm]
    exact h
  have hJoint : ∀ (y : Fin N) (k : ℕ), k ≤ n →
      ∀ s : Fin k → CubeVertex n,
        (∀ i j : Fin k, j < i → s i ∉ near (s j)) →
          (∑ z ∈ succ, P.w z * ∏ i, Zfun (s i) y z) ≤
            (2 : ℝ) ^ k * ∏ i, dfun (s i) y := by
    intro y k hk s hsep
    by_cases hAll : ∀ i : Fin k, Low (s i)
    · let S : Finset (CubeVertex n) := Finset.univ.image s
      have hsInj : Function.Injective s := by
        intro i j heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hij | hji
        · have hnot := hsep j i hij
          have hmem : s j ∈ near (s i) := by simpa [heq] using hSelfNear (s i)
          exact hnot hmem
        · have hnot := hsep i j hji
          have hmem : s i ∈ near (s j) := by simpa [heq] using hSelfNear (s j)
          exact hnot hmem
      have hCard : S.card = k := by
        dsimp [S]
        rw [Finset.card_image_of_injective _ hsInj]
        simp
      have hSub : S ⊆ X.oddRoles := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        simpa [Ctx6.oddRoles] using (hAll i).1
      have hLowSet : ∀ u ∈ S, X.stMode (X.g.L.stateOf u) = .low := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        exact (hAll i).2
      have hFarSet : ∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → X.SignFar u u' := by
        intro u hu u' hu' hne
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        rcases Finset.mem_image.mp hu' with ⟨j, hj, rfl⟩
        have hij : i ≠ j := by
          intro heq
          apply hne
          subst j
          rfl
        rcases lt_or_gt_of_ne hij with hij | hji
        · have hnot := hsep j i hij
          have hdist : ¬ _root_.hammingDist (X.g.L.sign (s j)) (X.g.L.sign (s i)) ≤ radius := by
            simpa [near] using hnot
          have hFar : X.SignFar (s j) (s i) := by
            simpa [Ctx6.SignFar, radius] using (not_le.mp hdist)
          exact hSignFarSymm _ _ hFar
        · have hnot := hsep i j hji
          have hdist : ¬ _root_.hammingDist (X.g.L.sign (s i)) (X.g.L.sign (s j)) ≤ radius := by
            simpa [near] using hnot
          simpa [Ctx6.SignFar, radius] using (not_le.mp hdist)
      have hJ :
          P.expect (fun z => ∏ u ∈ S, X.proxyMean ((v, c), z) u y) ≤
            (2 : ℝ) ^ S.card * ∏ u ∈ S,
              (2 * (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y) :=
        hHiddenJoint v c hv1 hVgood hc S y hSub hLowSet (by rw [hCard]; exact hk) hFarSet
      have hProdImage (f : CubeVertex n → ℝ) :
          ∏ u ∈ S, f u = ∏ i : Fin k, f (s i) := by
        dsimp [S]
        exact Finset.prod_image hsInj.injOn
      have hProdZ (z : X.Hid) :
          ∏ i : Fin k, Zfun (s i) y z =
            ∏ u ∈ S, X.proxyMean ((v, c), z) u y := by
        calc
          ∏ i : Fin k, Zfun (s i) y z =
              ∏ i : Fin k, X.proxyMean ((v, c), z) (s i) y := by
                apply Finset.prod_congr rfl
                intro i hi
                change (if Low (s i) then X.proxyMean ((v, c), z) (s i) y else 0) = _
                rw [if_pos (hAll i)]
          _ = ∏ u ∈ S, X.proxyMean ((v, c), z) u y :=
            (hProdImage (fun u => X.proxyMean ((v, c), z) u y)).symm
      have hProdD :
          ∏ i : Fin k, dfun (s i) y =
            ∏ u ∈ S, 2 * (N : ℝ) *
              (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y := by
        calc
          ∏ i : Fin k, dfun (s i) y =
              ∏ i : Fin k, 2 * (N : ℝ) *
                (X.hidPost (v, c) (X.tgt (X.g.L.stateOf (s i))).1).w y := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  change (if Low (s i) then
                    2 * (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf (s i))).1).w y else 0) = _
                  rw [if_pos (hAll i)]
          _ = ∏ u ∈ S, 2 * (N : ℝ) *
              (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y :=
                (hProdImage (fun u => 2 * (N : ℝ) *
                  (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y)).symm
      have hProductNonneg (z : X.Hid) :
          0 ≤ ∏ u ∈ S, X.proxyMean ((v, c), z) u y := by
        apply Finset.prod_nonneg
        intro u hu
        exact hProxyMean0 ((v, c), z) u y
      have hRestrict :
          (∑ z ∈ succ, P.w z * ∏ i : Fin k, Zfun (s i) y z) ≤
            P.expect (fun z => ∏ u ∈ S, X.proxyMean ((v, c), z) u y) := by
        rw [FinProb.expect]
        calc
          (∑ z ∈ succ, P.w z * ∏ i : Fin k, Zfun (s i) y z) =
              ∑ z ∈ succ, P.w z * ∏ u ∈ S, X.proxyMean ((v, c), z) u y := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hProdZ z]
          _ ≤ ∑ z, P.w z * ∏ u ∈ S, X.proxyMean ((v, c), z) u y := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro z hz hzu
                exact mul_nonneg (P.nonneg z) (hProductNonneg z)
      calc
        (∑ z ∈ succ, P.w z * ∏ i : Fin k, Zfun (s i) y z) ≤
            P.expect (fun z => ∏ u ∈ S, X.proxyMean ((v, c), z) u y) := hRestrict
        _ ≤ (2 : ℝ) ^ S.card * ∏ u ∈ S,
            (2 * (N : ℝ) * (X.hidPost (v, c) (X.tgt (X.g.L.stateOf u)).1).w y) := hJ
        _ = (2 : ℝ) ^ k * ∏ i : Fin k, dfun (s i) y := by
              rw [hCard, ← hProdD]
    · have hZero (z : X.Hid) : ∏ i : Fin k, Zfun (s i) y z = 0 := by
        obtain ⟨i, hi⟩ := not_forall.mp hAll
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [Zfun, hi]
      have hLeft : (∑ z ∈ succ, P.w z * ∏ i : Fin k, Zfun (s i) y z) = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        simp [hZero z]
      have hRight : 0 ≤ (2 : ℝ) ^ k * ∏ i : Fin k, dfun (s i) y := by
        apply mul_nonneg (by positivity)
        apply Finset.prod_nonneg
        intro i hi
        exact hDnonneg (s i) y
      rw [hLeft]
      exact hRight
  have hTail := scatteredMoments_union_labels P succ Zfun hZ0
    (Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))) (by positivity) hLrow
    near hSelfNear ballFactor hf hNear n (by omega) 2 (Ckb K)
    (by norm_num) hD0 dfun hDnonneg hMeanD hJoint hSmall hLabels
  let threshold : ℝ := 8 * (Ckb K + 1)
  have hThresholdEq : threshold = 4 * (2 : ℝ) * (Ckb K + 1) := by
    dsimp [threshold]
    norm_num
  have hTailProb :
      P.pr (fun z => ∃ y, threshold <
        ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z)) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    have hEq : P.pr (fun z => ∃ y, threshold <
        ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z)) =
        ∑ z, if z ∈ succ ∧ ∃ y,
          4 * (2 : ℝ) * (Ckb K + 1) <
            ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) then P.w z else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hw : P.w z = 0
      · simp [hw]
      · have hmem : z ∈ succ := by simp [succ, hw]
        rw [hThresholdEq]
        simp [hmem, hw]
    rw [hEq]
    simpa [threshold, mul_assoc] using hTail
  let highCap : ℝ := (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)
  have hLongMeanHigh (z : X.Hid) (hz : P.w z ≠ 0) (u : CubeVertex n)
      (hu : ¬ IsEvenRole u) (hmode : X.stMode (X.g.L.stateOf u) = .high) (y : Fin N) :
      X.longMean ((v, c), z) u y ≤ highCap := by
    have hRow (C : X.Centre) :
        (N : ℝ) * X.oddRow ((v, c), z) C u y ≤ highCap := by
      by_cases hv : X.OddValid ((v, c), z) C X.Rlong (X.g.L.stateOf u)
      · rcases hRowBounds ((v, c), z) C u (hHistWeight z hz) hu hv with
          ⟨_, _, hcap, _, _⟩
        have h := hcap y
        simpa [highCap, hmode] using h
      · have hzero : X.oddRow ((v, c), z) C u y = 0 := by
          simp [Ctx6.oddRow, Ctx6.oddRowAt, hv]
        rw [hzero]
        simpa [highCap] using
          (Real.rpow_nonneg (Nat.cast_nonneg n) ((5 / 100 : ℝ) * X.J))
    have hExp := FinProb.expect_mono (X.centreLaw ((v, c), z)) hRow
    calc
      X.longMean ((v, c), z) u y =
          (X.centreLaw ((v, c), z)).expect (fun C => (N : ℝ) * X.oddRow ((v, c), z) C u y) := rfl
      _ ≤ (X.centreLaw ((v, c), z)).expect (fun _ => highCap) := hExp
      _ = highCap := FinProb.expect_const _ _
  have hLongPoint (z : X.Hid) (hz : P.w z ≠ 0) (u : CubeVertex n)
      (hu : ¬ IsEvenRole u) (y : Fin N) :
      X.longMean ((v, c), z) u y ≤ Zfun u y z +
        (if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) + 1 := by
    cases hmode : X.stMode (X.g.L.stateOf u) with
    | low =>
        have h := hLongShort ((v, c), z) u (hHistWeight z hz) hu y
        have hLow : Low u := ⟨hu, hmode⟩
        have hZeq : Zfun u y z = X.proxyMean ((v, c), z) u y := by
          simp only [Zfun, if_pos hLow]
        change X.longMean ((v, c), z) u y ≤ X.proxyMean ((v, c), z) u y + 1 at h
        rw [← hZeq] at h
        simpa [hmode] using h
    | high =>
        have h := hLongMeanHigh z hz u hu hmode y
        have h' : X.longMean ((v, c), z) u y ≤ highCap + 1 :=
          h.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
        have hNotLow : ¬ Low u := by
          intro hlow
          exact Mode6.noConfusion (hlow.2.symm.trans hmode)
        have hZeq : Zfun u y z = 0 := by
          simp only [Zfun, if_neg hNotLow]
        rw [hZeq]
        simpa [hmode] using h'
  have hZSum (z : X.Hid) (y : Fin N) :
      (∑ u, Zfun u y z) =
        ∑ u ∈ X.oddRoles, if X.stMode (X.g.L.stateOf u) = .low then
          X.proxyMean ((v, c), z) u y else 0 := by
    have hEvenZero : ∑ u ∈ Finset.univ.filter IsEvenRole, Zfun u y z = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have heven : IsEvenRole u := (Finset.mem_filter.mp hu).2
      simp [Zfun, Low, heven]
    have hOddSet : Finset.univ.filter (fun u : CubeVertex n => ¬ IsEvenRole u) = X.oddRoles := rfl
    calc
      (∑ u, Zfun u y z) =
          (∑ u ∈ Finset.univ.filter IsEvenRole, Zfun u y z) +
            ∑ u ∈ Finset.univ.filter (fun u : CubeVertex n => ¬ IsEvenRole u), Zfun u y z := by
              rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := IsEvenRole)]
      _ = ∑ u ∈ X.oddRoles, Zfun u y z := by rw [hEvenZero, hOddSet]; simp
      _ = ∑ u ∈ X.oddRoles, if X.stMode (X.g.L.stateOf u) = .low then
          X.proxyMean ((v, c), z) u y else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            have huodd : ¬ IsEvenRole u := by simpa [Ctx6.oddRoles] using hu
            simp [Zfun, Low, huodd]
  have hCubeOddAvg (z : X.Hid) (y : Fin N) :
      ((X.oddRoles.card : ℝ)⁻¹ *
        ∑ u ∈ X.oddRoles, if X.stMode (X.g.L.stateOf u) = .low then
          X.proxyMean ((v, c), z) u y else 0) =
        2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) := by
    have hCoef : ((Fintype.card (CubeVertex n) : ℝ)⁻¹) * 2 =
        (X.oddRoles.card : ℝ)⁻¹ := by
      rw [hCubeCardR, hRoleCardR, hPowR]
      field_simp
    rw [hZSum]
    calc
      _ = (((Fintype.card (CubeVertex n) : ℝ)⁻¹) * 2) *
          (∑ u ∈ X.oddRoles, if X.stMode (X.g.L.stateOf u) = .low then
            X.proxyMean ((v, c), z) u y else 0) := by rw [hCoef]
      _ = _ := by ring
  have hOddCardPosR : 0 < (X.oddRoles.card : ℝ) := by exact_mod_cast hRolePos
  let highRoles : Finset (CubeVertex n) := X.oddRoles.filter
    fun u => X.stMode (X.g.L.stateOf u) = .high
  let tailRoles : Finset (CubeVertex n) := Finset.univ.filter
    fun u => X.J ≤ X.g.L.severity u
  have hHighSub : highRoles ⊆ tailRoles := by
    intro u hu
    have hmode : X.stMode (X.g.L.stateOf u) = .high := (Finset.mem_filter.mp hu).2
    have hmode' : modeOf6 X.J (X.g.L.stSeverity (X.g.L.stateOf u)) = .high := hmode
    rw [X.facts.severity_eq u] at hmode'
    simp [modeOf6] at hmode'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hSeverityTail :
      ((tailRoles.card : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) := by
    simpa [tailRoles] using X.g.severity_tail X.J (by omega) hJle
  have hHighRatio :
      ((highRoles.card : ℕ) : ℝ) / (X.oddRoles.card : ℝ) ≤
        2 * (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) := by
    have hcard : (highRoles.card : ℝ) ≤ (tailRoles.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hHighSub
    calc
      (highRoles.card : ℝ) / (X.oddRoles.card : ℝ) ≤
          (tailRoles.card : ℝ) / (X.oddRoles.card : ℝ) :=
        div_le_div_of_nonneg_right hcard hOddCardPosR.le
      _ = 2 * ((tailRoles.card : ℝ) / (2 : ℝ) ^ n) := by
        rw [hRoleCardR, hPowR]
        field_simp
        <;> ring
      _ ≤ 2 * (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) :=
        mul_le_mul_of_nonneg_left hSeverityTail (by norm_num)
  have hHighTermSum (z : X.Hid) (y : Fin N) :
      (∑ u ∈ X.oddRoles,
        if X.stMode (X.g.L.stateOf u) = .high then X.longMean ((v, c), z) u y else 0) =
          ∑ u ∈ highRoles, X.longMean ((v, c), z) u y := by
    rw [← Finset.sum_filter]
  have hHighCapSum (z : X.Hid) (hz : P.w z ≠ 0) (y : Fin N) :
      (∑ u ∈ highRoles, X.longMean ((v, c), z) u y) ≤
        (highRoles.card : ℝ) * highCap := by
    calc
      _ ≤ ∑ u ∈ highRoles, highCap := by
        apply Finset.sum_le_sum
        intro u hu
        have huodd : ¬ IsEvenRole u := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
        have hmode : X.stMode (X.g.L.stateOf u) = .high := (Finset.mem_filter.mp hu).2
        exact hLongMeanHigh z hz u huodd hmode y
      _ = (highRoles.card : ℝ) * highCap := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hHighCapTermSum :
      (∑ u ∈ X.oddRoles,
        if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) =
          ∑ u ∈ highRoles, highCap := by
    rw [← Finset.sum_filter]
  have hHighAvg :
      (X.oddRoles.card : ℝ)⁻¹ *
        (∑ u ∈ X.oddRoles,
          if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) ≤ 1 := by
    rw [hHighCapTermSum]
    calc
      (X.oddRoles.card : ℝ)⁻¹ *
          (∑ u ∈ highRoles, highCap) =
        (X.oddRoles.card : ℝ)⁻¹ * ((highRoles.card : ℝ) * highCap) :=
          by simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((highRoles.card : ℝ) / (X.oddRoles.card : ℝ)) * highCap := by
        field_simp [ne_of_gt hOddCardPosR]
        <;> ring
      _ ≤ (2 * (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J)) * highCap :=
        mul_le_mul_of_nonneg_right hHighRatio (by positivity)
      _ ≤ 1 := by
        have hJreal : (20 : ℝ) ≤ (X.J : ℝ) := by exact_mod_cast hJ
        have hexp : - (8 / 100 : ℝ) * X.J ≤ -1 := by nlinarith [hJreal]
        have hpow : (n : ℝ) ^ (- (8 / 100 : ℝ) * X.J) ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnReal hexp
        have hpowEq : (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) *
            (n : ℝ) ^ ((5 / 100 : ℝ) * X.J) =
              (n : ℝ) ^ (- (8 / 100 : ℝ) * X.J) := by
          rw [← Real.rpow_add hnRealPos]
          congr 1
          ring
        have hInv : (n : ℝ) ^ (-1 : ℝ) = 1 / (n : ℝ) := by
          rw [Real.rpow_neg hnRealPos.le, Real.rpow_one]
          exact (one_div (n : ℝ)).symm
        dsimp [highCap]
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
        have hTwoOverN : 2 / (n : ℝ) ≤ 1 := (div_le_one₀ hnRealPos).2 (by linarith)
        calc
          2 * (n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) *
              (n : ℝ) ^ ((5 / 100 : ℝ) * X.J) =
              2 * (n : ℝ) ^ (- (8 / 100 : ℝ) * X.J) := by
                calc
                  _ = 2 * ((n : ℝ) ^ (- (13 / 100 : ℝ) * X.J) *
                      (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) := by ring
                  _ = _ := by rw [hpowEq]
          _ ≤ 2 * (n : ℝ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
          _ = 2 / (n : ℝ) := by rw [hInv]; ring
          _ ≤ 1 := hTwoOverN
  have hOddZSum (z : X.Hid) (y : Fin N) :
      (∑ u ∈ X.oddRoles, Zfun u y z) =
        ∑ u ∈ X.oddRoles, if X.stMode (X.g.L.stateOf u) = .low then
          X.proxyMean ((v, c), z) u y else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have huodd : ¬ IsEvenRole u := by simpa [Ctx6.oddRoles] using hu
    simp [Zfun, Low, huodd]
  have hOddZAvg (z : X.Hid) (y : Fin N) :
      (X.oddRoles.card : ℝ)⁻¹ * (∑ u ∈ X.oddRoles, Zfun u y z) =
        2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) := by
    rw [hOddZSum]
    exact hCubeOddAvg z y
  have hLongAvgBound (z : X.Hid) (hz : P.w z ≠ 0) (y : Fin N) :
      X.longAvg ((v, c), z) y ≤
        2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) + 2 := by
    have hsum : (∑ u ∈ X.oddRoles, X.longMean ((v, c), z) u y) ≤
        (∑ u ∈ X.oddRoles, Zfun u y z) +
          (∑ u ∈ X.oddRoles,
            if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) +
          (X.oddRoles.card : ℝ) := by
      calc
        _ ≤ ∑ u ∈ X.oddRoles,
            (Zfun u y z +
              (if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) + 1) := by
                apply Finset.sum_le_sum
                intro u hu
                have huodd : ¬ IsEvenRole u := by simpa [Ctx6.oddRoles] using hu
                exact hLongPoint z hz u huodd y
        _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
              simp [Finset.sum_const, nsmul_eq_mul]
    have hsumScaled := mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr hOddCardPosR.le)
    calc
      X.longAvg ((v, c), z) y =
          (X.oddRoles.card : ℝ)⁻¹ *
            ∑ u ∈ X.oddRoles, X.longMean ((v, c), z) u y := rfl
      _ ≤ (X.oddRoles.card : ℝ)⁻¹ *
          ((∑ u ∈ X.oddRoles, Zfun u y z) +
            (∑ u ∈ X.oddRoles,
              if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) +
            (X.oddRoles.card : ℝ)) := hsumScaled
      _ = (X.oddRoles.card : ℝ)⁻¹ * (∑ u ∈ X.oddRoles, Zfun u y z) +
          (X.oddRoles.card : ℝ)⁻¹ *
            (∑ u ∈ X.oddRoles,
              if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) +
            (X.oddRoles.card : ℝ)⁻¹ * (X.oddRoles.card : ℝ) := by ring
      _ = (X.oddRoles.card : ℝ)⁻¹ * (∑ u ∈ X.oddRoles, Zfun u y z) +
          (X.oddRoles.card : ℝ)⁻¹ *
            (∑ u ∈ X.oddRoles,
              if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) + 1 := by
                have hInvCard : (X.oddRoles.card : ℝ)⁻¹ *
                    (X.oddRoles.card : ℝ) = 1 := inv_mul_cancel₀ hOddCardPosR.ne'
                rw [hInvCard]
      _ ≤ 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) + 2 := by
        rw [hOddZAvg z y]
        have hHigh := hHighAvg
        calc
          _ = 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) +
              ((X.oddRoles.card : ℝ)⁻¹ *
                (∑ u ∈ X.oddRoles,
                  if X.stMode (X.g.L.stateOf u) = .high then highCap else 0) + 1) := by ring
          _ ≤ 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) + (1 + 1) := by
            let A : ℝ := 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z)
            let B : ℝ := (X.oddRoles.card : ℝ)⁻¹ *
              (∑ u ∈ X.oddRoles,
                if X.stMode (X.g.L.stateOf u) = .high then highCap else 0)
            have hB : B ≤ 1 := hHigh
            have hB' : B + 1 ≤ 1 + 1 := add_le_add_left hB 1
            change A + (B + 1) ≤ A + (1 + 1)
            calc
              A + (B + 1) = (B + 1) + A := by ring
              _ ≤ (1 + 1) + A := add_le_add_left hB' A
              _ = A + (1 + 1) := by ring
          _ = _ := by ring
  have hScale : 1 ≤ Ckb K + 1 := by linarith [hCkb0]
  have hThresholdLarge : 2 * threshold + 2 < Ckh K := by
    dsimp [threshold, Ckh]
    norm_num
    nlinarith [hScale]
  have hEventSub : ∀ z, P.w z ≠ 0 →
      (∃ y, Ckh K < X.longAvg ((v, c), z) y) →
      ∃ y, threshold < (Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z := by
    intro z hz hbad
    obtain ⟨y, hy⟩ := hbad
    by_contra hnot
    push_neg at hnot
    have havg := hnot y
    have hlong := hLongAvgBound z hz y
    have hlong' : X.longAvg ((v, c), z) y ≤ 2 * threshold + 2 := by
      calc
        _ ≤ 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ u, Zfun u y z) + 2 := hlong
        _ ≤ 2 * threshold + 2 := by nlinarith [havg]
    linarith
  have hPrMono := pr_mono_supp6 P (fun z hz hbad => hEventSub z hz hbad)
  exact hPrMono.trans (hTailProb.trans (nat_two_pow_union_tail hn10))

/-- L6.1k (centres, 06:693–704): long computations at residual distance `> 2r + o(n)` use disjoint primitive
randomness; their means are the long means; caps handle close repeats. -/
theorem L6_1k_centres (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.OddRowBounds → X.OddCentreLoad := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hRows H hH hLong
  have hRow0 (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
      0 ≤ (N : ℝ) * X.oddRow H C u y :=
    mul_nonneg (Nat.cast_nonneg N) (Lane_sol_s06_loadA.oddRow_nonneg X H C u y)
  have hCap (C : X.Centre) (u : CubeVertex n) (hu : ¬ IsEvenRole u) (y : Fin N) :
      (N : ℝ) * X.oddRow H C u y ≤
        max (Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))) ((n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) :=
    Lane_sol_s06_loadA.oddRow_cap X hRows H hH C u hu y
  have hMean (y : Fin N) : (X.centreLaw H).expect (fun C => X.rowAvg H C y) = X.longAvg H y := by
    unfold Ctx6.rowAvg Ctx6.longAvg
    rw [FinProb.expect_smul]
    congr 1
    unfold Ctx6.longMean FinProb.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  -- Remaining: spatial scopes of long rows and the scattered-moment union estimate.
  sorry

/-- L6.1l (base, 06:713–749): rows outside interior `j = 0` are bounded deterministically (`T_β ≤ n^{d₂u}Λ`,
balance, rarity); at interior `j = 0` the cancellation `E_{I_h,Z_S}[f_x] ≤ N ∑_i T₀(i)μ_i(a)`, `T₀ ≤ O(η_{A_w})`,
`E_Π η = Λ`; scattered moments under stage 2. -/
theorem L6_1l_base (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step2Dom → X.CoarseCert → X.EvenBaseMean := by
  have hStages : ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StageFacts :=
    ((stepFacts6 γ p₀ K hadm).and (stageFacts6 γ p₀ K hadm)).mono
      (fun _ _ _ _ _ _ h => h.2 h.1)
  obtain ⟨n₀, C₀, hStages⟩ := hStages
  obtain ⟨nRare, hRare⟩ := Filter.eventually_atTop.1
    (Lane_sol_s06_loadD.outside_interiorZero_eventually_small K)
  refine ⟨max n₀ nRare, C₀, ?_⟩
  intro n N E G M X hLarge hTag hDom hCoarse v hv hGood
  have hStage := hStages n N E G M X
    ⟨le_trans (Nat.le_max_left _ _) hLarge.1, hLarge.2⟩
  have hNumerical := hRare n (le_trans (Nat.le_max_right _ _) hLarge.1)
  have hGoodMass : 0 < X.initLaw.pr X.V0Good :=
    lt_of_lt_of_le (by norm_num) hStage.1
  have hvRaw : X.initLaw.w v ≠ 0 :=
    (restrictOr6_supp hGoodMass hv).2
  have hvPos : 0 < X.initLaw.w v :=
    lt_of_le_of_ne (X.initLaw.nonneg v) (Ne.symm hvRaw)
  have hInteriorRaw (x : CubeVertex n) (hh : (X.evenType x).key.2 = .interior) (a : Fin N) :
      (X.coarseLaw v).expect (fun c => X.phiEven (v, c) x a) ≤ 20 * K / c₁ := by
    exact Lane_sol_s06_loadA.interior_gatedTagMixture_mean_le X v (X.evenType x) hh hvPos a
  have hPhiCap (b : X.Base) (x : CubeVertex n) (hx : IsEvenRole x)
      (hSupp : X.KeysSupp b {(X.evenType x).key}) (a : Fin N) :
      X.phiEven b x a ≤ (n : ℝ) ^ (d₂ * (X.evenType x).u) * K := by
    apply Lane_sol_s06_loadA.gatedTagMixture_hiddenMean_cap X hDom b (X.evenType x) _ hSupp a
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hOutside (c : X.Coarse) (hc : (X.stage2Law v).w c ≠ 0) (a : Fin N) :
      (X.evenRoles.card : ℝ)⁻¹ * ∑ x ∈ X.evenRoles,
        (if Lane_sol_s06_loadD.InteriorZero X x then 0 else X.phiEven (v, c) x a) ≤ 2 := by
    have hStage3Supp : ∃ z, (X.stage3Law (v, c)).w z ≠ 0 := by
      by_contra h
      push_neg at h
      have hsum : (∑ z, (X.stage3Law (v, c)).w z) = 0 :=
        Finset.sum_eq_zero fun z _ => h z
      rw [(X.stage3Law (v, c)).sum_eq_one] at hsum
      norm_num at hsum
    obtain ⟨z, hz⟩ := hStage3Supp
    have hHistWeight : X.histLaw.w ((v, c), z) ≠ 0 := by
      change (X.stage1Law.w v * (X.stage2Law v).w c) * (X.stage3Law (v, c)).w z ≠ 0
      exact mul_ne_zero (mul_ne_zero hv hc) hz
    have hBaseSupp := (hStage.2.2.2 ((v, c), z) hHistWeight).1
    exact Lane_sol_s06_loadD.outside_evenMean_average_le_two X hDom (v, c) hBaseSupp
      hNumerical.1 hNumerical.2.1 hNumerical.2.2 a
  -- Remaining: coarse-stage separated products, scattered moments, and the label union.
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
