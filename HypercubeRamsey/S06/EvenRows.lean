import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.Prob
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.S06.EvenRows_q_s06_ev_c

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

/-!
# Odd injection and even posterior reconstruction

L6.1m (06:759–853).  On entering histories with odd columns at most `1/10`, Lemma 3.9 (`near_product_injection`,
`d = N`) gives a random odd injection with exact marginals `p_b` and joint comparison `(1+o(1))∏` on at most `n²`
queried roles; `JfOK` records exactly these properties of a family of injection laws.

For an actual even role `v`, its selected ID `c` and the type `β(v)`, the remaining primitive variable is the
complete tagged tuple `z` at `(c, β(v))`, with raw law `P_c`.  With every choice and kernel recomputed at `z`,
`F_z(y) = 1_E ∏_{b∼v} p_b(y_b)` and `m_c(y) = ∫ F_z(y) dP_c(z)`; the gate `E` requires presence and legitimate long
selection of `c` at `v`, valid rows on the whole odd-state stars of its actual neighbours, legal eligibility in its
height consultation domain and the position counts.  The `z`-independent reference `Q = ∏ q_b` averages the deleted
posteriors `Q_{−c}` over the possible descriptors containing `(c, β(v))` (uniform at nonmatching neighbours).  The
even row is the average coordinate marginal of the posterior `∝ F_z dP_c`, restricted to labels where its normalized
marginal is at most `e^{.55n}`, normalized; zero on local failure (06:826–836).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- Odd roles as a type. -/
abbrev OddRole6 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- Even roles as a type. -/
abbrev EvenRole6 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

noncomputable instance evenRole6Fintype (n : ℕ) : Fintype (EvenRole6 n) := by
  classical
  exact Subtype.fintype IsEvenRole

noncomputable instance oddRole6Fintype (n : ℕ) : Fintype (OddRole6 n) := by
  classical
  exact Subtype.fintype (fun v => ¬ IsEvenRole v)

/-- The comparison-mean constant of the even rows (06:836–853). -/
def Cm6 : ℝ := 10 ^ 9

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-! ### The success of the odd stage and the injection laws -/

/-- Geometry success, valid odd rows and odd column sums at most `1/10` (06:704, 06:761). -/
def OddGood (H : X.Hist) (C : X.Centre) : Prop :=
  X.GeoGood H C ∧ X.AllOddValid H C ∧ ∀ y, ∑ u ∈ X.oddRoles, X.oddRow H C u y ≤ 1 / 10

/-- A family of odd injection laws with the conclusions of Lemma 3.9 at every good entering outcome (06:761–766). -/
def JfOK (Jf : X.Hist → X.Centre → FinProb (OddRole6 n → Fin N)) : Prop :=
  ∀ H C, X.histLaw.w H ≠ 0 → X.OddGood H C →
    (∀ ω, (Jf H C).w ω ≠ 0 → Function.Injective ω) ∧
    (∀ (u : OddRole6 n) y, (Jf H C).pr (fun ω => ω u = y) = X.oddRow H C u.1 y) ∧
    ∀ (S : Finset (OddRole6 n)) (o : OddRole6 n → Fin N), (S.card : ℝ) ≤ (N : ℝ) ^ (0.025 : ℝ) →
      (Jf H C).pr (fun ω => ∀ u ∈ S, ω u = o u) ≤
        Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ u ∈ S, X.oddRow H C u.1 (o u)

/-- The stagewise law of histories, centres and odd labels. -/
def fullLaw (Jf : X.Hist → X.Centre → FinProb (OddRole6 n → Fin N)) :
    FinProb (X.Hist × (X.Centre × (OddRole6 n → Fin N))) :=
  X.histLaw.bind fun H => (X.centreLaw H).bind (Jf H)

/-! ### The even reconstruction (06:768–836) -/

/-- The actual odd neighbours of a role. -/
def oddNbrs (_X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n) : Finset (OddRole6 n) :=
  Finset.univ.filter fun u => (cube n).Adj v u.1

/-- The type of an even role's state. -/
def evenTy (v : CubeVertex n) : X.Ty := X.stType (X.g.L.stateOf v)

/-- The selected ID at an even role (long rule). -/
def selC (H : X.Hist) (C : X.Centre) (v : CubeVertex n) : X.Loc :=
  (X.choice H C X.Rlong (X.g.L.stateOf v)).getD X.defaultLoc

/-- Replace the complete tagged tuple at one (ID, type) pair; all choices are recomputed from it. -/
def withTuple (C : X.Centre) (c : X.Loc × X.Ty) (z : X.Tuple) : X.Centre :=
  (((X.pos C, Function.update (X.tup C) c z), X.act C), X.ties C)

/-- The local gate `E` at `v` for the ID `c₀` (06:779–785). -/
def EvenGate (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (c₀ : X.Loc) : Prop :=
  X.choice H C X.Rlong (X.g.L.stateOf v) = some c₀ ∧ X.pos C c₀ = true ∧
    (∀ u ∈ X.oddNbrs v, X.OddValid H C X.Rlong (X.g.L.stateOf u.1)) ∧
      X.hp.Legal (X.pos C) (X.elig H C) (X.hp.domBall X.sites (X.site (X.g.L.stateOf v)) X.hp.Rlong) ∧
        ∀ l, ((X.prosp (X.pos C) (X.site (X.g.L.stateOf v)) l).card : ℝ) ≤ 2 * X.hp.lam

/-- `F_z(y) = 1_E ∏_{b∼v} p_b(y_b)`, everything recomputed at `z` (06:775–778). -/
def Fz (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (c₀ : X.Loc) (z : X.Tuple) (y : OddRole6 n → Fin N) :
    ℝ :=
  (if X.EvenGate H (X.withTuple C (c₀, X.evenTy v) z) v c₀ then 1 else 0) *
    ∏ u ∈ X.oddNbrs v, X.oddRow H (X.withTuple C (c₀, X.evenTy v) z) u.1 (y u)

/-- `m_c(y) = ∫ F_z(y) dP_c(z)` at the selected ID. -/
def mc (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) : ℝ :=
  ∑ z, (X.tupleLaw H (X.evenTy v)).w z * X.Fz H C v (X.selC H C v) z y

/-- The possible descriptors at an odd state containing a given (ID, type) pair, at any level pair; they depend
on positions only (06:787–791). -/
def descsWith (H : X.Hist) (C : X.Centre) (b : X.State) (c : X.Loc × X.Ty) : Finset (Finset (X.Loc × X.Ty)) :=
  (Finset.univ : Finset (Fin X.hp.H)).biUnion fun j =>
    (X.descsIn b (X.permAt (X.pos C) b j)).filter fun D => c ∈ D

/-- The uniform law on `Y`. -/
def unifLaw : Law N := normalize6 (fun _ => 1) X.y₀

/-- The reference `q_b`: the uniform average of the deleted posteriors at matching neighbours, uniform otherwise
(06:787–796). -/
def qRef (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (u : OddRole6 n) : Law N :=
  let b := X.g.L.stateOf u.1
  let c : X.Loc × X.Ty := (X.selC H C v, X.evenTy v)
  if X.Matching b c.2 ∧ (X.descsWith H C b c).Nonempty then
    normalize6 (fun y => ∑ D ∈ X.descsWith H C b c, (X.s3Del H b D (X.tup C) c).w y) X.y₀
  else X.unifLaw

/-- `Q(y) = ∏_{b∼v} q_b(y_b)`, independent of `z`. -/
def Qref (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) : ℝ :=
  ∏ u ∈ X.oddNbrs v, (X.qRef H C v u).w (y u)

/-- Local validity of the even row: the gate and the tests `m_c > 0`, `m_c ≥ e^{−.02kn} Q` (06:813–824). -/
def EvenValid (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) : Prop :=
  X.EvenGate H C v (X.selC H C v) ∧ 0 < X.mc H C v y ∧
    Real.exp (-(2 / 100) * X.k * n) * X.Qref H C v y ≤ X.mc H C v y

/-- The average coordinate marginal of the posterior `∝ F_z dP_c` (06:826–827). -/
def evenMarg (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) (a : Fin N) : ℝ :=
  ∑ z, (X.tupleLaw H (X.evenTy v)).w z * X.Fz H C v (X.selC H C v) z y / X.mc H C v y *
    (((Finset.univ.filter fun r => z.2 r = a).card : ℝ) / X.k)

/-- Labels where the normalized marginal exceeds `e^{.55n}` (06:826–828). -/
def heavyLab (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun a => Real.exp ((55 / 100) * n) < (N : ℝ) * X.evenMarg H C v y a

/-- The even row `w_v`: the light part of the marginal, normalized; zero on local failure (06:834–836). -/
def evenRow (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (y : OddRole6 n → Fin N) (a : Fin N) : ℝ :=
  if X.EvenValid H C v y then
    (if a ∈ X.heavyLab H C v y then 0 else X.evenMarg H C v y a) /
      ∑ a' ∈ Finset.univ.filter (fun a' => a' ∉ X.heavyLab H C v y), X.evenMarg H C v y a'
  else 0

/-- Auxiliary product odd sampling (06:836–838). -/
def prodOdd (H : X.Hist) (C : X.Centre) (y : OddRole6 n → Fin N) : ℝ :=
  ∏ u : OddRole6 n, X.oddRow H C u.1 (y u)

/-! ### L6.1m and L6.1n predicates -/

/-- On good odd outcomes the gate holds at the actually selected ID of every even role. -/
def EvenGateDet : Prop :=
  ∀ H C (v : CubeVertex n), X.histLaw.w H ≠ 0 → X.OddGood H C → IsEvenRole v → X.EvenGate H C v (X.selC H C v)

/-- `F_z ≤ e^{.34kn} Q` (06:797–811). -/
def EvenDom : Prop :=
  ∀ H C (v : CubeVertex n) z y, X.histLaw.w H ≠ 0 → IsEvenRole v →
    X.Fz H C v (X.selC H C v) z y ≤ Real.exp ((34 / 100) * X.k * n) * X.Qref H C v y

/-- The `m_c` tests fail with probability `≤ 1/100` jointly with a good odd outcome (06:813–824). -/
def EvenTest : Prop :=
  ∀ Jf, X.JfOK Jf → (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
    ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ (0 < X.mc ω.1 ω.2.1 v ω.2.2 ∧
      Real.exp (-(2 / 100) * X.k * n) * X.Qref ω.1 ω.2.1 v ω.2.2 ≤ X.mc ω.1 ω.2.1 v ω.2.2)) ≤ 1 / 100

/-- Valid even rows are probability rows on common neighbours of the odd labels, with cap `10 e^{.55n}`, and the
light part of the marginal keeps mass at least `.19` (heavy mass `≤ .8 + o(1)`, 06:826–836). -/
def EvenDensity : Prop :=
  ∀ H C (v : CubeVertex n) y, X.histLaw.w H ≠ 0 → IsEvenRole v → X.EvenValid H C v y →
    (∀ a, 0 ≤ X.evenRow H C v y a) ∧ (∑ a, X.evenRow H C v y a = 1) ∧
    (∀ a, X.evenRow H C v y a ≠ 0 → ∀ u ∈ X.oddNbrs v, Hits E G a (y u)) ∧
    (∀ a, (N : ℝ) * X.evenRow H C v y a ≤ 10 * Real.exp ((55 / 100) * n)) ∧
    (19 / 100 : ℝ) ≤
      ∑ a' ∈ Finset.univ.filter (fun a' => a' ∉ X.heavyLab H C v y), X.evenMarg H C v y a'

/-- With one centre forced present and its tuple fixed, the selection probabilities of the IDs at an even role sum
to at most `4`: `O(1/λ)` at level `0` (tie bound) against presence mass `λ`, `exp(−n^{Ω(1)})` above (06:849–853). -/
def SelectBound : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → ∀ (v : CubeVertex n) (z : X.Tuple), IsEvenRole v →
    ∑ c : X.Loc, (X.centreLaw H).expect (fun C =>
      if X.EvenGate H (X.withTuple C (c, X.evenTy v) z) v c then 1 else 0) ≤ 4

/-- Comparison mean of the even rows under product odd sampling and raw centres (06:836–853). -/
def EvenMean : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → ∀ (v : CubeVertex n) (a : Fin N), IsEvenRole v →
    (X.centreLaw H).expect (fun C => ∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
      Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)

/-- The near radius of even rows: twice the locality radius `r + O(R_long)` of a long computation (06:784–785,
06:860–861). -/
def nearR : ℕ := 2 * X.hp.r + 8 * X.hp.Rlong + 100

/-- Joint comparison for at most `n` even rows separated in residual bits (06:857–868): keep the successful entering
history while comparing the queried odd outputs with their product law, drop nonlocal success (each row keeps its
local gate), factor the centre integrals, and use the comparison means. -/
def EvenJoint : Prop :=
  ∀ Jf, X.JfOK Jf → ∀ H, X.histLaw.w H ≠ 0 → ∀ (U : Finset (CubeVertex n)) (a : Fin N),
    U ⊆ X.evenRoles → U.card ≤ n → (∀ v ∈ U, ∀ v' ∈ U, v ≠ v' → X.nearR < X.g.L.residualDist v v') →
      ((X.centreLaw H).bind (Jf H)).expect (fun ω => (if X.OddGood H ω.1 then 1 else 0) *
        ∏ v ∈ U, (N : ℝ) * X.evenRow H ω.1 v ω.2 a) ≤
        2 ^ U.card * ∏ v ∈ U, (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a))

/-- Even column sums exceed one with probability `≤ 1/100` jointly with the retained successes (06:855–884). -/
def EvenLoad : Prop :=
  ∀ Jf, X.JfOK Jf → (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
    (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
    ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ≤ 1 / 100

def EvenFacts : Prop :=
  X.EvenGateDet ∧ X.EvenDom ∧ X.EvenTest ∧ X.EvenDensity ∧ X.EvenMean ∧ X.EvenLoad ∧ X.SelectBound ∧
    X.EvenJoint

end Ctx6

/-- L6.1m (gate, 06:779–785): on good odd outcomes every even state has a legitimate prospective choice, its
neighbours are valid, eligibility is legal everywhere and counts are at most `2λ`. -/
theorem L6_1m_gate (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenGateDet := by
  refine ⟨1, 0, ?_⟩
  intro n N E G M X hL H C v hH hOdd hv
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hL.1
  let a : X.State := X.g.L.stateOf v
  have ha : a ∈ X.g.L.evenStates := by
    unfold a ChunkLayout6.evenStates
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  have hsite : X.site a ∈ X.sites := by
    unfold Ctx6.sites
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hgeo := hOdd.1
  have hheights := hgeo.2.2.2 (X.site a) hsite
  have hheight : X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.Rlong (X.site a) < X.hp.H :=
    hheights.1
  let j := X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.Rlong (X.site a)
  have hbad : ¬ X.hp.Bad (X.pos C) (X.act C) (X.elig H C) (X.site a)
      ⟨X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.Rlong (X.site a), by omega⟩ := by
    intro hb
    exact hheights.2.1 ⟨by omega, hb⟩
  let level : Fin (X.hp.H + 1) := ⟨j, by omega⟩
  have hlegal := hgeo.2.2.1
  have hlocalLegal : X.hp.Legal (X.pos C) (X.elig H C)
      (X.hp.domBall X.sites (X.site a) X.Rlong) := by
    intro q hq l
    exact hlegal q (Finset.mem_filter.mp hq).1 l
  have hcounts := hgeo.1
  have hcount : ∀ l, ((X.prosp (X.pos C) (X.site a) l).card : ℝ) ≤ 2 * X.hp.lam :=
    fun l => (hcounts (X.site a) hsite l).2
  have hoddvalid : ∀ u ∈ X.oddNbrs v, X.OddValid H C X.Rlong (X.g.L.stateOf u.1) := by
    intro u hu
    exact hOdd.2.1 u.1 u.2
  have hLegalAt := hlegal (X.site a) hsite level
  let active : Finset X.Loc := (X.elig H C (X.site a) level).filter
    (fun ℓ => X.act C ℓ = true)
  have hactive : active.Nonempty := by
    by_contra hne
    have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    apply hbad
    left
    intro ℓ hℓ
    cases hact : X.act C ℓ with
    | false => rfl
    | true =>
      have hmem : ℓ ∈ active := Finset.mem_filter.mpr ⟨hℓ, hact⟩
      rw [hempty] at hmem
      exact False.elim (by simpa using hmem)
  have hactiveAt : ({ℓ ∈ X.elig H C (X.site a)
      ⟨X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.Rlong (X.site a), by omega⟩ |
      X.act C ℓ = true}.Nonempty) := by
    simpa [active, level, j] using hactive
  have hselectedSome : (X.choice H C X.Rlong a).isSome := by
    change (X.hp.selectionAt X.sites (X.pos C) (X.act C) (X.elig H C)
      (X.ties C) X.Rlong (X.site a)).isSome
    unfold HDParams.selectionAt
    rw [dif_pos hheight, dif_neg hbad]
    simp [active, level, j, hactiveAt]
  cases hc : X.choice H C X.Rlong a with
  | none => simp [hc] at hselectedSome
  | some c =>
    have hpos : X.pos C c = true := by
      let prioritySet := active.image (fun ℓ => X.hp.priority (X.ties C) (X.site a, level) ℓ)
      have hpriority : prioritySet.Nonempty := Finset.image_nonempty.mpr hactive
      let choiceSpec : ∃ ℓ, ℓ ∈ active ∧
          X.hp.priority (X.ties C) (X.site a, level) ℓ = prioritySet.min' hpriority :=
        Finset.mem_image.mp (Finset.min'_mem prioritySet hpriority)
      have hchoiceRed : X.choice H C X.Rlong a = some (Classical.choose choiceSpec) := by
        change X.hp.selectionAt X.sites (X.pos C) (X.act C) (X.elig H C)
          (X.ties C) X.Rlong (X.site a) = some (Classical.choose choiceSpec)
        unfold HDParams.selectionAt
        rw [dif_pos hheight, dif_neg hbad]
        simp [prioritySet, active, level, j, choiceSpec, hpriority, hactiveAt]
      have hchooseEq : Classical.choose choiceSpec = c := by
        exact Option.some.inj (hchoiceRed.symm.trans hc)
      have hchosen : Classical.choose choiceSpec ∈ active := (Classical.choose_spec choiceSpec).1
      have hcactive : c ∈ active := by rw [← hchooseEq]; exact hchosen
      exact (hLegalAt.1 c (Finset.mem_filter.mp hcactive).1).1
    have hselC : X.selC H C v = c := by simp [Ctx6.selC, a, hc]
    have hcSel : X.choice H C X.Rlong (X.g.L.stateOf v) = some (X.selC H C v) := by
      change X.choice H C X.Rlong a = some (X.selC H C v)
      rw [hselC]
      exact hc
    have hposSel : X.pos C (X.selC H C v) = true := by
      rw [hselC]
      exact hpos
    refine ⟨hcSel, hposSel, ?_, hlocalLegal, hcount⟩
    exact hoddvalid

/-- L6.1m (domination, 06:787–811): at a matching neighbour `p_b ≤ e^{.2k}|𝒟_{b,c}| q_b` with
`log|𝒟_{b,c}| < .1k`; the `o(n^{.4})` other neighbours (coarse or fine chunk flips) cost `o(kn)`. -/
theorem L6_1m_dom (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.OddRowBounds → X.DescCount → X.EvenDom := by
  sorry

/-- L6.1m (tests, 06:813–824): keep the successful prehistory while comparing the queried odd labels with the
product law (`JfOK`), drop nonlocal success, keep `E`; Lemma 3.7 bounds each `(v, c)` by `(1+o(1))e^{−.02kn}`;
the union over `exp(O(n))` pairs. -/
theorem L6_1m_test (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.EvenDom → X.EvenGateDet → X.EvenTest := by
  sorry

/-- L6.1m (density, 06:826–836): joint density `≤ e^{.4kn}` against the uniform product (prior width
`n^γ + log(2/c₁) = o(n)` per coordinate); `Pr(#{j : x_j ∈ 𝓗} > .8k) ≤ 2^k e^{.4kn}(|𝓗|/N)^{.8k} = o(1)`; the
light mass is at least `.19`; support from the neighbouring kernels at the recomputed star. -/
theorem L6_1m_density (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.Step2Supp → X.OddRowBounds → X.EvenDom → X.EvenDensity := by
  sorry

/-- L6.1m (selection, 06:849–853): the forced-centre bounds of Lemma 3.8 (`height_selection_tie`,
`height_selection_positive`) against the position-averaged presence mass. -/
theorem L6_1m_select (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.SelectBound := by
  sorry

/-- L6.1m (comparison mean, 06:836–853): cancellation of the posterior denominator against the data subdensity
(`∫ m_c (F_z dP_c / m_c) dy = dP_c ∫ F_z dy`), rows summing to one bound `∫ F_z dy` by the gate, the selection
bound summed over IDs, and the tuple marginal costs `2/c₁` times the tag mixture; light mass `≥ .19`. -/
theorem L6_1m_mean (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.Step2Supp → X.EvenDensity → X.SelectBound → X.EvenMean := by
  classical
  refine ⟨2, 0, ?_⟩
  intro n N E G M X hLarge hHist hStep2 hDensity hSelect H hH v a hv
  let β : X.Ty := X.evenTy v
  have hβ : β = X.evenType v := by
    dsimp [β, Ctx6.evenTy, Ctx6.stType, Ctx6.evenType]
    rw [ChunkLayout6.stType, X.facts.key_eq v, X.facts.sign_eq v,
      X.facts.flippable_eq v, X.facts.severity_eq v]
  have hocc : β ∈ X.occTypes := by
    rw [hβ]
    unfold Ctx6.occTypes
    exact Finset.mem_image.mpr
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  obtain ⟨hBase, _hHid, _hV₀, _hStep1, hTests, _hRate⟩ := hHist H hH
  have hKeys : X.KeysSupp H.1 (X.typeKeys β) := by
    change X.KeysSupp H.1 Finset.univ at hBase
    obtain ⟨hInit, hCand, hTag⟩ := hBase
    refine ⟨hInit, ?_, ?_⟩
    · intro u hu
      apply hCand u
      rcases Finset.mem_image.mp hu with ⟨key, hkey, rfl⟩
      exact Finset.mem_image.mpr ⟨key, Finset.mem_univ key, rfl⟩
    · intro s hs
      exact hTag s (Finset.mem_univ s)
  have hTestsβ : X.Step2Tests H β := hTests β hocc
  have hTupleMass : ∀ i, 0 < (X.Tβ H β).w i →
      c₁ / 2 ≤ ∑ x ∈ X.reqNbhd H (reqNames6 β), (M.μ i).w x := by
    intro i hi
    exact (hStep2 H β hocc hKeys hTestsβ i hi).1
  have hTuple :=
    Lane_q_s06_ev_c.tuple_empirical_bound6 X H β a hTupleMass
  have hcenter :
      (X.centreLaw H).expect (fun C =>
        ∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
        (N : ℝ) * (100 / 19) * 4 *
          (X.tupleLaw H β).expect
            (fun z => ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) /
              (X.k : ℝ)) := by
    let star := X.oddNbrs v
    let StarY := {u : OddRole6 n // u ∈ star} → Fin N
    let starExt : StarY → (OddRole6 n → Fin N) := fun y =>
      (Equiv.piEquivPiSubtypeProd (fun u : OddRole6 n => u ∈ star)
        (fun _ : OddRole6 n => Fin N)).symm (y, fun _ => X.y₀)
    let freq : X.Tuple → ℝ := fun z =>
      ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) / (X.k : ℝ)
    let mcAt : X.Centre → X.Loc → (OddRole6 n → Fin N) → ℝ := fun C c y =>
      ∑ z, (X.tupleLaw H β).w z * X.Fz H C v c z y
    let margAt : X.Centre → X.Loc → (OddRole6 n → Fin N) → ℝ := fun C c y =>
      ∑ z, (X.tupleLaw H β).w z * X.Fz H C v c z y / mcAt C c y * freq z
    let rowLaw : X.Centre → OddRole6 n → FinProb (Fin N) := fun C u =>
      Lane_q_s06_ev_c.oddRowProb6 X H C u.1
    let rowsLaw : X.Centre → FinProb (OddRole6 n → Fin N) := fun C =>
      FinProb.pi (rowLaw C)
    let q : X.Centre → X.Loc → (OddRole6 n → Fin N) → ℝ := fun C c y =>
      if X.EvenGate H C v c then margAt C c y else 0
    have hFz_nonneg (C : X.Centre) (c : X.Loc) (z : X.Tuple)
        (y : OddRole6 n → Fin N) : 0 ≤ X.Fz H C v c z y := by
      unfold Ctx6.Fz
      apply mul_nonneg
      · split_ifs <;> norm_num
      · apply Finset.prod_nonneg
        intro u hu
        exact Lane_q_s06_ev_c.oddRow_nonneg6 X H
          (X.withTuple C (c, β) z) u.1 (y u)
    have hmc_nonneg (C : X.Centre) (c : X.Loc) (y : OddRole6 n → Fin N) :
        0 ≤ mcAt C c y := by
      dsimp [mcAt]
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg ((X.tupleLaw H β).nonneg z) (hFz_nonneg C c z y)
    have hfreq_nonneg (z : X.Tuple) : 0 ≤ freq z := by
      dsimp [freq]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hmarg_nonneg (C : X.Centre) (c : X.Loc) (y : OddRole6 n → Fin N) :
        0 ≤ margAt C c y := by
      dsimp [margAt]
      apply Finset.sum_nonneg
      intro z hz
      apply mul_nonneg
      · exact div_nonneg
          (mul_nonneg ((X.tupleLaw H β).nonneg z) (hFz_nonneg C c z y))
          (hmc_nonneg C c y)
      · exact hfreq_nonneg z
    have hq_nonneg (C : X.Centre) (c : X.Loc) (y : OddRole6 n → Fin N) :
        0 ≤ q C c y := by
      by_cases hg : X.EvenGate H C v c
      · simp [q, hg, hmarg_nonneg C c y]
      · simp [q, hg]
    have hevenMarg_eq (C : X.Centre) (y : OddRole6 n → Fin N) :
        X.evenMarg H C v y a = margAt C (X.selC H C v) y := by
      simp [Ctx6.evenMarg, Ctx6.mc, mcAt, margAt, freq, β]
    have hrow_nonneg (C : X.Centre) (y : OddRole6 n → Fin N) :
        0 ≤ X.evenRow H C v y a := by
      by_cases hvalid : X.EvenValid H C v y
      · exact (hDensity H C v y hH hv hvalid).1 a
      · simp [Ctx6.evenRow, hvalid]
    have hrow_point (C : X.Centre) (y : OddRole6 n → Fin N) :
        (N : ℝ) * X.evenRow H C v y a ≤
          (N : ℝ) * (100 / 19) * ∑ c : X.Loc, q C c y := by
      let c := X.selC H C v
      by_cases hvalid : X.EvenValid H C v y
      · obtain ⟨_, _, _, _, hlight⟩ := hDensity H C v y hH hv hvalid
        have hgate : X.EvenGate H C v c := hvalid.1
        have hmarg := hmarg_nonneg C c y
        have hrow : X.evenRow H C v y a ≤ (100 / 19) * margAt C c y := by
          by_cases hheavy : a ∈ X.heavyLab H C v y
          · simp [Ctx6.evenRow, hvalid, hheavy, hevenMarg_eq]
            positivity
          · rw [Ctx6.evenRow, if_pos hvalid, if_neg hheavy, hevenMarg_eq]
            calc
              margAt C c y / (∑ a' ∈ Finset.univ.filter
                    (fun a' => a' ∉ X.heavyLab H C v y), X.evenMarg H C v y a') ≤
              margAt C c y / (19 / 100) :=
                    div_le_div_of_nonneg_left hmarg (by norm_num) hlight
              _ = (100 / 19) * margAt C c y := by field_simp
        have hqterm : q C c y = margAt C c y := by simp [q, hgate]
        have hsumq : margAt C c y ≤ ∑ c' : X.Loc, q C c' y := by
          rw [← hqterm]
          exact Finset.single_le_sum (fun c' hc' => hq_nonneg C c' y) (Finset.mem_univ c)
        have hrow' : X.evenRow H C v y a ≤ (100 / 19) * ∑ c' : X.Loc, q C c' y :=
          hrow.trans (mul_le_mul_of_nonneg_left hsumq (by norm_num))
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hrow' (Nat.cast_nonneg N)
      · have hsumq : 0 ≤ ∑ c : X.Loc, q C c y :=
          Finset.sum_nonneg fun c hc => hq_nonneg C c y
        simp [Ctx6.evenRow, hvalid]
        positivity
    have hprod_le (C : X.Centre) (y : OddRole6 n → Fin N) :
        X.prodOdd H C y ≤ (rowsLaw C).w y := by
      dsimp [Ctx6.prodOdd, rowsLaw, FinProb.pi]
      apply Finset.prod_le_prod₀
      · intro u hu
        exact Lane_q_s06_ev_c.oddRow_nonneg6 X H C u.1 (y u)
      · intro u hu
        exact Lane_q_s06_ev_c.oddRow_le_oddRowProb6 X H C u.1 (y u)
    have hlocal_bound (C : X.Centre) :
        ∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a) ≤
          (N : ℝ) * (100 / 19) * ∑ c : X.Loc, (rowsLaw C).expect (q C c) := by
      have hnonneg (y : OddRole6 n → Fin N) : 0 ≤ (N : ℝ) * X.evenRow H C v y a :=
        mul_nonneg (Nat.cast_nonneg N) (hrow_nonneg C y)
      have hfirst :
          (∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
            ∑ y, (rowsLaw C).w y * ((N : ℝ) * X.evenRow H C v y a) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right (hprod_le C y) (hnonneg y)
      have hsecond :
          (∑ y, (rowsLaw C).w y * ((N : ℝ) * X.evenRow H C v y a)) ≤
            ∑ y, (rowsLaw C).w y * ((N : ℝ) * (100 / 19) * ∑ c : X.Loc, q C c y) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hrow_point C y) ((rowsLaw C).nonneg y)
      have hfubini :
          (∑ y, (rowsLaw C).w y * ∑ c : X.Loc, q C c y) =
            ∑ c : X.Loc, (rowsLaw C).expect (q C c) := by
        calc
          (∑ y, (rowsLaw C).w y * ∑ c : X.Loc, q C c y) =
              ∑ y, ∑ c : X.Loc, (rowsLaw C).w y * q C c y := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.mul_sum]
          _ = ∑ c : X.Loc, ∑ y, (rowsLaw C).w y * q C c y := by rw [Finset.sum_comm]
          _ = ∑ c : X.Loc, (rowsLaw C).expect (q C c) := rfl
      calc
        (∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
            ∑ y, (rowsLaw C).w y * ((N : ℝ) * X.evenRow H C v y a) := hfirst
        _ ≤ ∑ y, (rowsLaw C).w y * ((N : ℝ) * (100 / 19) * ∑ c : X.Loc, q C c y) := hsecond
        _ = (N : ℝ) * (100 / 19) * ∑ c : X.Loc, (rowsLaw C).expect (q C c) := by
              rw [← hfubini]
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
    have hq_dep (C : X.Centre) (c : X.Loc) :
        FinProb.DependsOn (q C c) star := by
      intro y y' hy
      have hFz (z : X.Tuple) : X.Fz H C v c z y = X.Fz H C v c z y' := by
        unfold Ctx6.Fz
        congr 1
        apply Finset.prod_congr rfl
        intro u hu
        rw [hy u hu]
      have hmc : mcAt C c y = mcAt C c y' := by
        dsimp [mcAt]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hFz z]
      have hmarg : margAt C c y = margAt C c y' := by
        dsimp [margAt]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hFz z, hmc]
      simp [q, hmarg]
    have hproj (C : X.Centre) (c : X.Loc) :
        (rowsLaw C).expect (q C c) =
          (FinProb.pi (fun u : {u : OddRole6 n // u ∈ star} => rowLaw C u.1)).expect
            (fun y => q C c ((Equiv.piEquivPiSubtypeProd (fun u : OddRole6 n => u ∈ star)
              (fun _ : OddRole6 n => Fin N)).symm (y, fun _ => X.y₀))) := by
      exact FinProb.pi_expect_depends (rowLaw C) star (q C c) (fun _ => X.y₀) (hq_dep C c)
    have hscore_expand (C : X.Centre) (c : X.Loc) :
        (rowsLaw C).expect (q C c) =
          ∑ y : StarY,
            (∏ u : {u : OddRole6 n // u ∈ star}, (rowLaw C u.1).w (y u)) *
              q C c (starExt y) := by
      rw [hproj]
      simp only [FinProb.expect, FinProb.pi]
      rfl
    have hwithTuple_idem (C : X.Centre) (c : X.Loc)
        (z₀ z : X.Tuple) :
        X.withTuple (X.withTuple C (c, β) z₀) (c, β) z = X.withTuple C (c, β) z := by
      have hdata : Function.update (Function.update (X.tup C) (c, β) z₀) (c, β) z =
          Function.update (X.tup C) (c, β) z := by
        funext e
        by_cases he : e = (c, β)
        · subst e
          simp
        · simp [he]
      change (((X.pos C, Function.update (Function.update (X.tup C) (c, β) z₀) (c, β) z),
          X.act C), X.ties C) =
        (((X.pos C, Function.update (X.tup C) (c, β) z), X.act C), X.ties C)
      rw [hdata]
    have hFz_inv (C : X.Centre) (c : X.Loc) (z₀ z : X.Tuple)
        (y : OddRole6 n → Fin N) :
        X.Fz H (X.withTuple C (c, β) z₀) v c z y = X.Fz H C v c z y := by
      unfold Ctx6.Fz
      rw [hwithTuple_idem C c z₀ z]
    have hmc_inv (C : X.Centre) (c : X.Loc) (z₀ : X.Tuple)
        (y : OddRole6 n → Fin N) :
        mcAt (X.withTuple C (c, β) z₀) c y = mcAt C c y := by
      dsimp [mcAt]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hFz_inv C c z₀ z y]
    have hmarg_inv (C : X.Centre) (c : X.Loc) (z₀ : X.Tuple)
        (y : OddRole6 n → Fin N) :
        margAt (X.withTuple C (c, β) z₀) c y = margAt C c y := by
      dsimp [margAt]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hFz_inv C c z₀ z y, hmc_inv C c z₀ y]
    have hExt (y : StarY) (u : OddRole6 n) (hu : u ∈ star) :
        starExt y u = y ⟨u, hu⟩ := by
      simp [starExt, Equiv.piEquivPiSubtypeProd_symm_apply, hu]
    have hFz_rowprod (C : X.Centre) (c : X.Loc) (z : X.Tuple)
        (y : OddRole6 n → Fin N) (hg : X.EvenGate H (X.withTuple C (c, β) z) v c) :
        X.Fz H C v c z y =
          ∏ u : {u : OddRole6 n // u ∈ star},
            (rowLaw (X.withTuple C (c, β) z) u.1).w (y u.1) := by
      have hprod :
          (∏ u ∈ star, X.oddRow H (X.withTuple C (c, β) z) u.1 (y u)) =
            ∏ u : {u : OddRole6 n // u ∈ star},
              (rowLaw (X.withTuple C (c, β) z) u.1).w (y u.1) := by
        calc
          (∏ u ∈ star, X.oddRow H (X.withTuple C (c, β) z) u.1 (y u)) =
              ∏ u : {u : OddRole6 n // u ∈ star},
                X.oddRow H (X.withTuple C (c, β) z) u.1 (y u.1) := by
                  simpa using (Finset.prod_attach star
                    (fun u => X.oddRow H (X.withTuple C (c, β) z) u.1 (y u))).symm
          _ = ∏ u : {u : OddRole6 n // u ∈ star},
                (rowLaw (X.withTuple C (c, β) z) u.1).w (y u.1) := by
                  apply Finset.prod_congr rfl
                  intro u hu
                  exact Lane_q_s06_ev_c.oddRow_eq_oddRowProb6_of_valid X H
                    (X.withTuple C (c, β) z) u.1 (hg.2.2.1 u.1 u.2) (y u.1)
      unfold Ctx6.Fz
      rw [if_pos hg, one_mul]
      simpa [star] using hprod
    have hFz_sum (C : X.Centre) (c : X.Loc) (z : X.Tuple) :
        (∑ y : StarY, X.Fz H C v c z (starExt y)) =
          if X.EvenGate H (X.withTuple C (c, β) z) v c then 1 else 0 := by
      by_cases hg : X.EvenGate H (X.withTuple C (c, β) z) v c
      · rw [if_pos hg]
        have hterm (y : StarY) :
            X.Fz H C v c z (starExt y) =
              ∏ u : {u : OddRole6 n // u ∈ star},
                (rowLaw (X.withTuple C (c, β) z) u.1).w (starExt y u.1) :=
          hFz_rowprod C c z (starExt y) hg
        have hsumFz :
            (∑ y : StarY, X.Fz H C v c z (starExt y)) =
              ∑ y : StarY,
                ∏ u : {u : OddRole6 n // u ∈ star},
                  (rowLaw (X.withTuple C (c, β) z) u.1).w (starExt y u.1) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact hterm y
        have hsumExt :
            (∑ y : StarY,
                ∏ u : {u : OddRole6 n // u ∈ star},
                  (rowLaw (X.withTuple C (c, β) z) u.1).w (starExt y u.1)) =
              ∑ y : StarY,
                ∏ u : {u : OddRole6 n // u ∈ star},
                  (rowLaw (X.withTuple C (c, β) z) u.1).w (y u) := by
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.prod_congr rfl
          intro u hu
          rw [hExt y u.1 u.2]
        rw [hsumFz, hsumExt]
        have hs := (FinProb.pi
          (fun u : {u : OddRole6 n // u ∈ star} =>
            rowLaw (X.withTuple C (c, β) z) u.1)).sum_eq_one
        simpa [FinProb.pi] using hs
      · unfold Ctx6.Fz
        rw [if_neg hg]
        simp
    have hscore_slot (C : X.Centre) (c : X.Loc) (z₀ : X.Tuple) :
        (rowsLaw (X.withTuple C (c, β) z₀)).expect
            (q (X.withTuple C (c, β) z₀) c) =
          ∑ y : StarY,
            X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y) := by
      rw [hscore_expand]
      apply Finset.sum_congr rfl
      intro y hy
      let C₀ := X.withTuple C (c, β) z₀
      by_cases hg : X.EvenGate H C₀ v c
      · have hMarg := hmarg_inv C c z₀ (starExt y)
        have hrowExt :
            (∏ u : {u : OddRole6 n // u ∈ star},
              (rowLaw C₀ u.1).w (y u)) =
              ∏ u : {u : OddRole6 n // u ∈ star},
                (rowLaw C₀ u.1).w (starExt y u.1) := by
          apply Finset.prod_congr rfl
          intro u hu
          rw [hExt y u.1 u.2]
        have hF : X.Fz H C v c z₀ (starExt y) =
            ∏ u : {u : OddRole6 n // u ∈ star},
              (rowLaw C₀ u.1).w (y u) := by
          have hFzRow : X.Fz H C v c z₀ (starExt y) =
              ∏ u : {u : OddRole6 n // u ∈ star},
                (rowLaw C₀ u.1).w (starExt y u.1) := by
            simpa [C₀] using hFz_rowprod C c z₀ (starExt y) hg
          exact hFzRow.trans hrowExt.symm
        simp [q, C₀, hg, hMarg, hF, mul_assoc]
      · have hF : X.Fz H C v c z₀ (starExt y) = 0 := by
          have hgate : ¬ X.EvenGate H (X.withTuple C (c, β) z₀) v c := by
            simpa [C₀] using hg
          unfold Ctx6.Fz
          simp [hgate]
        simp [q, C₀, hg, hF, mul_assoc]
    have hslot_cancel (C : X.Centre) (c : X.Loc) :
        (∑ z₀, (X.tupleLaw H β).w z₀ *
            (rowsLaw (X.withTuple C (c, β) z₀)).expect
              (q (X.withTuple C (c, β) z₀) c)) =
          ∑ z, (X.tupleLaw H β).w z * freq z *
            (if X.EvenGate H (X.withTuple C (c, β) z) v c then 1 else 0) := by
      calc
        (∑ z₀, (X.tupleLaw H β).w z₀ *
            (rowsLaw (X.withTuple C (c, β) z₀)).expect
              (q (X.withTuple C (c, β) z₀) c)) =
          ∑ z₀, (X.tupleLaw H β).w z₀ *
            ∑ y : StarY, X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y) := by
              apply Finset.sum_congr rfl
              intro z₀ hz₀
              rw [hscore_slot C c z₀]
        _ = ∑ y : StarY, ∑ z₀, (X.tupleLaw H β).w z₀ *
              X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y) := by
                calc
                  (∑ z₀, (X.tupleLaw H β).w z₀ *
                      ∑ y : StarY, X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y)) =
                    ∑ z₀, ∑ y : StarY, (X.tupleLaw H β).w z₀ *
                      X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y) := by
                        apply Finset.sum_congr rfl
                        intro z₀ hz₀
                        rw [Finset.mul_sum]
                  _ = ∑ y : StarY, ∑ z₀, (X.tupleLaw H β).w z₀ *
                        X.Fz H C v c z₀ (starExt y) * margAt C c (starExt y) := by
                          rw [Finset.sum_comm]
        _ = ∑ y : StarY, ∑ z, (X.tupleLaw H β).w z *
              X.Fz H C v c z (starExt y) * freq z := by
                apply Finset.sum_congr rfl
                intro y hy
                simpa [margAt, mcAt, freq] using
                  Lane_q_s06_ev_c.posterior_cancel6 (X.tupleLaw H β)
                    (fun z y => X.Fz H C v c z (starExt y)) freq
                    (fun z y => hFz_nonneg C c z (starExt y))
                    (fun z => hfreq_nonneg z) y
        _ = ∑ z, (X.tupleLaw H β).w z * freq z *
              ∑ y : StarY, X.Fz H C v c z (starExt y) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro z hz
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                ring
        _ = ∑ z, (X.tupleLaw H β).w z * freq z *
              (if X.EvenGate H (X.withTuple C (c, β) z) v c then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hFz_sum C c z]
    let score : X.Centre → X.Loc → ℝ := fun C c => (rowsLaw C).expect (q C c)
    let slot : X.Loc → X.Loc × X.Ty := fun c => (c, β)
    let Rest (c : X.Loc) := {e : X.Loc × X.Ty // e ∉ ({slot c} : Finset (X.Loc × X.Ty))}
    let fillData (c : X.Loc) (z : X.Tuple) (d : Rest c → X.Tuple) : X.Data X.Loc :=
      fun e => if h : e = slot c then z else d ⟨e, by simp [h]⟩
    let fallbackTuple : X.Tuple := (X.i₀, fun _ => X.y₀)
    let baseCenter (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) (d : Rest c → X.Tuple) : X.Centre :=
      (((P, fillData c fallbackTuple d), A), T)
    have hfill_update (c : X.Loc) (d : Rest c → X.Tuple) (z : X.Tuple) :
        fillData c z d = Function.update (fillData c fallbackTuple d) (slot c) z := by
      funext e
      by_cases h : e = slot c
      · subst e
        simp [fillData]
      · simp [fillData, h]
    have hcenter_update (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) (d : Rest c → X.Tuple) (z : X.Tuple) :
        (((P, fillData c z d), A), T) =
          X.withTuple (baseCenter P A T c d) (slot c) z := by
      change (((P, fillData c z d), A), T) =
        (((P, Function.update (fillData c fallbackTuple d) (slot c) z), A), T)
      rw [hfill_update]
    have hdataSplit (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) :
        (X.dataLaw X.Loc H).expect (fun D => score (((P, D), A), T) c) =
          ∑ z, (X.tupleLaw H β).w z *
            (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).expect
              (fun d => score (((P, fillData c z d), A), T) c) := by
      change (FinProb.pi (fun e : X.Loc × X.Ty => X.tupleLaw H e.2)).expect
          (fun D => score (((P, D), A), T) c) = _
      exact Lane_q_s06_ev_c.pi_expect_split_coord6
        (fun e : X.Loc × X.Ty => X.tupleLaw H e.2) (slot c)
        (fun D => score (((P, D), A), T) c)
    have hslot_rest (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) (d : Rest c → X.Tuple) :
        ∑ z, (X.tupleLaw H β).w z * score (((P, fillData c z d), A), T) c =
          ∑ z, (X.tupleLaw H β).w z * freq z *
            (if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0) := by
      calc
        (∑ z, (X.tupleLaw H β).w z * score (((P, fillData c z d), A), T) c) =
            ∑ z, (X.tupleLaw H β).w z *
              score (X.withTuple (baseCenter P A T c d) (slot c) z) c := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hcenter_update]
        _ = ∑ z, (X.tupleLaw H β).w z * freq z *
              (if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0) :=
                hslot_cancel (baseCenter P A T c d) c
    have hdataRest (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) :
        (X.dataLaw X.Loc H).expect (fun D => score (((P, D), A), T) c) =
          (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).expect
            (fun d => ∑ z, (X.tupleLaw H β).w z * freq z *
              (if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0)) := by
      rw [hdataSplit P A T c]
      calc
        (∑ z, (X.tupleLaw H β).w z *
            (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).expect
              (fun d => score (((P, fillData c z d), A), T) c)) =
          (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).expect
            (fun d => ∑ z, (X.tupleLaw H β).w z * score (((P, fillData c z d), A), T) c) := by
              unfold FinProb.expect
              calc
                (∑ z, (X.tupleLaw H β).w z *
                    ∑ d, (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                      score (((P, fillData c z d), A), T) c) =
                  ∑ z, ∑ d, (X.tupleLaw H β).w z *
                    (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                    score (((P, fillData c z d), A), T) c := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro d hd
                      ring
                _ = ∑ d, ∑ z, (X.tupleLaw H β).w z *
                      (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                      score (((P, fillData c z d), A), T) c := by rw [Finset.sum_comm]
                _ = ∑ d, (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                      ∑ z, (X.tupleLaw H β).w z * score (((P, fillData c z d), A), T) c := by
                      apply Finset.sum_congr rfl
                      intro d hd
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro z hz
                      ring
                _ = _ := rfl
        _ = (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).expect
              (fun d => ∑ z, (X.tupleLaw H β).w z * freq z *
                (if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0)) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro d hd
              exact congrArg
                (fun x : ℝ => (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d * x)
                (hslot_rest P A T c d)
    have hforceData (P : X.hp.Loc → Bool) (A : X.Loc → Bool) (T : X.hp.Ties)
        (c : X.Loc) (z : X.Tuple) :
        (X.dataLaw X.Loc H).expect (fun D =>
          if X.EvenGate H (X.withTuple (((P, D), A), T) (slot c) z) v c then 1 else 0) =
          (FinProb.pi (fun d : Rest c => X.tupleLaw H d.1.2)).expect
            (fun d => if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0) := by
      change (FinProb.pi (fun e : X.Loc × X.Ty => X.tupleLaw H e.2)).expect _ = _
      rw [Lane_q_s06_ev_c.pi_expect_split_coord6
        (fun e : X.Loc × X.Ty => X.tupleLaw H e.2) (slot c)
        (fun D => if X.EvenGate H (X.withTuple (((P, D), A), T) (slot c) z) v c then 1 else 0)]
      calc
        (∑ z₀, (X.tupleLaw H β).w z₀ *
            (FinProb.pi (fun d : Rest c => X.tupleLaw H d.1.2)).expect
              (fun d => if X.EvenGate H
                (X.withTuple (((P, fillData c z₀ d), A), T) (slot c) z) v c then 1 else 0)) =
          ∑ z₀, (X.tupleLaw H β).w z₀ *
            (FinProb.pi (fun d : Rest c => X.tupleLaw H d.1.2)).expect
              (fun d => if X.EvenGate H
                (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro z₀ hz₀
              congr 1
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro d hd
              rw [hcenter_update]
              rw [hwithTuple_idem (baseCenter P A T c d) c z₀ z]
        _ = (FinProb.pi (fun d : Rest c => X.tupleLaw H d.1.2)).expect
              (fun d => if X.EvenGate H
                (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0) := by
                unfold FinProb.expect
                rw [Finset.sum_mul]
                simp [(X.tupleLaw H β).sum_eq_one]
    have hscoreCenterEq (c : X.Loc) :
        (X.centreLaw H).expect (fun C => score C c) =
          ∑ z, (X.tupleLaw H β).w z * freq z *
            (X.centreLaw H).expect (fun C =>
              if X.EvenGate H (X.withTuple C (slot c) z) v c then 1 else 0) := by
      have hexpScore := Lane_q_s06_ev_c.centre_expect_data_last6 X H
        (fun P D A T => score (((P, D), A), T) c)
      have hexpGate (z : X.Tuple) := Lane_q_s06_ev_c.centre_expect_data_last6 X H
        (fun P D A T =>
          if X.EvenGate H (X.withTuple (((P, D), A), T) (slot c) z) v c then 1 else 0)
      rw [hexpScore]
      rw [hexpGate]
      rw [hdataRest, hforceData]
      change
        (∑ P, X.hp.posLaw.w P *
          ∑ A, X.hp.actLaw.w A *
            ∑ T, X.hp.tieLaw.w T *
              ∑ d : Rest c, (FinProb.pi
                (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                ∑ z, (X.tupleLaw H β).w z * freq z *
                  (if X.EvenGate H
                    (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0)) =
          ∑ z, (X.tupleLaw H β).w z * freq z *
            ∑ P, X.hp.posLaw.w P *
              ∑ A, X.hp.actLaw.w A *
                ∑ T, X.hp.tieLaw.w T *
                  ∑ d : Rest c, (FinProb.pi
                    (fun e : Rest c => X.tupleLaw H e.1.2)).w d *
                    (if X.EvenGate H
                      (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0))
      exact Lane_q_s06_ev_c.sum_pull_last5
          (X.hp.posLaw.w) (X.hp.actLaw.w) (X.hp.tieLaw.w)
          (fun d : Rest c => (FinProb.pi (fun e : Rest c => X.tupleLaw H e.1.2)).w d)
          (fun z => (X.tupleLaw H β).w z * freq z)
          (fun P A T d z =>
            if X.EvenGate H (X.withTuple (baseCenter P A T c d) (slot c) z) v c then 1 else 0)
    have hcore :
        ∑ c : X.Loc, (X.centreLaw H).expect (fun C => (rowsLaw C).expect (q C c)) ≤
          4 * (X.tupleLaw H β).expect freq := by
      calc
        (∑ c : X.Loc, (X.centreLaw H).expect (fun C => (rowsLaw C).expect (q C c))) =
            ∑ c : X.Loc, ∑ z, (X.tupleLaw H β).w z * freq z *
              (X.centreLaw H).expect (fun C =>
                if X.EvenGate H (X.withTuple C (slot c) z) v c then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  exact hscoreCenterEq c
        _ = ∑ z, (X.tupleLaw H β).w z * freq z *
              ∑ c : X.Loc, (X.centreLaw H).expect (fun C =>
                if X.EvenGate H (X.withTuple C (slot c) z) v c then 1 else 0) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro z hz
                rw [← Finset.mul_sum]
        _ ≤ ∑ z, (X.tupleLaw H β).w z * freq z * 4 := by
              apply Finset.sum_le_sum
              intro z hz
              exact mul_le_mul_of_nonneg_left (hSelect H hH v z hv)
                (mul_nonneg ((X.tupleLaw H β).nonneg z) (hfreq_nonneg z))
        _ = 4 * (X.tupleLaw H β).expect freq := by
              unfold FinProb.expect
              rw [← Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro z hz
              ring
    calc
      (X.centreLaw H).expect (fun C =>
          ∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
          (X.centreLaw H).expect (fun C =>
            (N : ℝ) * (100 / 19) * ∑ c : X.Loc, (rowsLaw C).expect (q C c)) :=
              FinProb.expect_mono (X.centreLaw H) hlocal_bound
      _ = (N : ℝ) * (100 / 19) *
            ∑ c : X.Loc, (X.centreLaw H).expect (fun C => (rowsLaw C).expect (q C c)) := by
              rw [FinProb.expect_smul]
              congr 1
              unfold FinProb.expect
              rw [Finset.mul_sum, Finset.sum_comm]
      _ ≤ (N : ℝ) * (100 / 19) * (4 * (X.tupleLaw H β).expect freq) :=
            mul_le_mul_of_nonneg_left hcore (mul_nonneg (Nat.cast_nonneg N) (by norm_num))
      _ = (N : ℝ) * (100 / 19) * 4 *
            (X.tupleLaw H β).expect
              (fun z => ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) /
                (X.k : ℝ)) := by simp [freq]; ring
  have hmix : 0 ≤ ∑ i, (X.Tβ H β).w i * (M.μ i).w a :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg ((X.Tβ H β).nonneg i) ((M.μ i).nonneg a)
  have hconst : (100 / 19 : ℝ) * 4 * (2 / c₁) ≤ Cm6 := by
    norm_num [Cm6, c₁, c₀]
  calc
    (X.centreLaw H).expect (fun C =>
        ∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) ≤
        (N : ℝ) * (100 / 19) * 4 *
          (X.tupleLaw H β).expect
            (fun z => ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) /
              (X.k : ℝ)) := hcenter
    _ ≤ (N : ℝ) * ((100 / 19) * 4 * (2 / c₁)) *
          ∑ i, (X.Tβ H β).w i * (M.μ i).w a := by
        calc
          (N : ℝ) * (100 / 19) * 4 *
              (X.tupleLaw H β).expect
                (fun z => ((Finset.univ.filter fun r : Fin X.k => z.2 r = a).card : ℝ) /
                  (X.k : ℝ)) ≤
            ((N : ℝ) * (100 / 19) * 4) *
              ((2 / c₁) * ∑ i, (X.Tβ H β).w i * (M.μ i).w a) :=
                mul_le_mul_of_nonneg_left hTuple (by positivity)
          _ = (N : ℝ) * ((100 / 19) * 4 * (2 / c₁)) *
                ∑ i, (X.Tβ H β).w i * (M.μ i).w a := by ring
    _ = ((100 / 19) * 4 * (2 / c₁)) *
          ((N : ℝ) * ∑ i, (X.Tβ H β).w i * (M.μ i).w a) := by ring
    _ ≤ Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H β).w i * (M.μ i).w a) :=
        mul_le_mul_of_nonneg_right hconst (mul_nonneg (Nat.cast_nonneg N) hmix)

/-- L6.1n (joint comparison, 06:857–868): actual odd-neighbour sets of separated rows are disjoint; the
near-product bound of `JfOK` on at most `n²` outputs; long computations at residual distance `> nearR` read
disjoint centre randomness, so the raw centre integrals factor into the comparison means. -/
theorem L6_1n_joint (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → X.EvenMean → X.EvenJoint := by
  sorry

/-- L6.1n (even loads, 06:870–884): close repeats by `H_bin(2ρ) < log 2 − .55` and the cap `10e^{.55n}`; the joint
comparison for separated rows; Lemma 3.6, Markov, the union over labels, and `|A|/N → 0`. -/
theorem L6_1n_loads (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → X.EvenJoint → X.EvenLoad := by
  sorry

/-- L6.1m–n assembled from their nodes. -/
theorem evenFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.StepFacts → X.StageFacts → X.CentreFacts → X.OddRowFacts → X.EvenFacts := by
  have h := (L6_1m_gate γ p₀ K hadm).and <| (L6_1m_dom γ p₀ K hadm).and <| (L6_1m_test γ p₀ K hadm).and <|
    (L6_1m_density γ p₀ K hadm).and <| (L6_1m_select γ p₀ K hadm).and <| (L6_1m_mean γ p₀ K hadm).and <|
    (L6_1n_joint γ p₀ K hadm).and (L6_1n_loads γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hG, hD, hT, hDe, hSel, hMe, hJo, hL⟩ hS hSt _hC hO
  obtain ⟨_hTD, _hC1, _hD1, _h2, _h2d, h2s, _hS, hN, _h3l, _h3h, _hbl, _hbh⟩ := hS
  obtain ⟨_hV, _hCo, _hHi, hSu⟩ := hSt
  obtain ⟨_hTa, hRo, _hPc, _hPr, _hLS⟩ := hO
  have hdom := hD hRo hN
  have hden := hDe hSu h2s hRo hdom
  have hsel := hSel
  have hmean := hMe hSu h2s hden hsel
  have hjoint := hJo hden hmean
  exact ⟨hG, hdom, hT hSu hdom hG, hden, hmean, hL hden hjoint, hsel, hjoint⟩

end

end S06
end HypercubeRamsey
